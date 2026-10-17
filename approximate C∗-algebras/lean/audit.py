#!/usr/bin/env python3
"""Audit one Lean certificate and write its machine-readable record.

Usage (from the lean_certificates workspace root):
    python3 <skill>/scripts/audit.py <Name>

Expects Certs/<Name>/Statement.lean (defines `Cert.<Name>.Claim : Prop`) and
Certs/<Name>/Proof.lean (proves `theorem Cert.<Name>.main : Claim`). Optional
Certs/<Name>/Sanity.lean (non-vacuity witnesses; every `theorem` in it is audited too).

Checks, in order, and stops at the first failure:
  1. forbidden-construct scan over every .lean file of the certificate (comments stripped)
  2. lake build of Proof (and Sanity)
  3. `main` has exactly the type `Claim`  (an `example : Claim := main` in Audit.lean)
  4. #print axioms: only propext, Classical.choice, Quot.sound are allowed
  5. leanchecker kernel replay of each module
Then writes Certs/<Name>/audit.json (hashes, toolchain, Mathlib rev, axioms, timings).
Exit code 0 only if every check passed.
"""
import hashlib, json, re, subprocess, sys, time
from pathlib import Path

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# token -> why it breaks the certificate
FORBIDDEN = {
    r"\bsorry\b": "unproved goal",
    r"\badmit\b": "unproved goal",
    r"^\s*(private\s+|protected\s+)?axiom\b": "new axiom",
    r"\bnative_decide\b": "trusts the compiler (adds Lean.ofReduceBool)",
    r"\bimplemented_by\b": "swaps the kernel term for compiled code",
    r"@\[\s*extern": "opaque external code",
    r"\bunsafe\b": "bypasses the kernel",
    r"^\s*#exit\b": "silently stops elaboration of the rest of the file",
    r"set_option\s+debug\.": "debug options can skip kernel checks",
    r"\bTrust\b|\btrust\b\s*:=": "kernel trust level change",
}
# extra rules for Statement.lean only: the reader must be able to read the claim literally
STATEMENT_ONLY = {
    r"^\s*(local\s+|scoped\s+)?(notation|infix[lr]?|prefix|postfix|macro|syntax|elab)\b":
        "custom syntax in the statement can make it read as something it is not",
    r"^\s*(local\s+|scoped\s+)?instance\b":
        "a local instance can change what +, <, ∑ mean in the statement",
    r"^\s*(theorem|lemma)\b": "the statement file must not prove anything",
    r"^\s*opaque\b": "opaque definitions hide their meaning",
}


def strip_comments(src: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
            continue
        if src[i] == '"':  # skip string literals
            j = i + 1
            while j < len(src) and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append(" " * (j + 1 - i)); i = j + 1; continue
        out.append(src[i]); i += 1
    return "".join(out)


def scan(path: Path, rules: dict) -> list:
    code = strip_comments(path.read_text())
    hits = []
    for pat, why in rules.items():
        for m in re.finditer(pat, code, flags=re.M):
            line = code.count("\n", 0, m.start()) + 1
            hits.append(f"{path}:{line}: `{m.group(0).strip()}` -- {why}")
    return hits


def run(cmd, timeout=3600):
    t = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout + p.stderr, round(time.time() - t, 1)


def fail(msg, record, cdir):
    record["result"] = "FAIL"
    record["failure"] = msg
    (cdir / "audit.json").write_text(json.dumps(record, indent=2, ensure_ascii=False))
    print("FAIL:", msg)
    sys.exit(1)


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    name = sys.argv[1]
    root = Path.cwd()
    cdir = root / "Certs" / name
    stmt, proof, sanity = cdir / "Statement.lean", cdir / "Proof.lean", cdir / "Sanity.lean"
    for f in (stmt, proof):
        if not f.exists():
            sys.exit(f"missing {f}")
    ns = f"Cert.{name}"
    files = [f for f in (stmt, proof, sanity) if f.exists()]
    extra = sorted(p for p in cdir.glob("*.lean") if p not in files and p.name != "Audit.lean")
    files += extra

    manifest = json.loads((root / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    record = {
        "certificate": name,
        "claim": f"{ns}.Claim",
        "theorem": f"{ns}.main",
        "toolchain": (root / "lean-toolchain").read_text().strip(),
        "mathlib_rev": mathlib["rev"],
        "files": {str(f.relative_to(root)): hashlib.sha256(f.read_bytes()).hexdigest() for f in files},
        "checks": {},
    }

    # 1. forbidden constructs
    hits = []
    for f in files:
        hits += scan(f, FORBIDDEN)
    hits += scan(stmt, STATEMENT_ONLY)
    record["checks"]["forbidden_scan"] = hits or "clean"
    if hits:
        fail("forbidden constructs:\n  " + "\n  ".join(hits), record, cdir)

    # 2. build
    mods = [f"Certs.{name}.{f.stem}" for f in files]
    code, out, dt = run(["lake", "build", *mods])
    record["checks"]["build"] = {"ok": code == 0, "seconds": dt}
    if code != 0:
        fail("lake build failed:\n" + out[-4000:], record, cdir)
    warn = [l for l in out.splitlines() if "declaration uses" in l]
    if warn:
        fail("build warnings indicate holes:\n  " + "\n  ".join(warn), record, cdir)

    # 3 + 4. type match and axioms
    sanity_thms = []
    if sanity.exists():
        sanity_thms = re.findall(r"^\s*theorem\s+([\w.'₀-₉]+)", strip_comments(sanity.read_text()), re.M)
    imports = "\n".join(f"import {m}" for m in mods)
    targets = [f"{ns}.main"] + [f"{ns}.{t}" if not t.startswith(ns) else t for t in sanity_thms]
    audit_src = (
        f"{imports}\n\n"
        f"/-! Generated by audit.py. `main` must have exactly the type `Claim`. -/\n"
        f"example : {ns}.Claim := {ns}.main\n\n"
        + "".join(f"#print axioms {t}\n" for t in targets)
        + f"#print {ns}.Claim\n"
    )
    (cdir / "Audit.lean").write_text(audit_src)
    code, out, dt = run(["lake", "env", "lean", str(cdir / "Audit.lean")])
    record["checks"]["audit_elaboration"] = {"ok": code == 0, "seconds": dt}
    if code != 0:
        fail("Audit.lean failed (does `main` prove exactly `Claim`?):\n" + out[-4000:], record, cdir)
    axioms, bad = {}, []
    for t in targets:
        m = re.search(rf"'{re.escape(t)}' depends on axioms: \[([^\]]*)\]", out)
        if m:
            ax = [a.strip() for a in m.group(1).split(",") if a.strip()]
        elif re.search(rf"'{re.escape(t)}' does not depend on any axioms", out):
            ax = []
        else:
            fail(f"could not read axioms of {t}:\n{out[-2000:]}", record, cdir)
        axioms[t] = ax
        bad += [f"{t}: {a}" for a in ax if a not in ALLOWED_AXIOMS]
    record["checks"]["axioms"] = axioms
    pm = re.search(r"def " + re.escape(ns) + r"\.Claim\b.*", out, re.S)
    record["claim_as_elaborated"] = pm.group(0).strip() if pm else None
    if bad:
        fail("non-standard axioms:\n  " + "\n  ".join(bad), record, cdir)

    # 5. independent kernel replay
    replay = {}
    for m in mods:
        code, out, dt = run(["lake", "env", "leanchecker", m])
        replay[m] = {"ok": code == 0, "seconds": dt}
        if code != 0:
            record["checks"]["leanchecker"] = replay
            fail(f"leanchecker rejected {m}:\n{out[-2000:]}", record, cdir)
    record["checks"]["leanchecker"] = replay

    record["result"] = "PASS"
    record["audited_at"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    (cdir / "audit.json").write_text(json.dumps(record, indent=2, ensure_ascii=False))
    print(json.dumps(record, indent=2, ensure_ascii=False))
    print("\nPASS")


if __name__ == "__main__":
    main()
