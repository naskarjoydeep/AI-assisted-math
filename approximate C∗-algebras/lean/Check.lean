import Certs.KitaevChannels.Proof
import Certs.KitaevChannels.Sanity
import Certs.KitaevSectors.Proof
import Certs.KitaevSectors.Sanity
import LeanProof

/-!
# Quick check of the main results

After `lake build`, run `lake env lean Check.lean`. Each `example` succeeds only if `main` proves
*exactly* the stated `Claim`, and `#print axioms` must list only `propext`, `Classical.choice` and
`Quot.sound`. The full audit (source scan, build, type match, axioms, `leanchecker` replay) is
`python3 audit.py KitaevChannels` and `python3 audit.py KitaevSectors`.
-/

-- Theorem A (approximate factorization on a Hilbert space of any dimension)
example : Cert.KitaevChannels.Claim := Cert.KitaevChannels.main
#print axioms Cert.KitaevChannels.main
#print axioms Cert.KitaevChannels.hyps_satisfiable_infinite_dim

-- Theorem B (infinitely many finite sectors)
example : Cert.KitaevSectors.Claim := Cert.KitaevSectors.main
#print axioms Cert.KitaevSectors.main
#print axioms Cert.KitaevSectors.hyps_satisfiable

-- Further results (Part III of LEAN_CERTIFICATE.md)
#print axioms Kitaev.DeltaIso.symm
#print axioms Kitaev.Graded.graded_rigidity
