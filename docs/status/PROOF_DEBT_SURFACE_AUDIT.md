# Proof-debt surface audit

This repository-local audit records a block-comment-aware scan of Lean source files under `Iris/` and `IrisMath/`.

The audit checks for active visible occurrences of:

```text
sorry
admit
axiom
opaque
unsafe
The intended interpretation is deliberately narrow:
NO_ACTIVE_SORRY_ADMIT_AXIOM_OPAQUE_SURFACE
means only that the scanned Lean source surface contains no active visible occurrences of sorry, admit, axiom, or opaque outside comments.
It does not claim repository-wide semantic soundness, upstream endorsement, theorem ownership, or proof replacement.
Run:
python3 scripts/audit_proof_debt_surface.py
Machine-readable output:
docs/status/proof_debt_surface_audit_latest.json
