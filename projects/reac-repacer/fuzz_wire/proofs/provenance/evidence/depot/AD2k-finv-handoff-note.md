# AD2k hunk 6 — note for composition / close owners (ruling 14:51Z, (D) join statement)

`AD2k.tfib_finv_handoff` (A/AD2k.v:102) is the start-up hand-off the unit close cites. Its statement takes the layout as
`AD1g.ly0 E model` (two arguments: the env E and the model), NOT grant's three-argument `AD1g.ly0 ch E model`. The `ch`
argument dropped because fuzz_wire's empty-depot AD1g.ly0 (A/AD1g.v:741-742) closes over E and model only: in the
depot form there is no HH / HHc ch cell (grant's `HH = HHc ch`, grant-w4 AD1g.v:745-749, is gone), so ly0 reads no
value from ch. This is AD2k hunk 6, not AD1p hunk 10 (AD1p 10 is a proof-body `set` that follows the same arity).

Where ly0's facts come from: the hand-off's `ameta_inv ... (AD1g.ly0 E model) ...` is discharged inside
`tfib_drv_main`'s proof (A/AD1p.v, cited by the composition file A/AD1q.v:105) from AR via `tfib_finv_handoff` at
AD1p.v:115; the layout facts (top_ok, FINV) come from AD1f.tfib_top_ok (A/AD1f.v:244) and AD1f.tfib_AR (A/AD1f.v:235),
whose own ly0 uses are the same two-argument form (A/AD1f.v:59). A composition / close file that states the hand-off
must write `AD1g.ly0 E model` (no ch). tfib_drv_main reaches the tops through the composition file A/AD1q.v (its proof
at A/AD1q.v:105 applies tfib_srealizesX_of_main to it); the Print Assumptions row of record is pa-wire.tsv
`AD1q.v tfib_srealizesX`: 15 axioms, the Rocq primitives (PrimInt63.*, PrimString.*, PrimArray.array),
FunctionalExtensionality.functional_extensionality_dep and Classical_Prop.classic; equal to grant's row in
pa-grant-release.tsv (pa-diff.txt: 0 differ).
