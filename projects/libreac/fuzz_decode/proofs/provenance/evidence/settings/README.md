This README replaces the slice MANIFEST.md (2026-10-31); the file list and sha256 of every file are in provenance/evidence/MANIFEST.md.

# provenance/evidence/settings: the lib's tactic-level settings, recorded once (stream lead rule 1i-ter)

The files (the file list with the sha256 of every file is in `provenance/evidence/MANIFEST.md`):

- `TACTIC-SETTINGS.md`: every tactic-level setting of the lib (ESCAPES 1229, UNMEASURED 4, KERNEL 0) from one run of
  global_settings.py over all 2673 .v files of lib/ at 3f64815aead2
- `mk_settings_record.py`: writes TACTIC-SETTINGS.md from that run's stdout; reproduce:
  `mk_settings_record.py RUN_OUTPUT proofs/libreac/fuzz_decode/lib 3f64815aead2 > TACTIC-SETTINGS.md`

The run used global_settings release r2, whose script is byte-identical to v10 (sha256
439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242; the release's SHA256SUMS verified, 22 OK); r2 changes
only the release wrapper. Tactic-level settings change proof search, not what the kernel checks: they are recorded, not
made Local and not rebuilt. No proof file changes.

Delta against the released base: the same script over all 2673 .v files of lib/ at the released prover commit
5607400a019c (the series base) prints the same SUMMARY (ESCAPES 1229; PLAIN 4735; UNMEASURED 4; KERNEL 0; TACTIC 5154,
OPTION 814; HINTS 227), and its 6195 reported rows (file, line, class, text) are identical to the head run's: ESCAPES
1229 at base and at head, delta 0. The series adds no setting. By class (TACTIC-SETTINGS.md, 'ESCAPES, by setting'):
`Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=` 1100 rows in 453 files, `Ltac numconst ::=` 92,
`Ltac drv_anch ::=` 6, `#[global] Set Default Proof Mode` 4 (OPTION), `Global Opaque` 2, `Ltac Lia.lia ::=` 2,
`Ltac Lia.nia ::=` 2, and 21 single rows (Lia / Nia / Nra cache flags, tauto, zify hooks and the unit's own simulation
tactics), all TACTIC except the 4 OPTION rows.

The 4 UNMEASURED rows are `Arguments` commands, whose locality the tool cannot decide: lib/A/Prog/PaSym.v:179
`Arguments codeptr _ /.`, lib/Lib/Exec.v:136 `Arguments mstep segs ms ms' /.`, lib/Lib/ExecF.v:321
`Arguments mstepF segs RNG ms ms' /.` and lib/Reusable/YG0f.v:88 `Arguments shadow_addr _ : simpl never.`. Each sets
only how `simpl` / `cbn` unfold one constant (a reduction hint, not a kernel setting), and each is the same at base.
