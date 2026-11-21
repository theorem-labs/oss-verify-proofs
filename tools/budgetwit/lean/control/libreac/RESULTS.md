# libreac Lean witness control

## Reference and result

The reference is branch `lean/libreac` at commit
`b0aef8518ca2a9313b20a19284d6ff1e07eb632b`.

The seven requested files total **4,272 lines** on that ref. The 4,858-line / nine-file number
in the original hand-build record includes a larger set than these seven files.

| File | Output lines | Copied source lines | Explicit fragment/template lines | Recorded comparison | Recorded differences |
| --- | ---: | ---: | ---: | --- | --- |
| `BudgetWit/Rzb.lean` | 329 | 0 | 329 carrier template | identical | None |
| `BudgetWit/RunB.lean` | 537 | 413 | 124 | identical | None |
| `BudgetWit/StartB.lean` | 505 | 450 | 55 | identical | None |
| `BudgetWit/UsageB.lean` | 1,388 | 1,284 | 104 | identical | None |
| `BudgetWit/WritevF.lean` | 712 | 658 | 54 | identical | None |
| `BudgetWit/WritevG.lean` | 660 | 559 | 101 | identical | None |
| `BudgetWitness.lean` | 141 | 0 | 141 composed witness | identical | None |

The recorded control compared bytes, not whitespace- or name-normalized text:
`diff -qr` over `BudgetWit/` and `diff -q` over `BudgetWitness.lean` exited zero.
The checked-in recipe omits issue identifiers from the seven header comments; the
recorded comparison predates that text-only change and does not claim byte identity
for the current output. The proof bodies are unchanged.

The recipe contains 3,364 copied-source lines and 908 supplied lines. The latter are not 908
new hand-proof lines: they include headers, comments, imports, namespace/section setup,
reformatted proof applications, the actual grant-obligation additions, the 329-line carrier
soundness template, and the 141-line composed witness. The retained fragments make each such
line explicit instead of pretending it was inferred from the released walk.

The genuine strengthening in `RunB` is `grant_ok` after the syscall checker premise in
`rzb_chk1_silent` and `rzb_ret_only_copyins_silent`; their caller knows syscall 66. The grant
proof at `set_tid_address` uses 96. `WritevF.rzb_writev_dep` and
`WritevG.rzb_writev_empty` discharge syscall 66's grant. The carrier removes `rz_cut`, adds
`grant_ok` at `rzb_node` and `rzb_silent`, and proves the never-refused results. These are
hand-supplied proof changes, not rename-only claims. Startup and usage walks consume the
strengthened helpers. The top-level witness composes the usage path and its non-vacuity fact.

## Parser decision and cost

The copier plus explicit fragments/templates regenerates **all 4,272 lines**; 3,364 come from
released-source ranges. **Zero lines require `gen_file.py` or `leanparse.py`** for this
control. This does not automate discovery of the ranges or the 908 supplied lines.

The curl observation is 99 Lean files / 42,409 lines / 9.8 agent-hours versus 100 Rocq files /
32,763 lines / 17.7 agent-hours. `CurlHarnessWit/RESUME.md:57,65` records the wave-2 parser and
emitter, so that aggregate cannot be attributed to the 57-line copier alone. This control,
not that confounded timing comparison, is the reason to retain the small copier here.

One regeneration, measured with Bash's `time`, took `regeneration_elapsed_s=0.243`. That is
recipe replay, not a fresh-harness proof-time measurement. The reference witness was already
available while constructing this recipe. No new harness was proved in this exercise.

**[INFERENCE] Planning estimate:** 1–3 agent-hours plus farm time for another harness with the
same YK15/AllocMode carrier, existing released walk proofs and straightforward non-allocation
grant premises, versus the recorded 5.5 hours by hand for the reference libreac witness. This estimate covers choosing
ranges and renames, supplying changed premises and a top-level witness, then checking types
and compiling. A new carrier/index or a new allocation-bound premise is outside that estimate;
its end-to-end cost remains unmeasured. The measured 0.243-second replay is not a defensible
end-to-end forecast for such a harness.

## Local checks

The recorded commands ran from the repository root. In the portable forms below,
`LEAN_WORK` is a caller-supplied scratch checkout of the reference, outside this worktree:

```sh
TMPDIR="$LEAN_WORK" PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tools/budgetwit/lean -p 'test_*.py' -v
PYTHONPYCACHEPREFIX="$LEAN_WORK/pycache" python3 -m py_compile tools/budgetwit/lean/__main__.py tools/budgetwit/lean/about_check.py tools/budgetwit/lean/emitter.py tools/budgetwit/lean/units.py tools/budgetwit/lean/test_lean.py tools/budgetwit/carriers.py
TIMEFORMAT='regeneration_elapsed_s=%3R' && time env PYTHONDONTWRITEBYTECODE=1 python3 -m tools.budgetwit.lean tools/budgetwit/lean/control/libreac/manifest.json --repo "$LEAN_WORK" --unit libreac/fuzz_knock --out "$LEAN_WORK/final-output" --about "$LEAN_WORK/final-probe.lean"
diff -qr "$LEAN_WORK/lean-proofs/libreac/fuzz_knock/OssFuzzTheorems/libreac/fuzz_knock/BudgetWit" "$LEAN_WORK/final-output/BudgetWit"
diff -q "$LEAN_WORK/lean-proofs/libreac/fuzz_knock/OssFuzzTheorems/libreac/fuzz_knock/BudgetWitness.lean" "$LEAN_WORK/final-output/BudgetWitness.lean"
```

Observed output excerpts:

```text
Ran 13 tests in 0.094s
OK
py_compile: PASS (five new Python files and shared carriers.py)
budgetwit type coverage: 60 public = 48 paired + 12 fresh
regeneration_elapsed_s=0.243
control (b): all seven byte-identical
```

The tests were first exercised with the missing implementation; fragment-range,
image-constructor, identifier-boundary, overlap, profile-substitution, output-duplication,
coverage-count and macro-audit regressions were observed failing before their fixes. The
first attempt to use `/usr/bin/time` failed because that executable is absent; Bash's built-in
`time` supplied the measurement. No Lean, Lake, Rocq or dune command ran on the dev box.

## Review findings resolved

The first 47-entry pair list omitted the public, unchanged pure helper
`WritevF.skipn_all_nil`. The new coverage check found this real defect locally. It is now
paired with `Reusable.YN3f.skipn_all_nil`; the tool checks 48 pairs and 12 explicitly fresh
claims, not an unchecked assertion that a hand-maintained list is complete. Stale exemptions,
missing twins, duplicated pairs and stale original names are rejected too.

Review also found that the original grant normalizer traversed hypotheses as well as the
outer telescope. It now traverses only outer forall bodies, counts deletions directly and
rejects a dependent grant proof. The Lean negative controls exercise nested, doubled and used
grants; an actual strengthened pair must also fail `equal` mode. Default-transparency
comparison deliberately accepts a different but definitionally equal abbreviation, wrapper
or `let`; it is not a syntactic statement comparison.

The copied tactic macro is `StartB.bwst_omega`: its body uses arithmetic facts and `omega`,
not old carrier lemmas. Imported `yn3f_omega` and `yn3f_gr` use numeral/register facts. The
carrier-typed `YL0v` walk macros are not copied. A lexical macro audit and regression test
also reject stale calls to renamed originals, including qualified calls in tactic quotations.

All staging trees, generated outputs, logs and bytecode caches were outside the worktree
in the scratch checkout. The recipe directory contains only the manifest, rename tables,
fragments, counts and this report.

## Farm control

Green `lean-precheck` Job: **`libreac-lean-budgetwit-control-1108-055435-tn8t8`**.
Unit label: `libreac__fuzz_knock`. Lean version: `4.34.0`.
Packed tree: `7f5f88844260f6e3b10ce68c0e07b1dc1cc63cc380d5977c674f498483eadb78`.
The package was a scratch directory, so the farm records `commit=none, dirty=1`; source
provenance is the fetched ref above and the manifest's pinned source hashes, not a claimed
commit of these uncommitted edits.

The submission used the existing farm driver, unchanged sizing, a successful server-side
Job dry run, then watched only `PodScheduled=False` pods until the pending gate cleared.
Scheduled Pending pods with running init containers did not block it. The staging script
used the existing `libreac-farmbuild.sh` driver with `PKG` set to the scratch Lake package,
`SCRATCH` set to the scratch checkout, `OSSV_KIND=lean-precheck`, and
`OSSV_UNIT=libreac__fuzz_knock`. Its owner and session fields came from the submitting
session. These were the seven module arguments:

```text
OssFuzzTheorems.libreac.fuzz_knock.BudgetWit.Rzb
OssFuzzTheorems.libreac.fuzz_knock.BudgetWit.RunB
OssFuzzTheorems.libreac.fuzz_knock.BudgetWit.StartB
OssFuzzTheorems.libreac.fuzz_knock.BudgetWit.UsageB
OssFuzzTheorems.libreac.fuzz_knock.BudgetWit.WritevF
OssFuzzTheorems.libreac.fuzz_knock.BudgetWit.WritevG
OssFuzzTheorems.libreac.fuzz_knock.BudgetWitness
```

Observed verdict and gate excerpts:

```text
Build completed successfully (1308 jobs).
build_rc=0 seconds=6 rebuilt: 0 package modules, 0 other
axiom gate: 0 modules to check, 1113 passed before on the same bytes
checker: 0 modules to check, 1113 passed before on the same bytes
AXIOM_GATE: no module to check
BUDGETWIT NEGATIVE CONTROL rejected OssFuzzTheorems.libreac.fuzz_knock.proofs.lib.Reusable.YP0n.rz_chk1_silent => OssFuzzTheorems.libreac.fuzz_knock.BudgetWit.RunB.rzb_chk1_silent
BUDGETWIT NEGATIVE CONTROLS nested_grant, double_grant, used_grant rejected
smoke_rc=0
=== FARMBUILD VERDICT green job=libreac-lean-budgetwit-control-1108-055435-tn8t8 forbid=0 build=0 axioms=0 checker=0 smoke=0 axioms_checked=0 axioms_skipped=1113 checker_checked=0 checker_skipped=1113 full_check=0 tree=7f5f88844260f6e3b10ce68c0e07b1dc1cc63cc380d5977c674f498483eadb78 dirty=1 commit=none peak_mib=533 cpu_avg=0.96 cpu_peak=0.96 disk_peak_mib=16103 disk_end_mib=16103 wall_s=98 ===
```

All 48 discharged-type comparisons ran successfully: 42 `equal`, six `extra_grant`.
The proof modules and axiom/kernel verdicts were restored from the same-byte farm ledger;
**this run did not perform a fresh 1,113-module axiom or kernel replay**. The elaborator probe
and its negative controls ran afresh in the preserved layout smoke phase. Each of
`usage_never_refused`, `plain_budget_witness` and `plain_halts_not_vacuous` printed exactly:

```text
[propext,
 Classical.choice,
 Quot.sound]
```

Job `libreac-lean-budgetwit-control-1108-055435-tn8t8` established the recorded green
build, cached axiom/kernel verdicts and fresh type-comparison smoke results above.
The final emitted probe was byte-compared with this run's probe input and matched.

Three preceding Jobs were red while developing the control: `053936-5skvs` (the farm's
import scanner treated the redundant `import Lean` as a package target), `054237-lckc4`
(the original emit-nil theorem was named `realizes_emit_nil`, not `rz_emit_nil`), and
`055017-jf7m9` (`mkArrow` in the negative-control code is monadic). Their full Job names have
the same `libreac-lean-budgetwit-control-1108-` prefix. All were fixed; these were smoke /
recipe defects, not differences in the seven regenerated proof files. Their receipts remain
in the external scratch directory. Pending-only submit attempts were not treated as builds.

## Time spent

From the first recorded clock (`2026-11-08T05:28:14+00:00`) through the green control and final
checks (`2026-11-08T06:00:03.189023+00:00`): **0.530 worker wall-hours**, including farm waits.
This is one worker's elapsed time; the peer review was not separately metered. It is not a
measurement of proving a previously unseen harness, which is why the 1–3-hour estimate above
is marked as an inference.

