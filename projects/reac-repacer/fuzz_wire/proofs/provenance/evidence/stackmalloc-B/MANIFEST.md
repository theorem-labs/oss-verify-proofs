# provenance/evidence/stackmalloc-B: fuzz_wire image-B __asan_stack_malloc_0 / _1 contracts, relocation and gate record

The record of five files relocated from fuzz_grant's released image-B lib to fuzz_wire's image B (fuzz_wire.asan-ubsan,
pin af4534831a45 = harness.yaml, unstripped twin 51eb4bef2425): two contracts of the ASan runtime, no new proof.

| file (lib/) | donor (fuzz_grant's released lib; the same blob at origin/ossv/recipes 283c35cdd4dc `projects/libreac/fuzz_grant/proofs/lib/...` and at recipes 4f87de75d67 `proofs/libreac/fuzz_grant/lib/...`) | contract |
|---|---|---|
| B/Rt/StackMalloc0.v | lib/B/Rt/StackMalloc0.v, blob 5fa59c37a532 | B/Rt/StackMalloc0.v:515 `Corollary stack_malloc0_contract : forall B, AR_laws tfibsegs B -> WireSyms B -> astack_malloc_realizes tfibsegs B 0.` |
| B/Rt/StackMalloc0Tbl.v | lib/B/Rt/StackMalloc0Tbl.v, blob edb042b027b7 | (the class-0 constants, probe points and cells) |
| B/Rt/YF0r.v | lib/B/Rt/YF0r.v, blob d741f2d982c3 | (the class-1 constants and the code table) |
| B/Rt/YF0s.v | lib/B/Rt/YF0s.v, blob 9269619b602a | B/Rt/YF0s.v:515 `Corollary stack_malloc1_contract : forall B, AR_laws tfibsegs B -> WireSyms B -> astack_malloc_realizes tfibsegs B 1.` |
| Reusable/YF0v.v | lib/Reusable/YF0v.v, blob 75c25878eab7 | (own_free_frame / own_free_frame_shadow; StackMalloc0.v and YF0s.v Require it, the unit's lib/Reusable lacked it) |

Every other module the five files Require was already in the unit's lib (B/YCe5, B/YB1v, B/YE34, B/YF0l, B/YF0m,
B/YF0x, B/YE2y and the shared Reusable kernel files). The new files carry no licence lines: apply-smB.sh removes the
donor's and the tool's (applied.txt counts them); every other byte is the run's stage-out.

## Route

1. Tool: port_core 0e4e065eab9f (port_core.py sha256 0e4e065eab9f9a67; `git archive 7f0e4b05267
   tools/pg-reloc/0e4e065eab9f`, as the tools registry row names it) with the flags of the unit's image-B core run of record
   (../core-B/run.sh): the same donor normalisation (../core-B/mkdon.sh 4f87de75d67 fuzz_grant B), --old-syms
   (../core-B/fuzz_grant.asan-ubsan.syms.txt), --old-prog, --no-stage list, image-B mode, kernel / known images and the
   rename set GrantB / GrantSyms / GrantB_syms / GrantB_ok -> WireB / WireSyms / WireB_syms / WireB_ok; --files
   files-smB.txt. Module paths change only by --src-mod -> --target-mod.
2. Numerals: every numeral that differs from the donor or lies in an address range of either image is decided by role
   on fuzz_wire's own image (gates/numerals-smB.py, records/numerals-smB.tsv); no relocation tool decides a row.
   Two values no port_core rule decides are --override rows (overrides-smB.tsv: the low-shadow bound
   kLowShadowBeg + IMG_TOP / 8, which port_core read as the shadow of a .bss address).
3. Structural patch (B-smB.patch, applied by port_core --patch, zero fuzz):
   - YF0r.v fs_ranges without the rows of __asan_stack_malloc_2 / _4, which port_core refuses (code-no-counterpart):
     fuzz_wire links classes 0 and 1 only (its twin has no __asan_stack_malloc_2 / _4 symbol).
   - StackMalloc0.v and YF0s.v, the `assert (SZ : 0 <= snd e)` step: `try destruct (ly_NB ly =? 0); try destruct
     (ly_SB ly =? 0);` before `cbn [snd]`. The unit's kernel is the empty-depot one (lib/Reusable/DepotCfg.v
     depot_has_trace = false), whose owned_extents (lib/Reusable/YG0f.v) has `if (ly_NB ly =? 0) ...` entries; the
     donor text leaves `0 <= snd (if ...)`, which lia does not prove (the first build: `No applicable tactic`). The
     added text is the released empty-depot form of fuzz_knock's image-B file (commit 48907dc7e8ca,
     projects/libreac/fuzz_knock/proofs/lib/AU/YF0s.v:75), byte for byte. No statement changes.
4. Apply: apply-smB.sh copies the stage-out by --apply's rule (nothing overwritten), because of core-B's known FAIL row
   `rename-new-undeclared WireSyms` (the Record is declared in the start-up file lib/B/YF0m.v, never staged).
5. Gates: GATES.md (gates/run-gates.sh; records/ by its step 6, host paths and lane names in tool output replaced by
   placeholders, images named by sha256).

## Files

| file | role |
|---|---|
| run.sh | the relocation run of record (port_core flags), with what differs from core-B's |
| files-smB.txt | --files: the five donor paths, each with its blob |
| overrides-smB.tsv | --override: the two low-shadow-bound values, each decided by role |
| B-smB.patch | --patch: the fs_ranges rows and the empty-depot step (section 3 above) |
| apply-smB.sh, applied.txt | copies the stage-out (licence lines removed); the list of the five files written |
| gates/run-gates.sh | every gate in order, each with its planted control; writes records/ |
| gates/bodycmp-smB.py | the body compare on cmpkit 86da41d3ef68 (strictcmp3 65688e94214a): functions, decoded ranges, plant |
| gates/numerals-smB.py | the per-numeral table by role, with the donor image as the control of each rule |
| gates/pac-smB.sh, gates/triage-smB.py | port_addr_check 45b78aaa48c3 donor -> ported; one measured reason per row that is not a pass |
| records/portcore-run.txt | the run of record's versions, summary lines, FAIL rows and required.tsv |
| records/numerals-smB.tsv, numerals*.txt | the numeral table (116 rows) and its run; numerals-plant.* the planted control |
| records/bodycmp-*.out, bodycmp.txt | kit check, twins, function compare (with the JUDGED row), range compare, plant |
| records/size-moves*.tsv, size-moves*.out | size_moves 7edcb4804346 and size_moves_classify 810be4eaa791 |
| records/flag*.tsv, flag*.log, triage*.txt | port_addr_check, its triage, and the planted run |
| records/ab1w-*.tsv, ab1w-*.txt | ab1w_swaps 3f885801a1f5 over the five files and lib/B/YB1w.v |
| records/print-assumptions.txt | Check / Print Assumptions of both contracts |
| records/build.txt | the builds: the iterating builds and the fresh build of the pushed head |
| takes.tsv | the one proof-body line taken from a released file (the SZ step on the empty-depot kernel), its break, the knock line it copies byte-equal and the ruling |
| records/gates.txt | one line per gate run of run-gates.sh |

Line numbers: the five files carry their donor header lines byte-equal (lines 1-5; YF0v.v 1-4), restored after the
gate run, so code line N of the records is line N + 5 of the committed file (YF0v.v: N + 4).
