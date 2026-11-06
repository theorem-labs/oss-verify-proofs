# The A/AFet.v cost fix (afet-cost.patch): the lane report of record

proves no function (kind: proof-script cost). The report of lane TcaAFet (row TCA, 2026-10-31 07:2xZ), as it reported it; host paths are written as variables (MANIFEST.md). The patch is ../afet-cost.patch (sha256 9f5dfea19198); the build log it cites was removed from the shipped tree on 2026-11-04; internal record, in git history.

AFet.vo now builds in 8.48 s using 0.7 GB at MEM=24g. Before the fix it took 7936 s and 43 GB. The time came from four copies of one proof step that grows with the square of the length of `Tfib_const`. Transport's `Tfib_const` holds 3080 cells; the other units hold 310 to 792. No Lemma or Definition statement changed, and nothing is Admitted.

## Cause
- **Where:** four proof steps in stage-out `A/AFet.v`, inside the `CONST'` assert, each one the sub-proof `assert (Hv : v = AV (ANum 0))`:
  - lines 294–295 and 302–303 in `FIN_a`
  - lines 483–484 and 491–492 in `DRPRE`
- **The step:** `cbv [Tfib_const Tfib_const_sym Tfib_const_abs Tfib_const_shadow app In …] in Hc. repeat (destruct Hc as [Hc|Hc]; [first [congruence | discriminate] |]). destruct Hc.` This turns `In c (Tfib_const ly)` into a disjunction with one case per cell, then splits it one cell at a time. Time and memory grow with the square of the cell count. Most of the time is in `Qed`, where the kernel checks the nested `or` matches.
- **Why only transport:** AFet.v is the same text in all three copies. Diffed with numerals masked, transport's file differs from grant's and decode's only in module paths and in `GrantSyms`/`DecodeSyms` → `TransportSyms`. AFet.v is also byte-identical between the interim lib (work-rec2's 492 files) and work-rec4. What differs is `Tfib_const` in AF0m:

|Unit|Cells (sym + abs + shadow)|AFet.vo time / peak memory|
|---|---|---|
|transport (interim)|22 + 568 + 2490 = 3080|7936 s / 43.3 GB|
|libdiginet fuzz_decode|369|90.9 s / 1.67 GB (the fuzz_decode build log build-20261031T035813Z)|
|fuzz_reply|792|297–397 s / 3.6–4.2 GB|
|fuzz_wire|310|50–55 s / 1.25 GB|
|fuzz_pcap|330|55–70 s / 1.45 GB|
|grant (donor)|491|no AFet time found in any log|
|frame|326|no AFet time found in any log|

- **Measured cost of one block** (scratch probe, run on a prefix of the list; all three prefixes include the target cell, which is at index 284):

|Cells|Tactic|`Qed`|
|---|---|---|
|400|3.8 s|14.7 s|
|800|11.1 s|65.6 s|
|1600|54.1 s|285.2 s|

  Each doubling costs about 4.3×. The probe file peaked at 6.76 GB. Scaled up, one block at 3080 cells needs about 25 GB. `FIN_a` and `DRPRE` each hold two blocks in one proof, which matches the 43 GB peak.

## Fix
- **New proof:** each block now gets the address and width from `Hc`'s type and the expected value from the goal. It then proves `forallb (…check…) (Tfib_const ly) = true` with `vm_compute; reflexivity`. `forallb_forall`, a short `cbn`, `destruct v`/`destruct e0`, and `Z.eqb_eq` then give `v = AV (ANum 0)`.
- **No shifts:** each block still takes two lines, so no line number moves. The new lines contain no numeric literals or addresses.
- **Same cost on the new lines:** in the probe, each new block took 0.03 s and its `Qed` 0.004 s.

## Patch
- **Path:** `EV/afet-cost.patch`
- **sha256:** `9f5dfea19198b183735e332d13d4d0700b3d6398a90952982b2d295a6db2d8a1`
- **Contents:** 2 hunks against stage-out with its `(* Relocated from …` line removed, in the same form as `cell-lookup.patch`.
- **Apply test:** I copied `work-rec4/stage-out` and removed the provenance line from its files. `patch -p0 -F0` applied cleanly, with no `.rej` or `.orig`. The result is byte-equal to the text I built.

## Build
- **Command:** `VM=<the transport build VM> JOBS=4 MEM=24g cb build <CLONE_AFET> …`, on the clone CLONE_AFET (the interim lib: work-rec2's 492 files) with the fix.
- **Log:** `CLONE_AFET.logs/build-20261031T071623Z.log`, line 51:
  `proofs/libdiginet/fuzz_transport/lib/A/AFet.vo (real: 8.48, user: 8.13, sys: 0.35, mem: 706944 ko)`
- **Result:** rc=0, 0 failed, 0 inconsistent .vo.
- **Print Assumptions of `tfib_drain_ok`** (log lines 18–34): 14 axioms, all on `toolchain/allowed-axioms.txt`. They are 13 PrimInt63 / PrimString / PrimArray primitives and `functional_extensionality_dep`.

## Not run
I built against the interim lib, not the run of record's lib, because the build of the run of record's lib is still running. For the changed lines the two libs give the same input:
- AF0x.v (`aexp_eqb`) and YG0f.v are identical.
- AF0m.v differs only by the added cell `z8 (ANum 0x10338)`. The `0xa970a`/`0xa970c` cells are at the same positions (284 and 285) with value 0.

## Clean-up
- I removed the scratch probe files from the clone and from the VM's `ws/` and `dco/` copies.
- Copies of the probe sources are next to the log as `ZZafetProbe.v.txt` and `ZZafetAx.v.txt`, so the timing lines can be read.
- The clone still has the fixed `AFet.v`, uncommitted and identical to the patch. Nothing is pushed.

## What you must do
Add `afet-cost` to the `--patch` list of the run script (`run83.sh` line 28, or the run of record's copy) so the next run applies it.
