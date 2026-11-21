(** * EnoughCheck — LAYER 2: the differential validation harness.
    EVERY Example below was GENERATED FROM THE C ORACLE'S OUTPUT:
    zlib-1.3.1/examples/enough.c (md5 ),
    compiled gcc -O2, run per-cell; the C binary is the spec.  The C's own
    overflow asserts passed on every cell (it aborts on big_t overflow),
    so no oracle value is overflow-corrupted.  Grid: 26 success cells
    (incl. ENOUGH_LENS 852 and ENOUGH_DISTS 592 from inftrees.h:49-50),
    one cannot-handle cell (total printed, no table line), two hard
    refusals.  native_compute is the trusted evaluator (oracle role).
    R63 scaffolding (g6-bound lane, 2026-08-21). *)

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From Stdlib Require Import ZArith.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* FAST TEXT (fasttext-wave2, 2026-09-02): each cell is now checked by ONE kernel evaluation (`native_cast_no_check` /
   `vm_cast_no_check` of `eq_refl` at the cell's own RHS) instead of `native_compute. reflexivity.`, which evaluated the goal
   twice (tactic + the kernel's cast re-check). Statements untouched; the native evaluator keeps its oracle role (the kernel's
   NATIVEcast check IS the native evaluation). *)

(* SPLIT by tools/split_enough_cells.py: the cells live one per file. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Export
  EnoughRun_30_6_8 EnoughRun_30_6_15 EnoughRun_286_9_12 EnoughRun_286_9_15.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* PA probes: expect "Closed under the global context" on all three. *)
Print Assumptions c_286_9_15.
Print Assumptions c_30_6_15.
Print Assumptions enough_run.
