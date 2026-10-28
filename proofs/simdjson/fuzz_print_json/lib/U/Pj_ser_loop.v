(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_ser_loop_defs Pj_ser_ends Pj_ser_disp Pj_ser_head.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length]; lia]
  | |- _ => reflexivity
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

  Theorem loop_closed : rmalloc_stmt -> rfree_stmt ->
    forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (D : nat),
    senv_ok E -> exit_K E Q ->
    (forall f k, head_stmt E Q D f -> aval_stmt E Q D f -> open_stmt E Q D f k) ->
    str_stmt -> i64_stmt -> u64_stmt -> dbl_stmt -> true_stmt -> false_stmt -> null_stmt -> key_stmt ->
    forall f, head_stmt E Q D f.
  Proof.
    intros HM HF E Q D OK KX OPEN PSTR PI64 PU64 PDBL PTRUE PFALSE PNULL PKEY.
    induction f as [|f IH].
    - unfold head_stmt. intros d0 ks i i2 c c2 after isobj st s m F fc e64 e72 e80 spill xs3 xs8 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
             HF0 HD HL KR HIT HR HAF HI HC HSM FRM ACC.
      exfalso. pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & _). pose proof (item_ok_lt E _ _ _ _ _ _ HIT) as LT. lia.
    - pose proof (aval_proof HM HF E Q D f OK KX IH) as AV.
      pose proof (disp_proof E Q D f OK AV (OPEN f false IH AV) (OPEN f true IH AV) PSTR PI64 PU64 PDBL PTRUE PFALSE PNULL) as DISP.
      exact (head_proof HM HF E Q D f OK DISP PKEY).
  Qed.

End WithCeiling0.
