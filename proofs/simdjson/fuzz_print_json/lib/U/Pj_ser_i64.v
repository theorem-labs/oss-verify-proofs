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
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_defs Pj_kit Pj_copy Pj_grow Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_num_defs Pj_itoa Pj_ser_ncalls.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma int_arm : forall (pc hpc r1 r2 r3 : Z),
    (pc = 0x3e2f4 /\ hpc = PJ_ITOA_S /\ r1 = 0x3e304 /\ r2 = 0x3e310) \/ (pc = 0x3e660 /\ hpc = PJ_ITOA_U /\ r1 = 0x3e670 /\ r2 = 0x3e67c) ->
    forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte) (st : sbst) (s : PState) (m : mem)
           (F : bvmap 5 word) (fc : bv 32) (i dp A : Z)
           (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> frm0 fc ->
    1 <= i -> i + 1 < e_n E ->
    sb_size st <= A -> A + 20 <= PJ_OUTMAX (e_len E) ->
    av_K E Q e64 e72 e80 isobj PJ_AV0 (i + 1) dp (A + 20) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (LST E pc i dp (Z_to_bv 64 PJ_TMASK) (Z_to_bv 64 PJ_RBR56) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xt3 xt4 xt5 xt6 F fc m).
  Proof.
    intros pc hpc r1 r2 r3 HPC E Q e64 e72 e80 spill isobj st s m F fc i dp A xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6
           OK HSM FRM I1 I2 ACC BUD HK.
    ser_env OK.
    pose proof OK as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [D8 T8]].
    pose proof (ser_ranges _ _ _ _ _ _ _ _ _ OK HSM) as (TP0 & TP1 & _ & _).
    pose proof HSM as HSM0.
    ser_open HSM OK.
    pose proof (doc_cells_mu E _ _ _ _ OK HREF MU WM) as DOCC.
    pose proof (tape_read_mu E _ _ _ _ (i + 1) OK HREF MU WM ltac:(lia)) as RD.
    destruct HPC as [(-> & -> & -> & ->) | (-> & -> & -> & ->)].
    all:
         zstep; step; step; step.
    all: eapply tape_ref_call; [exact DOCC| exact T8| lia| lia| lia| lia| reflexivity|].
    all:
         step; zstep; step.
    all: clear RD DOCC;
         set (wd := Z_to_bv 64 (e_T E (i + 1)));
         pose proof (bv_unsigned_in_range 64 wd) as WR; unfold bv_modulus in WR; cbn in WR;
         rewrite <- (Z_to_bv_bv_unsigned wd); set (w := bv_unsigned wd) in *; clearbody w; clear wd.
    all: ser_close HSM1 OK.
    1: eapply (ser_itoa PJ_ITOA_S E Q e64 e72 e80 spill isobj _ s) with (rpc := 0x3e310); [right; reflexivity| exact OK| exact HSM1| lia| lia| reflexivity|].
    2: eapply (ser_itoa PJ_ITOA_U E Q e64 e72 e80 spill isobj _ s) with (rpc := 0x3e67c); [left; reflexivity| exact OK| exact HSM1| lia| lia| reflexivity|].
    all: intros m2 n yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM2 HN.
    all:   step.
    all: eapply (num_tail HM HF E Q e64 e72 e80 spill isobj st s m2 F fc (i + 1) dp A 20 n); try eassumption; lia.
  Qed.

  Theorem i64_proof : i64_stmt.
  Proof.
    unfold i64_stmt. intros. eapply (int_arm 0x3e2f4 PJ_ITOA_S 0x3e304 0x3e310 0); [left; repeat split; reflexivity| eassumption ..].
  Qed.

  Theorem u64_proof : u64_stmt.
  Proof.
    unfold u64_stmt. intros. eapply (int_arm 0x3e660 PJ_ITOA_U 0x3e670 0x3e67c 0); [right; repeat split; reflexivity| eassumption ..].
  Qed.
End Proofs.
End WithCeiling0.
