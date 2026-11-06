(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_arm_dbl_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Section ArmDblExitB.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma dbl_success_s : forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs10 xt3 xt4 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    od_plus_k E Q st ->
    evt bsegs Q (DBLCST E 0x9af70 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 (Z_to_bv 64 2) xt6 xF xfc m1).
  Proof using OK.
    intros Q st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs10 xt3 xt4 xt6 xF xfc m1 HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (HD2 : o_depth st = 2%Z) by lia.
    destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. rewrite HD2 in ITER.
    pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.

    ostep. ostep. if_true. ostep. ostep. ostep. ostep. if_false.

    ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. dgok. ostep. dgok. ostep. ostep. ostep. dgok. ostep. ostep. ostep. ostep. if_true.
    ostep. ostep. dgok. ostep. ostep. if_true. ostep. ostep. ostep. ostep.
    od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3).

    ostep. dgok. ostep. ual. ostep. dgok. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. ostep. dgok. ostep. ostep. ostep. unz. ostep. dgok.
    ostep. ostep. dgok. ostep. ostep. if_false. ostep. ostep. ostep.
    eapply evt_eq; [| eapply (HK0 (consume 1 st))]; [od_st_eq| | exact FRM| od_close_inv].
    apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
  Qed.

  Theorem dbl_resume : dbl_resume_stmt E.
  Proof using OK.
    unfold dbl_resume_stmt.
    intros Q st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH HK FRM INV.
    pose proof HH as (HP & HD & HE & HA & HB).
    assert (INV2 := INV).
    destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK.
    pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.

    dstep. dstep. dstep. dstep. dstep. dstep. dstep.
    if_cases KB; try clear KB.
    -
      eapply evt_eq; [| eapply (HK0 st)]; [od_st_eq| | exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      dstep.
      eapply evt_eq; [| eapply (dbl_success_s Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]]. od_st_eq.
  Qed.
End ArmDblExitB.
