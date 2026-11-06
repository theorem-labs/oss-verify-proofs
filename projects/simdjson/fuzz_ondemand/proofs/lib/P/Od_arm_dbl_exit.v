(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk Od_fromch Od_arm_dbl_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section ArmDblExit.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma dbl_success : forall (Q : machine_state -> Prop) st (neg : Z) w0 w8 j56 j64 j72 j80 j128 j136
      xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc ->
    DBLINVc E st [C8 w0; C8 w8; C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))] [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)]
                 [CB 8 j128; CB 8 j136] m1 ->
    od_plus_k E Q st ->
    evt psegs Q (ODST E 0x28418 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HAL & HB).
    dbl_open_inv INV. od_env OK.
    zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply (HK (consume 1 st)); [| exact FRM| dbl_close_od].
    apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_scalar.
  Qed.

  Hypothesis HFROMCH : fromch_stmt_g psegs OD_FROMCH OD_GTOP.

  Lemma dbl_slow : forall (Q : machine_state -> Prop) st (neg q0 : Z) w0 w8 w16 j56 j64 j72 j80 j128 j136
      xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc ->
    DBLINVc E st [C8 w0; C8 w8; C8 w16] [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)] [CB 8 j128; CB 8 j136] m1 ->
    od_plus_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z ->
    evt psegs Q (ODST E 0x2849c xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).
  Proof using OK HFROMCH.
    intros until m1. intros HLAST HH FRM INV HK NGR Hq0.
    pose proof HH as (HP & HD & HE & HAL & HB).
    dbl_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    set (off := tokI bs idxs (o_pos st)) in *.
    assert (LO0 : (0 <= o_lo E)%Z) by (destruct ST as [? _]; assumption).
    zstep. zstep. zstep. zstep.
    pose proof HFROMCH as HS. unfold fromch_stmt_g in HS.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HS with (A := o_BUF E) (off := off) (stop := blen bs) (lo := o_lo E) (txt := padded_bytes bs) (b := Z_to_bv 8 0)];
        [ num_st_eq | .. ]; rewrite ?unsigned_lit by lia; unfold OD_GTOP, FF_STACK, SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK, NUM_TXT_MAX;
        [ exact MI | exact FRM | exact ST | lia | lia | exact BUFRO | lia | lia | lia | | ].
      - replace (Z_to_bv 8 0) with (Z_to_bv 8 (B bs (blen bs))) by (rewrite B_pad by lia; reflexivity).
        apply nth_error_padded. lia.
      - vm_compute. reflexivity. }
    cbv beta. intros ms' P. unfold ff_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & -> & FRM3 & MUc & WMc & MI3 & ST3).
    rewrite !unsigned_lit in MUc, ST3 by lia. unfold FF_STACK, SPATH_STACK, NDC_STACK, P5_STACK, LM_STACK in MUc.
    clear ST.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call psegs mo mn MUc WMc end.
    clear MUc WMc MI HS.
    num_ret_pc.
    zstep. zstep. zstep. zstep. zstep. zstep.
    match goal with |- context [bword ?f] => set (flag := f); clearbody flag end.
    destruct flag; unfold bword; zstep.
    - if_true.
      apply (HK st); [| exact FRM| dbl_close_od].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    - if_false. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_eq; [| eapply (dbl_success Q st neg); [exact HLAST | exact HH | exact FRM | dbl_close_inv | exact HK]] end.
      od_st_eq.
  Qed.
End ArmDblExit.
