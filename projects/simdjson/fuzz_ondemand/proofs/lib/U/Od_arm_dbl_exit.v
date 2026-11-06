(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Sj_num_iface Sj_num_kitu Od_fromch Od_arm_dbl_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ArmDblExit.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma dbl_success : forall (Q : machine_state -> Prop) st v24 v32 j40 j48 w88 w168
      xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc ->
    DBLINVu E st [C8 v24; C8 v32; CB 8 j40; CB 8 j48] [C8 w88] [C8 w168] m1 ->
    od_plus_k E Q st ->
    evt usegs Q (ODST E 0x290b4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros until m1. intros HLAST HH FRM INV HK.
    pose proof HH as (HP & HD & HE & HAL & HB).
    dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    set (off := tokI bs idxs (o_pos st)) in *.
    assert (A8 : ((bv_unsigned (o_sp E) + -272) mod 8 = 0)%Z) by (apply od_sp_al8; [exact USP| reflexivity]).
    assert (A4 : ((o_IDX E + 4 * o_pos st) mod 4 = 0)%Z) by (apply od_idx_al4; lia).
    dwalk ltac:(fun pc => lazymatch pc with
      | 0x28750%Z => first [
          od_cur_mem ltac:(fun mm => pose proof (tokI_read mm E ws (o_pos st) ltac:(eassumption) (conj IDXL IDXF) ltac:(lia)) as RD3);
          fold off in RD3;
          dstep; dwalk ltac:(fun pc => lazymatch pc with
            | 0x2877c%Z => first [ apply (HK (consume 1 st)); [| exact FRM| dbl_close_od];
                                   apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_scalar
                                 | fail 100 "cut" pc ]
            end)
        | fail 100 "cut" pc ]
      | 0x2877c%Z => fail 100 "PLUS reached early"
      end).
  Qed.

  Hypothesis HFROMCH : fromchu_stmt_g usegs OD_FROMCH OD_GTOP.

  Lemma dbl_slow : forall (Q : machine_state -> Prop) st (neg q0 : Z) v24 v32 j40 j48 w88 w168
      xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc ->
    DBLINVu E st [C8 v24; C8 v32; CB 8 j40; CB 8 j48] [C8 w88] [C8 w168] m1 ->
    od_plus_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z ->
    evt usegs Q (ODST E 0x2905c xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HFROMCH.
    intros until m1. intros HLAST HH FRM INV HK [NGR NV] Hq0.
    pose proof HH as (HP & HD & HE & HAL & HB).
    dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    set (off := tokI bs idxs (o_pos st)) in *.
    assert (LO0 : (0 <= o_lo E)%Z) by (destruct ST as [? _]; assumption).
    pose proof (bv_unsigned_in_range 64 v24) as R24. unfold bv_modulus in R24. cbn in R24.
    dwalk ltac:(fun pc => lazymatch pc with
      | 0x2907c%Z => idtac
      end).
    dstep.
    pose proof HFROMCH as HS. unfold fromchu_stmt_g in HS.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HS with (A := o_BUF E) (off := off) (stop := blen bs) (lo := o_lo E) (txt := padded_bytes bs) (b := Z_to_bv 8 0)];
        [ num_st_eq | .. ]; rewrite ?unsigned_lit by lia;
        unfold OD_GTOP, FFU_STACK, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, NUM_TXT_MAX;
        [ exact MI | exact FRM | exact ST | lia | lia | | exact BUFRO | lia | lia | lia | lia | | ].
      - clear - USP. Z.div_mod_to_equations. lia.
      - replace (Z_to_bv 8 0) with (Z_to_bv 8 (B bs (blen bs))) by (rewrite B_pad by lia; reflexivity).
        apply nth_error_padded. lia.
      - vm_compute. reflexivity. }
    cbv beta. intros ms' P. unfold ffu_post_g in P.
    destruct P as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & F3 & fc3 & m3 & -> & FRM3 & MUc & WMc & MI3 & ST3).
    rewrite !unsigned_lit in MUc, ST3 by lia. unfold FFU_STACK, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MUc.
    clear ST.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call usegs mo mn MUc WMc end.
    clear MUc WMc MI HS.
    num_ret_pc.
    dstep. dstep. dstep. dstep. dstep.
    match goal with |- context [bword ?f] => set (flag := f); clearbody flag end.
    destruct flag; unfold bword; dstep.
    - if_false. dstep.
      apply (HK st); [| exact FRM| dbl_close_od].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    - if_true.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_eq; [| eapply (dbl_success Q st); [exact HLAST | exact HH | exact FRM | dbl_close_inv | exact HK]] end.
      od_st_eq.
  Qed.
End ArmDblExit.
