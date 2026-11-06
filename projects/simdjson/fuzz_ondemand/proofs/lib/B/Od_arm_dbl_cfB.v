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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_tablesB Od_arm_dbl_defsB Od_arm_dbl_slowB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Lemma cf_range : forall t2 x, (0 <= x < 18446744073709551616)%Z ->
  Z.lor t2 (Z.b2z ((x + -309) mod 18446744073709551616 <? 18446744073709550965)) = 0%Z ->
  (x < 309 \/ 18446744073709551274 <= x)%Z.
Proof.
  intros t2 x Hx H. apply Z.lor_eq_0_iff in H. destruct H as [_ H].
  destruct (Z.ltb_spec ((x + -309) mod 18446744073709551616) 18446744073709550965) as [L|G]; cbn [Z.b2z] in H; [discriminate|].
  clear H. Z.div_mod_to_equations. lia.
Qed.

Section ArmDblCfB.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Theorem dbl_cf_front : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> od_slow_k E Q st -> dbl_C_k E Q st -> dbl_T_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HS HC. unfold dbl_T_k.
    intros neg q0 r v4 xra xt1 xt2 xa1 xa3 xa6 xs6 xs10 xt3 xt4 xt6 xF xfc m1 PS SG Hr FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK r) as R0.
    pose proof (tokB_read m1 E r BUFRO ltac:(lia)) as RB0.
    set (c := B bs r) in *.
    pose proof (bsown_read m1 c MI ltac:(lia)) as RT. pose proof (osown_range c) as RS. unfold BT_SOWN in RT.
    pose proof (bv_unsigned_in_range 64 xt1) as RT1. unfold bv_modulus in RT1. cbn in RT1.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    ostep. ostep. ostep. ostep. if_false. ostep. ostep. ostep. odnorm. ostep. ostep. dgok. ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. ostep. dgok. ostep.
    if_cases KT; try clear KT.
    -
      eapply evt_eq; [| eapply (HK0 st)]; [od_st_eq| | exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      clear RB0 RT.
      ostep. ostep. ostep. ostep.
      if_cases KR; zify_cond KR.
      +
        clear KR.
        eapply evt_eq; [| eapply (dbl_slow E OK Q st neg q0 v4); [exact HH| exact FRM| exact INV2| exact HS| exact PS| exact SG]]. od_st_eq.
      + pose proof (cf_range _ _ RT1 KR) as CR. clear KR.
        eapply evt_eq; [| eapply (HC neg q0 v4 xt1 xa6); [exact PS| exact SG| exact CR| exact FRM| exact INV2]]. od_st_eq.
  Qed.
End ArmDblCfB.
