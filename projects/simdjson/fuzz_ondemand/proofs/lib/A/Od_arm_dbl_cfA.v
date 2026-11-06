(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Od_arm_dbl_swar Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_cpsA Od_tablesA Od_pow5A Od_arm_dbl_defsA Od_arm_dbl_exitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Lemma apow5_addr : forall x, (0 <= x < 18446744073709551616)%Z -> (x < 309 \/ 18446744073709551274 <= x)%Z ->
  exists t, (-342 <= t <= 308)%Z /\
    Z_to_bv 64 (8 * (bv_swrap 32 (2 * x) mod 18446744073709551616) + 150848) = Z_to_bv 64 (150848 + 16 * t).
Proof.
  intros x Hx [L|G].
  - exists x. split; [lia|]. rewrite swrap32_small by lia. rewrite Z.mod_small by lia. f_equal. lia.
  - exists (x - 18446744073709551616)%Z. split; [lia|].
    set (t := (x - 18446744073709551616)%Z). assert (Ex : x = (t + 18446744073709551616)%Z) by (unfold t; lia).
    assert (Ht : (-342 <= t <= -1)%Z) by lia. clearbody t. subst x.
    assert (SW : bv_swrap 32 (2 * (t + 18446744073709551616)) = (2 * t)%Z).
    { rewrite bv_swrap32. unfold swrap32. Z.div_mod_to_equations. lia. }
    rewrite SW.
    replace ((2 * t) mod 18446744073709551616)%Z with (2 * t + 18446744073709551616)%Z by (apply Z.mod_unique with (q := (-1)%Z); lia).
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
    replace (8 * (2 * t + 18446744073709551616) + 150848)%Z with ((150848 + 16 * t) + 8 * 18446744073709551616)%Z by lia.
    apply Z_mod_plus_full.
Qed.

Lemma cf_range : forall t2 x, (0 <= x < 18446744073709551616)%Z ->
  Z.lor t2 (Z.b2z ((x + -309) mod 18446744073709551616 <? 18446744073709550965)) = 0%Z ->
  (x < 309 \/ 18446744073709551274 <= x)%Z.
Proof.
  intros t2 x Hx H. apply Z.lor_eq_0_iff in H. destruct H as [_ H].
  destruct (Z.ltb_spec ((x + -309) mod 18446744073709551616) 18446744073709550965) as [L|G]; cbn [Z.b2z] in H; [discriminate|].
  clear H. Z.div_mod_to_equations. lia.
Qed.

Section ArmDblCfA.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation DINV st neg j0 j8 j104 j112 v176 m1 := (DINVa E st neg j0 j8 j104 j112 v176 m1).

  Lemma dinv_success : forall (Q : machine_state -> Prop) st neg j0 j8 j104 j112 v176
      xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DINV st neg j0 j8 j104 j112 v176 m1 -> od_plus_k E Q st ->
    evt asegs Q (ODST E 0x99640 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HK.
    eapply (dbl_success E OK Q st); [exact HLAST | exact HH | exact FRM | exact INV | | | | exact HK].
    - intros mm Hm. forget_C8 Hm. eauto 8.
    - intros mm Hm. forget_C8 Hm. eauto 8.
    - intros mm Hm. forget_C8 Hm. eauto 8.
  Qed.

  Lemma dbl_slow : forall (Q : machine_state -> Prop) st neg q0 j0 j8 j104 j112 v176
      xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xF xfc m1,
    frm0 xfc -> DINV st neg j0 j8 j104 j112 v176 m1 -> od_slow_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (0 <= tokI bs idxs (o_pos st) <= o_len E)%Z ->
    evt asegs Q (ODST E 0x99488 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0)) xt3 xt4 xF xfc m1).
  Proof using OK.
    intros until m1. intros FRM INV HS NGR Hq0 TR.
    dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
    dstep. dstep. dstep. dstep.
    eapply evt_eq; [| eapply HS; [exact FRM | dbl_close_od]].
    unfold OD_FROMCH. od_st_eq.
  Qed.

  Local Ltac cf_K Q st neg q0 w3 t EA HLAST HH FRM INV2 HK HS NGR Hq0 TR pc :=
    lazymatch pc with
    | 0x99640%Z => first [ eapply evt_eq; [| eapply (dinv_success Q st neg); [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK]]; od_st_eq
                         | fail 100 "cut" pc ]
    | 0x99488%Z => first [ eapply evt_eq; [| eapply (dbl_slow Q st neg q0); [exact FRM | exact INV2 | exact HS | exact NGR | exact Hq0 | exact TR]]; od_st_eq
                         | fail 100 "cut" pc ]
    | 0x994ec%Z => first [ rewrite EA; ddata w3; dstep; dwalkv ltac:(cf_K Q st neg q0 w3 t EA HLAST HH FRM INV2 HK HS NGR Hq0 TR) | fail 100 "cut" pc ]
    | 0x994f8%Z => first [ replace (Z_to_bv 64 (150848 + 16 * t + 5472)) with (Z_to_bv 64 (150848 + (16 * t + 5472))) by (f_equal; lia);
                           dstep; dwalkv ltac:(cf_K Q st neg q0 w3 t EA HLAST HH FRM INV2 HK HS NGR Hq0 TR) | fail 100 "cut" pc ]
    | 0x995b8%Z => first [ replace (Z_to_bv 64 (150848 + 16 * t + 5480)) with (Z_to_bv 64 (150848 + (16 * t + 5480))) by (f_equal; lia);
                           dstep; dwalkv ltac:(cf_K Q st neg q0 w3 t EA HLAST HH FRM INV2 HK HS NGR Hq0 TR) | fail 100 "cut" pc ]
    end.

  Lemma dbl_cf_c : forall (Q : machine_state -> Prop) st neg q0 (w3 : word) j0 j8 j104 j112 v176
      xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt4 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DINV st neg j0 j8 j104 j112 v176 m1 ->
    od_plus_k E Q st -> od_slow_k E Q st ->
    dbl_pos E st neg q0 ->
    (bv_unsigned w3 < 309 \/ 18446744073709551274 <= bv_unsigned w3)%Z ->
    evt asegs Q (ODST E 0x994bc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0)) w3 xt4 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HK HS [NGR Hq0] RW.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (bv_unsigned_in_range 64 w3) as R3. unfold bv_modulus in R3. cbn in R3.
    destruct (apow5_addr (bv_unsigned w3) R3 RW) as (t & Ht & EA).
    destruct (apow5_read m1 (16 * t + 5472) MI ltac:(lia) ltac:(lia)) as [pv0 RD0].
    destruct (apow5_read m1 (16 * t + 5480) MI ltac:(lia) ltac:(lia)) as [pv1 RD1].
    ddata xa5. ddata pv0. ddata pv1.
    dwalkv ltac:(cf_K Q st neg q0 w3 t EA HLAST HH FRM INV2 HK HS NGR Hq0 TR).
  Qed.

  Theorem dbl_cf : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> od_slow_k E Q st -> dbl_T_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HS. unfold dbl_T_k.
    intros neg q0 r j0 j8 j104 j112 v176 xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xF xfc m1 PS Hr FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK r) as Rc.
    pose proof (tokB_read m1 E r BUFRO ltac:(lia)) as RB.
    set (c := B bs r) in *.
    pose proof (asown_read m1 c MI Rc) as RT. unfold AT_SOWN in RT.
    pose proof (osown_range c) as RTR.
    pose proof (bv_unsigned_in_range 64 xt3) as R3. unfold bv_modulus in R3. cbn in R3.
    ddata xa5.
    dwalkk ltac:(fun pc => lazymatch pc with
      | 0x98e3c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                             apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                           | fail 100 "cut" pc ]
      | 0x99488%Z => first [ eapply evt_eq; [| eapply (dbl_slow Q st neg q0); [exact FRM | exact INV2 | exact HS | exact NGR | exact Hq0 | exact TR]]; od_st_eq
                           | fail 100 "cut" pc ]
      | 0x994bc%Z => first [ lazymatch goal with KBR : Z.lor _ (Z.b2z _) = 0%Z |- _ =>
                               eapply evt_eq; [| eapply (dbl_cf_c Q st neg q0 xt3);
                                                 [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK | exact HS | exact PS | exact (cf_range _ _ R3 KBR)]];
                               od_st_eq end
                           | fail 100 "cut" pc ]
      end).
  Qed.
End ArmDblCfA.
