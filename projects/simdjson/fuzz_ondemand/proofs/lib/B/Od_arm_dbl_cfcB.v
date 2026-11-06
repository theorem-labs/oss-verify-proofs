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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_tablesB Od_pow5B Od_arm_dbl_defsB Od_arm_dbl_slowB Od_arm_dbl_cfB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Lemma bpow5_idx : forall x, (0 <= x < 18446744073709551616)%Z -> (x < 309 \/ 18446744073709551274 <= x)%Z ->
  exists i, (0 <= i <= 650)%Z /\ bv_swrap 32 ((2 * x) mod 18446744073709551616 + 684) = (2 * i)%Z.
Proof.
  intros x Hx [L|G].
  - exists (x + 342)%Z. split; [lia|]. rewrite Z.mod_small by lia. rewrite swrap32_small by lia. lia.
  - exists (x - 18446744073709551616 + 342)%Z. split; [lia|].
    rewrite bv_swrap32. unfold swrap32. Z.div_mod_to_equations. lia.
Qed.
Lemma lor_2i_1 : forall i, (0 <= i)%Z -> Z.lor (2 * i) 1 = (2 * i + 1)%Z.
Proof.
  intros i Hi. apply (lor_disj (2 * i) 1 1); [lia | lia | | change (2 ^ 1)%Z with 2%Z; lia].
  change (2 ^ 1)%Z with 2%Z. rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.
Lemma lor_16i_8 : forall i, (0 <= i)%Z -> Z.lor (8 * (2 * i)) 8 = (16 * i + 8)%Z.
Proof.
  intros i Hi. rewrite (lor_disj (8 * (2 * i)) 8 4); [lia | lia | lia | | change (2 ^ 4)%Z with 16%Z; lia].
  change (2 ^ 4)%Z with 16%Z. replace (8 * (2 * i))%Z with (i * 16)%Z by lia. apply Z.mod_mul. lia.
Qed.

Section ArmDblCfcB.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma dbl_success_g : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs10 xt3 xt4 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    od_plus_k E Q st ->
    evt bsegs Q (DBLST E 0x9af70 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5 xs6 xs10
                       (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 (Z_to_bv 64 2) xt6 xF xfc m1).
  Proof using OK.
    intros Q st xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs10 xt3 xt4 xt6 xF xfc m1 HLAST HH FRM INV HK.
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

  Lemma dbl_cf_c4 : forall (Q : machine_state -> Prop) st neg q0 v4
      xra xt0 xt1 xt2 xa1 xa2 xa3 xa6 xa7 xs5 xs6 xs10 xt3 xt4 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    od_plus_k E Q st -> od_slow_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 ->
    evt bsegs Q (DBLST E 0x9af50 xra xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E + q0)) xa1 xa2 xa3 v4 (Z_to_bv 64 neg) xa6 xa7
                       (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192))
                       xt3 xt4 (Z_to_bv 64 2) xt6 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HK HS PS SG.
    ddata xa1. ddata xa2. ddata xa3.

    dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
    if_cases K1; try clear K1.
    - eapply evt_eq; [| eapply (dbl_slow E OK Q st neg q0 v4); [exact HH| exact FRM| exact INV| exact HS| exact PS| exact SG]]. od_st_eq.
    - eapply evt_eq; [| eapply (dbl_success_g Q st); [exact HLAST| exact HH| exact FRM| exact INV| exact HK]]. od_st_eq.
  Qed.

  Lemma dbl_cf_c3 : forall (Q : machine_state -> Prop) st neg q0 v4
      xra xt0 xt1 xt2 xa1 xa2 xa3 xa6 xa7 xs6 xs10 xt3 xt4 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    od_plus_k E Q st -> od_slow_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 ->
    evt bsegs Q (DBLST E 0x9af0c xra xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E + q0)) xa1 xa2 xa3 v4 (Z_to_bv 64 neg) xa6 xa7
                       (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 2) xs6 xs10 (Z_to_bv 64 (oa_F E + 192))
                       xt3 xt4 (Z_to_bv 64 2) xt6 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HK HS PS SG.
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.
    ddata xa1. ddata xa2. ddata xa3. ddata xa6. ddata xa7. ddata xt0. ddata xt1. ddata xt2. ddata xt3. ddata xt4. ddata xt6.

    dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
    if_cases K1; try clear K1.
    { eapply evt_eq; [| eapply (dbl_success_g Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]]. od_st_eq. }

    dstep. dstep. dstep. dstep. dstep.
    if_cases K2; try clear K2.
    { eapply evt_eq; [| eapply (dbl_cf_c4 Q st neg q0 v4); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HS| exact PS| exact SG]]. od_st_eq. }

    dstep. dstep.
    if_cases K3; try clear K3.
    { eapply evt_eq; [| eapply (dbl_cf_c4 Q st neg q0 v4); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HS| exact PS| exact SG]]. od_st_eq. }

    dstep. dstep.
    if_cases K4; try clear K4.
    -
      dstep. dstep.
      if_cases K5; try clear K5.
      +
        dstep. dstep. dstep. dstep. dstep. dstep. dstep.
        eapply evt_eq; [| eapply (dbl_cf_c4 Q st neg q0 v4); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HS| exact PS| exact SG]]. od_st_eq.
      +
        dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
        eapply evt_eq; [| eapply (dbl_cf_c4 Q st neg q0 v4); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HS| exact PS| exact SG]]. od_st_eq.
    - eapply evt_eq; [| eapply (dbl_cf_c4 Q st neg q0 v4); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HS| exact PS| exact SG]]. od_st_eq.
  Qed.

  Lemma dbl_cf_c1 : forall (Q : machine_state -> Prop) st neg q0 v4 (w1 w6 : word)
      xra xt2 xa1 xa2 xa3 xs6 xs10 xt3 xt4 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    od_plus_k E Q st -> od_slow_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 ->
    (bv_unsigned w1 < 309 \/ 18446744073709551274 <= bv_unsigned w1)%Z ->
    evt bsegs Q (DBLST E 0x9adbc xra (Z_to_bv 64 DBL_KT0) w1 xt2 (Z_to_bv 64 (o_BUF E + q0)) xa1 xa2 xa3 v4 (Z_to_bv 64 neg) w6
                       (Z_to_bv 64 DBL_KA7) (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 2) xs6 xs10 (Z_to_bv 64 (oa_F E + 192))
                       xt3 xt4 (Z_to_bv 64 2) xt6 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HK HS PS SG RW.
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof (bv_unsigned_in_range 64 w1) as R1. unfold bv_modulus in R1. cbn in R1.
    destruct (bpow5_idx (bv_unsigned w1) R1 RW) as (i & Hi & EA).
    destruct (bpow5_read m1 (8 * (2 * i)) MI ltac:(lia) ltac:(lia)) as [pv0 RD0].
    destruct (bpow5_read m1 (8 * (2 * i + 1)) MI ltac:(lia) ltac:(lia)) as [pv1 RD1].
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.
    ddata w6. ddata pv0. ddata pv1. ddata xa1. ddata xa2. ddata xa3. ddata xt2. ddata xt3. ddata xt4. ddata xt6.

    dstep0.
    if_cases K0; try clear K0.
    { eapply evt_eq; [| eapply (dbl_success_g Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]]. od_st_eq. }

    dstep0. dstep0.
    rewrite d_shl1, EA. ddata w1.
    dstep. dstep. dgok.

    dstep. dstep. dstep. dstep. dstep. dgok.

    dstep. dstep. dstep.
    ostep. ostep. if_true.

    dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
    dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
    dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
    dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
    clear RD0.
    if_cases K1; try clear K1.
    {
      dstep. dstep.
      eapply evt_eq; [| eapply (dbl_cf_c3 Q st neg q0 v4); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HS| exact PS| exact SG]]. od_st_eq. }

    dstep0. rewrite (lor_16i_8 i) by lia. dstep. dstep. dstep. dgok.

    dstep0. rewrite (lor_2i_1 i) by lia. dstep. dstep. dstep. dstep. ostep. ostep. if_true.

    dstep. dstep. dstep. dstep. dstep. dstep.
    eapply evt_eq; [| eapply (dbl_cf_c3 Q st neg q0 v4); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HS| exact PS| exact SG]]. od_st_eq.
  Qed.

  Theorem dbl_cf_c : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> od_slow_k E Q st -> dbl_C_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HS. unfold dbl_C_k.
    intros neg q0 v4 w1 w6 xra xt2 xa1 xa2 xa3 xs6 xs10 xt3 xt4 xt6 xF xfc m1 PS SG RW FRM INV.
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof (bv_unsigned_in_range 64 w1) as R1. unfold bv_modulus in R1. cbn in R1.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    dstep0. dstep0.
    if_cases K1; try clear K1.
    { eapply evt_eq; [| eapply (dbl_cf_c1 Q st neg q0 v4 w1 w6); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HS| exact PS| exact SG| exact RW]]. od_st_eq. }

    dstep0. dstep0. dstep0.
    if_cases K2; zify_cond K2.
    { clear K2. eapply evt_eq; [| eapply (dbl_cf_c1 Q st neg q0 v4 w1 w6); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HS| exact PS| exact SG| exact RW]]. od_st_eq. }

    dstep0.
    if_cases K3; zify_cond K3.
    -
      assert (W1 : (18446744073709551594 <= bv_unsigned w1)%Z) by (clear - K2 K3 R1; Z.div_mod_to_equations; lia). clear K2 K3.
      dstep0. dstep0. dstep0. dstep0. dstep0. dstep0.
      rewrite d_shl3.
      if_cases KG; zify_cond KG; [| exfalso; clear - KG W1 R1; Z.div_mod_to_equations; lia]. clear KG.
      eapply evt_eq; [| eapply (dbl_success_g Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]]. od_st_eq.
    -
      assert (W1 : (bv_unsigned w1 <= 22)%Z) by (clear - K2 K3 R1; Z.div_mod_to_equations; lia). clear K2 K3.
      dstep0. dstep0. dstep0. dstep0. dstep0.
      rewrite d_shl3.
      if_cases KG; zify_cond KG; [| exfalso; clear - KG W1 R1; Z.div_mod_to_equations; lia]. clear KG.
      eapply evt_eq; [| eapply (dbl_success_g Q st); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK]]. od_st_eq.
  Qed.

  Theorem dbl_cf : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> od_slow_k E Q st -> dbl_T_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HS.
    apply (dbl_cf_front E OK Q st HLAST HH HK HS). apply (dbl_cf_c Q st HLAST HH HK HS).
  Qed.
End ArmDblCfcB.
