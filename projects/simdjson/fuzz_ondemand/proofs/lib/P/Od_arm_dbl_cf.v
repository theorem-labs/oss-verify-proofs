(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk Od_fromch Od_pow5 Od_arm_dbl_defs Od_arm_dbl_exit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma Z_to_bv64_mod : forall a b k, (a = b + k * 18446744073709551616)%Z -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
  intros a b k ->. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  apply Z_mod_plus_full.
Qed.

Lemma pow5_addr : forall x, (0 <= x < 18446744073709551616)%Z -> (x < 309 \/ 18446744073709551274 <= x)%Z ->
  exists t, (-342 <= t <= 308)%Z /\
    Z_to_bv 64 (Z.shiftl (bv_swrap 32 (Z.shiftl x 1) mod 18446744073709551616) 3 + 88184) = Z_to_bv 64 (88184 + 16 * t).
Proof.
  intros x Hx [L|G].
  - exists x. split; [lia|]. rewrite !Z.shiftl_mul_pow2 by lia. rewrite swrap32_small by lia. rewrite Z.mod_small by lia. f_equal. lia.
  - exists (x - 18446744073709551616)%Z. split; [lia|].
    set (t := (x - 18446744073709551616)%Z). assert (Ex : x = (t + 18446744073709551616)%Z) by (unfold t; lia).
    assert (Ht : (-342 <= t <= -1)%Z) by lia. clearbody t. subst x.
    rewrite !Z.shiftl_mul_pow2 by lia.
    assert (SW : bv_swrap 32 ((t + 18446744073709551616) * 2 ^ 1) = (2 * t)%Z).
    { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
      replace ((t + 18446744073709551616) * 2 ^ 1 + 2147483648)%Z with ((2 * t + 2147483648) + 8589934592 * 4294967296)%Z by lia.
      rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia. }
    rewrite SW.
    replace ((2 * t) mod 18446744073709551616)%Z with (2 * t + 18446744073709551616)%Z by (apply Z.mod_unique with (q := (-1)%Z); lia).
    apply (Z_to_bv64_mod _ _ 8). lia.
Qed.

Lemma opow5_len : Z.of_nat (length (u64s OD_POW5_WORDS)) = 10416%Z.
Proof. rewrite u64s_length. unfold OD_POW5_WORDS. rewrite length_map. vm_compute. reflexivity. Qed.

Lemma opow5_read : forall (m : mem) t h, mem_inv psegs m -> (-342 <= t <= 308)%Z -> (h = 0 \/ h = 8)%Z ->
  exists v, ov_read_bytes psegs m (wa (88184 + 16 * t + (1376 + h))) 8 = Some (le8 v).
Proof.
  intros m t h MI Ht Hh. eexists.
  apply (bytes_read8_at psegs m OT_POW5 (u64s OD_POW5_WORDS) (16 * t + 5472 + h)%Z); [apply opow5_at; exact MI | lia | rewrite opow5_len; lia |].
  unfold wa, OT_POW5. f_equal. lia.
Qed.

Section ArmDblCf.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis HFROMCH : fromch_stmt_g psegs OD_FROMCH OD_GTOP.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation DINV st neg j56 j64 j72 j80 j128 j136 m1 :=
    (DBLINVc E st [C8 (Z_to_bv 64 DBL_K0); C8 (Z_to_bv 64 DBL_K8); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))]
                  [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)] [CB 8 j128; CB 8 j136] m1).

  Definition dbl_C_k (Q : machine_state -> Prop) (st : ost) : Prop :=
    forall neg q0 (w1 : word) j56 j64 j72 j80 j128 j136 xt0 xt2 xa0 xa2 xa3 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
      (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z ->
      (bv_unsigned w1 < 309 \/ 18446744073709551274 <= bv_unsigned w1)%Z -> frm0 xfc ->
      DINV st neg j56 j64 j72 j80 j128 j136 m1 ->
      evt psegs Q (ODST E 0x282ec xt0 w1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 (Z_to_bv 64 DBL_K8) xa5 xa6 xa7
                        (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).

  Lemma dbl_cf_d : forall (Q : machine_state -> Prop) st neg q0 j56 j64 j72 j80 j128 j136
      xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    DINV st neg j56 j64 j72 j80 j128 j136 m1 -> od_plus_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z ->
    evt psegs Q (ODST E 0x283f8 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).
  Proof using OK HFROMCH.
    intros until m1. intros HLAST HH FRM INV HK NGR Hq0.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K; clear K.
    - eapply evt_eq; [| eapply (dbl_slow E OK HFROMCH Q st neg q0); [exact HLAST | exact HH | exact FRM | exact INV | exact HK | exact NGR | exact Hq0]].
      od_st_eq.
    - eapply evt_eq; [| eapply (dbl_success E OK Q st neg); [exact HLAST | exact HH | exact FRM | exact INV | exact HK]]. od_st_eq.
  Qed.

  Lemma dbl_cf_head : forall (Q : machine_state -> Prop) st,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_C_k Q st -> dbl_T_k E Q st.
  Proof using OK HFROMCH.
    intros Q st HLAST HH HK HC. unfold dbl_T_k.
    intros neg q0 c j56 j64 j72 j80 j128 j136 xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt4 xt5 xF xfc m1 NGR Hq0 Rc FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    assert (INV2 := INV). dbl_open_inv INV. od_env OK.
    pose proof (osown_read m1 c MI Rc) as RT. unfold OT_SOWN in RT.
    pose proof (osown_range c) as RTR.
    zstep. zstep. zstep. zstep. odnorm. zstep.
    if_cases K; zify_cond K.
    { apply (HK st); [| exact FRM| dbl_close_od].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none. }
    zstep. zstep. zstep. zstep.
    if_cases K1; zify_cond K1.
    {
      eapply evt_eq; [| eapply (dbl_slow E OK HFROMCH Q st neg q0); [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK | exact NGR | exact Hq0]].
      od_st_eq. }
    assert (RW : (bv_unsigned xt1 < 309 \/ 18446744073709551274 <= bv_unsigned xt1)%Z).
    { pose proof (bv_unsigned_in_range 64 xt1) as R1. unfold bv_modulus in R1. cbn in R1.
      pose proof (bv_unsigned_in_range 64 xt4) as R4. unfold bv_modulus in R4. cbn in R4.
      revert K1. destruct (Z.ltb_spec ((bv_unsigned xt1 + -309) mod 18446744073709551616) 18446744073709550965) as [L|G]; cbn [Z.b2z]; intros K1.
      - exfalso. rewrite ?Z.mod_small in K1 by (split; [apply Z.lor_nonneg; lia | ]; lia).
        apply Z.lor_eq_0_iff in K1. lia.
      - destruct (Z_lt_ge_dec (bv_unsigned xt1) 309) as [A|A]; [left; exact A | right; rewrite Z.mod_small in G by lia; lia]. }
    clear K1.
    zstep. zstep. if_cases K2; zify_cond K2.
    { eapply evt_eq; [| eapply (dbl_success E OK Q st neg); [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK]]. od_st_eq. }
    zstep. zstep. zstep. zstep. zstep. zstep.
    if_cases K3; zify_cond K3.
    { eapply evt_eq; [| eapply (dbl_success E OK Q st neg); [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK]]. od_st_eq. }
    clear K2 K3.
    eapply evt_eq; [| eapply (HC neg q0 xt1); [exact NGR | exact Hq0 | exact RW | exact FRM | exact INV2]].
    od_st_eq.
  Qed.

  Lemma dbl_cf_c3 : forall (Q : machine_state -> Prop) st neg q0 j56 j64 j72 j80 j128 j136
      xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    DINV st neg j56 j64 j72 j80 j128 j136 m1 -> od_plus_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z ->
    evt psegs Q (ODST E 0x283b8 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).
  Proof using OK HFROMCH.
    intros until m1. intros HLAST HH FRM INV HK NGR Hq0.
    assert (KD : forall xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5,
      evt psegs Q (ODST E 0x283f8 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1)).
    { intros. eapply (dbl_cf_d Q st neg q0); eassumption. }
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K0, DBL_K8 in *.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K; clear K.
    { eapply evt_eq; [| eapply (dbl_success E OK Q st neg); [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK]]. od_st_eq. }
    zstep. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K; clear K; [eapply evt_eq; [| eapply KD]; od_st_eq|].
    zstep. if_cases K; zify_cond K; clear K; [eapply evt_eq; [| eapply KD]; od_st_eq|].
    zstep. zstep. if_cases K; zify_cond K; clear K; [| eapply evt_eq; [| eapply KD]; od_st_eq].
    zstep. zstep. if_cases K; zify_cond K; clear K.
    - zstep. zstep. zstep. zstep. zstep. eapply evt_eq; [| eapply KD]; od_st_eq.
    - zstep. zstep. zstep. zstep. zstep. zstep. eapply evt_eq; [| eapply KD]; od_st_eq.
  Qed.

  Lemma dbl_cf_c2 : forall (Q : machine_state -> Prop) st neg q0 (t : Z) j56 j64 j72 j80 j128 j136
      xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    DINV st neg j56 j64 j72 j80 j128 j136 m1 -> od_plus_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (-342 <= t <= 308)%Z ->
    evt psegs Q (ODST E 0x28380 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 (Z_to_bv 64 (88184 + 16 * t)) xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).
  Proof using OK HFROMCH.
    intros until m1. intros HLAST HH FRM INV HK NGR Hq0 Ht.
    assert (KC3 : forall xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5,
      evt psegs Q (ODST E 0x283b8 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1)).
    { intros. eapply (dbl_cf_c3 Q st neg q0); eassumption. }
    dbl_open_inv INV. od_env OK. unfold DBL_K0, DBL_K8 in *.
    destruct (opow5_read m1 t 0 MI Ht (or_introl eq_refl)) as [pv0 RD0].
    destruct (opow5_read m1 t 8 MI Ht (or_intror eq_refl)) as [pv8 RD8].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K; clear K; [eapply evt_eq; [| eapply KC3]; od_st_eq|].
    zstep. zstep. zstep. zstep. zstep.
    eapply evt_eq; [| eapply KC3]; od_st_eq.
  Qed.

  Theorem dbl_cf_c1 : forall (Q : machine_state -> Prop) st,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_C_k Q st.
  Proof using OK HFROMCH.
    intros Q st HLAST HH HK. unfold dbl_C_k.
    intros neg q0 w1 j56 j64 j72 j80 j128 j136 xt0 xt2 xa0 xa2 xa3 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1 NGR Hq0 RW FRM INV.
    assert (KC2 : forall (t : Z) xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa6 xa7 xt3 xt4 xt5, (-342 <= t <= 308)%Z ->
      evt psegs Q (ODST E 0x28380 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 (Z_to_bv 64 (88184 + 16 * t)) xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1)).
    { intros. eapply (dbl_cf_c2 Q st neg q0); eassumption. }
    dbl_open_inv INV. od_env OK. unfold DBL_K0, DBL_K8 in *.
    pose proof (bv_unsigned_in_range 64 w1) as R1. unfold bv_modulus in R1. cbn in R1.
    destruct (pow5_addr (bv_unsigned w1) R1 RW) as (t & Ht & EA).
    zstep. zstep. zstep. zstep.
    do 12 zstep.
    rewrite EA. clear EA.
    do 21 zstep.
    eapply evt_eq; [| eapply (KC2 t); exact Ht]. od_st_eq.
  Qed.

  Theorem dbl_cf : dbl_cf_stmt E.
  Proof using OK HFROMCH.
    unfold dbl_cf_stmt. intros Q st HLAST HH HK.
    apply (dbl_cf_head Q st HLAST HH HK). apply (dbl_cf_c1 Q st HLAST HH HK).
  Qed.
End ArmDblCf.
