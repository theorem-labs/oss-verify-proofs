(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnModel BnMInv BgState BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX BnNumBits.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_num_bits_word.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnRep W_small BnUKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_GET_FLAGS : Z := 0xfdefc.
Definition BN_IS_ODD : Z := 0xffb40.
Definition BN_IS_ONE : Z := 0xff9c4.
Definition BN_ABS_IS_WORD : Z := 0xff958.
Definition BN_IS_BIT_SET : Z := 0xff340.
Definition BN_VALUE_ONE : Z := 0xfdbbc.

Definition CONST_ONE : Z := 0x2d0170.

Lemma wlimbs_nth : forall buf (i : nat), (i < length buf)%nat -> nth_error (wlimbs buf) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i buf 0)).
Proof. intros buf i H. rewrite Nat2Z.id. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' buf 0) by lia. reflexivity. Qed.

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Lemma u64arr_read_lo4 : forall m A x (l : list Z) a,
  u64arr bgusegs m A (wlimbs (x :: l)) -> a = wa A -> ov_read_bytes bgusegs m a 4 = Some (le4 (Z_to_bv 64 x)).
Proof.
  intros m A x l a [Hb _] ->.
  pose proof (bytes_at_read bgusegs m A (u64s (wlimbs (x :: l))) 0 4 Hb ltac:(lia)) as R.
  specialize (R ltac:(unfold wlimbs; cbn [map u64s]; rewrite length_app; cbn; lia)).
  unfold wlimbs in R. cbn [map u64s] in R. rewrite Z.add_0_r in R. change (Z.to_nat 0) with 0%nat in R.
  rewrite skipn_O, firstn_app, firstn4_le8 in R. cbn [length le8 word_to_le_bytes Nat.sub firstn] in R. rewrite app_nil_r in R. exact R.
Qed.

Lemma BN_get_flags_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0)%Z -> (0 <= bn_flags b < 2^31)%Z ->
  stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.land (bn_flags b) (bv_unsigned a1))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_GET_FLAGS) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] FL ST LO MI SEP ->. unfold BN_GET_FLAGS.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (AB : (A + 24 <= 2^64)%Z) by (destruct BN as [BN _]; apply cells_at_bound in BN; cbn in BN; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step.
  chk ltac:(fun C => clear - C PA AB; lia).
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. unfold wz at 1. rewrite (sx32_small (bn_flags b)) by lia.
  step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
  finish. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma BN_value_one_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgusegs m ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 CONST_ONE))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_VALUE_ONE) fc None m (seg_rom bgusegs)).
Proof.
  intros until lo. intros ST LO MI. unfold BN_VALUE_ONE.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  carve_frame 16%nat ST.
  do 4 step.
  step. step.
  do 3 step. release_frame FR ST (bv_unsigned sp). step.
  finish. reflexivity.
Qed.

Lemma BN_is_odd_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0) -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  u64arr bgusegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= D) ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (is_odd_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_ODD) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] PD U0 LB HT HD ST LO MI SEP SEPD ->. unfold BN_IS_ODD.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  assert (AB : A + 24 <= 2^64) by (destruct BN as [BN _]; apply cells_at_bound in BN; cbn in BN; lia).
  assert (DT : 0 < Z.of_nat (bn_top b) -> 0 < D /\ D mod 8 = 0 /\ D + 8 * Z.of_nat (length (bn_buf b)) <= 2^47).
  { intros H. destruct (PD H) as [P1 P2]. split; [exact P1|]. split; [exact P2|].
    destruct U0 as [_ U0]. rewrite wlimbs_len in U0. apply (wr_at_below bgusegs m D _ MI) in U0; [| unfold bn_dmax in HT; lia].
    unfold UTOP in U0. lia. }
  apply hide_intro in DT. clear PD.
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step.
  chk ltac:(fun C => clear - C PA AB; lia).
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step. if_cases KT; zify_cond KT.
  -
    assert (ET0 : bn_top b = 0%nat) by (apply andb_false_iff in KT; destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia).
    step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    finish. unfold is_odd_pure. rewrite ET0. reflexivity.
  -
    assert (KTP : 0 < Z.of_nat (bn_top b)) by lia.
    apply hide_elim in DT. destruct (DT KTP) as (D0 & DM & DTOP). clear DT.
    step. unfold wz at 1.
    chk ltac:(fun C => clear - C D0 DTOP; lia).
    step. rewrite (land7_wrap _ DM).
    chk ltac:(fun C => clear - C; lia).
    destruct (bn_buf b) as [|x0 l0] eqn:Ebuf; [exfalso; unfold bn_dmax in HT; rewrite Ebuf in HT; cbn [length] in HT; lia|].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let a := cur_mem_addr in pose proof (u64arr_read_lo4 mx D x0 l0 a U0 ltac:(addr_tac)) as RD end.
    step. clear RD.
    step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    finish.
    pose proof (limbs_nth (x0 :: l0) 0 LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN. cbn [nth] in LN.
    unfold zx32. rewrite (unsigned_lit x0) by lia. rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
    unfold is_odd_pure. rewrite Ebuf. cbn [nth]. replace (0 <? bn_top b)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb].
    f_equal. rewrite Z.land_ones with (n := 1) by lia. change (2 ^ 1) with 2. change (2 ^ 32) with 4294967296.
    rewrite Zodd_mod. destruct (Z.eqb_spec (x0 mod 2) 1) as [E|E]; cbn [Z.b2z]; Z.div_mod_to_equations; lia.
Qed.

Lemma u64arr_read_0 : forall m A x (l : list Z) a,
  u64arr bgusegs m A (wlimbs (x :: l)) -> a = wa A -> ov_read_bytes bgusegs m a 8 = Some (le8 (Z_to_bv 64 x)).
Proof.
  intros m A x l a U ->. rewrite <- (Z.add_0_r A).
  apply (u64arr_read bgusegs m A (wlimbs (x :: l)) 0 (Z_to_bv 64 x)); [exact U | reflexivity | lia | f_equal; lia].
Qed.

Lemma BN_abs_is_word_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0) -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  u64arr bgusegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= D) ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (abs_is_word_pure b (bv_unsigned a1)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_ABS_IS_WORD) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] PD U0 LB HT HD ST LO MI SEP SEPD ->. unfold BN_ABS_IS_WORD.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  pose proof (zr_word a1) as R1. unfold inr64 in R1. change (2 ^ 64)%Z with 18446744073709551616%Z in R1.
  assert (AB : A + 24 <= 2^64) by (destruct BN as [BN _]; apply cells_at_bound in BN; cbn in BN; lia).
  assert (DT : 0 < Z.of_nat (bn_top b) -> 0 < D /\ D mod 8 = 0 /\ D + 8 * Z.of_nat (length (bn_buf b)) <= 2^47).
  { intros H. destruct (PD H) as [P1 P2]. split; [exact P1|]. split; [exact P2|].
    destruct U0 as [_ U0]. rewrite wlimbs_len in U0. apply (wr_at_below bgusegs m D _ MI) in U0; [| unfold bn_dmax in HT; lia].
    unfold UTOP in U0. lia. }
  apply hide_intro in DT. clear PD.
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step.
  chk ltac:(fun C => clear - C PA AB; lia).
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step.
  step. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by lia.
  -
    step. if_cases KW; zify_cond KW; rewrite ?unsigned_lit in KW by lia.
    +
      step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
      finish. unfold abs_is_word_pure. replace (bn_top b =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia). cbn [andb orb].
      rewrite KW. cbn [Z.eqb andb].
      rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1%Z. do 2 f_equal.
      destruct (Nat.eqb_spec (bn_top b) 0) as [E|E]; [rewrite E; reflexivity | apply Z.ltb_ge; lia].
    + step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
      finish. unfold abs_is_word_pure. replace (bn_top b =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (bv_unsigned a1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact KW). cbn [andb orb]. reflexivity.
  - assert (ET1 : bn_top b = 1%nat) by lia.
    apply hide_elim in DT. destruct (DT ltac:(lia)) as (D0 & DM & DTOP). clear DT.
    step. unfold wz at 1.
    chk ltac:(fun C => clear - C D0 DTOP; lia).
    step. rewrite (land7_wrap _ DM).
    chk ltac:(fun C => clear - C; lia).
    destruct (bn_buf b) as [|x0 l0] eqn:Ebuf; [exfalso; unfold bn_dmax in HT; rewrite Ebuf in HT; cbn [length] in HT; lia|].
    pose proof (limbs_nth (x0 :: l0) 0 LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN. cbn [nth] in LN.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let a := cur_mem_addr in pose proof (u64arr_read_0 mx D x0 l0 a U0 ltac:(addr_tac)) as RD end.
    step. clear RD.
    step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    + step. if_cases KW; zify_cond KW; rewrite ?unsigned_lit in KW by lia.
      *
        step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
        finish. unfold abs_is_word_pure. rewrite ET1, Ebuf. cbn [nth Nat.eqb andb orb].
        replace (x0 =? bv_unsigned a1) with false by (symmetry; apply Z.eqb_neq; exact K1). cbn [orb].
        rewrite KW. cbn [Z.eqb andb]. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1%Z.
        replace (Z.of_nat 1 <? 1) with false by reflexivity. reflexivity.
      * step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
        finish. unfold abs_is_word_pure. rewrite ET1, Ebuf. cbn [nth Nat.eqb andb orb].
        replace (x0 =? bv_unsigned a1) with false by (symmetry; apply Z.eqb_neq; exact K1).
        replace (bv_unsigned a1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact KW). reflexivity.
    +
      step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
      finish. unfold abs_is_word_pure. rewrite ET1, Ebuf. cbn [nth Nat.eqb andb orb].
      replace (x0 =? bv_unsigned a1) with true by (symmetry; apply Z.eqb_eq; exact K1). reflexivity.
Qed.

Lemma BN_is_one_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0) -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  u64arr bgusegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= D) ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 48, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (is_one_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_ONE) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] PD U0 LB HT HD ST LO MI SEP SEPD ->. unfold BN_IS_ONE.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (AB : A + 24 <= 2^64) by (destruct BN as [BN' _]; apply cells_at_bound in BN'; cbn in BN'; lia).
  pose proof (proj1 ST) as LO0.
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  unfold bn_cells in BN.
  carve_frame 32%nat ST. do 5 step.
  step. step.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  step. eapply evt_cut.
  { eapply (BN_abs_is_word_spec _ (Z_to_bv 64 (bv_unsigned sp + -32))) with (lo := lo) (A := A) (D := D) (b := b);
      [ exact BN | split; assumption | exact PD | exact U0 | exact LB | exact HT | exact HD | rewrite ESP; exact ST | rewrite ESP; lia
      | exact MI | rewrite ESP; lia | rewrite ESP; lia | reflexivity ]. }
  cbv beta. intros ms2 (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ->).
  rewrite ESP in MU2, ST2. rewrite ret_pc_even by first [lia | reflexivity].
  assert (FR2 := rw_cells_transport bgusegs _ _ m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)).
  assert (BN2 := rw_cells_transport bgusegs _ _ m2 _ _ BN MU2 WM2 ltac:(cbn [disjoint_from bn_cells cells_size csize Nat.add]; lia)).
  assert (MU12 : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
  assert (WM12 := wmono_trans bgusegs _ _ _ WM WM2).
  clear FR BN MU WM MU2 WM2 ST MI.
  rewrite ?(unsigned_lit 1) by lia.
  destruct (abs_is_word_pure b 1) eqn:EAW; cbn [Z.b2z].
  - step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia; try (exfalso; lia).
    unfold bn_cells in BN2.
    chk ltac:(fun C => clear - C PA AB; lia).
    step. rewrite (land7_wrap _ PM).
    chk ltac:(fun C => clear - C; lia).
    step. unfold wz at 1. rewrite (sx32_small (Z.b2z (bn_neg b))) by (destruct (bn_neg b); cbn; lia).
    step. do 4 step. release_frame FR2 ST2 (bv_unsigned sp). step.
    finish. unfold is_one_pure. rewrite EAW. cbn [andb].
    rewrite v_sltiu_b2z, unsigned_lit by (destruct (bn_neg b); cbn; lia). change (bv_wrap 64 1) with 1%Z. do 2 f_equal.
    destruct (bn_neg b); reflexivity.
  - step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia; try (exfalso; lia).
    do 4 step. release_frame FR2 ST2 (bv_unsigned sp). step.
    finish. unfold is_one_pure. rewrite EAW. reflexivity.
Qed.

Lemma BN_is_bit_set_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D n : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0) -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  u64arr bgusegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= D) ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> (-2147483648 <= n < 2147483648)%Z ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (is_bit_set_pure b n))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_BIT_SET) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] PD U0 LB HT HD ST LO MI SEP SEPD -> -> HN. unfold BN_IS_BIT_SET.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  assert (AB : A + 24 <= 2^64) by (destruct BN as [BN' _]; apply cells_at_bound in BN'; cbn in BN'; lia).
  assert (DT : 0 < Z.of_nat (bn_top b) -> 0 < D /\ D mod 8 = 0 /\ D + 8 * Z.of_nat (length (bn_buf b)) <= 2^47).
  { intros H. destruct (PD H) as [P1 P2]. split; [exact P1|]. split; [exact P2|].
    destruct U0 as [_ U0']. rewrite wlimbs_len in U0'. apply (wr_at_below bgusegs m D _ MI) in U0'; [| unfold bn_dmax in HT; lia].
    unfold UTOP in U0'. lia. }
  apply hide_intro in DT. clear PD.
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step.
  step. rewrite lts_signed by lia. if_cases KN; zify_cond KN.
  {
    step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    finish. unfold is_bit_set_pure. replace (n <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  chk ltac:(fun C => clear - C PA AB; lia).
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step. setreg 13%Z (Z_to_bv 64 (n / 64))
          ltac:(f_equal; rewrite (unsigned_lit n) by lia; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32)%Z with 4294967296%Z;
                rewrite (Z.mod_small n 4294967296) by lia; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 6) with 64;
                symmetry; apply bn_swrap32_small; Z.div_mod_to_equations; lia).
  assert (HI : 0 <= n / 64 <= n) by (Z.div_mod_to_equations; lia).
  step. rewrite lts_signed by lia. if_cases KI; zify_cond KI.
  {
    step. step. do 3 step. release_frame FR ST (bv_unsigned sp). step.
    finish. unfold is_bit_set_pure. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (bn_top b <=? Z.to_nat (n / 64))%nat with true by (symmetry; apply Nat.leb_le; lia). reflexivity. }
  apply hide_elim in DT. destruct (DT ltac:(lia)) as (D0 & DM & DTOP). clear DT.
  step. unfold wz at 1.
  step. step. setreg 10%Z (Z_to_bv 64 (D + 8 * (n / 64))) ltac:(f_equal; rewrite (unsigned_lit (n / 64)) by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  set (i := Z.to_nat (n / 64)).
  assert (Ei : n / 64 = Z.of_nat i) by (subst i; lia). rewrite Ei.
  assert (IT : (i < bn_top b)%nat) by lia.
  assert (DI : 0 < D + 8 * Z.of_nat i /\ D + 8 * Z.of_nat i + 8 <= 2^47) by (unfold bn_dmax in HT; lia).
  chk ltac:(fun C => rewrite ?unsigned_lit in C by lia; clear - C D0 DI; lia).
  step. rewrite (snez_pos D) by lia.
  step. rewrite (seqz_pos (D + 8 * Z.of_nat i)) by lia.
  step.
  chk ltac:(fun C => clear - C; lia).
  chk ltac:(fun C => clear - C D0 DTOP; lia).
  step. rewrite (land7_wrap (D + 8 * Z.of_nat i)) by (clear - DM; Z.div_mod_to_equations; lia).
  chk ltac:(fun C => clear - C; lia).
  assert (NTH : nth_error (wlimbs (bn_buf b)) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i (bn_buf b) 0)))
    by (apply wlimbs_nth; unfold bn_dmax in HT; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let a := cur_mem_addr in
    pose proof (u64arr_read bgusegs mx D (wlimbs (bn_buf b)) (Z.of_nat i) (Z_to_bv 64 (nth i (bn_buf b) 0)) a U0 NTH ltac:(lia) ltac:(addr_tac)) as RD end.
  step. clear RD.
  pose proof (limbs_nth (bn_buf b) i LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN.
  step. step. step.
  do 3 step. release_frame FR ST (bv_unsigned sp). step.
  finish.
  set (x := nth i (bn_buf b) 0) in *.
  rewrite (unsigned_lit x), (unsigned_lit n) by lia.
  replace (Z.land n 63) with (n mod 64) by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
  rewrite (unsigned_lit (n mod 64)) by (Z.div_mod_to_equations; lia). rewrite Zmod_mod.
  assert (HS : 0 <= x ≫ (n mod 64) <= x).
  { rewrite Z.shiftr_div_pow2 by (Z.div_mod_to_equations; lia). split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; Z.div_mod_to_equations; lia]|].
    apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; Z.div_mod_to_equations; lia|].
    assert (1 <= 2 ^ (n mod 64)) by (apply Z.pow_le_mono_r with (a := 2) (b := 0); Z.div_mod_to_equations; lia). nia. }
  rewrite unsigned_lit by lia.
  unfold is_bit_set_pure. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia). fold i.
  replace (bn_top b <=? i)%nat with false by (symmetry; apply Nat.leb_gt; lia). fold x.
  f_equal. rewrite Z.land_ones with (n := 1) by lia. change (2 ^ 1) with 2.
  rewrite Z.testbit_spec' by (Z.div_mod_to_equations; lia). rewrite Z.shiftr_div_pow2 by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Definition BN_NUM_BITS : Z := 0xfdc78.

Lemma le4_byte : forall f, 0 <= f < 256 -> le4 (Z_to_bv 64 f) = [Z_to_bv 8 f; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros f Hf. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  rewrite Z.mod_small by lia. cbn [Z_to_le_bytes]. rewrite (Z.shiftr_div_pow2 f 8), (Z.div_small f (2 ^ 8)) by lia. reflexivity.
Qed.

Lemma flags_cell_split : forall m a (d t x n : word) f, 0 <= f < 256 ->
  rw_cells bgusegs m a [C8 d; C4 t; C4 x; C4 n; C4 (Z_to_bv 64 f)] ->
  rw_cells bgusegs m a [C8 d; C4 t; C4 x; C4 n; C1 (Z_to_bv 8 f); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
Proof.
  intros m a d t x n f Hf [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. repeat split.
  - cbn [cells_bytes cbytes] in *. rewrite (le4_byte f Hf) in Hb. exact Hb.
  - exact Hw.
Qed.

Lemma BN_num_bits_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgusegs m A (bn_cells D b) -> (0 < A /\ A mod 8 = 0) -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  u64arr bgusegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^25 -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 4 = 0 ->
  stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 128 -> mem_inv bgusegs m ->
  (A + 24 <= bv_unsigned sp - 128 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 128 \/ bv_unsigned sp <= D) ->
  a0 = Z_to_bv 64 A ->
  evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 128, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (num_bits_pure b)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_NUM_BITS) fc None m (seg_rom bgusegs)).
Proof.
  intros until b. intros BN [PA PM] PD U0 LB HT HD HF HF4 ST LO MI SEP SEPD ->. unfold BN_NUM_BITS.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  assert (AB : A + 24 <= 2^64) by (destruct BN as [BN' _]; apply cells_at_bound in BN'; cbn in BN'; lia).
  assert (DT : 0 < Z.of_nat (bn_top b) -> 0 < D /\ D mod 8 = 0 /\ D + 8 * Z.of_nat (length (bn_buf b)) <= 2^47).
  { intros H. destruct (PD H) as [P1 P2]. split; [exact P1|]. split; [exact P2|].
    destruct U0 as [_ U0']. rewrite wlimbs_len in U0'. apply (wr_at_below bgusegs m D _ MI) in U0'; [| unfold bn_dmax in HT; lia].
    unfold UTOP in U0'. lia. }
  apply hide_intro in DT. clear PD.
  pose proof (proj1 ST) as LO0.
  unfold bn_cells in BN. apply flags_cell_split in BN; [|exact HF].
  carve_frame 112%nat ST.
  do 15 step.
  chk ltac:(fun C => clear - C PA AB; lia).
  step. rewrite (land7_wrap _ PM).
  chk ltac:(fun C => clear - C; lia).
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step. rewrite (unsigned_lit (Z.of_nat (bn_top b))) by lia. rewrite (bn_swrap32_small (Z.of_nat (bn_top b) + -1)) by lia.
  ub_chk.
  step. rewrite (zxb_small (bn_flags b)) by lia.
  step. rewrite (unsigned_lit (bn_flags b)), HF4 by lia.
  step. if_false.
  step. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by lia.
  {
    step. do 14 step. release_frame FR ST (bv_unsigned sp). step.
    finish. unfold num_bits_pure. replace (bn_top b =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia).
    assert (ET0 : bn_top b = 0%nat) by lia. rewrite ET0. reflexivity. }
  apply hide_elim in DT. destruct (DT ltac:(lia)) as (D0 & DM & DTOP). clear DT.
  assert (E26 : bv_wrap 32 (Z.of_nat (bn_top b) + 33554431) ≫ 26 = 0).
  { unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_small. change (2 ^ 26) with 67108864. lia. }
  zstep. zstep. zstep. rewrite E26. change (bv_swrap 32 0) with 0. clear E26.
  ub_chk.
  step. unfold wz at 1.
  step. step. setreg 10%Z (Z_to_bv 64 (D + 8 * (Z.of_nat (bn_top b) + -1))) ltac:(f_equal; rewrite ?unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  set (i := (bn_top b - 1)%nat).
  assert (Ei : Z.of_nat (bn_top b) + -1 = Z.of_nat i) by (subst i; lia). rewrite Ei.
  assert (DI : 0 < D + 8 * Z.of_nat i /\ D + 8 * Z.of_nat i + 8 <= 2^47) by (unfold bn_dmax in HT; lia).
  assert (NTH : nth_error (wlimbs (bn_buf b)) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i (bn_buf b) 0)))
    by (apply wlimbs_nth; unfold bn_dmax in HT; lia).
  zstep. zstep. ub_chk.
  do 4 zstep. ub_chk.
  ub_chk.
  zstep. ub_chk.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let a := cur_mem_addr in
    pose proof (u64arr_read bgusegs mx D (wlimbs (bn_buf b)) (Z.of_nat i) (Z_to_bv 64 (nth i (bn_buf b) 0)) a U0 NTH ltac:(lia) ltac:(addr_tac)) as RD end.
  step. clear RD.
  pose proof (limbs_nth (bn_buf b) i LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN.
  step. setreg 9%Z (Z_to_bv 64 (64 * Z.of_nat i)) ltac:(f_equal; rewrite ?unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; rewrite ?bn_swrap32_small by lia; lia).
  step.

  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112).
  { apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R. lia. }
  eapply evt_cut.
  { eapply BN_num_bits_word_uspec with (lo := lo); [rewrite ESP; exact ST | rewrite ESP; lia | exact MI]. }
  intros ms' PO. unfold nbw_upost in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc).
  subst ms'. rewrite ESP in MUc, STc. rewrite ret_pc_even by first [lia | reflexivity].
  rewrite (unsigned_lit (nth i (bn_buf b) 0)) by lia.
  pose proof (num_bits_word_range (nth i (bn_buf b) 0) ltac:(lia)) as NR.
  lazymatch goal with MUx : munch _ m ?mq |- _ =>
    assert (FR2 := rw_cells_transport bgusegs _ mq m2 _ _ FR MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia));
    assert (MU2 : munch [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m m2)
      by (eapply munch_trans; [exact MUx|]; eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros x Hx; lia)
  end.
  assert (WM2 := wmono_trans bgusegs _ _ _ WM WMc).
  clear FR MU WM MUc WMc ST MI.
  step. step. rewrite ?(unsigned_lit (num_bits_word (nth i (bn_buf b) 0))), ?(unsigned_lit (64 * Z.of_nat i)) by lia.
  rewrite ?(bn_swrap32_small (64 * Z.of_nat i + num_bits_word (nth i (bn_buf b) 0))) by lia.
  step. if_true.
  step. do 14 step. release_frame FR2 STc (bv_unsigned sp). step.
  finish. unfold num_bits_pure. replace (bn_top b =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). fold i.
  replace (Z.of_nat (bn_top b) - 1) with (Z.of_nat i) by lia. f_equal.
  rewrite ?unsigned_lit by lia. rewrite ?Z.add_0_r. rewrite ?bn_swrap32_small by lia. lia.
Qed.
