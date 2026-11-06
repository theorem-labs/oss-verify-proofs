(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnModel BnMInv BgState BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX BnNumBits.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import BnRepDefs AsStruct AsStruct2 W_smallA AW_num_bits_word.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2236744 => 2
  | 2236748 => 1
  | 2236752 => 2
  | 2236796 => 2
  | 2236836 => 1
  | 2236840 => 1
  | 2236844 => 1
  | 2236848 => 2
  | 2236880 => 1
  | 2236884 => 1
  | 2236888 => 2
  | 2236908 => 2
  | 2236912 => 2
  | 2236916 => 1
  | 2236920 => 2
  | 2237044 => 1
  | 2237048 => 1
  | 2237052 => 1
  | 2237056 => 1
  | 2237068 => 2
  | 2237072 => 1
  | 2237076 => 1
  | 2237080 => 2
  | 2237084 => 2
  | 2237756 => 2
  | 2237760 => 1
  | 2237764 => 2
  | 2246752 => 2
  | 2246756 => 1
  | 2246760 => 2
  | 2246836 => 2
  | 2246840 => 1
  | 2246844 => 1
  | 2246848 => 1
  | 2246852 => 2
  | 2246856 => 2
  | 2246860 => 1
  | 2246864 => 2
  | 2249444 => 2
  | 2249448 => 1
  | 2249452 => 2
  | 2249520 => 2
  | 2249524 => 1
  | 2249528 => 2
  | 2250308 => 2
  | 2250312 => 1
  | 2250316 => 2
  | 2250380 => 2
  | 2250384 => 1
  | 2250388 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).
Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => apply hide_intro in H end.
Ltac unhide := repeat match goal with H : hide _ |- _ => apply hide_elim in H end.
Definition BN_GET_FLAGS : Z := 0x22252c.
Definition BN_IS_ODD : Z := 0x225634.
Definition BN_ABS_IS_WORD : Z := 0x2252d4.
Definition BN_IS_BIT_SET : Z := 0x22484c.
Definition BN_VALUE_ONE : Z := 0x222050.

Lemma wlimbs_nth : forall buf (i : nat), (i < length buf)%nat -> nth_error (wlimbs buf) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i buf 0)).
Proof. intros buf i H. rewrite Nat2Z.id. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' buf 0) by lia. reflexivity. Qed.

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Lemma u64arr_read_lo4 : forall m A x (l : list Z) a,
  u64arr bgbsegs m A (wlimbs (x :: l)) -> a = wa A -> ov_read_bytes bgbsegs m a 4 = Some (le4 (Z_to_bv 64 x)).
Proof.
  intros m A x l a [Hb _] ->.
  pose proof (bytes_at_read bgbsegs m A (u64s (wlimbs (x :: l))) 0 4 Hb ltac:(lia)) as R.
  specialize (R ltac:(unfold wlimbs; cbn [map u64s]; rewrite length_app; cbn; lia)).
  unfold wlimbs in R. cbn [map u64s] in R. rewrite Z.add_0_r in R. change (Z.to_nat 0) with 0%nat in R.
  rewrite skipn_O, firstn_app, firstn4_le8 in R. cbn [length le8 word_to_le_bytes Nat.sub firstn] in R. rewrite app_nil_r in R. exact R.
Qed.

Lemma u64arr_read_0 : forall m A x (l : list Z) a,
  u64arr bgbsegs m A (wlimbs (x :: l)) -> a = wa A -> ov_read_bytes bgbsegs m a 8 = Some (le8 (Z_to_bv 64 x)).
Proof.
  intros m A x l a U ->.
  apply (u64arr_read bgbsegs m A (wlimbs (x :: l)) 0 (Z_to_bv 64 x) (wa A) U); [reflexivity| cbn [length wlimbs map]; lia| f_equal; lia].
Qed.

Lemma BN_get_flags_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgbsegs m A (bn_cells D b) -> (0 <= bn_flags b < 2^31)%Z ->
  stk bgbsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgbsegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A)%Z ->
  shb_cells bgbsegs 6147864 6945336 m -> acc bgbsegs m A 24 -> (A mod 8 = 0)%Z ->
  (SHHI <= lo)%Z ->
  a0 = Z_to_bv 64 A -> 0 < A ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.land (bn_flags b) (bv_unsigned a1))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_GET_FLAGS) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros BN FL ST LO MI SEP (SHB1 & SHB2) ACC AL SLO -> PA. unfold SHLO, SHHI in *. unfold BN_GET_FLAGS.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step. ub. do 3 step. do 3 step. shl. chk0.
  step. unfold wz at 1. rewrite (sx32_small (bn_flags b)) by lia.
  step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  finish. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma BN_value_one_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk bgbsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> mem_inv bgbsegs m ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 0x57acc0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_VALUE_ONE) fc None m (seg_rom bgbsegs)).
Proof.
  intros until lo. intros ST LO MI. unfold BN_VALUE_ONE.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  carve_frame 16%nat ST.
  do 4 step.
  step. step.
  do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  finish. reflexivity.
Qed.

Lemma BN_is_odd_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgbsegs m A (bn_cells D b) -> u64arr bgbsegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk bgbsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv bgbsegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= D) ->
  shb_cells bgbsegs 6147864 6945336 m -> acc bgbsegs m A 24 -> A mod 8 = 0 ->
  acc bgbsegs m D (8 * Z.of_nat (bn_top b)) -> D mod 8 = 0 -> 0 <= D /\ D + 8 * Z.of_nat (bn_top b) <= 140737488355328 ->
  SHHI <= lo ->
  a0 = Z_to_bv 64 A -> 0 < A -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (is_odd_pure b))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_ODD) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros BN U0 LB HT HD ST LO MI SEP SEPD (SHB1 & SHB2) ACC AL ACCD ALD BD SLO -> PA PD. unfold BN_IS_ODD.
  unfold SHLO, SHHI in *.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step. ub. do 3 step. do 3 step. shl_with ACC AL. chk0.
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step. if_cases KT; zify_cond KT.
  -
    assert (ET0 : bn_top b = 0%nat) by (apply andb_false_iff in KT; destruct KT as [KT|KT]; apply Z.ltb_ge in KT; lia).
    step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
    finish. unfold is_odd_pure. rewrite ET0. reflexivity.
  -
    do 2 step. shl_with ACC AL. chk0.
    step. unfold wz at 1.
    destruct (bn_buf b) as [|x0 l0] eqn:Ebuf; [exfalso; unfold bn_dmax in HT; rewrite Ebuf in HT; cbn [length] in HT; clear - HT KT0; lia|].
    assert (DM1 : 1 <= Z.of_nat (bn_dmax b)) by (unfold bn_dmax; rewrite Ebuf; cbn [length]; lia).
    destruct (PD ltac:(lia)) as (PD0 & PD8). ub.
    do 2 step. shl_limb ACCD ALD BD 0. chk0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let a := cur_mem_addr in pose proof (u64arr_read_lo4 mx D x0 l0 a U0 ltac:(addr_tac)) as RD end.
    step. clear RD.
    step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
    finish.
    pose proof (limbs_nth (x0 :: l0) 0 LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN. cbn [nth] in LN.
    unfold zx32. rewrite (unsigned_lit x0) by lia. rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
    unfold is_odd_pure. rewrite Ebuf. cbn [nth]. replace (0 <? bn_top b)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb].
    f_equal. rewrite Z.land_ones with (n := 1) by lia. change (2 ^ 1) with 2. change (2 ^ 32) with 4294967296.
    rewrite Zodd_mod. destruct (Z.eqb_spec (x0 mod 2) 1) as [E|E]; cbn [Z.b2z]; Z.div_mod_to_equations; lia.
Qed.

Lemma BN_abs_is_word_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgbsegs m A (bn_cells D b) -> u64arr bgbsegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk bgbsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv bgbsegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= D) ->
  shb_cells bgbsegs 6147864 6945336 m -> acc bgbsegs m A 24 -> A mod 8 = 0 ->
  acc bgbsegs m D (8 * Z.of_nat (bn_top b)) -> D mod 8 = 0 -> 0 <= D /\ D + 8 * Z.of_nat (bn_top b) <= 140737488355328 ->
  SHHI <= lo ->
  a0 = Z_to_bv 64 A -> 0 < A -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (abs_is_word_pure b (bv_unsigned a1)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_ABS_IS_WORD) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros BN U0 LB HT HD ST LO MI SEP SEPD (SHB1 & SHB2) ACC AL ACCD ALD BD SLO -> PA PD. unfold BN_ABS_IS_WORD.
  unfold SHLO, SHHI in *.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  pose proof (zr_word a1) as R1. unfold inr64 in R1. change (2 ^ 64)%Z with 18446744073709551616%Z in R1.
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step. ub. do 3 step. do 3 step. shl_with ACC AL. chk0.
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step.
  step. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by lia.
  -
    step. if_cases KW; zify_cond KW; rewrite ?unsigned_lit in KW by lia.
    +
      step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
      finish. unfold abs_is_word_pure. replace (bn_top b =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia). cbn [andb orb].
      rewrite KW. cbn [Z.eqb andb].
      rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1%Z. do 2 f_equal.
      destruct (Nat.eqb_spec (bn_top b) 0) as [E|E]; [rewrite E; reflexivity | apply Z.ltb_ge; lia].
    + step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
      finish. unfold abs_is_word_pure. replace (bn_top b =? 1)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
      replace (bv_unsigned a1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact KW). cbn [andb orb]. reflexivity.
  - assert (ET1 : bn_top b = 1%nat) by lia.
    do 2 step. shl_with ACC AL. chk0.
    step. unfold wz at 1.
    destruct (bn_buf b) as [|x0 l0] eqn:Ebuf; [exfalso; unfold bn_dmax in HT; rewrite Ebuf in HT; cbn [length] in HT; lia|].
    assert (DM1 : 1 <= Z.of_nat (bn_dmax b)) by (unfold bn_dmax; rewrite Ebuf; cbn [length]; lia).
    pose proof (limbs_nth (x0 :: l0) 0 LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN. cbn [nth] in LN.
    destruct (PD ltac:(lia)) as (PD0 & PD8). ub.
    do 2 step. shl_limb ACCD ALD BD 0. chk0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      let a := cur_mem_addr in pose proof (u64arr_read_0 mx D x0 l0 a U0 ltac:(addr_tac)) as RD end.
    step. clear RD.
    step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    +
      step. if_cases KW; zify_cond KW; rewrite ?unsigned_lit in KW by lia.
      *
        step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
        finish. unfold abs_is_word_pure. rewrite ET1, Ebuf. cbn [nth Nat.eqb andb orb].
        replace (x0 =? bv_unsigned a1) with false by (symmetry; apply Z.eqb_neq; exact K1). cbn [orb].
        rewrite KW. cbn [Z.eqb andb]. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1%Z.
        replace (Z.of_nat 1 <? 1) with false by reflexivity. reflexivity.
      * step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
        finish. unfold abs_is_word_pure. rewrite ET1, Ebuf. cbn [nth Nat.eqb andb orb].
        replace (x0 =? bv_unsigned a1) with false by (symmetry; apply Z.eqb_neq; exact K1).
        replace (bv_unsigned a1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact KW). reflexivity.
    +
      step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
      finish. unfold abs_is_word_pure. rewrite ET1, Ebuf. cbn [nth Nat.eqb andb orb].
      replace (x0 =? bv_unsigned a1) with true by (symmetry; apply Z.eqb_eq; exact K1). reflexivity.
Qed.

Lemma BN_is_bit_set_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D n : Z) (b : bignum bptr),
  rw_cells bgbsegs m A (bn_cells D b) -> u64arr bgbsegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^31 ->
  stk bgbsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv bgbsegs m ->
  (A + 24 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= D) ->
  shb_cells bgbsegs 6147864 6945336 m -> acc bgbsegs m A 24 -> A mod 8 = 0 ->
  acc bgbsegs m D (8 * Z.of_nat (bn_top b)) -> D mod 8 = 0 -> 0 <= D /\ D + 8 * Z.of_nat (bn_top b) <= 140737488355328 ->
  SHHI <= lo ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> (-2147483648 <= n < 2147483648)%Z -> 0 < A -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (Z.b2z (is_bit_set_pure b n))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_IS_BIT_SET) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros BN U0 LB HT HD ST LO MI SEP SEPD (SHB1 & SHB2) ACC AL ACCD ALD BD SLO -> -> HN PA PD. unfold BN_IS_BIT_SET.
  unfold SHLO, SHHI in *.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  unfold bn_cells in BN.
  carve_frame 16%nat ST.
  do 4 step.
  step. rewrite lts_signed by lia. if_cases KN; zify_cond KN.
  {
    step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
    finish. unfold is_bit_set_pure. replace (n <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  ub. do 3 step. do 3 step. shl_with ACC AL. chk0.
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step. setreg 14%Z (Z_to_bv 64 (n / 64))
          ltac:(f_equal; rewrite (unsigned_lit n) by lia; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32)%Z with 4294967296%Z;
                rewrite (Z.mod_small n 4294967296) by lia; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 6) with 64;
                symmetry; apply bn_swrap32_small; Z.div_mod_to_equations; lia).
  assert (HI : 0 <= n / 64 <= n) by (Z.div_mod_to_equations; lia).
  step. rewrite lts_signed by lia. if_cases KI; zify_cond KI.
  {
    step. step. do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
    finish. unfold is_bit_set_pure. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (bn_top b <=? Z.to_nat (n / 64))%nat with true by (symmetry; apply Nat.leb_le; lia). reflexivity. }
  do 2 step. shl_with ACC AL. chk0.
  step. unfold wz at 1.
  step. step. setreg 10%Z (Z_to_bv 64 (D + 8 * (n / 64))) ltac:(f_equal; rewrite (unsigned_lit (n / 64)) by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  set (i := Z.to_nat (n / 64)).
  assert (Ei : n / 64 = Z.of_nat i) by (subst i; lia). rewrite Ei.
  assert (NTH : nth_error (wlimbs (bn_buf b)) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i (bn_buf b) 0)))
    by (apply wlimbs_nth; unfold bn_dmax in HT; lia).
  destruct (PD ltac:(lia)) as (PD0 & PD8). ub.
  do 2 step. shl_limb ACCD ALD BD (Z.of_nat i). chk0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let a := cur_mem_addr in
    pose proof (u64arr_read bgbsegs mx D (wlimbs (bn_buf b)) (Z.of_nat i) (Z_to_bv 64 (nth i (bn_buf b) 0)) a U0 NTH ltac:(lia) ltac:(addr_tac)) as RD end.
  step. clear RD.
  pose proof (limbs_nth (bn_buf b) i LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN.
  step. step. step.
  do 2 step. release_frame FR ST (bv_unsigned sp). step. step.
  finish.
  set (x := nth i (bn_buf b) 0) in *.
  rewrite (unsigned_lit x), (unsigned_lit n) by lia.
  assert (E63 : Z.land n 63 = n mod 64) by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
  rewrite ?E63. rewrite ?(unsigned_lit (n mod 64)) by (Z.div_mod_to_equations; lia). rewrite ?Z.mod_mod by lia.
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

Definition BN_NUM_BITS : Z := 0x22210c.

Definition BN_NUM_BITS_STACK : Z := 128.

Lemma le4_byte : forall f, 0 <= f < 256 -> le4 (Z_to_bv 64 f) = [Z_to_bv 8 f; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros f Hf. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  rewrite Z.mod_small by lia. cbn [Z_to_le_bytes]. rewrite (Z.shiftr_div_pow2 f 8), (Z.div_small f (2 ^ 8)) by lia. reflexivity.
Qed.

Lemma flags_cell_split : forall m a (d t x n : word) f, 0 <= f < 256 ->
  rw_cells bgbsegs m a [C8 d; C4 t; C4 x; C4 n; C4 (Z_to_bv 64 f)] ->
  rw_cells bgbsegs m a [C8 d; C4 t; C4 x; C4 n; C1 (Z_to_bv 8 f); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
Proof.
  intros m a d t x n f Hf [[Hwf Hb] Hw]. split; [split|].
  - cbn [cells_wf cell_wf]. repeat split.
  - cbn [cells_bytes cbytes] in *. rewrite (le4_byte f Hf) in Hb. exact Hb.
  - exact Hw.
Qed.

Lemma BN_num_bits_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A D : Z) (b : bignum bptr),
  rw_cells bgbsegs m A (bn_cells D b) -> u64arr bgbsegs m D (wlimbs (bn_buf b)) -> limbs (bn_buf b) ->
  (bn_top b <= bn_dmax b)%nat -> Z.of_nat (bn_dmax b) < 2^25 -> 0 <= bn_flags b < 256 -> Z.land (bn_flags b) 4 = 0 ->
  stk bgbsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 128 -> mem_inv bgbsegs m ->
  (A + 24 <= bv_unsigned sp - 128 \/ bv_unsigned sp <= A) ->
  (D + 8 * Z.of_nat (bn_dmax b) <= bv_unsigned sp - 128 \/ bv_unsigned sp <= D) ->
  shb_cells bgbsegs 6147864 6945336 m -> acc bgbsegs m A 24 -> A mod 8 = 0 ->
  acc bgbsegs m D (8 * Z.of_nat (bn_top b)) -> D mod 8 = 0 -> 0 <= D /\ D + 8 * Z.of_nat (bn_top b) <= 140737488355328 ->
  SHHI <= lo ->
  a0 = Z_to_bv 64 A -> 0 < A -> ub_ptr_ok (Z.of_nat (bn_top b)) D ->
  evt bgbsegs (bn_small_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               [(bv_unsigned sp - 128, bv_unsigned sp)]%Z lo m
               (fun a0' _ => a0' = Z_to_bv 64 (num_bits_pure b)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BN_NUM_BITS) fc None m (seg_rom bgbsegs)).
Proof.
  intros until b. intros BN U0 LB HT HD HF HF4 ST LO MI SEP SEPD (SHB1 & SHB2) ACC AL ACCD ALD BD SLO -> PA PD. unfold BN_NUM_BITS.
  unfold SHLO, SHHI in *.
  pose proof (bn_cells_bound47 m A _ BN MI ltac:(cbn; lia)) as B47. cbn [bn_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B47.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 128, bv_unsigned sp)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; lia).
  assert (LW : Z.of_nat (length (wlimbs (bn_buf b))) = Z.of_nat (bn_dmax b)) by (rewrite wlimbs_len; reflexivity).
  pose proof (proj1 ST) as LO0.
  unfold bn_cells in BN. apply flags_cell_split in BN; [|exact HF].
  carve_frame 112%nat ST.
  do 15 step. hide_ors. ub. unhide. do 3 step.
  do 3 step. shl_with ACC AL. chk0.
  step. unfold wz at 1. rewrite (sx32_small (Z.of_nat (bn_top b))) by lia.
  step. rewrite (unsigned_lit (Z.of_nat (bn_top b))) by lia. rewrite (bn_swrap32_small (Z.of_nat (bn_top b) + -1)) by lia.
  hide_ors. ub. unhide.
  do 3 step. shl_with ACC AL. chk0.
  step. rewrite (zxb_small (bn_flags b)) by lia.
  step. rewrite (unsigned_lit (bn_flags b)), HF4 by lia.
  step. if_false.
  step. if_cases KT; zify_cond KT; rewrite ?unsigned_lit in KT by lia.
  {
    step. step. step. do 13 step. release_frame FR ST (bv_unsigned sp). step. step.
    finish. unfold num_bits_pure. replace (bn_top b =? 0)%nat with true by (symmetry; apply Nat.eqb_eq; lia). reflexivity. }
  destruct (PD ltac:(lia)) as (PD0 & PD8).

  assert (E26 : bv_wrap 32 (Z.of_nat (bn_top b) + 33554431) ≫ 26 = 0).
  { unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_small. change (2 ^ 26) with 67108864. lia. }
  zstep. zstep. zstep. rewrite E26. change (bv_swrap 32 0) with 0. clear E26.
  hide_ors. ub. unhide.
  do 2 step. shl_with ACC AL. chk0.
  step. unfold wz at 1.
  step. step. setreg 10%Z (Z_to_bv 64 (D + 8 * (Z.of_nat (bn_top b) + -1))) ltac:(f_equal; rewrite ?unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  set (i := (bn_top b - 1)%nat).
  assert (Ei : Z.of_nat (bn_top b) + -1 = Z.of_nat i) by (subst i; lia). rewrite Ei.
  assert (NTH : nth_error (wlimbs (bn_buf b)) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i (bn_buf b) 0)))
    by (apply wlimbs_nth; unfold bn_dmax in HT; lia).
  hide_ors. ub. unhide.
  do 4 step.
  hide_ors. ub. unhide.
  do 2 step. shl_limb ACCD ALD BD (Z.of_nat i). chk0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let a := cur_mem_addr in
    pose proof (u64arr_read bgbsegs mx D (wlimbs (bn_buf b)) (Z.of_nat i) (Z_to_bv 64 (nth i (bn_buf b) 0)) a U0 NTH ltac:(lia) ltac:(addr_tac)) as RD end.
  step. clear RD.
  pose proof (limbs_nth (bn_buf b) i LB) as LN. unfold limb in LN. rewrite BnArith.BW_lit in LN.
  step. setreg 9%Z (Z_to_bv 64 (64 * Z.of_nat i)) ltac:(f_equal; rewrite ?unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; rewrite bn_swrap32_small by lia; lia).
  step.

  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112).
  { apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R. lia. }
  eapply evt_cut.
  { eapply BN_num_bits_word_aspec with (lo := lo); [rewrite ESP; exact ST | rewrite ESP; lia | exact MI]. }
  intros ms' PO. unfold nbw_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc).
  subst ms'. rewrite ESP in MUc, STc. rewrite (ret_pc_even 2236952) by lia.
  rewrite (unsigned_lit (nth i (bn_buf b) 0)) by lia.
  pose proof (num_bits_word_range (nth i (bn_buf b) 0) ltac:(lia)) as NR.
  lazymatch goal with MUx : munch _ m ?mq |- _ =>
    assert (FR2 := rw_cells_transport bgbsegs _ mq m2 _ _ FR MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia));
    assert (MU2 : munch [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m m2)
      by (eapply munch_trans; [exact MUx|]; eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros x Hx; lia)
  end.
  assert (WM2 := wmono_trans bgbsegs _ _ _ WM WMc).
  clear FR MU WM MUc WMc ST MI.
  step. step. rewrite ?(unsigned_lit (num_bits_word (nth i (bn_buf b) 0))), ?(unsigned_lit (64 * Z.of_nat i)) by lia.
  rewrite ?(bn_swrap32_small (64 * Z.of_nat i + num_bits_word (nth i (bn_buf b) 0))) by lia.
  step. if_true.
  step. do 13 step. release_frame FR2 STc (bv_unsigned sp). step. step.
  finish. unfold num_bits_pure. replace (bn_top b =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). fold i.
  replace (Z.of_nat (bn_top b) - 1) with (Z.of_nat i) by lia. f_equal.
  rewrite ?unsigned_lit by lia. rewrite ?Z.add_0_r. rewrite ?bn_swrap32_small by lia. lia.
Qed.
