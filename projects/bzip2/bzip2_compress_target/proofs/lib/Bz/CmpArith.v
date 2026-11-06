(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem CmpMem.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLia.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Notation M32 := 4294967296.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod64_mod32 : forall z, (z mod 18446744073709551616) mod M32 = z mod M32.
Proof.
  intros z. change 18446744073709551616 with (M32 * M32). rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm M32), Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.
Lemma low32_lit : forall z, bv_unsigned (Z_to_bv 64 z) mod M32 = z mod M32.
Proof. intros z. rewrite unsigned_lit_wrap. apply mod64_mod32. Qed.
Lemma swrap32_mod32 : forall x, bv_swrap 32 x mod M32 = x mod M32.
Proof.
  intros x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with M32. change (M32 `div` 2) with 2147483648.
  set (y := x + 2147483648).
  replace x with (y - 2147483648) by lia.
  rewrite Zminus_mod_idemp_l. reflexivity.
Qed.
Lemma low32_sx32 : forall w : word, bv_unsigned (sx32 w) mod M32 = bv_unsigned w mod M32.
Proof. intros w. unfold sx32. rewrite low32_lit. apply swrap32_mod32. Qed.
Lemma low32_zx32 : forall w : word, bv_unsigned (zx32 w) mod M32 = bv_unsigned w mod M32.
Proof. intros w. unfold zx32. rewrite low32_lit. apply Z.mod_mod. lia. Qed.
Lemma low32_mul : forall a k, (a * k) mod M32 = ((a mod M32) * k) mod M32.
Proof. intros. rewrite Z.mul_mod_idemp_l by lia. reflexivity. Qed.
Lemma low32_add : forall a b, (a + b) mod M32 = (a mod M32 + b mod M32) mod M32.
Proof. intros. rewrite <- Z.add_mod by lia. reflexivity. Qed.
Lemma low32_lor : forall a b, Z.lor a b mod M32 = Z.lor (a mod M32) (b mod M32).
Proof.
  intros. change M32 with (2 ^ 32). rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l.
Qed.
Lemma low32_mod : forall a, (a mod M32) mod M32 = a mod M32.
Proof. intros. apply Z.mod_mod. lia. Qed.
Lemma low32_small : forall a, 0 <= a < M32 -> a mod M32 = a.
Proof. intros. apply Z.mod_small. lia. Qed.
Lemma shiftl_mul256 : forall x, Z.shiftl x 8 = x * 256.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma shiftr_div24 : forall x, Z.shiftr x 24 = x / 16777216.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma high_byte_of_low32 : forall (x : Z) u, 0 <= x -> x mod M32 = u -> 0 <= u < M32 -> (x / 16777216) mod 256 = u / 16777216.
Proof.
  intros x u Hx Hm Hu. subst u.
  change 16777216 with (2 ^ 24). change M32 with (2 ^ 32).
  rewrite <- (div_mod_pow2 x 32 24) by lia.
  apply Z.mod_small. split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia|].
  apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 24 * 256) with (2 ^ 32). apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint cset (k : nat) (c : cell) (cs : list cell) : list cell :=
  match cs, k with
  | [], _ => []
  | _ :: cs', O => c :: cs'
  | x :: cs', S k' => x :: cset k' c cs'
  end.

Lemma cset_split : forall cs k c x, nth_error cs k = Some x ->
  exists pre post, cs = pre ++ x :: post /\ cset k c cs = pre ++ c :: post.
Proof.
  induction cs as [|y cs IH]; intros [|k] c x H; cbn in H; try discriminate.
  - inversion H; subst. exists [], cs. split; reflexivity.
  - cps_destruct (IH k c x H) as (pre & post & E1 & E2). exists (y :: pre), post. cbn. rewrite E1 at 1. rewrite E2. split; reflexivity.
Qed.

Section Cells.
  Variable segs : list Segment.
  Lemma rw_cells_C4_reword : forall m A cs k (w w' : word),
    rw_cells segs m A cs -> nth_error cs k = Some (C4 w) -> bv_unsigned w mod M32 = bv_unsigned w' mod M32 ->
    rw_cells segs m A (cset k (C4 w') cs).
  Proof.
    intros m A cs k w w' H Hn Hm.
    cps_destruct (cset_split cs k (C4 w') (C4 w) Hn) as (pre & post & E1 & E2). rewrite E2. rewrite E1 in H.
    destruct H as [[Hwf Hb] Hw]. split; [split|].
    - apply cells_wf_app in Hwf. destruct Hwf as [H1 H2]. cbn in H2. destruct H2 as [_ H2].
      apply cells_wf_app. split; [exact H1|]. cbn. split; [exact I| exact H2].
    - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite <- (le4_mod32 w w' Hm). exact Hb.
    - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
  Qed.
  (* [comment removed for export] *)
  Lemma rw_cells_C4_relit : forall m A cs k (w : word) z,
    rw_cells segs m A cs -> nth_error cs k = Some (C4 w) -> bv_unsigned w mod M32 = z mod M32 ->
    rw_cells segs m A (cset k (C4 (Z_to_bv 64 z)) cs).
  Proof. intros. eapply rw_cells_C4_reword; [eassumption| eassumption|]. rewrite low32_lit. assumption. Qed.
End Cells.
End ACeilS1.


(* [comment removed for export] *)
Ltac reword_C4 H k z :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let H' := fresh in
    unshelve (epose proof (rw_cells_C4_relit segs m A cs k _ z H eq_refl _) as H');
    [| clear H; cbn [cset] in H'; rename H' into H]
  end.

(* [comment removed for export] *)
Ltac low32 :=
  rewrite ?shiftl_mul256, ?shiftr_div24;
  repeat first [ rewrite low32_lit | rewrite low32_sx32 | rewrite low32_zx32 ];
  try reflexivity.
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma low32_shl8_sx32 : forall u, bv_unsigned (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 u)) * 256)) mod M32 = Z.shiftl u 8 mod M32.
Proof.
  intros u. rewrite low32_lit. rewrite low32_mul, low32_sx32, low32_lit, <- low32_mul. rewrite shiftl_mul256. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma neg_shift_amount : forall l n, 0 <= l -> 1 <= n -> l + n <= 32 ->
  ((0 - (l + n)) mod 18446744073709551616) mod 32 = if l + n =? 32 then 0 else 32 - l - n.
Proof.
  intros l n Hl Hn Hln.
  replace ((0 - (l + n)) mod 18446744073709551616) with (18446744073709551616 - l - n)
    by (apply (Z.mod_unique_pos _ _ (-1)); lia).
  destruct (Z.eqb_spec (l + n) 32).
  - symmetry. apply (Z.mod_unique_pos _ _ (576460752303423487)); lia.
  - symmetry. apply (Z.mod_unique_pos _ _ (576460752303423487)); lia.
Qed.

(* [comment removed for export] *)
Lemma low32_or_shifted : forall v sh (x : word) buff,
  bv_unsigned x mod M32 = buff -> 0 <= buff < M32 ->
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_swrap 32 (Z.shiftl v sh) mod 18446744073709551616) (bv_unsigned x))) mod M32
  = Z.lor buff (Z.shiftl v sh mod M32) mod M32.
Proof.
  intros v sh x buff Hx Hb. rewrite low32_lit, !low32_lor, Hx, mod64_mod32, swrap32_mod32, !low32_mod, (low32_small buff) by lia.
  apply Z.lor_comm.
Qed.

Lemma low32_or_shifted2 : forall v sh (x : word) buff,
  bv_unsigned x mod M32 = buff -> 0 <= buff < M32 ->
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_swrap 32 (Z.shiftl v sh) mod 18446744073709551616))) mod M32
  = Z.lor buff (Z.shiftl v sh mod M32) mod M32.
Proof.
  intros v sh x buff Hx Hb. rewrite low32_lit, !low32_lor, Hx, mod64_mod32, swrap32_mod32, !low32_mod, (low32_small buff) by lia.
  reflexivity.
Qed.
(* [comment removed for export] *)
Lemma low32_or_shifted3 : forall v sh buff, 0 <= buff < M32 ->
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 (Z_to_bv 64 buff))) (bv_swrap 32 (Z.shiftl v sh) mod 18446744073709551616))) mod M32
  = Z.lor buff (Z.shiftl v sh mod M32) mod M32.
Proof.
  intros v sh buff Hb. apply low32_or_shifted2; [|exact Hb]. rewrite low32_sx32, low32_lit. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma land255_mod : forall x, Z.land x 255 = x mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma byte3_eq : forall u, 0 <= u < M32 -> Z.land (Z.shiftr u 24) 255 = u / 16777216.
Proof.
  intros u Hu. rewrite land255_mod, shiftr_div24. apply Z.mod_small.
  split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.
Lemma byte_mid_eq : forall u k, 0 <= u -> 8 <= k <= 24 ->
  (u * 2 ^ (64 - k - 8)) mod 18446744073709551616 / 72057594037927936 = Z.land (Z.shiftr u k) 255.
Proof.
  intros u k Hu Hk. rewrite land255_mod.
  change 18446744073709551616 with (2 ^ 64). change 72057594037927936 with (2 ^ 56).
  replace (2 ^ 64) with (2 ^ (k + 8) * 2 ^ (64 - k - 8)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r by (try apply Z.pow_nonzero; lia).
  replace (2 ^ 56) with (2 ^ (64 - k - 8) * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  pose proof (Z.pow_pos_nonneg 2 (64 - k - 8) ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
  rewrite <- Z.div_div, Z.div_mul by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite <- (div_mod_pow2 u (k + 8) k) by lia.
  symmetry. apply Z.mod_small. split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia|].
  apply Z.div_lt_upper_bound; [lia|].
  replace (2 ^ k * 256) with (2 ^ (k + 8)) by (rewrite Z.pow_add_r by lia; reflexivity).
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
Lemma byte2_eq : forall u, 0 <= u -> (u * 1099511627776) mod 18446744073709551616 / 72057594037927936 = Z.land (Z.shiftr u 16) 255.
Proof. intros u Hu. exact (byte_mid_eq u 16 Hu ltac:(lia)). Qed.
Lemma byte1_eq : forall u, 0 <= u -> (u * 281474976710656) mod 18446744073709551616 / 72057594037927936 = Z.land (Z.shiftr u 8) 255.
Proof. intros u Hu. exact (byte_mid_eq u 8 Hu ltac:(lia)). Qed.

Lemma low32_lxor : forall a b, Z.lxor a b mod M32 = Z.lxor (a mod M32) (b mod M32).
Proof.
  intros. change M32 with (2 ^ 32). rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit (Z.ones 32) n); reflexivity.
Qed.
(* [comment removed for export] *)
Lemma wr8_zset_land : forall a i v, 0 <= v -> wr8 a i v = zset a i (Z.land v 255).
Proof. intros. unfold wr8. rewrite land255_mod. reflexivity. Qed.

Lemma lxor_byte : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
  intros a b Ha Hb.
  assert (E : Z.lxor a b = Z.land (Z.lxor a b) (Z.ones 8)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec.
    destruct (Z_lt_le_dec n 8).
    - rewrite Z.ones_spec_low by lia. rewrite andb_true_r. reflexivity.
    - assert (La : Z.log2 a < 8) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]; apply Z.log2_lt_pow2; lia).
      assert (Lb : Z.log2 b < 8) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]; apply Z.log2_lt_pow2; lia).
      rewrite (Z.bits_above_log2 a n), (Z.bits_above_log2 b n) by lia.
      rewrite Z.ones_spec_high by lia. reflexivity. }
  rewrite E, Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma low32_crc_step' : forall (w : word) crc t, bv_unsigned w mod M32 = crc -> 0 <= t < M32 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor ((bv_unsigned w * 256) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 t))))) mod M32
  = Z.lxor ((Z.shiftl crc 8) mod M32) t.
Proof.
  intros w crc t Hw Ht. rewrite low32_lit, low32_lxor, mod64_mod32, low32_mul, Hw, low32_sx32, low32_lit, (low32_small t), shiftl_mul256 by lia.
  reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ov_read_bytes_prefix : forall segs m a n k bs, ov_read_bytes segs m a (n + k) = Some bs -> ov_read_bytes segs m a n = Some (firstn n bs).
Proof.
  intros segs m a n. revert a. induction n as [|n IH]; intros a k bs H; [reflexivity|].
  cbn [ov_read_bytes Nat.add] in H |- *.
  destruct (match m a with Some b => Some b | None => match memory_read segs a 1 with Some (b :: _) => Some b | _ => None end end) as [b|]; [|discriminate].
  lazymatch goal with |- match ov_read_bytes _ _ ?a' _ with _ => _ end = _ =>
    destruct (ov_read_bytes segs m a' (n + k)) as [rest|] eqn:E; [|discriminate];
    injection H as <-; rewrite (IH _ _ _ E); reflexivity end.
Qed.
Lemma low_byte_word : forall w : word, firstn 1 (le4 w) = [Z_to_bv 8 (bv_unsigned w)].
Proof. intros w. rewrite le4_unsigned. reflexivity. Qed.
Section SubRead.
  Variable segs : list Segment.
  Lemma rw_cells_read_byte0 : forall m A cs k w a,
    rw_cells segs m A cs -> cell_at cs k = Some (C4 w) -> a = wa (A + Z.of_nat k) ->
    ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (bv_unsigned w)].
  Proof.
    intros m A cs k w a H Hc ->. pose proof (rw_cells_read segs m A cs k (C4 w) H Hc) as R. cbn [csize cbytes] in R.
    rewrite <- low_byte_word. exact (ov_read_bytes_prefix segs m _ 1 3 _ R).
  Qed.
End SubRead.

End ACeilS2.
