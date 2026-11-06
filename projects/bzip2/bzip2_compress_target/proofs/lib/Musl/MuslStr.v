(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require MState Mem Cells Step Arr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.MState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Mem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Cells OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Step OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section NulTerminated.
  Variables (A n : Z) (str slack : list byte).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End NulTerminated.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list MemImageType.Segment.

Lemma u8arr_write_bytes : forall m A bs (i : Z) xs,
  u8arr segs m A bs -> (0 <= i)%Z -> (Z.to_nat i + length xs <= length bs)%nat ->
  u8arr segs (write_to_mem m (wa (A + i)) xs) A (upd_bytes bs (Z.to_nat i) xs).
Proof.
  intros m A bs i xs [Hb Hw] Hi Hl. split.
  - apply bytes_at_write_inside; assumption.
  - rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.

Lemma u8arr_store_ok_n : forall m A bs (i : Z) n a,
  u8arr segs m A bs -> (0 <= i)%Z -> (i + Z.of_nat n <= Z.of_nat (length bs))%Z -> a = wa (A + i) ->
  store_ok segs m a n = true.
Proof. intros m A bs i n a [_ Hw] Hi Hn ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma rw_cells_CB_length : forall m A n bs, rw_cells segs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[H _] _]. cbn in H. tauto. Qed.
End WithSegs.

(* [comment removed for export] *)
Definition filled (c : byte) (bs : list byte) (Q : Z -> Prop) : Prop :=
  forall j, (0 <= j < Z.of_nat (length bs))%Z -> Q j -> nth_error bs (Z.to_nat j) = Some c.

Lemma filled_init : forall c bs, filled c bs (fun _ => False).
Proof. intros c bs j _ []. Qed.

(* [comment removed for export] *)

Lemma nth_error_repeat' : forall {X} (x : X) k i, (i < k)%nat -> nth_error (repeat x k) i = Some x.
Proof. intros X x k; induction k as [|k IH]; intros [|i] H; cbn; try lia; auto. apply IH. lia. Qed.

Lemma filled_upd : forall c bs Q i k,
  filled c bs Q -> (i + k <= length bs)%nat ->
  filled c (upd_bytes bs i (repeat c k)) (fun j => Q j \/ (Z.of_nat i <= j < Z.of_nat i + Z.of_nat k)%Z).
Proof.
  intros c bs Q i k HF Hk j Hj HQ. rewrite upd_bytes_length in Hj by (rewrite repeat_length; lia).
  rewrite upd_bytes_nth by (rewrite ?repeat_length; lia). rewrite repeat_length.
  destruct (Nat.leb_spec0 i (Z.to_nat j)); destruct (Nat.ltb_spec0 (Z.to_nat j) (i + k)); cbn [andb];
    first [ apply nth_error_repeat'; lia | destruct HQ as [HQ|HQ]; [apply HF; [lia| exact HQ] | exfalso; lia] ].
Qed.

Lemma filled_updZ : forall c bs Q (i : Z) k,
  filled c bs Q -> (0 <= i)%Z -> (Z.to_nat i + k <= length bs)%nat ->
  filled c (upd_bytes bs (Z.to_nat i) (repeat c k)) (fun j => Q j \/ (i <= j < i + Z.of_nat k)%Z).
Proof.
  intros c bs Q i k HF Hi Hk j Hj HQ. apply (filled_upd c bs Q (Z.to_nat i) k HF Hk j Hj). destruct HQ; [left; assumption| right; lia].
Qed.

Lemma filled_all : forall c bs Q, filled c bs Q -> (forall j, (0 <= j < Z.of_nat (length bs))%Z -> Q j) -> bs = repeat c (length bs).
Proof.
  intros c bs Q HF HQ. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite nth_error_repeat' by lia. replace i with (Z.to_nat (Z.of_nat i)) by lia. apply HF; [lia|]. apply HQ. lia.
  - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.

Lemma Z_to_bv8_mod : forall z, Z_to_bv 8 z = Z_to_bv 8 (z mod 256).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 256)%Z. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_align_down : forall x j, 0 <= x < 2^64 -> 0 <= j <= 64 ->
  Z.land x (2^64 - 2^j) = x - x mod 2^j.
Proof.
  intros x j Hx Hj.
  replace (2^64 - 2^j)%Z with (Z.ldiff (Z.ones 64) (Z.ones j)).
  2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
      replace (2^64)%Z with (2^j * 2^(64-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      replace (Z.pred (1 * (2 ^ j * 2 ^ (64 - j))))%Z with ((2^(64-j) - 1) * 2^j + (2^j - 1))%Z by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by (split; [lia| apply Z.lt_pred_l || lia]). lia. }
  rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod x (2^j)%Z ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma forallb_zseq : forall n f, forallb f (zseq n) = true -> forall c, 0 <= c < Z.of_nat n -> f c = true.
Proof.
  intros n f H c Hc. rewrite forallb_forall in H. apply H. unfold zseq. apply in_map_iff.
  exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma brute256_ok : forall (P : Z -> bool), forallb P (zseq 256) = true -> forall c, 0 <= c < 256 -> P c = true.
Proof. intros P H c Hc. exact (forallb_zseq 256 P H c Hc). Qed.

Lemma word_eq_of_eqb : forall x y : Z, (x mod 2^64 =? y mod 2^64) = true -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply Z.eqb_eq in H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

Lemma map_unsigned_inj : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Hl. f_equal; [apply bv_eq; exact Hx| apply IH; exact Hl].
Qed.

Definition list_Z_eqb (l1 l2 : list Z) : bool := if list_eq_dec Z.eq_dec l1 l2 then true else false.
Lemma list_Z_eqb_eq : forall l1 l2, list_Z_eqb l1 l2 = true -> l1 = l2.
Proof. intros l1 l2. unfold list_Z_eqb. destruct (list_eq_dec Z.eq_dec l1 l2); [auto|discriminate]. Qed.

Lemma bcast_ok : forall (F : Z -> list byte) k,
  forallb (fun c => list_Z_eqb (map bv_unsigned (F c)) (repeat c k)) (zseq 256) = true ->
  forall c, 0 <= c < 256 -> F c = repeat (Z_to_bv 8 c) k.
Proof.
  intros F k H c Hc. apply map_unsigned_inj.
  pose proof (forallb_zseq 256 _ H c Hc) as E. cbn beta in E. apply list_Z_eqb_eq in E. rewrite E.
  rewrite map_repeat. f_equal. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition BC4 := 16843009.
Definition BC8 := 72340172838076673.

(* [comment removed for export] *)
Lemma le4_bcast : forall c, 0 <= c < 256 -> le4 (Z_to_bv 64 (c * BC4)) = repeat (Z_to_bv 8 c) 4.
Proof. apply (bcast_ok (fun c => le4 (Z_to_bv 64 (c * BC4))) 4). vm_compute. reflexivity. Qed.
Lemma le8_bcast : forall c, 0 <= c < 256 -> le8 (Z_to_bv 64 (c * BC8)) = repeat (Z_to_bv 8 c) 8.
Proof. apply (bcast_ok (fun c => le8 (Z_to_bv 64 (c * BC8))) 8). vm_compute. reflexivity. Qed.
Lemma le1_byte : forall x : word, le1 x = [Z_to_bv 8 (bv_unsigned x mod 256)].
Proof. intros x. cbn. rewrite <- Z_to_bv8_mod. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma bv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.

Lemma le_bytes_to_word4 : forall b0 b1 b2 b3 : byte,
  bv_unsigned (le_bytes_to_word [b0;b1;b2;b3]) = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.
Proof.
  intros. unfold le_bytes_to_word. rewrite bytes_le_to_Z_le_val. cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lw_unsigned4 : forall b0 b1 b2 b3 : byte,
  bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word [b0;b1;b2;b3]))) =
  bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3 + (2^64 - 2^32) * (bv_unsigned b3 / 128).
Proof.
  intros. rewrite sext_small, Z_to_bv_unsigned, signed_of_extract, le_bytes_to_word4 by reflexivity.
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  rewrite bv_swrap32_eq. change (bv_wrap 64 ?x) with (x mod 2^64).
  Z.div_mod_to_equations. lia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma le4_of_mod32 : forall (v : word) (bs : list byte), length bs = 4%nat ->
  bv_unsigned v mod 2^32 = le_val (map bv_unsigned bs) -> le4 v = bs.
Proof.
  intros v bs Hl Hv. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). change (2 ^ 32) with (2^32) in *. rewrite Hv.
  rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma le4_lw : forall w : list byte, length w = 4%nat -> le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word w))) = w.
Proof.
  intros w Hl. destruct w as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try (cbn in Hl; discriminate).
  apply le4_of_mod32; [reflexivity|]. rewrite lw_unsigned4. cbn [map le_val].
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
