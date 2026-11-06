(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 604 of its 627 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/check_step.v, with its module paths and module names changed; 89 of its 131 lines of code are new or changed and 585 lines of the source are left out. *)
(* Pure facts for segment S3 of the ASan walk of check_step (fuzz_scene.asan): the 50-byte frame object that the two
   __asan_memcpy calls build (0x83500: 16 bytes of __const.check_step.frame; 0x83510: the 34-byte block blk), what
   reac_ctrl_parse's model returns on it, and the 32 control-block bytes frame[18..50) that
   reac_ctrl_checksum_verify sums. No kit, no Section.
   scene_fields_length, scene_block_length, cks_sum and byte_sum_nonneg are copies of lib/Prog/check_step.v:33-57
   (that file is not Required here). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_check_step_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac norm_nat_lits :=
  repeat match goal with
  | H : context [Nat.of_num_uint ?u] |- _ =>
      let v := eval vm_compute in (Nat.of_num_uint u) in change (Nat.of_num_uint u) with v in H
  end.
(* Copies of lib/Prog/check_step.v:33-57. *)
Lemma scene_fields_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_fields b k) = 31%nat.
Proof.
  intros b k Hb Hk. norm_nat_lits. unfold scene_fields, scene_payload, scene_off.
  destruct (Z.eqb_spec k 0); [subst; cbn [length app]; rewrite length_firstn, Hb; reflexivity|].
  destruct (Z.eqb_spec k 342).
  - cbn [length app]. rewrite length_app, length_firstn, length_skipn, Hb. reflexivity.
  - cbn [length app]. rewrite length_firstn, length_skipn, Hb. lia.
Qed.
Lemma scene_block_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_block b k) = 34%nat.
Proof.
  intros b k Hb Hk. unfold scene_block. rewrite !length_app, scene_fields_length by assumption. reflexivity.
Qed.
Lemma cks_sum : forall S, 0 <= S -> (S + bv_unsigned (Z_to_bv 8 ((256 - S mod 256) mod 256))) mod 256 = 0.
Proof.
  intros S HS. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8).
  Z.div_mod_to_equations. lia.
Qed.
Lemma byte_sum_nonneg : forall l, 0 <= byte_sum l.
Proof.
  induction l as [|x l IH]; cbn [byte_sum fold_right]; [lia|].
  pose proof (bv_unsigned_in_range 8 x). unfold byte_sum in IH. lia.
Qed.
(* The frame object at the parse call. *)
Definition s3_fr (b : list byte) (k : Z) : list byte := firstn 16 cs_frame_init ++ scene_block b k.
Definition s3_bs (b : list byte) (k : Z) : list Z := map (fun i => cp_v (s3_fr b k) (18 + i)) (seq 0 32).
(* firstn 16 cs_frame_init, spelled out. *)
Definition cs_hd16 : list byte :=
  [Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 0; Z_to_bv 8 64;
   Z_to_bv 8 171; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0].
Lemma s3_fr_eq : forall b k, s3_fr b k = cs_hd16 ++ scene_block b k.
Proof. intros b k. reflexivity. Qed.
Lemma bvu8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.
Lemma nth_map_seq : forall (f : nat -> Z) n m d, (m < n)%nat -> nth m (map f (seq 0 n)) d = f m.
Proof.
  intros f n m d Hm. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hm).
  rewrite map_nth, seq_nth by exact Hm. reflexivity.
Qed.
Lemma byte_sum_app : forall l1 l2, byte_sum (l1 ++ l2) = byte_sum l1 + byte_sum l2.
Proof.
  intros l1 l2. induction l1 as [|x l1 IH]; unfold byte_sum in *; cbn [app fold_right] in *; lia.
Qed.
Lemma byte_sum_one : forall x, byte_sum [x] = bv_unsigned x.
Proof. intros x. unfold byte_sum. cbn [fold_right]. lia. Qed.
Lemma psum_app_le : forall l l' n, (n <= length l)%nat -> psum (l ++ l') n = psum l n.
Proof.
  intros l l' n. induction n as [|n IH]; intros H; cbn [psum]; [reflexivity|].
  rewrite IH by lia. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma psum_byte_sum : forall l, psum l (length l) = byte_sum l.
Proof.
  induction l as [|x l IH] using rev_ind; [reflexivity|].
  rewrite length_app. cbn [length]. rewrite Nat.add_1_r. cbn [psum].
  rewrite psum_app_le by lia. rewrite IH, nth_middle, byte_sum_app, byte_sum_one. reflexivity.
Qed.
(* The statements S3 uses. *)
Lemma s3_fr_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (s3_fr b k) = 50%nat.
Proof.
  intros b k Hb Hk. rewrite s3_fr_eq, length_app, scene_block_length by assumption. reflexivity.
Qed.
Lemma s3_fr_lo : forall b k i, (i < 16)%nat -> cp_b (s3_fr b k) i = nth i cs_frame_init (Z_to_bv 8 0).
Proof.
  intros b k i Hi. unfold cp_b. rewrite s3_fr_eq.
  do 16 (destruct i as [|i]; [reflexivity|]). lia.
Qed.
Lemma s3_fr_hi : forall b k i, length b = 8904%nat -> 0 <= k <= 342 -> (16 <= i < 50)%nat ->
  cp_b (s3_fr b k) i = nth (i - 16) (scene_block b k) (Z_to_bv 8 0).
Proof.
  intros b k i Hb Hk Hi. unfold cp_b. rewrite s3_fr_eq.
  rewrite app_nth2 by (unfold cs_hd16; cbn [length]; lia).
  replace (i - length cs_hd16)%nat with (i - 16)%nat by reflexivity. reflexivity.
Qed.
Lemma s3_fr_v : forall b k,
  cp_v (s3_fr b k) 12 = 0x88 /\ cp_v (s3_fr b k) 13 = 0x19 /\ cp_v (s3_fr b k) 16 = 0xcd /\
  cp_v (s3_fr b k) 17 = 0xea /\ cp_v (s3_fr b k) 18 = 1 /\ cp_v (s3_fr b k) 22 = 0.
Proof.
  intros b k. unfold cp_v, cp_b. rewrite s3_fr_eq. unfold cs_hd16, scene_block, scene_fields. cbn [nth app].
  rewrite !bvu8 by lia. repeat split; reflexivity.
Qed.
Lemma s3_fr_parse : forall b k, length b = 8904%nat -> 0 <= k <= 342 ->
  let P := ctrlparse 50 (s3_fr b k) in
  fst P = 2 /\ nth 22 (snd P) cp_z = Z_to_bv 8 1 /\ nth 23 (snd P) cp_z = Z_to_bv 8 (scene_seg k) /\
  nth 24 (snd P) cp_z = Z_to_bv 8 (scene_len k) /\ nth 25 (snd P) cp_z = Z_to_bv 8 0 /\ nth 26 (snd P) cp_z = Z_to_bv 8 0.
Proof.
  intros b k Hb Hk. cbv zeta.
  destruct (s3_fr_v b k) as (V12 & V13 & V16 & V17 & V18 & V22).
  assert (Hhdr : cp_hdr 50 (s3_fr b k) = true) by (unfold cp_hdr; rewrite V12, V13; reflexivity).
  assert (Hkind : cp_kind (s3_fr b k) = 2) by (unfold cp_kind, cp_type; rewrite V16, V17, V18, V22; reflexivity).
  unfold ctrlparse. rewrite Hhdr, Hkind. cbn [fst snd]. split; [reflexivity|].
  unfold cp_struct. cbn [nth app].
  unfold cp_b. rewrite s3_fr_eq. unfold cs_hd16, scene_block, scene_fields. cbn [nth app].
  repeat split; reflexivity.
Qed.
Lemma s3_bs_map : forall b k, length b = 8904%nat -> 0 <= k <= 342 ->
  map (Z_to_bv 8) (s3_bs b k) =
  scene_fields b k ++ [Z_to_bv 8 ((256 - byte_sum (scene_fields b k) mod 256) mod 256)].
Proof.
  intros b k Hb Hk. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - unfold s3_bs. rewrite length_map, length_map, length_seq, length_app, scene_fields_length by assumption.
    reflexivity.
  - intros n Hn. unfold s3_bs in *. rewrite length_map, length_map, length_seq in Hn.
    rewrite (map_nth (Z_to_bv 8)). rewrite nth_map_seq by exact Hn.
    unfold cp_v. rewrite Z_to_bv_bv_unsigned. unfold cp_b. rewrite s3_fr_eq. unfold cs_hd16, scene_block.
    cbn [nth app Nat.add]. reflexivity.
Qed.
Lemma s3_bs_ok : forall b k, length b = 8904%nat -> 0 <= k <= 342 ->
  length (s3_bs b k) = 32%nat /\ (forall j, (j < 32)%nat -> 0 <= nth j (s3_bs b k) 0 < 256) /\
  blocksum (map (Z_to_bv 8) (s3_bs b k)) = 0.
Proof.
  intros b k Hb Hk. split; [unfold s3_bs; rewrite length_map, length_seq; reflexivity|]. split.
  - intros j Hj. unfold s3_bs. rewrite nth_map_seq by exact Hj. unfold cp_v.
    pose proof (bv_unsigned_in_range 8 (cp_b (s3_fr b k) (18 + j))) as R. change (bv_modulus 8) with 256 in R. lia.
  - unfold blocksum. rewrite (s3_bs_map b k Hb Hk).
    set (F := scene_fields b k).
    replace 32%nat with (length (F ++ [Z_to_bv 8 ((256 - byte_sum F mod 256) mod 256)]))
      by (rewrite length_app; unfold F; rewrite scene_fields_length by assumption; reflexivity).
    rewrite psum_byte_sum, byte_sum_app, byte_sum_one.
    exact (cks_sum (byte_sum F) (byte_sum_nonneg F)).
Qed.
