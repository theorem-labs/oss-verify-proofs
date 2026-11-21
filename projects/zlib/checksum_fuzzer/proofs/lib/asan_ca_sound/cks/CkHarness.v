(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.cks Require Import
  CkTables CkModel CkXt CkMultmodp CkMathCrc CkMathAdler.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma harness_crc_init : crc32_spec 0 [] = 0.
Proof. apply crc32_spec_nil. lia. Qed.

Lemma harness_adler_init : adler_spec 1 [] = 1.
Proof. apply adler_spec_nil. apply adler_ok_1. Qed.


Theorem harness_crc_stream : forall a A B, bytes A -> bytes B ->
  crc32_z_model a (crc32_spec 0 A) B = crc32_spec 0 (A ++ B).
Proof.
  intros a A B HA HB. rewrite crc32_z_model_spec by exact HB.
  apply crc32_spec_app. exact HA.
Qed.

Theorem harness_assert1 : forall a0 a1 c B, bytes B -> 0 <= c < 2 ^ 32 -> 1 <= Zlen B < 2 ^ 29 ->
  crc32_z_model a1 c B = crc32_combine_op c (crc32_z_model a0 0 B) (crc32_combine_gen (Zlen B)).
Proof.
  intros a0 a1 c B HB Hc HL. rewrite !crc32_z_model_spec by exact HB.
  symmetry. apply crc32_combine_op_spec; [exact HB | exact Hc | lia].
Qed.

Theorem harness_crc_whole : forall a D, bytes D -> crc32_model a 0 D = crc32_spec 0 D.
Proof. intros a D HD. unfold crc32_model. apply crc32_z_model_spec. exact HD. Qed.

Theorem harness_assert2 : forall a a' A T, bytes A -> bytes T ->
  crc32_z_model a (crc32_spec 0 A) T = crc32_model a' 0 (A ++ T).
Proof.
  intros a a' A T HA HT. rewrite harness_crc_stream by assumption.
  symmetry. apply harness_crc_whole. apply bytes_app; assumption.
Qed.

Theorem harness_assert3 : forall crc1 crc2 len, crc1 = crc2 ->
  crc32_combine crc1 crc2 len = crc32_combine crc1 crc1 len.
Proof. intros crc1 crc2 len ->. reflexivity. Qed.

Theorem harness_assert4 : forall crc1 crc2 op, crc1 = crc2 ->
  crc32_combine_op crc1 crc2 op = crc32_combine_op crc2 crc1 op.
Proof. intros crc1 crc2 op ->. reflexivity. Qed.

Theorem harness_assert5 : forall crc1 crc2 len, crc1 = crc2 ->
  crc32_combine crc1 crc2 len = crc32_combine_op crc2 crc1 (crc32_combine_gen len).
Proof. intros crc1 crc2 len ->. apply crc32_combine_gen_op. Qed.


Theorem crc32_combine_op_range : forall crc1 crc2 op, 0 <= crc1 < 2 ^ 32 ->
  0 <= crc32_combine_op crc1 crc2 op < 2 ^ 32.
Proof.
  (* 1.4: the op = 0 branch is 0; crc1 is masked before multmodp *)
  intros crc1 crc2 op Hc. unfold crc32_combine_op.
  destruct (op =? 0); [lia|].
  apply lxor_bound32.
  - apply multmodp_range. rewrite land_M32. apply Z.mod_pos_bound. lia.
  - rewrite land_M32. apply Z.mod_pos_bound. lia.
Qed.

Theorem crc32_combine_range : forall crc1 crc2 len, 0 <= crc1 < 2 ^ 32 ->
  0 <= crc32_combine crc1 crc2 len < 2 ^ 32.
Proof. intros. rewrite crc32_combine_gen_op. apply crc32_combine_op_range. assumption. Qed.

Theorem crc32_combine_gen_range : forall len, 0 <= crc32_combine_gen len < 2 ^ 32.
Proof.
  (* 1.4: a negative length gives 0 *)
  intros. unfold crc32_combine_gen, crc32_combine_gen64. destruct (len <? 0); [lia|]. apply x2nmodp_range_any.
Qed.

Theorem crc32_combine_gen_nz : forall len, 0 <= len < 2 ^ 29 ->
  crc32_combine_gen len mod 2 ^ 32 <> 0.
Proof.
  intros len Hl. unfold crc32_combine_gen, crc32_combine_gen64.
  (* 1.4: the length is not negative here *)
  rewrite (proj2 (Z.ltb_ge len 0)) by lia.
  apply x2nmodp_nz_mod; lia.
Qed.

Theorem crc32_model_range : forall a c D, bytes D -> 0 <= crc32_model a c D < 2 ^ 32.
Proof. intros. unfold crc32_model. apply crc32_z_model_range. assumption. Qed.


Theorem harness_adler_stream : forall A B, bytes A -> bytes B ->
  adler32_z_model (adler_spec 1 A) B = adler_spec 1 (A ++ B).
Proof.
  intros A B HA HB.
  rewrite adler32_z_model_spec by (try apply adler_spec_ok; try apply adler_ok_1; exact HB).
  apply adler_spec_app. apply adler_ok_1.
Qed.

Theorem harness_adler_whole : forall D, bytes D -> adler32_model 1 D = adler_spec 1 D.
Proof. intros D HD. unfold adler32_model. apply adler32_z_model_spec; [apply adler_ok_1 | exact HD]. Qed.

Theorem harness_assert6 : forall A T, bytes A -> bytes T ->
  adler32_z_model (adler_spec 1 A) T = adler32_model 1 (A ++ T).
Proof.
  intros A T HA HT. rewrite harness_adler_stream by assumption.
  symmetry. apply harness_adler_whole. apply bytes_app; assumption.
Qed.

Theorem harness_assert7 : forall adler1 adler2 len, adler1 = adler2 ->
  adler32_combine_model adler1 adler2 len = adler32_combine_model adler1 adler1 len.
Proof. intros adler1 adler2 len ->. reflexivity. Qed.

Theorem adler_spec_1_range : forall D, 0 <= adler_spec 1 D < 2 ^ 32.
Proof. intros. apply adler_spec_range. apply adler_ok_1. Qed.

Theorem adler_spec_1_ok : forall D, adler_ok (adler_spec 1 D).
Proof. intros. apply adler_spec_ok. apply adler_ok_1. Qed.

Theorem adler32_model_range : forall adler D, bytes D -> 0 <= adler32_model adler D < 2 ^ 32.
Proof. intros. unfold adler32_model. apply adler32_z_model_range. assumption. Qed.


Lemma chunk_app : forall (off k : nat) (D : list Z),
  firstn off D ++ firstn k (skipn off D) = firstn (off + k) D.
Proof. intros. apply firstn_add_skipn. Qed.

Lemma chunk_tail : forall (off : nat) (D : list Z), firstn off D ++ skipn off D = D.
Proof. intros. apply firstn_skipn. Qed.

Lemma chunk_bytes : forall (off k : nat) (D : list Z), bytes D -> bytes (firstn k (skipn off D)).
Proof. intros. apply bytes_firstn, bytes_skipn. assumption. Qed.

Lemma prefix_bytes : forall (off : nat) (D : list Z), bytes D -> bytes (firstn off D).
Proof. intros. apply bytes_firstn. assumption. Qed.

Lemma tail_bytes : forall (off : nat) (D : list Z), bytes D -> bytes (skipn off D).
Proof. intros. apply bytes_skipn. assumption. Qed.


Definition buff_size (D : list Z) : Z := let b := hd 0 D in if b =? 0 then 1 else b.

Fixpoint crc_chunks (fuel : nat) (bs : nat) (c : Z) (D : list Z) : Z :=
  match fuel with
  | O => c
  | S f => if (length D <? bs)%nat then crc32_z_model 0 c D
           else crc_chunks f bs (crc32_z_model 0 c (firstn bs D)) (skipn bs D)
  end.

Fixpoint adler_chunks (fuel : nat) (bs : nat) (ad : Z) (D : list Z) : Z :=
  match fuel with
  | O => ad
  | S f => if (length D <? bs)%nat then adler32_z_model ad D
           else adler_chunks f bs (adler32_z_model ad (firstn bs D)) (skipn bs D)
  end.

Definition harness_crc1 (D : list Z) : Z :=
  crc_chunks (S (length D)) (Z.to_nat (buff_size D)) 0 D.
Definition harness_adler1 (D : list Z) : Z :=
  adler_chunks (S (length D)) (Z.to_nat (buff_size D)) 1 D.

Lemma crc_chunks_spec : forall fuel bs A D, bytes A -> bytes D -> (0 < bs)%nat -> (length D < fuel * bs)%nat ->
  crc_chunks fuel bs (crc32_spec 0 A) D = crc32_spec 0 (A ++ D).
Proof.
  induction fuel as [|f IH]; intros bs A D HA HD Hbs Hf; [cbn in Hf; lia|].
  cbn [crc_chunks]. destruct (Nat.ltb_spec (length D) bs) as [Hlt|Hge].
  - apply harness_crc_stream; assumption.
  - rewrite harness_crc_stream by (try apply bytes_firstn; assumption).
    rewrite IH; try assumption.
    + rewrite <- app_assoc, firstn_skipn. reflexivity.
    + apply bytes_app; [exact HA | apply bytes_firstn; exact HD].
    + apply bytes_skipn. exact HD.
    + rewrite length_skipn. cbn in Hf. lia.
Qed.

Theorem harness_crc1_spec : forall D, bytes D -> harness_crc1 D = crc32_spec 0 D.
Proof.
  intros D HD. unfold harness_crc1.
  replace (crc_chunks (S (length D)) (Z.to_nat (buff_size D)) 0 D)
     with (crc_chunks (S (length D)) (Z.to_nat (buff_size D)) (crc32_spec 0 []) D)
       by (rewrite harness_crc_init; reflexivity).
  pose proof (bytes_hd D HD).
  assert (Hbs : (0 < Z.to_nat (buff_size D))%nat)
    by (unfold buff_size; destruct (Z.eqb_spec (hd 0 D) 0); lia).
  apply (crc_chunks_spec (S (length D)) _ [] D); [apply Forall_nil | exact HD | exact Hbs | nia].
Qed.

Lemma adler_chunks_spec : forall fuel bs A D, bytes A -> bytes D -> (0 < bs)%nat -> (length D < fuel * bs)%nat ->
  adler_chunks fuel bs (adler_spec 1 A) D = adler_spec 1 (A ++ D).
Proof.
  induction fuel as [|f IH]; intros bs A D HA HD Hbs Hf; [cbn in Hf; lia|].
  cbn [adler_chunks]. destruct (Nat.ltb_spec (length D) bs) as [Hlt|Hge].
  - apply harness_adler_stream; assumption.
  - rewrite harness_adler_stream by (try apply bytes_firstn; assumption).
    rewrite IH; try assumption.
    + rewrite <- app_assoc, firstn_skipn. reflexivity.
    + apply bytes_app; [exact HA | apply bytes_firstn; exact HD].
    + apply bytes_skipn. exact HD.
    + rewrite length_skipn. cbn in Hf. lia.
Qed.

Theorem harness_adler1_spec : forall D, bytes D -> harness_adler1 D = adler_spec 1 D.
Proof.
  intros D HD. unfold harness_adler1.
  replace (adler_chunks (S (length D)) (Z.to_nat (buff_size D)) 1 D)
     with (adler_chunks (S (length D)) (Z.to_nat (buff_size D)) (adler_spec 1 []) D)
       by (rewrite harness_adler_init; reflexivity).
  pose proof (bytes_hd D HD).
  assert (Hbs : (0 < Z.to_nat (buff_size D))%nat)
    by (unfold buff_size; destruct (Z.eqb_spec (hd 0 D) 0); lia).
  apply (adler_chunks_spec (S (length D)) _ [] D); [apply Forall_nil | exact HD | exact Hbs | nia].
Qed.

Theorem harness_asserts_hold : forall D, bytes D -> 1 <= Zlen D <= 2 ^ 20 ->
  let crc1 := harness_crc1 D in
  let crc2 := crc32_model 0 0 D in
  let op := crc32_combine_gen (Zlen D) in
  let adler1 := harness_adler1 D in
  let adler2 := adler32_model 1 D in
  crc1 = crc2 /\
  crc32_combine crc1 crc2 (Zlen D) = crc32_combine crc1 crc1 (Zlen D) /\
  crc32_combine_op crc1 crc2 op = crc32_combine_op crc2 crc1 op /\
  crc32_combine crc1 crc2 (Zlen D) = crc32_combine_op crc2 crc1 op /\
  adler1 = adler2 /\
  adler32_combine_model adler1 adler2 (Zlen D) = adler32_combine_model adler1 adler1 (Zlen D).
Proof.
  intros D HD HL. cbv zeta.
  rewrite harness_crc1_spec, harness_crc_whole, harness_adler1_spec, harness_adler_whole by exact HD.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply crc32_combine_gen_op|]. split; reflexivity.
Qed.

Example ck_harness_1 :
  let D := [7; 11; 48; 85; 122; 159; 196; 233; 14; 51; 88; 125; 162; 199; 236; 17; 54; 91; 128; 165;
            202; 239; 20; 57; 94; 131; 168; 205; 242; 23; 60; 97; 134; 171; 208; 245; 26; 63; 100; 137;
            174; 211; 248; 29; 66; 103; 140; 177; 214; 251; 32; 69; 106; 143; 180; 217; 254; 35; 72; 109; 146] in
  (harness_crc1 D, crc32_model 0 0 D, harness_adler1 D, adler32_model 1 D)
  = (3152701231, 3152701231, 2053447278, 2053447278).
Proof. vm_compute. reflexivity. Qed.

Example ck_harness_2 :
  let D := [0; 5; 255] in
  (harness_crc1 D, crc32_model 0 0 D, harness_adler1 D, adler32_model 1 D)
  = (2939470554, 2939470554, 17563909, 17563909).
Proof. vm_compute. reflexivity. Qed.
