(** Streaming Adler identity in the exact packed-word form used by the fuzzer. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import AdlerModel AdlerWord.
Import ListNotations.
Open Scope Z_scope.
Definition adler_model (seed : Z) (bs : list byte) : Z :=
  adler_output bs (seed mod 65536) (Z.shiftr seed 16).
Lemma adler_model_packed : forall bs a b,
  0 <= a < ADLER_BASE -> 0 <= b < ADLER_BASE ->
  adler_model (adler_pack a b) bs = adler_output bs a b.
Proof. intros. unfold adler_model. rewrite adler_pack_low,adler_pack_high by assumption. reflexivity. Qed.
Lemma adler_output_components : forall bs a b,
  exists u v, 0 <= u < ADLER_BASE /\ 0 <= v < ADLER_BASE /\ adler_output bs a b = adler_pack u v.
Proof.
  intros. unfold adler_output. destruct (adler_raw bs a b) as [u v].
  exists (u mod ADLER_BASE),(v mod ADLER_BASE).
  repeat split;try reflexivity;apply Z.mod_pos_bound;unfold ADLER_BASE;lia.
Qed.
Lemma adler_output_feed : forall xs ys a b,
  adler_output (xs++ys) a b = adler_model (adler_output xs a b) ys.
Proof.
  intros xs ys a b.
  assert (E : adler_output xs a b =
    let '(u,v) := adler_raw xs a b in adler_pack (u mod ADLER_BASE) (v mod ADLER_BASE)) by reflexivity.
  rewrite E,adler_chunk_append. destruct (adler_raw xs a b) as [u v].
  symmetry. apply adler_model_packed;apply Z.mod_pos_bound;unfold ADLER_BASE;lia.
Qed.
Theorem adler_model_append : forall seed xs ys,
  adler_model seed (xs++ys) = adler_model (adler_model seed xs) ys.
Proof. intros. unfold adler_model at 1 3. apply adler_output_feed. Qed.
Lemma adler_model_range : forall seed bs, 0 <= adler_model seed bs < 2^32.
Proof. intros. apply adler_output_range. Qed.
Lemma adler_model_valid_seed : forall seed bs,
  exists a b, 0 <= a < ADLER_BASE /\ 0 <= b < ADLER_BASE /\ adler_model seed bs = adler_pack a b.
Proof. intros. apply adler_output_components. Qed.
Lemma adler_initial_word : adler_pack 1 0 = 1.
Proof. reflexivity. Qed.
Lemma adler_model_initial : forall bs, adler_model 1 bs = adler_output bs 1 0.
Proof. intros. change 1 with (adler_pack 1 0) at 1. apply adler_model_packed;unfold ADLER_BASE;lia. Qed.
Lemma adler_model_empty : forall a b,
  0 <= a < ADLER_BASE -> 0 <= b < ADLER_BASE -> adler_model (adler_pack a b) [] = adler_pack a b.
Proof.
  intros. rewrite adler_model_packed by assumption. unfold adler_output. cbn [adler_raw].
  rewrite !Z.mod_small by assumption. reflexivity.
Qed.
