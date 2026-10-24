(** Input slices and streaming invariants for the actual fuzzer loops.
    These lemmas do not establish the machine loop or catalog target. *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Mem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcModel AdlerComposition.
Import ListNotations.
Open Scope Z_scope.
Lemma fuzzer_bytes_slice : forall segs m A bs offset count,
  bytes_at segs m A bs -> (offset+count <= length bs)%nat ->
  bytes_at segs m (A+Z.of_nat offset) (firstn count (skipn offset bs)).
Proof.
  intros segs m A bs offset count H HN.
  rewrite <- (firstn_skipn offset bs) in H.
  apply (proj1 (bytes_at_app segs m A (firstn offset bs) (skipn offset bs))) in H.
  destruct H as [_ H]. rewrite firstn_length,Nat.min_l in H by lia.
  rewrite <- (firstn_skipn count (skipn offset bs)) in H.
  apply (proj1 (bytes_at_app segs m (A+Z.of_nat offset)
    (firstn count (skipn offset bs)) (skipn count (skipn offset bs)))) in H.
  exact (proj1 H).
Qed.
Lemma fuzzer_crc_suffix_chunk : forall bs offset count q,
  crc_model q (skipn offset bs) =
  crc_model (crc_model q (firstn count (skipn offset bs))) (skipn (offset+count) bs).
Proof.
  intros. replace (skipn (offset+count) bs) with (skipn count (skipn offset bs))
    by (rewrite skipn_skipn;f_equal;lia).
  rewrite <- crc_model_append,firstn_skipn.
  reflexivity.
Qed.
Lemma fuzzer_adler_suffix_chunk : forall bs offset count seed,
  adler_model seed (skipn offset bs) =
  adler_model (adler_model seed (firstn count (skipn offset bs))) (skipn (offset+count) bs).
Proof.
  intros. replace (skipn (offset+count) bs) with (skipn count (skipn offset bs))
    by (rewrite skipn_skipn;f_equal;lia).
  rewrite <- adler_model_append,firstn_skipn.
  reflexivity.
Qed.
Lemma fuzzer_slice_length : forall (bs : list byte) offset count,
  (offset+count <= length bs)%nat -> length (firstn count (skipn offset bs)) = count.
Proof. intros. rewrite firstn_length,skipn_length,Nat.min_l;lia. Qed.
