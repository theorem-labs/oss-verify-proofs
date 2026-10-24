(** Symbolic eight-byte CRC chunks and their exact suffix composition. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcLib CrcModel CrcSuffix.
Import ListNotations.
Open Scope Z_scope.
Definition eight_crc (inp : list byte) (i q : Z) : Z := raw_crc (firstn 8 (skipn (Z.to_nat i) inp)) q.
Lemma firstn8_bytes : forall (inp : list byte) i,
  0 <= i -> i+8 <= Z.of_nat (length inp) ->
  firstn 8 (skipn (Z.to_nat i) inp) =
  [bbyte inp i;bbyte inp (i+1);bbyte inp (i+2);bbyte inp (i+3);bbyte inp (i+4);bbyte inp (i+5);bbyte inp (i+6);bbyte inp (i+7)].
Proof.
  intros inp i Hi HL.
  rewrite (skipn_byte_cons inp (Z.to_nat i) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat i)) with (Z.to_nat (i+1)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+1)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+1))) with (Z.to_nat (i+2)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+2)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+2))) with (Z.to_nat (i+3)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+3)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+3))) with (Z.to_nat (i+4)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+4)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+4))) with (Z.to_nat (i+5)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+5)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+5))) with (Z.to_nat (i+6)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+6)) ltac:(lia)). cbn [firstn].
  replace (S (Z.to_nat (i+6))) with (Z.to_nat (i+7)) by lia.
  rewrite (skipn_byte_cons inp (Z.to_nat (i+7)) ltac:(lia)). cbn [firstn].
  reflexivity.
Qed.
Lemma eight_crc_bytes : forall inp i q,
  0 <= i -> i+8 <= Z.of_nat (length inp) -> eight_crc inp i q = (raw_byte (raw_byte (raw_byte (raw_byte (raw_byte (raw_byte (raw_byte (raw_byte q (bbyte inp i)) (bbyte inp (i+1))) (bbyte inp (i+2))) (bbyte inp (i+3))) (bbyte inp (i+4))) (bbyte inp (i+5))) (bbyte inp (i+6))) (bbyte inp (i+7))).
Proof. intros. unfold eight_crc. rewrite firstn8_bytes by assumption. reflexivity. Qed.
Lemma eight_crc_range : forall inp i q, 0 <= q < 2^32 -> 0 <= eight_crc inp i q < 2^32.
Proof. intros. unfold eight_crc. apply raw_crc_range;assumption. Qed.
Lemma raw_suffix_chunk : forall inp i (k : nat) q,
  0 <= i -> raw_crc (skipn (Z.to_nat i) inp) q =
  raw_crc (skipn (Z.to_nat (i+Z.of_nat k)) inp)
    (raw_crc (firstn k (skipn (Z.to_nat i) inp)) q).
Proof.
  intros inp i k q Hi.
  rewrite <- (firstn_skipn k (skipn (Z.to_nat i) inp)) at 1.
  rewrite raw_crc_append,skipn_skipn.
  replace (Z.to_nat (i+Z.of_nat k)) with (k+Z.to_nat i)%nat by lia. reflexivity.
Qed.
Lemma raw_suffix_eight : forall inp i q, 0 <= i ->
  raw_crc (skipn (Z.to_nat i) inp) q =
  raw_crc (skipn (Z.to_nat (i+8)) inp) (eight_crc inp i q).
Proof. intros. exact (raw_suffix_chunk inp i 8 q H). Qed.
