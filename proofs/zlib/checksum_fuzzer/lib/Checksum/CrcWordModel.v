(** Relate a four-byte little-endian load to the bytewise CRC model. *)
From Stdlib Require Import ZArith NArith List Lia Bool Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcAlgebra CrcLib CrcLinearBasis CrcByteStep CrcModel.
Import ListNotations.
Open Scope Z_scope.
Opaque csteps.
Definition word_bytes (w : Z) : list byte :=
  [Z_to_bv 8 w; Z_to_bv 8 (Z.shiftr w 8);
   Z_to_bv 8 (Z.shiftr w 16); Z_to_bv 8 (Z.shiftr w 24)].
Definition word_serial (w : Z) : Z :=
  csteps 8 (Z.lxor
    (csteps 8 (Z.lxor
      (csteps 8 (Z.lxor (csteps 8 (w mod 256)) ((Z.shiftr w 8) mod 256)))
      ((Z.shiftr w 16) mod 256))) ((Z.shiftr w 24) mod 256)).
Lemma word_serial_zero : word_serial 0 = 0.
Proof. unfold word_serial. rewrite !csteps_zero. reflexivity. Qed.
Lemma word_serial_linear : forall a b,
  word_serial (Z.lxor a b) = Z.lxor (word_serial a) (word_serial b).
Proof.
  intros a b. unfold word_serial. rewrite !Z.shiftr_lxor,!low8_xor.
  rewrite !csteps_xor. apply Z.bits_inj'. intros k Hk.
  rewrite !Z.lxor_spec.
  btauto.
Qed.
Definition word_serial_check : bool := forallb (fun i =>
  word_serial (2^Z.of_nat i) =? csteps 32 (2^Z.of_nat i)) (seq 0 32).
Lemma word_serial_checked : word_serial_check = true.
Proof. vm_compute. reflexivity. Qed.
Theorem word_serial_value : forall w, 0 <= w < 2^32 -> word_serial w = csteps 32 w.
Proof.
  intros w Hw. eapply linear32_equal with (f:=word_serial) (g:=csteps 32);
    [apply word_serial_zero|apply csteps_zero|apply word_serial_linear|apply csteps_xor| |exact Hw].
  intros i Hi. apply Z.eqb_eq.
  exact (forallb_seq _ 0 32 i word_serial_checked ltac:(lia)).
Qed.
Lemma word_bytes_length : forall w, length (word_bytes w) = 4%nat.
Proof. reflexivity. Qed.
Lemma raw_word_zero : forall w, raw_crc (word_bytes w) 0 = word_serial w.
Proof.
  intros w. unfold word_bytes,word_serial. cbn [raw_crc raw_byte].
  first [reflexivity | rewrite Z.lxor_0_l; reflexivity].
Qed.
Theorem raw_word_value : forall w q, 0 <= w < 2^32 ->
  raw_crc (word_bytes w) q = csteps 32 (Z.lxor q w).
Proof.
  intros w q Hw.
  pose proof (raw_crc_xor (word_bytes w) q 0) as H.
  rewrite Z.lxor_0_r,word_bytes_length,raw_word_zero,word_serial_value in H by exact Hw.
  rewrite H,csteps_xor. reflexivity.
Qed.
Lemma word_bytes_little_endian : forall w, word_bytes w = Z_to_le_bytes 4 w.
Proof.
  intros w. unfold word_bytes. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia. reflexivity.
Qed.
Theorem raw_four_bytes_value : forall (bs : list byte) q,
  length bs = 4%nat -> raw_crc bs q = csteps 32 (Z.lxor q (bytes_le_to_Z bs)).
Proof.
  intros bs q HL. rewrite <- (Z_to_le_bytes_roundtrip bs) at 1.
  rewrite HL,<-word_bytes_little_endian. apply raw_word_value.
  split; [apply bytes_le_to_Z_nonneg|].
  pose proof (bytes_le_to_Z_bound bs). rewrite HL in H. exact H.
Qed.
