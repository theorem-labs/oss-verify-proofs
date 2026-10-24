(** Functional invariant for the fixed CRC routine's five parallel chains.
    This is algebra; instruction and memory contracts are separate obligations. *)
From Stdlib Require Import ZArith NArith List Lia Bool Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcAlgebra CrcLinearBasis CrcByteStep CrcModel CrcWordModel.
Import ListNotations.
Open Scope Z_scope.
Opaque csteps.

Lemma csteps_commute : forall n k q, csteps n (csteps k q) = csteps k (csteps n q).
Proof. intros. rewrite <-!csteps_add,Nat.add_comm. reflexivity. Qed.

Definition word_update (q w : Z) := csteps 32 (Z.lxor q w).
Definition braid_update (q w : Z) := csteps 160 (Z.lxor q w).
Definition merge5 (c0 c1 c2 c3 c4 : Z) :=
  Z.lxor (csteps 128 c0) (Z.lxor (csteps 96 c1)
    (Z.lxor (csteps 64 c2) (Z.lxor (csteps 32 c3) c4))).
Definition block5 (q w0 w1 w2 w3 w4 : Z) :=
  word_update (word_update (word_update (word_update (word_update q w0) w1) w2) w3) w4.

Lemma merge5_zero : merge5 0 0 0 0 0 = 0.
Proof. unfold merge5. rewrite !csteps_zero. reflexivity. Qed.
Lemma merge5_initial : forall q, merge5 q 0 0 0 0 = csteps 128 q.
Proof. intros. unfold merge5. rewrite !csteps_zero. cbn. apply Z.lxor_0_r. Qed.
Lemma merge5_linear : forall a0 a1 a2 a3 a4 b0 b1 b2 b3 b4,
  merge5 (Z.lxor a0 b0) (Z.lxor a1 b1) (Z.lxor a2 b2) (Z.lxor a3 b3) (Z.lxor a4 b4) =
  Z.lxor (merge5 a0 a1 a2 a3 a4) (merge5 b0 b1 b2 b3 b4).
Proof.
  intros. unfold merge5. rewrite !csteps_xor.
  apply Z.bits_inj'. intros k Hk. rewrite !Z.lxor_spec. btauto.
Qed.
Lemma merge5_csteps : forall n c0 c1 c2 c3 c4,
  merge5 (csteps n c0) (csteps n c1) (csteps n c2) (csteps n c3) (csteps n c4) =
  csteps n (merge5 c0 c1 c2 c3 c4).
Proof.
  intros. unfold merge5. rewrite !csteps_xor.
  rewrite (csteps_commute 128 n),(csteps_commute 96 n),
    (csteps_commute 64 n),(csteps_commute 32 n). reflexivity.
Qed.
Lemma block5_value : forall q w0 w1 w2 w3 w4,
  block5 q w0 w1 w2 w3 w4 =
  Z.lxor (csteps 160 q) (csteps 32 (merge5 w0 w1 w2 w3 w4)).
Proof.
  intros. unfold block5,word_update,merge5. rewrite !csteps_xor.
  repeat rewrite <-csteps_add. cbn [Nat.add].
  apply Z.bits_inj'. intros k Hk. rewrite !Z.lxor_spec. btauto.
Qed.
Theorem braid_step_preserves_serial : forall q c0 c1 c2 c3 c4 w0 w1 w2 w3 w4,
  merge5 c0 c1 c2 c3 c4 = csteps 128 q ->
  merge5 (braid_update c0 w0) (braid_update c1 w1)
    (braid_update c2 w2) (braid_update c3 w3) (braid_update c4 w4) =
  csteps 128 (block5 q w0 w1 w2 w3 w4).
Proof.
  intros q c0 c1 c2 c3 c4 w0 w1 w2 w3 w4 H.
  unfold braid_update. rewrite merge5_csteps,merge5_linear,H,block5_value,!csteps_xor.
  rewrite <-!csteps_add. reflexivity.
Qed.

Definition braid_finish (c0 c1 c2 c3 c4 w0 w1 w2 w3 w4 : Z) :=
  word_update (Z.lxor c4
    (word_update (Z.lxor c3
      (word_update (Z.lxor c2
        (word_update (Z.lxor c1 (word_update c0 w0)) w1)) w2)) w3)) w4.
Lemma braid_finish_value : forall c0 c1 c2 c3 c4 w0 w1 w2 w3 w4,
  braid_finish c0 c1 c2 c3 c4 w0 w1 w2 w3 w4 =
  Z.lxor (csteps 32 (merge5 c0 c1 c2 c3 c4))
    (csteps 32 (merge5 w0 w1 w2 w3 w4)).
Proof.
  intros. unfold braid_finish,word_update,merge5. rewrite !csteps_xor.
  repeat rewrite <-csteps_add. cbn [Nat.add].
  apply Z.bits_inj'. intros k Hk. rewrite !Z.lxor_spec. btauto.
Qed.
Theorem braid_finish_serial : forall q c0 c1 c2 c3 c4 w0 w1 w2 w3 w4,
  merge5 c0 c1 c2 c3 c4 = csteps 128 q ->
  braid_finish c0 c1 c2 c3 c4 w0 w1 w2 w3 w4 = block5 q w0 w1 w2 w3 w4.
Proof.
  intros q c0 c1 c2 c3 c4 w0 w1 w2 w3 w4 H.
  rewrite braid_finish_value,H,block5_value,<-csteps_add. reflexivity.
Qed.
Theorem block5_bytes : forall (bs0 bs1 bs2 bs3 bs4 : list byte) q,
  length bs0 = 4%nat -> length bs1 = 4%nat -> length bs2 = 4%nat ->
  length bs3 = 4%nat -> length bs4 = 4%nat ->
  raw_crc (bs0++bs1++bs2++bs3++bs4) q =
  block5 q (bytes_le_to_Z bs0) (bytes_le_to_Z bs1) (bytes_le_to_Z bs2)
    (bytes_le_to_Z bs3) (bytes_le_to_Z bs4).
Proof.
  intros bs0 bs1 bs2 bs3 bs4 q H0 H1 H2 H3 H4.
  rewrite !raw_crc_append,!raw_four_bytes_value by assumption. reflexivity.
Qed.

Definition braid_word (w : Z) :=
  Z.lxor (csteps 160 (w mod 256))
    (Z.lxor (csteps 152 ((Z.shiftr w 8) mod 256))
      (Z.lxor (csteps 144 ((Z.shiftr w 16) mod 256))
        (csteps 136 ((Z.shiftr w 24) mod 256)))).
Lemma braid_word_zero : braid_word 0 = 0.
Proof. unfold braid_word. rewrite !csteps_zero. reflexivity. Qed.
Lemma braid_word_linear : forall a b, braid_word (Z.lxor a b) = Z.lxor (braid_word a) (braid_word b).
Proof.
  intros a b. unfold braid_word. rewrite !Z.shiftr_lxor,!low8_xor,!csteps_xor.
  apply Z.bits_inj'. intros k Hk. rewrite !Z.lxor_spec. btauto.
Qed.
Definition braid_word_check := forallb (fun i =>
  braid_word (2^Z.of_nat i) =? csteps 160 (2^Z.of_nat i)) (seq 0 32).
Lemma braid_word_checked : braid_word_check = true.
Proof. vm_compute. reflexivity. Qed.
Theorem braid_word_value : forall w, 0 <= w < 2^32 -> braid_word w = csteps 160 w.
Proof.
  intros w Hw. eapply linear32_equal with (f:=braid_word) (g:=csteps 160);
    [apply braid_word_zero|apply csteps_zero|apply braid_word_linear|apply csteps_xor| |exact Hw].
  intros i Hi. apply Z.eqb_eq.
  exact (forallb_seq _ 0 32 i braid_word_checked ltac:(lia)).
Qed.
