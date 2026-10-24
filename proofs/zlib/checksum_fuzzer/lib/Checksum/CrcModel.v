(** A byte-wise CRC-32 model and composition laws. Machine-code correctness
    must still be proved against this model before using it for the target. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcAlgebra CrcLinearBasis.
Import ListNotations.
Open Scope Z_scope.
Lemma csteps_n0 : forall q, csteps 0 q = q. Proof. idtac "MODEL csteps_n0". reflexivity. Qed.
Opaque csteps.
Definition CRC_MASK : Z := 2^32-1.
Definition raw_byte (q : Z) (b : byte) : Z := csteps 8 (Z.lxor q (bv_unsigned b)).
Fixpoint raw_crc (bs : list byte) (q : Z) : Z :=
  match bs with [] => q | b::rest => raw_crc rest (raw_byte q b) end.
Definition crc_model (q : Z) (bs : list byte) : Z :=
  Z.lxor (raw_crc bs (Z.lxor q CRC_MASK)) CRC_MASK.
Lemma byte_unsigned_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. idtac "MODEL byte_unsigned_range". intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.
Lemma raw_byte_range : forall q b, 0 <= q < 2^32 -> 0 <= raw_byte q b < 2^32.
Proof. idtac "MODEL raw_byte_range".
  intros q b Hq. apply csteps_range,lxor_bound;try lia.
  pose proof (byte_unsigned_range b). lia.
Qed.
Lemma raw_crc_range : forall bs q, 0 <= q < 2^32 -> 0 <= raw_crc bs q < 2^32.
Proof. idtac "MODEL raw_crc_range". induction bs;intros;cbn;[exact H|apply IHbs,raw_byte_range,H]. Qed.
Lemma crc_model_range : forall q bs, 0 <= q < 2^32 -> 0 <= crc_model q bs < 2^32.
Proof. idtac "MODEL crc_model_range".
  intros q bs Hq. unfold crc_model.
  assert (HM : 0 <= CRC_MASK < 2^32) by (unfold CRC_MASK;lia).
  apply lxor_bound;try lia. apply raw_crc_range,lxor_bound;lia.
Qed.
Lemma raw_crc_append : forall xs ys q,
  raw_crc (xs++ys) q = raw_crc ys (raw_crc xs q).
Proof. idtac "MODEL raw_crc_append". induction xs;intros;cbn;[reflexivity|apply IHxs]. Qed.
Lemma raw_byte_xor : forall q1 q2 b,
  raw_byte (Z.lxor q1 q2) b = Z.lxor (csteps 8 q1) (raw_byte q2 b).
Proof. idtac "MODEL raw_byte_xor". intros. unfold raw_byte. rewrite Z.lxor_assoc,csteps_xor. reflexivity. Qed.
Lemma raw_crc_xor : forall bs q1 q2,
  raw_crc bs (Z.lxor q1 q2) = Z.lxor (csteps (8*length bs) q1) (raw_crc bs q2).
Proof. idtac "MODEL raw_crc_xor".
  induction bs as [|b bs IH];intros q1 q2;cbn [raw_crc length].
  - rewrite csteps_n0. reflexivity.
  - rewrite raw_byte_xor.
    rewrite (IH (csteps 8 q1) (raw_byte q2 b)).
    rewrite <- (csteps_add (8*length bs)%nat 8%nat q1).
    replace (8*length bs+8)%nat with (8*S(length bs))%nat by lia. reflexivity.
Qed.
Theorem crc_model_affine : forall q bs,
  crc_model q bs = Z.lxor (csteps (8*length bs) q) (crc_model 0 bs).
Proof. idtac "MODEL crc_model_affine".
  intros q bs. unfold crc_model. rewrite Z.lxor_0_l,raw_crc_xor,Z.lxor_assoc. reflexivity.
Qed.
Theorem crc_model_append : forall xs ys q,
  crc_model q (xs++ys) = crc_model (crc_model q xs) ys.
Proof. idtac "MODEL crc_model_append".
  intros xs ys q. unfold crc_model. rewrite raw_crc_append.
  rewrite (Z.lxor_assoc (raw_crc xs (Z.lxor q CRC_MASK)) CRC_MASK CRC_MASK).
  rewrite Z.lxor_nilpotent,Z.lxor_0_r. reflexivity.
Qed.
Theorem crc_model_empty : forall q, crc_model q [] = q.
Proof. idtac "MODEL crc_model_empty".
  intros q. unfold crc_model. cbn [raw_crc].
  rewrite Z.lxor_assoc,Z.lxor_nilpotent,Z.lxor_0_r. reflexivity.
Qed.
