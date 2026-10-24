(** Algebra for the byte-at-a-time CRC lookup, covering arbitrary32-bit state. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcAlgebra CrcLinearBasis CrcLib.
Open Scope Z_scope.
Lemma low8_xor : forall a b, Z.lxor a b mod 256 = Z.lxor (a mod 256) (b mod 256).
Proof.
  intros a b. change 256 with (2^8). apply Z.bits_inj'. intros k Hk.
  rewrite Z.lxor_spec. destruct (Z_lt_ge_dec k 8).
  - rewrite !Z.mod_pow2_bits_low by lia. apply Z.lxor_spec.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Definition byte_split_rhs (x : Z) := Z.lxor (csteps 8 (x mod 256)) (Z.shiftr x 8).
Lemma byte_split_zero : byte_split_rhs 0 = 0.
Proof. unfold byte_split_rhs. rewrite csteps_zero. reflexivity. Qed.
Lemma byte_split_linear : forall a b,
  byte_split_rhs (Z.lxor a b) = Z.lxor (byte_split_rhs a) (byte_split_rhs b).
Proof.
  intros a b. unfold byte_split_rhs. rewrite low8_xor,Z.shiftr_lxor,csteps_xor. apply lxor4.
Qed.
Definition byte_split_check : bool := List.forallb (fun i =>
  csteps 8 (2^Z.of_nat i) =? byte_split_rhs (2^Z.of_nat i)) (List.seq 0 32).
Lemma byte_split_checked : byte_split_check = true.
Proof. vm_compute. reflexivity. Qed.
Theorem byte_split_value : forall x, 0 <= x < 2^32 -> csteps 8 x = byte_split_rhs x.
Proof.
  intros x Hx. eapply linear32_equal with (f:=csteps 8) (g:=byte_split_rhs);
    [apply csteps_zero|apply byte_split_zero|apply csteps_xor|apply byte_split_linear| |exact Hx].
  intros i Hi. apply Z.eqb_eq. exact (forallb_seq _ 0 32 i byte_split_checked ltac:(lia)).
Qed.
Theorem byte_table_step : forall q b, 0 <= q < 2^32 -> 0 <= b < 256 ->
  csteps 8 (Z.lxor q b) =
  Z.lxor (csteps 8 (Z.land (Z.lxor q b) 255)) (Z.shiftr q 8).
Proof.
  intros q b Hq Hb. rewrite byte_split_value by (apply lxor_bound;lia).
  unfold byte_split_rhs. rewrite land255_mod,Z.shiftr_lxor.
  assert (E : Z.shiftr b 8 = 0).
  { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. exact Hb. }
  rewrite E,Z.lxor_0_r. reflexivity.
Qed.
