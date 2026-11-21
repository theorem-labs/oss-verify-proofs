(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZChecksum ZChkArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma u8_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intro b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Import ListNotations.
Local Open Scope Z_scope.


Definition b0 : byte := Z_to_bv 8 0.
Definition bZ (d : list byte) : list Z := map bv_unsigned d.
Definition bnth (d : list byte) (k : nat) : Z := bv_unsigned (nth k d b0).






Definition A1 (d : list byte) (s1 s2 : Z) (k : nat) : Z :=
  fst (adl_raw (firstn k (bZ d)) s1 s2).
Definition A2 (d : list byte) (s1 s2 : Z) (k : nat) : Z :=
  snd (adl_raw (firstn k (bZ d)) s1 s2).













Definition IS1 (init : Z) : Z := Z.land init 65535.
Definition IS2 (init : Z) : Z := Z.land (Z.shiftr init 16) 65535.





Lemma lor_lxor_disj : forall a b, Z.land a b = 0 -> Z.lor a b = Z.lxor a b.
Proof.
  intros a b H. apply Z.bits_inj'. intros n Hn.
  assert (Hb : andb (Z.testbit a n) (Z.testbit b n) = false)
    by (rewrite <- Z.land_spec, H, Z.bits_0; reflexivity).
  rewrite Z.lor_spec, Z.lxor_spec.
  destruct (Z.testbit a n), (Z.testbit b n); cbn in Hb |- *; congruence.
Qed.

Lemma combine_lor : forall a s, 0 <= a < 65536 -> 0 <= s ->
  Z.lor (Z.shiftl s 16) a = Z.lxor (Z.shiftl s 16) a.
Proof.
  intros a s Ha Hs. apply lor_lxor_disj. rewrite Z.land_comm.
  apply (land_shiftl_disj a s 16); [change (2 ^ 16) with 65536; lia|lia|lia].
Qed.

Lemma condsub : forall x, 0 <= x < 2 * ABASE ->
  (if Z.leb x 65520 then x else x - ABASE) = x mod ABASE.
Proof.
  intros x Hx. unfold ABASE in *.
  destruct (Z.leb_spec x 65520) as [H|H].
  - symmetry. apply Z.mod_small. lia.
  - rewrite <- (Z.mod_add x (-1) 65521) by lia.
    symmetry. apply Z.mod_small. lia.
Qed.







