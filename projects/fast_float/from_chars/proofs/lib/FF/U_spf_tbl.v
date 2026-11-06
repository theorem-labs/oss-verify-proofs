(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Fixpoint image_u64s (A : Z) (n : nat) : list Z :=
  match n with O => [] | S n' =>
    match image_bytes USEGS A 8 with Some xs => bv_unsigned (le_bytes_to_word xs) | None => 0%Z end
    :: image_u64s (A + 8) n' end.
Fixpoint image_u32s (A : Z) (n : nat) : list Z :=
  match n with O => [] | S n' =>
    match image_bytes USEGS A 4 with Some xs => bv_unsigned (le_bytes_to_word xs) | None => 0%Z end
    :: image_u32s (A + 4) n' end.

(* [comment removed for export] *)
Definition TBLF : list Z := Eval vm_compute in (image_u32s 0x15d28 11).
Lemma TBLF_ok : table_b USEGS 0x15d28 4 (fun v => le4 (Z_to_bv 64 v)) TBLF = true.
Proof. vm_compute. reflexivity. Qed.
Lemma TBLF_length : length TBLF = 11%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition TBL5 : list Z := Eval vm_compute in (image_u64s 0x13158 1302).
Lemma TBL5_ok : table_b USEGS 0x13158 8 (fun v => le8 (Z_to_bv 64 v)) TBL5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma TBL5_length : length TBL5 = 1302%nat. Proof. reflexivity. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma ucf_idx : forall q : word, (-342 <= bv_signed q <= 308)%Z ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned q) 1)) + 684) = (2 * bv_signed q + 684)%Z.
Proof.
  intros q Hq. pose proof (zb_signed q) as SQ.
  pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31)%Z by reflexivity.
  replace (bv_modulus 32) with (2^32)%Z by reflexivity.
  destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma lor_2k_1 : forall k, (0 <= k)%Z -> Z.lor (2 * k) 1 = (2 * k + 1)%Z.
Proof.
  intros k Hk.
  assert (D : Z.land (2 * k) 1 = 0%Z).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 0) as [->|].
    - replace (2 * k)%Z with (Z.shiftl k 1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite Z.shiftl_spec_low by lia. reflexivity.
    - replace (Z.testbit 1 i) with false; [apply andb_false_r|].
      symmetry. change 1%Z with (2^0)%Z. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity.
Qed.
Lemma lor_16k_8 : forall k, (0 <= k)%Z -> Z.lor (16 * k) 8 = (16 * k + 8)%Z.
Proof.
  intros k Hk.
  assert (D : Z.land (16 * k) 8 = 0%Z).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 3) as [->|].
    - replace (16 * k)%Z with (Z.shiftl k 4) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite Z.shiftl_spec_low by lia. reflexivity.
    - replace (Z.testbit 8 i) with false; [apply andb_false_r|].
      symmetry. change 8%Z with (2^3)%Z. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma swrap32_small : forall z, (- 2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31)%Z by reflexivity.
  replace (bv_modulus 32) with (2^32)%Z by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.
Lemma swrap32_unsigned : forall q : word, (- 2^31 <= bv_signed q < 2^31)%Z -> bv_swrap 32 (bv_unsigned q) = bv_signed q.
Proof.
  intros q Hq. pose proof (zb_signed q) as SQ.
  pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31)%Z by reflexivity.
  replace (bv_modulus 32) with (2^32)%Z by reflexivity.
  destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Lemma q342_word : forall q : word, Z_to_bv 64 (bv_unsigned q + 342) = Z_to_bv 64 (bv_signed q + 342).
Proof.
  intros q. pose proof (zb_signed q) as SQ. pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  apply Z_to_bv_eqm. destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma uce_A_range : forall q : word, (-342 <= bv_signed q <= 308)%Z ->
  (-1137 <= bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_signed q)) * 217706)))) 16) <= 1023)%Z.
Proof.
  intros q Hq. pose proof (zb_signed q) as SQ.
  pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  rewrite Z.shiftr_div_pow2 by lia. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31)%Z by reflexivity.
  replace (bv_modulus 32) with (2^32)%Z by reflexivity.
  destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.
Lemma uce_A_range' : forall q : word, (-342 <= bv_signed q <= 308)%Z ->
  (-1137 <= bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_signed q * 217706)))) 16) <= 1023)%Z.
Proof.
  intros q Hq. pose proof (zb_signed q) as SQ.
  pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  rewrite Z.shiftr_div_pow2 by lia. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31)%Z by reflexivity.
  replace (bv_modulus 32) with (2^32)%Z by reflexivity.
  destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.
