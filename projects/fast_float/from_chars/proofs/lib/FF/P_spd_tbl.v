(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Fixpoint image_u64s (A : Z) (n : nat) : list Z :=
  match n with O => [] | S n' =>
    match image_bytes PSEGS A 8 with Some xs => bv_unsigned (le_bytes_to_word xs) | None => 0%Z end
    :: image_u64s (A + 8) n' end.

(* [comment removed for export] *)
Definition TBLD : list Z := Eval vm_compute in (image_u64s 0x15ba8 23).
Lemma TBLD_ok : table_b PSEGS 0x15ba8 8 (fun v => le8 (Z_to_bv 64 v)) TBLD = true.
Proof. vm_compute. reflexivity. Qed.
Lemma TBLD_length : length TBLD = 23%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition TBL5 : list Z := Eval vm_compute in (image_u64s 0x13150 1302).
Lemma TBL5_ok : table_b PSEGS 0x13150 8 (fun v => le8 (Z_to_bv 64 v)) TBL5 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma TBL5_length : length TBL5 = 1302%nat. Proof. reflexivity. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma idx16_cf : forall q : word, (-342 <= bv_signed q <= 308)%Z ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned q) 1)))) 3 + 82256)
  = Z_to_bv 64 (76784 + 8 * (2 * (bv_signed q + 342)))%Z.
Proof.
  intros q Hq. pose proof (zb_signed q) as SQ.
  pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  rewrite !Z.shiftl_mul_pow2 by lia. unfold bv_swrap, bv_wrap. rewrite unsigned_lit_wrap.
  apply Z_to_bv_eqm.
  replace (bv_half_modulus 32) with (2^31)%Z by reflexivity.
  replace (bv_modulus 32) with (2^32)%Z by reflexivity.
  destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.

Ltac swrap_unfold :=
  unfold bv_swrap, bv_wrap in *;
  replace (bv_half_modulus 32) with (2^31)%Z in * by reflexivity;
  replace (bv_modulus 32) with (2^32)%Z in * by reflexivity.

(* [comment removed for export] *)
Lemma idx16_ce : forall (q A1 : word), A1 = Z_to_bv 64 (Z.shiftl (bv_unsigned q) 1) -> (-342 <= bv_signed q <= 308)%Z ->
  Z_to_bv 64 (78160 + Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned A1 + 684)))) 3)
  = Z_to_bv 64 (78160 + 8 * (2 * (bv_signed q + 342)))%Z.
Proof.
  intros q A1 -> Hq. pose proof (zb_signed q) as SQ.
  pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite !unsigned_lit_wrap. swrap_unfold.
  apply Z_to_bv_eqm.
  destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.
Lemma idx16_ce' : forall (q A1 : word), A1 = Z_to_bv 64 (Z.shiftl (bv_unsigned q) 1) -> (-342 <= bv_signed q <= 308)%Z ->
  Z_to_bv 64 (78160 + Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned A1 + 685)))) 3)
  = Z_to_bv 64 (78160 + 8 * (2 * (bv_signed q + 342) + 1))%Z.
Proof.
  intros q A1 -> Hq. pose proof (zb_signed q) as SQ.
  pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite !unsigned_lit_wrap. swrap_unfold.
  apply Z_to_bv_eqm.
  destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma ce_A_range : forall q : word, (-342 <= bv_signed q <= 308)%Z ->
  (-1137 <= bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned q * 217706)))) 16) <= 1023)%Z.
Proof.
  intros q Hq. pose proof (zb_signed q) as SQ.
  pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  rewrite Z.shiftr_div_pow2 by lia. rewrite !unsigned_lit_wrap. swrap_unfold.
  destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma ce_X_eq : forall (A lz ub : Z), (-1137 <= A <= 1023)%Z -> (0 <= lz < 256)%Z -> (0 <= ub <= 1)%Z ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 A) - lz) + -31693)) + ub)
  = (A - lz - 31693 + ub)%Z.
Proof.
  intros A lz ub HA Hlz Hub. rewrite !unsigned_lit_wrap. swrap_unfold.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma zx32_shifts : forall X : Z,
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 X)) 32))) 32)) = (X mod 2^32)%Z.
Proof.
  intros X. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite !unsigned_lit_wrap.
  Z.div_mod_to_equations. lia.
Qed.
