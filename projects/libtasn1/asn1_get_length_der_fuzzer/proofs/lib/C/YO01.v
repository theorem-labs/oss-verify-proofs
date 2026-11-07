(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK0w.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YQ0b.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP0g YP0c.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP09 YP0a YP0b.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma nth_error_Z_to_le_bytes : forall n z k, (k < n)%nat ->
nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma le_byte_bv : forall v w k, (k < w)%nat ->
Z_to_bv 8 (le_byte v w k) = Z_to_bv 8 (Z.shiftr (v mod 2 ^ (8 * Z.of_nat w)) (8 * Z.of_nat k)).
Proof.
intros v w k Hk. unfold le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma bytes_rdn : forall segs mem a (w : nat) v,
0 <= a -> a + Z.of_nat w <= 2^64 ->
(forall k, (k < w)%nat -> mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v w k))) ->
rdn segs mem (Z_to_bv 64 a) w = Some (Z_to_le_bytes w (v mod 2 ^ (8 * Z.of_nat w))).
Proof.
intros segs mem a w v Ha Hw Hb. apply rdn_mbytes. split; [apply length_Z_to_le_bytes|].
intros i Hi. rewrite (Hb i Hi), nth_error_Z_to_le_bytes by lia. f_equal. apply le_byte_bv. exact Hi.
Qed.
Lemma word_mem_rdn : forall segs mem a v,
word_mem segs mem a v -> 0 <= a -> a + 8 <= 2^64 ->
rdn segs mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
Proof.
intros segs mem a v Hw Ha H8. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 v) with (v mod 2 ^ (8 * Z.of_nat 8)).
apply bytes_rdn; [lia|lia|]. exact Hw.
Qed.
Lemma word_mem_ld : forall segs mem a v,
word_mem segs mem a v -> 0 <= a -> a + 8 <= 2^64 ->
exists bs, rdn segs mem (Z_to_bv 64 a) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 v).
Proof.
intros segs mem a v Hw Ha H8. eexists. split; [apply (word_mem_rdn segs mem a v Hw Ha H8)|]. apply bytes_le_to_Z_8.
Qed.








End c.
