(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR.
Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Definition one_d : word := fcvt_d_w RNE (Z_to_bv 64 1).

Definition scalbn_chk (n : Z) : bool := Z.eqb (bv_unsigned (m_scalbn one_d n)) ((1023 + n) * 2^52).
Lemma scalbn_chk_all : forallb scalbn_chk (map Z.of_nat (seq 1 225)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma word_eq_unsigned : forall (a : word) z, bv_unsigned a = z -> a = Z_to_bv 64 z.
Proof. intros a z <-. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma scalbn_one_pow2 : forall n, 1 <= n <= 225 ->
m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) n = Z_to_bv 64 (Z.shiftl (1023 + n) 52).
Proof.
intros n Hn.
assert (In n (map Z.of_nat (seq 1 225))).
{ apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia. }
pose proof (proj1 (forallb_forall _ _) scalbn_chk_all n H) as C. unfold scalbn_chk in C. apply Z.eqb_eq in C.
fold one_d. rewrite Z.shiftl_mul_pow2 by lia. apply word_eq_unsigned. exact C.
Qed.

Lemma fmul_sign_comm : forall sign (C : word), (sign = 1 \/ sign = -1) ->
(C = D_025 \/ C = D_05 \/ C = D_075) ->
fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 sign)) C = fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign)).
Proof.
intros sign C [-> | ->] [-> | [-> | ->]]; vm_compute; reflexivity.
Qed.

