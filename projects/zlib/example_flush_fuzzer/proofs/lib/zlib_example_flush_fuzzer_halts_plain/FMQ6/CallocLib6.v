(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Frame Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import ZlibStmtBase ExSmallIface MallocDefs LibMaskBits.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel MemFill SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 Callee6 Memset6_run.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.


Lemma rdn_zero_pointwise : forall k m (a : word),
  bv_unsigned a + Z.of_nat k <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k -> m x <> None) ->
  rdn s6_segs m a k = Some (repeat (Z_to_bv 8 0) k) ->
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k -> m x = Some (Z_to_bv 8 0).
Proof.
  induction k as [|k IH]; intros m a Hnw Hmp Hr x Hx; [lia|].
  cbn [rdn repeat] in Hr. pose proof (u64_range a) as Ha.
  destruct (m a) as [b|] eqn:Hma; [|exfalso; exact (Hmp a ltac:(lia) Hma)].
  destruct (rdn s6_segs m (a + 1) k) as [rest|] eqn:Hrest; [|discriminate].
  injection Hr as Hb Hrest'.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [E|NE].
  - assert (x = a) by (apply bv_eq; exact E). subst x. rewrite Hma, Hb. reflexivity.
  - destruct k as [|k']; [cbn in Hx; lia|].
    assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
    apply (IH m (a + 1)%bv); [rewrite Hu1; lia | intros y Hy; apply Hmp; rewrite Hu1 in Hy; lia | rewrite <- Hrest'; exact Hrest | rewrite Hu1; lia].
Qed.

Lemma rdn_pointwise : forall segs mem n (a : word) bs,
  length bs = n ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> mem (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
  rdn segs mem a n = Some bs.
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
  - destruct bs; [reflexivity | cbn in Hlen; lia].
  - destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen.
    cbn [rdn].
    pose proof (Hpt 0%nat ltac:(lia)) as H0. cbn [nth Z.of_nat] in H0.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
    destruct n as [|n'].
    + destruct bs'; [reflexivity | cbn in Hlen; lia].
    + assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
      rewrite (IH (a + 1)%bv bs'); [reflexivity | lia | lia |].
      intros j Hj. rewrite Hu1.
      replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
      rewrite (Hpt (S j)) by lia. reflexivity.
Qed.


Lemma pointwise_of_zeros_at : forall m a k, 0 <= a -> 0 <= k -> a + k <= 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + k -> m x <> None) ->
  zeros_at s6_segs m a k -> forall x : word, a <= bv_unsigned x < a + k -> m x = Some (Z_to_bv 8 0).
Proof.
  intros m a k Ha Hk Hak Hmp Hz x Hx. unfold zeros_at in Hz.
  pose proof (Z2Nat.id k Hk). pose proof (u64_range x).
  apply (rdn_zero_pointwise (Z.to_nat k) m (zw a)); change (Z_to_bv 64 a) with (zw a) in Hz; rewrite ?u_zw_small by lia;
    [lia | intros y Hy; apply Hmp; lia | exact Hz | lia].
Qed.
End FXG.
