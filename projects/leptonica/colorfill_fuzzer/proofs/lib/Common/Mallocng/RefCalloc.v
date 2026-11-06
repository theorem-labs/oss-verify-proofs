(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare StoreOk MmapSim AllocSim ShapeAlg PureModel VmLedger AllocIface AsanCeil MemSplit ZStores.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import WalksLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps MallocShape.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout}.

Lemma tsafe_stbytes_inv {A} : forall (a : word) bs (k : unit -> M A) s P,
  tsafe ((x <- m_stbytes a bs ;; k x) s) P ->
  acc_ok s a (Z.of_nat (length bs)) = true /\ store_ok ml_segs (ms_mem s) a (length bs) = true /\
  (x <- m_stbytes a bs ;; k x) s = k tt (upd s (wbytes (ms_mem s) a bs) (ms_vm s)).
Proof.
  intros a bs k s P H. unfold m_stbytes, mbind in *.
  destruct (acc_ok s a (Z.of_nat (length bs))) eqn:Hok; [|cbn in H; contradiction].
  destruct (st_zone a (Z.of_nat (length bs))) eqn:Hz; [|cbn in H; contradiction].
  destruct (store_ok ml_segs (ms_mem s) a (length bs)) eqn:Hso; [|cbn in H; contradiction].
  cbn. split; [reflexivity | split; reflexivity].
Qed.

Lemma length_zero_bytes : forall n : word, length (zero_bytes n) = Z.to_nat (bv_unsigned n).
Proof. intros n. unfold zero_bytes. apply repeat_length. Qed.

(* [comment removed for export] *)
Lemma zf_zero_bytes : forall (M : word -> option byte) (d n : word),
  bv_unsigned d + bv_unsigned n <= 2^64 ->
  zf M (bv_unsigned d) [(0, bv_unsigned n)] = wbytes M d (zero_bytes n).
Proof.
  intros M d n Hdn. pose proof (u64_range d) as Hd. pose proof (u64_range n) as Hn.
  unfold zero_bytes. change (repeat (Z_to_bv 8 0) (Z.to_nat (bv_unsigned n))) with (zeros (Z.to_nat (bv_unsigned n))).
  rewrite <- (zf_nil M (bv_unsigned d)) at 2.
  replace d with (Z_to_bv 64 (bv_unsigned d + 0)) at 3 by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
  rewrite wbytes_zf by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma is0_true_u : forall v : word, is0 v = true -> bv_unsigned v = 0.
Proof.
  intros v H. unfold is0, c_eq, w0 in H. apply bv_eqb_eq in H. rewrite H. reflexivity.
Qed.
Lemma is0_false_u : forall v : word, is0 v = false -> bv_unsigned v <> 0.
Proof.
  intros v H E. unfold is0, c_eq, w0 in H.
  assert (v = Z_to_bv 64 0) by (apply bv_eq; rewrite E; reflexivity). subst v.
  rewrite bv_eqb_refl in H. discriminate.
Qed.

End WithLayout.
