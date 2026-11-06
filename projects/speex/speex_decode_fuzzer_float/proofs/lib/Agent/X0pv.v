(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1br.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Definition f10 : bv 5 := Z_to_bv 5 10.

Lemma tset_tset_same : forall {A} (p : positive) (x y : A) (t : tree A),
tset p x (tset p y t) = tset p x t.
Proof.
intros A p. induction p as [p IH|p IH|]; intros x y [|l v r]; cbn; try rewrite IH; reflexivity.
Qed.

Lemma bvmap_set_set_same : forall {n A} (k : bv n) (x y : A) (m : bvmap n A),
bvmap_set k x (bvmap_set k y m) = bvmap_set k x m.
Proof. intros. unfold bvmap_set. apply tset_tset_same. Qed.

Definition Fok10 (F Ft : bvmap 5 word) : Prop :=
Ft = F \/ exists v : word, Ft = bvmap_set f10 v F.

Lemma Fok10_refl : forall F, Fok10 F F.
Proof. intros F. left. reflexivity. Qed.

Lemma Fok10_set : forall F v, Fok10 F (bvmap_set f10 v F).
Proof. intros F v. right. exists v. reflexivity. Qed.

Lemma Fok10_trans : forall F F1 F2, Fok10 F F1 -> Fok10 F1 F2 -> Fok10 F F2.
Proof.
intros F F1 F2 [->|[v ->]] [->|[w ->]].
- left; reflexivity.
- right; exists w; reflexivity.
- right; exists v; reflexivity.
- right; exists w. apply bvmap_set_set_same.
Qed.

Lemma Fok10_agree : forall F Ft, Fok10 F Ft ->
forall k : bv 5, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k.
Proof.
intros F Ft [->|[v ->]] k Hk; [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other; [reflexivity|].
intros E. apply Hk. rewrite <- E. reflexivity.
Qed.

Definition is_mkF (F : bvmap 5 word) : Prop :=
exists f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 fa0 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31,
F = mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 fa0 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31.

Lemma Fok10_mkF : forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 fa0 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 Ft,
Fok10 (mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 fa0 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31) Ft ->
exists v, Ft = mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 v f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31.
Proof.
intros until Ft. intros [->|[v ->]]; [exists fa0; reflexivity| exists v; reflexivity].
Qed.

Lemma is_mkF_mkF : forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 fa0 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31,
is_mkF (mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 fa0 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31).
Proof. intros. unfold is_mkF. sf_eexists 32%nat. reflexivity. Qed.

Lemma is_mkF_mkF0 : is_mkF mkF0.
Proof. apply is_mkF_mkF. Qed.

Lemma Fok10_is_mkF : forall F Ft, is_mkF F -> Fok10 F Ft -> is_mkF Ft.
Proof.
intros F Ft HM HF.
first [ sf_destruct 33%nat HM as f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 fa0 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 -> | sf_fb; destruct HM as (f0 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & f9 & fa0 & f11 & f12 & f13 & f14 & f15 & f16 & f17 & f18 & f19 & f20 & f21 & f22 & f23 & f24 & f25 & f26 & f27 & f28 & f29 & f30 & f31 & ->) ].
destruct (Fok10_mkF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as [v ->]. apply is_mkF_mkF.
Qed.
