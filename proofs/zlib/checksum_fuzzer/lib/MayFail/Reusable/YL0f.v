(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0f.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Context {A B C : Type}.
Lemma tset_ext : forall (t : itree astate A) (k1 k2 : A -> itree astate B) (K : B -> TSet),
(forall r, k1 r = k2 r) -> t_eq (tset (ibind t k1) K) (tset (ibind t k2) K).
Proof. intros t k1 k2 K Hk. rewrite !tset_ibind. apply tset_congr. intros r. rewrite Hk. apply t_eq_refl. Qed.
Lemma jinv_ext : forall (K : B -> TSet) (t : itree astate A) (k1 k2 : A -> itree astate B),
(forall r, k1 r = k2 r) -> jinv K (ibind t k1) -> jinv K (ibind t k2).
Proof.
intros K t; induction t as [a | q s k IH | e]; intros k1 k2 Hk H; cbn in *.
- rewrite <- Hk. exact H.
- destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn in H |- *;
try (destruct H as [H0 H1]; split; [apply (IH _ k1 k2 Hk H0) | apply (IH _ k1 k2 Hk H1)]);
try (apply (IH _ k1 k2 Hk H)).
destruct H as [Heq Hj]. split.
+ intros z Hz. eapply t_eq_trans; [apply t_eq_sym; apply (tset_ext (k z) k1 k2 K Hk)|].
eapply t_eq_trans; [apply Heq; exact Hz|]. apply (tset_ext _ k1 k2 K Hk).
+ intros z Hz. apply (IH z k1 k2 Hk). apply Hj. exact Hz.
- exact I.
Qed.
Lemma gtree_ext : forall (G : astate -> kreq -> Prop) (t : itree astate A) (k1 k2 : A -> itree astate B),
(forall r, k1 r = k2 r) -> gtree G (ibind t k1) -> gtree G (ibind t k2).
Proof.
intros G t; induction t as [a | q s k IH | e]; intros k1 k2 Hk H; cbn in *.
- rewrite <- Hk. exact H.
- destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn in H |- *;
try (destruct H as (G0 & H0 & H1); split; [exact G0 | split; [apply (IH _ k1 k2 Hk H0) | apply (IH _ k1 k2 Hk H1)]]);
try (apply (IH _ k1 k2 Hk H)).
intros z Hz. apply (IH z k1 k2 Hk). apply H. exact Hz.
- exact I.
Qed.
Lemma tset_assoc : forall (t : itree astate A) (g : A -> itree astate B) (h : B -> itree astate C) (K : C -> TSet),
t_eq (tset (ibind (ibind t g) h) K) (tset (ibind t (fun r => ibind (g r) h)) K).
Proof. intros. rewrite !tset_ibind. apply tset_congr. intros r. rewrite tset_ibind. apply t_eq_refl. Qed.
Lemma jinv_assoc : forall (K : C -> TSet) (t : itree astate A) (g : A -> itree astate B) (h : B -> itree astate C),
jinv K (ibind (ibind t g) h) -> jinv K (ibind t (fun r => ibind (g r) h)).
Proof.
intros K t; induction t as [a | q s k IH | e]; intros g h H; cbn in *.
- exact H.
- destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn in H |- *;
try (destruct H as [H0 H1]; split; [apply IH; exact H0 | apply IH; exact H1]);
try (apply IH; exact H).
destruct H as [Heq Hj]. split.
+ intros z Hz. eapply t_eq_trans; [apply t_eq_sym; apply tset_assoc|].
eapply t_eq_trans; [apply Heq; exact Hz|]. apply tset_assoc.
+ intros z Hz. apply IH. apply Hj. exact Hz.
- exact I.
Qed.
Lemma gtree_assoc : forall (G : astate -> kreq -> Prop) (t : itree astate A) (g : A -> itree astate B) (h : B -> itree astate C),
gtree G (ibind (ibind t g) h) -> gtree G (ibind t (fun r => ibind (g r) h)).
Proof.
intros G t; induction t as [a | q s k IH | e]; intros g h H; cbn in *.
- exact H.
- destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn in H |- *;
try (destruct H as (G0 & H0 & H1); split; [exact G0 | split; [apply IH; exact H0 | apply IH; exact H1]]);
try (apply IH; exact H).
intros z Hz. apply IH. apply H. exact Hz.
- exact I.
Qed.
End c.
Section d.
Context {A B C : Type}.
Variables (m : M A) (g : A -> M B) (h : B -> M C) (s : astate).
Lemma tset_bind_assoc : forall K,
t_eq (tset (bind (bind m g) h s) K) (tset (bind m (fun a => bind (g a) h) s) K).
Proof.
intros K. unfold bind. eapply t_eq_trans; [apply tset_assoc|].
apply tset_ext. intros [a s']. reflexivity.
Qed.
Lemma jinv_bind_assoc : forall K,
jinv K (bind (bind m g) h s) -> jinv K (bind m (fun a => bind (g a) h) s).
Proof.
intros K H. unfold bind in *. apply jinv_assoc in H.
eapply jinv_ext; [| exact H]. intros [a s']. reflexivity.
Qed.
Lemma gtree_bind_assoc : forall G,
gtree G (bind (bind m g) h s) -> gtree G (bind m (fun a => bind (g a) h) s).
Proof.
intros G H. unfold bind in *. apply gtree_assoc in H.
eapply gtree_ext; [| exact H]. intros [a s']. reflexivity.
Qed.
End d.
End b.
