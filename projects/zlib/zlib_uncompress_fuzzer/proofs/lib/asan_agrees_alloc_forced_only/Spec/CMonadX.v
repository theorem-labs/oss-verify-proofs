(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Exec ITree Nodes CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Monad CMonad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section ImplCX.
Variable segs : list Segment.
Local Notation implC := (implC segs (at_node segs)).

Lemma implC_from_evt : forall {R} (c : ctree node R) Q ms, evt segs (fun ms' => implC c Q ms') ms -> implC c Q ms.
Proof. intros R c Q ms H. eapply implC_evt; [exact H|]. intros ms' H'. exact H'. Qed.

Lemma implC_bind_cong : forall {A B} (c : ctree node A) (k1 k2 : A -> ctree node B) (Q : B -> machine_state -> Prop) ms,
  (forall r ms', implC (k1 r) Q ms' -> implC (k2 r) Q ms') ->
  implC (cbind c k1) Q ms -> implC (cbind c k2) Q ms.
Proof.
  intros A B c. induction c as [r|n k IH|a IHa b IHb]; intros k1 k2 Q ms HK H; cbn [cbind] in *.
  - apply HK. exact H.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; [exact HK| apply Hk].
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hl|Hr]; [left; eapply IHa; eauto| right; eapply IHb; eauto].
Qed.

Lemma implC_bind_assoc : forall {A B C} (c : ctree node A) (g : A -> ctree node B) (f : B -> ctree node C) Q ms,
  implC (cbind c (fun x => cbind (g x) f)) Q ms -> implC (cbind (cbind c g) f) Q ms.
Proof.
  intros A B C c. induction c as [r|n k IH|a IHa b IHb]; intros g f Q ms H; cbn [cbind] in *.
  - exact H.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hl|Hr]; [left; apply IHa; exact Hl| right; apply IHb; exact Hr].
Qed.

Lemma cinj_bind : forall {A B} (t : itree node A) (k : A -> itree node B),
  cinj (ITree.bind node t k) = cbind (cinj t) (fun r => cinj (k r)).
Proof.
  intros A B t k. induction t as [r|n k0 IH]; cbn; [reflexivity|].
  f_equal. apply functional_extensionality. intros rsp. apply IH.
Qed.
End ImplCX.

Section ImplMCX.
Context {St : Type}.
Variable segs : list Segment.

Lemma implMC_from_evt : forall {A} (c : MC St A) s Q ms,
  evt segs (fun ms' => implMC segs c s Q ms') ms -> implMC segs c s Q ms.
Proof. intros A c s Q ms H. eapply implMC_evt; [exact H|]. intros ms' H'. exact H'. Qed.

Lemma implMC_lift_bind : forall {A B} (m : M St A) (f : A -> MC St B) s Q1 Q ms,
  implM segs m s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implMC segs (f a) s' Q ms') ->
  implMC segs (cmbind (clift m) f) s Q ms.
Proof. intros A B m f s Q1 Q ms Hm Hf. eapply implMC_bind; [apply implMC_lift; exact Hm| exact Hf]. Qed.

Lemma implMC_retb : forall {A B} (a : A) (f : A -> MC St B) (s : St) Q ms,
  implMC segs (f a) s Q ms -> implMC segs (cmbind (cmret a) f) s Q ms.
Proof. intros A B a f s Q ms H. exact H. Qed.

Lemma implMC_bind_assoc : forall {A B C} (m : MC St A) (g : A -> MC St B) (f : B -> MC St C) s Q ms,
  implMC segs (cmbind m (fun a => cmbind (g a) f)) s Q ms ->
  implMC segs (cmbind (cmbind m g) f) s Q ms.
Proof.
  intros A B C m g f s Q ms H. unfold implMC, cmbind, cebind in *.
  apply implC_bind_assoc. eapply implC_bind_cong; [| exact H].
  intros [|[a s']] ms'; cbn [cbind fst snd]; intros H'; exact H'.
Qed.

Lemma implMC_unr : forall {A} s (Q : A -> St -> machine_state -> Prop) ms, implMC segs (clift munr) s Q ms.
Proof. intros A s Q ms. apply implMC_lift. apply implM_unr. Qed.

Lemma clift_mbind : forall {A B} (m : M St A) (f : A -> M St B),
  clift (mbind m f) = cmbind (clift m) (fun a => clift (f a)).
Proof.
  intros A B m f. apply functional_extensionality. intros s. unfold clift, mbind, cmbind, cebind, ebind.
  rewrite cinj_bind. f_equal. apply functional_extensionality. intros [|[a s']]; reflexivity.
Qed.

Lemma clift_mret : forall {A} (a : A), clift (mret a) = cmret (St := St) a.
Proof. intros A a. reflexivity. Qed.

Lemma clift_fold_bind : forall {A B} (m : M St A) (f : A -> M St B) (g : A -> MC St B),
  (forall a, g a = clift (f a)) -> cmbind (clift m) g = clift (mbind m f).
Proof.
  intros A B m f g H. rewrite clift_mbind. f_equal. apply functional_extensionality. exact H.
Qed.

Lemma implMC_of_implM : forall {A} (c : MC St A) (m : M St A) s Q ms,
  c = clift m -> implM segs m s Q ms -> implMC segs c s Q ms.
Proof. intros A c m s Q ms -> H. apply implMC_lift. exact H. Qed.

Lemma implMC_liftretb : forall {A B} (a : A) (f : A -> MC St B) (s : St) Q ms,
  implMC segs (f a) s Q ms -> implMC segs (cmbind (clift (mret a)) f) s Q ms.
Proof. intros A B a f s Q ms H. exact H. Qed.

Lemma implMC_lift_bind_assoc : forall {A B C} (m : M St A) (g : A -> M St B) (f : B -> MC St C) s Q ms,
  implMC segs (cmbind (clift m) (fun a => cmbind (clift (g a)) f)) s Q ms ->
  implMC segs (cmbind (clift (mbind m g)) f) s Q ms.
Proof. intros A B C m g f s Q ms H. rewrite clift_mbind. apply implMC_bind_assoc. exact H. Qed.

Lemma clift_if : forall {A} (b : bool) (m1 m2 : M St A), (if b then clift m1 else clift m2) = clift (if b then m1 else m2).
Proof. intros A [|] m1 m2; reflexivity. Qed.

End ImplMCX.

Ltac clift_eq := repeat first [ reflexivity | apply clift_fold_bind; intros ? ].
