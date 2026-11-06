(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad HarnessM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section ImplX2.
  Variable segs : list Segment.
  Lemma impl_bind_assoc' : forall {A B C} (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) Q ms,
    impl segs (at_node segs) (ITree.bind node (ITree.bind node t g) f) Q ms -> impl segs (at_node segs) (ITree.bind node t (fun x => ITree.bind node (g x) f)) Q ms.
  Proof.
    intros A B C t. induction t as [r|n k IH]; intros g f Q ms H; cbn [ITree.bind] in *.
    - exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. apply IH. apply Hk.
  Qed.
  Context {St : Type}.
  Lemma implM_bind_assoc' : forall {A B C} (m : @M St A) (g : A -> @M St B) (f : B -> @M St C) s Q ms,
    implM segs (Monad.mbind (Monad.mbind m g) f) s Q ms ->
    implM segs (Monad.mbind m (fun a => Monad.mbind (g a) f)) s Q ms.
  Proof.
    intros A B C m g f s Q ms H. unfold implM, Monad.mbind, ebind in *.
    apply impl_bind_assoc' in H. eapply impl_bind_cong; [| exact H].
    intros [|[a s']] ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.
  Lemma implM_bind_cong : forall {A B} (m : @M St A) (k1 k2 : A -> @M St B) s Q ms,
    (forall a s' ms', implM segs (k1 a) s' Q ms' -> implM segs (k2 a) s' Q ms') ->
    implM segs (Monad.mbind m k1) s Q ms -> implM segs (Monad.mbind m k2) s Q ms.
  Proof.
    intros A B m k1 k2 s Q ms HK H. unfold implM, Monad.mbind, ebind in *.
    eapply impl_bind_cong; [| exact H]. intros [|[a s']] ms'; cbn [ITree.bind fst snd]; intros H'; [exact H'|].
    apply HK. exact H'.
  Qed.
End ImplX2.

Section Lam.
  Context {St ptr : Type}.
  Variable raw_malloc : Z -> M St (option ptr).
  Variable raw_free : ptr -> M St unit.
  Variable new_handler : M St Empty_set.
  Notation opnew := (HarnessM.opnew raw_malloc new_handler).
  Notation opdelete := (HarnessM.opdelete raw_free).
  Notation odelete := (HarnessM.odelete raw_free).

  (* [comment removed for export] *)
  Definition vctor_model (n : Z) : M St (option ptr) :=
    if n =? 0 then mret None else p <- opnew n ;; mret (Some p).
  (* [comment removed for export] *)
  Definition assign_model (n : Z) (b : option ptr) : M St (option ptr) :=
    if ERRMSG_LEN <=? n then mret b else odelete b ;;; p' <- opnew ERRMSG_LEN ;; mret (Some p').
  (* [comment removed for export] *)
  Definition lam_model (data : list Z) : M St (option ptr) :=
    let n := Z.of_nat (length data) in
    b <- vctor_model n ;;
    if unclosed data then
      t <- opnew ERRSTR_BYTES ;;
      b' <- assign_model n b ;;
      opdelete t ;;;
      mret b'
    else mret b.

  Variable segs : list Segment.
  (* [comment removed for export] *)
  Lemma minify_call_of_lam : forall data s Q ms,
    implM segs (b' <- lam_model data ;; odelete b') s Q ms ->
    implM segs (HarnessM.minify_call raw_malloc raw_free new_handler data) s Q ms.
  Proof.
    intros data s Q ms H. unfold HarnessM.minify_call. unfold lam_model, vctor_model, assign_model in H.
    apply implM_bind_assoc' in H. eapply implM_bind_cong; [| exact H]. clear H.
    intros b s' ms' H. cbv beta in H. destruct (unclosed data).
    - apply implM_bind_assoc' in H. eapply implM_bind_cong; [| exact H]. clear H. intros t s2 ms2 H. cbv beta in H.
      apply implM_bind_assoc' in H. eapply implM_bind_cong; [| exact H]. clear H. intros b' s3 ms3 H. cbv beta in H.
      apply implM_bind_assoc' in H. eapply implM_bind_cong; [| exact H]. clear H. intros u s4 ms4 H. cbv beta in H.
      exact H.
    - exact H.
  Qed.
End Lam.
