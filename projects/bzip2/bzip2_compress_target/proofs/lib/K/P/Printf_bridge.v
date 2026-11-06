(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Monad PrintfModel Stdio.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import PrintfFormats.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Printf_lib Printf_mlib F_printf_iface Printf_stdio_iface Printf_pieces Printf_sn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section ITreeFacts.
  Variable segs : list Segment.
  Context {node : Type}.
  Variable atn : node -> machine_state -> Prop.
  Local Notation impl := (ITree.impl segs atn).
  Local Notation bind := (ITree.bind node).

  (* [comment removed for export] *)
  Fixpoint tforall {A} (P : A -> Prop) (t : itree node A) : Prop :=
    match t with
    | ITree.Ret r => P r
    | Vis n k => forall x, tforall P (k x)
    end.

  Lemma tforall_bind : forall {A B} (P : A -> Prop) (P' : B -> Prop) (t : itree node A) (f : A -> itree node B),
    tforall P t -> (forall a, P a -> tforall P' (f a)) -> tforall P' (bind t f).
  Proof.
    induction t as [r|n k IH]; intros f H Hf; cbn in *; [apply Hf; exact H|].
    intros x. apply IH; [apply H | exact Hf].
  Qed.

  (* [comment removed for export] *)
  Lemma impl_bind_ext2 : forall {A B C} (P : A -> Prop) (t : itree node A) (f : A -> itree node B) (g : A -> itree node C) Q1 Q2 ms,
    tforall P t ->
    (forall r ms', P r -> impl (f r) Q1 ms' -> impl (g r) Q2 ms') ->
    impl (bind t f) Q1 ms -> impl (bind t g) Q2 ms.
  Proof.
    induction t as [r|n k IH]; intros f g Q1 Q2 ms HP Hfg H; cbn [ITree.bind] in *.
    - apply Hfg; [exact HP | exact H].
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. eapply IH; [apply HP | exact Hfg | apply Hk].
  Qed.

  (* [comment removed for export] *)
  Lemma impl_bind_elim : forall {A B} (P : A -> Prop) (t : itree node A) (h : A -> itree node B) Q1 Q2 ms,
    tforall P t ->
    (forall r ms', P r -> impl (h r) Q1 ms' -> evt segs (Q2 r) ms') ->
    impl (bind t h) Q1 ms -> impl t Q2 ms.
  Proof.
    induction t as [r|n k IH]; intros h Q1 Q2 ms HP Hh H; cbn [ITree.bind] in *.
    - cbn. apply (Hh r); [exact HP | exact H].
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. eapply IH; [apply HP | exact Hh | apply Hk].
  Qed.

  (* [comment removed for export] *)
  Lemma impl_tforall : forall {A} (P : A -> Prop) (t : itree node A) Q ms,
    tforall P t -> impl t Q ms -> impl t (fun r ms' => Q r ms' /\ P r) ms.
  Proof.
    induction t as [r|n k IH]; intros Q ms HP H; cbn in *.
    - eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ | exact HP].
    - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply HP | apply Hk].
  Qed.
End ITreeFacts.

Section StderrBridge.
  Variable segs : list Segment.
  Context {St : Type}.
  Local Notation impl := (ITree.impl segs (at_node segs)).

  (* [comment removed for export] *)
  Definition FLUSH_stderr : M (list Z * St) unit :=
    fun bs => let '(buf, st) := bs in
      ebind (stdio_writev 2 buf [] st) (fun r => ITree.Ret (Ok (tt, (@nil Z, snd r)))).

  (* [comment removed for export] *)
  Lemma wv_loop_leaves : forall fuel fd iovs (st : St),
    tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (mloop fuel (wv_body fd) iovs st).
  Proof.
    induction fuel as [|fuel IH]; intros fd iovs st; cbn [mloop]; [exact I|].
    unfold mbind at 1. unfold wv_body, mbind, msys, enode, ebind. cbn [ITree.bind].
    intros x. destruct (dec_writev (iov_total iovs) x) as [k|]; cbn [ITree.bind fst snd]; [|exact I].
    unfold mret. cbn [ITree.bind fst snd].
    destruct (k =? iov_total iovs); cbn [ITree.bind fst snd]; [reflexivity | apply IH].
  Qed.
  Lemma stdio_writev_leaves : forall fd buf s (st : St),
    tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (stdio_writev fd buf s st).
  Proof. intros fd buf s st. unfold stdio_writev. apply wv_loop_leaves. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma stderr_bridge : forall ps buf (st : St) (Q : St -> machine_state -> Prop) ms,
    Forall (fun p => zlength p <= OUT_MAX) ps ->
    impl (outsk OUT_stderr ps FLUSH_stderr (buf, st)) (epost (fun p ms' => Q (snd (snd p)) ms')) ms ->
    impl (mbind (stderr_pieces buf ps) (fun b => stdio_writev 2 b []) st) (epost (fun p ms' => Q (snd p) ms')) ms.
  Proof.
    induction ps as [|p ps IH]; intros buf st Q ms SZ H; cbn [outsk stderr_pieces] in H |- *.
    - (* [comment removed for export] *)
      rewrite mbind_mret. unfold FLUSH_stderr, ebind in H.
      eapply (impl_bind_elim segs (at_node segs) _ _ _ _ _ _ (stdio_writev_leaves 2 buf [] st)); [|exact H].
      intros [|[[] st']] ms' Hr Hi; cbn in Hi |- *; [apply evt_done; exact I|].
      cbn in Hi. exact Hi.
    - apply Forall_cons_iff in SZ. destruct SZ as [SZp SZ].
      assert (G : (OUT_MAX <? zlength p) = false) by (apply Z.ltb_ge; lia).
      destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p) eqn:T.
      + (* [comment removed for export] *)
        unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite G, T in H. unfold ebind in H.
        apply impl_bind_assoc_rev in H.
        unfold mbind at 1. change ((stdio_writev 2 buf p ;;; stderr_pieces [] ps) st) with (ebind (stdio_writev 2 buf p st) (fun q => stderr_pieces [] ps (snd q))).
        unfold ebind. apply impl_bind_assoc.
        eapply (impl_bind_ext2 segs (at_node segs) _ _ _ _ _ _ _ (stdio_writev_leaves 2 buf p st)); [|exact H].
        intros [|[[] st']] ms' Hr Hi; cbn [ITree.bind] in Hi |- *.
        * exact Hi.
        * cbn in Hr. subst st'. apply IH; [exact SZ | exact Hi].
      + (* [comment removed for export] *)
        unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite G, T in H. cbn [ebind ITree.bind fst snd] in H.
        apply IH; [exact SZ | exact H].
  Qed.
End StderrBridge.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section OnePiece.
  Context {St : Type}.
  Let zlength_app := @Printf_sn.zlength_app Z.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End OnePiece.
