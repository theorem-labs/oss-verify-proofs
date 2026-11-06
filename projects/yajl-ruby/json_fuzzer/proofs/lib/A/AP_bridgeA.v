(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages ExecA ITreeA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib Printf_pieces Printf_bridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AP_mlibA AP_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section ITreeFactsA.
  Variable segs : list Segment.
  Context {node : Type}.
  Variable atn : (acc -> Prop) -> node -> machine_state -> Prop.
  Variable P : acc -> Prop.
  Local Notation impl := (implA segs atn P).
  Local Notation bind := (ITree.bind node).

  Lemma implA_bind_ext2 : forall {A B C} (PP : A -> Prop) (t : itree node A) (f : A -> itree node B) (g : A -> itree node C) Q1 Q2 ms,
    tforall PP t ->
    (forall r ms', PP r -> impl (f r) Q1 ms' -> impl (g r) Q2 ms') ->
    impl (bind t f) Q1 ms -> impl (bind t g) Q2 ms.
  Proof.
    induction t as [r|n k IH]; intros f g Q1 Q2 ms HP Hfg H; cbn [ITree.bind] in *.
    - apply Hfg; [exact HP | exact H].
    - cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. eapply IH; [apply HP | exact Hfg | apply Hk].
  Qed.

  Lemma implA_bind_elim : forall {A B} (PP : A -> Prop) (t : itree node A) (h : A -> itree node B) Q1 Q2 ms,
    tforall PP t ->
    (forall r ms', PP r -> impl (h r) Q1 ms' -> evtA segs P (Q2 r) ms') ->
    impl (bind t h) Q1 ms -> impl t Q2 ms.
  Proof.
    induction t as [r|n k IH]; intros h Q1 Q2 ms HP Hh H; cbn [ITree.bind] in *.
    - cbn. apply (Hh r); [exact HP | exact H].
    - cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. eapply IH; [apply HP | exact Hh | apply Hk].
  Qed.

  Lemma implA_tforall : forall {A} (PP : A -> Prop) (t : itree node A) Q ms,
    tforall PP t -> impl t Q ms -> impl t (fun r ms' => Q r ms' /\ PP r) ms.
  Proof.
    induction t as [r|n k IH]; intros Q ms HP H; cbn in *.
    - eapply evtA_mono; [exact H|]. intros ms' HQ. split; [exact HQ | exact HP].
    - eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply HP | apply Hk].
  Qed.

  Lemma implA_bind_assoc0 : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C) Q ms,
    impl (bind t (fun x => bind (f x) g)) Q ms -> impl (bind (bind t f) g) Q ms.
  Proof.
    induction t as [r|n k IH]; intros f g Q ms H; cbn [ITree.bind] in *; [exact H|].
    cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
  Qed.
  Lemma implA_bind_assoc0_rev : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C) Q ms,
    impl (bind (bind t f) g) Q ms -> impl (bind t (fun x => bind (f x) g)) Q ms.
  Proof.
    induction t as [r|n k IH]; intros f g Q ms H; cbn [ITree.bind] in *; [exact H|].
    cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
  Qed.

  Lemma implA_epost_mono : forall {A} (t : itree node (exc A)) (Q Q' : A -> machine_state -> Prop) ms,
    impl t (epost Q) ms -> (forall a ms', Q a ms' -> Q' a ms') -> impl t (epost Q') ms.
  Proof.
    intros A t Q Q' ms H HQ. eapply implA_mono; [exact H|]. intros [|a] ms'; cbn; [intros X; exact X | apply HQ].
  Qed.
End ITreeFactsA.

Section StderrBridgeA.
  Context {St : Type}.
  Variable P : acc -> Prop.
  Local Notation impl := (implA asegs (NodesA.at_nodeA asegs) P).


  (* [comment removed for export] *)
  Lemma OUT_stderr_leavesA : forall p buf (st : St),
    tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (OUT_stderr p (buf, st)).
  Proof.
    intros p buf st. unfold OUT_stderr.
    destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); [|cbn; reflexivity].
    unfold ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
  Qed.
  Lemma outsk_flush_leavesA : forall ps buf (st : St),
    tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (outsk OUT_stderr ps FLUSH_stderr (buf, st)).
  Proof.
    induction ps as [|p ps IH]; intros buf st; cbn [outsk].
    - unfold FLUSH_stderr, ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
    - unfold mbind at 1. unfold ebind. eapply tforall_bind; [apply OUT_stderr_leavesA|].
      intros [|[[] [buf' st']]] H; cbn in H |- *; [exact I|]. subst st'. apply IH.
  Qed.

  (* [comment removed for export] *)
  Lemma stderr_bridgeA : forall ps buf (st : St) (Q : St -> machine_state -> Prop) ms,
    impl (outsk OUT_stderr ps FLUSH_stderr (buf, st)) (epost (fun p ms' => Q (snd (snd p)) ms')) ms ->
    impl (mbind (stderr_pieces buf ps) (fun b => stdio_writev 2 b []) st) (epost (fun p ms' => Q (snd p) ms')) ms.
  Proof.
    induction ps as [|p ps IH]; intros buf st Q ms H; cbn [outsk stderr_pieces] in H |- *.
    - rewrite mbind_mret. unfold FLUSH_stderr, ebind in H.
      eapply (implA_bind_elim asegs (NodesA.at_nodeA asegs) P _ _ _ _ _ _ (stdio_writev_leaves 2 buf [] st)); [|exact H].
      intros [|[[] st']] ms' Hr Hi; cbn in Hi |- *; [apply evtA_done; exact I|].
      cbn in Hi. exact Hi.
    - destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p) eqn:T.
      + unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite T in H. unfold ebind in H.
        apply implA_bind_assoc0_rev in H.
        unfold mbind at 1. change ((stdio_writev 2 buf p ;;; stderr_pieces [] ps) st) with (ebind (stdio_writev 2 buf p st) (fun q => stderr_pieces [] ps (snd q))).
        unfold ebind. apply implA_bind_assoc0.
        eapply (implA_bind_ext2 asegs (NodesA.at_nodeA asegs) P _ _ _ _ _ _ _ (stdio_writev_leaves 2 buf p st)); [|exact H].
        intros [|[[] st']] ms' Hr Hi; cbn [ITree.bind] in Hi |- *.
        * exact Hi.
        * cbn in Hr. subst st'. apply IH. exact Hi.
      + unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite T in H. cbn [ebind ITree.bind fst snd] in H.
        apply IH. exact H.
  Qed.
End StderrBridgeA.
End RC__1.
