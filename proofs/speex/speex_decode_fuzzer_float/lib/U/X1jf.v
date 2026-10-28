(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2 X1bn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1rd X1oc X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1jh. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1jg. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fr X1ji.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section ITreeFacts.
Context {RCEIL : RunCeiling}.
Variable segs : list Segment.
Context {node : Type}.
Variable atn : node -> machine_state -> Prop.
Local Notation impl := (X1bs.impl segs atn).
Local Notation bind := (X1bs.bind node).

Fixpoint tforall {A} (P : A -> Prop) (t : itree node A) : Prop :=
match t with
| X1bs.Ret r => P r
| Vis n k => forall x, tforall P (k x)
end.

#[using="Type"] Lemma tforall_bind : forall {A B} (P : A -> Prop) (P' : B -> Prop) (t : itree node A) (f : A -> itree node B),
tforall P t -> (forall a, P a -> tforall P' (f a)) -> tforall P' (bind t f).
Proof.
induction t as [r|n k IH]; intros f H Hf; cbn in *; [apply Hf; exact H|].
intros x. apply IH; [apply H | exact Hf].
Qed.

#[using="Type"] Lemma impl_bind_ext2 : forall {A B C} (P : A -> Prop) (t : itree node A) (f : A -> itree node B) (g : A -> itree node C) Q1 Q2 ms,
tforall P t ->
(forall r ms', P r -> impl (f r) Q1 ms' -> impl (g r) Q2 ms') ->
impl (bind t f) Q1 ms -> impl (bind t g) Q2 ms.
Proof.
induction t as [r|n k IH]; intros f g Q1 Q2 ms HP Hfg H; cbn [X1bs.bind] in *.
- apply Hfg; [exact HP | exact H].
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. eapply IH; [apply HP | exact Hfg | apply Hk].
Qed.

#[using="Type"] Lemma impl_bind_elim : forall {A B} (P : A -> Prop) (t : itree node A) (h : A -> itree node B) Q1 Q2 ms,
tforall P t ->
(forall r ms', P r -> impl (h r) Q1 ms' -> evt segs (Q2 r) ms') ->
impl (bind t h) Q1 ms -> impl t Q2 ms.
Proof.
induction t as [r|n k IH]; intros h Q1 Q2 ms HP Hh H; cbn [X1bs.bind] in *.
- cbn. apply (Hh r); [exact HP | exact H].
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. eapply IH; [apply HP | exact Hh | apply Hk].
Qed.

#[using="Type"] Lemma impl_tforall : forall {A} (P : A -> Prop) (t : itree node A) Q ms,
tforall P t -> impl t Q ms -> impl t (fun r ms' => Q r ms' /\ P r) ms.
Proof.
induction t as [r|n k IH]; intros Q ms HP H; cbn in *.
- eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ | exact HP].
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply HP | apply Hk].
Qed.
End ITreeFacts.

Section StderrBridge.
Context {RCEIL : RunCeiling}.
Variable segs : list Segment.
Context {St : Type}.
Local Notation impl := (X1bs.impl segs (at_node segs)).

Definition FLUSH_stderr : M (list Z * St) unit :=
fun bs => let '(buf, st) := bs in
ebind (stdio_writev 2 buf [] st) (fun r => X1bs.Ret (Ok (tt, (@nil Z, snd r)))).

#[using="Type"] Lemma stdio_wloop_leaves : forall fuel fd iovs (st : St),
tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (stdio_wloop fuel fd iovs st).
Proof.
induction fuel as [|fuel IH]; intros fd iovs st; cbn [stdio_wloop]; [exact I|].
unfold mbind, msys, enode, ebind. cbn [X1bs.bind].
intros x. destruct (dec_writev (wv_total iovs) x) as [cnt|]; cbn [X1bs.bind fst snd]; [|exact I].
destruct (cnt =? wv_total iovs); [cbn; reflexivity| apply IH].
Qed.
#[using="Type"] Lemma stdio_writev_leaves : forall fd buf s (st : St),
tforall (fun r => match r with Ok q => snd q = st | Unr => True end) (stdio_writev fd buf s st).
Proof.
intros fd buf s st. unfold stdio_writev. destruct (WRITEV_MAX <? zlength buf + zlength s); [exact I|].
apply stdio_wloop_leaves.
Qed.

#[using="Type"] Lemma OUT_stderr_leaves : forall p buf (st : St),
tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (OUT_stderr p (buf, st)).
Proof.
intros p buf st. unfold OUT_stderr.
destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p); [|cbn; reflexivity].
unfold ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
Qed.

#[using="Type"] Lemma outsk_flush_leaves : forall ps buf (st : St),
tforall (fun r => match r with Ok q => snd (snd q) = st | Unr => True end) (outsk OUT_stderr ps FLUSH_stderr (buf, st)).
Proof.
induction ps as [|p ps IH]; intros buf st; cbn [outsk].
- unfold FLUSH_stderr, ebind. eapply tforall_bind; [apply stdio_writev_leaves|]. intros [|[a s']] H; cbn; [exact I | exact H].
- unfold mbind at 1. unfold ebind. eapply tforall_bind; [apply OUT_stderr_leaves|].
intros [|[[] [buf' st']]] H; cbn in H |- *; [exact I|]. subst st'. apply IH.
Qed.

#[using="Type"] Lemma stderr_bridge : forall ps buf (st : St) (Q : St -> machine_state -> Prop) ms,
impl (outsk OUT_stderr ps FLUSH_stderr (buf, st)) (epost (fun p ms' => Q (snd (snd p)) ms')) ms ->
impl (mbind (stderr_pieces buf ps) (fun b => stdio_writev 2 b []) st) (epost (fun p ms' => Q (snd p) ms')) ms.
Proof.
induction ps as [|p ps IH]; intros buf st Q ms H; cbn [outsk stderr_pieces] in H |- *.
-
rewrite mbind_mret. unfold FLUSH_stderr, ebind in H.
eapply (impl_bind_elim segs (at_node segs) _ _ _ _ _ _ (stdio_writev_leaves 2 buf [] st)); [|exact H].
intros [|[[] st']] ms' Hr Hi; cbn in Hi |- *; [apply evt_done; exact I|].
cbn in Hi. exact Hi.
- destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p) eqn:T.
+
unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite T in H. unfold ebind in H.
apply impl_bind_assoc_rev in H.
unfold mbind at 1. change ((stdio_writev 2 buf p ;;; stderr_pieces [] ps) st) with (ebind (stdio_writev 2 buf p st) (fun q => stderr_pieces [] ps (snd q))).
unfold ebind. apply impl_bind_assoc.
eapply (impl_bind_ext2 segs (at_node segs) _ _ _ _ _ _ _ (stdio_writev_leaves 2 buf p st)); [|exact H].
intros [|[[] st']] ms' Hr Hi; cbn [X1bs.bind] in Hi |- *.
* exact Hi.
* cbn in Hr. subst st'. apply IH. exact Hi.
+
unfold mbind at 1 in H. unfold OUT_stderr in H. rewrite T in H. cbn [ebind X1bs.bind fst snd] in H.
apply IH. exact H.
Qed.
End StderrBridge.
