(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree Realloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition xevent_pre (L : mled) (e : xev) : Prop :=
  match e with
  | XE e => event_pre L e
  | XMremap a ol nl fl =>
      brk_quiet L /\ fl = MREMAP_MAYMOVE
      /\ (exists l, In (a, l) (ld_groups L) /\ ol = round_up_pg l)
      /\ 0 < nl < LEN_MAX /\ nl mod PGSZ = 0 /\ nl <> ol
  end.

Definition xanswer_ok (L : mled) (e : xev) (z : Z) : bool :=
  match e with
  | XE e => answer_ok L e z
  | XMremap a ol nl fl => mremap_answer_ok (lranges L) a ol nl z
  end.

Definition xevent_post (L : mled) (e : xev) (z : Z) : mled :=
  match e with
  | XE e => event_post L e z
  | XMremap a ol nl fl =>
      if is_err z then L else KInv.set_groups ((z, nl) :: g_remove a (ld_groups L)) L
  end.

(* [comment removed for export] *)
Lemma event_post_live' L e z : ld_live (event_post L e z) = ld_live L.
Proof.
  destruct e; cbn; repeat (destruct (_ =? _)); try reflexivity;
  try (destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[? ?]|]; reflexivity);
  try (destruct (is_err z); reflexivity); try (destruct (_ || _); reflexivity).
Qed.

Lemma xevent_post_live L e z : ld_live (xevent_post L e z) = ld_live L.
Proof.
  destruct e as [e|a ol nl fl]; cbn [xevent_post]; [apply event_post_live'|].
  destruct (is_err z); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xrejects {R} (t : MX R) : Prop :=
  match t with SVis (XE (EUndef _)) _ => True | _ => False end.

Definition xis_peek (e : xev) : bool := match e with XE (EPeek _ _ _) => true | _ => false end.
Definition xis_undef (e : xev) : bool := match e with XE (EUndef _) => true | _ => false end.

Lemma xrejects_inv {R} (t : MX R) : xrejects t -> exists w k, t = SVis (XE (EUndef w)) k.
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e as [e|]; [destruct e|]; cbn; try tauto. intros _. eauto. Qed.

Lemma xrejects_bind {R S} (t : MX R) (f : R -> MX S) : xrejects t -> xrejects (sbind t f).
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e as [e|]; [destruct e|]; cbn; tauto. Qed.

Lemma xrejects_xbad_answer {R} (b : MX R) : xrejects (xbad_answer b).
Proof. exact I. Qed.

Lemma xrejects_xlift {R} (t : M R) : rejects t -> xrejects (xlift t).
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; tauto. Qed.

Fixpoint ftreeX {R} (L : mled) (t : MX R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (XE (EPeek _ _ _)) k => forall v, 0 <= v < 256 -> ftreeX L (k v) Post
  | SVis (XE (EUndef _)) _ => False
  | SVis e k => xevent_pre L e /\ forall a, if xanswer_ok L e a then ftreeX (xevent_post L e a) (k a) Post else xrejects (k a)
  end.

Fixpoint ptreeX {R} (L : mled) (t : MX R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (XE (EPeek _ _ _)) k => False
  | SVis (XE (EUndef _)) _ => False
  | SVis e k => xevent_pre L e /\ forall a, if xanswer_ok L e a then ptreeX (xevent_post L e a) (k a) Post else xrejects (k a)
  end.

End RC__1.
Ltac xcase_ans :=
  match goal with
  | |- context [if xanswer_ok ?L ?e ?a then _ else _] => destruct (xanswer_ok L e a) eqn:?
  | H : context [if xanswer_ok ?L ?e ?a then _ else _] |- _ => destruct (xanswer_ok L e a) eqn:?
  end.

(* [comment removed for export] *)
Ltac xev_cases e :=
  let e' := fresh "e" in
  destruct e as [e'|]; [destruct e'|].

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma ftreeX_ret {R} L (r : R) Post : Post L r -> ftreeX L (SRet r) Post.
Proof. intros H. exact H. Qed.

Lemma ftreeX_vis {R} L e (k : Z -> MX R) Post :
  xis_peek e = false -> xis_undef e = false ->
  xevent_pre L e ->
  (forall a, xanswer_ok L e a = true -> ftreeX (xevent_post L e a) (k a) Post) ->
  (forall a, xanswer_ok L e a = false -> xrejects (k a)) ->
  ftreeX L (SVis e k) Post.
Proof.
  intros Hp Hu He Hk Hr. xev_cases e; cbn in Hp, Hu; try discriminate; cbn [ftreeX]; split; auto;
  intros a; xcase_ans; auto.
Qed.

Lemma ftreeX_peek {R} L p c h (k : Z -> MX R) Post :
  (forall v, 0 <= v < 256 -> ftreeX L (k v) Post) -> ftreeX L (SVis (XE (EPeek p c h)) k) Post.
Proof. intros H. exact H. Qed.

Lemma ftreeX_mono {R} (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, ftreeX L t Post -> ftreeX L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [ftreeX] in *; [auto|].
  xev_cases e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    xcase_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

Lemma ftreeX_bind {R S} (t : MX R) (f : R -> MX S) Post Q L :
  ftreeX L t Post -> (forall L' r, Post L' r -> ftreeX L' (f r) Q) -> ftreeX L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftreeX sbind] in *.
  - apply Hf. exact H.
  - xev_cases e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
      xcase_ans; [apply IH; [exact Hk| exact Hf]|];
      apply xrejects_bind; exact Hk).
    + intros v Hv. apply IH; [apply H; exact Hv| exact Hf].
    + destruct H.
Qed.

(* [comment removed for export] *)
Lemma ftreeX_steq {R} (t1 t2 : MX R) : steq t1 t2 -> forall L Post, ftreeX L t1 Post -> ftreeX L t2 Post.
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros L Post H; [exact H|]. cbn [ftreeX] in *.
  xev_cases e; try (destruct H as [He H1]; split; [exact He|]; intros a; specialize (H1 a);
    xcase_ans; [apply IH; exact H1|];
    specialize (Hk a); destruct (xrejects_inv _ H1) as (w & k' & E); rewrite E in Hk; inversion Hk; subst; exact I).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

Lemma ftreeX_xguard {R} L tag (c : bool) (k bail : MX R) Post :
  c = true -> ftreeX L k Post -> ftreeX L (xguard tag c k bail) Post.
Proof. intros -> H. exact H. Qed.

Lemma ftreeX_xguard_inv {R} L tag (c : bool) (k bail : MX R) Post :
  ftreeX L (xguard tag c k bail) Post -> c = true /\ ftreeX L k Post.
Proof. unfold xguard. destruct c; cbn; [auto| intros H; destruct H]. Qed.

(* [comment removed for export] *)
Lemma ftreeX_xlift {R} : forall (t : M R) L Post, ftree L t Post <-> ftreeX L (xlift t) Post.
Proof.
  induction t as [r|e k IH]; intros L Post; cbn [ftree ftreeX xlift]; [tauto|].
  destruct e; cbn [xevent_pre xanswer_ok xevent_post];
    try (split; intros [He Hk]; split; [exact He| | exact He|]; intros a; specialize (Hk a);
         case_ans; [apply IH; exact Hk| apply xrejects_xlift; exact Hk | apply IH; exact Hk|];
         destruct (xrejects_inv _ Hk) as (w & k' & E);
         destruct (k a) as [|e' k'']; cbn in E; [discriminate|]; destruct e'; cbn in E; try discriminate; exact I).
  - split; intros H v Hv; apply IH; apply H; exact Hv.
  - tauto.
Qed.

Lemma ptreeX_ftreeX {R} : forall (t : MX R) L Post, ptreeX L t Post -> ftreeX L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [ftreeX ptreeX] in *; [exact H|].
  xev_cases e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    xcase_ans; [apply IH; exact Hk| exact Hk]); destruct H.
Qed.

(* [comment removed for export] *)
Section XPRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Lemma ftreeX_xprun {R} : forall (t : MX R) L Post o,
  ftreeX L t Post -> ptreeX L (xprun pans pupd o t) (fun L' x => Post L' (snd x)).
Proof.
  induction t as [r|e k IH]; intros L Post o H; cbn [ftreeX ptreeX] in *.
  - exact H.
  - unfold xprun. xev_cases e; cbn [eruns xpsel];
      try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
           xcase_ans; [apply IH; exact Hk|];
           destruct (xrejects_inv _ Hk) as (w & k' & E); rewrite E; exact I).
    + apply IH. apply H. apply Hpans.
    + destruct H.
Qed.
End XPRUN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive xcpath {R} : mled -> MX R -> mled -> R -> Prop :=
| xcpath_ret L r : xcpath L (SRet r) L r
| xcpath_vis L e k z L' r :
    xanswer_ok L e z = true -> xcpath (xevent_post L e z) (k z) L' r -> xcpath L (SVis e k) L' r.

Lemma xcpath_live {R} : forall L (t : MX R) L' r, xcpath L t L' r -> ld_live L' = ld_live L.
Proof. induction 1; [reflexivity|]. rewrite IHxcpath. apply xevent_post_live. Qed.

(* [comment removed for export] *)
Lemma ptreeX_xfollow {R} : forall (t : MX R) L Post ans r,
  ptreeX L t Post -> xfollow t ans = Some r -> exists L', xcpath L t L' r /\ Post L' r.
Proof.
  induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ptreeX xfollow] in *.
  - assert (r0 = r) by (destruct ans; congruence). subst. exists L. split; [constructor| exact H].
  - xev_cases e; try (destruct H; fail); try contradiction.
    all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
      specialize (Hk a); xcase_ans;
      [ destruct (IH a _ _ _ _ Hk Hf) as (L' & HP & HQ); exists L'; split; [econstructor; eauto| exact HQ]
      | destruct (xrejects_inv _ Hk) as (w & k' & E); rewrite E in Hf; cbn in Hf; destruct ans'; discriminate ].
Qed.
End RC__2.
