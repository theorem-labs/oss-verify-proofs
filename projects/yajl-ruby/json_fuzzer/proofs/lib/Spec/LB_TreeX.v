(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Realloc ReallocProto KInv KLink KStep KStepX MI_Tree MI_Sim
  LB_Kernel LB_Embed LB_Tree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

Section RC__.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Definition XBOUND (L : mled) (e : xev) (B : Z) : Prop :=
  forall z, xanswer_ok L e z = true -> gm (xevent_post L e z) + BB (xevent_post L e z) <= B.

Lemma XBOUND_XE L e B : XBOUND L (XE e) B <-> BOUND L e B.
Proof. unfold XBOUND, BOUND. cbn. tauto. Qed.

Lemma XBOUND_mono L e B B' : XBOUND L e B -> B <= B' -> XBOUND L e B'.
Proof. intros H HB z Hz. specialize (H z Hz). lia. Qed.

Fixpoint xfbnd {R} (B : Z) (L : mled) (t : MX R) {struct t} : Prop :=
  match t with
  | SRet _ => True
  | SVis (XE (EPeek _ _ _)) k => forall v, xfbnd B L (k v)
  | SVis (XE (EUndef _)) _ => True
  | SVis e k => XBOUND L e B /\ forall a, xanswer_ok L e a = true -> xfbnd B (xevent_post L e a) (k a)
  end.

Fixpoint xfbnd8 {R} (B : Z) (L : mled) (t : MX R) {struct t} : Prop :=
  match t with
  | SRet _ => True
  | SVis (XE (EPeek _ _ _)) k => forall v, 0 <= v < 256 -> xfbnd8 B L (k v)
  | SVis (XE (EUndef _)) _ => True
  | SVis e k => XBOUND L e B /\ forall a, xanswer_ok L e a = true -> xfbnd8 B (xevent_post L e a) (k a)
  end.

Fixpoint xfqtree {R} (B : Z) (L : mled) (t : MX R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (XE (EPeek _ _ _)) k => forall v, 0 <= v < 256 -> xfqtree B L (k v) Post
  | SVis (XE (EUndef _)) _ => False
  | SVis e k => xevent_pre L e /\ XBOUND L e B /\
                forall a, if xanswer_ok L e a then xfqtree B (xevent_post L e a) (k a) Post else xrejects (k a)
  end.

(* [comment removed for export] *)
Fixpoint xqtree {R} (B : Z) (L : mled) (t : MX R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => xevent_pre L e /\ XBOUND L e B /\ forall z, xanswer_ok L e z = true -> xqtree B (xevent_post L e z) (k z) Post
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma xfqtree_ftreeX {R} B (t : MX R) : forall L Post, xfqtree B L t Post -> ftreeX L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [xfqtree ftreeX] in *; [exact H|].
  xev_cases e; try (destruct H as (He & HB & Hk); split; [exact He|]; intros a; specialize (Hk a); xcase_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

Lemma xfqtree_xfbnd8 {R} B (t : MX R) : forall L Post, xfqtree B L t Post -> xfbnd8 B L t.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [xfqtree xfbnd8] in *; [exact I|].
  xev_cases e; try (destruct H as (He & HB & Hk); split; [exact HB|]; intros a Ha; specialize (Hk a); rewrite Ha in Hk; eapply IH; exact Hk).
  - intros v Hv. eapply IH. apply H. exact Hv.
  - exact I.
Qed.

Lemma xfqtree_mono {R} B (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall (t : MX R) L, xfqtree B L t Post -> xfqtree B L t Post'.
Proof.
  intros HP t. induction t as [r|e k IH]; intros L H; cbn [xfqtree] in *; [apply HP; exact H|].
  xev_cases e; try (destruct H as (He & HB & Hk); split; [exact He|]; split; [exact HB|]; intros a; specialize (Hk a); xcase_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

Lemma xfqtree_monoB {R} B B' (t : MX R) : B <= B' -> forall L P, xfqtree B L t P -> xfqtree B' L t P.
Proof.
  intros HB. induction t as [r|e k IH]; intros L P H; cbn [xfqtree] in *; [exact H|].
  xev_cases e; try (destruct H as (He & HB1 & Hk); split; [exact He|]; split; [exact (XBOUND_mono HB1 HB)|]; intros a; specialize (Hk a); xcase_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

Lemma xfqtree_ret {R} B L (r : R) Post : Post L r -> xfqtree B L (SRet r) Post.
Proof. intros H. exact H. Qed.

Lemma xfqtree_bind {R S} B (t : MX R) (f : R -> MX S) Post Q L :
  xfqtree B L t Post -> (forall L' r, Post L' r -> xfqtree B L' (f r) Q) -> xfqtree B L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [sbind xfqtree] in *; [apply Hf; exact H|].
  xev_cases e; try (destruct H as (He & HB & Hk); split; [exact He|]; split; [exact HB|]; intros a; specialize (Hk a); xcase_ans;
                    [apply IH; [exact Hk| exact Hf] | apply xrejects_bind; exact Hk]).
  - intros v Hv. apply IH; [apply H; exact Hv| exact Hf].
  - exact H.
Qed.

(* [comment removed for export] *)
Lemma xfqtree_xlift {R} B : forall (t : M R) L Post, fqtree B L t Post -> xfqtree B L (xlift t) Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [xlift fqtree xfqtree] in *; [exact H|].
  destruct e; cbn [xevent_pre xanswer_ok xevent_post] in *;
    try (destruct H as (He & HB & Hk); split; [exact He|]; split; [apply XBOUND_XE; exact HB|];
         intros a; specialize (Hk a); case_ans; [apply IH; exact Hk| apply xrejects_xlift; exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

Lemma xfbnd8_xlift {R} B : forall (t : M R) L, fbnd8 B L t -> xfbnd8 B L (xlift t).
Proof.
  induction t as [r|e k IH]; intros L H; cbn [xlift fbnd8 xfbnd8] in *; [exact I|].
  destruct e; cbn [xanswer_ok xevent_post] in *;
    try (destruct H as [HB Hk]; split; [apply XBOUND_XE; exact HB|]; intros a Ha; apply IH; apply Hk; exact Ha).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact I.
Qed.

(* [comment removed for export] *)
Lemma xqtree_intro {R} B : forall (t : MX R) L Post, xctree_ok L t Post -> xfbnd B L t -> xqtree B L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post HC HB; cbn [xctree_ok xfbnd xqtree] in *; [exact HC|].
  destruct HC as [He Hk].
  xev_cases e; try (destruct HB as [HB1 HB2]; split; [exact He|]; split; [exact HB1|]; intros z Hz; apply IH; [apply Hk; exact Hz| apply HB2; exact Hz]);
    cbn in He; destruct He.
Qed.

Lemma xqtree_mono {R} B (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall (t : MX R) L, xqtree B L t Post -> xqtree B L t Post'.
Proof.
  intros HP t. induction t as [r|e k IH]; intros L H; cbn [xqtree] in *; [apply HP; exact H|].
  destruct H as (He & HB & Hk). split; [exact He|]. split; [exact HB|]. intros z Hz. apply IH. apply Hk. exact Hz.
Qed.

Lemma xqtree_xctree_ok {R} B : forall (t : MX R) L Post, xqtree B L t Post -> xctree_ok L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [xctree_ok xqtree] in *; [exact H|].
  destruct H as (He & HB & Hk). split; [exact He|]. intros z Hz. apply IH. apply Hk. exact Hz.
Qed.

(* [comment removed for export] *)
Section XPRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Lemma xfbnd8_xprun {R} B : forall (t : MX R) L o, xfbnd8 B L t -> xfbnd B L (xprun pans pupd o t).
Proof.
  induction t as [r|e k IH]; intros L o H; cbn [xfbnd8 xfbnd] in *; [exact I|].
  unfold xprun. xev_cases e; cbn [eruns xpsel]; try (destruct H as [HB Hk]; split; [exact HB|]; intros a Ha; apply IH; apply Hk; exact Ha).
  - apply IH. apply H. apply Hpans.
  - exact I.
Qed.

(* [comment removed for export] *)
Theorem xqtree_of_full8 {R} B (t : MX R) L Post o :
  xfqtree B L t Post -> xqtree B L (xprun pans pupd o t) (fun L' x => Post L' (snd x)).
Proof.
  intros H. apply xqtree_intro.
  - apply ptreeX_xctree_ok. apply (ftreeX_xprun pans pupd Hpans). apply xfqtree_ftreeX with (B := B). exact H.
  - apply xfbnd8_xprun. eapply xfqtree_xfbnd8. exact H.
Qed.
End XPRUN.

End RC__.
