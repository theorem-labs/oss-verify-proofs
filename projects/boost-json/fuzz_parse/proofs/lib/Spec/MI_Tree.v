(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~he2ev37Corelib7Numbers7BinNumsm11Z05false04truehe4aptrhecundef_reason37Corelib4Init5Logicq13and46Stdlib6ZArith6BinInt1Zrb2lerb2lt" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

(* [comment removed for export] *)
Definition rejects {R} (t : M R) : Prop :=
  match t with SVis (EUndef _) _ => True | _ => False end.

Definition is_peek : ltac2:(zQ "20!h8!lc>1e$1$0") := ltac2:(zQ "70!na!ne!lc!h8!o5!ob!p2\1e$2M2\1e$2$3^1\4addr$0$1\4addr$0\3len$0\4prot$0\5flags$0$1\4addr$0\3len$0$1\4addr$0\3len$0\4prot$0$1\1p$5\5caddr$0\4hint$0$4\3why$6$1").
Definition is_undef : ltac2:(zQ "20!h8!lc>1e$1$0") := ltac2:(zQ "70!na!ne!lc!h8!o5!ob!p2\1e$2M2\1e$2$3^1\4addr$0$1\4addr$0\3len$0\4prot$0\5flags$0$1\4addr$0\3len$0$1\4addr$0\3len$0\4prot$0$1\1p$5\5caddr$0\4hint$0$1\3why$6$4").

Lemma rejects_inv {R} (t : M R) : rejects t -> exists w k, t = SVis (EUndef w) k.
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; try tauto. intros _. eauto. Qed.

Lemma rejects_bind {R S} (t : M R) (f : R -> M S) : rejects t -> rejects (sbind t f).
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; tauto. Qed.

Fixpoint ftree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> ftree L (k v) Post
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ftree (event_post L e a) (k a) Post else rejects (k a)
  end.

(* [comment removed for export] *)
Fixpoint ptree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => False
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ptree (event_post L e a) (k a) Post else rejects (k a)
  end.

Ltac case_ans :=
  match goal with
  | |- context [if answer_ok ?L ?e ?a then _ else _] => destruct (answer_ok L e a) eqn:?
  | H : context [if answer_ok ?L ?e ?a then _ else _] |- _ => destruct (answer_ok L e a) eqn:?
  end.

Lemma ftree_vis {R} L e (k : Z -> M R) Post :
  is_peek e = false -> is_undef e = false ->
  event_pre L e ->
  (forall a, answer_ok L e a = true -> ftree (event_post L e a) (k a) Post) ->
  (forall a, answer_ok L e a = false -> rejects (k a)) ->
  ftree L (SVis e k) Post.
Proof.
  intros Hp Hu He Hk Hr. destruct e; cbn in Hp, Hu; try discriminate; cbn [ftree]; split; auto;
  intros a; case_ans; auto.
Qed.

Lemma ftree_bind {R S} (t : M R) (f : R -> M S) Post Q L :
  ftree L t Post -> (forall L' r, Post L' r -> ftree L' (f r) Q) -> ftree L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftree ptree follow sbind] in *.
  - apply Hf. exact H.
  - destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
      case_ans; [apply IH; [exact Hk| exact Hf]|];
      apply rejects_bind; exact Hk).
    + intros v Hv. apply IH; [apply H; exact Hv| exact Hf].
    + destruct H.
Qed.

(* [comment removed for export] *)
Lemma ptree_mono {R} (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, ptree L t Post -> ptree L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]); exact H.
Qed.

(* [comment removed for export] *)
Lemma ptree_ctree_ok {R} : forall (t : M R) L Post, ptree L t Post -> ctree_ok L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [ftree ptree follow sbind] in *; [exact H|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros z Hz; specialize (Hk z); rewrite Hz in Hk; apply IH; exact Hk);
    destruct H.
Qed.

(* [comment removed for export] *)
Lemma ptree_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L (P1 : mled -> R1 -> Prop) (P2 : mled -> R2 -> Prop),
  (forall L' r1 r2, RR r1 r2 -> P1 L' r1 -> P2 L' r2) ->
  ptree L t1 P1 -> ptree L t2 P2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L P1 P2 HP H; cbn [ftree ptree follow sbind] in *.
  - eapply HP; eauto.
  - destruct e; try exact H. all: destruct H as [He H]; split; [exact He|]; intros a; specialize (H a);
      case_ans; [eapply IH; eauto|].
    all: specialize (Hk a); destruct (rejects_inv _ H) as (w & k' & E); rewrite E in Hk; inversion Hk; subst; exact I.
Qed.

(* [comment removed for export] *)
Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : ltac2:(zQ "50!na!r5!ob!t3!t8>1o?1O>1p$2>1c$0>1h$0@2$1@2$3Z@4?4pans^4^3^2^1@2$4@4?4pans^4^3^2^1+hg0").

Lemma ftree_prun {R} : forall (t : M R) L Post o,
  ftree L t Post -> ptree L (prun pans pupd o t) (fun L' x => Post L' (snd x)).
Proof.
  induction t as [r|e k IH]; intros L Post o H; cbn [ftree ptree follow sbind] in *.
  - exact H.
  - unfold prun. destruct e; cbn [eruns psel];
      try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
           case_ans; [apply IH; exact Hk|];
           destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E; exact I).
    + apply IH. apply H. apply Hpans.
    + destruct H.
Qed.
End PRUN.

(* [comment removed for export] *)
Lemma ptree_follow {R} : forall (t : M R) L Post ans r,
  ptree L t Post -> follow t ans = Some r -> exists L', cpath L t L' r /\ Post L' r.
Proof.
  induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ftree ptree follow sbind] in *.
  - inversion Hf; subst. exists L. split; [constructor| exact H].
  - destruct e; try (destruct H; fail); try contradiction.
    all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
      specialize (Hk a); case_ans;
      [ destruct (IH a _ _ _ _ Hk Hf) as (L' & Hp & HP); exists L'; split; [econstructor; eauto| exact HP]
      | destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E in Hf; cbn in Hf; discriminate ].
Qed.

(* [comment removed for export] *)

Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall ans,
  match follow t1 ans, follow t2 ans with
  | Some r1, Some r2 => RR r1 r2
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros ans; cbn.
  - exact Hr.
  - destruct e; destruct ans; cbn; auto; apply IH.
Qed.
(* [comment removed for export] *)
