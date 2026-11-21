(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (19 recorded proofs replaced by written proofs (rejects_inv, rejects_bind, ftree_ret and 16 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MI_Tree () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Tree7rejectsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Tree5ptreeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00c59OSSVerify5KrLib4Spec7MI_Tree7is_peekC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Tree8is_undefC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec5STree9stree_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Tree<rejects_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8ctree_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7MI_Tree;rejects_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree9strel_indC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5strel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5STree5erunsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl6followC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01I59OSSVerify5KrLib4Spec4KInv5cpath00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec4KInv5cpath01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K59OSSVerify5KrLib4Spec4KInv5cpath02C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

(* [comment removed for export] *)
Definition rejects {R} (t : M R) : Prop :=
  match t with SVis (EUndef _) _ => True | _ => False end.

Definition is_peek (e : ev) : bool := match e with EPeek _ _ _ => true | _ => false end.
Definition is_undef (e : ev) : bool := match e with EUndef _ => true | _ => false end.

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

Lemma ftree_ret {R} L (r : R) Post : Post L r -> ftree L (SRet r) Post.
Proof. intros H. exact H. Qed.

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

Lemma ftree_peek {R} L p c h (k : Z -> M R) Post :
  (forall v, 0 <= v < 256 -> ftree L (k v) Post) -> ftree L (SVis (EPeek p c h) k) Post.
Proof. intros H. exact H. Qed.

Lemma ftree_mono {R} (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, ftree L t Post -> ftree L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
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

Lemma rejects_bad_answer {R} (b : M R) : rejects (bad_answer b).
Proof. exact I. Qed.

Lemma ftree_guard {R} L tag (c : bool) (k bail : M R) Post :
  c = true -> ftree L k Post -> ftree L (guard tag c k bail) Post.
Proof. intros -> H. exact H. Qed.

Lemma ftree_guard_inv {R} L tag (c : bool) (k bail : M R) Post :
  ftree L (guard tag c k bail) Post -> c = true /\ ftree L k Post.
Proof. unfold guard. destruct c; cbn; [auto| intros H; destruct H]. Qed.

(* [comment removed for export] *)
Lemma ptree_mono {R} (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, ptree L t Post -> ptree L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]); exact H.
Qed.

Lemma ptree_bind {R S} (t : M R) (f : R -> M S) Post Q L :
  ptree L t Post -> (forall L' r, Post L' r -> ptree L' (f r) Q) -> ptree L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftree ptree follow sbind] in *.
  - apply Hf. exact H.
  - destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
      case_ans; [apply IH; [exact Hk| exact Hf]|];
      apply rejects_bind; exact Hk); exact H.
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
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

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

Lemma ptree_cpath {R} : forall (t : M R) L Post L' r,
  ptree L t Post -> cpath L t L' r -> Post L' r.
Proof.
  induction t as [r0|e k IH]; intros L Post L' r H Hp; cbn [ftree ptree follow sbind] in *.
  - inversion Hp; subst. exact H.
  - inversion Hp; subst. destruct e; try contradiction.
    all: destruct H as [He Hk];
      match goal with Ha : answer_ok _ _ ?z = true |- _ => specialize (Hk z); rewrite Ha in Hk; eapply IH; eauto end.
Qed.

(* [comment removed for export] *)
Lemma strel_cpath {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L L' r2, cpath L t2 L' r2 -> exists r1, cpath L t1 L' r1 /\ RR r1 r2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L L' r Hp.
  - inversion Hp; subst. exists r1. split; [constructor| exact Hr].
  - inversion Hp; subst.
    match goal with Hc : cpath _ (k2 ?z) _ _ |- _ =>
      destruct (IH z _ _ _ Hc) as (r1 & Hp1 & Hr1); exists r1; split; [econstructor; eauto| exact Hr1] end.
Qed.

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
