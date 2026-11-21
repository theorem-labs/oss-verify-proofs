(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (33 recorded proofs replaced by written proofs (fbnd_ret, fbnd_strel, fbnd_steq and 30 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl KInv KStep KLink KEv MI_Tree MI_Sim LB_Logic LB_Kernel LB_Embed.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_Tree () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<enframe_fullC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Tree4fbndC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec5STree9strel_indC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5strel00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Embed5BOUNDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:event_postC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9answer_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree8steq_indC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree4steq00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5erunsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree9stree_indC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Embed5qtreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv8ctree_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9event_preC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec8LB_Embed2QBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec9LB_Kernel2BBC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib4Spec9LB_Kernel2gmC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib4Spec7LB_Tree:BOUND_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Tree6fqtreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree7rejectsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree5ftreeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec7LB_Tree5fbnd8C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib4Spec7MI_Tree7is_peekC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree8is_undefC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree<rejects_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree;rejects_invC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib4Spec7LB_Tree:fbnd_strelC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib4Spec7LB_Tree:fbnd8_prunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree;ptree_strelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree:ftree_prunC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Tree<fqtree_ftreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Tree<fqtree_fbnd8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Tree;qtree_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7MI_Tree>ptree_ctree_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec4KInv8g_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv:set_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_Kernel=BB_set_groupsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:fold_rightK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega=RingMicromega3Op205C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC59OSSVerify5KrLib4Spec5KStep<page_size_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3rd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>peek_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Tree9fbnd8_rd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4rd16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8fold_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7LB_Tree:fbnd8_rd16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint fbnd {R} (B : Z) (L : mled) (t : M R) {struct t} : Prop :=
  match t with
  | SRet _ => True
  | SVis (EPeek _ _ _) k => forall v, fbnd B L (k v)
  | SVis (EUndef _) _ => True
  | SVis e k => BOUND L e B /\ forall a, answer_ok L e a = true -> fbnd B (event_post L e a) (k a)
  end.

Lemma fbnd_ret {R} B L (r : R) : fbnd B L (SRet r).
Proof. exact I. Qed.


(* [comment removed for export] *)
Lemma fbnd_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) B :
  strel RR t1 t2 -> forall L, fbnd B L t1 -> fbnd B L t2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L H; cbn [fbnd] in *; [exact I|].
  destruct e; try (destruct H as [HB H1]; split; [exact HB|]; intros a Ha; apply IH; apply H1; exact Ha).
  - intros v. apply IH. apply H.
  - exact I.
Qed.

(* [comment removed for export] *)
Lemma fbnd_steq {R} (t1 t2 : M R) B : steq t1 t2 -> forall L, fbnd B L t1 -> fbnd B L t2.
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros L H; cbn [fbnd] in *; [exact I|].
  destruct e; try (destruct H as [HB H1]; split; [exact HB|]; intros a Ha; apply IH; apply H1; exact Ha).
  - intros v. apply IH. apply H.
  - exact I.
Qed.

(* [comment removed for export] *)
Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).

Lemma fbnd_prun {R} B : forall (t : M R) L o, fbnd B L t -> fbnd B L (prun pans pupd o t).
Proof.
  induction t as [r|e k IH]; intros L o H; cbn [fbnd] in *; [exact I|].
  unfold prun. destruct e; cbn [eruns psel]; try (destruct H as [HB Hk]; split; [exact HB|]; intros a Ha; apply IH; apply Hk; exact Ha).
  - apply IH. apply H.
  - exact I.
Qed.
End PRUN.

(* [comment removed for export] *)
Lemma qtree_intro {R} B : forall (t : M R) L Post, ctree_ok L t Post -> fbnd B L t -> qtree B L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post HC HB; cbn [ctree_ok fbnd qtree] in *; [exact HC|].
  destruct HC as [He Hk].
  destruct e; try (destruct HB as [HB1 HB2]; split; [exact He|]; split; [exact HB1|]; intros z Hz; apply IH; [apply Hk; exact Hz| apply HB2; exact Hz]);
    cbn in He; destruct He.
Qed.

Lemma qtree_elim {R} B : forall (t : M R) L Post, qtree B L t Post -> ctree_ok L t Post /\ fbnd B L t.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [ctree_ok fbnd qtree] in *; [split; [exact H| exact I]|].
  destruct H as (He & HB & Hk).
  destruct e; try (cbn in He; destruct He; fail);
    (split; [split; [exact He|]; intros z Hz; apply (IH z _ Post); apply Hk; exact Hz
           | split; [exact HB|]; intros z Hz; apply (IH z _ Post); apply Hk; exact Hz]).
Qed.

(* [comment removed for export] *)
Lemma BOUND_mono L e B B' : BOUND L e B -> B <= B' -> BOUND L e B'.
Proof.
  intros [H HQ] HB. split.
  - intros z Hz. specialize (H z Hz). lia.
  - destruct e; cbn in HQ |- *; auto; intros Hf; destruct (HQ Hf) as [Q2 Q3]; split; lia.
Qed.

Lemma fbnd_mono {R} B B' : B <= B' -> forall (t : M R) L, fbnd B L t -> fbnd B' L t.
Proof.
  intros HB. induction t as [r|e k IH]; intros L H; cbn [fbnd] in *; [exact I|].
  destruct e; try (destruct H as [H1 H2]; split; [exact (BOUND_mono H1 HB)|]; intros a Ha; apply IH; apply H2; exact Ha).
  - intros v. apply IH. apply H.
  - exact I.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint fqtree {R} (B : Z) (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> fqtree B L (k v) Post
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ BOUND L e B /\ forall a, if answer_ok L e a then fqtree B (event_post L e a) (k a) Post else rejects (k a)
  end.

Lemma fqtree_ftree {R} B (t : M R) : forall L Post, fqtree B L t Post -> ftree L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [fqtree ftree] in *; [exact H|].
  destruct e; try (destruct H as (He & HB & Hk); split; [exact He|]; intros a; specialize (Hk a); case_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

(* [comment removed for export] *)
Fixpoint fbnd8 {R} (B : Z) (L : mled) (t : M R) {struct t} : Prop :=
  match t with
  | SRet _ => True
  | SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> fbnd8 B L (k v)
  | SVis (EUndef _) _ => True
  | SVis e k => BOUND L e B /\ forall a, answer_ok L e a = true -> fbnd8 B (event_post L e a) (k a)
  end.

Lemma fqtree_fbnd8 {R} B (t : M R) : forall L Post, fqtree B L t Post -> fbnd8 B L t.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [fqtree fbnd8] in *; [exact I|].
  destruct e; try (destruct H as (He & HB & Hk); split; [exact HB|]; intros a Ha; specialize (Hk a); rewrite Ha in Hk; apply (IH a _ Post); exact Hk).
  - intros v Hv. apply (IH v _ Post). apply H. exact Hv.
  - exact I.
Qed.

Section PRUN8.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Lemma fbnd8_prun {R} B : forall (t : M R) L o, fbnd8 B L t -> fbnd B L (prun pans pupd o t).
Proof.
  induction t as [r|e k IH]; intros L o H; cbn [fbnd8 fbnd] in *; [exact I|].
  unfold prun. destruct e; cbn [eruns psel]; try (destruct H as [HB Hk]; split; [exact HB|]; intros a Ha; apply IH; apply Hk; exact Ha).
  - apply IH. apply H. apply Hpans.
  - exact I.
Qed.
End PRUN8.

(* [comment removed for export] *)
Lemma fqtree_ret {R} B L (r : R) Post : Post L r -> fqtree B L (SRet r) Post.
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
Lemma fqtree_vis {R} B L e (k : Z -> M R) Post :
  is_peek e = false -> is_undef e = false ->
  event_pre L e -> QB L e B ->
  (forall z, answer_ok L e z = true -> gm (event_post L e z) + BB (event_post L e z) <= B) ->
  (forall a, answer_ok L e a = true -> fqtree B (event_post L e a) (k a) Post) ->
  (forall a, answer_ok L e a = false -> rejects (k a)) ->
  fqtree B L (SVis e k) Post.
Proof.
  intros Hp Hu He HQ HB Hk Hr. assert (HBB : BOUND L e B) by (split; assumption).
  destruct e; cbn in Hp, Hu; try discriminate; cbn [fqtree]; split; auto; split; auto;
  intros a; case_ans; auto.
Qed.

Lemma fqtree_vis_inv {R} B L e (k : Z -> M R) Post :
  fqtree B L (SVis e k) Post -> is_peek e = false ->
  event_pre L e /\ BOUND L e B /\ forall a, answer_ok L e a = true -> fqtree B (event_post L e a) (k a) Post.
Proof.
  intros H Hp. destruct e; cbn in Hp; try discriminate; cbn [fqtree] in H; try (destruct H; fail).
  all: destruct H as (He & HB & Hk); split; [exact He|]; split; [exact HB|]; intros a Ha; specialize (Hk a); rewrite Ha in Hk; exact Hk.
Qed.

Lemma fqtree_peek {R} B L p c h (k : Z -> M R) Post :
  (forall v, 0 <= v < 256 -> fqtree B L (k v) Post) -> fqtree B L (SVis (EPeek p c h) k) Post.
Proof. intros H. exact H. Qed.

Lemma fqtree_mono {R} B (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, fqtree B L t Post -> fqtree B L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [fqtree] in *; [auto|].
  destruct e; try (destruct H as (He & HB & Hk); split; [exact He|]; split; [exact HB|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

Lemma fqtree_bind {R S} B (t : M R) (f : R -> M S) Post Q L :
  fqtree B L t Post -> (forall L' r, Post L' r -> fqtree B L' (f r) Q) -> fqtree B L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [fqtree sbind] in *.
  - apply Hf. exact H.
  - destruct e; try (destruct H as (He & HB & Hk); split; [exact He|]; split; [exact HB|]; intros a; specialize (Hk a);
      case_ans; [apply IH; [exact Hk| exact Hf]|];
      apply rejects_bind; exact Hk).
    + intros v Hv. apply IH; [apply H; exact Hv| exact Hf].
    + destruct H.
Qed.

Lemma fqtree_guard {R} B L tag (c : bool) (k bail : M R) Post :
  c = true -> fqtree B L k Post -> fqtree B L (guard tag c k bail) Post.
Proof. intros -> H. exact H. Qed.

Lemma fqtree_guard_inv {R} B L tag (c : bool) (k bail : M R) Post :
  fqtree B L (guard tag c k bail) Post -> c = true /\ fqtree B L k Post.
Proof. unfold guard. destruct c; cbn; [auto| intros H; destruct H]. Qed.

Lemma fqtree_steq {R} B (t t' : M R) : steq t t' -> forall L P, fqtree B L t P -> fqtree B L t' P.
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros L P H; [exact H|].
  destruct e; cbn [fqtree] in H |- *; try exact H.
  5: { intros v Hv. apply IH. apply H. exact Hv. }
  all: destruct H as (He & HB & H3); split; [exact He|]; split; [exact HB|]; intros a; specialize (H3 a); case_ans; [apply IH; exact H3|].
  all: specialize (Hk a); destruct (rejects_inv _ H3) as (w & k' & E); rewrite E in Hk; inversion Hk; subst; exact I.
Qed.

(* [comment removed for export] *)
Lemma fqtree_of_ret {R} B L (t : M R) (r : R) Post : t = SRet r -> Post L r -> fqtree B L t Post.
Proof. intros -> H. exact H. Qed.

(* [comment removed for export] *)
Lemma fqtree_monoB {R} B B' (t : M R) : B <= B' -> forall L P, fqtree B L t P -> fqtree B' L t P.
Proof.
  intros HB. induction t as [r|e k IH]; intros L P H; cbn [fqtree] in *; [exact H|].
  destruct e; try (destruct H as (He & H1 & H2); split; [exact He|]; split; [exact (BOUND_mono H1 HB)|]; intros a; specialize (H2 a); case_ans; [apply IH; exact H2| exact H2]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CTRL.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

(* [comment removed for export] *)
Theorem qtree_of_full {R1 R2} (RR : (O * R1)%type -> R2 -> Prop) B (t : M R1) (tc : M R2) L Post (PostC : mled -> R2 -> Prop) o :
  fqtree B L t Post -> strel RR (prun pans pupd o t) tc ->
  (forall L' x r2, RR x r2 -> Post L' (snd x) -> PostC L' r2) ->
  qtree B L tc PostC.
Proof.
  intros FQ REL HP. apply qtree_intro.
  - apply ptree_ctree_ok. eapply (ptree_strel REL); [exact HP|].
    exact (ftree_prun pans pupd Hpans t L Post o (@fqtree_ftree _ B t L Post FQ)).
  - eapply (@fbnd_strel _ _ RR _ tc B REL). apply (fbnd8_prun pans pupd Hpans). exact (@fqtree_fbnd8 _ B t L Post FQ).
Qed.
End CTRL.

(* [comment removed for export] *)
Lemma lbytes_event_post_munmap L a len z : (forall g, In g (ld_groups L) -> 0 <= snd g) ->
  gm (event_post L (EMunmap a len) z) + BB (event_post L (EMunmap a len) z) <= gm L + BB L.
Proof.
  intros POS. cbn [event_post]. rewrite BB_set_groups.
  assert (H : forall l, (forall g, In g l -> 0 <= snd g) ->
    fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) (g_remove a l)) <= fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) l)).
  { induction l as [|[b l0] l IH]; intros P0; cbn; [lia|]. pose proof (P0 (b, l0) (or_introl eq_refl)) as Hl0. cbn in Hl0.
    destruct (b =? a); cbn.
    - assert (0 <= mmap_len l0) by (unfold mmap_len, page_round_up_Z; rewrite page_size_eq; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
      lia.
    - specialize (IH ltac:(intros g Hg; apply P0; right; exact Hg)). lia. }
  unfold gm. cbn [ld_groups ld_metas set_groups]. specialize (H (ld_groups L) POS). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fbnd8_ret {R} B L (r : R) : fbnd8 B L (SRet r).
Proof. exact I. Qed.

Lemma fbnd8_bind {R S} B (t : M R) (f : R -> M S) (Post : mled -> R -> Prop) : forall L,
  fqtree B L t Post -> (forall L' r, Post L' r -> fbnd8 B L' (f r)) -> fbnd8 B L (sbind t f).
Proof.
  induction t as [r|e k IH]; intros L FT Hf; cbn [fbnd8 fqtree sbind] in *.
  - apply Hf. exact FT.
  - destruct e; try (destruct FT as (_ & HB & FK); split; [exact HB|]; intros a Ha; specialize (FK a); rewrite Ha in FK;
      apply IH; [exact FK| exact Hf]).
    + intros v Hv. apply IH; [apply FT; exact Hv| exact Hf].
    + destruct FT.
Qed.

Lemma fbnd8_of_fqtree {R} B (t : M R) L Post : fqtree B L t Post -> fbnd8 B L t.
Proof. intros H. exact (@fqtree_fbnd8 _ B t L Post H). Qed.

Lemma fbnd8_rd8 {R} B L st q (k : Z -> M R) : (forall v, fbnd8 B L (k v)) -> fbnd8 B L (rd8 st q k).
Proof.
  intros H. unfold rd8. destruct (cell_read _ _) as [v|h]; [apply H|].
  cbn [fbnd8]. intros v Hv. destruct (peek_answer_ok v); [apply H| exact I].
Qed.

Lemma fbnd8_rd16 {R} B L st q (k : Z -> M R) : (forall v, fbnd8 B L (k v)) -> fbnd8 B L (rd16 st q k).
Proof. intros H. unfold rd16. apply fbnd8_rd8. intros b0. apply fbnd8_rd8. intros b1. apply H. Qed.

Lemma fbnd8_mono {R} B B' : B <= B' -> forall (t : M R) L, fbnd8 B L t -> fbnd8 B' L t.
Proof.
  intros HB. induction t as [r|e k IH]; intros L H; cbn [fbnd8] in *; [exact I|].
  destruct e; try (destruct H as [H1 H2]; split; [exact (BOUND_mono H1 HB)|]; intros a Ha; apply IH; apply H2; exact Ha).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact I.
Qed.

Lemma fbnd8_steq {R} (t1 t2 : M R) B : steq t1 t2 -> forall L, fbnd8 B L t1 -> fbnd8 B L t2.
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros L H; cbn [fbnd8] in *; [exact I|].
  destruct e; try (destruct H as [HB H1]; split; [exact HB|]; intros a Ha; apply IH; apply H1; exact Ha).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact I.
Qed.

(* [comment removed for export] *)
Lemma fbnd8_enframe_full B L st g idx n ctr (k : mstate -> aptr -> M (mstate * optr)) :
  (forall st' p, fbnd8 B L (k st' p)) -> fbnd8 B L (enframe_full st g idx n ctr k).
Proof.
  intros Hk. unfold enframe_full, enframe_read_off. apply fbnd8_rd8. intros b3.
  destruct (negb (b3 =? 0)).
  - apply fbnd8_rd16. intros o16. destruct (enframe_at _ _ _ _ _). apply Hk.
  - destruct (enframe_at _ _ _ _ _). apply Hk.
Qed.

Section CTRL8.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

(* [comment removed for export] *)
Theorem qtree_of_full8 {R1 R2} (RR : (O * R1)%type -> R2 -> Prop) B (t : M R1) (tc : M R2) L Post (PostC : mled -> R2 -> Prop) o :
  ftree L t Post -> fbnd8 B L t -> strel RR (prun pans pupd o t) tc ->
  (forall L' x r2, RR x r2 -> Post L' (snd x) -> PostC L' r2) ->
  qtree B L tc PostC.
Proof.
  intros FT FB REL HP. apply qtree_intro.
  - apply ptree_ctree_ok. eapply (ptree_strel REL); [exact HP|]. exact (ftree_prun pans pupd Hpans t L Post o FT).
  - eapply (@fbnd_strel _ _ RR _ tc B REL). apply (fbnd8_prun pans pupd Hpans). exact FB.
Qed.
End CTRL8.
