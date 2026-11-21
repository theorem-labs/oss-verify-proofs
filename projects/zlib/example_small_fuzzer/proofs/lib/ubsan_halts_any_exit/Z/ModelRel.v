(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Fixpoint mrel {A B : Type} (Q : A -> B -> Prop) (m1 : M A) (m2 : M B) : Prop :=
  match m1 with
  | MRet a => match m2 with MRet b => Q a b | _ => False end
  | MOut bs1 k1 => match m2 with MOut bs2 k2 => bs1 = bs2 /\ mrel Q k1 k2 | _ => False end
  | MExit c1 => match m2 with MExit c2 => c1 = c2 | _ => False end
  | MTry k1 => match m2 with MTry k2 => forall b, mrel Q (k1 b) (k2 b) | _ => False end
  end.

Section MRel.
  Context {A B : Type}.

  Lemma mrel_ret : forall (Q : A -> B -> Prop) a b, Q a b -> mrel Q (MRet a) (MRet b).
  Proof. intros Q a b H. exact H. Qed.

  Lemma mrel_exit : forall (Q : A -> B -> Prop) c, mrel Q (MExit c) (MExit c).
  Proof. intros Q c. reflexivity. Qed.

  Lemma mrel_mono : forall (Q Q' : A -> B -> Prop) m1 m2,
    (forall a b, Q a b -> Q' a b) -> mrel Q m1 m2 -> mrel Q' m1 m2.
  Proof.
    intros Q Q' m1. induction m1 as [a|bs k IH|c|k IH]; intros m2 HQ H; destruct m2; cbn in *; try contradiction.
    - apply HQ. exact H.
    - destruct H as [-> H]. split; [reflexivity|]. apply IH; assumption.
    - exact H.
    - intro b. apply IH; [exact HQ | apply H].
  Qed.
End MRel.

Lemma mrel_bind : forall {A B C D : Type} (Q : A -> B -> Prop) (R : C -> D -> Prop)
    (m1 : M A) (m2 : M B) (f1 : A -> M C) (f2 : B -> M D),
  mrel Q m1 m2 ->
  (forall a b, Q a b -> mrel R (f1 a) (f2 b)) ->
  mrel R (mbind m1 f1) (mbind m2 f2).
Proof.
  intros A B C D Q R m1. induction m1 as [a|bs k IH|c|k IH]; intros m2 f1 f2 H Hf; destruct m2; cbn in *; try contradiction.
  - apply Hf. exact H.
  - destruct H as [-> H]. split; [reflexivity|]. apply IH; assumption.
  - exact H.
  - intro b. apply IH; [apply H | exact Hf].
Qed.

Lemma mrel_refl : forall {A : Type} (Q : A -> A -> Prop) (m : M A),
  (forall a, Q a a) -> mrel Q m m.
Proof.
  intros A Q m HQ. induction m as [a|bs k IH|c|k IH]; cbn.
  - apply HQ.
  - split; [reflexivity | exact IH].
  - reflexivity.
  - intro b. apply IH.
Qed.

Lemma mrel_eq_refl : forall {A : Type} (m : M A), mrel eq m m.
Proof. intros A m. apply mrel_refl. intro a; reflexivity. Qed.

Lemma mrel_sym : forall {A B : Type} (Q : A -> B -> Prop) (m1 : M A) (m2 : M B),
  mrel Q m1 m2 -> mrel (fun b a => Q a b) m2 m1.
Proof.
  intros A B Q m1. induction m1 as [a|bs k IH|c|k IH]; intros m2 H; destruct m2; cbn in *; try contradiction.
  - exact H.
  - destruct H as [-> H]. split; [reflexivity|]. apply IH; exact H.
  - symmetry; exact H.
  - intro b. apply IH. apply H.
Qed.

Lemma mrel_trans : forall {A B C : Type} (Q : A -> B -> Prop) (R : B -> C -> Prop)
    (m1 : M A) (m2 : M B) (m3 : M C),
  mrel Q m1 m2 -> mrel R m2 m3 -> mrel (fun a c => exists b, Q a b /\ R b c) m1 m3.
Proof.
  intros A B C Q R m1. induction m1 as [a|bs k IH|c|k IH]; intros m2 m3 H12 H23;
    destruct m2; cbn in *; try contradiction; destruct m3; cbn in *; try contradiction.
  - exists a0. split; assumption.
  - destruct H12 as [-> H12]. destruct H23 as [-> H23]. split; [reflexivity|]. eapply IH; eassumption.
  - congruence.
  - intro b. eapply IH; [apply H12 | apply H23].
Qed.

Lemma mrel_eq : forall {A : Type} (m1 m2 : M A), mrel eq m1 m2 -> m1 = m2.
Proof.
  intros A m1. induction m1 as [a|bs k IH|c|k IH]; intros m2 H; destruct m2; cbn in *; try contradiction.
  - subst; reflexivity.
  - destruct H as [-> H]. f_equal. apply IH. exact H.
  - subst; reflexivity.
  - f_equal. apply FunctionalExtensionality.functional_extensionality. intro b. apply IH. apply H.
Qed.

Lemma mrel_to_beh : forall (Q : unit -> unit -> Prop) (m1 m2 : M unit),
  mrel Q m1 m2 -> to_beh m1 = to_beh m2.
Proof.
  intros Q m1. induction m1 as [a|bs k IH|c|k IH]; intros m2 H; destruct m2; cbn in *; try contradiction.
  - reflexivity.
  - destruct H as [-> H]. f_equal. apply IH. exact H.
  - subst; reflexivity.
  - rewrite (IH false (k0 false)) by apply H. rewrite (IH true (k0 true)) by apply H. reflexivity.
Qed.

Lemma mrel_mtree_M : forall (MM : MallocModel) (t : mtree (mm_state MM)),
  mrel eq (mtree_M MM t) (mtree_M MM t).
Proof. intros MM t. apply mrel_eq_refl. Qed.

Lemma mrel_malloc_M : forall (MM : MallocModel) s n,
  mrel eq (malloc_M MM s n) (malloc_M MM s n).
Proof. intros. apply mrel_eq_refl. Qed.


Fixpoint mall {A : Type} (P : A -> Prop) (m : M A) : Prop :=
  match m with
  | MRet a => P a
  | MOut _ k => mall P k
  | MExit _ => True
  | MTry k => forall b, mall P (k b)
  end.

Lemma mall_mono : forall {A} (P P' : A -> Prop) (m : M A),
  (forall a, P a -> P' a) -> mall P m -> mall P' m.
Proof.
  intros A P P' m HP. induction m as [a|bs k IH|c|k IH]; cbn; intros H; auto.
Qed.

Lemma mall_bind : forall {A B} (P : A -> Prop) (R : B -> Prop) (m : M A) (f : A -> M B),
  mall P m -> (forall a, P a -> mall R (f a)) -> mall R (mbind m f).
Proof.
  intros A B P R m. induction m as [a|bs k IH|c|k IH]; intros f H Hf; cbn in *.
  - apply Hf. exact H.
  - apply IH; assumption.
  - exact I.
  - intro b. apply IH; [apply H | exact Hf].
Qed.

Lemma mall_true : forall {A} (m : M A), mall (fun _ => True) m.
Proof. intros A m. induction m; cbn; auto. Qed.

Lemma mrel_mall : forall {A B} (Q : A -> B -> Prop) (P : A -> Prop) (P' : B -> Prop) (m1 : M A) (m2 : M B),
  mrel Q m1 m2 -> mall P m1 -> mall P' m2 ->
  mrel (fun a b => Q a b /\ P a /\ P' b) m1 m2.
Proof.
  intros A B Q P P' m1. induction m1 as [a|bs k IH|c|k IH]; intros m2 H H1 H2; destruct m2; cbn in *; try contradiction.
  - auto.
  - destruct H as [-> H]. split; [reflexivity|]. apply IH; assumption.
  - exact H.
  - intro b. apply IH; auto.
Qed.

Lemma mrel_mall_l : forall {A B} (Q : A -> B -> Prop) (m1 : M A) (m2 : M B),
  mrel Q m1 m2 -> mall (fun a => exists b, Q a b) m1.
Proof.
  intros A B Q m1. induction m1 as [a|bs k IH|c|k IH]; intros m2 H; destruct m2; cbn in *; try contradiction; auto.
  - exists a0; exact H.
  - destruct H as [_ H]. eapply IH; exact H.
  - intro b. eapply IH. apply H.
Qed.


Definition prod_rel {A1 A2 B1 B2 : Type} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
  (p : A1 * B1) (q : A2 * B2) : Prop := RA (fst p) (fst q) /\ RB (snd p) (snd q).

Definition sum_rel {A1 A2 B1 B2 : Type} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
  (p : A1 + B1) (q : A2 + B2) : Prop :=
  match p, q with
  | inl a, inl b => RA a b
  | inr a, inr b => RB a b
  | _, _ => False
  end.

Definition opt_rel {A1 A2 : Type} (RA : A1 -> A2 -> Prop) (p : option A1) (q : option A2) : Prop :=
  match p, q with
  | Some a, Some b => RA a b
  | None, None => True
  | _, _ => False
  end.

Definition st_rel {St A B : Type} (R : A -> B -> Prop) (p : A * St) (q : B * St) : Prop :=
  R (fst p) (fst q) /\ snd p = snd q.


Section SRel.
  Context {St : Type}.

  Definition srel {A B : Type} (R : A -> B -> Prop) (m1 : SM St A) (m2 : SM St B) : Prop :=
    forall s, mrel (st_rel R) (m1 s) (m2 s).

  Definition sall {A : Type} (I : St -> Prop) (P : A -> St -> Prop) (m : SM St A) : Prop :=
    forall s, I s -> mall (fun p => P (fst p) (snd p)) (m s).

  Lemma srel_mono : forall {A B} (R R' : A -> B -> Prop) (m1 : SM St A) (m2 : SM St B),
    (forall a b, R a b -> R' a b) -> srel R m1 m2 -> srel R' m1 m2.
  Proof.
    intros A B R R' m1 m2 HR H s. eapply mrel_mono; [|apply H].
    intros [a s1] [b s2] [H1 H2]; split; [apply HR; exact H1 | exact H2].
  Qed.

  Lemma srel_ret : forall {A B} (R : A -> B -> Prop) (a : A) (b : B),
    R a b -> srel R (sret a) (sret b).
  Proof. intros A B R a b H s. cbn. split; [exact H | reflexivity]. Qed.

  Lemma srel_bind : forall {A B C D} (Q : A -> B -> Prop) (R : C -> D -> Prop)
      (m1 : SM St A) (m2 : SM St B) (f1 : A -> SM St C) (f2 : B -> SM St D),
    srel Q m1 m2 ->
    (forall a b, Q a b -> srel R (f1 a) (f2 b)) ->
    srel R (sbind m1 f1) (sbind m2 f2).
  Proof.
    intros A B C D Q R m1 m2 f1 f2 Hm Hf s. unfold sbind.
    eapply mrel_bind; [apply Hm|].
    intros [a s1] [b s2] [H1 H2]; cbn in *. subst s2. apply Hf. exact H1.
  Qed.

  Lemma srel_refl : forall {A} (R : A -> A -> Prop) (m : SM St A),
    (forall a, R a a) -> srel R m m.
  Proof. intros A R m HR s. apply mrel_refl. intros [a s']; split; [apply HR | reflexivity]. Qed.

  Lemma srel_eq_refl : forall {A} (m : SM St A), srel eq m m.
  Proof. intros A m. apply srel_refl. intro; reflexivity. Qed.

  Lemma srel_of_eq : forall {A} (R : A -> A -> Prop) (m1 m2 : SM St A),
    m1 = m2 -> (forall a, R a a) -> srel R m1 m2.
  Proof. intros A R m1 m2 -> HR. apply srel_refl. exact HR. Qed.

  Lemma srel_sym : forall {A B} (R : A -> B -> Prop) (m1 : SM St A) (m2 : SM St B),
    srel R m1 m2 -> srel (fun b a => R a b) m2 m1.
  Proof.
    intros A B R m1 m2 H s. eapply mrel_mono; [|apply mrel_sym; apply H].
    intros [b s2] [a s1] [H1 H2]; split; [exact H1 | symmetry; exact H2].
  Qed.

  Lemma srel_sget : srel eq (@sget St) sget.
  Proof. apply srel_eq_refl. Qed.
  Lemma srel_sgets : forall {A} (f : St -> A), srel eq (sgets f) (sgets f).
  Proof. intros; apply srel_eq_refl. Qed.
  Lemma srel_sput : forall s, srel eq (@sput St s) (sput s).
  Proof. intros; apply srel_eq_refl. Qed.
  Lemma srel_smodify : forall f, srel eq (@smodify St f) (smodify f).
  Proof. intros; apply srel_eq_refl. Qed.
  Lemma srel_sout : forall bs, srel eq (@sout St bs) (sout bs).
  Proof. intros; apply srel_eq_refl. Qed.
  Lemma srel_soutb : forall bs, srel eq (@soutb St bs) (soutb bs).
  Proof. intros; apply srel_eq_refl. Qed.
  Lemma srel_stry : srel eq (@stry St) stry.
  Proof. apply srel_eq_refl. Qed.
  Lemma srel_sexit : forall {A B} (R : A -> B -> Prop) c, srel R (@sexit St A c) (@sexit St B c).
  Proof. intros A B R c s. cbn. reflexivity. Qed.
  Lemma srel_swhen : forall (b : bool) (m1 m2 : SM St unit),
    (b = true -> srel eq m1 m2) -> srel eq (swhen b m1) (swhen b m2).
  Proof. intros b m1 m2 H. destruct b; cbn; [apply H; reflexivity | apply srel_eq_refl]. Qed.
  Lemma srel_sunless : forall (b : bool) (m1 m2 : SM St unit),
    (b = false -> srel eq m1 m2) -> srel eq (sunless b m1) (sunless b m2).
  Proof. intros b m1 m2 H. destruct b; cbn; [apply srel_eq_refl | apply H; reflexivity]. Qed.

  Lemma srel_smalloc : forall (MM : MallocModel) (gm : St -> mm_state MM) (sm : mm_state MM -> St -> St) n,
    srel eq (smalloc MM gm sm n) (smalloc MM gm sm n).
  Proof. intros; apply srel_eq_refl. Qed.
  Lemma srel_sfree : forall (MM : MallocModel) (gm : St -> mm_state MM) (sm : mm_state MM -> St -> St) b,
    srel eq (sfree MM gm sm b) (sfree MM gm sm b).
  Proof. intros; apply srel_eq_refl. Qed.
  Lemma srel_sfree_opt : forall (MM : MallocModel) (gm : St -> mm_state MM) (sm : mm_state MM -> St -> St) b,
    srel eq (sfree_opt MM gm sm b) (sfree_opt MM gm sm b).
  Proof. intros; apply srel_eq_refl. Qed.

  Lemma srel_if : forall {A B} (R : A -> B -> Prop) (c : bool) (t1 : SM St A) (t2 : SM St B) e1 e2,
    (c = true -> srel R t1 t2) -> (c = false -> srel R e1 e2) ->
    srel R (if c then t1 else e1) (if c then t2 else e2).
  Proof. intros A B R c t1 t2 e1 e2 Ht He. destruct c; [apply Ht | apply He]; reflexivity. Qed.


  Lemma srel_kcont : forall {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
      (k1 : A1 -> SM St (A1 + B1)) (k2 : A2 -> SM St (A2 + B2)) r1 r2,
    (forall a b, RA a b -> srel (sum_rel RA RB) (k1 a) (k2 b)) ->
    sum_rel RA RB r1 r2 ->
    srel (sum_rel RA RB) (kcont k1 r1) (kcont k2 r2).
  Proof.
    intros A1 A2 B1 B2 RA RB k1 k2 r1 r2 Hk Hr.
    destruct r1 as [a1|b1], r2 as [a2|b2]; cbn in Hr; try contradiction.
    - apply Hk. exact Hr.
    - apply srel_ret. exact Hr.
  Qed.

  Lemma srel_siterK_nat : forall {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
      n (step1 : A1 -> SM St (A1 + B1)) (step2 : A2 -> SM St (A2 + B2)) a1 a2,
    (forall a b, RA a b -> srel (sum_rel RA RB) (step1 a) (step2 b)) ->
    RA a1 a2 ->
    srel (sum_rel RA RB) (siterK_nat n step1 a1) (siterK_nat n step2 a2).
  Proof.
    intros A1 A2 B1 B2 RA RB n. induction n as [|n IH]; intros step1 step2 a1 a2 Hs Ha; cbn [siterK_nat].
    - apply srel_ret. exact Ha.
    - eapply srel_bind; [apply Hs; exact Ha|].
      intros r1 r2 Hr. apply srel_kcont; [|exact Hr]. intros a b Hab. apply IH; assumption.
  Qed.

  Lemma srel_siterZ : forall {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
      n (step1 : A1 -> SM St (A1 + B1)) (step2 : A2 -> SM St (A2 + B2)) d1 d2 a1 a2,
    (forall a b, RA a b -> srel (sum_rel RA RB) (step1 a) (step2 b)) ->
    (forall a b, RA a b -> RB (d1 a) (d2 b)) ->
    RA a1 a2 ->
    srel RB (siterZ n step1 d1 a1) (siterZ n step2 d2 a2).
  Proof.
    intros A1 A2 B1 B2 RA RB n step1 step2 d1 d2 a1 a2 Hs Hd Ha.
    rewrite !siterZ_nat. eapply srel_bind.
    - apply srel_siterK_nat; eassumption.
    - intros r1 r2 Hr. apply srel_ret.
      destruct r1 as [x1|y1], r2 as [x2|y2]; cbn in Hr; try contradiction; [apply Hd; exact Hr | exact Hr].
  Qed.

  Lemma srel_sloopZ : forall {A1 A2} (RA : A1 -> A2 -> Prop) (RB : A1 -> A2 -> Prop)
      n (step1 : A1 -> SM St (bool * A1)) (step2 : A2 -> SM St (bool * A2)) a1 a2,
    (forall a b, RA a b ->
       srel (fun (r1 : bool * A1) (r2 : bool * A2) =>
               fst r1 = fst r2 /\ if fst r1 then RA (snd r1) (snd r2) else RB (snd r1) (snd r2))
            (step1 a) (step2 b)) ->
    (forall a b, RA a b -> RB a b) ->
    RA a1 a2 ->
    srel RB (sloopZ n step1 a1) (sloopZ n step2 a2).
  Proof.
    intros A1 A2 RA RB n step1 step2 a1 a2 Hs Hd Ha. unfold sloopZ.
    apply (srel_siterZ RA RB); [|exact Hd|exact Ha].
    intros a b Hab. eapply srel_bind; [apply Hs; exact Hab|].
    intros [c1 x1] [c2 x2] [Hc Hx]; cbn in *. subst c2. apply srel_ret. destruct c1; cbn; exact Hx.
  Qed.

  Lemma sforZ_unfold : forall {A} lo hi (body : Z -> A -> SM St A) a,
    sforZ lo hi body a =
    if lo <? hi then sbind (body lo a) (fun a' => sforZ (lo + 1) hi body a') else sret a.
  Proof.
    intros A lo hi body a. unfold sforZ.
    destruct (Z.ltb_spec lo hi).
    - rewrite sloopZ_step by lia. cbn [fst snd].
      rewrite (proj2 (Z.ltb_lt lo hi)) by lia.
      rewrite !sbind_assoc. f_equal.
      apply FunctionalExtensionality.functional_extensionality. intro a'.
      rewrite sbind_ret_l. cbn [fst snd].
      replace (hi - lo - 1) with (hi - (lo + 1)) by lia. reflexivity.
    - rewrite sloopZ_le0 by lia. rewrite sbind_ret_l. reflexivity.
  Qed.

  Lemma srel_sforZ_le : forall {A1 A2} (RA : Z -> A1 -> A2 -> Prop)
      lo hi (body1 : Z -> A1 -> SM St A1) (body2 : Z -> A2 -> SM St A2) a1 a2,
    (forall i a b, lo <= i < hi -> RA i a b -> srel (RA (i + 1)) (body1 i a) (body2 i b)) ->
    RA lo a1 a2 ->
    lo <= hi ->
    srel (RA hi) (sforZ lo hi body1 a1) (sforZ lo hi body2 a2).
  Proof.
    intros A1 A2 RA lo hi body1 body2 a1 a2 Hb Ha Hle.
    remember (Z.to_nat (hi - lo)) as n eqn:Hn.
    revert lo a1 a2 Hb Ha Hle Hn. induction n as [|n IH]; intros lo a1 a2 Hb Ha Hle Hn.
    - assert (lo = hi) by lia. subst lo.
      rewrite (sforZ_unfold hi hi body1), (sforZ_unfold hi hi body2).
      rewrite (proj2 (Z.ltb_ge hi hi)) by lia. apply srel_ret. exact Ha.
    - rewrite (sforZ_unfold lo hi body1), (sforZ_unfold lo hi body2). rewrite (proj2 (Z.ltb_lt lo hi)) by lia.
      eapply srel_bind; [apply Hb; [lia | exact Ha]|].
      intros a b Hab. apply IH; [| exact Hab | lia | lia].
      intros i x y Hi Hr. apply Hb; [lia | exact Hr].
  Qed.

  Lemma srel_sforZ : forall {A1 A2} (RA : Z -> A1 -> A2 -> Prop)
      lo hi (body1 : Z -> A1 -> SM St A1) (body2 : Z -> A2 -> SM St A2) a1 a2,
    (forall i a b, lo <= i < hi -> RA i a b -> srel (RA (i + 1)) (body1 i a) (body2 i b)) ->
    RA lo a1 a2 ->
    srel (RA (Z.max lo hi)) (sforZ lo hi body1 a1) (sforZ lo hi body2 a2).
  Proof.
    intros A1 A2 RA lo hi body1 body2 a1 a2 Hb Ha.
    destruct (Z.le_gt_cases lo hi).
    - rewrite Z.max_r by lia. apply srel_sforZ_le; assumption.
    - rewrite Z.max_l by lia.
      rewrite (sforZ_unfold lo hi body1), (sforZ_unfold lo hi body2).
      rewrite (proj2 (Z.ltb_ge lo hi)) by lia. apply srel_ret. exact Ha.
  Qed.

  Lemma srel_sfor_each : forall {A1 A2 B} (RA : list B -> A1 -> A2 -> Prop)
      (l : list B) (body1 : B -> A1 -> SM St A1) (body2 : B -> A2 -> SM St A2) a1 a2,
    (forall x rest a b, RA (x :: rest) a b -> srel (RA rest) (body1 x a) (body2 x b)) ->
    RA l a1 a2 ->
    srel (RA []) (sfor_each l body1 a1) (sfor_each l body2 a2).
  Proof.
    intros A1 A2 B RA l. induction l as [|x l IH]; intros body1 body2 a1 a2 Hb Ha; cbn [sfor_each].
    - apply srel_ret. exact Ha.
    - eapply srel_bind; [apply Hb; exact Ha|]. intros a b Hab. apply IH; [|exact Hab].
      intros y rest a' b' H. apply Hb. exact H.
  Qed.
End SRel.


Lemma iterK_nat_rel : forall {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
    n (step1 : A1 -> A1 + B1) (step2 : A2 -> A2 + B2) a1 a2,
  (forall a b, RA a b -> sum_rel RA RB (step1 a) (step2 b)) ->
  RA a1 a2 ->
  sum_rel RA RB (iterK_nat n step1 a1) (iterK_nat n step2 a2).
Proof.
  intros A1 A2 B1 B2 RA RB n. induction n as [|n IH]; intros step1 step2 a1 a2 Hs Ha; cbn.
  - exact Ha.
  - pose proof (Hs a1 a2 Ha) as H. destruct (step1 a1) as [x1|y1], (step2 a2) as [x2|y2]; cbn in H; try contradiction.
    + apply IH; assumption.
    + exact H.
Qed.

Lemma iterZ_rel : forall {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
    n (step1 : A1 -> A1 + B1) (step2 : A2 -> A2 + B2) d1 d2 a1 a2,
  (forall a b, RA a b -> sum_rel RA RB (step1 a) (step2 b)) ->
  (forall a b, RA a b -> RB (d1 a) (d2 b)) ->
  RA a1 a2 ->
  RB (iterZ n step1 d1 a1) (iterZ n step2 d2 a2).
Proof.
  intros A1 A2 B1 B2 RA RB n step1 step2 d1 d2 a1 a2 Hs Hd Ha.
  rewrite !iterZ_nat.
  pose proof (iterK_nat_rel RA RB (Z.to_nat n) step1 step2 a1 a2 Hs Ha) as H.
  destruct (iterK_nat _ step1 a1) as [x1|y1], (iterK_nat _ step2 a2) as [x2|y2]; cbn in H; try contradiction.
  - apply Hd. exact H.
  - exact H.
Qed.

Lemma loopZ_rel : forall {A1 A2} (RA RB : A1 -> A2 -> Prop)
    n (step1 : A1 -> bool * A1) (step2 : A2 -> bool * A2) a1 a2,
  (forall a b, RA a b ->
     fst (step1 a) = fst (step2 b) /\
     (if fst (step1 a) then RA (snd (step1 a)) (snd (step2 b)) else RB (snd (step1 a)) (snd (step2 b)))) ->
  (forall a b, RA a b -> RB a b) ->
  RA a1 a2 ->
  RB (loopZ n step1 a1) (loopZ n step2 a2).
Proof.
  intros A1 A2 RA RB n step1 step2 a1 a2 Hs Hd Ha. unfold loopZ.
  apply (iterZ_rel RA RB); [|exact Hd|exact Ha].
  intros a b Hab. pose proof (Hs a b Hab) as [Hc Hr].
  destruct (step1 a) as [c1 x1], (step2 b) as [c2 x2]; cbn in *. subst c2. destruct c1; cbn; exact Hr.
Qed.

Lemma forZ_unfold : forall {A} lo hi (body : Z -> A -> A) a,
  forZ lo hi body a = if lo <? hi then forZ (lo + 1) hi body (body lo a) else a.
Proof.
  intros A lo hi body a. unfold forZ.
  destruct (Z.ltb_spec lo hi).
  - rewrite loopZ_step by lia. rewrite (proj2 (Z.ltb_lt lo hi)) by lia.
    replace (hi - lo - 1) with (hi - (lo + 1)) by lia. reflexivity.
  - rewrite loopZ_le0 by lia. reflexivity.
Qed.

Lemma forZ_rel : forall {A1 A2} (RA : Z -> A1 -> A2 -> Prop)
    lo hi (body1 : Z -> A1 -> A1) (body2 : Z -> A2 -> A2) a1 a2,
  (forall i a b, lo <= i < hi -> RA i a b -> RA (i + 1) (body1 i a) (body2 i b)) ->
  RA lo a1 a2 ->
  lo <= hi ->
  RA hi (forZ lo hi body1 a1) (forZ lo hi body2 a2).
Proof.
  intros A1 A2 RA lo hi body1 body2 a1 a2 Hb Ha Hle.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn.
  revert lo a1 a2 Hb Ha Hle Hn. induction n as [|n IH]; intros lo a1 a2 Hb Ha Hle Hn.
  - assert (lo = hi) by lia. subst lo.
    rewrite (forZ_unfold hi hi body1), (forZ_unfold hi hi body2).
    rewrite (proj2 (Z.ltb_ge hi hi)) by lia. exact Ha.
  - rewrite (forZ_unfold lo hi body1), (forZ_unfold lo hi body2). rewrite (proj2 (Z.ltb_lt lo hi)) by lia.
    apply IH; [| apply Hb; [lia | exact Ha] | lia | lia].
    intros i x y Hi Hr. apply Hb; [lia | exact Hr].
Qed.

Lemma forZ_ind : forall {A} (P : Z -> A -> Prop) lo hi (body : Z -> A -> A) a,
  (forall i x, lo <= i < hi -> P i x -> P (i + 1) (body i x)) ->
  P lo a -> lo <= hi -> P hi (forZ lo hi body a).
Proof.
  intros A P lo hi body a Hb Ha Hle.
  apply (proj1 (B := forZ lo hi body a = forZ lo hi body a)).
  apply (forZ_rel (fun i x y => P i x /\ x = y) lo hi body body a a); [|split; [exact Ha|reflexivity]|exact Hle].
  intros i x y Hi [Hp He]. subst y. split; [apply Hb; assumption | reflexivity].
Qed.


Definition agree {A : Type} (n : Z) (a1 a2 : parr A) : Prop :=
  arr_len a1 = arr_len a2 /\ forall i, 0 <= i < n -> arr_get a1 i = arr_get a2 i.

Section Agree.
  Context {A : Type}.
  Implicit Types a : parr A.

  Lemma agree_len : forall n a1 a2, agree n a1 a2 -> arr_len a1 = arr_len a2.
  Proof. intros n a1 a2 [H _]; exact H. Qed.

  Lemma agree_get : forall n a1 a2 i, agree n a1 a2 -> 0 <= i < n -> arr_get a1 i = arr_get a2 i.
  Proof. intros n a1 a2 i [_ H] Hi. apply H. exact Hi. Qed.

  Lemma agree_le : forall n m a1 a2, agree n a1 a2 -> m <= n -> agree m a1 a2.
  Proof. intros n m a1 a2 [HL H] Hm. split; [exact HL|]. intros i Hi. apply H. lia. Qed.

  Lemma agree_refl : forall n a, agree n a a.
  Proof. intros n a. split; [reflexivity|]. intros; reflexivity. Qed.

  Lemma agree_sym : forall n a1 a2, agree n a1 a2 -> agree n a2 a1.
  Proof. intros n a1 a2 [HL H]. split; [symmetry; exact HL|]. intros i Hi. symmetry. apply H. exact Hi. Qed.

  Lemma agree_trans : forall n a1 a2 a3, agree n a1 a2 -> agree n a2 a3 -> agree n a1 a3.
  Proof.
    intros n a1 a2 a3 [HL12 H12] [HL23 H23]. split; [congruence|].
    intros i Hi. rewrite H12 by exact Hi. apply H23. exact Hi.
  Qed.

  Lemma agree_of_eq : forall n a1 a2, a1 = a2 -> agree n a1 a2.
  Proof. intros n a1 a2 ->. apply agree_refl. Qed.

  Lemma agree_init : forall n k (f1 f2 : Z -> A), n <= 0 -> agree n (arr_init k f1) (arr_init k f2).
  Proof. intros n k f1 f2 Hn. split; [reflexivity|]. intros i Hi. lia. Qed.

  Lemma agree_make : forall n k (v : A), agree n (arr_make k v) (arr_make k v).
  Proof. intros. apply agree_refl. Qed.

  Lemma agree_set : forall n a1 a2 i v, agree n a1 a2 -> agree n (arr_set a1 i v) (arr_set a2 i v).
  Proof.
    intros n a1 a2 i v [HL H]. split; [rewrite !arr_len_set; exact HL|].
    intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite <- HL.
    destruct (_ && _); [reflexivity | apply H; exact Hj].
  Qed.

  Lemma agree_set_ext : forall n a1 a2 i v,
    agree n a1 a2 -> 0 <= i <= n -> i < arr_len a1 ->
    agree (Z.max n (i + 1)) (arr_set a1 i v) (arr_set a2 i v).
  Proof.
    intros n a1 a2 i v [HL H] Hi Hi2. split; [rewrite !arr_len_set; exact HL|].
    intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite <- HL.
    destruct (Z.eqb_spec i j).
    - subst j. replace ((0 <=? i) && (i <? arr_len a1)) with true; [reflexivity|].
      symmetry. apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    - cbn [andb]. apply H. lia.
  Qed.

  Lemma agree_upd : forall l n (a1 a2 : parr A) ofs,
    agree n a1 a2 -> agree n (arr_upd a1 ofs l) (arr_upd a2 ofs l).
  Proof.
    induction l as [|x l IH]; intros n a1 a2 ofs H; cbn [arr_upd].
    - exact H.
    - apply IH. apply agree_set. exact H.
  Qed.

  Lemma agree_upd_ext : forall l n (a1 a2 : parr A) ofs,
    agree n a1 a2 -> 0 <= ofs <= n -> ofs + zlength l <= arr_len a1 ->
    agree (Z.max n (ofs + zlength l)) (arr_upd a1 ofs l) (arr_upd a2 ofs l).
  Proof.
    induction l as [|x l IH]; intros n a1 a2 ofs H Hofs Hlen; cbn [arr_upd].
    - rewrite zlength_nil. replace (Z.max n (ofs + 0)) with n by lia. exact H.
    - rewrite zlength_cons in *.
      assert (Hl : 0 <= zlength l) by apply zlength_nonneg.
      pose proof (agree_set_ext n a1 a2 ofs x H ltac:(lia) ltac:(lia)) as H1.
      pose proof (IH (Z.max n (ofs + 1)) _ _ (ofs + 1) H1 ltac:(lia)) as H2.
      rewrite arr_len_set in H2. specialize (H2 ltac:(lia)).
      replace (Z.max n (ofs + (1 + zlength l))) with (Z.max (Z.max n (ofs + 1)) (ofs + 1 + zlength l)) by lia.
      exact H2.
  Qed.

  Lemma agree_upd_app : forall l n (a1 a2 : parr A),
    agree n a1 a2 -> 0 <= n -> n + zlength l <= arr_len a1 ->
    agree (n + zlength l) (arr_upd a1 n l) (arr_upd a2 n l).
  Proof.
    intros l n a1 a2 H Hn Hlen.
    pose proof (agree_upd_ext l n a1 a2 n H ltac:(lia) Hlen) as H1.
    pose proof (zlength_nonneg l).
    replace (Z.max n (n + zlength l)) with (n + zlength l) in H1 by lia. exact H1.
  Qed.

  Lemma arr_slice_nat_agree : forall k n (a1 a2 : parr A) ofs,
    agree n a1 a2 -> 0 <= ofs -> ofs + Z.of_nat k <= n ->
    arr_slice_nat a1 ofs k = arr_slice_nat a2 ofs k.
  Proof.
    induction k as [|k IH]; intros n a1 a2 ofs H Hofs Hk; cbn [arr_slice_nat].
    - reflexivity.
    - rewrite Nat2Z.inj_succ in Hk. f_equal.
      + apply (agree_get n); [exact H | lia].
      + apply (IH n); [exact H | lia | lia].
  Qed.

  Lemma agree_slice : forall n (a1 a2 : parr A) ofs k,
    agree n a1 a2 -> 0 <= ofs -> ofs + Z.max 0 k <= n ->
    arr_slice a1 ofs k = arr_slice a2 ofs k.
  Proof.
    intros n a1 a2 ofs k H Hofs Hk. unfold arr_slice.
    apply (arr_slice_nat_agree (Z.to_nat k) n); [exact H | exact Hofs | lia].
  Qed.

  Lemma agree_blit_nat : forall k n m (d1 d2 s1 s2 : parr A) dofs sofs,
    agree n d1 d2 -> agree m s1 s2 ->
    0 <= sofs -> sofs + Z.of_nat k <= m ->
    0 <= dofs <= n -> dofs + Z.of_nat k <= arr_len d1 ->
    agree (Z.max n (dofs + Z.of_nat k)) (arr_blit_nat d1 dofs s1 sofs k) (arr_blit_nat d2 dofs s2 sofs k).
  Proof.
    induction k as [|k IH]; intros n m d1 d2 s1 s2 dofs sofs Hd Hs Hso Hsk Hdo Hdk; cbn [arr_blit_nat].
    - replace (Z.max n (dofs + Z.of_nat 0)) with n by lia. exact Hd.
    - rewrite Nat2Z.inj_succ in *.
      rewrite (agree_get m s1 s2 sofs Hs) by lia.
      pose proof (agree_set_ext n d1 d2 dofs (arr_get s2 sofs) Hd ltac:(lia) ltac:(lia)) as H1.
      pose proof (IH (Z.max n (dofs + 1)) m _ _ s1 s2 (dofs + 1) (sofs + 1) H1 Hs ltac:(lia) ltac:(lia) ltac:(lia)) as H2.
      rewrite arr_len_set in H2. specialize (H2 ltac:(lia)).
      replace (Z.max n (dofs + Z.succ (Z.of_nat k))) with (Z.max (Z.max n (dofs + 1)) (dofs + 1 + Z.of_nat k)) by lia.
      exact H2.
  Qed.

  Lemma agree_blit : forall n m (d1 d2 s1 s2 : parr A) dofs sofs k,
    agree n d1 d2 -> agree m s1 s2 ->
    0 <= sofs -> sofs + Z.max 0 k <= m ->
    0 <= dofs <= n -> dofs + Z.max 0 k <= arr_len d1 ->
    agree (Z.max n (dofs + Z.max 0 k)) (arr_blit d1 dofs s1 sofs k) (arr_blit d2 dofs s2 sofs k).
  Proof.
    intros n m d1 d2 s1 s2 dofs sofs k Hd Hs Hso Hsk Hdo Hdk. unfold arr_blit.
    replace (Z.max 0 k) with (Z.of_nat (Z.to_nat k)) in * by lia.
    apply (agree_blit_nat (Z.to_nat k) n m); assumption.
  Qed.

  Lemma agree_len_upd : forall l a ofs, arr_len (arr_upd a ofs l) = arr_len a.
  Proof. intros. apply arr_len_upd. Qed.
End Agree.


Lemma wrap32_le : forall z, 0 <= z -> 0 <= wrap32 z <= z.
Proof.
  intros z Hz. rewrite wrap32_mod. split; [apply Z.mod_pos_bound; lia|]. apply Z.mod_le; lia.
Qed.
Lemma wrap64_le : forall z, 0 <= z -> 0 <= wrap64 z <= z.
Proof.
  intros z Hz. rewrite wrap64_mod. split; [apply Z.mod_pos_bound; lia|]. apply Z.mod_le; lia.
Qed.
Lemma wrap64_small : forall z, 0 <= z < two64 -> wrap64 z = z.
Proof. intros z Hz. unfold two64 in Hz. apply wrap64_id. lia. Qed.
Lemma add64_small : forall a b, 0 <= a -> 0 <= b -> a + b < two64 -> add64 a b = a + b.
Proof. intros. unfold add64. apply wrap64_small. lia. Qed.
Lemma sub64_small : forall a b, 0 <= b <= a -> a < two64 -> sub64 a b = a - b.
Proof. intros a b H Ha. unfold sub64, two64 in *. apply wrap64_id. lia. Qed.
Lemma mul64_small : forall a b, 0 <= a -> 0 <= b -> a * b < two64 -> mul64 a b = a * b.
Proof. intros. unfold mul64. apply wrap64_small. nia. Qed.
Lemma sub32_small : forall a b, 0 <= b <= a -> a < two32 -> sub32 a b = a - b.
Proof. intros a b H Ha. unfold sub32, two32 in *. apply wrap32_id. lia. Qed.
Lemma wrap32_nonneg : forall z, 0 <= wrap32 z.
Proof. intros z. apply wrap32_range. Qed.
Lemma wrap64_nonneg : forall z, 0 <= wrap64 z.
Proof. intros z. apply wrap64_range. Qed.
Lemma wrap32_lt64 : forall z, wrap32 z < two32.
Proof. intros z. unfold two32. pose proof (wrap32_range z). lia. Qed.

Lemma zlength_arr_slice : forall {A} (a : parr A) ofs n, zlength (arr_slice a ofs n) = Z.max 0 n.
Proof. intros. apply arr_slice_length. Qed.

Lemma arr_slice_0 : forall {A} (a1 a2 : parr A) ofs1 ofs2 n, n <= 0 -> arr_slice a1 ofs1 n = arr_slice a2 ofs2 n.
Proof. intros A a1 a2 ofs1 ofs2 n Hn. unfold arr_slice. replace (Z.to_nat n) with 0%nat by lia. reflexivity. Qed.


Lemma mall_sbind : forall {St A B} (P : A * St -> Prop) (R : B * St -> Prop)
    (m : SM St A) (f : A -> SM St B) s,
  mall P (m s) -> (forall a s', P (a, s') -> mall R (f a s')) -> mall R (sbind m f s).
Proof.
  intros St A B P R m f s Hm Hf. unfold sbind. eapply mall_bind; [exact Hm|].
  intros [a s'] H. apply Hf. exact H.
Qed.

Lemma mall_sbind_any : forall {St A B} (R : B * St -> Prop) (m : SM St A) (f : A -> SM St B) s,
  (forall a s', mall R (f a s')) -> mall R (sbind m f s).
Proof.
  intros St A B R m f s Hf. apply (mall_sbind (fun _ => True)); [apply mall_true|]. intros a s' _. apply Hf.
Qed.

Lemma mall_sret : forall {St A} (P : A * St -> Prop) (a : A) (s : St), P (a, s) -> mall P (sret a s).
Proof. intros St A P a s H. exact H. Qed.

Lemma mall_let : forall {St A R : Type} (P : R * St -> Prop) (X : A) (B : A -> SM St R) (g : St),
  (let x := X in mall P (B x g)) -> mall P ((let x := X in B x) g).
Proof. intros St A R P X B g H. exact H. Qed.

Lemma mrel_let2 : forall {St A R1 R2 : Type} (Q : R1 * St -> R2 * St -> Prop) (X1 X2 : A)
    (B1 : A -> SM St R1) (B2 : A -> SM St R2) (g1 g2 : St),
  (let x1 := X1 in let x2 := X2 in mrel Q (B1 x1 g1) (B2 x2 g2)) ->
  mrel Q ((let x := X1 in B1 x) g1) ((let x := X2 in B2 x) g2).
Proof. intros St A R1 R2 Q X1 X2 B1 B2 g1 g2 H. exact H. Qed.
