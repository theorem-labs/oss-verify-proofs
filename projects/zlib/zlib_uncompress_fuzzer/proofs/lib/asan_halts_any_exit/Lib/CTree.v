(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical IndefiniteDescription FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Exec ITree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* allowed-axiom cure: the informative excluded middle and functional
   choice, proved from Stdlib.Logic.Classical_Prop.classic and
   Stdlib.Logic.IndefiniteDescription.constructive_indefinite_description only (the repository's allowlist), in place of
   ClassicalDescription / ClassicalChoice. Local: no importer sees these names. The same block, byte for byte, in every text. *)
Local Lemma excluded_middle_informative : forall P : Prop, {P} + {~ P}.
Proof.
  intro P.
  assert (E : exists b : bool, if b then P else ~ P).
  { destruct (classic P) as [p|np]; [exists true; exact p | exists false; exact np]. }
  destruct (constructive_indefinite_description _ E) as [[|] H].
  - left; exact H.
  - right; exact H.
Qed.
Local Lemma choice : forall {A B : Type} (R : A -> B -> Prop),
  (forall x : A, exists y : B, R x y) -> exists f : A -> B, forall x : A, R x (f x).
Proof.
  intros A B R H.
  exists (fun x => proj1_sig (constructive_indefinite_description _ (H x))).
  intro x. exact (proj2_sig (constructive_indefinite_description _ (H x))).
Qed.

Section CTree.
Variable node : Type.
Local Notation itree := (itree node).

Inductive ctree (R : Type) : Type :=
| CRet (r : R)
| CVis (n : node) (k : resp -> ctree R)
| CChoice (a b : ctree R).
Arguments CRet {R} r.
Arguments CVis {R} n k.
Arguments CChoice {R} a b.

Fixpoint cbind {A B} (c : ctree A) (f : A -> ctree B) : ctree B :=
  match c with
  | CRet r => f r
  | CVis n k => CVis n (fun x => cbind (k x) f)
  | CChoice a b => CChoice (cbind a f) (cbind b f)
  end.

Fixpoint cinj {R} (t : itree R) : ctree R :=
  match t with
  | Ret r => CRet r
  | Vis n k => CVis n (fun x => cinj (k x))
  end.


Inductive member {R} : ctree R -> itree R -> Prop :=
| mem_ret : forall r, member (CRet r) (Ret r)
| mem_vis : forall n k k', (forall rsp, member (k rsp) (k' rsp)) -> member (CVis n k) (Vis n k')
| mem_l : forall a b t, member a t -> member (CChoice a b) t
| mem_r : forall a b t, member b t -> member (CChoice a b) t.

Lemma member_cinj : forall {R} (t : itree R), member (cinj t) t.
Proof. induction t as [r|n k IH]; cbn; [apply mem_ret| apply mem_vis; exact IH]. Qed.

Inductive hev : Type := HR (rsp : resp) | HD (b : bool).
Definition hist : Type := list hev.

Fixpoint resH {R} (D : hist -> bool) (h : hist) (c : ctree R) : itree (R * hist) :=
  match c with
  | CRet r => Ret (r, h)
  | CVis n k => Vis n (fun rsp => resH D (h ++ [HR rsp]) (k rsp))
  | CChoice a b => if D h then resH D (h ++ [HD true]) a else resH D (h ++ [HD false]) b
  end.

Fixpoint res {R} (D : hist -> bool) (h : hist) (c : ctree R) : itree R :=
  match c with
  | CRet r => Ret r
  | CVis n k => Vis n (fun rsp => res D (h ++ [HR rsp]) (k rsp))
  | CChoice a b => if D h then res D (h ++ [HD true]) a else res D (h ++ [HD false]) b
  end.

Fixpoint with_hist {R} (t : itree R) (h : hist) : itree (R * hist) :=
  match t with
  | Ret r => Ret (r, h)
  | Vis n k => Vis n (fun rsp => with_hist (k rsp) (h ++ [HR rsp]))
  end.

Lemma res_cinj : forall {R} D (t : itree R) h, res D h (cinj t) = t.
Proof.
  intros R D t. induction t as [r|n k IH]; intros h; cbn; [reflexivity|].
  f_equal. apply functional_extensionality. intros rsp. apply IH.
Qed.

Lemma resH_cinj : forall {R} D (t : itree R) h, resH D h (cinj t) = with_hist t h.
Proof.
  intros R D t. induction t as [r|n k IH]; intros h; cbn; [reflexivity|].
  f_equal. apply functional_extensionality. intros rsp. apply IH.
Qed.

Lemma res_cbind : forall {A B} D (c : ctree A) (f : A -> ctree B) h,
  res D h (cbind c f) = bind node (resH D h c) (fun p => res D (snd p) (f (fst p))).
Proof.
  intros A B D c f. induction c as [r|n k IH|a IHa b IHb]; intros h; cbn.
  - reflexivity.
  - f_equal. apply functional_extensionality. intros rsp. apply IH.
  - destruct (D h); [apply IHa| apply IHb].
Qed.

Lemma resH_cbind : forall {A B} D (c : ctree A) (f : A -> ctree B) h,
  resH D h (cbind c f) = bind node (resH D h c) (fun p => resH D (snd p) (f (fst p))).
Proof.
  intros A B D c f. induction c as [r|n k IH|a IHa b IHb]; intros h; cbn.
  - reflexivity.
  - f_equal. apply functional_extensionality. intros rsp. apply IH.
  - destruct (D h); [apply IHa| apply IHb].
Qed.

Lemma res_local : forall {R} (c : ctree R) D1 D2 h,
  (forall h', D1 (h ++ h') = D2 (h ++ h')) -> res D1 h c = res D2 h c.
Proof.
  intros R c. induction c as [r|n k IH|a IHa b IHb]; intros D1 D2 h HD; cbn.
  - reflexivity.
  - f_equal. apply functional_extensionality. intros rsp. apply IH.
    intros h'. rewrite <- !app_assoc. apply HD.
  - pose proof (HD []) as H0. rewrite app_nil_r in H0. rewrite H0.
    destruct (D2 h); [apply IHa| apply IHb]; intros h'; rewrite <- !app_assoc; apply HD.
Qed.

Lemma res_member : forall {R} (c : ctree R) D h, member c (res D h c).
Proof.
  intros R c. induction c as [r|n k IH|a IHa b IHb]; intros D h; cbn.
  - apply mem_ret.
  - apply mem_vis. intros rsp. apply IH.
  - destruct (D h); [apply mem_l, IHa| apply mem_r, IHb].
Qed.

Definition glue (h : hist) (DD : resp -> hist -> bool) : hist -> bool :=
  fun h2 => match excluded_middle_informative (exists rsp rest, h2 = h ++ HR rsp :: rest) with
            | left E => DD (proj1_sig (constructive_indefinite_description _ E)) h2
            | right _ => true
            end.
Lemma glue_ext : forall h DD rsp h', glue h DD ((h ++ [HR rsp]) ++ h') = DD rsp ((h ++ [HR rsp]) ++ h').
Proof.
  intros h DD rsp h'. unfold glue.
  destruct (excluded_middle_informative _) as [E|NE].
  - destruct (constructive_indefinite_description _ E) as [rsp0 [rest Hr]]. cbn [proj1_sig].
    rewrite <- app_assoc in Hr. apply app_inv_head in Hr. cbn in Hr. injection Hr as E1 _. subst rsp0. reflexivity.
  - exfalso. apply NE. exists rsp, h'. rewrite <- app_assoc. reflexivity.
Qed.

Definition override (h : hist) (b : bool) (D0 : hist -> bool) : hist -> bool :=
  fun h2 => if excluded_middle_informative (h2 = h) then b else D0 h2.
Lemma override_at : forall h b D0, override h b D0 h = b.
Proof. intros. unfold override. destruct (excluded_middle_informative (h = h)); [reflexivity| congruence]. Qed.
Lemma override_ext : forall h b D0 e h', override h b D0 ((h ++ [e]) ++ h') = D0 ((h ++ [e]) ++ h').
Proof.
  intros. unfold override. destruct (excluded_middle_informative _) as [X|_]; [| reflexivity].
  exfalso. apply (f_equal (@length hev)) in X. rewrite !length_app in X. cbn in X. lia.
Qed.

Theorem member_res : forall {R} (c : ctree R) (t : itree R), member c t -> forall h, exists D, t = res D h c.
Proof.
  intros R c t H. induction H as [r|n k k' Hk IH|a b t Ha IH|a b t Hb IH]; intros h.
  - exists (fun _ => true). reflexivity.
  -
    destruct (choice (fun rsp D => k' rsp = res D (h ++ [HR rsp]) (k rsp)) (fun rsp => IH rsp (h ++ [HR rsp]))) as [DD HDD].
    exists (glue h DD). cbn. f_equal. apply functional_extensionality. intros rsp. rewrite (HDD rsp).
    apply res_local. intros h'. symmetry. apply glue_ext.
  - destruct (IH (h ++ [HD true])) as [Da HDa].
    exists (override h true Da). cbn. rewrite override_at, HDa. apply res_local. intros h'. symmetry. apply override_ext.
  - destruct (IH (h ++ [HD false])) as [Db HDb].
    exists (override h false Db). cbn. rewrite override_at, HDb. apply res_local. intros h'. symmetry. apply override_ext.
Qed.

Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Local Notation impl := (impl segs at_node).

Fixpoint implC {R} (c : ctree R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match c with
  | CRet r => evt segs (Q r) ms
  | CVis n k => evt segs (fun ms1 => at_node n ms1 /\ forall rsp, implC (k rsp) Q (nret ms1 rsp)) ms
  | CChoice a b => evt segs (fun ms1 => implC a Q ms1 \/ implC b Q ms1) ms
  end.

Lemma implC_evt : forall {R} (c : ctree R) Q P ms,
  evt segs P ms -> (forall ms', P ms' -> implC c Q ms') -> implC c Q ms.
Proof. intros R c Q P ms H K. destruct c; cbn in *; eapply evt_cut; eauto; intros ms' HP; apply (K _ HP). Qed.

Lemma implC_mono : forall {R} (c : ctree R) (Q Q' : R -> machine_state -> Prop) ms,
  implC c Q ms -> (forall r ms', Q r ms' -> Q' r ms') -> implC c Q' ms.
Proof.
  induction c as [r|n k IH|a IHa b IHb]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_mono; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 [Hl|Hr]; [left; eapply IHa; eauto| right; eapply IHb; eauto].
Qed.

Lemma implC_cinj : forall {R} (t : itree R) Q ms, impl t Q ms <-> implC (cinj t) Q ms.
Proof.
  induction t as [r|n k IH]; intros Q ms; cbn; [reflexivity|].
  split; intros H; (eapply evt_mono; [exact H|]); intros ms1 [Hat Hk]; (split; [exact Hat|]); intros rsp; apply IH, Hk.
Qed.

Lemma implC_bind : forall {A B} (c : ctree A) (f : A -> ctree B) Q1 Q ms,
  implC c Q1 ms -> (forall r ms', Q1 r ms' -> implC (f r) Q ms') -> implC (cbind c f) Q ms.
Proof.
  induction c as [r|n k IH|a IHa b IHb]; intros f Q1 Q ms H Hf; cbn [cbind].
  - cbn in H. eapply implC_evt; [exact H|]. intros ms' HQ. exact (Hf _ _ HQ).
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hl|Hr]; [left; eapply IHa; eauto| right; eapply IHb; eauto].
Qed.

Lemma implC_choice_l : forall {R} (a b : ctree R) Q ms, implC a Q ms -> implC (CChoice a b) Q ms.
Proof. intros. cbn. apply evt_done. left. assumption. Qed.
Lemma implC_choice_r : forall {R} (a b : ctree R) Q ms, implC b Q ms -> implC (CChoice a b) Q ms.
Proof. intros. cbn. apply evt_done. right. assumption. Qed.

Theorem implC_member : forall {R} (c : ctree R) Q ms, implC c Q ms -> exists t, member c t /\ impl t Q ms.
Proof.
  induction c as [r|n k IH|a IHa b IHb]; intros Q ms H; cbn in H.
  - exists (Ret r). split; [apply mem_ret| exact H].
  - destruct H as (ms1 & Hs & Hat & Hk).
    destruct (choice (fun rsp t => member (k rsp) t /\ impl t Q (nret ms1 rsp)) (fun rsp => IH rsp Q _ (Hk rsp))) as [k' Hk'].
    exists (Vis n k'). split; [apply mem_vis; intros rsp; exact (proj1 (Hk' rsp))|].
    cbn. exists ms1. split; [exact Hs|]. split; [exact Hat|]. intros rsp. exact (proj2 (Hk' rsp)).
  - destruct H as (ms1 & Hs & [Hl|Hr]).
    + destruct (IHa Q ms1 Hl) as (t & Hm & Ht). exists t. split; [apply mem_l; exact Hm|].
      apply impl_evt with (P := fun m => m = ms1); [exists ms1; split; [exact Hs| reflexivity]|]. intros ms' ->. exact Ht.
    + destruct (IHb Q ms1 Hr) as (t & Hm & Ht). exists t. split; [apply mem_r; exact Hm|].
      apply impl_evt with (P := fun m => m = ms1); [exists ms1; split; [exact Hs| reflexivity]|]. intros ms' ->. exact Ht.
Qed.

Corollary implC_res : forall {R} (c : ctree R) Q ms, implC c Q ms -> exists D, impl (res D [] c) Q ms.
Proof.
  intros R c Q ms H. destruct (implC_member c Q ms H) as (t & Hm & Ht).
  destruct (member_res c t Hm []) as [D ->]. exists D. exact Ht.
Qed.

End CTree.

Arguments CRet {node R} r.
Arguments CVis {node R} n k.
Arguments CChoice {node R} a b.
Arguments cbind {node A B} c f.
Arguments cinj {node R} t.
Arguments member {node R} c t.
Arguments resH {node R} D h c.
Arguments res {node R} D h c.
Arguments with_hist {node R} t h.
Arguments implC {node} segs at_node {R} c Q ms.
