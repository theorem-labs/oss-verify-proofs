(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Classical IndefiniteDescription.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Exec ITree CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import AcctCore ExecF ITreeA.
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

Section CTreeA.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> footprint -> machine_state -> Prop.
Variable fstep : node -> resp -> footprint -> footprint -> Prop.
Local Notation implF := (implF segs at_node fstep).
Local Notation itree := (itree node).
Local Notation ctree := (ctree node).

Fixpoint implFC {R} (RNG : footprint) (c : ctree R) (Q : R -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match c with
  | CRet r => evtF segs RNG (Q r RNG) ms
  | CVis n k => evtF segs RNG (fun ms1 => at_node n RNG ms1 /\
                  forall rsp RNG', fstep n rsp RNG RNG' -> implFC RNG' (k rsp) Q (nret ms1 rsp)) ms
  | CChoice a b => evtF segs RNG (fun ms1 => implFC RNG a Q ms1 \/ implFC RNG b Q ms1) ms
  end.

Lemma implFC_evtF : forall {R} RNG (c : ctree R) Q P ms,
  evtF segs RNG P ms -> (forall ms', P ms' -> implFC RNG c Q ms') -> implFC RNG c Q ms.
Proof. intros R RNG c Q P ms H K. destruct c; cbn in *; eapply evtF_cut; eauto; intros ms' HP; apply (K _ HP). Qed.

Lemma implFC_mono : forall {R} (c : ctree R) RNG (Q Q' : R -> footprint -> machine_state -> Prop) ms,
  implFC RNG c Q ms -> (forall r RNG' ms', Q r RNG' ms' -> Q' r RNG' ms') -> implFC RNG c Q' ms.
Proof.
  intros R c. induction c as [r|n k IH|a IHa b IHb]; intros RNG Q Q' ms H HQ; cbn in *.
  - eapply evtF_mono; [exact H|]. cbn. intros ms' H'. apply HQ. exact H'.
  - eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp RNG' HF. eapply IH; eauto.
  - eapply evtF_mono; [exact H|]. intros ms1 [Hl|Hr]; [left; eapply IHa; eauto| right; eapply IHb; eauto].
Qed.

Lemma implFC_cinj : forall {R} (t : itree R) RNG Q ms, implF RNG t Q ms <-> implFC RNG (cinj t) Q ms.
Proof.
  intros R t. induction t as [r|n k IH]; intros RNG Q ms; cbn; [reflexivity|].
  split; intros H; (eapply evtF_mono; [exact H|]); intros ms1 [Hat Hk]; (split; [exact Hat|]);
    intros rsp RNG' HF; apply IH, Hk; exact HF.
Qed.

Lemma implFC_bind : forall {A B} (c : ctree A) RNG (f : A -> ctree B) Q1 Q ms,
  implFC RNG c Q1 ms -> (forall r RNG' ms', Q1 r RNG' ms' -> implFC RNG' (f r) Q ms') -> implFC RNG (cbind c f) Q ms.
Proof.
  intros A B c. induction c as [r|n k IH|a IHa b IHb]; intros RNG f Q1 Q ms H Hf; cbn [cbind].
  - cbn in H. eapply implFC_evtF; [exact H|]. intros ms' HQ. exact (Hf _ _ _ HQ).
  - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp RNG' HF. eapply IH; eauto.
  - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hl|Hr]; [left; eapply IHa; eauto| right; eapply IHb; eauto].
Qed.

Lemma implFC_choice_l : forall {R} RNG (a b : ctree R) Q ms, implFC RNG a Q ms -> implFC RNG (CChoice a b) Q ms.
Proof. intros. cbn. apply evtF_done. left. assumption. Qed.
Lemma implFC_choice_r : forall {R} RNG (a b : ctree R) Q ms, implFC RNG b Q ms -> implFC RNG (CChoice a b) Q ms.
Proof. intros. cbn. apply evtF_done. right. assumption. Qed.

Lemma implFC_from_evtF : forall {R} RNG (c : ctree R) Q ms, evtF segs RNG (fun ms' => implFC RNG c Q ms') ms -> implFC RNG c Q ms.
Proof. intros R RNG c Q ms H. eapply implFC_evtF; [exact H|]. intros ms' H'. exact H'. Qed.

Lemma implFC_bind_cong : forall {A B} (c : ctree A) RNG (k1 k2 : A -> ctree B) (Q : B -> footprint -> machine_state -> Prop) ms,
  (forall r RNG' ms', implFC RNG' (k1 r) Q ms' -> implFC RNG' (k2 r) Q ms') ->
  implFC RNG (cbind c k1) Q ms -> implFC RNG (cbind c k2) Q ms.
Proof.
  intros A B c. induction c as [r|n k IH|a IHa b IHb]; intros RNG k1 k2 Q ms HK H; cbn [cbind] in *.
  - apply HK. exact H.
  - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp RNG' HF. eapply IH; [exact HK| apply Hk; exact HF].
  - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hl|Hr]; [left; eapply IHa; eauto| right; eapply IHb; eauto].
Qed.

Lemma implFC_bind_assoc : forall {A B C} (c : ctree A) RNG (g : A -> ctree B) (f : B -> ctree C) Q ms,
  implFC RNG (cbind c (fun x => cbind (g x) f)) Q ms -> implFC RNG (cbind (cbind c g) f) Q ms.
Proof.
  intros A B C c. induction c as [r|n k IH|a IHa b IHb]; intros RNG g f Q ms H; cbn [cbind] in *.
  - exact H.
  - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp RNG' HF. apply IH. apply Hk. exact HF.
  - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hl|Hr]; [left; apply IHa; exact Hl| right; apply IHb; exact Hr].
Qed.

Variable fmin : node -> resp -> footprint -> footprint.
Hypothesis fmin_ok : forall n rsp R R1 R1', fp_le R R1 -> fstep n rsp R1 R1' ->
  fstep n rsp R (fmin n rsp R) /\ fp_le (fmin n rsp R) R1'.
Hypothesis at_node_mono : forall n R R' ms, fp_le R R' -> at_node n R ms -> at_node n R' ms.

Definition fadm (n : node) (rsp : resp) (R : footprint) : Prop := exists R', fstep n rsp R R'.

Fixpoint implFm {R} (RNG : footprint) (t : itree R) (Q : R -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match t with
  | Ret r => evtF segs RNG (Q r RNG) ms
  | Vis n k => evtF segs RNG (fun ms1 => at_node n RNG ms1 /\
                 forall rsp, fadm n rsp RNG -> implFm (fmin n rsp RNG) (k rsp) Q (nret ms1 rsp)) ms
  end.

Fixpoint implFmC {R} (RNG : footprint) (c : ctree R) (Q : R -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match c with
  | CRet r => evtF segs RNG (Q r RNG) ms
  | CVis n k => evtF segs RNG (fun ms1 => at_node n RNG ms1 /\
                  forall rsp, fadm n rsp RNG -> implFmC (fmin n rsp RNG) (k rsp) Q (nret ms1 rsp)) ms
  | CChoice a b => evtF segs RNG (fun ms1 => implFmC RNG a Q ms1 \/ implFmC RNG b Q ms1) ms
  end.

Lemma implFm_evtF : forall {R} RNG (t : itree R) Q P ms,
  evtF segs RNG P ms -> (forall ms', P ms' -> implFm RNG t Q ms') -> implFm RNG t Q ms.
Proof. intros R RNG t Q P ms H K. destruct t; cbn in *; eapply evtF_cut; eauto; intros ms' HP; apply (K _ HP). Qed.

Lemma implFC_implFmC : forall {R} (c : ctree R) RNG Q ms, implFC RNG c Q ms -> implFmC RNG c Q ms.
Proof.
  intros R c. induction c as [r|n k IH|a IHa b IHb]; intros RNG Q ms H; cbn in *.
  - exact H.
  - eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp [R' HF]. apply IH. apply Hk. exact (proj1 (fmin_ok n rsp RNG RNG R' (fp_le_refl RNG) HF)).
  - eapply evtF_mono; [exact H|]. intros ms1 [Hl|Hr]; [left; apply IHa; exact Hl| right; apply IHb; exact Hr].
Qed.

Lemma member_exists : forall {R} (c : ctree R), exists t, member c t.
Proof. intros R c. exists (res (fun _ => true) [] c). apply res_member. Qed.

Lemma implFmC_member : forall {R} (c : ctree R) RNG Q ms, implFmC RNG c Q ms -> exists t, member c t /\ implFm RNG t Q ms.
Proof.
  intros R c. induction c as [r|n k IH|a IHa b IHb]; intros RNG Q ms H; cbn in H.
  - exists (Ret r). split; [apply mem_ret| exact H].
  - destruct H as (ms1 & Hs & Hat & Hk).
    assert (EX : forall rsp, exists t, member (k rsp) t /\ (fadm n rsp RNG -> implFm (fmin n rsp RNG) t Q (nret ms1 rsp))).
    { intros rsp. destruct (classic (fadm n rsp RNG)) as [HA|NA].
      - destruct (IH rsp _ Q _ (Hk rsp HA)) as (t & Hm & Ht). exists t. split; [exact Hm| intros _; exact Ht].
      - destruct (member_exists (k rsp)) as [t Hm]. exists t. split; [exact Hm| intros HA; contradiction]. }
    destruct (choice _ EX) as [k' Hk'].
    exists (Vis n k'). split; [apply mem_vis; intros rsp; exact (proj1 (Hk' rsp))|].
    cbn. exists ms1. split; [exact Hs|]. split; [exact Hat|]. intros rsp HA. exact (proj2 (Hk' rsp) HA).
  - destruct H as (ms1 & Hs & [Hl|Hr]).
    + destruct (IHa RNG Q ms1 Hl) as (t & Hm & Ht). exists t. split; [apply mem_l; exact Hm|].
      apply implFm_evtF with (P := fun m => m = ms1); [exists ms1; split; [exact Hs| reflexivity]|]. intros ms' ->. exact Ht.
    + destruct (IHb RNG Q ms1 Hr) as (t & Hm & Ht). exists t. split; [apply mem_r; exact Hm|].
      apply implFm_evtF with (P := fun m => m = ms1); [exists ms1; split; [exact Hs| reflexivity]|]. intros ms' ->. exact Ht.
Qed.

Lemma implFm_implF : forall {R} (t : itree R) RNG Q ms,
  (forall r R1 R2 ms', fp_le R1 R2 -> Q r R1 ms' -> Q r R2 ms') ->
  implFm RNG t Q ms -> forall R1, fp_le RNG R1 -> implF R1 t Q ms.
Proof.
  intros R t. induction t as [r|n k IH]; intros RNG Q ms Qmono H R1 HLE; cbn in *.
  - eapply evtF_mono; [eapply evtF_weaken; [exact HLE| exact H]|]. cbn. intros ms' HQ. eapply Qmono; [exact HLE| exact HQ].
  - eapply evtF_mono; [eapply evtF_weaken; [exact HLE| exact H]|]. intros ms1 [Hat Hk].
    split; [eapply at_node_mono; [exact HLE| exact Hat]|].
    intros rsp R1' HF. destruct (fmin_ok n rsp RNG R1 R1' HLE HF) as [HF0 HLE'].
    eapply IH; [exact Qmono| apply Hk; exists (fmin n rsp RNG); exact HF0| exact HLE'].
Qed.

Theorem implFC_member : forall {R} (c : ctree R) RNG Q ms,
  (forall r R1 R2 ms', fp_le R1 R2 -> Q r R1 ms' -> Q r R2 ms') ->
  implFC RNG c Q ms -> exists t, member c t /\ implF RNG t Q ms.
Proof.
  intros R c RNG Q ms Qmono H.
  destruct (implFmC_member c RNG Q ms (implFC_implFmC c RNG Q ms H)) as (t & Hm & Ht).
  exists t. split; [exact Hm|]. exact (implFm_implF t RNG Q ms Qmono Ht RNG (fp_le_refl RNG)).
Qed.

Corollary implFC_res : forall {R} (c : ctree R) RNG Q ms,
  (forall r R1 R2 ms', fp_le R1 R2 -> Q r R1 ms' -> Q r R2 ms') ->
  implFC RNG c Q ms -> exists D, implF RNG (res D [] c) Q ms.
Proof.
  intros R c RNG Q ms Qmono H. destruct (implFC_member c RNG Q ms Qmono H) as (t & Hm & Ht).
  destruct (member_res node c t Hm []) as [D ->]. exists D. exact Ht.
Qed.

End CTreeA.

Arguments implFC {node} segs at_node fstep {R} RNG c Q ms.
