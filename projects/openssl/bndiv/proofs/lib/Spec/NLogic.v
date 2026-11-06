(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Monad MSafe Relim LB_Logic ProgDetIface ProgDetLogic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint twfN {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ (node_noerr n mo -> forall rsp mo' evs, nstep n mo rsp mo' evs -> twfN (k rsp) mo' P)
  end.

Lemma twfN_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twfN t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twfN t mo P'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros Hn rsp mo' evs Hst. eapply IH; [exact (Hk Hn rsp mo' evs Hst)| exact HP].
Qed.

Lemma twfN_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  twfN t mo (fun a mo1 => twfN (f a) mo1 P) -> twfN (ITree.bind node t f) mo P.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros Hn rsp mo' evs Hst. apply IH. exact (Hk Hn rsp mo' evs Hst).
Qed.

Lemma twf_twfN : forall {R} (t : itree node R) mo P, twf t mo P -> twfN t mo P.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact H|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros _ rsp mo' evs Hst. apply IH. exact (Hk rsp mo' evs Hst).
Qed.

(* [comment removed for export] *)
Definition etwfN {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twfN t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Lemma etwfN_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwfN t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwfN t mo Q'.
Proof. intros A t mo Q Q' H HQ. unfold etwfN in *. eapply twfN_mono; [exact H|]. intros [|a] mo1; cbn; auto. Qed.

Lemma etwfN_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
  etwfN t mo (fun a mo1 => etwfN (f a) mo1 Q) -> etwfN (ebind t f) mo Q.
Proof.
  intros A B t f mo Q H. unfold etwfN, ebind in *. apply twfN_bind.
  eapply twfN_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [destruct Ha| exact Ha].
Qed.

Lemma etwf_etwfN : forall {A} (t : itree node (exc A)) mo Q, etwf t mo Q -> etwfN t mo Q.
Proof. intros A t mo Q H. apply twf_twfN. exact H. Qed.

(* [comment removed for export] *)
Lemma twfN_twf : forall {R} (t : itree node R) mo P,
  twfN t mo P -> tsafe nstep node_noerr t mo -> twf t mo P.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P H Hs; cbn in *; [exact H|].
  destruct H as [Hsafe Hk]. destruct Hs as [Hn Hks]. split; [exact Hsafe|].
  intros rsp mo' evs Hst. apply IH; [exact (Hk Hn rsp mo' evs Hst)| exact (Hks rsp mo' evs Hst)].
Qed.

Theorem twfN_final : forall {A} (t : itree node (exc A)) mo,
  etwfN t mo (fun _ _ => False) -> tsafe nstep node_noerr t mo ->
  leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof. intros A t mo H Hs. apply etwf_leaves. exact (twfN_twf t mo _ H Hs). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma twf_twl : forall {R} B (t : itree node R) mo (P1 P2 : R -> Model -> Prop),
  twf t mo P1 -> twl B t mo P2 -> twf t mo (fun r mo1 => P1 r mo1 /\ P2 r mo1).
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo P1 P2 H1 H2; cbn in *; [split; assumption|].
  destruct H1 as [Hs Hk1]. destruct H2 as [_ Hk2]. split; [exact Hs|].
  intros rsp mo' evs Hst. apply IH; [exact (Hk1 rsp mo' evs Hst)| exact (proj2 (Hk2 rsp mo' evs Hst))].
Qed.

Lemma etwf_etwl : forall {A} B (t : itree node (exc A)) mo (Q1 Q2 : A -> Model -> Prop),
  etwf t mo Q1 -> etwl B t mo Q2 -> etwf t mo (fun a mo1 => Q1 a mo1 /\ Q2 a mo1).
Proof.
  intros A B t mo Q1 Q2 H1 H2. unfold etwf, etwl in *.
  eapply twf_mono; [exact (twf_twl B t mo _ _ H1 H2)|]. intros [|a] mo1 [Ha Hb]; cbn in *; [exact Ha| split; assumption].
Qed.

(* [comment removed for export] *)
Lemma node_noerr_no_enomem : forall n mo, node_noerr n mo -> no_enomem n mo.
Proof. intros n mo H. destruct n; exact H. Qed.

Section WithE.
Variable XT : list event -> Prop.

Lemma etwfN_of_etwf_twfE : forall {A} (t : itree node (exc A)) mo tr (Q1 : A -> Model -> Prop) (Q3 : A -> Model -> list event -> Prop),
  etwf t mo Q1 -> twfE None XT t mo tr Q3 -> minv mo -> m_halted mo = None ->
  etwfN t mo (fun a mo1 => Q1 a mo1 /\ exists tr1, Q3 a mo1 tr1).
Proof.
  intros A t. induction t as [r|n k IH]; intros mo tr Q1 Q3 H1 H3 Hmi Hh.
  - destruct r as [|a]; cbn in *; [exact H1| split; [exact H1| exists tr; exact H3]].
  - cbn in H1, H3 |- *. unfold etwfN. cbn [twfN]. destruct H1 as [Hs Hk1]. destruct H3 as (_ & _ & Hk3).
    split; [exact Hs|]. intros Hn rsp mo' evs Hst.
    destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hs Hst) as [Hh' Hmi'].
    apply (IH rsp mo' (tr ++ evs) Q1 Q3); [exact (Hk1 rsp mo' evs Hst)| |exact Hmi'|exact Hh'].
    apply Hk3. split; [|split; [exact Hst| exact I]].
    split; [exact Hs|]. split; [exact (node_noerr_no_enomem n mo Hn)|]. split; assumption.
Qed.
End WithE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSpecN.
Context {St : Type}.

Definition mspecN {A} (P : assn St) (m : M St A) (Q : A -> assn St) : Prop :=
  forall s mo, P s mo -> etwfN (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Lemma mspec_N {A} (P : assn St) (m : M St A) (Q : A -> assn St) : mspec P m Q -> mspecN P m Q.
Proof. intros H s mo HP. apply etwf_etwfN. exact (H s mo HP). Qed.

Lemma mspecN_ret {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecN P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspecN_bind {A B} (m : M St A) (f : A -> M St B) (P : assn St) (Q1 : A -> assn St) (Q : B -> assn St) :
  mspecN P m Q1 -> (forall a, mspecN (Q1 a) (f a) Q) -> mspecN P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind. apply etwfN_ebind.
  eapply etwfN_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.

Lemma mspecN_conseq {A} (m : M St A) (P P' : assn St) (Q Q' : A -> assn St) :
  mspecN P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecN P' m Q'.
Proof.
  intros Hm HP HQ s mo HP'. eapply etwfN_mono; [exact (Hm s mo (HP _ _ HP'))|]. intros [a s1] mo1; cbn; auto.
Qed.

Lemma mspecN_pre {A} (m : M St A) (P P' : assn St) (Q : A -> assn St) :
  mspecN P m Q -> (forall s mo, P' s mo -> P s mo) -> mspecN P' m Q.
Proof. intros Hm HP. eapply mspecN_conseq; eauto. Qed.

Lemma mspecN_post {A} (m : M St A) (P : assn St) (Q Q' : A -> assn St) :
  mspecN P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecN P m Q'.
Proof. intros Hm HQ. eapply mspecN_conseq; eauto. Qed.

Lemma mspecN_false {A} (m : M St A) (Q : A -> assn St) : mspecN (fun _ _ => False) m Q.
Proof. intros s mo []. Qed.

Lemma mspecN_get (P : assn St) : mspecN P mget (fun s' s mo => s' = s /\ P s mo).
Proof. apply mspec_N. apply mspec_get. Qed.

Lemma mspecN_upd' (P : assn St) (Q : unit -> assn St) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspecN P (mupd f) Q.
Proof. intros H. apply mspec_N. apply mspec_upd'. exact H. Qed.

Lemma mspecN_exI {A X} (P : X -> assn St) (m : M St A) (Q : A -> assn St) :
  (forall x, mspecN (P x) m Q) -> mspecN (fun s mo => exists x, P x s mo) m Q.
Proof. intros H s mo [x HP]. exact (H x s mo HP). Qed.

Lemma mspecN_pure {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
  (phi -> mspecN P m Q) -> mspecN (fun s mo => P s mo /\ phi) m Q.
Proof. intros H s mo [HP Hphi]. exact (H Hphi s mo HP). Qed.

Lemma mspecN_pure_l {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
  (phi -> mspecN P m Q) -> mspecN (fun s mo => phi /\ P s mo) m Q.
Proof. intros H s mo [Hphi HP]. exact (H Hphi s mo HP). Qed.

Lemma mspecN_pointwise {A} (P : assn St) (m : M St A) (Q : A -> assn St) :
  (forall s mo, P s mo -> mspecN (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspecN P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

Lemma mspecN_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn St) (Q : B -> assn St) :
  mspecN P m (fun _ => R) -> (forall a, mspecN R (f a) Q) -> mspecN P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspecN_bind; [exact Hm|]. intros a. apply Hf. Qed.

Lemma mspecN_if {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  (b = true -> mspecN P m1 Q) -> (b = false -> mspecN P m2 Q) -> mspecN P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

(* [comment removed for export] *)
Lemma mspecN_combine {A} (B : Z) (XT : list event -> Prop) (m : M St A)
    (P1 P2 : assn St) (P3 : assnE St) (Q1 Q2 : A -> assn St) (Q3 : A -> assnE St) :
  mspec P1 m Q1 -> mspecL B P2 m Q2 -> mspecE None XT P3 m Q3 ->
  mspecN (fun s mo => P1 s mo /\ P2 s mo /\ (exists tr, P3 s mo tr) /\ minv mo /\ m_halted mo = None) m
         (fun a s mo => Q1 a s mo /\ Q2 a s mo /\ exists tr, Q3 a s mo tr).
Proof.
  intros H1 H2 H3 s mo (HP1 & HP2 & (tr & HP3) & Hmi & Hh).
  pose proof (etwf_etwl B (m s) mo _ _ (H1 s mo HP1) (H2 s mo HP2)) as H12.
  pose proof (etwfN_of_etwf_twfE XT (m s) mo tr _ _ H12 (H3 s mo tr HP3) Hmi Hh) as H123.
  eapply etwfN_mono; [exact H123|]. intros [a s1] mo1 [[Ha Hb] Hc]. cbn in *. auto.
Qed.

(* [comment removed for export] *)
Lemma mspecN_combine2 {A} (B : Z) (m : M St A) (P1 P2 : assn St) (Q1 Q2 : A -> assn St) :
  mspec P1 m Q1 -> mspecL B P2 m Q2 ->
  mspecN (fun s mo => P1 s mo /\ P2 s mo) m (fun a s mo => Q1 a s mo /\ Q2 a s mo).
Proof.
  intros H1 H2 s mo [HP1 HP2]. apply etwf_etwfN.
  eapply etwf_mono; [exact (etwf_etwl B (m s) mo _ _ (H1 s mo HP1) (H2 s mo HP2))|]. intros [a s1] mo1 H. exact H.
Qed.

(* [comment removed for export] *)
Lemma mspecN_program {A} (P : assn St) (m : M St A) s mo :
  mspecN P m (fun _ _ _ => False) -> P s mo ->
  forall {B} (f : A * St -> itree node (exc B)),
  tsafe nstep node_noerr (ebind (m s) f) mo ->
  leaves_unreachable_m nstep (ebind (m s) f) mo /\ tsafe nstep nsafe (ebind (m s) f) mo.
Proof.
  intros Hm HP B f Hs. apply twfN_final; [|exact Hs]. apply etwfN_ebind.
  eapply etwfN_mono; [exact (Hm s mo HP)|]. intros [a s'] mo' [].
Qed.

End MSpecN.
