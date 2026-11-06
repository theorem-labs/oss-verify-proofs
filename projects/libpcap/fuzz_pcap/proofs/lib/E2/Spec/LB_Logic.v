(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Monad MSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition live (mo : Model) : Z := vm_live_bytes (m_vmmaps mo).

(* [comment removed for export] *)
Fixpoint tlive {R} (B : Z) (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> vm_live_bytes (m_vmmaps mo') <= B /\ tlive B (k rsp) mo'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint twl {R} (B : Z) (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> live mo' <= B /\ twl B (k rsp) mo' P
  end.

Lemma twl_mono : forall {R} B (t : itree node R) mo (P P' : R -> Model -> Prop),
  twl B t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twl B t mo P'.
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - intros rsp mo' evs Hst. destruct (H rsp mo' evs Hst) as [HB Hk]. split; [exact HB|]. eapply IH; eauto.
Qed.

Lemma twl_bind : forall {A R} B (t : itree node A) (f : A -> itree node R) mo (P : R -> Model -> Prop),
  twl B t mo (fun a mo1 => twl B (f a) mo1 P) -> twl B (ITree.bind node t f) mo P.
Proof.
  intros A R B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - intros rsp mo' evs Hst. destruct (H rsp mo' evs Hst) as [HB Hk]. split; [exact HB|]. apply IH. exact Hk.
Qed.

Lemma twl_tlive : forall {R} B (t : itree node R) mo P, twl B t mo P -> tlive B t mo.
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact I|].
  intros rsp mo' evs Hst. destruct (H rsp mo' evs Hst) as [HB Hk]. split; [exact HB|]. eapply IH. exact Hk.
Qed.

(* [comment removed for export] *)
Definition etwl {A} (B : Z) (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twl B t mo (fun r mo1 => match r with Unr => True | Ok a => Q a mo1 end).

Lemma etwl_mono : forall {A} B (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwl B t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwl B t mo Q'.
Proof.
  intros A B t mo Q Q' H HQ. unfold etwl in *. eapply twl_mono; [exact H|]. intros [|a] mo1; cbn; auto.
Qed.

Lemma etwl_ebind : forall {A C} B (t : itree node (exc A)) (f : A -> itree node (exc C)) mo Q,
  etwl B t mo (fun a mo1 => etwl B (f a) mo1 Q) -> etwl B (ebind t f) mo Q.
Proof.
  intros A C B t f mo Q H. unfold etwl, ebind in *. apply twl_bind.
  eapply twl_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [exact I| exact Ha].
Qed.

Lemma etwl_tlive : forall {A} B (t : itree node (exc A)) mo Q, etwl B t mo Q -> tlive B t mo.
Proof. intros A B t mo Q H. eapply twl_tlive. exact H. Qed.

(* [comment removed for export] *)
Fixpoint flat {R} (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => forall rsp, match k rsp with Ret _ => True | Vis _ _ => False end
  end.

Lemma etwf_flat_etwl : forall {A} B (t : itree node (exc A)) mo (Q : A -> Model -> Prop),
  flat t -> etwf t mo Q -> (forall a mo1, Q a mo1 -> live mo1 <= B) -> etwl B t mo Q.
Proof.
  intros A B t mo Q Hf H HQ. destruct t as [r|n k]; cbn in *.
  - destruct r; [exact I| exact H].
  - destruct H as [_ Hk]. intros rsp mo' evs Hst. specialize (Hk rsp mo' evs Hst). specialize (Hf rsp).
    destruct (k rsp) as [r|n' k']; [| destruct Hf]. cbn in Hk |- *.
    destruct r as [|a]; [destruct Hk|]. split; [eapply HQ; exact Hk| exact Hk].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSpecL.
Context {St : Type}.
Variable B : Z.

Definition mspecL {A} (P : assn St) (m : M St A) (Q : A -> assn St) : Prop :=
  forall s mo, P s mo -> etwl B (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

#[using="Type"] Lemma mspecL_ret {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecL P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

#[using="Type"] Lemma mspecL_bind {A C} (m : M St A) (f : A -> M St C) (P : assn St) (Q1 : A -> assn St) (Q : C -> assn St) :
  mspecL P m Q1 -> (forall a, mspecL (Q1 a) (f a) Q) -> mspecL P (mbind m f) Q.
Proof.
  intros Hm Hf s mo HP. unfold mbind. apply etwl_ebind.
  eapply etwl_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.

#[using="Type"] Lemma mspecL_conseq {A} (m : M St A) (P P' : assn St) (Q Q' : A -> assn St) :
  mspecL P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecL P' m Q'.
Proof.
  intros Hm HP HQ s mo HP'. eapply etwl_mono; [exact (Hm s mo (HP _ _ HP'))|]. intros [a s1] mo1; cbn; auto.
Qed.

#[using="Type"] Lemma mspecL_pre {A} (m : M St A) (P P' : assn St) (Q : A -> assn St) :
  mspecL P m Q -> (forall s mo, P' s mo -> P s mo) -> mspecL P' m Q.
Proof. intros Hm HP. eapply mspecL_conseq; eauto. Qed.

#[using="Type"] Lemma mspecL_post {A} (m : M St A) (P : assn St) (Q Q' : A -> assn St) :
  mspecL P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecL P m Q'.
Proof. intros Hm HQ. eapply mspecL_conseq; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mspecL_munr {A} (P : assn St) (Q : A -> assn St) : mspecL P munr Q.
Proof. intros s mo _. exact I. Qed.

#[using="Type"] Lemma mspecL_false {A} (m : M St A) (Q : A -> assn St) : mspecL (fun _ _ => False) m Q.
Proof. intros s mo []. Qed.

#[using="Type"] Lemma mspecL_get (P : assn St) : mspecL P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

#[using="Type"] Lemma mspecL_put (P : assn St) (s1 : St) : mspecL P (mput s1) (fun _ s mo => s = s1 /\ exists s0, P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

#[using="Type"] Lemma mspecL_upd (P : assn St) (f : St -> St) : mspecL P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

#[using="Type"] Lemma mspecL_upd' (P : assn St) (Q : unit -> assn St) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspecL P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mspecL_sys {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo ->
     forall rsp mo' evs, nstep n mo rsp mo' evs -> live mo' <= B /\ forall a, dec rsp = Some a -> Q a s mo') ->
  mspecL P (msys n dec) Q.
Proof.
  intros H s mo HP. unfold msys, enode. cbn. intros rsp mo' evs Hst.
  destruct (H s mo HP rsp mo' evs Hst) as [HB HQ]. split; [exact HB|].
  destruct (dec rsp) as [a|]; cbn; [apply HQ; reflexivity| exact I].
Qed.

#[using="Type"] Lemma mspecL_if {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  (b = true -> mspecL P m1 Q) -> (b = false -> mspecL P m2 Q) -> mspecL P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

#[using="Type"] Lemma mspecL_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  mspecL (fun s mo => P s mo /\ b = true) m1 Q -> mspecL (fun s mo => P s mo /\ b = false) m2 Q ->
  mspecL P (if b then m1 else m2) Q.
Proof. intros H1 H2 s mo HP. destruct b; [apply H1|apply H2]; auto. Qed.

#[using="Type"] Lemma mspecL_exI {A X} (P : X -> assn St) (m : M St A) (Q : A -> assn St) :
  (forall x, mspecL (P x) m Q) -> mspecL (fun s mo => exists x, P x s mo) m Q.
Proof. intros H s mo [x HP]. exact (H x s mo HP). Qed.

#[using="Type"] Lemma mspecL_pure {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
  (phi -> mspecL P m Q) -> mspecL (fun s mo => P s mo /\ phi) m Q.
Proof. intros H s mo [HP Hphi]. exact (H Hphi s mo HP). Qed.

#[using="Type"] Lemma mspecL_pure_l {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
  (phi -> mspecL P m Q) -> mspecL (fun s mo => phi /\ P s mo) m Q.
Proof. intros H s mo [Hphi HP]. exact (H Hphi s mo HP). Qed.

#[using="Type"] Lemma mspecL_pointwise {A} (P : assn St) (m : M St A) (Q : A -> assn St) :
  (forall s mo, P s mo -> mspecL (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspecL P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

#[using="Type"] Lemma mspecL_when (b : bool) (m : M St unit) (P : assn St) (Q : unit -> assn St) :
  (b = true -> mspecL P m Q) -> (b = false -> forall s mo, P s mo -> Q tt s mo) -> mspecL P (mwhen b m) Q.
Proof. intros H1 H2. unfold mwhen. destruct b; [apply H1; reflexivity|]. apply mspecL_ret. apply H2. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mspecL_loop {X R} (body : X -> M St (X + R)) (I : X -> assn St) (Q : R -> assn St) :
  (forall x, mspecL (I x) (body x) (fun r s mo => match r with inl x' => I x' s mo | inr v => Q v s mo end)) ->
  forall fuel x, mspecL (I x) (mloop fuel body x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x; cbn [mloop].
  - apply mspecL_munr.
  - eapply mspecL_bind; [apply Hb|]. intros [x'|v]; cbn; [apply IH|]. apply mspecL_ret. auto.
Qed.

#[using="Type"] Lemma mspecL_seq {A C} (m : M St A) (f : A -> M St C) (P R : assn St) (Q : C -> assn St) :
  mspecL P m (fun _ => R) -> (forall a, mspecL R (f a) Q) -> mspecL P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspecL_bind; [exact Hm|]. intros a. apply Hf. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mspecL_program {A} (P : assn St) (m : M St A) (Q : A -> assn St) s mo :
  mspecL P m Q -> P s mo ->
  forall {C} (f : A * St -> itree node (exc C)),
  (forall a s' mo', Q a s' mo' -> etwl B (f (a, s')) mo' (fun _ _ => True)) ->
  tlive B (ebind (m s) f) mo.
Proof.
  intros Hm HP C f Hf. eapply etwl_tlive. apply etwl_ebind.
  eapply etwl_mono; [exact (Hm s mo HP)|]. intros [a s'] mo' HQ. cbn in HQ. apply Hf. exact HQ.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mspec_flat_L {A} (P : assn St) (m : M St A) (Q : A -> assn St) :
  (forall s, flat (m s)) -> mspec P m Q -> (forall a s mo, Q a s mo -> live mo <= B) -> mspecL P m Q.
Proof.
  intros Hf Hm HQ s mo HP. apply (etwf_flat_etwl B (m s) mo _ (Hf s) (Hm s mo HP)).
  intros [a s1] mo1 H1. cbn in H1. eapply HQ. exact H1.
Qed.

(* [comment removed for export] *)
Fixpoint pure_tree {R} (t : itree node R) : Prop := match t with Ret _ => True | Vis _ _ => False end.

#[using="Type"] Lemma mspec_pure_tree_L {A} (P : assn St) (m : M St A) (Q : A -> assn St) :
  (forall s, pure_tree (m s)) -> mspec P m Q -> mspecL P m Q.
Proof.
  intros Hp Hm s mo HP. specialize (Hm s mo HP). specialize (Hp s). unfold etwl, etwf in *.
  destruct (m s) as [r|n k]; [| destruct Hp]. cbn in *. destruct r; [exact I| exact Hm].
Qed.
End MSpecL.

Arguments mspecL {St} B {A} P m Q.
