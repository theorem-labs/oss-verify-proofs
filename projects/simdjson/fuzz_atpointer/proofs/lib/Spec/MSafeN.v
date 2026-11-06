(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition noerr_ans (n : node) (rsp : resp) : Prop :=
  match n with
  | NMmap _ _ _ flags => Z.land flags Prog.MAP_FIXED_Z = 0 -> errno_of (eff_ret rsp) = None
  | NMprotect _ _ _ => errno_of (eff_ret rsp) = None
  | _ => True
  end.

Definition nstepN (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo rsp mo' evs /\ noerr_ans n rsp.

Definition node_noerrN (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap _ _ _ flags => (Z.land flags Prog.MAP_FIXED_Z = 0 ->
      forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None) /\ unforced n mo
  | NMprotect _ _ _ => (forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None) /\ unforced n mo
  | _ => True
  end.

Lemma node_noerrN_ans : forall n mo rsp mo' evs, node_noerrN n mo -> nstep n mo rsp mo' evs -> noerr_ans n rsp.
Proof.
  intros n mo rsp mo' evs Hn Hst. destruct n; cbn in *; try exact I.
  - intros Hf. exact (proj1 Hn Hf rsp mo' evs Hst).
  - exact (proj1 Hn rsp mo' evs Hst).
Qed.

Fixpoint twfN {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstepN n mo rsp mo' evs -> twfN (k rsp) mo' P
  | Cho k => forall z, twfN (k z) mo P
  end.

Lemma twf_N : forall {R} (t : itree node R) mo (P : R -> Model -> Prop), twf t mo P -> twfN t mo P.
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros mo P H; cbn in *; [exact H| |intros z; apply IHc; apply H].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs [Hst _]. apply IH. eapply Hk; exact Hst.
Qed.

Lemma twfN_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twfN t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twfN t mo P'.
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; eauto.
  - intros z. eapply IHc; eauto.
Qed.

Lemma twfN_and : forall {R} (t : itree node R) mo (P1 P2 : R -> Model -> Prop),
  twfN t mo P1 -> twfN t mo P2 -> twfN t mo (fun r mo1 => P1 r mo1 /\ P2 r mo1).
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros mo P1 P2 H1 H2; cbn in *; [split; assumption| |intros z; apply IHc; auto].
  destruct H1 as [Hs H1]. destruct H2 as [_ H2]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; eauto.
Qed.

Lemma twfN_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  twfN t mo (fun a mo1 => twfN (f a) mo1 P) -> twfN (ITree.bind node t f) mo P.
Proof.
  intros A B t. induction t as [r|n k IH|kc IHc]; intros f mo P H; cbn in *.
  - exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
  - intros z. apply IHc. apply H.
Qed.

Lemma twfN_tsafe : forall {R} (t : itree node R) mo P,
  twfN t mo P -> tsafe nstep node_noerrN t mo -> tsafe nstep nsafe t mo.
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros mo P H HN; cbn in *; [exact I| |intros z; eapply IHc; [apply H| apply HN]].
  destruct H as [Hs Hk]. destruct HN as [Hn HNk]. split; [exact Hs|]. intros rsp mo' evs Hst.
  eapply IH; [eapply Hk; split; [exact Hst| exact (node_noerrN_ans _ _ _ _ _ Hn Hst)]| exact (HNk rsp mo' evs Hst)].
Qed.

Lemma twfN_tpath : forall {R} (t : itree node R) mo P tr r mo',
  twfN t mo P -> tsafe nstep node_noerrN t mo -> tpath nstep t mo tr r mo' -> P r mo'.
Proof.
  intros R t. induction t as [r0|n k IH|kc IHc]; intros mo P tr r mo' H HN Hp; cbn in *.
  - destruct Hp as (<- & -> & ->). exact H.
  - destruct H as [_ Hk]. destruct HN as [Hn HNk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    eapply IH; [eapply Hk; split; [exact Hst| exact (node_noerrN_ans _ _ _ _ _ Hn Hst)]| exact (HNk rsp mo1 evs Hst)| exact Hp].
  - destruct Hp as [z Hp]. eapply IHc; [apply H| apply HN| exact Hp].
Qed.

Definition etwfN {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twfN t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Lemma etwf_N : forall {A} (t : itree node (exc A)) mo (Q : A -> Model -> Prop), etwf t mo Q -> etwfN t mo Q.
Proof. intros A t mo Q H. unfold etwf, etwfN in *. apply twf_N. exact H. Qed.

Lemma etwfN_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwfN t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwfN t mo Q'.
Proof.
  intros A t mo Q Q' H HQ. unfold etwfN in *. eapply twfN_mono; [exact H|].
  intros [|a] mo1; cbn; auto.
Qed.

Lemma etwfN_and : forall {A} (t : itree node (exc A)) mo (Q1 Q2 : A -> Model -> Prop),
  etwfN t mo Q1 -> etwfN t mo Q2 -> etwfN t mo (fun a mo1 => Q1 a mo1 /\ Q2 a mo1).
Proof.
  intros A t mo Q1 Q2 H1 H2. unfold etwfN in *. eapply twfN_mono; [exact (twfN_and _ _ _ _ H1 H2)|].
  intros [|a] mo1; cbn; tauto.
Qed.

Lemma etwfN_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
  etwfN t mo (fun a mo1 => etwfN (f a) mo1 Q) -> etwfN (ebind t f) mo Q.
Proof.
  intros A B t f mo Q H. unfold etwfN, ebind in *. apply twfN_bind.
  eapply twfN_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [destruct Ha| exact Ha].
Qed.

Lemma etwfN_leaves : forall {A} (t : itree node (exc A)) mo,
  etwfN t mo (fun _ _ => False) -> tsafe nstep node_noerrN t mo ->
  leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof.
  intros A t mo H HN. split.
  - intros tr r mo' Hp. pose proof (twfN_tpath t mo _ tr r mo' H HN Hp) as HP. destruct r; exact HP.
  - eapply twfN_tsafe; [exact H| exact HN].
Qed.

Section MSpecN.
Context {St : Type}.

Definition mspecN {A} (P : assn St) (m : M St A) (Q : A -> assn St) : Prop :=
  forall s mo, P s mo -> etwfN (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Lemma mspec_N {A} (P : assn St) (m : M St A) (Q : A -> assn St) : mspec P m Q -> mspecN P m Q.
Proof. intros H s mo HP. apply etwf_N. exact (H s mo HP). Qed.

Lemma mspecN_and {A} (P : assn St) (m : M St A) (Q1 Q2 : A -> assn St) :
  mspecN P m Q1 -> mspecN P m Q2 -> mspecN P m (fun a s mo => Q1 a s mo /\ Q2 a s mo).
Proof. intros H1 H2 s mo HP. exact (etwfN_and _ _ _ _ (H1 s mo HP) (H2 s mo HP)). Qed.

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
  intros Hm HP HQ s mo HP'. eapply etwfN_mono; [exact (Hm s mo (HP _ _ HP'))|].
  intros [a s1] mo1; cbn; auto.
Qed.

Lemma mspecN_pre {A} (m : M St A) (P P' : assn St) (Q : A -> assn St) :
  mspecN P m Q -> (forall s mo, P' s mo -> P s mo) -> mspecN P' m Q.
Proof. intros Hm HP. eapply mspecN_conseq; eauto. Qed.

Lemma mspecN_post {A} (m : M St A) (P : assn St) (Q Q' : A -> assn St) :
  mspecN P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecN P m Q'.
Proof. intros Hm HQ. eapply mspecN_conseq; eauto. Qed.

Lemma mspecN_munr {A} (Q : A -> assn St) : mspecN (fun _ _ => False) munr Q.
Proof. intros s mo []. Qed.

Lemma mspecN_cho (P : assn St) : mspecN P mcho (fun _ s mo => P s mo).
Proof. apply mspec_N, mspec_cho. Qed.

Lemma mspecN_chok {B} (k : Z -> M St B) (P : assn St) (Q : B -> assn St) :
  (forall z, mspecN P (k z) Q) -> mspecN P (mbind mcho k) Q.
Proof. intros H s mo HP. rewrite mbind_mcho. intros z. exact (H z s mo HP). Qed.

Lemma mspecN_false {A} (m : M St A) (Q : A -> assn St) : mspecN (fun _ _ => False) m Q.
Proof. intros s mo []. Qed.

Lemma mspecN_get (P : assn St) : mspecN P mget (fun s' s mo => s' = s /\ P s mo).
Proof. apply mspec_N, mspec_get. Qed.

Lemma mspecN_put (P : assn St) (s1 : St) : mspecN P (mput s1) (fun _ s mo => s = s1 /\ exists s0, P s0 mo).
Proof. apply mspec_N, mspec_put. Qed.

Lemma mspecN_upd (P : assn St) (f : St -> St) : mspecN P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof. apply mspec_N, mspec_upd. Qed.

Lemma mspecN_upd' (P : assn St) (Q : unit -> assn St) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspecN P (mupd f) Q.
Proof. intros H. apply mspec_N, mspec_upd'. exact H. Qed.

Lemma mspecN_sys {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo ->
     nsafe n mo /\
     forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
  mspecN P (msys n dec) Q.
Proof. intros H. apply mspec_N, mspec_sys. exact H. Qed.

Lemma mspecN_if {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  (b = true -> mspecN P m1 Q) -> (b = false -> mspecN P m2 Q) -> mspecN P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

Lemma mspecN_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  mspecN (fun s mo => P s mo /\ b = true) m1 Q -> mspecN (fun s mo => P s mo /\ b = false) m2 Q ->
  mspecN P (if b then m1 else m2) Q.
Proof. intros H1 H2 s mo HP. destruct b; [apply H1|apply H2]; auto. Qed.

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

Lemma mspecN_when (b : bool) (m : M St unit) (P : assn St) (Q : unit -> assn St) :
  (b = true -> mspecN P m Q) -> (b = false -> forall s mo, P s mo -> Q tt s mo) -> mspecN P (mwhen b m) Q.
Proof. intros H1 H2. unfold mwhen. destruct b; [apply H1; reflexivity|]. apply mspecN_ret. apply H2. reflexivity. Qed.

Lemma mspecN_loop {X R} (body : X -> M St (X + R)) (I : X -> assn St) (Q : R -> assn St) (meas : X -> nat) :
  (forall x, mspecN (I x) (body x)
     (fun r s mo => match r with
                    | inl x' => I x' s mo /\ (meas x' < meas x)%nat
                    | inr v => Q v s mo
                    end)) ->
  forall fuel x, (meas x < fuel)%nat -> mspecN (I x) (mloop fuel body x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x Hf; [lia|].
  cbn [mloop]. eapply mspecN_bind; [apply Hb|].
  intros [x'|v]; cbn.
  - intros s mo [HI Hm]. apply (IH x'); [lia| exact HI].
  - apply mspecN_ret. auto.
Qed.

Lemma mspecN_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn St) (Q : B -> assn St) :
  mspecN P m (fun _ => R) -> (forall a, mspecN R (f a) Q) -> mspecN P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspecN_bind; [exact Hm|]. intros a. apply Hf. Qed.

Lemma mspecN_program {A} (P : assn St) (m : M St A) s mo :
  mspecN P m (fun _ _ _ => False) -> P s mo ->
  forall {B} (f : A * St -> itree node (exc B)),
  tsafe nstep node_noerrN (ebind (m s) f) mo ->
  leaves_unreachable_m nstep (ebind (m s) f) mo /\ tsafe nstep nsafe (ebind (m s) f) mo.
Proof.
  intros Hm HP B f HN. apply etwfN_leaves; [| exact HN]. apply etwfN_ebind.
  eapply etwfN_mono; [exact (Hm s mo HP)|]. intros [a s'] mo' [].
Qed.

End MSpecN.

Arguments mspecN {St A} P m Q.
