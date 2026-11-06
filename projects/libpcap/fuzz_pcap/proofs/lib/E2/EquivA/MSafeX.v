(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Monad MSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section GhostSafety.
Context {G : Type}.
Variable nsafeX : node -> G -> Model -> Prop.
Variable gstep : node -> resp -> G -> G.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint twfX {R} (t : itree node R) (g : G) (mo : Model) (P : R -> G -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r g mo
  | Vis n k => nsafeX n g mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> twfX (k rsp) (gstep n rsp g) mo' P
  end.

#[using="Type"] Lemma twfX_mono : forall {R} (t : itree node R) g mo (P P' : R -> G -> Model -> Prop),
  twfX t g mo P -> (forall r g1 mo1, P r g1 mo1 -> P' r g1 mo1) -> twfX t g mo P'.
Proof.
  intros R t. induction t as [r|n k IH]; intros g mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; eauto.
Qed.

#[using="Type"] Lemma twfX_bind : forall {A B} (t : itree node A) (f : A -> itree node B) g mo (P : B -> G -> Model -> Prop),
  twfX t g mo (fun a g1 mo1 => twfX (f a) g1 mo1 P) -> twfX (ITree.bind node t f) g mo P.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f g mo P H; cbn in *.
  - exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
Qed.

(* [comment removed for export] *)
Fixpoint grun {R} (rsps : list resp) (t : itree node R) (g : G) : option G :=
  match rsps with
  | [] => match t with Ret _ => Some g | Vis _ _ => None end
  | rsp :: rsps' => match t with Ret _ => None | Vis n k => grun rsps' (k rsp) (gstep n rsp g) end
  end.

#[using="Type"] Lemma twfX_tpath : forall {R} (t : itree node R) g mo P tr r mo',
  twfX t g mo P -> tpath nstep t mo tr r mo' -> exists g', P r g' mo'.
Proof.
  intros R t. induction t as [r0|n k IH]; intros g mo P tr r mo' H Hp; cbn in *.
  - destruct Hp as (<- & -> & ->). exists g. exact H.
  - destruct H as [_ Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    eapply IH; [eapply Hk; exact Hst| exact Hp].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twfX_tpath_run : forall {R} (t : itree node R) g mo P tr r mo',
  twfX t g mo P -> tpath nstep t mo tr r mo' -> exists rsps g', grun rsps t g = Some g' /\ P r g' mo'.
Proof.
  intros R t. induction t as [r0|n k IH]; intros g mo P tr r mo' H Hp; cbn in *.
  - destruct Hp as (<- & -> & ->). exists [], g. split; [reflexivity| exact H].
  - destruct H as [_ Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    destruct (IH rsp (gstep n rsp g) mo1 P tr' r mo' (Hk _ _ _ Hst) Hp) as (rsps & g' & Hr & HP).
    exists (rsp :: rsps), g'. split; [exact Hr| exact HP].
Qed.

(* [comment removed for export] *)
Definition etwfX {A} (t : itree node (exc A)) (g : G) (mo : Model) (Q : A -> G -> Model -> Prop) : Prop :=
  twfX t g mo (fun r g1 mo1 => match r with Unr => False | Ok a => Q a g1 mo1 end).

#[using="Type"] Lemma etwfX_mono : forall {A} (t : itree node (exc A)) g mo (Q Q' : A -> G -> Model -> Prop),
  etwfX t g mo Q -> (forall a g1 mo1, Q a g1 mo1 -> Q' a g1 mo1) -> etwfX t g mo Q'.
Proof.
  intros A t g mo Q Q' H HQ. unfold etwfX in *. eapply twfX_mono; [exact H|].
  intros [|a] g1 mo1; cbn; auto.
Qed.

#[using="Type"] Lemma etwfX_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) g mo Q,
  etwfX t g mo (fun a g1 mo1 => etwfX (f a) g1 mo1 Q) -> etwfX (ebind t f) g mo Q.
Proof.
  intros A B t f g mo Q H. unfold etwfX, ebind in *. apply twfX_bind.
  eapply twfX_mono; [exact H|]. intros [|a] g1 mo1 HQ; cbn; [|exact HQ]. exact HQ.
Qed.

#[using="Type"] Lemma etwfX_ret : forall {A} (a : A) g mo (Q : A -> G -> Model -> Prop), Q a g mo -> etwfX (Ret (Ok a)) g mo Q.
Proof. intros A a g mo Q H. exact H. Qed.

#[using="Type"] Lemma etwfX_enode : forall {A} n (pl : resp -> option A) g mo (Q : A -> G -> Model -> Prop),
  nsafeX n g mo ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, pl rsp = Some a /\ Q a (gstep n rsp g) mo') ->
  etwfX (enode n pl) g mo Q.
Proof.
  intros A n pl g mo Q Hs Hk. unfold etwfX, enode. cbn. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

(* [comment removed for export] *)
Fixpoint gfree {R} (ok : node -> Prop) (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => ok n /\ forall rsp, gfree ok (k rsp)
  end.

#[using="Type"] Lemma twfX_of_twf : forall (ok : node -> Prop),
  (forall n g mo, ok n -> nsafe n mo -> nsafeX n g mo) ->
  forall {R} (t : itree node R) g mo (P : R -> Model -> Prop),
  gfree ok t -> twf t mo P -> twfX t g mo (fun r _ mo1 => P r mo1).
Proof.
  intros ok Hok R t. induction t as [r|n k IH]; intros g mo P Hgf H; cbn in *.
  - exact H.
  - destruct Hgf as [Hn Hk']. destruct H as [Hs Hk]. split; [apply Hok; assumption|].
    intros rsp mo' evs Hst. apply IH; [apply Hk'| eapply Hk; exact Hst].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSpecX.
Context {St : Type}.

Definition assnX : Type := St -> G -> Model -> Prop.

Definition mspecX {A} (P : assnX) (m : M St A) (Q : A -> assnX) : Prop :=
  forall s g mo, P s g mo -> etwfX (m s) g mo (fun p g' mo' => Q (fst p) (snd p) g' mo').

#[using="Type"] Lemma mspecX_ret {A} (a : A) (P : assnX) (Q : A -> assnX) :
  (forall s g mo, P s g mo -> Q a s g mo) -> mspecX P (mret a) Q.
Proof. intros H s g mo HP. cbn. apply H. exact HP. Qed.

#[using="Type"] Lemma mspecX_bind {A B} (m : M St A) (f : A -> M St B) (P : assnX) (Q1 : A -> assnX) (Q : B -> assnX) :
  mspecX P m Q1 -> (forall a, mspecX (Q1 a) (f a) Q) -> mspecX P (mbind m f) Q.
Proof.
  intros Hm Hf s g mo HP. unfold mbind. apply etwfX_ebind.
  eapply etwfX_mono; [exact (Hm s g mo HP)|]. intros [a s1] g1 mo1 H1. cbn in *. exact (Hf a s1 g1 mo1 H1).
Qed.

#[using="Type"] Lemma mspecX_conseq {A} (m : M St A) (P P' : assnX) (Q Q' : A -> assnX) :
  mspecX P m Q -> (forall s g mo, P' s g mo -> P s g mo) -> (forall a s g mo, Q a s g mo -> Q' a s g mo) -> mspecX P' m Q'.
Proof.
  intros Hm HP HQ s g mo HP'. eapply etwfX_mono; [exact (Hm s g mo (HP _ _ _ HP'))|].
  intros [a s1] g1 mo1; cbn; auto.
Qed.

#[using="Type"] Lemma mspecX_pre {A} (m : M St A) (P P' : assnX) (Q : A -> assnX) :
  mspecX P m Q -> (forall s g mo, P' s g mo -> P s g mo) -> mspecX P' m Q.
Proof. intros Hm HP. eapply mspecX_conseq; eauto. Qed.

#[using="Type"] Lemma mspecX_post {A} (m : M St A) (P : assnX) (Q Q' : A -> assnX) :
  mspecX P m Q -> (forall a s g mo, Q a s g mo -> Q' a s g mo) -> mspecX P m Q'.
Proof. intros Hm HQ. eapply mspecX_conseq; eauto. Qed.

#[using="Type"] Lemma mspecX_munr {A} (Q : A -> assnX) : mspecX (fun _ _ _ => False) munr Q.
Proof. intros s g mo []. Qed.

#[using="Type"] Lemma mspecX_false {A} (m : M St A) (Q : A -> assnX) : mspecX (fun _ _ _ => False) m Q.
Proof. intros s g mo []. Qed.

#[using="Type"] Lemma mspecX_get (P : assnX) : mspecX P mget (fun s' s g mo => s' = s /\ P s g mo).
Proof. intros s g mo HP. cbn. auto. Qed.

#[using="Type"] Lemma mspecX_put (P : assnX) (s1 : St) : mspecX P (mput s1) (fun _ s g mo => s = s1 /\ exists s0, P s0 g mo).
Proof. intros s g mo HP. cbn. eauto. Qed.

#[using="Type"] Lemma mspecX_upd (P : assnX) (f : St -> St) : mspecX P (mupd f) (fun _ s g mo => exists s0, s = f s0 /\ P s0 g mo).
Proof. intros s g mo HP. cbn. eauto. Qed.

#[using="Type"] Lemma mspecX_upd' (P : assnX) (Q : unit -> assnX) (f : St -> St) :
  (forall s g mo, P s g mo -> Q tt (f s) g mo) -> mspecX P (mupd f) Q.
Proof. intros H s g mo HP. cbn. apply H. exact HP. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mspecX_sys {A} (n : node) (dec : resp -> option A) (P : assnX) (Q : A -> assnX) :
  (forall s g mo, P s g mo ->
     nsafeX n g mo /\
     forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s (gstep n rsp g) mo') ->
  mspecX P (msys n dec) Q.
Proof.
  intros H s g mo HP. destruct (H s g mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

#[using="Type"] Lemma mspecX_if {A} (b : bool) (m1 m2 : M St A) (P : assnX) Q :
  (b = true -> mspecX P m1 Q) -> (b = false -> mspecX P m2 Q) -> mspecX P (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

#[using="Type"] Lemma mspecX_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assnX) Q :
  mspecX (fun s g mo => P s g mo /\ b = true) m1 Q -> mspecX (fun s g mo => P s g mo /\ b = false) m2 Q ->
  mspecX P (if b then m1 else m2) Q.
Proof. intros H1 H2 s g mo HP. destruct b; [apply H1|apply H2]; auto. Qed.

#[using="Type"] Lemma mspecX_exI {A X} (P : X -> assnX) (m : M St A) (Q : A -> assnX) :
  (forall x, mspecX (P x) m Q) -> mspecX (fun s g mo => exists x, P x s g mo) m Q.
Proof. intros H s g mo [x HP]. exact (H x s g mo HP). Qed.

#[using="Type"] Lemma mspecX_pure {A} (P : assnX) (phi : Prop) (m : M St A) (Q : A -> assnX) :
  (phi -> mspecX P m Q) -> mspecX (fun s g mo => P s g mo /\ phi) m Q.
Proof. intros H s g mo [HP Hphi]. exact (H Hphi s g mo HP). Qed.

#[using="Type"] Lemma mspecX_pure_l {A} (P : assnX) (phi : Prop) (m : M St A) (Q : A -> assnX) :
  (phi -> mspecX P m Q) -> mspecX (fun s g mo => phi /\ P s g mo) m Q.
Proof. intros H s g mo [Hphi HP]. exact (H Hphi s g mo HP). Qed.

#[using="Type"] Lemma mspecX_pointwise {A} (P : assnX) (m : M St A) (Q : A -> assnX) :
  (forall s g mo, P s g mo -> mspecX (fun s' g' mo' => s' = s /\ g' = g /\ mo' = mo) m Q) -> mspecX P m Q.
Proof. intros H s g mo HP. apply (H s g mo HP). auto. Qed.

#[using="Type"] Lemma mspecX_when (b : bool) (m : M St unit) (P : assnX) (Q : unit -> assnX) :
  (b = true -> mspecX P m Q) -> (b = false -> forall s g mo, P s g mo -> Q tt s g mo) -> mspecX P (mwhen b m) Q.
Proof. intros H1 H2. unfold mwhen. destruct b; [apply H1; reflexivity|]. apply mspecX_ret. apply H2. reflexivity. Qed.

#[using="Type"] Lemma mspecX_loop {X R} (body : X -> M St (X + R)) (I : X -> assnX) (Q : R -> assnX) (meas : X -> nat) :
  (forall x, mspecX (I x) (body x)
     (fun r s g mo => match r with
                      | inl x' => I x' s g mo /\ (meas x' < meas x)%nat
                      | inr v => Q v s g mo
                      end)) ->
  forall fuel x, (meas x < fuel)%nat -> mspecX (I x) (mloop fuel body x) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x Hf; [lia|].
  cbn [mloop]. eapply mspecX_bind; [apply Hb|].
  intros [x'|v]; cbn.
  - intros s g mo [HI Hm]. apply (IH x'); [lia| exact HI].
  - apply mspecX_ret. auto.
Qed.

#[using="Type"] Lemma mspecX_seq {A B} (m : M St A) (f : A -> M St B) (P R : assnX) (Q : B -> assnX) :
  mspecX P m (fun _ => R) -> (forall a, mspecX R (f a) Q) -> mspecX P (mbind m f) Q.
Proof. intros Hm Hf. eapply mspecX_bind; [exact Hm|]. intros a. apply Hf. Qed.

(* [comment removed for export] *)
Definition mgfree {A} (ok : node -> Prop) (m : M St A) : Prop := forall s, gfree ok (m s).

#[using="Type"] Lemma mspecX_of_mspec {A} (ok : node -> Prop) (m : M St A) (P : @assn St) (Q : A -> @assn St) :
  (forall n g mo, ok n -> nsafe n mo -> nsafeX n g mo) ->
  mgfree ok m -> mspec P m Q ->
  mspecX (fun s _ mo => P s mo) m (fun a s _ mo => Q a s mo).
Proof.
  intros Hok Hgf Hm s g mo HP. unfold etwfX.
  pose proof (twfX_of_twf ok Hok (m s) g mo _ (Hgf s) (Hm s mo HP)) as H.
  eapply twfX_mono; [exact H|]. intros [|[a s1]] g1 mo1; cbn; auto.
Qed.

End MSpecX.
End GhostSafety.

Arguments twfX {G} nsafeX gstep {R} t g mo P.
Arguments etwfX {G} nsafeX gstep {A} t g mo Q.
Arguments mspecX {G} nsafeX gstep {St A} P m Q.
