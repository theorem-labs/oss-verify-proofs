(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Monad.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge TSim.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ClfIx Require Import PathX.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import TSimS.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation tsh := (tshape node nstep nexit) (only parsing).
Local Notation SIM := (stsim nstep nexit nstep nexit) (only parsing).
Local Notation stwfN := (stwf node nstep nexit nsafe) (only parsing).

Lemma stsim_left_stwf {RA RB SA : Type} : forall (L : SA -> Model -> RB -> Model -> Prop)
    (t : itree node RA) (kA : RA -> itree node SA) (Q : RA -> Model -> Prop) moA (tB : itree node RB) moB,
  stwfN t moA Q ->
  (forall r moA', Q r moA' -> SIM L (kA r) moA' tB moB) ->
  SIM L (ITree.bind node t kA) moA tB moB.
Proof.
  intros L t. induction t as [r | n k IH]; intros kA Q moA tB moB HW HK; cbn [ITree.bind]; cbn in HW.
  - apply HK. exact HW.
  - destruct HW as (Hs & NX & HC). apply ss_left.
    + split; [| exact NX]. intros rsp mo' evs ST. exact (proj1 (HC _ _ _ ST)).
    + intros rspA moA' evs ST. destruct (HC _ _ _ ST) as [-> HW']. eapply IH; [exact HW'| exact HK].
Qed.

Lemma stsim_right_path {RA RB SB : Type} : forall (L : RA -> Model -> SB -> Model -> Prop)
    (tA : itree node RA) moA (t : itree node RB) (kB : RB -> itree node SB) (Q : RB -> Model -> Prop) moB r moB',
  stwfN t moB Q -> tpaths t moB [] r moB' ->
  SIM L tA moA (kB r) moB' ->
  SIM L tA moA (ITree.bind node t kB) moB.
Proof.
  intros L tA moA t. induction t as [r0 | n k IH]; intros kB Q moB r moB' HW HP HS; cbn [ITree.bind]; cbn in HW, HP.
  - destruct HP as (-> & -> & _). exact HS.
  - destruct HW as (Hs & NX & HC). destruct HP as (_ & _ & rsp & mo1 & evs & tr' & ST & HP' & E).
    destruct (HC _ _ _ ST) as [-> HW']. cbn in E. subst tr'.
    eapply ss_right; [split; [intros rsp' mo' evs' ST'; exact (proj1 (HC _ _ _ ST'))| exact NX] | exact ST|].
    eapply IH; [exact HW'| exact HP'| exact HS].
Qed.

Lemma stsim_left_stwf_ret {RA RB : Type} : forall (L : RA -> Model -> RB -> Model -> Prop)
    (t : itree node RA) (Q : RA -> Model -> Prop) moA (rB : RB) moB,
  stwfN t moA Q -> (forall r moA', Q r moA' -> L r moA' rB moB) -> SIM L t moA (Ret rB) moB.
Proof.
  intros L t. induction t as [r | n k IH]; intros Q moA rB moB HW HK; cbn in HW.
  - apply ss_ret. apply HK. exact HW.
  - destruct HW as (Hs & NX & HC). apply ss_left.
    + split; [| exact NX]. intros rsp mo' evs ST. exact (proj1 (HC _ _ _ ST)).
    + intros rspA moA' evs ST. destruct (HC _ _ _ ST) as [-> HW']. eapply IH; [exact HW'| exact HK].
Qed.

Lemma stsim_right_path_ret {RA RB : Type} : forall (L : RA -> Model -> RB -> Model -> Prop)
    (rA : RA) moA (t : itree node RB) (Q : RB -> Model -> Prop) moB r moB',
  stwfN t moB Q -> tpaths t moB [] r moB' -> L rA moA r moB' -> SIM L (Ret rA) moA t moB.
Proof.
  intros L rA moA t. induction t as [r0 | n k IH]; intros Q moB r moB' HW HP HL; cbn in HW, HP.
  - destruct HP as (-> & -> & _). apply ss_ret. exact HL.
  - destruct HW as (Hs & NX & HC). destruct HP as (_ & _ & rsp & mo1 & evs & tr' & ST & HP' & E).
    destruct (HC _ _ _ ST) as [-> HW']. cbn in E. subst tr'.
    eapply ss_right; [split; [intros rsp' mo' evs' ST'; exact (proj1 (HC _ _ _ ST'))| exact NX] | exact ST|].
    eapply IH; [exact HW'| exact HP'| exact HL].
Qed.

Section MSimS.
  Context {StA StB : Type}.

  Definition rel : Type := StA -> Model -> StB -> Model -> Prop.

  Definition leafQ {A B} (Q : A -> B -> rel) : exc (A * StA) -> Model -> exc (B * StB) -> Model -> Prop :=
    fun xA moA xB moB => match xA, xB with
                         | Ok pA, Ok pB => Q (fst pA) (fst pB) (snd pA) moA (snd pB) moB
                         | Unr, Unr => True
                         | _, _ => False
                         end.

  Definition msimS {A B} (R : rel) (cA : M StA A) (cB : M StB B) (Q : A -> B -> rel) : Prop :=
    forall sA moA sB moB, R sA moA sB moB -> SIM (leafQ Q) (cA sA) moA (cB sB) moB.

  #[using="Type"] Lemma msimS_conseq {A B} (R R' : rel) (cA : M StA A) (cB : M StB B) (Q Q' : A -> B -> rel) :
    msimS R cA cB Q -> (forall sA moA sB moB, R' sA moA sB moB -> R sA moA sB moB) ->
    (forall a b sA moA sB moB, Q a b sA moA sB moB -> Q' a b sA moA sB moB) -> msimS R' cA cB Q'.
  Proof.
    intros H HR HQ sA moA sB moB HR'. eapply stsim_mono; [exact (H _ _ _ _ (HR _ _ _ _ HR'))|].
    intros [|[a sA']] moA' [|[b sB']] moB'; cbn; auto.
  Qed.
  #[using="Type"] Lemma msimS_pre {A B} (R R' : rel) (cA : M StA A) (cB : M StB B) (Q : A -> B -> rel) :
    msimS R cA cB Q -> (forall sA moA sB moB, R' sA moA sB moB -> R sA moA sB moB) -> msimS R' cA cB Q.
  Proof. intros H HR. eapply msimS_conseq; eauto. Qed.
  #[using="Type"] Lemma msimS_post {A B} (R : rel) (cA : M StA A) (cB : M StB B) (Q Q' : A -> B -> rel) :
    msimS R cA cB Q -> (forall a b sA moA sB moB, Q a b sA moA sB moB -> Q' a b sA moA sB moB) -> msimS R cA cB Q'.
  Proof. intros H HQ. eapply msimS_conseq; eauto. Qed.

  #[using="Type"] Lemma msimS_ret {A B} (R : rel) (a : A) (b : B) (Q : A -> B -> rel) :
    (forall sA moA sB moB, R sA moA sB moB -> Q a b sA moA sB moB) -> msimS R (mret a) (mret b) Q.
  Proof. intros H sA moA sB moB HR. unfold mret. apply ss_ret. apply H. exact HR. Qed.

  #[using="Type"] Lemma msimS_munr {A B} (R : rel) (Q : A -> B -> rel) : msimS R (munr (A:=A)) (munr (A:=B)) Q.
  Proof. intros sA moA sB moB _. unfold munr. apply ss_ret. exact I. Qed.

  #[using="Type"] Lemma msimS_false {A B} (cA : M StA A) (cB : M StB B) (Q : A -> B -> rel) : msimS (fun _ _ _ _ => False) cA cB Q.
  Proof. intros sA moA sB moB []. Qed.

  #[using="Type"] Lemma msimS_get (R : rel) : msimS R mget mget (fun a b sA moA sB moB => a = sA /\ b = sB /\ R sA moA sB moB).
  Proof. intros sA moA sB moB HR. unfold mget. apply ss_ret. cbn. auto. Qed.

  #[using="Type"] Lemma msimS_upd (R : rel) (fA : StA -> StA) (fB : StB -> StB) (Q : unit -> unit -> rel) :
    (forall sA moA sB moB, R sA moA sB moB -> Q tt tt (fA sA) moA (fB sB) moB) -> msimS R (mupd fA) (mupd fB) Q.
  Proof. intros H sA moA sB moB HR. unfold mupd. apply ss_ret. apply H. exact HR. Qed.

  #[using="Type"] Lemma msimS_bind {A B A' B'} (R : rel) (cA : M StA A) (cB : M StB B) (Q1 : A -> B -> rel)
        (kA : A -> M StA A') (kB : B -> M StB B') (Q : A' -> B' -> rel) :
    msimS R cA cB Q1 -> (forall a b, msimS (Q1 a b) (kA a) (kB b) Q) -> msimS R (mbind cA kA) (mbind cB kB) Q.
  Proof.
    intros H1 H2 sA moA sB moB HR. unfold mbind, ebind.
    eapply stsim_bind; [exact (H1 _ _ _ _ HR)|].
    intros [|[a sA']] moA' [|[b sB']] moB' HQ; cbn in HQ; [apply ss_ret; exact I| destruct HQ| destruct HQ|].
    cbn [fst snd]. apply (H2 a b). exact HQ.
  Qed.

  #[using="Type"] Lemma msimS_seq {A B A' B'} (R R1 : rel) (cA : M StA A) (cB : M StB B) (kA : A -> M StA A') (kB : B -> M StB B') (Q : A' -> B' -> rel) :
    msimS R cA cB (fun _ _ => R1) -> (forall a b, msimS R1 (kA a) (kB b) Q) -> msimS R (mbind cA kA) (mbind cB kB) Q.
  Proof. intros H1 H2. eapply msimS_bind; [exact H1| exact H2]. Qed.

  #[using="Type"] Lemma msimS_bind_eq {A A' B'} (R : rel) (cA : M StA A) (cB : M StB A) (R1 : A -> rel)
        (kA : A -> M StA A') (kB : A -> M StB B') (Q : A' -> B' -> rel) :
    msimS R cA cB (fun a b sA moA sB moB => a = b /\ R1 a sA moA sB moB) ->
    (forall a, msimS (R1 a) (kA a) (kB a) Q) -> msimS R (mbind cA kA) (mbind cB kB) Q.
  Proof. intros H1 H2. eapply msimS_bind; [exact H1|]. intros a b sA moA sB moB [<- HR]. apply (H2 a). exact HR. Qed.

  #[using="Type"] Lemma msimS_if {A B} (b : bool) (c1A c2A : M StA A) (c1B c2B : M StB B) (R : rel) Q :
    (b = true -> msimS R c1A c1B Q) -> (b = false -> msimS R c2A c2B Q) ->
    msimS R (if b then c1A else c2A) (if b then c1B else c2B) Q.
  Proof. intros H1 H2. destruct b; auto. Qed.

  #[using="Type"] Lemma msimS_exI {A B X} (P : X -> rel) (cA : M StA A) (cB : M StB B) Q :
    (forall x, msimS (P x) cA cB Q) -> msimS (fun sA moA sB moB => exists x, P x sA moA sB moB) cA cB Q.
  Proof. intros H sA moA sB moB [x HP]. exact (H x _ _ _ _ HP). Qed.

  #[using="Type"] Lemma msimS_expose {A B} (R : rel) (phi : Prop) (cA : M StA A) (cB : M StB B) Q :
    (forall sA moA sB moB, R sA moA sB moB -> phi) -> (phi -> msimS R cA cB Q) -> msimS R cA cB Q.
  Proof. intros H1 H2 sA moA sB moB HR. exact (H2 (H1 _ _ _ _ HR) _ _ _ _ HR). Qed.

  #[using="Type"] Lemma msimS_loop {XA XB A B} (bodyA : XA -> M StA (XA + A)) (bodyB : XB -> M StB (XB + B)) (I : XA -> XB -> rel) (Q : A -> B -> rel) :
    (forall xA xB, msimS (I xA xB) (bodyA xA) (bodyB xB)
       (fun rA rB sA moA sB moB => match rA, rB with
                                  | inl xA', inl xB' => I xA' xB' sA moA sB moB
                                  | inr a, inr b => Q a b sA moA sB moB
                                  | _, _ => False
                                  end)) ->
    forall fuel xA xB, msimS (I xA xB) (mloop fuel bodyA xA) (mloop fuel bodyB xB) Q.
  Proof.
    intros HB fuel. induction fuel as [|fuel IH]; intros xA xB; cbn [mloop]; [apply msimS_munr|].
    eapply msimS_bind; [apply HB|]. intros [xA'|a] [xB'|b]; cbn beta iota.
    - apply IH.
    - apply msimS_false.
    - apply msimS_false.
    - apply msimS_ret. auto.
  Qed.

  #[using="Type"] Lemma msimS_sys {A B} (nA nB : node) (decA : resp -> option A) (decB : resp -> option B) (R : rel) (Q : A -> B -> rel) :
    (forall sA moA sB moB, R sA moA sB moB ->
       (forall rspA moA' evs, nstep nA moA rspA moA' evs -> exists rspB moB', nstep nB moB rspB moB' evs /\
           match decA rspA, decB rspB with
           | Some a, Some b => Q a b sA moA' sB moB'
           | None, None => True
           | _, _ => False
           end)
       /\ (forall code moA', nexit nA moA code moA' -> exists moB', nexit nB moB code moB' /\ m_fs moB' = m_fs moA')) ->
    msimS R (msys nA decA) (msys nB decB) Q.
  Proof.
    intros H sA moA sB moB HR. destruct (H _ _ _ _ HR) as (F & XF). unfold msys, enode.
    apply ss_match; [| exact XF].
    intros rspA moA' evs ST. destruct (F _ _ _ ST) as (rspB & moB' & STB & HQ). exists rspB, moB'. split; [exact STB|].
    destruct (decA rspA), (decB rspB); apply ss_ret; cbn; [exact HQ| destruct HQ| destruct HQ| exact I].
  Qed.

  #[using="Type"] Lemma msimS_left {A A' B'} (R : rel) (cA : M StA A) (QA : A -> rel) (kA : A -> M StA A') (cB : M StB B') (Q : A' -> B' -> rel) :
    (forall sA moA sB moB, R sA moA sB moB ->
       stwfN (cA sA) moA (fun r moA' => exists a sA', r = Ok (a, sA') /\ QA a sA' moA' sB moB)) ->
    (forall a, msimS (QA a) (kA a) cB Q) ->
    msimS R (mbind cA kA) cB Q.
  Proof.
    intros HW HK sA moA sB moB HR. unfold mbind, ebind.
    eapply stsim_left_stwf; [exact (HW _ _ _ _ HR)|].
    intros [|[a sA']] moA' HQ; [destruct HQ as (? & ? & E & _); discriminate E|].
    destruct HQ as (a0 & sA0 & E & HQA). injection E as -> ->. cbn [fst snd]. apply (HK a0). exact HQA.
  Qed.

  #[using="Type"] Lemma msimS_right {A' B B'} (R : rel) (cA : M StA A') (cB : M StB B) (QB : B -> rel) (kB : B -> M StB B') (Q : A' -> B' -> rel) :
    (forall sA moA sB moB, R sA moA sB moB ->
       exists (W : exc (B * StB) -> Model -> Prop) b sB' moB',
         stwfN (cB sB) moB W /\ tpaths (cB sB) moB [] (Ok (b, sB')) moB' /\ QB b sA moA sB' moB') ->
    (forall b, msimS (QB b) cA (kB b) Q) ->
    msimS R cA (mbind cB kB) Q.
  Proof.
    intros HP HK sA moA sB moB HR. unfold mbind, ebind.
    destruct (HP _ _ _ _ HR) as (W & b & sB' & moB' & HW & HT & HQB).
    eapply stsim_right_path; [exact HW| exact HT|]. cbn [fst snd]. apply (HK b). exact HQB.
  Qed.

  #[using="Type"] Lemma msimS_left_ret {A B} (R : rel) (cA : M StA A) (b : B) (Q : A -> B -> rel) :
    (forall sA moA sB moB, R sA moA sB moB ->
       stwfN (cA sA) moA (fun r moA' => exists a sA', r = Ok (a, sA') /\ Q a b sA' moA' sB moB)) ->
    msimS R cA (mret b) Q.
  Proof.
    intros HW sA moA sB moB HR. unfold mret. eapply stsim_left_stwf_ret; [exact (HW _ _ _ _ HR)|].
    intros [|[a sA']] moA' HQ; [destruct HQ as (? & ? & E & _); discriminate E|].
    destruct HQ as (a0 & sA0 & E & HQA). injection E as -> ->. exact HQA.
  Qed.

  #[using="Type"] Lemma msimS_right_ret {A B} (R : rel) (a : A) (cB : M StB B) (Q : A -> B -> rel) :
    (forall sA moA sB moB, R sA moA sB moB ->
       exists (W : exc (B * StB) -> Model -> Prop) b sB' moB',
         stwfN (cB sB) moB W /\ tpaths (cB sB) moB [] (Ok (b, sB')) moB' /\ Q a b sA moA sB' moB') ->
    msimS R (mret a) cB Q.
  Proof.
    intros HP sA moA sB moB HR. unfold mret. destruct (HP _ _ _ _ HR) as (W & b & sB' & moB' & HW & HT & HQB).
    eapply stsim_right_path_ret; [exact HW| exact HT| exact HQB].
  Qed.

  #[using="Type"] Theorem msimS_tshape {A B} (R : rel) (cA : M StA A) (cB : M StB B) (Q : A -> B -> rel)
      (KA : exc (A * StA) -> Model -> TSet) (KB : exc (B * StB) -> Model -> TSet) sA moA sB moB :
    msimS R cA cB Q -> R sA moA sB moB ->
    (forall a sA' moA' b sB' moB', Q a b sA' moA' sB' moB' -> t_incl0 (KA (Ok (a, sA')) moA') (KB (Ok (b, sB')) moB')) ->
    (forall moA' moB', t_incl0 (KA Unr moA') (KB Unr moB')) ->
    t_incl0 (tsh (cA sA) moA KA) (tsh (cB sB) moB KB).
  Proof.
    intros H HR HK HU. eapply stsim_tshape; [exact (H _ _ _ _ HR)|].
    intros [|[a sA']] moA' [|[b sB']] moB'; cbn; intros HQ; [apply HU| destruct HQ| destruct HQ| apply HK; exact HQ].
  Qed.
End MSimS.
Arguments rel StA StB : clear implicits.
