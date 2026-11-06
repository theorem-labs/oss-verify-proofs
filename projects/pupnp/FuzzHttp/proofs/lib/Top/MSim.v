(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Monad.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge TSim.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Notation tsh := (tshape node nstep nexit).

Section MSim.
  Context {StA StB : Type}.

  Definition rel : Type := StA -> Model -> StB -> Model -> Prop.

  Definition leafQ {A B} (Q : A -> B -> rel) : exc (A * StA) -> Model -> exc (B * StB) -> Model -> Prop :=
    fun xA moA xB moB => match xA, xB with
                         | Ok pA, Ok pB => Q (fst pA) (fst pB) (snd pA) moA (snd pB) moB
                         | Unr, Unr => True
                         | _, _ => False
                         end.

  Definition msim {A B} (R : rel) (cA : M StA A) (cB : M StB B) (Q : A -> B -> rel) : Prop :=
    forall sA moA sB moB, R sA moA sB moB -> tsim (leafQ Q) (cA sA) moA (cB sB) moB.

  #[using="Type"] Lemma msim_conseq {A B} (R R' : rel) (cA : M StA A) (cB : M StB B) (Q Q' : A -> B -> rel) :
    msim R cA cB Q -> (forall sA moA sB moB, R' sA moA sB moB -> R sA moA sB moB) ->
    (forall a b sA moA sB moB, Q a b sA moA sB moB -> Q' a b sA moA sB moB) -> msim R' cA cB Q'.
  Proof.
    intros H HR HQ sA moA sB moB HR'. eapply tsim_mono; [exact (H _ _ _ _ (HR _ _ _ _ HR'))|].
    intros [|[a sA']] moA' [|[b sB']] moB'; cbn; auto.
  Qed.
  #[using="Type"] Lemma msim_pre {A B} (R R' : rel) (cA : M StA A) (cB : M StB B) (Q : A -> B -> rel) :
    msim R cA cB Q -> (forall sA moA sB moB, R' sA moA sB moB -> R sA moA sB moB) -> msim R' cA cB Q.
  Proof. intros H HR. eapply msim_conseq; eauto. Qed.
  #[using="Type"] Lemma msim_post {A B} (R : rel) (cA : M StA A) (cB : M StB B) (Q Q' : A -> B -> rel) :
    msim R cA cB Q -> (forall a b sA moA sB moB, Q a b sA moA sB moB -> Q' a b sA moA sB moB) -> msim R cA cB Q'.
  Proof. intros H HQ. eapply msim_conseq; eauto. Qed.

  #[using="Type"] Lemma msim_ret {A B} (R : rel) (a : A) (b : B) (Q : A -> B -> rel) :
    (forall sA moA sB moB, R sA moA sB moB -> Q a b sA moA sB moB) -> msim R (mret a) (mret b) Q.
  Proof. intros H sA moA sB moB HR. cbn. apply H. exact HR. Qed.

  #[using="Type"] Lemma msim_munr {A B} (R : rel) (Q : A -> B -> rel) : msim R (munr (A:=A)) (munr (A:=B)) Q.
  Proof. intros sA moA sB moB _. cbn. exact I. Qed.

  #[using="Type"] Lemma msim_false {A B} (cA : M StA A) (cB : M StB B) (Q : A -> B -> rel) : msim (fun _ _ _ _ => False) cA cB Q.
  Proof. intros sA moA sB moB []. Qed.

  #[using="Type"] Lemma msim_get (R : rel) : msim R mget mget (fun a b sA moA sB moB => a = sA /\ b = sB /\ R sA moA sB moB).
  Proof. intros sA moA sB moB HR. cbn. auto. Qed.

  #[using="Type"] Lemma msim_upd (R : rel) (fA : StA -> StA) (fB : StB -> StB) (Q : unit -> unit -> rel) :
    (forall sA moA sB moB, R sA moA sB moB -> Q tt tt (fA sA) moA (fB sB) moB) -> msim R (mupd fA) (mupd fB) Q.
  Proof. intros H sA moA sB moB HR. cbn. apply H. exact HR. Qed.

  #[using="Type"] Lemma msim_bind {A B A' B'} (R : rel) (cA : M StA A) (cB : M StB B) (Q1 : A -> B -> rel)
        (kA : A -> M StA A') (kB : B -> M StB B') (Q : A' -> B' -> rel) :
    msim R cA cB Q1 -> (forall a b, msim (Q1 a b) (kA a) (kB b) Q) -> msim R (mbind cA kA) (mbind cB kB) Q.
  Proof.
    intros H1 H2 sA moA sB moB HR. unfold mbind, ebind.
    eapply tsim_bind; [exact (H1 _ _ _ _ HR)|].
    intros [|[a sA']] moA' [|[b sB']] moB' HQ; cbn in HQ; [cbn; exact I| destruct HQ| destruct HQ|].
    apply (H2 a b). exact HQ.
  Qed.

  #[using="Type"] Lemma msim_seq {A B A' B'} (R R1 : rel) (cA : M StA A) (cB : M StB B) (kA : A -> M StA A') (kB : B -> M StB B') (Q : A' -> B' -> rel) :
    msim R cA cB (fun _ _ => R1) -> (forall a b, msim R1 (kA a) (kB b) Q) -> msim R (mbind cA kA) (mbind cB kB) Q.
  Proof. intros H1 H2. eapply msim_bind; [exact H1| exact H2]. Qed.

  #[using="Type"] Lemma msim_bind_eq {A A' B'} (R : rel) (cA : M StA A) (cB : M StB A) (R1 : A -> rel)
        (kA : A -> M StA A') (kB : A -> M StB B') (Q : A' -> B' -> rel) :
    msim R cA cB (fun a b sA moA sB moB => a = b /\ R1 a sA moA sB moB) ->
    (forall a, msim (R1 a) (kA a) (kB a) Q) -> msim R (mbind cA kA) (mbind cB kB) Q.
  Proof. intros H1 H2. eapply msim_bind; [exact H1|]. intros a b sA moA sB moB [<- HR]. apply (H2 a). exact HR. Qed.

  #[using="Type"] Lemma msim_if {A B} (b : bool) (c1A c2A : M StA A) (c1B c2B : M StB B) (R : rel) Q :
    (b = true -> msim R c1A c1B Q) -> (b = false -> msim R c2A c2B Q) ->
    msim R (if b then c1A else c2A) (if b then c1B else c2B) Q.
  Proof. intros H1 H2. destruct b; auto. Qed.

  #[using="Type"] Lemma msim_exI {A B X} (P : X -> rel) (cA : M StA A) (cB : M StB B) Q :
    (forall x, msim (P x) cA cB Q) -> msim (fun sA moA sB moB => exists x, P x sA moA sB moB) cA cB Q.
  Proof. intros H sA moA sB moB [x HP]. exact (H x _ _ _ _ HP). Qed.

  #[using="Type"] Lemma msim_expose {A B} (R : rel) (phi : Prop) (cA : M StA A) (cB : M StB B) Q :
    (forall sA moA sB moB, R sA moA sB moB -> phi) -> (phi -> msim R cA cB Q) -> msim R cA cB Q.
  Proof. intros H1 H2 sA moA sB moB HR. exact (H2 (H1 _ _ _ _ HR) _ _ _ _ HR). Qed.

  #[using="Type"] Lemma msim_loop {XA XB A B} (bodyA : XA -> M StA (XA + A)) (bodyB : XB -> M StB (XB + B)) (I : XA -> XB -> rel) (Q : A -> B -> rel) :
    (forall xA xB, msim (I xA xB) (bodyA xA) (bodyB xB)
       (fun rA rB sA moA sB moB => match rA, rB with
                                  | inl xA', inl xB' => I xA' xB' sA moA sB moB
                                  | inr a, inr b => Q a b sA moA sB moB
                                  | _, _ => False
                                  end)) ->
    forall fuel xA xB, msim (I xA xB) (mloop fuel bodyA xA) (mloop fuel bodyB xB) Q.
  Proof.
    intros HB fuel. induction fuel as [|fuel IH]; intros xA xB; cbn [mloop]; [apply msim_munr|].
    eapply msim_bind; [apply HB|]. intros [xA'|a] [xB'|b]; cbn beta iota.
    - apply IH.
    - apply msim_false.
    - apply msim_false.
    - apply msim_ret. auto.
  Qed.

  #[using="Type"] Lemma msim_sys {A B} (nA nB : node) (decA : resp -> option A) (decB : resp -> option B) (R : rel) (Q : A -> B -> rel) :
    (forall sA moA sB moB, R sA moA sB moB ->
       (forall rspA moA' evs, nstep nA moA rspA moA' evs -> exists rspB moB', nstep nB moB rspB moB' evs /\
           match decA rspA, decB rspB with
           | Some a, Some b => Q a b sA moA' sB moB'
           | None, None => True
           | _, _ => False
           end)
       /\ (forall code moA', nexit nA moA code moA' -> exists moB', nexit nB moB code moB' /\ m_fs moB' = m_fs moA')) ->
    msim R (msys nA decA) (msys nB decB) Q.
  Proof.
    intros H sA moA sB moB HR. destruct (H _ _ _ _ HR) as (F & XF). unfold msys, enode. cbn.
    split; [| exact XF].
    intros rspA moA' evs ST. destruct (F _ _ _ ST) as (rspB & moB' & STB & HQ). exists rspB, moB'. split; [exact STB|].
    destruct (decA rspA), (decB rspB); cbn; [exact HQ| destruct HQ| destruct HQ| exact I].
  Qed.

  #[using="Type"] Theorem msim_tshape {A B} (R : rel) (cA : M StA A) (cB : M StB B) (Q : A -> B -> rel)
      (KA : exc (A * StA) -> Model -> TSet) (KB : exc (B * StB) -> Model -> TSet) sA moA sB moB :
    msim R cA cB Q -> R sA moA sB moB ->
    (forall a sA' moA' b sB' moB', Q a b sA' moA' sB' moB' -> t_incl (KA (Ok (a, sA')) moA') (KB (Ok (b, sB')) moB')) ->
    (forall moA' moB', t_incl (KA Unr moA') (KB Unr moB')) ->
    t_incl (tsh (cA sA) moA KA) (tsh (cB sB) moB KB).
  Proof.
    intros H HR HK HU. eapply tsim_tshape; [exact (H _ _ _ _ HR)|].
    intros [|[a sA']] moA' [|[b sB']] moB'; cbn; intros HQ; [apply HU| destruct HQ| destruct HQ| apply HK; exact HQ].
  Qed.
End MSim.
Arguments rel StA StB : clear implicits.
