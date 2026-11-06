(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope mspec_scope.

Section USimX.
Context {G : Type}.
Variable nsafeP : node -> G -> Model -> Prop.
Variable gstepP : node -> resp -> G -> G.
Context {StG StC : Type}.
Variable npk : node -> option (machine_state -> resp).

#[local] Abbreviation twfX := (MSafeX.twfX nsafeP gstepP).
#[local] Abbreviation etwfX := (MSafeX.etwfX nsafeP gstepP).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tpathX {R} (t : itree node R) (g : G) (mo : Model) (tr : list event) (r : R) (g' : G) (mo' : Model) : Prop :=
  match t with
  | Ret r0 => r0 = r /\ g' = g /\ mo' = mo /\ tr = []
  | Vis n k => exists rsp mo1 evs tr', nstep n mo rsp mo1 evs /\ tpathX (k rsp) (gstepP n rsp g) mo1 tr' r g' mo' /\ tr = evs ++ tr'
  end.

#[using="Type"] Lemma tpathX_tpath {R} (t : itree node R) : forall g mo tr r g' mo',
  tpathX t g mo tr r g' mo' -> tpath nstep t mo tr r mo'.
Proof.
  induction t as [r0|n k IH]; intros g mo tr r g' mo' H; cbn in *.
  - destruct H as (-> & _ & -> & ->). repeat split; reflexivity.
  - destruct H as (rsp & mo1 & evs & tr' & Hst & Hp & ->). exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [| reflexivity].
    eapply IH. exact Hp.
Qed.

#[using="Type"] Lemma tpath_tpathX {R} (t : itree node R) : forall g mo tr r mo',
  tpath nstep t mo tr r mo' -> exists g', tpathX t g mo tr r g' mo'.
Proof.
  induction t as [r0|n k IH]; intros g mo tr r mo' H; cbn in *.
  - destruct H as (-> & -> & ->). exists g. repeat split; reflexivity.
  - destruct H as (rsp & mo1 & evs & tr' & Hst & Hp & ->). destruct (IH rsp (gstepP n rsp g) mo1 tr' r mo' Hp) as [g' Hp'].
    exists g', rsp, mo1, evs, tr'. repeat split; assumption || reflexivity.
Qed.

#[using="Type"] Lemma tpathX_bind {A B} (t : itree node A) (f : A -> itree node B) : forall g mo tr r g' mo',
  tpathX (ITree.bind node t f) g mo tr r g' mo' ->
  exists tr1 a g1 mo1 tr2, tpathX t g mo tr1 a g1 mo1 /\ tpathX (f a) g1 mo1 tr2 r g' mo' /\ tr = tr1 ++ tr2.
Proof.
  induction t as [a0|n k IH]; intros g mo tr r g' mo' H; cbn in *.
  - exists [], a0, g, mo, tr. split; [repeat split; reflexivity|]. split; [exact H| reflexivity].
  - destruct H as (rsp & mo1 & evs & tr' & Hst & Hp & ->).
    destruct (IH rsp (gstepP n rsp g) mo1 tr' r g' mo' Hp) as (tr1 & a & g1 & mo2 & tr2 & H1 & H2 & ->).
    exists (evs ++ tr1), a, g1, mo2, tr2. split; [| split; [exact H2| rewrite app_assoc; reflexivity]].
    exists rsp, mo1, evs, tr1. repeat split; assumption || reflexivity.
Qed.

#[using="Type"] Lemma tpathX_ebind {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) g mo tr r g' mo' :
  tpathX (ebind t f) g mo tr r g' mo' ->
  (tpathX t g mo tr Unr g' mo' /\ r = Unr)
  \/ exists tr1 a g1 mo1 tr2, tpathX t g mo tr1 (Ok a) g1 mo1 /\ tpathX (f a) g1 mo1 tr2 r g' mo' /\ tr = tr1 ++ tr2.
Proof.
  unfold ebind. intros H. apply tpathX_bind in H. destruct H as (tr1 & [|a] & g1 & mo1 & tr2 & H1 & H2 & ->).
  - left. cbn in H2. destruct H2 as (<- & -> & -> & ->). rewrite app_nil_r. split; [exact H1| reflexivity].
  - right. exists tr1, a, g1, mo1, tr2. repeat split; assumption.
Qed.

#[using="Type"] Lemma tpathX_enode {A} n (pl : resp -> option A) g mo tr r g' mo' :
  tpathX (enode n pl) g mo tr r g' mo' ->
  exists rsp, nstep n mo rsp mo' tr /\ g' = gstepP n rsp g /\ r = match pl rsp with Some a => Ok a | None => Unr end.
Proof.
  cbn. intros (rsp & mo1 & evs & tr' & Hst & Hp & ->). exists rsp.
  destruct (pl rsp) as [a|]; cbn in Hp; destruct Hp as (<- & -> & -> & ->); rewrite app_nil_r; repeat split; assumption || reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twfX_tpathX {R} (t : itree node R) : forall g mo P tr r g' mo',
  twfX t g mo P -> tpathX t g mo tr r g' mo' -> P r g' mo'.
Proof.
  induction t as [r0|n k IH]; intros g mo P tr r g' mo' H Hp; cbn in *.
  - destruct Hp as (<- & -> & -> & ->). exact H.
  - destruct H as [_ Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _). eapply IH; [eapply Hk; exact Hst| exact Hp].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma twfX_of_tpathX {R} (t : itree node R) : forall g mo (P : R -> G -> Model -> Prop),
  twfX t g mo (fun _ _ _ => True) -> (forall tr r g' mo', tpathX t g mo tr r g' mo' -> P r g' mo') -> twfX t g mo P.
Proof.
  induction t as [r|n k IH]; intros g mo P HT HP; cbn in *.
  - apply (HP []). repeat split; reflexivity.
  - destruct HT as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; [exact (Hk _ _ _ Hst)|].
    intros tr r g'' mo'' Hp. apply (HP (evs ++ tr)). exists rsp, mo', evs, tr. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition relX : Type := G -> StG -> Model -> StC -> Model -> Prop.

(* [comment removed for export] *)
Definition wpostX {A B} (Q : A -> B -> relX) (trG : list event) (a : A) (g' : G) (sG' : StG) (moG' : Model)
  : list event -> exc (B * StC) -> Model -> Prop :=
  fun trC r moC' => exists b sC', r = Ok (b, sC') /\ trC = trG /\ Q a b g' sG' moG' sC' moC'.

Definition usimX {A B} (R : relX) (mG : M StG A) (mC : M StC B) (Q : A -> B -> relX) : Prop :=
  forall g sG moG sC moC, R g sG moG sC moC ->
    (forall trG a sG' g' moG', tpathX (mG sG) g moG trG (Ok (a, sG')) g' moG' ->
       wreach npk nstep (mC sC) moC (wpostX Q trG a g' sG' moG'))
    /\ (forall trG, texit nstep nexit (mG sG) moG trG -> wexit npk nstep nexit (mC sC) moC (eq trG))
    /\ etwfX (mG sG) g moG (fun _ _ _ => True).

(* [comment removed for export] *)
Definition eqpost {A} (R1 : A -> relX) : A -> A -> relX :=
  fun a b g sG moG sC moC => a = b /\ R1 a g sG moG sC moC.

(* [comment removed for export] *)
#[using="Type"] Lemma usimX_fsimw {A B} (R : relX) (mG : M StG A) (mC : M StC B) Q g :
  usimX R mG mC Q -> fsimw npk (R g) mG mC (fun a b sG moG sC moC => exists g', Q a b g' sG moG sC moC).
Proof.
  intros H sG moG sC moC HR. destruct (H g sG moG sC moC HR) as (HP & HE & _). split; [| exact HE].
  intros trG a sG' moG' Hp. destruct (tpath_tpathX _ g _ _ _ _ Hp) as [g' Hp'].
  eapply wreach_mono; [exact (HP _ _ _ _ _ Hp')|]. intros tr r mo' (b & sC' & -> & -> & HQ). exists b, sC'. repeat split; auto. exists g'. exact HQ.
Qed.

#[using="Type"] Lemma usimX_safe {A B} (R : relX) (mG : M StG A) (mC : M StC B) Q g sG moG sC moC :
  usimX R mG mC Q -> R g sG moG sC moC -> etwfX (mG sG) g moG (fun _ _ _ => True).
Proof. intros H HR. exact (proj2 (proj2 (H g sG moG sC moC HR))). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma usimX_conseq {A B} (R R' : relX) (mG : M StG A) (mC : M StC B) (Q Q' : A -> B -> relX) :
  usimX R' mG mC Q' -> (forall g sG moG sC moC, R g sG moG sC moC -> R' g sG moG sC moC) ->
  (forall a b g sG moG sC moC, Q' a b g sG moG sC moC -> Q a b g sG moG sC moC) -> usimX R mG mC Q.
Proof.
  intros H HR HQ g sG moG sC moC H0. destruct (H g sG moG sC moC (HR _ _ _ _ _ H0)) as (HP & HE & HS).
  split; [| split; [exact HE| exact HS]].
  intros trG a sG' g' moG' Hp. eapply wreach_mono; [exact (HP trG a sG' g' moG' Hp)|].
  intros tr r mo' (b & sC' & -> & -> & HQ1). exists b, sC'. repeat split; auto.
Qed.

#[using="Type"] Lemma usimX_pre {A B} (R R' : relX) (mG : M StG A) (mC : M StC B) Q :
  usimX R' mG mC Q -> (forall g sG moG sC moC, R g sG moG sC moC -> R' g sG moG sC moC) -> usimX R mG mC Q.
Proof. intros H HR. eapply usimX_conseq; eauto. Qed.

#[using="Type"] Lemma usimX_post {A B} (R : relX) (mG : M StG A) (mC : M StC B) (Q Q' : A -> B -> relX) :
  usimX R mG mC Q' -> (forall a b g sG moG sC moC, Q' a b g sG moG sC moC -> Q a b g sG moG sC moC) -> usimX R mG mC Q.
Proof. intros H HQ. eapply usimX_conseq; eauto. Qed.

#[using="Type"] Lemma usimX_ret {A B} (R : relX) (a : A) (b : B) (Q : A -> B -> relX) :
  (forall g sG moG sC moC, R g sG moG sC moC -> Q a b g sG moG sC moC) -> usimX R (mret a) (mret b) Q.
Proof.
  intros H g sG moG sC moC HR. split; [| split; [intros trG []| exact I]].
  intros trG a' sG' g' moG' Hp. cbn in Hp. destruct Hp as (E & -> & -> & ->). injection E as <- <-.
  apply wreach_ret. exists b, sC. repeat split; auto.
Qed.

(* [comment removed for export] *)
Hypothesis NPK : forall n f mo1, npk n = Some f -> exists rsp, nstep n mo1 rsp mo1 [].

#[using="NPK"] Lemma usimX_bind {A B A' B'} (R : relX) (mG : M StG A) (mC : M StC B) (Q1 : A -> B -> relX)
      (kG : A -> M StG A') (kC : B -> M StC B') (Q : A' -> B' -> relX) :
  usimX R mG mC Q1 -> (forall a b, usimX (Q1 a b) (kG a) (kC b) Q) -> usimX R (mbind mG kG) (mbind mC kC) Q.
Proof.
  intros H1 H2 g sG moG sC moC HR. destruct (H1 g sG moG sC moC HR) as (HP1 & HE1 & HS1).
  (* [comment removed for export] *)
  assert (LEAF : forall tr1 a sG' g1 mo1, tpathX (mG sG) g moG tr1 (Ok (a, sG')) g1 mo1 ->
            exists trC b sC' moC1, tpath nstep (mC sC) moC trC (Ok (b, sC')) moC1 /\ trC = tr1 /\ Q1 a b g1 sG' mo1 sC' moC1).
  { intros tr1 a sG' g1 mo1 Hp1. pose proof (HP1 tr1 a sG' g1 mo1 Hp1) as W.
    eapply wreach_tpath in W; [| exact NPK]. destruct W as (trC & r & moC1 & HpC & (b & sC' & -> & -> & HQ1)).
    exists tr1, b, sC', moC1. repeat split; auto. }
  split; [| split].
  - intros trG a' sG'' g'' moG'' Hp. unfold mbind in Hp. apply tpathX_ebind in Hp.
    destruct Hp as [[_ E]|(tr1 & [a sG'] & g1 & mo1 & tr2 & Hp1 & Hp2 & ->)]; [discriminate|]. cbn [fst snd] in Hp2.
    unfold mbind. apply wreach_ebind. eapply wreach_mono; [exact (HP1 tr1 a sG' g1 mo1 Hp1)|].
    intros trC r moC1 (b & sC' & -> & -> & HQ1). cbn [fst snd].
    destruct (H2 a b g1 sG' mo1 sC' moC1 HQ1) as (HP2 & _ & _).
    eapply wreach_mono; [exact (HP2 tr2 a' sG'' g'' moG'' Hp2)|].
    intros trC2 r2 moC2 (b' & sC'' & -> & -> & HQ2). exists b', sC''. repeat split; auto.
  - intros trG Hx. unfold mbind in Hx. apply texit_ebind in Hx. unfold mbind.
    destruct Hx as [Hx|(tr1 & [a sG'] & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + apply wexit_ebind_l. exact (HE1 trG Hx).
    + destruct (tpath_tpathX _ g _ _ _ _ Hp1) as [g1 Hp1'].
      apply wexit_ebind_r. eapply wreach_mono; [exact (HP1 tr1 a sG' g1 mo1 Hp1')|].
      intros trC r moC1 (b & sC' & -> & -> & HQ1). exists (b, sC'). split; [reflexivity|]. cbn [fst snd].
      destruct (H2 a b g1 sG' mo1 sC' moC1 HQ1) as (_ & HE2 & _). cbn [fst snd] in Hx2.
      eapply wexit_mono; [exact (HE2 tr2 Hx2)|]. intros tr <-. reflexivity.
  - unfold mbind. apply etwfX_ebind. unfold MSafeX.etwfX in *. eapply twfX_of_tpathX; [eapply twfX_mono; [exact HS1| intros; exact I]|].
    intros tr [|[a sG']] g1 mo1 Hp; cbn.
    + exact (twfX_tpathX _ _ _ _ _ _ _ _ HS1 Hp).
    + destruct (LEAF tr a sG' g1 mo1 Hp) as (trC & b & sC' & moC1 & _ & _ & HQ1).
      destruct (H2 a b g1 sG' mo1 sC' moC1 HQ1) as (_ & _ & HS2). exact HS2.
Qed.

#[using="NPK"] Lemma usimX_seq {A B A' B'} (R R1 : relX) (mG : M StG A) (mC : M StC B) (kG : A -> M StG A') (kC : B -> M StC B') (Q : A' -> B' -> relX) :
  usimX R mG mC (fun _ _ => R1) -> (forall a b, usimX R1 (kG a) (kC b) Q) -> usimX R (mbind mG kG) (mbind mC kC) Q.
Proof. intros H1 H2. eapply usimX_bind; [exact H1| exact H2]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma usimX_munr {A B} (R : relX) (mC : M StC B) (Q : A -> B -> relX) :
  (forall g sG moG sC moC, R g sG moG sC moC -> False) -> usimX R (munr (A:=A)) mC Q.
Proof. intros H g sG moG sC moC HR. destruct (H _ _ _ _ _ HR). Qed.

#[using="Type"] Lemma usimX_false {A B} (mG : M StG A) (mC : M StC B) (Q : A -> B -> relX) : usimX (fun _ _ _ _ _ => False) mG mC Q.
Proof. intros ? ? ? ? ? []. Qed.

#[using="Type"] Lemma usimX_get (R : relX) :
  usimX R mget mget (fun a b g sG moG sC moC => a = sG /\ b = sC /\ R g sG moG sC moC).
Proof.
  intros g sG moG sC moC HR. split; [| split; [intros trG []| exact I]].
  intros trG a sG' g' moG' Hp. cbn in Hp. destruct Hp as (E & -> & -> & ->). injection E as <- <-.
  apply wreach_ret. exists sC, sC. repeat split; auto.
Qed.

#[using="Type"] Lemma usimX_upd (R : relX) (Q : unit -> unit -> relX) (fG : StG -> StG) (fC : StC -> StC) :
  (forall g sG moG sC moC, R g sG moG sC moC -> Q tt tt g (fG sG) moG (fC sC) moC) -> usimX R (mupd fG) (mupd fC) Q.
Proof.
  intros H g sG moG sC moC HR. split; [| split; [intros trG []| exact I]].
  intros trG a sG' g' moG' Hp. cbn in Hp. destruct Hp as (E & -> & -> & ->). injection E as <- <-.
  apply wreach_ret. exists tt, (fC sC). repeat split; auto.
Qed.

#[using="Type"] Lemma usimX_pure {A B} (R : relX) (phi : Prop) (mG : M StG A) (mC : M StC B) Q :
  (phi -> usimX R mG mC Q) -> usimX (fun g sG moG sC moC => phi /\ R g sG moG sC moC) mG mC Q.
Proof. intros H g sG moG sC moC [Hphi HR]. exact (H Hphi g sG moG sC moC HR). Qed.

#[using="Type"] Lemma usimX_exI {A B X} (R : X -> relX) (mG : M StG A) (mC : M StC B) Q :
  (forall x, usimX (R x) mG mC Q) -> usimX (fun g sG moG sC moC => exists x, R x g sG moG sC moC) mG mC Q.
Proof. intros H g sG moG sC moC [x HR]. exact (H x g sG moG sC moC HR). Qed.

#[using="Type"] Lemma usimX_pointwise {A B} (R : relX) (mG : M StG A) (mC : M StC B) Q :
  (forall g sG moG sC moC, R g sG moG sC moC ->
     usimX (fun g' sG' moG' sC' moC' => g' = g /\ sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC) mG mC Q) ->
  usimX R mG mC Q.
Proof. intros H g sG moG sC moC HR. apply (H g sG moG sC moC HR). repeat split; reflexivity. Qed.

#[using="NPK"] Lemma usimX_bind_eq {A A' B'} (R : relX) (mG : M StG A) (mC : M StC A) (R1 : A -> relX)
      (kG : A -> M StG A') (kC : A -> M StC B') (Q : A' -> B' -> relX) :
  usimX R mG mC (eqpost R1) ->
  (forall a, usimX (R1 a) (kG a) (kC a) Q) -> usimX R (mbind mG kG) (mbind mC kC) Q.
Proof.
  intros H1 H2. eapply usimX_bind; [exact H1|]. intros a b. apply usimX_pure. intros <-. apply H2.
Qed.

#[using="Type"] Lemma usimX_if {A B} (b : bool) (R : relX) (m1G m2G : M StG A) (m1C m2C : M StC B) Q :
  (b = true -> usimX R m1G m1C Q) -> (b = false -> usimX R m2G m2C Q) ->
  usimX R (if b then m1G else m2G) (if b then m1C else m2C) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

(* [comment removed for export] *)
#[using="NPK"] Lemma usimX_loopV {X Y A B} (I : X -> Y -> relX) (V : X -> nat -> Prop) (Q : A -> B -> relX)
      (bodyG : X -> M StG (X + A)) (bodyC : Y -> M StC (Y + B)) :
  (forall x y n, V x (S n) -> usimX (I x y) (bodyG x) (bodyC y)
     (fun r r' g sG moG sC moC => match r, r' with
                                  | inl x', inl y' => V x' n /\ I x' y' g sG moG sC moC
                                  | inr a, inr b => Q a b g sG moG sC moC
                                  | _, _ => False
                                  end)) ->
  (forall x, V x 0%nat -> False) ->
  forall fuel x y, V x fuel -> usimX (I x y) (mloop fuel bodyG x) (mloop fuel bodyC y) Q.
Proof.
  intros Hb HV0 fuel. induction fuel as [|fuel IH]; intros x y HV; cbn [mloop].
  - destruct (HV0 x HV).
  - eapply usimX_bind; [apply (Hb x y fuel HV)|]. intros [x'|a] [y'|b]; cbn beta.
    + apply usimX_pure. intros HV'. apply IH. exact HV'.
    + apply usimX_false.
    + apply usimX_false.
    + apply usimX_ret. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma usimX_sys {A B} (nG nC : node) (decG : resp -> option A) (decC : resp -> option B) (R : relX) (Q : A -> B -> relX) :
  npk nC = None ->
  (forall g sG moG sC moC, R g sG moG sC moC ->
     nsafeP nG g moG
     /\ (forall rspG moG' evs, nstep nG moG rspG moG' evs -> exists a, decG rspG = Some a)
     /\ (forall rspG moG' evs a, nstep nG moG rspG moG' evs -> decG rspG = Some a ->
        exists rspC moC' b, nstep nC moC rspC moC' evs /\ decC rspC = Some b /\ Q a b (gstepP nG rspG g) sG moG' sC moC')
     /\ (forall code moG', nexit nG moG code moG' ->
        exists moC', nexit nC moC code moC' /\ m_fs moC' = m_fs moG')) ->
  usimX R (msys nG decG) (msys nC decC) Q.
Proof.
  intros Hnp H g sG moG sC moC HR. destruct (H _ _ _ _ _ HR) as (Hs & Hd & HS & HX). split; [| split].
  - intros trG a sG' g' moG' Hp. unfold msys in Hp. apply tpathX_enode in Hp. destruct Hp as (rsp & Hst & -> & E).
    destruct (decG rsp) as [a0|] eqn:Ed; [|discriminate]. injection E as -> ->.
    destruct (HS rsp moG' trG a0 Hst Ed) as (rspC & moC' & b & HstC & EdC & HQ).
    unfold msys. eapply wreach_enode; [exact Hnp| exact HstC|]. rewrite EdC. exists b, sC. repeat split; auto.
  - intros trG Hx. unfold msys in Hx. apply texit_enode in Hx. destruct Hx as (code & moG' & Hex & ->).
    destruct (HX code moG' Hex) as (moC' & HexC & Efs).
    unfold msys. eapply wexit_enode; [exact Hnp| exact HexC|]. rewrite Efs. reflexivity.
  - unfold msys. apply etwfX_enode; [exact Hs|]. intros rsp mo' evs Hst. destruct (Hd _ _ _ Hst) as [a Ha].
    exists (a, sG). rewrite Ha. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma usimX_of_paths {A B} (R : relX) (mG : M StG A) (mC : M StC B) (Q : A -> B -> relX) :
  (forall g sG moG sC moC, R g sG moG sC moC ->
     etwfX (mG sG) g moG (fun _ _ _ => True)
     /\ (forall trG, texit nstep nexit (mG sG) moG trG -> False)
     /\ (forall trG a sG' g' moG', tpathX (mG sG) g moG trG (Ok (a, sG')) g' moG' ->
           wreach npk nstep (mC sC) moC (wpostX Q trG a g' sG' moG'))) ->
  usimX R mG mC Q.
Proof.
  intros H g sG moG sC moC HR. destruct (H _ _ _ _ _ HR) as (HS & HX & HP).
  split; [exact HP|]. split; [| exact HS]. intros trG Hx. destruct (HX trG Hx).
Qed.

End USimX.

Arguments relX G StG StC : clear implicits.
Arguments usimX {G} nsafeP gstepP {StG StC} npk {A B} R mG mC Q.
Arguments eqpost {G StG StC A} R1.
Arguments tpathX {G} gstepP {R} t g mo tr r g' mo'.
