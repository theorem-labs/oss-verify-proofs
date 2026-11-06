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
Open Scope mspec_scope.

Section SimW.
Context {StG StC : Type}.
Variable npk : node -> option (machine_state -> resp).

Definition rel : Type := StG -> Model -> StC -> Model -> Prop.

(* [comment removed for export] *)
Definition wpost {A B} (Q : A -> B -> rel) (trG : list event) (a : A) (sG' : StG) (moG' : Model)
  : list event -> exc (B * StC) -> Model -> Prop :=
  fun trC r moC' => exists b sC', r = Ok (b, sC') /\ trC = trG /\ Q a b sG' moG' sC' moC'.

Definition fsimw {A B} (R : rel) (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel) : Prop :=
  forall sG moG sC moC, R sG moG sC moC ->
    (forall trG a sG' moG', tpath nstep (mG sG) moG trG (Ok (a, sG')) moG' ->
       wreach npk nstep (mC sC) moC (wpost Q trG a sG' moG'))
    /\ (forall trG, texit nstep nexit (mG sG) moG trG -> wexit npk nstep nexit (mC sC) moC (eq trG)).

#[using="Type"] Lemma fsimw_conseq {A B} (R R' : rel) (mG : M StG A) (mC : M StC B) (Q Q' : A -> B -> rel) :
  fsimw R mG mC Q ->
  (forall sG moG sC moC, R' sG moG sC moC -> R sG moG sC moC) ->
  (forall a b sG moG sC moC, Q a b sG moG sC moC -> Q' a b sG moG sC moC) ->
  fsimw R' mG mC Q'.
Proof.
  intros H HR HQ sG moG sC moC HR'. destruct (H sG moG sC moC (HR _ _ _ _ HR')) as [HP HE]. split; [|exact HE].
  intros trG a sG' moG' Hp. eapply wreach_mono; [exact (HP trG a sG' moG' Hp)|].
  intros tr r mo' (b & sC' & -> & -> & HQ1). exists b, sC'. repeat split; auto.
Qed.

#[using="Type"] Lemma fsimw_pre {A B} (R R' : rel) (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel) :
  fsimw R mG mC Q -> (forall sG moG sC moC, R' sG moG sC moC -> R sG moG sC moC) -> fsimw R' mG mC Q.
Proof. intros H HR. eapply fsimw_conseq; eauto. Qed.

#[using="Type"] Lemma fsimw_post {A B} (R : rel) (mG : M StG A) (mC : M StC B) (Q Q' : A -> B -> rel) :
  fsimw R mG mC Q -> (forall a b sG moG sC moC, Q a b sG moG sC moC -> Q' a b sG moG sC moC) -> fsimw R mG mC Q'.
Proof. intros H HQ. eapply fsimw_conseq; eauto. Qed.

#[using="Type"] Lemma fsimw_ret {A B} (R : rel) (a : A) (b : B) (Q : A -> B -> rel) :
  (forall sG moG sC moC, R sG moG sC moC -> Q a b sG moG sC moC) -> fsimw R (mret a) (mret b) Q.
Proof.
  intros H sG moG sC moC HR. split.
  - intros trG a' sG' moG' Hp. cbn in Hp. destruct Hp as (E & -> & ->). injection E as <- <-.
    apply wreach_ret. exists b, sC. repeat split; auto.
  - intros trG Hx. destruct Hx.
Qed.

#[using="Type"] Lemma fsimw_bind {A B A' B'} (R : rel) (mG : M StG A) (mC : M StC B) (Q1 : A -> B -> rel)
      (kG : A -> M StG A') (kC : B -> M StC B') (Q : A' -> B' -> rel) :
  fsimw R mG mC Q1 -> (forall a b, fsimw (Q1 a b) (kG a) (kC b) Q) ->
  fsimw R (mbind mG kG) (mbind mC kC) Q.
Proof.
  intros H1 H2 sG moG sC moC HR. destruct (H1 sG moG sC moC HR) as [HP1 HE1]. split.
  - intros trG a' sG'' moG'' Hp. unfold mbind in Hp. apply tpath_ebind in Hp.
    destruct Hp as [[_ E]|(tr1 & [a sG'] & mo1 & tr2 & Hp1 & Hp2 & ->)]; [discriminate|]. cbn [fst snd] in Hp2.
    unfold mbind. apply wreach_ebind. eapply wreach_mono; [exact (HP1 tr1 a sG' mo1 Hp1)|].
    intros trC r moC1 (b & sC' & -> & -> & HQ1). cbn [fst snd].
    destruct (H2 a b sG' mo1 sC' moC1 HQ1) as [HP2 _].
    eapply wreach_mono; [exact (HP2 tr2 a' sG'' moG'' Hp2)|].
    intros trC2 r2 moC2 (b' & sC'' & -> & -> & HQ2). exists b', sC''. repeat split; auto.
  - intros trG Hx. unfold mbind in Hx. apply texit_ebind in Hx. unfold mbind.
    destruct Hx as [Hx|(tr1 & [a sG'] & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + apply wexit_ebind_l. exact (HE1 trG Hx).
    + apply wexit_ebind_r. eapply wreach_mono; [exact (HP1 tr1 a sG' mo1 Hp1)|].
      intros trC r moC1 (b & sC' & -> & -> & HQ1). exists (b, sC'). split; [reflexivity|]. cbn [fst snd].
      destruct (H2 a b sG' mo1 sC' moC1 HQ1) as [_ HE2]. cbn [fst snd] in Hx2.
      eapply wexit_mono; [exact (HE2 tr2 Hx2)|]. intros tr <-. reflexivity.
Qed.

#[using="Type"] Lemma fsimw_seq {A B A' B'} (R R1 : rel) (mG : M StG A) (mC : M StC B)
      (kG : A -> M StG A') (kC : B -> M StC B') (Q : A' -> B' -> rel) :
  fsimw R mG mC (fun _ _ => R1) -> (forall a b, fsimw R1 (kG a) (kC b) Q) ->
  fsimw R (mbind mG kG) (mbind mC kC) Q.
Proof. intros H1 H2. eapply fsimw_bind; [exact H1|]. intros a b. apply H2. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fsimw_bind_eq {A A' B'} (R : rel) (mG : M StG A) (mC : M StC A) (R1 : A -> rel)
      (kG : A -> M StG A') (kC : A -> M StC B') (Q : A' -> B' -> rel) :
  fsimw R mG mC (fun a b sG moG sC moC => a = b /\ R1 a sG moG sC moC) ->
  (forall a, fsimw (R1 a) (kG a) (kC a) Q) ->
  fsimw R (mbind mG kG) (mbind mC kC) Q.
Proof.
  intros H1 H2. eapply fsimw_bind; [exact H1|]. intros a b sG moG sC moC [<- HR]. apply (H2 a). exact HR.
Qed.

#[using="Type"] Lemma fsimw_munr {A B} (R : rel) (mC : M StC B) (Q : A -> B -> rel) : fsimw R (munr (A:=A)) mC Q.
Proof. intros sG moG sC moC HR. split; [intros trG a sG' moG' Hp; cbn in Hp; destruct Hp as (E & _); discriminate| intros trG []]. Qed.

#[using="Type"] Lemma fsimw_false {A B} (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel) : fsimw (fun _ _ _ _ => False) mG mC Q.
Proof. intros sG moG sC moC []. Qed.

#[using="Type"] Lemma fsimw_get (R : rel) :
  fsimw R mget mget (fun a b sG moG sC moC => a = sG /\ b = sC /\ R sG moG sC moC).
Proof.
  intros sG moG sC moC HR. split; [|intros trG []].
  intros trG a sG' moG' Hp. cbn in Hp. destruct Hp as (E & -> & ->). injection E as <- <-.
  apply wreach_ret. exists sC, sC. repeat split; auto.
Qed.

#[using="Type"] Lemma fsimw_upd (R : rel) (Q : unit -> unit -> rel) (fG : StG -> StG) (fC : StC -> StC) :
  (forall sG moG sC moC, R sG moG sC moC -> Q tt tt (fG sG) moG (fC sC) moC) ->
  fsimw R (mupd fG) (mupd fC) Q.
Proof.
  intros H sG moG sC moC HR. split; [|intros trG []].
  intros trG a sG' moG' Hp. cbn in Hp. destruct Hp as (E & -> & ->). injection E as <- <-.
  apply wreach_ret. exists tt, (fC sC). repeat split; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fsimw_upd_l {B} (R : rel) (Q : unit -> B -> rel) (fG : StG -> StG) (mC : M StC B) :
  fsimw (fun sG moG sC moC => exists s0, sG = fG s0 /\ R s0 moG sC moC) (mret tt) mC Q ->
  fsimw R (mupd fG) mC Q.
Proof.
  intros H sG moG sC moC HR. destruct (H (fG sG) moG sC moC) as [HP HE]; [exists sG; auto|]. split.
  - intros trG a sG' moG' Hp. cbn in Hp. destruct Hp as (E & -> & ->). injection E as <- <-.
    apply (HP [] tt (fG sG) moG). cbn. repeat split; reflexivity.
  - intros trG [].
Qed.

#[using="Type"] Lemma fsimw_upd_r {A} (R : rel) (Q : A -> unit -> rel) (mG : M StG A) (fC : StC -> StC) :
  fsimw (fun sG moG sC moC => exists s0, sC = fC s0 /\ R sG moG s0 moC) mG (mret tt) Q ->
  fsimw R mG (mupd fC) Q.
Proof.
  intros H sG moG sC moC HR. destruct (H sG moG (fC sC) moC) as [HP HE]; [exists sC; auto|]. split.
  - intros trG a sG' moG' Hp. specialize (HP trG a sG' moG' Hp).
    unfold mupd. unfold mret in HP. inversion HP; subst. apply wreach_ret. assumption.
  - intros trG Hx. specialize (HE trG Hx). unfold mret in HE. inversion HE.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fsimw_pure {A B} (R : rel) (phi : Prop) (mG : M StG A) (mC : M StC B) Q :
  (phi -> fsimw R mG mC Q) -> fsimw (fun sG moG sC moC => phi /\ R sG moG sC moC) mG mC Q.
Proof. intros H sG moG sC moC [Hphi HR]. exact (H Hphi sG moG sC moC HR). Qed.

#[using="Type"] Lemma fsimw_exI {A B X} (R : X -> rel) (mG : M StG A) (mC : M StC B) Q :
  (forall x, fsimw (R x) mG mC Q) -> fsimw (fun sG moG sC moC => exists x, R x sG moG sC moC) mG mC Q.
Proof. intros H sG moG sC moC [x HR]. exact (H x sG moG sC moC HR). Qed.

#[using="Type"] Lemma fsimw_pointwise {A B} (R : rel) (mG : M StG A) (mC : M StC B) Q :
  (forall sG moG sC moC, R sG moG sC moC ->
     fsimw (fun sG' moG' sC' moC' => sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC) mG mC Q) ->
  fsimw R mG mC Q.
Proof. intros H sG moG sC moC HR. apply (H sG moG sC moC HR). repeat split; reflexivity. Qed.

#[using="Type"] Lemma fsimw_if {A B} (b : bool) (R : rel) (m1G m2G : M StG A) (m1C m2C : M StC B) Q :
  (b = true -> fsimw R m1G m1C Q) -> (b = false -> fsimw R m2G m2C Q) ->
  fsimw R (if b then m1G else m2G) (if b then m1C else m2C) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fsimw_loop {X Y A B} (I : X -> Y -> rel) (Q : A -> B -> rel)
      (bodyG : X -> M StG (X + A)) (bodyC : Y -> M StC (Y + B)) :
  (forall x y, fsimw (I x y) (bodyG x) (bodyC y)
     (fun r r' sG moG sC moC => match r, r' with
                                | inl x', inl y' => I x' y' sG moG sC moC
                                | inr a, inr b => Q a b sG moG sC moC
                                | _, _ => False
                                end)) ->
  forall fuel x y, fsimw (I x y) (mloop fuel bodyG x) (mloop fuel bodyC y) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x y; cbn [mloop].
  - apply fsimw_munr.
  - eapply fsimw_bind; [apply Hb|]. intros [x'|a] [y'|b]; cbn beta.
    + apply IH.
    + apply fsimw_false.
    + apply fsimw_false.
    + apply fsimw_ret. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fsimw_sys {A B} (nG nC : node) (decG : resp -> option A) (decC : resp -> option B) (R : rel) (Q : A -> B -> rel) :
  npk nC = None ->
  (forall sG moG sC moC, R sG moG sC moC ->
     (forall rspG moG' evs a, nstep nG moG rspG moG' evs -> decG rspG = Some a ->
        exists rspC moC' b, nstep nC moC rspC moC' evs /\ decC rspC = Some b /\ Q a b sG moG' sC moC')
     /\ (forall code moG', nexit nG moG code moG' ->
        exists moC', nexit nC moC code moC' /\ m_fs moC' = m_fs moG')) ->
  fsimw R (msys nG decG) (msys nC decC) Q.
Proof.
  intros Hnp H sG moG sC moC HR. destruct (H _ _ _ _ HR) as [HS HX]. split.
  - intros trG a sG' moG' Hp. unfold msys in Hp. apply tpath_enode in Hp. destruct Hp as (rsp & Hst & E).
    destruct (decG rsp) as [a0|] eqn:Ed; [|discriminate]. injection E as -> ->.
    destruct (HS rsp moG' trG a0 Hst Ed) as (rspC & moC' & b & HstC & EdC & HQ).
    unfold msys. eapply wreach_enode; [exact Hnp| exact HstC|]. rewrite EdC. exists b, sC. repeat split; auto.
  - intros trG Hx. unfold msys in Hx. apply texit_enode in Hx. destruct Hx as (code & moG' & Hex & ->).
    destruct (HX code moG' Hex) as (moC' & HexC & Efs).
    unfold msys. eapply wexit_enode; [exact Hnp| exact HexC|]. rewrite Efs. reflexivity.
Qed.

End SimW.

Arguments rel StG StC : clear implicits.
