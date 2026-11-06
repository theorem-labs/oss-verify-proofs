(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Monad MSafe.
Import ListNotations.
Import ITree.Exc.
Open Scope mspec_scope.

Section Sim.
Context {StG StC : Type}.
Variable debtG : StG -> list event.
Variable debtC : StC -> list event.
(* [comment removed for export] *)
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.

Definition rel : Type := StG -> Model -> StC -> Model -> Prop.

Definition fsim {A B} (R : rel) (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel) : Prop :=
  forall sG moG sC moC, R sG moG sC moC ->
    (forall trG a sG' moG', tpath stepG (mG sG) moG trG (Ok (a, sG')) moG' ->
       exists trC b sC' moC' v,
         tpath nstep (mC sC) moC trC (Ok (b, sC')) moC'
         /\ trG ++ debtG sG' = debtG sG ++ v /\ trC ++ debtC sC' = debtC sC ++ v
         /\ Q a b sG' moG' sC' moC')
    /\ (forall trG, texit stepG nexit (mG sG) moG trG ->
       exists trC v, texit nstep nexit (mC sC) moC trC /\ trG = debtG sG ++ v /\ trC = debtC sC ++ v).

Lemma fsim_conseq {A B} (R R' : rel) (mG : M StG A) (mC : M StC B) (Q Q' : A -> B -> rel) :
  fsim R mG mC Q ->
  (forall sG moG sC moC, R' sG moG sC moC -> R sG moG sC moC) ->
  (forall a b sG moG sC moC, Q a b sG moG sC moC -> Q' a b sG moG sC moC) ->
  fsim R' mG mC Q'.
Proof.
  intros H HR HQ sG moG sC moC HR'. destruct (H sG moG sC moC (HR _ _ _ _ HR')) as [HP HE]. split; [|exact HE].
  intros trG a sG' moG' Hp. destruct (HP trG a sG' moG' Hp) as (trC & b & sC' & moC' & v & HpC & E1 & E2 & HQ1).
  exists trC, b, sC', moC', v. repeat split; auto.
Qed.

Lemma fsim_pre {A B} (R R' : rel) (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel) :
  fsim R mG mC Q -> (forall sG moG sC moC, R' sG moG sC moC -> R sG moG sC moC) -> fsim R' mG mC Q.
Proof. intros H HR. eapply fsim_conseq; eauto. Qed.

Lemma fsim_post {A B} (R : rel) (mG : M StG A) (mC : M StC B) (Q Q' : A -> B -> rel) :
  fsim R mG mC Q -> (forall a b sG moG sC moC, Q a b sG moG sC moC -> Q' a b sG moG sC moC) -> fsim R mG mC Q'.
Proof. intros H HQ. eapply fsim_conseq; eauto. Qed.

Lemma fsim_ret {A B} (R : rel) (a : A) (b : B) (Q : A -> B -> rel) :
  (forall sG moG sC moC, R sG moG sC moC -> Q a b sG moG sC moC) -> fsim R (mret a) (mret b) Q.
Proof.
  intros H sG moG sC moC HR. split.
  - intros trG a' sG' moG' Hp. cbn in Hp. destruct Hp as (E & -> & ->). injection E as <- <-.
    exists [], b, sC, moC, []. split; [cbn; repeat split; reflexivity|]. rewrite !app_nil_r. repeat split; auto.
  - intros trG Hx. destruct Hx.
Qed.

Lemma fsim_bind {A B A' B'} (R : rel) (mG : M StG A) (mC : M StC B) (Q1 : A -> B -> rel)
      (kG : A -> M StG A') (kC : B -> M StC B') (Q : A' -> B' -> rel) :
  fsim R mG mC Q1 -> (forall a b, fsim (Q1 a b) (kG a) (kC b) Q) ->
  fsim R (mbind mG kG) (mbind mC kC) Q.
Proof.
  intros H1 H2 sG moG sC moC HR. destruct (H1 sG moG sC moC HR) as [HP1 HE1]. split.
  - intros trG a' sG'' moG'' Hp. unfold mbind in Hp. apply tpath_ebind in Hp.
    destruct Hp as [[_ E]|(tr1 & [a sG'] & mo1 & tr2 & Hp1 & Hp2 & ->)]; [discriminate|]. cbn [fst snd] in Hp2.
    destruct (HP1 tr1 a sG' mo1 Hp1) as (trC1 & b & sC' & moC1 & v1 & HpC1 & E1 & E2 & HQ1).
    destruct (H2 a b sG' mo1 sC' moC1 HQ1) as [HP2 _].
    destruct (HP2 tr2 a' sG'' moG'' Hp2) as (trC2 & b' & sC'' & moC'' & v2 & HpC2 & E3 & E4 & HQ2).
    exists (trC1 ++ trC2), b', sC'', moC'', (v1 ++ v2). split.
    + unfold mbind. apply tpath_ebind. right. exists trC1, (b, sC'), moC1, trC2. repeat split; auto.
    + split; [|split; [|exact HQ2]].
      * rewrite <- app_assoc, E3, app_assoc, E1, app_assoc. reflexivity.
      * rewrite <- app_assoc, E4, app_assoc, E2, app_assoc. reflexivity.
  - intros trG Hx. unfold mbind in Hx. apply texit_ebind in Hx. destruct Hx as [Hx|(tr1 & [a sG'] & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + destruct (HE1 trG Hx) as (trC & v & HxC & E1 & E2). exists trC, v. split; [|auto]. unfold mbind. apply texit_ebind. left. exact HxC.
    + destruct (HP1 tr1 a sG' mo1 Hp1) as (trC1 & b & sC' & moC1 & v1 & HpC1 & E1 & E2 & HQ1).
      destruct (H2 a b sG' mo1 sC' moC1 HQ1) as [_ HE2]. cbn [fst snd] in Hx2.
      destruct (HE2 tr2 Hx2) as (trC2 & v2 & HxC2 & E3 & E4).
      exists (trC1 ++ trC2), (v1 ++ v2). split; [|split].
      * unfold mbind. apply texit_ebind. right. exists trC1, (b, sC'), moC1, trC2. repeat split; auto.
      * rewrite E3, app_assoc, E1, app_assoc. reflexivity.
      * rewrite E4, app_assoc, E2, app_assoc. reflexivity.
Qed.

Lemma fsim_seq {A B A' B'} (R R1 : rel) (mG : M StG A) (mC : M StC B)
      (kG : A -> M StG A') (kC : B -> M StC B') (Q : A' -> B' -> rel) :
  fsim R mG mC (fun _ _ => R1) -> (forall a b, fsim R1 (kG a) (kC b) Q) ->
  fsim R (mbind mG kG) (mbind mC kC) Q.
Proof. intros H1 H2. eapply fsim_bind; [exact H1|]. intros a b. apply H2. Qed.

(* [comment removed for export] *)
Lemma fsim_bind_eq {A A' B'} (R : rel) (mG : M StG A) (mC : M StC A) (R1 : A -> rel)
      (kG : A -> M StG A') (kC : A -> M StC B') (Q : A' -> B' -> rel) :
  fsim R mG mC (fun a b sG moG sC moC => a = b /\ R1 a sG moG sC moC) ->
  (forall a, fsim (R1 a) (kG a) (kC a) Q) ->
  fsim R (mbind mG kG) (mbind mC kC) Q.
Proof.
  intros H1 H2. eapply fsim_bind; [exact H1|]. intros a b sG moG sC moC [<- HR]. apply (H2 a). exact HR.
Qed.

Lemma fsim_munr {A B} (R : rel) (mC : M StC B) (Q : A -> B -> rel) : fsim R (munr (A:=A)) mC Q.
Proof. intros sG moG sC moC HR. split; [intros trG a sG' moG' Hp; cbn in Hp; destruct Hp as (E & _); discriminate| intros trG []]. Qed.

Lemma fsim_false {A B} (mG : M StG A) (mC : M StC B) (Q : A -> B -> rel) : fsim (fun _ _ _ _ => False) mG mC Q.
Proof. intros sG moG sC moC []. Qed.

(* [comment removed for export] *)
Lemma fsim_get (R : rel) :
  fsim R mget mget (fun a b sG moG sC moC => a = sG /\ b = sC /\ R sG moG sC moC).
Proof.
  intros sG moG sC moC HR. split; [|intros trG []].
  intros trG a sG' moG' Hp. cbn in Hp. destruct Hp as (E & -> & ->). injection E as <- <-.
  exists [], sC, sC, moC, []. split; [cbn; repeat split; reflexivity|]. rewrite !app_nil_r. repeat split; auto.
Qed.

Lemma fsim_upd (R : rel) (Q : unit -> unit -> rel) (fG : StG -> StG) (fC : StC -> StC) :
  (forall sG moG sC moC, R sG moG sC moC ->
     debtG (fG sG) = debtG sG /\ debtC (fC sC) = debtC sC /\ Q tt tt (fG sG) moG (fC sC) moC) ->
  fsim R (mupd fG) (mupd fC) Q.
Proof.
  intros H sG moG sC moC HR. destruct (H _ _ _ _ HR) as (E1 & E2 & HQ). split; [|intros trG []].
  intros trG a sG' moG' Hp. cbn in Hp. destruct Hp as (E & -> & ->). injection E as <- <-.
  exists [], tt, (fC sC), moC, []. split; [cbn; repeat split; reflexivity|]. rewrite !app_nil_r, E1, E2. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma fsim_upd_l {B} (R : rel) (Q : unit -> B -> rel) (fG : StG -> StG) (mC : M StC B) :
  (forall sG, debtG (fG sG) = debtG sG) ->
  fsim (fun sG moG sC moC => exists s0, sG = fG s0 /\ R s0 moG sC moC) (mret tt) mC Q ->
  fsim R (mupd fG) mC Q.
Proof.
  intros Hd H sG moG sC moC HR. destruct (H (fG sG) moG sC moC) as [HP HE]; [exists sG; auto|]. split.
  - intros trG a sG' moG' Hp. cbn in Hp. destruct Hp as (E & -> & ->). injection E as <- <-.
    destruct (HP [] tt (fG sG) moG) as (trC & b & sC' & moC' & v & HpC & E1 & E2 & HQ); [cbn; repeat split; reflexivity|].
    exists trC, b, sC', moC', v. rewrite Hd in E1. rewrite Hd. repeat split; auto.
  - intros trG [].
Qed.

Lemma fsim_upd_r {A} (R : rel) (Q : A -> unit -> rel) (mG : M StG A) (fC : StC -> StC) :
  (forall sC, debtC (fC sC) = debtC sC) ->
  fsim (fun sG moG sC moC => exists s0, sC = fC s0 /\ R sG moG s0 moC) mG (mret tt) Q ->
  fsim R mG (mupd fC) Q.
Proof.
  intros Hd H sG moG sC moC HR. destruct (H sG moG (fC sC) moC) as [HP HE]; [exists sC; auto|]. split.
  - intros trG a sG' moG' Hp.
    destruct (HP trG a sG' moG' Hp) as (trC & b & sC' & moC' & v & HpC & E1 & E2 & HQ).
    cbn in HpC. destruct HpC as (E & -> & ->). injection E as <- <-.
    exists [], tt, (fC sC), moC, v. split; [cbn; repeat split; reflexivity|]. rewrite Hd in E2. rewrite Hd. repeat split; auto.
  - intros trG Hx. destruct (HE trG Hx) as (trC & v & HxC & _). destruct HxC.
Qed.

(* [comment removed for export] *)
Lemma fsim_pure {A B} (R : rel) (phi : Prop) (mG : M StG A) (mC : M StC B) Q :
  (phi -> fsim R mG mC Q) -> fsim (fun sG moG sC moC => phi /\ R sG moG sC moC) mG mC Q.
Proof. intros H sG moG sC moC [Hphi HR]. exact (H Hphi sG moG sC moC HR). Qed.

Lemma fsim_exI {A B X} (R : X -> rel) (mG : M StG A) (mC : M StC B) Q :
  (forall x, fsim (R x) mG mC Q) -> fsim (fun sG moG sC moC => exists x, R x sG moG sC moC) mG mC Q.
Proof. intros H sG moG sC moC [x HR]. exact (H x sG moG sC moC HR). Qed.

Lemma fsim_pointwise {A B} (R : rel) (mG : M StG A) (mC : M StC B) Q :
  (forall sG moG sC moC, R sG moG sC moC ->
     fsim (fun sG' moG' sC' moC' => sG' = sG /\ moG' = moG /\ sC' = sC /\ moC' = moC) mG mC Q) ->
  fsim R mG mC Q.
Proof. intros H sG moG sC moC HR. apply (H sG moG sC moC HR). repeat split; reflexivity. Qed.

Lemma fsim_if {A B} (b : bool) (R : rel) (m1G m2G : M StG A) (m1C m2C : M StC B) Q :
  (b = true -> fsim R m1G m1C Q) -> (b = false -> fsim R m2G m2C Q) ->
  fsim R (if b then m1G else m2G) (if b then m1C else m2C) Q.
Proof. intros H1 H2. destruct b; auto. Qed.

(* [comment removed for export] *)
Lemma fsim_loop {X Y A B} (I : X -> Y -> rel) (Q : A -> B -> rel)
      (bodyG : X -> M StG (X + A)) (bodyC : Y -> M StC (Y + B)) :
  (forall x y, fsim (I x y) (bodyG x) (bodyC y)
     (fun r r' sG moG sC moC => match r, r' with
                                | inl x', inl y' => I x' y' sG moG sC moC
                                | inr a, inr b => Q a b sG moG sC moC
                                | _, _ => False
                                end)) ->
  forall fuel x y, fsim (I x y) (mloop fuel bodyG x) (mloop fuel bodyC y) Q.
Proof.
  intros Hb fuel. induction fuel as [|fuel IH]; intros x y; cbn [mloop].
  - apply fsim_munr.
  - eapply fsim_bind; [apply Hb|]. intros [x'|a] [y'|b]; cbn beta.
    + apply IH.
    + apply fsim_false.
    + apply fsim_false.
    + apply fsim_ret. auto.
Qed.

(* [comment removed for export] *)
Lemma fsim_sys {A B} (nG nC : node) (decG : resp -> option A) (decC : resp -> option B) (R : rel) (Q : A -> B -> rel) :
  (forall sG moG sC moC, R sG moG sC moC ->
     (forall rspG moG' evs a, stepG nG moG rspG moG' evs -> decG rspG = Some a ->
        (evs = [] \/ (debtG sG = [] /\ debtC sC = [])) /\
        exists rspC moC' b, nstep nC moC rspC moC' evs /\ decC rspC = Some b /\ Q a b sG moG' sC moC')
     /\ (forall code moG', nexit nG moG code moG' ->
        debtG sG = [] /\ debtC sC = [] /\ exists moC', nexit nC moC code moC' /\ m_fs moC' = m_fs moG')) ->
  fsim R (msys nG decG) (msys nC decC) Q.
Proof.
  intros H sG moG sC moC HR. destruct (H _ _ _ _ HR) as [HS HX]. split.
  - intros trG a sG' moG' Hp. unfold msys in Hp. apply tpath_enode in Hp. destruct Hp as (rsp & Hst & E).
    destruct (decG rsp) as [a0|] eqn:Ed; [|discriminate]. injection E as -> ->.
    destruct (HS rsp moG' trG a0 Hst Ed) as (Hev & rspC & moC' & b & HstC & EdC & HQ).
    exists trG, b, sC, moC', trG. split; [| split; [|split; [|exact HQ]]].
    + unfold msys. apply tpath_enode. exists rspC. rewrite EdC. auto.
    + destruct Hev as [-> | [-> _]]; [rewrite app_nil_r; reflexivity| rewrite app_nil_r; reflexivity].
    + destruct Hev as [-> | [_ ->]]; [rewrite app_nil_r; reflexivity| rewrite app_nil_r; reflexivity].
  - intros trG Hx. unfold msys in Hx. apply texit_enode in Hx. destruct Hx as (code & moG' & Hex & ->).
    destruct (HX code moG' Hex) as (D1 & D2 & moC' & HexC & Efs).
    exists [ExitEv code (m_fs moC')], [ExitEv code (m_fs moG')]. rewrite D1, D2, Efs. split; [|split; reflexivity].
    unfold msys. apply texit_enode. exists code, moC'. rewrite Efs. auto.
Qed.

End Sim.

Arguments rel StG StC : clear implicits.
