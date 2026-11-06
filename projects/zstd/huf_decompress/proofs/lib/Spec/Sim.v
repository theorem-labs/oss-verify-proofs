(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Sim () := "c59OSSVerify5KrLib4Spec3Sim3relC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib4Spec3Sim4fsimC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5texitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;tpath_enodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;texit_enodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;tpath_ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;texit_ebindC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Sim;fsim_conseqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01C46Stdlib5Lists4List9app_nil_rI47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib4Spec3Sim9fsim_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Sim8fsim_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Sim9fsim_munrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Sim:fsim_falseC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib4Init9Datatypes4list02".
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
Proof.
ltac2:(KReplay.run1 (kr_t_Sim ()) ["Sim"] "h01Ah11Bh21Qh31Rh42R'h52mCh62mGh73moCh83moGh92sCh:2sGh;1Hh<2H0h=2HRh>1ah?1bp;2p;6p;;p200R0g002KR1p4p7210R2p8P0g0047R3p605611111002p8P0g00F4R4p605611111001p8p201R5P2p8P5P3p6057111111001p8P5P4p6057111111000p8P1j20TP3j62TP4l;1Tg0000R4p,3StGR3f3R1'0R2p,3StCR6/01R7f5R8P4\8[R9f6R:P8f4R;f2R<f1R=f0R>E2g00DJR?f8R@P1P<P=P>O4f:P;P1P<P=O4[^7?^96]8^:3P@f7P:P8P;P1P<P<P=P>P@P8P;P1P<P=P>O6P>W<X7?X96X8?X:3X?@X>@M;1W=W;X29X57X62X44X34X15X00P:P8P;P1P<P=P>O7W2W5W6X44W3X15X00o"). Qed.

Lemma fsim_post {A B} (R : rel) (mG : M StG A) (mC : M StC B) (Q Q' : A -> B -> rel) :
  fsim R mG mC Q -> (forall a b sG moG sC moC, Q a b sG moG sC moC -> Q' a b sG moG sC moC) -> fsim R mG mC Q'.
Proof.
ltac2:(KReplay.run1 (kr_t_Sim ()) ["Sim"] "h01Ah11Bh21Qh32Q'h41Rh52mCh62mGh73moCh83moGh92sCh:2sGh;1Hh<2H0h=2HQh>1ah?1bp;2p;6p;;p200R0g002KR1p4p7210R2p8P0g0047R3p605611111002p8P0g00F4R4p605611111001p8p201R5P2p8P5P3p6057111111001p8P5P4p6057111111000p8P1j20TP3j62TP4l;1Tg0000R4p,3StGR3f2R1'0R2p,3StCR6/01R7f4R8P4\8[R9f5R:P4\:[R;f6R<P:P8f3R=P1f1R>E2f7R?g00DJR@f8RAP:P8P=P1P>f0RBO6PAP<P:P8P=P1P>O6[^7@^96]8^:3^??]>PAP?P<P<P:P8P=P1P>f:P=P1P>PBO4PBW<X7@X96X8@X:3PBM;1W=W;X3;X29X57X62X44X15X00P<P:P8P=P1P>PBO7W3W2W5W6W4X15X00o"). Qed.

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
Proof.
ltac2:(KReplay.run1 (kr_t_Sim ()) ["Sim"] "h01Ah12A'h21Bh32B'h41Qh51Rh62R1h71ah81bh92kCh:2kGh;2mCh<2mGh=2H1h>2H2p;2p;6p;=p200R0g002KR1p4p7210R2p8P0g0047R3p605611111002R4p8P0p100IVR5p4p7210R6p8P0g00ShR7p605611111003p8p201R8P2p8P8P3p6057111111001R9p8P8P6p8P8P7p6057111111002p8p202R6P2p8P6P4p8P6P5p4p73110R5p8P6P7p60581111111001p8p203R4P2p8P4P9p8P4P5p8P4P7p605911111111000p8P1j20TP3j61TP7l=2Tg0000R7p,3StGR3f5R1'0R5p,3StCR9/01R2f7R:f6R;,03[R3109;\:R9P7\:\:R<f:R=f9R>P;f4R?f3R@P:V=V=E1f;RAPAP=f8RBP1f1RCO1P?f0RDO1P@E1^8A]7f<REPAP=P>PBP;P1P>VEVEP?P@f2RAPCPAPCPDO2X8EX7EM=2W>W=X4<X99X:3X;2X<5X67X57X34X16X28X00P=P>PBP:P;P1P?P@PAPCPDO;W4W9W:W;W<X67W5X34X16X28X00o"). Qed.

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
Proof.
ltac2:(KReplay.run1 (kr_t_Sim ()) ["Sim"] "h01Ah11Bh21Qh31Rh42mCh52mGh63moCh73moGh82sCh92sGh:1Hh;2HRh<4moC'h=4moG'h>3sC'h?3sG'p;2p;3p;6p;4p200R0g002KR1p4p7210R2p8P0g0047R3p605611111002p8p201R4P2p8P4P3p6057111111001p8P1j25Tg00?Dj30Tg00>ij21TP3j64Tg00HAj22Tg00@>j43Tg0000R3p,3StGR1f2R2'5R5p,3StCR6/52R7f4R8P3\8[R9g00DJR:f7R;f3R<P2f1R=f0R>O4f:f9f8R?901<A0:2;f6R@906=f5RA90:>'1'1'1X<:X>6X=:X?1P;P@PAE4[^6:^86]7^91P?P<P2P=P>O4PAP8P<P2P=P>P8P<P2P=A0188A0:<<R?A0622R;A0:==RB'1RC'11218P?PC12:<P;PB126212:=C3C3C3O:W;X6:X86X7:X91P@PAP8P<P2P=E4eW:X29X47X55X33X14X00PAP8P<P2P=P>O6W2W4W5W3X14X00o"). Qed.

Lemma fsim_if {A B} (b : bool) (R : rel) (m1G m2G : M StG A) (m1C m2C : M StC B) Q :
  (b = true -> fsim R m1G m1C Q) -> (b = false -> fsim R m2G m2C Q) ->
  fsim R (if b then m1G else m2G) (if b then m1C else m2C) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_Sim ()) ["Sim"] "p'0h02H1h12H2h21Ah31Bh41Qh51Rh61bi001bh73m1Ch83m1Gh93m2Ch:3m2Gp;2p;3p;6p200R0g002KR1p4p7210R2p8P0g0047R3p605611111002p8p201R4P2p8P4P3p6057111111001p8P1j22Tg00?Dj30TP3j61Tg00HAj23Tg00X;R3g0000R1p,3StGR2f3R5'2R6f4R7,22R8p,3StCR9/27R:f5R;,29R<f7R=P1\=[R>f6R?g00X[R@503f9RAf8RBP?P;P5f1RCE1[g00Y;RD903=f:REPAP=P;P5f2RFE1[P3f0RG=03@f<RHf;RIPAPBP?P7E1[A03CDf=RJPHPEPBP?P;E1[PJPHPEP3f>,22PFPAPBn0110000020000P3129JPFP=P?n0110000020000P;E1]1]0PBA03@@PIPEPBP=P;P5E1RE[A03@DPHPIPAP=P;P7E1RA[PC133@O1W1W0A03D@PE[A03DDPA[PG133DO1W1W0n0110000020000PCPGO2W1W0X4>X9<X7:X:8X86X51X63X34X20PBP=P?P;P7P5PFPCPGO9W4W9W7W:W8W5W6X34X20o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_Sim ()) ["Sim"] "p'0h03moCh13moGh22sCh32sGh41xi001xh51yi011yh61bi021bh74fuelh81Ah91Bh:1Ih;1Qh<1Xh=1Yh>2b0h?5bodyCh@5bodyGhA1ri031rhB2r'i042r'hC1si051shD2y'i062y'hE1HhF2HbhG2IHhH1ai071ahI2a0hJ2x'i082x'i092y0p;2p;6p;5p;3p;7p;=p;1p;4p200R0g002KR1p4p7210R2p8P0g0047R3p605611111002R4p8P0g00Y[R5p4p7210R6p8P0g00ShR7p605611111003R8p8p201R9P2p8P9P3p6057111111001R:p8P9P6p8P9P7p6057111111002R6p8p202R;P2p8P;P4p8P;P5p4p73110R4p8P;g00ZPR<p605611111001p8P;P8p8P;P7p60581111111001p8P;g00[FR8p605611111001p8P;g00\=R=p605611111001p8p203R>P2p8P>P:p8P>P4p8P>P<p6057111111000p8P>P6p8P>P7p605911111111000p8P>P8p6057111111000p8P>P=p6057111111000p8g00]5R6j23TP1j24TP3j61TP5j60Tg00T_j2;TP8j5:Tg00Fmj32TP=j55TP<j78TP7l=7Tg00]Tj16Tg00^3j49Tf3R7g0000R<\7[R=f2R8P<\8[R<f5R5p,3StGR3f6R1f4R4'3R:'4[R2p,3StCR?/4:\5R:f7R@f9RA/3@RBf8RC/31P5f1RDf0REO2RFP7PDO1P8PEO1g00DJRGP6f?RHf=RIp-0RJP5P6PHPIPJP5PIPDPEP5P4P7P8O6g00I9RKn200110400021010610102P6PHPIPJP5PKf<RLPDPEP5P4P7P8O6n200110400021010910102n200110300021010810107X0GX2?W1X33XBBXABE1^5@]4g00^TRBf:RMPMPAPCPDPEO2P3PLPMP8P1PDE0P?f;RNPAP8P5PEE0P@E1^5M]4ROX7BPAPCP@PDPEO2RP1;?CP1D:PAPCPPP3PNPAg00_3RPP5PDE0P?PMPCPPP4PEE0P1E1eX5AX4A13INRP13LMRQPNPMPAPDPEO2RRP@PDO1P1PEO1P6fCRSfARTPJP5P6PSPTPJP5PTPDPEP5P4P7P8O6RUPKn200110400021010610102P6PSPTPJP5PKf@RVPDPEP5P4P7P8O6n200110400021010910102n200110300021010810107X0GX2?X1GX33XBPXAPP6f>RWPL143IPEP3PHPIP5PAPEE0A23IEn200110500021010810103XCPP6PIPN14?LPEP?PWPLP5PCPEE0A2?LEn200110500021010810103XCQPCPFP6PWPL13WLPWPIP6fDRFfBRQPJP5P6PFPQPJP5PQPDPEP5P4P7P8O6PKn200110400021010610102P6PFPQPJP5PKPUn200110400021010910102n200110300021010810107X0GX2?X1GX33P6PVPW143HPDP3PTPHP@PNPEE0A23HEn200110500021010810103P6PHPI14?WPEP?PVPWP@PMPEE0A2?WEn200110500021010810103PNE1]6PE13HIRUP6PVPWPVPHP6fERFPSPJP4PSP@PEP4P7P8PDO6PKn200110400021010610102X0GX2?X1GX33P3PQPVPCPLP8E0P6PTPH14?VPEP?PQPVPAPLPEE0RXA2?VERYn200110500021010810103RZPIE1PEPCP7PEO2PTPVPSP@P4P7P8PDPEO6X0GX2?X1GX33P3PSPTPAPIP7E0RAPXPWE1eXDTPEO1PTPVPAPYPWD5PTPVPKX0GX2?X1GX33R[PAPYPWE1eX6HPEO1n200110500021010110102W>XJHPEO1P6PVPWPVPHP6PFPSPJP4PKPQP@PEP4P7P8PDO6n200110400021010910102X0GX2?X1GX33A23V8PZPIE1PEPTPVA23T7RZPXPWD5PTPVP[PZPXPWE1eXDTPEO1PTPVPQP@P4P7P8PDPEO6RQX0GX2?X1GX33RXP7PEPWPEXEQX0GX2?X1GX33F8PTPVPXPZPYPWE1eX6HPEO1n200110500021010110102X>UXHIPEO1n200110500021010010107XIPM=7PNPMPRP3PIPN%67RIP@PDE0P?PLPMPIP1PEE0PCE1eX5NX4NXGOX7BPEC9W7WFX?:X@2X;<X:=X9>X8;X=9X<0P@P1P5P4P7P8PDPEO8W?W@W;W:X9>X8;X=9X<0o"). Qed.

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
