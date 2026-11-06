(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MSafe () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib4Spec5MSafe3twfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes3appc59OSSVerify5KrLib4Spec5MSafe4etwfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe8twf_monoC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c59OSSVerify5KrLib4Spec5MSafe8twf_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe9twf_tsafeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe9twf_tpathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe4assnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe9etwf_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe:etwf_ebindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib4Spec5MSafe5mspecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4Spec5MSafe<mspec_conseqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec5Monad4mputC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec5MSafe9mspec_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mwhenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec5MSafe:mspec_bindC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib4Spec5MSafe;etwf_leavesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint twf {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> twf (k rsp) mo' P
  end.

Lemma twf_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twf t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twf t mo P'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; eauto.
Qed.

Lemma twf_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  twf t mo (fun a mo1 => twf (f a) mo1 P) -> twf (ITree.bind node t f) mo P.
Proof.
  intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
  - exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
Qed.

Lemma twf_tsafe : forall {R} (t : itree node R) mo P, twf t mo P -> tsafe nstep nsafe t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact I|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH. eapply Hk; eauto.
Qed.

Lemma twf_tpath : forall {R} (t : itree node R) mo P tr r mo',
  twf t mo P -> tpath nstep t mo tr r mo' -> P r mo'.
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo P tr r mo' H Hp; cbn in *.
  - destruct Hp as (<- & -> & ->). exact H.
  - destruct H as [_ Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    eapply IH; [eapply Hk; exact Hst| exact Hp].
Qed.

(* [comment removed for export] *)
Definition etwf {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twf t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Lemma etwf_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwf t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwf t mo Q'.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) [] "p'0h03mo1h11ri001rh22H0h31ai011ah41Ah51Hh62HQh71Qh82Q'h92moh:1ti021ep;1p;2p;4p;7g00BER0p4p710R1p1001>p4p710p8p200R2g00C9R3p4p710p8P2P1p8g00D1R1j11Tg004Mj23TP0j40TP3j72Tg009mf0R3#1'3g00:bR0f2R4p-0R5\0R6[f3R7P6[f4R6P7P4f1R7C0f5R8P6P7P3O2P6P4P7O2[^00]3f6R9#1R:P8P6P1f8R;P5P7g00DiR<P9P3P7O2n10110000020010101X00X1:P1P;P5P7P<P8P3P7O2n10110000020010101X00X1:P7P1f7R=P1f9P5P7P<P=P3P7O2n10110000020010101P1f:P5P4P<P=P3P4O2n10110000020010101[^00P3P3X2<P<\<eX00P=P7P3O2R<P8P4P7P3O3W2P=P4P7O2\<eX00X3;P3O1n10110200020010101X1:F2P9P8P6P4C0eW6W5W8W7W9W:X42o"). Qed.

Lemma etwf_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
  etwf t mo (fun a mo1 => etwf (f a) mo1 Q) -> etwf (ebind t f) mo Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) [] "p'0h03mo1h11ri001rh21ai011ah32Hah41Ah51Bh61Hh71Qh81fh92moh:1ti021ep;1p;2p;4p;3p;7p;5p200R0g00C9R1p4p710p8P0g00EFR2p4p710p8P0g00BER3p4p710R4p8P0g00F>R5p4p7210p8p201R6g001>R7p4p710p8P6P2p4p7210p8P6P4p8P6P5p4p73110p8g00D1R4j10Tg004Mj22TP3j45Tg00G2j13Tg005Cj34TP7j41TP1j78TP2j77TP5j56Tg009mR5f1R2#0'2f2R1%01,25[g00:bR7f3R3p-0R8\7[f5R9P3P2f6R:f4R;P2O1f0R<P1C5X07X29C5%0:R=%09R>P;P4f7R?%0?R@,25P<%3:945=P9P<O1n10110000020010101X1=P1P4P?P8P2g00DiRAP;P<P2O2n10110000020010101X07X1>P=P;P1P4f8R>P8P2PA%0>RBP:P<O1RCP2P4f:RDP8P2PAP?P<P2O2n10110000020010101X07X1BREC1n10110000020010101X07X1=P@P4P>125BP2%3?945@PCn10110000020010101P<P4f9RCP8P2PAP:P<P2O2n10110000020010101X07X1@C1X07X2=P<P4P?P4PCP8P2PA%0CR@P?P<O1P2P4f;P8P2PAP>P<P2O2n10110000020010101X07X1@RFC1n10110000020010101P@P4PD%0DRD,25P1%3C945@P>P<O1n10110000020010101P2PFC1[^07P<PAPAP<n010000000PB%3>945BP2PEC1eX3AX07P@P?P2O1P<PFC1P<PDP>P1O1P2P4f<P8P2PAPCP<P2O2n10110000020010101X07X1DC1eW3X07X2>P<O1n10110200020010101X1=F8F7P9P5P:P9P;P3D6P1P2C5eW6W7W9W8W:X56X40o"). Qed.

Lemma etwf_ret : forall {A} (a : A) mo (Q : A -> Model -> Prop), Q a mo -> etwf (Ret (Ok a)) mo Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) [] "h01Ah11Hh21Qh31ah42mop200R0p100BEp4p710p8f0R1g00:bR2f2R3p-0\2[P1P3f1O2P1W1W2W4W3X00o"). Qed.

Lemma etwf_enode : forall {A} n (pl : resp -> option A) mo (Q : A -> Model -> Prop),
  nsafe n mo ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, pl rsp = Some a /\ Q a mo') ->
  etwf (enode n pl) mo Q.
Proof.
  intros A n pl mo Q Hs Hk. unfold etwf, enode. cbn. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

Lemma etwf_leaves : forall {A} (t : itree node (exc A)) mo,
  etwf t mo (fun _ _ => False) -> leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof.
  intros A t mo H. split.
  - intros tr r mo' Hp. pose proof (twf_tpath t mo _ tr r mo' H Hp) as HP. destruct r; exact HP.
  - eapply twf_tsafe. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSpec.
Context {St : Type}.

Definition assn : Type := St -> Model -> Prop.

Definition mspec {A} (P : assn) (m : M St A) (Q : A -> assn) : Prop :=
  forall s mo, P s mo -> etwf (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Lemma mspec_ret {A} (a : A) (P : assn) (Q : A -> assn) :
  (forall s mo, P s mo -> Q a s mo) -> mspec P (mret a) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ah11Ph21Qh31ah42moh51sh61Hh72HPh83mo'h91pp;2p;4p;3p-1g00MOR0p6051100R1p9p10000p4p70P1p8p1002ip4p70P1p8p,2StR2p4p300R3g00NCR4p4p710p8P3g00BER5p6051002R6p8P3p100O7p6051002p8P3p100P0R7p6051002p8P3P7p60521001p8P3g00PjR7p4p7210p8P3P1p8P3g00QGR8p60521001R9p8P3p100F>p4p7210p8P9p100R<p4p7210p8P9P6p8P9P7p4p710p8p200R6P4p4p7210p8P6P9p8p1003Wp4p70P1p8g00Rmj26TP4j45j32TP7j30Tg00SMj31TP5j44TP8j43Tf0R8f2R5P0[R7g00:bR4f3R1f1R9P8O2P1f5P5P9O3[]4^52f4R3P9P8O2P1P5P9P8O3f7R:/62R;P2P:f6R:P5C5P9P:f9R:?029A1:29P8O3X84X9;C4eW7X44X52P3P5A2231P9C3eW6X27X10X38X06P1P5P9P8O4W2X10W3X06o"). Qed.

Lemma mspec_bind {A B} (m : M St A) (f : A -> M St B) (P : assn) (Q1 : A -> assn) (Q : B -> assn) :
  mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (mbind m f) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "p'0h01pi001ph13mo'h21ai011ah33mo1h41Ah51Bh61Ph71Qh82Q1h91fh:1mh;2H1h<2HPh=2Hfh>2Hmh?2a0h@2mohA1si021shB2s1p;2p;4p;3p;7p;6p;5p200R0g00R<R1p4p7210R2p8P0g00SjR3p4p7210p8P0g00O7R4p6051002p8P0g00P0R5p6051002p8P0g00PjR6p4p710R7p8P0g00QGR8p60521001R9p8p201R:P2p8P:P3p4p73110p8P:g00BER2p6051002p8P:P5p60521001p8P:P7p8P:P9p8P1j25TP8j44Tg00RmR8j22TP6j30Tg00SMj31TP2j43Tg00T_j46TP4j7:TP5j79TP3j68j57Tp,2StR3f1R5'5R4f2R21532[R6g00MOR1f4R9P1[R7f6R;P2P9P5C4f7R<P<f3R=f0R>O1f5R?P>O1P2C4]2g00:bR@P;P5P>O2f;RA/23RBf:RC/23RDf9REP2O1RFPEf<RG?03>A1G3>O2X0BP5P<A0G35A1G35P>O3X1@X0DRHPBPFP5f8RFf=RI?035RJA1I35RIP>O3X1@X0B12G3RKPCPJPIO2P>PEf>RI?035A1I35P>O3RJX1@X0KC3X3@X2BP9P2P5P>O3P8PGP312I3R8PGf?RK?032A1K32O2P5PAf@RL?035A1L35P>O3X1@X08C3\J^3@P>PGfARGPGP3P2P5C6RJ703A1G3JP>O3PCP=P2P5P>O412G3RGPKfBRKPKP3P=P2C6RJ703A1K3JO2P5PIfCRJ?035A1J35P>O3X1@X0GC3eW;X3@XB3X2IP5P>O2n2001100000120101102X?BF:F9PDP3PAPCPEPFP2E8P5PHC3eW<W@XA3P<P9P3PFP<P;P?D7P2C4eW=W>X77X87X61X96X:4X5:X40P;P?P9P=P2P5P>O7X77W8W6W9W:X5:X40o"). Qed.

Lemma mspec_conseq {A} (m : M St A) (P P' : assn) (Q Q' : A -> assn) :
  mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P' m Q'.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "p'0h02moh11si001sh21Ah31Ph42P'h51Qh62Q'h71ai011ah81mh93mo'h:3mo1h;1pi021ph<1Hh=2HPh>3HP'h?2HQh@2HmhA2a0hB2s1p;2p;4p;3p;7p200R0g00R<R1p4p7210p8P0g00O7R2p6051002p8P0g00PjR3p4p710p8P0g00QGR4p60521001p8P1j26TP4j42Tg00RmR4j24TP3j30Tg00SMj31Tg00T_j43TP2j75Tp,2StR2f0R3'6R1g00MOR5f3R6P5[R7f4R8P5[R9f5R:P6P8f1R;C2g00:bR<P:P;P3O2f7R=f2R>P;O2[]0^12f6R?P>P;P3O3P?P6P>P;O3[^0<^12^7=P=P;P3O2f;/42R?f:R@P>O1P;f9f=RA?02;RBA1A2;RCP3O3X9<X;?f8RDPBPCP3O3X9<X;?P:P>P;P8P>P;P3O3O3P4f<P2P@f>R4?02;A142;P3O3P@f?RC?02>A1C2>P;O3[^:<P3PAP>P;P3O3P@P6P>P;P3O4W<PAfAR@P@P2P>P;C3RC702A1@2CP3O3PAfBRAPAP2P6P>C3RC702A1A2CP;O3[eX:<XB2X74P;P3O2n2001102000120101100XA?F5W>X0<X12PDP:P=P6C2eW?W=W@X69X57X45X35X81X20P:P8P6P>P;P3O6W6W5X45W3W8X20o"). Qed.

Lemma mspec_pre {A} (m : M St A) (P P' : assn) (Q : A -> assn) :
  mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> mspec P' m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ah11Ph22P'h31Qh41mh52moh61sh71Hh82HPh92Hmh:1ap;2p;4p;9p200R0g00R<R1p4p7210p8P0g00QGR2p60521001p8P0g00U?R3p60521000p8P1j22TP2j41TP3l90Tp,2StR3f0R2'2R1g00MOR4f3R5P4[R6f4R7f2R8P5P2C1g00:bR9P7f1R:P2O2f6R;P8P:O2[]5^63P;f5R<P7P5P8P8P:P2P<P8P:P2O3P2W7X59X63X:;M90W8W9X36X24X14X41X00P7P5P8P:P2O5W3X24W1W4X00o"). Qed.

Lemma mspec_post {A} (m : M St A) (P : assn) (Q Q' : A -> assn) :
  mspec P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P m Q'.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ah11Ph21Qh32Q'h41mh52moh61sh71Hh82HQh92Hmh:1ap;2p;4p;9p200R0g00R<R1p4p7210p8P0g00QGR2p60521001p8P0g00U?R3p60521000p8P1j22TP2j41TP3l90Tp,2StR3f0R2'2R1g00MOR4f2R5P4[R6f3R7P4[R8f4R9P5P7f1R:C1f5R;g00:bR<P;P5P:P2O3P;P7P5P:O3[]5^63]:f6R=P;P9P9P7P5P:P=P:P2O2P2W7X5<X63P2M90W8W9X38X26X14X41X00P9P7P5P:P2O5W3W2W1W4X00o"). Qed.

Lemma mspec_munr {A} (Q : A -> assn) : mspec (fun _ _ => False) munr Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ah11Qh21Hh32moh43mo'h51ph61sp;2p;3p;4p200R0g00V;R1p4p7210p8P0g00QGR2p60521001p8g00Rmj26TP1j35j22Tg00Pjj30Tg00SMj31Tg00BEj44TP2j43Tf0R2g00MO[R1p,2StR3g00:bR4g00DiR5P5f5R6/63R7f39536f2f6f7R6f1R8703A1638P2O3X44X57C4P2n010000000W2W3W6P8P5V4V31238P2C3eX11X00P8P2O2W1X00o"). Qed.

Lemma mspec_false {A} (m : M St A) (Q : A -> assn) : mspec (fun _ _ => False) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ah11Qh21mh31Hh42moh53mo'h61ph71sp;2p;3p;4p200R0g00R<R1p4p7210p8P0g00QGR2p60521001p8P1j25Tg00Rmj24Tg00Pjj30Tg00SMj31Tg00BEj43TP2j42Tp,2StR2f0R1'5R3f1R4g00MO[R5g00:bR6g00DiR7P7f6R8/42R9f5f3O1f2R:P8f8R8?024A1824P1O3X56X69C3P1n010000000W3W4X72P:P7V6V2P4P1C2eX15X23X00P:P4P1O3W1W2X00o"). Qed.

Lemma mspec_get (P : assn) : mspec P mget (fun s' s mo => s' = s /\ P s mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ph12moh21sh32HPh43mo'h51ph62s'p;3p;2p;4p;1g00@Tj30Tg00Voj2:Tg009Rj43Tg00Rmj22Tg00WIj29j16Tg00Pjj38Tg00SMj34Tg0097j21Tg00BEj45Tg00QGj47Tg00MOR0p,2StR1g00:bR2f2R3f1R4f0R5O2A0133f3R6P3P4O21:13P5C31211R71913P4A8114A4114R8501f5P8P5O2'1X42X57C5eW3W1W2P1P5%61A0134P6P4P5O2'1X12X21X61C7eX00P5O1W0o"). Qed.

Lemma mspec_put (P : assn) (s1 : St) : mspec P (mput s1) (fun _ s mo => s = s1 /\ exists s0, P s0 mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h02s0h11Ph22moh31sh42s1h52HPh63mo'h71pp;3p;2p;4g00@Tj30Tg00ANj21Tg00Voj24Tg00X=j43Tg009Rj4;Tg00Rmj2:Tg00XWj39j27Tg00SMj35Tg0097j22Tg00BEj46Tg00QGj48Tg00MOR0p,2StR1g00:bR2f3R3f1R4f0R5O2A0133f5R6P5f2R7O2X01R8,111413P1P8P7P5C3C;g00YKR8/:1R9A9137P4A5814=016f7P5P4O2X01,11'2X62X79C6eW5W2X31P8P41715A0143P6P5P4O2X01,11'2X22X31V8C8eX41X10P4P5O2W4W1o"). Qed.

Lemma mspec_upd (P : assn) (f : St -> St) : mspec P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h02s0h11Ph21fh32moh41sh52HPh63mo'h71pp;3p;2p;4g00@Tj30Tg0097j21Tg00Voj24Tg009Rj43Tg00X=j4;Tg00Rmj2:Tg00Ykj39j27Tg00SMj35Tg00ANj22Tg00BEj46Tg00QGj48Tg00MOR0p,2StR1P1[R2g00:bR3f3R4f1R5f0R6O2P1f4R7P4O1P7P6O1R8501f5R9P6f2R:O2'1X01P:P4P:O1R;=01;P7P:P5O2141;P6C3C;g00YKR;/:1R7A914:P5A5;1:f6P6O1501f7P6P5O2'1X01,21X63X77C6eW5W3X41P;P51716A01:8P9P6P5O2'1X01,21X33X41V;C8eX22X10P5P6O2W2W1o"). Qed.

Lemma mspec_upd' (P : assn) (Q : unit -> assn) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspec P (mupd f) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ph11Qh21fh32moh41sh51Hh62HPh73mo'h81pp;2p;3p;4g00Rmj26Tg00Ykj35j22Tg00Pjj30Tg00SMj31Tg00BEj44Tg00QGj43Tg00MOR0g00YKR1P0[R2p,2StR3P3[R4g00:bR5f4R6f1R7f0R8O2P6g00Z_f3R9f2R:O1P7O3[]3^43f5P7P8O2P9P:P7P8O31613R;A536:P7f7A0137A1137P8O3X75X8;C4eW6X35X43P1P91237P:C3eW5X24X12X00P:P7P8O3W2W1W0o"). Qed.

(* [comment removed for export] *)
Lemma mspec_sys {A} (n : node) (dec : resp -> option A) (P : assn) (Q : A -> assn) :
  (forall s mo, P s mo ->
     nsafe n mo /\
     forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
  mspec P (msys n dec) Q.
Proof.
  intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

Lemma mspec_if {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
  (b = true -> mspec P m1 Q) -> (b = false -> mspec P m2 Q) -> mspec P (if b then m1 else m2) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "p'0h02H1h12H2h21Ah31Ph41Qh51bi001bh62m1h72m2p;2p;3p;4p200R0g00R<R1p4p7210p8P0g00QGR2p60521001p8P1j22Tg00@Tj30TP2j41Tg00Voj23Tg00\UR2p,2StR1f1R3'2R4f2R5,21R6g00MOR7f4R8P7[R9g00]5R:9028f6R;P5P8P3C1[f5R<g00]UR=502f7R>f3R?P8P5C1[P2f0R@=02:f9RAP<P>P8C1[A023=f:RBP;P>P<C1[PBP;P2f;,21P5f8R1P>n0110000020000P<C1]1]0P;A02::P1P8P;P?C1R1[A02:=PAP<P;P8C1R;[P3132:O1W1W0A02=:P1[A02==P;[P@132=O1W1W0n0110000020000P3P@O2W1W0X49X37X76X64X52X20P<P8P?P5P3P@O6W4W3W7W6W5X20o"). Qed.

(* [comment removed for export] *)
Lemma mspec_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn) Q :
  mspec (fun s mo => P s mo /\ b = true) m1 Q -> mspec (fun s mo => P s mo /\ b = false) m2 Q ->
  mspec P (if b then m1 else m2) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "p'0h02moh11sh22H1h32H2h41Ah51Ph61Qh71bi001bh82m1h92m2h:2HPh;3mo'h<1pp;2p;3p;4p200R0g00R<R1p4p7210p8P0g00BER2p6051002p8P0g00PjR3p4p710p8P0g00QGR4p60521001p8P1j23Tg00@Tj32Tg0097j21TP4j40Tg00Rmj29TP3j38Tg00SMj37TP2j46Tg00Voj24Tg009Rj45Tg00\UR2p,2StR3f1R4'3R1f2R5,33R6g00MOR7f4R8P7[R9f5R:g00:bR;f3R<P4f0R=O2f6R>g00]5R?522'1W0X13P<P=C0P>P8P4P=O2f7R@g00]URA522'1X0;X13P<P4C0P:P4P=O2P2f;RBf9RCP4P=O2RDA225?'1X0;X13PCP>C0f<f:REP4P=O2A22<A'1X0;X13PCP@C0f=/93RFP2f>,33P5PBPEn0110000020000P:O1P8PEf?RG?834A7G34P=O3X;;X<FC6]3]2PCPEf8RCP4P=O2RFA22??RG'1X0;X13PCP:C0PBA22?A,1DX0;X13PCP>C0P4P8P<PCP8P<O2RHPGP5142?C5O3W3W2PEA22A?,1FX0;X13PCP:C0PBA22AARB,1DX0;X13PCP>C0P=P8P<PHPBP5142AC5O3W3W2n0110000020000P8P<O2W:X0;X13P@P<P2133CP>P:P8n0110000020000P5C0eW3W2X69X57X96X81X72X40P:P8P<P5P4P=O6W6W5W9W8W7X40o"). Qed.

(* [comment removed for export] *)
Lemma mspec_exI {A X} (P : X -> assn) (m : M St A) (Q : A -> assn) :
  (forall x, mspec (P x) m Q) -> mspec (fun s mo => exists x, P x s mo) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "p'0h01xi001xh11Ah21Ph31Qh41Xh51mh62moh71sh81Hh92H0h:2HPh;3mo'h<1pp;2p;4p;3p200R0g00R<R1p4p7210p8P0g00QGR2p60521001p8P1j26TP2j40Tg00ANR2j22Tg00Rmj21Tg00Pjj35Tg00SMj34Tg00BEj43Tp201R1f0R3g00MOR4[R5p,2StR6f2R7'6R8f3R9P4[R4f5R:P9P3O1P7f1R;C0^09g00:bR<f6R=P=P3P7P;O3X0='2R>P2f7R2P2P3P9P7O3X02f9R?/16R@P=P9O1P7P2f;RA?56;A4A6;P3O3X;<X<@C3P3P?P3P:f4R@O3P2P;P=P:P3O4W:X0?P;P3O2n2001000000120100000W9W6X76P:P>X6<X76P7P;C0eW8X34X58X25X41X10P@P9P7P;P3O5W3W5W2W4X10o"). Qed.

Lemma mspec_pure {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
  (phi -> mspec P m Q) -> mspec (fun s mo => P s mo /\ phi) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ah11Ph21Qh31mh42moh53phih61sh71Hh82H0h92HPh:4Hphih;3mo'h<1pp;2p;4p;3p200R0g00R<R1p4p7210p8P0g00QGR2p60521001p8P1j26TP2j40Tg0097R2j22Tg00Rmj21Tg00Pjj35Tg00SMj34Tg00BEj43Tg00MOR1p-0R3p,2StR4f2R5'6R6f3R7P1[R8f5R9f4R:P5f1R;C0\5g00:bR<f6R=P;f0R>O2/29R?P2f7R2P5P;O2P=f9R@/14RAP=P7O1P5P2f;RB?54;A4B4;P>O3X;<X<AC3P>P@P:P7O2P2P>P=P9P;O4X:@W9P;P>O2n2001000000120000000W8W4X64P9P?X4<X64P5P;C0eW7X28X36X53X11X00P:P7P5P;P>O5W2W3W5W1X00o"). Qed.

Lemma mspec_pure_l {A} (P : assn) (phi : Prop) (m : M St A) (Q : A -> assn) :
  (phi -> mspec P m Q) -> mspec (fun s mo => phi /\ P s mo) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ah11Ph21Qh31mh42moh53phih61sh71Hh82H0h92HPh:4Hphih;3mo'h<1pp;2p;4p;3p200R0g00R<R1p4p7210p8P0g00QGR2p60521001p8P1j26TP2j40Tg0097R2j22Tg00Rmj21Tg00Pjj35Tg00SMj34Tg00BEj43Tg00MOR1p-0R3p,2StR4f2R5'6R6f3R7P1[R8f5R9f4R:P5f1R;C0\5g00:bR<f6R=P;f0R>O2,29R?P2P=f7R2P5P;O2f9/14R@P=P7O1P5P2f;RA?54;A4A4;P>O3X;<X<@C3P>f8f:P9P:O2P2P;P=P9P>O4W9W:P;P>O2n2001000000120000000W8W4X64P9P?X4<X64P5P;C0eW7X28X36X53X11X00P:P7P5P;P>O5W2W3W5W1X00o"). Qed.

(* [comment removed for export] *)
Lemma mspec_pointwise {A} (P : assn) (m : M St A) (Q : A -> assn) :
  (forall s mo, P s mo -> mspec (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspec P m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ah11Ph21Qh31mh42moh51sh61Hh72HPh83mo'h92s'p;2p;3p;4p200R0g00R<R1p4p7210p8P0g00QGR2p60521001p8P1j25Tg00@Tj30Tg0097j23TP2j41Tg00Voj22Tg009Rj44Tg00MOR2p,2StR1f1R3'5R4f2R5P2[R6g00:bR7f4R8P3f0R9O2f6A0138f3R:9079'3X87X91P8P:C1[]4^51f5P3P9O2P:P5P3P9P5P3A0155A073312151273C4O6W7X47X51P8P:P5P3C1eW6X26X34X12X00P:P5P3P9O4W2W3W1X00o"). Qed.

(* [comment removed for export] *)
Lemma mspec_when (b : bool) (m : M St unit) (P : assn) (Q : unit -> assn) :
  (b = true -> mspec P m Q) -> (b = false -> forall s mo, P s mo -> Q tt s mo) -> mspec P (mwhen b m) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "p'0h02H1h12H2h22moh31sh41Ph51Qh61bi001bh71mp;2p;3p;4p;5g00R<j26Tg00@Tj30Tg00QGj41Tg00NCj33Tg00Voj22Tg00^5j55Tg00^nj34Tg00\UR0p,2StR1g00YKR2'6R3g00MOR4P4\2R5f3R6g00]5R7500P2f2R8P6f1R9C1[f4R:g00]UR;500g00:bR<f5R=P9f0R>O2P=g00Z_R?P8P9O3[]2^31[P0A00>7P2P=f6R@P:C1[A009;f8RAP9P>O2PAP?P8P9O3[^2<^31[P2P@P0P3P8f7R@A312?n0110000020000P=C1]1]0P=A0077P2P:P=P6C1RA[A007;P@P9P>O2P@P?P8P9O3[^2<^31R<[P91207O1W1W0A00;7PA[A00;;P<[P2P?P=P:P>120;O1D5W1W0n0110000020000P9P>O2P2P6A41=:P8C1eW1W0X55X44X73X60P6P8P9P>O4W5W4W7W6o"). Qed.

(* [comment removed for export] *)
Lemma mspec_loop {X R} (body : X -> M St (X + R)) (I : X -> assn) (Q : R -> assn) (meas : X -> nat) :
  (forall x, mspec (I x) (body x)
     (fun r s mo => match r with
                    | inl x' => I x' s mo /\ (meas x' < meas x)%nat
                    | inr v => Q v s mo
                    end)) ->
  forall fuel x, (meas x < fuel)%nat -> mspec (I x) (mloop fuel body x) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "p'0h01si001sh12moh21xi011xh34__x1h44fuelh51Hh62Hfh73Hf0h81Ih91Qh:1Rh;1Xh<7__arithh=4__ffh>4__p1h?8__varmaph@5__withA4__x2hB4__x3hC4bodyhD4cstrhE4meashF1ri021rhG2HIhH2HbhI2HmhJ3Hm0hK2IHhL1ahM5cstr0hN5cstr1hO3mo'hP1phQ1vi031vhR2x'i042x'p;2p;4p;6p;1p;3p;7p;5p;9p;<p;8p200R0g00R<R1p4p7210R2p8P0g00_cR3p4p7210p8P0g00QGR4p60521001R5p8P0g00`XR6p60521001R7p8p201R8P2p8P8P3p4p73110p8P8P5p8P8g00^5R5p60521000p8P8P7p8P8P6p605311000p8g00aRR7j2ATP1j2ETg00b1R1j21Tg0097R2j29TP4j43TP3j67j7OTg00bIR3j10Tg00biR4j22Tg00Voj2>Tg00cEj4=Tg00clj1:Tg00dQj28Tg00@nj1hTg007cj1fTg00dmj2BTg00eKj1ZTg00eij1YTg00fTj2HTg00g7j2@Tg00gZj4GTg00\3j1WTg00hEj6VTg00hij2UTg00iKj2TTg00@Tj3STg00j7j3QTg00jVj4MTg00kHR9j15Tg00NCj3FTg00Rmj2LTg00Pjj3PTg00SMj3KTg00BEj4RTg00kgj1jTg00lEj2CTg00lbj2DTg00mKj3JTg00n4j2gTg00n`j3eTg00o@j4bTg00o^j1]Tg010Cj1\Tg010hj3[Tg011Kj4^TP5j5_TP6l9`Tg0126j4aTg012Wl<ITg013<j7cTg013`j8dTg014Dl<XTg014iR6f0R5'>p=4g015GR:P6P1P3P4g015fR;f3R<f2R=f1R>g016HR?g016gR@P5M<Ip=NP>g017ERAg00YKRBPBg017dRCP5g00Z_Fcp=6P6P>g018DP5CGp=;P<PAPBPBPCP=P>P5Gdp=<P:P6P1P3P4P;f5R;f4R4P<P=P>P5M<Ip=?P:P:P6P6P9P3P3P<g018kP=P>P5M<Xp=ip,2StR31A=>'E\>R9g00MO\=R1P:\4RDf6RE/A;RFP<P5O1RGP4P5O1RHg00:bRIP7f9RJf8RKp-0RLP=f7RMP5P=P>O3P;P5O1RNP;P4O1'1'9PEP5P=P>O3n200110200021010410103W1X03XFFC3^2;11H>PJPMP>O1P3f:RHPJP=PKP>E7PEC3[^2KRFX4:11G?P4P>O1RG/1?%0GRO/2@RPPGPO%4O1>6@CNP5C=PPP;P=O1RP#:%0P,8@g019ORP#hRO%fPRG1B6>%Z6RQ%Y6RRP61H6@RSg01:;g01:bRT,@6RUCG,6R%WBRVPR1;US,6RPVPRPAPBPBPCP<EVC<C<1URCRCP5P=g00\URBg00]5RA'>1T5==SBAdAQ6@>CMRAb=b?b@X36X>L18@512>@P<[[^36^>LP5f;RBPJP4O1P3f<RSPBP?PHP4E7PKC3PMP4O1#0P>P=O4b<bDb7W6X2M%5=,1N1ABHRNPHPJP>O1P7PSPB1E3SP5P3f=RWPSP;PBP5E7AF3S5n200110000021010410102X0NPKP>O1RKP7f>RXPWPLP=PSP5P=P>O3RYPHP5O1PHP;O1'1'9PBP5P=P>O3n200110200021010410103X1IX03XFNPMP;P>O1P7PSPBPSP7f?RZPXPLP=PWP5P=P>O3PBP5O1PBPEO1RL'1'9PYn200110200021010410103X1IX03P7PWPS1E3WP5P3PXPWPEPSP5E7R7AF3W5RYn200110000021010410102PJC3P5PWP=P>P5O3PBP=O1/1L'9RLP2PXP<P=P>O3PSP<O1PSPMO1'1fAR2/L3R[P3fBP2PHf@R\P4P<FOP=P\fCR]?P3>AK]3>P5O3XOIXP[CRP5P\P;P4P<O3PZPEO1PZPHO1'1PSPMP\PMO1R[/1W%0[R^%0WR_'2P[P^%4^R`PWP_%4_E?P\PBO1R\,1[%0\R_,2^RaP[P^P`P\P_%4_E?P5C=PaP2PSO1Ra%5XR_'1%0aR\%0XR`%jTR^'C'2R[PaP\%4\P_1C5^X26R_P`O1P_PXP`%4`CiE?PBC=P[%:Z%0Z,8@P]PHO1R[#:%0[,8@fDPZO1RZ#:%0Z,8@%5?R@#5,D61D6@1D6?5J65J6g01;G'g=ePOPGP61B6=P>1B6<CbPQPR%]T,@6RQ%\T,@6RT1H6^5[6';,6RPVPR1;UQ,6RPV1;UT,6RC<C<PCPAb=b?b@X36XA6XB61C>^,2=12><12=<[[^36^A6^B6P5fFR6P2O1#0%0]P6PWO1#0P4P;O5b<bNbMbDb7bJC^PEP;P>O5WIWGP>P5O2n2001000000121000000W5X1IX03PWPLX1IX03P7PHC3R7eP7eXRWP5O1PWP5PSP=P>P5O3R7X1IX03RLPHP5X57X1IX03D_PWPLPYPHC3eXQSP5O1n200110000021110110102XLNM9`PHPKP3PBPH%5<PJP>E7PMC3eW6X2JXKFX4:P5CaX4:WHXEDX91X81XC9X:8X;0P;P4P<P=P>P5O6WEX91W8WCX:8X;0o"). Qed.

(* [comment removed for export] *)
Lemma mspec_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn) (Q : B -> assn) :
  mspec P m (fun _ => R) -> (forall a, mspec R (f a) Q) -> mspec P (mbind m f) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "h01Ah11Bh21Ph31Qh41Rh51ah61fh71mh82Hfh92Hmp;2p;4p;9p200R0g00R<R1p4p7210R2p8P0p100SjR3p4p7210p8P0g00QGR4p60521001R5p8P0g00`XR6p60521001p8p201R7P2p8P7P3p4p73110p8P7P5p8P7P6p605311000p8P1j20TP4j41TP6l92Tp,2StR6f1R4'0R1f2R51065[R6g00MOR3f4R2P3[R8f6R9P5P2P5V9C1f7R:P:f3R;f5R<f0R=O1P5C1]5f8R>P:P9P<P2P2V>P5P4P4P=O1X5>M92W8W9X38X43X23X66X71X17X00P9P<P2P;P5P4P=O7W3X43W2W6W7X17X00o"). Qed.

(* [comment removed for export] *)
Lemma mspec_program {A} (P : assn) (m : M St A) s mo :
  mspec P m (fun _ _ _ => False) -> P s mo ->
  forall {B} (f : A * St -> itree node (exc B)),
  leaves_unreachable_m nstep (ebind (m s) f) mo /\ tsafe nstep nsafe (ebind (m s) f) mo.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafe ()) ["MSpec"] "p'0h01Ah11Ph21ai001ah31mh42moh53mo'h63mo1h71si011sh81Bh91Hh:2HPh;2Hmh<2a0h=1fh>1pi021ph?2s'p;2p;4p;1p;5p;3p;7p200R0g00R<R1p4p7210p8P0g00O7R2p6051002p8P0g00P0R3p6051002p8P0g00QGR4p60521001p8P0g00F>R5p4p7210p8p201R6g00BER7p6051002p8P6P3p60521001p8P6g01<3R8p6051000p8P6p100>4p4p741110p8P6p100LLp4p73110p8P6P5p4p73110p8P1j2<TP4j4;Tg00RmR4j21Tg00D1j12Tg004Mj2:TP5j55Tg00Pjj34Tg00SMj33TP7j40Tg00T_j46TP2j77TP3j78TP8j49Tg00MOR8p,2StR3f1R2'<R7g00:bR5f4R1f3R9f2R:g00DiR;V5R<V3R=V1C;P1P:P2O2f7/13g009mR>%22':[P2P>f8R>/13R?P2f6f5R@O1RAf0RBD5P1P?P2PAPBP1P<V2P?PAP1f:RAP=UA4A32A3A32PBO3X55X>?P9P:P2O1PBP<V9C0X65X2?P9P@P1P:O3P4f9R4P3P@P1P:O1P2P<V@C0\;^65PBf;P;P4P>f@P3P1P9C6O1P:P<V4C0PBn010000000X9;X55X?3W2P2PBO2n2001102000120100101X<?F7F8C9W=X86W:W;X45X73X37X18X00P1P9P:P2PBO5W4X73W3W1X00o"). Qed.

End MSpec.

Arguments assn St : clear implicits.
Arguments mspec {St A} P m Q.
