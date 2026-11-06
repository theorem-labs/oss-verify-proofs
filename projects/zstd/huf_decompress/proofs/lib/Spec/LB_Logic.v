(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Monad MSafe StepB.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_Logic () := "c59OSSVerify5KrLib4Spec8LB_Logic3twlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB2NFC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic4liveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB5tliveC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesK47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec5StepB3tnfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic4etwlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic8twl_monoC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00c59OSSVerify5KrLib4Spec8LB_Logic8twl_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic9twl_tliveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic7twl_tnfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe3twfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe4etwfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic4flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic9etwl_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic:etwl_ebindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec5MSafe4assnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic6mspecLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4Spec8LB_Logic=mspecL_conseqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec5Monad4mputC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec8LB_Logic:mspecL_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mwhenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic;mspecL_bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic;mspecL_munrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib4Spec8LB_Logic:etwl_tliveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic8etwl_tnfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec8LB_Logic9pure_treeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe5mspecC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition live (mo : Model) : Z := vm_live_bytes (m_vmmaps mo).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint twl {R} (B : Z) (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => NF n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> live mo' <= B /\ twl B (k rsp) mo' P
  end.

Lemma twl_mono : forall {R} B (t : itree node R) mo (P P' : R -> Model -> Prop),
  twl B t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twl B t mo P'.
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo P P' H HP; cbn -[NF] in *.
  - apply HP. exact H.
  - destruct H as [HN H]. split; [exact HN|].
    intros rsp mo' evs Hst. destruct (H rsp mo' evs Hst) as [HB Hk]. split; [exact HB|]. eapply IH; eauto.
Qed.

Lemma twl_bind : forall {A R} B (t : itree node A) (f : A -> itree node R) mo (P : R -> Model -> Prop),
  twl B t mo (fun a mo1 => twl B (f a) mo1 P) -> twl B (ITree.bind node t f) mo P.
Proof.
  intros A R B t. induction t as [r|n k IH]; intros f mo P H; cbn -[NF] in *.
  - exact H.
  - destruct H as [HN H]. split; [exact HN|].
    intros rsp mo' evs Hst. destruct (H rsp mo' evs Hst) as [HB Hk]. split; [exact HB|]. apply IH. exact Hk.
Qed.

Lemma twl_tlive : forall {R} B (t : itree node R) mo P, twl B t mo P -> tlive B t mo.
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo P H; cbn -[NF] in *; [exact I|].
  destruct H as [_ H].
  intros rsp mo' evs Hst. destruct (H rsp mo' evs Hst) as [HB Hk]. split; [exact HB|]. eapply IH. exact Hk.
Qed.

Lemma twl_tnf : forall {R} B (t : itree node R) mo P, twl B t mo P -> tnf t mo.
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo P H; cbn -[NF] in *; [exact I|].
  destruct H as [HN H]. split; [exact HN|].
  intros rsp mo' evs Hst. destruct (H rsp mo' evs Hst) as [HB Hk]. eapply IH. exact Hk.
Qed.

(* [comment removed for export] *)
Definition etwl {A} (B : Z) (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twl B t mo (fun r mo1 => match r with Unr => True | Ok a => Q a mo1 end).

Lemma etwl_mono : forall {A} B (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwl B t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwl B t mo Q'.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) [] "p'0h03mo1h11ri001rh22H0h31ai011ah41Ah51Bh61Hh72HQh81Qh92Q'h:2moh;1ti021ep;1p;2p;5p;8g00@kR0p4p710R1p10000p4p710p8p200R2g00AbR3p4p710p8P2P1p8g00B]R1j11Tg001^j23TP0j50TP3j82Tg008Og008mf1R3#1'3g009bR0f3R4p-0R5\0R6[f4R7P6[f5R6P7P4f2R4P3D0f6R8P7P3f0R9O2P7P4P3O2[^00]3f7R:#1R;P8P6P7P1f9R<P5P3g00CUR=P8P9P3O2n10110000020010101X00X1;P1P<P5P3P=P6P9P3O2n10110000020010101X00X1;P3P1f8P1f:P5P3P=P:P9P3O2n10110000020010101P1f;P5P4P=P:P9P4O2n10110000020010101[^00P9P9X2=P=\=eX00P:P3P9O2R=P6P4P3P9O3W2P:P4P3O2\=eX00X3<P9O1n10110200020010101X1;G2P:P8P6P7P4D0eW7W6W9W8W:W;W5X42o"). Qed.

Lemma etwl_ebind : forall {A C} B (t : itree node (exc A)) (f : A -> itree node (exc C)) mo Q,
  etwl B t mo (fun a mo1 => etwl B (f a) mo1 Q) -> etwl B (ebind t f) mo Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) [] "p'0h03mo1h11ri001rh21ai011ah32Hah41Ah51Bh61Ch71Hh81Qh91fh:2moh;1ti021ep;1p;2p;5p;3p;8p200R0g00AbR1p4p710p8P0g00D1R2p4p710p8P0g00@kR3p4p710R4p8P0g00DlR5p4p7210p8p201R6g0000R7p4p710p8P6P2p4p7210p8P6P4p8P6P5p4p73110p8g00B]R4j10Tg001^j22TP3j55Tg00E`j13Tg002Tj34TP7j51TP1j88TP2j87TP5j56Tg008Og008mR5f2R2#0'2f3R1%01,25[g009bR7f4R3p-0R8\7[f6R9P3P1f1R:f7R;P9P3P:O1f0R<P2D5X07X29D5%0;R=%09R>f5R?P3P4f8R@%0@RA,25P<%3;945=P?P<O1n10110000020010101X1=P2P4P@P8P:g00CURBP3P<P:O2n10110000020010101X07X1>P=P?P3P2P4f9R>P8P:PB%0>RCP@P9P<O1RDP:P4f;REP8P:PBP;P<P:O2n10110000020010101X07X1CRFD1n10110000020010101X07X1=PAP;P4P>125CP:%3@945APDn10110000020010101P<P4f:RDP8P:PBP9P<P:O2n10110000020010101X07X1AD1X07X2=P<P4P@P4PDP8P:PB%0DRAP>P;P<O1P:P4f<P8P:PBP@P<P:O2n10110000020010101X07X1ARGD1n10110000020010101PAP>P4PE%0ERE,25P2%3D945AP@P<O1n10110000020010101P:PGD1[^07P<g00?\PCP@%3>945CP:PFD1eX3BX07PAP>P;P:O1P<PGD1P<PEPDP@P2O1P:P4f=P8P:PBP>P<P:O2n10110000020010101X07X1ED1eW3X07X2>P<O1n10110200020010101X1=G8G7P9P?P5P;P9P3P1D6P2P:D5eW7W8W:W9W;W5X66X40o"). Qed.

Lemma etwl_tlive : forall {A} B (t : itree node (exc A)) mo Q, etwl B t mo Q -> tlive B t mo.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) [] "p'0h01Ah11Bh21Hh31Qh42moh53mo1h61ri001rh71ti011ap;1p;2p;5p;6p200R0g00FXR1p4p710p8P0g00@kR2p4p710p8P0p100=4p4p710p8g00B]R3j10Tg001^j23TP2j52TP1j61Tg008Og008mf1R1#0'3g009bR2f3R4p-0R5\2[f4R6P4f2R7P1f0R8D2f5#0R9P6P4P7P3f7P5P1g00CUP6P8P1O2n10110000020010101X52X69P8E1W2W3W4W7W1X00o"). Qed.

Lemma etwl_tnf : forall {A} B (t : itree node (exc A)) mo Q, etwl B t mo Q -> tnf t mo.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) [] "p'0h01Ah11Bh21Hh31Qh42moh53mo1h61ri001rh71ti011ap;1p;2p;5p;6p200R0g00GTR1p4p710p8P0g00@kR2p4p710p8P0p100@8p4p710p8g00B]R3j10Tg001^j23TP2j52TP1j61Tg008Og008mf1R1#0'3g009bR2f3R4p-0R5\2[f4R6P4f2R7P1f0R8D2f5#0R9P6P4P7P3f7P5P1g00CUP6P8P1O2n10110000020010101X52X69P8E1W2W3W4W7W1X00o"). Qed.

(* [comment removed for export] *)
Fixpoint flat {R} (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => forall rsp, match k rsp with Ret _ => True | Vis _ _ => False end
  end.

Lemma etwf_flat_etwl : forall {A} B (t : itree node (exc A)) mo (Q : A -> Model -> Prop),
  flat t -> etwf t mo Q -> (forall a mo1, Q a mo1 -> live mo1 <= B) ->
  match t with Vis n _ => NF n mo | Ret _ => True end ->
  etwl B t mo Q.
Proof.
  intros A B t mo Q Hf H HQ HN. destruct t as [r|n k]; cbn -[NF] in *.
  - destruct r; [exact I| exact H].
  - destruct H as [_ Hk]. split; [exact HN|]. intros rsp mo' evs Hst. specialize (Hk rsp mo' evs Hst). specialize (Hf rsp).
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

Lemma mspecL_ret {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecL P (mret a) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ah11Ph21Qh31ah42moh51sh61Hh72HPh83mo'h91pp;1p;2p;4p;3p;5p,2StR0p4p300R1g00L=R2p4p710p8P1p10000p6051002p8P1p100HNp4p710p8P1g00@kR3p6051002R4p8P1p100M1p6051002p8P1p100MmR5p6051002p8P1P5p60521001p8P1g00NjR5p4p7210p8P1g00OGR6p4p710p8P1g00P;R7p605311001R8p8P1p100Dlp4p7210p8P8p100Q4p4p7210p8P8P4p8P8P5p4p710p8p200R4P2p4p7210p8P4P8p8P6j17Tg00Qej26TP2j40j33TP5j31Tg00REj35TP3j52TP7j44Tf0R7%70R3f2R5P3[R2g009bR6f3R8f1R1P7O2P8f5P5P1O3[]4^50f4R9P1P7O2P8P5P1P7O3f7R:/60R;p,1BP0P:f6R:P5C0P1P:f9R:?101A5:01P7O3X86X9;D2eW7X46X50P9P5A3098P1C4eW6X22X13X37X04P8P5P1P7O4W2W1W3X04o"). Qed.

Lemma mspecL_bind {A C} (m : M St A) (f : A -> M St C) (P : assn St) (Q1 : A -> assn St) (Q : C -> assn St) :
  mspecL P m Q1 -> (forall a, mspecL (Q1 a) (f a) Q) -> mspecL P (mbind m f) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "p'0h01pi001ph13mo'h21ai011ah33mo1h41Ah51Ch61Ph71Qh82Q1h91fh:1mh;2H1h<2HPh=2Hfh>2Hmh?2a0h@2mohA1si021shB2s1p;2p;1p;4p;3p;5p;8p;6p200R0g00Q4R1p4p7210R2p8P0g00RbR3p4p7210p8P0g00M1R4p6051002p8P0g00MmR5p6051002p8P0g00NjR6p4p710R7p8P0g00P;R8p605311001R9p8p201R:P2p8P:P3p4p73110p8P:g00@kR2p6051002p8P:P5p60521001p8P:P7p8P:P9p8P1j26Tg00OGj1;TP8j44Tg00QeR8j22TP6j31Tg00REj30TP2j53Tg00SWj45TP4j8:TP5j89TP3j67j58Tp,2StR3f1R5'6R4f2R21632[R6%;3R1f4R9P1[R7f6R;P2P9P5C4f7R<P<f3R=f0R>O1f5R?P>O1P2C4]2g009bR@P;P5P>O2f;RA/23RBf:RC/23RDp,1BREf9RFP2O1RGPFf<RH?13>A0H3>O2X0BP5P<A1H35A0H35P>O3X1@X0DRIPBPEPGP5f8RGf=RJ?135RKA0J35RJP>O3X1@X0B12H3RLPEPCPKPJO2P>PFf>RJ?135A0J35P>O3RKX1@X0LD3X3@X2BP9P2P5P>O3P8PHP312J3R8PEPHf?RL?132A0L32O2P5PAf@RM?135A0M35P>O3X1@X08D3\K^3@P>PHfARHPHP3P2P5C5RK713A0H3KP>O3PCP=P2P5P>O412H3RHPEPLfBRLPLP3P=P2C5RK713A0L3KO2P5PJfCRK?135A0K35P>O3X1@X0HD3eW;X3@XB3X2JP5P>O2n2001100000120101102X?BG:G9PDPEP3PAPCPFPGP2E7P5PID3eW<W@XA3P<P9P3PGP<P;P?D8P2C4eW=W>X77X87X61X96X:4X5:X40P;P?P9P=P2P5P>O7X77W8W6W9W:X5:X40o"). Qed.

Lemma mspecL_conseq {A} (m : M St A) (P P' : assn St) (Q Q' : A -> assn St) :
  mspecL P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecL P' m Q'.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "p'0h02moh11si001sh21Ah31Ph42P'h51Qh62Q'h71ai011ah81mh93mo'h:3mo1h;1pi021ph<1Hh=2HPh>3HP'h?2HQh@2HmhA2a0hB2s1p;2p;1p;4p;3p;8p200R0g00Q4R1p4p7210p8P0g00M1R2p6051002p8P0g00NjR3p4p710p8P0g00P;R4p605311001p8P1j27Tg00OGj16TP4j42Tg00QeR4j24TP3j31Tg00REj30Tg00SWj43TP2j85Tp,2StR2f0R3'7R1%62R5f3R6P5[R7f4R8P5[R9f5R:P6P8f1R;C2g009bR<P:P;P3O2f7R=f2R>P;O2[]0^12f6R?P>P;P3O3P?P6P>P;O3[^0<^12^7=P=P;P3O2f;/42R?p,1Bf:R@P>O1P;f9f=RA?12;RBA0A2;RCP3O3X9<X;?f8RDPBPCP3O3X9<X;?P:P>P;P8P>P;P3O3O3P4f<P2P@f>R4?12;A042;P3O3P@f?RC?12>A0C2>P;O3[^:<P3PAP>P;P3O3P@P6P>P;P3O4W<PAfAR@P@P2P>P;C3RC712A0@2CP3O3PAfBRAPAP2P6P>C3RC712A0A2CP;O3[eX:<XB2X74P;P3O2n2001102000120101100XA?G5W>X0<X12PDP:P=P6C2eW?W=W@X69X57X45X35X81X20P:P8P6P>P;P3O6W6W5X45W3W8X20o"). Qed.

Lemma mspecL_pre {A} (m : M St A) (P P' : assn St) (Q : A -> assn St) :
  mspecL P m Q -> (forall s mo, P' s mo -> P s mo) -> mspecL P' m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ah11Ph22P'h31Qh41mh52moh61sh71Hh82HPh92Hmh:1ap;2p;1p;4p;9p200R0g00Q4R1p4p7210p8P0g00P;R2p605311001p8P0g00T7R3p605311000p8P1j23Tg00OGj12TP2j40TP3l91Tp,2StR3f0R2'3R1%23R4f3R5P4[R6f4R7f2R8P5P2C0g009bR9P7f1R:P2O2f6R;P8P:O2[]5^63P;f5R<P7P5P8P8P:P2P<P8P:P2O3P2W7X59X63X:;M91W8W9X36X24X14X41X00P7P5P8P:P2O5W3X24W1W4X00o"). Qed.

Lemma mspecL_post {A} (m : M St A) (P : assn St) (Q Q' : A -> assn St) :
  mspecL P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecL P m Q'.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ah11Ph21Qh32Q'h41mh52moh61sh71Hh82HQh92Hmh:1ap;2p;1p;4p;9p200R0g00Q4R1p4p7210p8P0g00P;R2p605311001p8P0g00T7R3p605311000p8P1j23Tg00OGj12TP2j40TP3l91Tp,2StR3f0R2'3R1%23R4f2R5P4[R6f3R7P4[R8f4R9P5P7f1R:C0f5R;g009bR<P;P5P:P2O3P;P7P5P:O3[]5^63]:f6R=P;P9P9P7P5P:P=P:P2O2P2W7X5<X63P2M91W8W9X38X26X14X41X00P9P7P5P:P2O5W3W2W1W4X00o"). Qed.

(* [comment removed for export] *)
Lemma mspecL_munr {A} (P : assn St) (Q : A -> assn St) : mspecL P munr Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ah11Ph21Qh32_Hh42moh51sp;1p;2p;4p200R0g00U7R1p4p7210p8P0g00P;R2p605311001p8g00OGj12TP1j21TP2j40Tp,2StR2#2R1f1R3P1[R4g009bf3P3f0R5O2g00?\W3W4X52f2R6P31126P5C0eX24X11X00P6P3P5O3W2W1X00o"). Qed.

Lemma mspecL_false {A} (m : M St A) (Q : A -> assn St) : mspecL (fun _ _ => False) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ah11Qh21mh31Hh42moh53mo'h61ph71sp;2p;1p;3p;5p;4p200R0g00Q4R1p4p7210p8P0g00P;R2p605311001p8P1j26Tg00OGj15Tg00Qej20Tg00Njj31Tg00REj34Tg00@kj52TP2j43Tp,2StR2f0R1'6R3f1R4%52[R5g009bR6g00K`R7P7f6R8/02R9p,1Bf5f3O1f2R:P8f8R8?124A4824P1O3X56X69D2P1n010000000W3W4X72P:P7V6V2P4P1C3eX15X23X00P:P4P1O3W1W2X00o"). Qed.

Lemma mspecL_get (P : assn St) : mspecL P mget (fun s' s mo => s' = s /\ P s mo).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ph12moh21sh32HPh43mo'h51ph62s'p;1p;3p;2p;4p;5g00OGj1;Tg00Ukj30Tg00VEj23Tg0084j42Tg00Qej2:Tg00V_j29j17Tg00Njj35Tg00REj34Tg007Yj21Tg00@kj56Tg00P;j48Tp,2StR0#;R1g009bR2f2R3f1R4f0R5O2A0033f3R6P3P4O21303P5C21:00R7p,1B1903P4A5004A4004R8500f5P8P5O2'1X42X57D6eW3W1X20P0P5%70A0034P6P4P5O2'1X12X20X60C8eX01P5O1W0o"). Qed.

Lemma mspecL_put (P : assn St) (s1 : St) : mspecL P (mput s1) (fun _ s mo => s = s1 /\ exists s0, P s0 mo).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h02s0h11Ph22moh31sh42s1h52HPh63mo'h71pp;1p;3p;2p;4p;5g00OGj1<Tg00Ukj31Tg00WSj20Tg00VEj23Tg00Wmj4;Tg0084j4:Tg00Qej26Tg00XGj34j28Tg00REj35Tg007Yj22Tg00@kj57Tg00P;j49Tp,2StR0#<R1g009bR2f3R3f1R4f0R5O2A1033f5R6P5f2R7O2X00R8,001303P0P8P7P5C;C:g00Y;R8/60R9p,1BA4037P4A5804=106f7P5P4O2X00,00'2X62X79D7eW5W2X30P8P41805A1043P6P5P4O2X00,00'2X22X30V8C9eX40X11P4P5O2X40W1o"). Qed.

Lemma mspecL_upd (P : assn St) (f : St -> St) : mspecL P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h02s0h11Ph21fh32moh41sh52HPh63mo'h71pp;1p;3p;2p;4p;5g00OGj1<Tg00Ukj30Tg007Yj21Tg00VEj23Tg0084j4;Tg00Wmj4:Tg00Qej26Tg00Y[j34j28Tg00REj35Tg00WSj22Tg00@kj57Tg00P;j49Tp,2StR0#<R1P0\0R2g009bR3f3R4f1R5f0R6O2P0f4R7P4O1P7P6O1R8500f5R9P6f2R:O2'1X00P:P4P:O1R;=00;P7P:P5O2130;P6C;C:g00Y;R;/60R7p,1BA404:P5A5;0:f6P6O1500f7P6P5O2'1X00,20X63X77D7eW5W3X40P;P51806A00:8P9P6P5O2'1X00,20X33X40V;C9eX22X11P5P6O2W2W1o"). Qed.

Lemma mspecL_upd' (P : assn St) (Q : unit -> assn St) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspecL P (mupd f) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ph11Qh21fh32moh41sh51Hh62HPh73mo'h81pp;1p;2p;3p;5p;4g00OGj17Tg00Qej26Tg00Y[j30j23Tg00Njj31Tg00REj35Tg00@kj52Tg00P;j44Tp,2StR0#7R1g00Y;R2P1[R3P0\0R4g009bR5f4R6f1R7f0R8O2P6g00ZOf3R9f2R:O1P7O3[]3^40f5P7P8O2P9P:P7P8O31620R;p,1BA006:P7f7A1207A5207P8O3X75X8;D2eW6X35X40P2P91307P:C4eW5X24X13X01P:P7P8O3W2W1W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mspecL_sys {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> NF n mo) ->
  (forall s mo, P s mo ->
     forall rsp mo' evs, nstep n mo rsp mo' evs -> live mo' <= B /\ forall a, dec rsp = Some a -> Q a s mo') ->
  mspecL P (msys n dec) Q.
Proof.
  intros HN H s mo HP. unfold msys, enode. cbn -[NF]. split; [exact (HN s mo HP)|]. intros rsp mo' evs Hst.
  destruct (H s mo HP rsp mo' evs Hst) as [HB HQ]. split; [exact HB|].
  destruct (dec rsp) as [a|]; cbn; [apply HQ; reflexivity| exact I].
Qed.

Lemma mspecL_if {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  (b = true -> mspecL P m1 Q) -> (b = false -> mspecL P m2 Q) -> mspecL P (if b then m1 else m2) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "p'0h02H1h12H2h21Ah31Ph41Qh51bi001bh62m1h72m2p;2p;1p;3p;4p200R0g00Q4R1p4p7210p8P0g00P;R2p605311001p8P1j22Tg00OGj14Tg00Ukj30TP2j41Tg00VEj23Tg00^AR2p,2StR1f1R3'2R4f2R5,21R6%41R7f4R8P7[R9g00^aR:9028f6R;P5P8P3C1[f5R<g00_AR=502f7R>f3R?P8P5C1[P2f0R@=02:f9RAP<P>P8C1[A023=f:RBP;P>P<C1[PBP;P2f;,21P5f8R1P>n0110000020000P<C1]1]0P;A02::P1P8P;P?C1R1[A02:=PAP<P;P8C1R;[P3132:O1W1W0A02=:P1[A02==P;[P@132=O1W1W0n0110000020000P3P@O2W1W0X49X37X76X64X52X20P<P8P?P5P3P@O6W4W3W7W6W5X20o"). Qed.

Lemma mspecL_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  mspecL (fun s mo => P s mo /\ b = true) m1 Q -> mspecL (fun s mo => P s mo /\ b = false) m2 Q ->
  mspecL P (if b then m1 else m2) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "p'0h02moh11sh22H1h32H2h41Ah51Ph61Qh71bi001bh82m1h92m2h:2HPh;3mo'h<1pp;2p;1p;3p;4p;5p200R0g00Q4R1p4p7210p8P0g00@kR2p6051002p8P0g00NjR3p4p710p8P0g00P;R4p605311001p8P1j23Tg00OGj1:Tg00Ukj32Tg007Yj21TP4j40Tg00Qej29TP3j38Tg00REj37TP2j56Tg00VEj25Tg0084j44Tg00^AR2p,2StR3f1R4'3R1f2R5,33R6%:3R7f4R8P7[R9f5R:g009bR;f3R<P4f0R=O2f6R>g00^aR?522'1W0X13P<P=C0P>P8P4P=O2f7R@g00_ARA522'1X0;X13P<P4C0P:P4P=O2P2f;RBf9RCP4P=O2RDA225?'1X0;X13PCP>C0f<f:REP4P=O2A22<A'1X0;X13PCP@C0f=/93RFp,1BP2f>,33P5PBPEn0110000020000P:O1P8PEf?RG?834A7G34P=O3X;;X<FD6]3]2PCPEf8RCP4P=O2RFA22??RG'1X0;X13PCP:C0PBA22?A,1DX0;X13PCP>C0P4P8P<PCP8P<O2RHPGP5152?C4O3W3W2PEA22A?,1FX0;X13PCP:C0PBA22AARB,1DX0;X13PCP>C0P=P8P<PHPBP5152AC4O3W3W2n0110000020000P8P<O2W:X0;X13P@P<P2133CP>P:P8n0110000020000P5C0eW3W2X69X57X96X81X72X40P:P8P<P5P4P=O6W6W5W9W8W7X40o"). Qed.

Lemma mspecL_exI {A X} (P : X -> assn St) (m : M St A) (Q : A -> assn St) :
  (forall x, mspecL (P x) m Q) -> mspecL (fun s mo => exists x, P x s mo) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "p'0h01xi001xh11Ah21Ph31Qh41Xh51mh62moh71sh81Hh92H0h:2HPh;3mo'h<1pp;1p;2p;4p;3p;5p200R0g00Q4R1p4p7210p8P0g00P;R2p605311001p8g00OGj17TP1j26TP2j40Tg00WSR2j21Tg00Qej25Tg00Njj34Tg00REj33Tg00@kj52Tp201R1f0R3p,2StR4#7R5[R6f2R7,64R8f3R9P5[R5f5R:P9P3O1P7f1R;C0^09g009bR<f6R=P=P3P7P;O3X0='1R>P2f7R2P2P3P9P7O3X02f9R?/54R@p,1BP=P9O1P7P2f;RA?44;A3A4;P3O3X;<X<@D2P3P?P3P:f4R@O3P2P;P=P:P3O4W:X0?P;P3O2n2001000000120100000W9W6X74P:P>X6<X74P7P;C0eW8X35X58X26X41X10P@P9P7P;P3O5W3W5W2W4X10o"). Qed.

Lemma mspecL_pure {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
  (phi -> mspecL P m Q) -> mspecL (fun s mo => P s mo /\ phi) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ah11Ph21Qh31mh42moh53phih61sh71Hh82H0h92HPh:4Hphih;3mo'h<1pp;1p;2p;4p;3p;5p200R0g00Q4R1p4p7210p8P0g00P;R2p605311001p8g00OGj17TP1j26TP2j40Tg007YR2j21Tg00Qej25Tg00Njj34Tg00REj33Tg00@kj52Tp,2StR1#7R3p-0R4f2R5,61R6f3R7P3[R8f5R9f4R:P5f1R;C0\5g009bR<f6R=P;f0R>O2/19R?P2f7R2P5P;O2P=f9R@/51RAp,1BP=P7O1P5P2f;RB?41;A3B1;P>O3X;<X<AD2P>P@P:P7O2P2P>P=P9P;O4X:@W9P;P>O2n2001000000120000000W8W4X61P9P?X4<X61P5P;C0eW7X28X36X54X13X00P:P7P5P;P>O5W2W3W5W1X00o"). Qed.

Lemma mspecL_pure_l {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
  (phi -> mspecL P m Q) -> mspecL (fun s mo => phi /\ P s mo) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ah11Ph21Qh31mh42moh53phih61sh71Hh82H0h92HPh:4Hphih;3mo'h<1pp;1p;2p;4p;3p;5p200R0g00Q4R1p4p7210p8P0g00P;R2p605311001p8g00OGj17TP1j26TP2j40Tg007YR2j21Tg00Qej25Tg00Njj34Tg00REj33Tg00@kj52Tp,2StR1#7R3p-0R4f2R5,61R6f3R7P3[R8f5R9f4R:P5f1R;C0\5g009bR<f6R=P;f0R>O2,19R?P2P=f7R2P5P;O2f9/51R@p,1BP=P7O1P5P2f;RA?41;A3A1;P>O3X;<X<@D2P>f8f:P9P:O2P2P;P=P9P>O4W9W:P;P>O2n2001000000120000000W8W4X61P9P?X4<X61P5P;C0eW7X28X36X54X13X00P:P7P5P;P>O5W2W3W5W1X00o"). Qed.

Lemma mspecL_pointwise {A} (P : assn St) (m : M St A) (Q : A -> assn St) :
  (forall s mo, P s mo -> mspecL (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspecL P m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ah11Ph21Qh31mh42moh51sh61Hh72HPh83mo'h92s'p;1p;2p;3p;4p200R0g00Q4R1p4p7210p8P0g00P;R2p605311001p8g00OGj16TP1j25Tg00Ukj30Tg007Yj23TP2j42Tg00VEj21Tg0084j44Tp,2StR2#6R1f1R3,52R4f2R5P1[R6g009bR7f4R8P3f0R9O2f6A0238f3R:9079'3X87X92P8P:C2[]4^52f5P3P9O2P:P5P3P9P5P3A0255A073311251173C4O6W7X47X52P8P:P5P3C2eW6X26X34X11X00P:P5P3P9O4W2W3W1X00o"). Qed.

Lemma mspecL_when (b : bool) (m : M St unit) (P : assn St) (Q : unit -> assn St) :
  (b = true -> mspecL P m Q) -> (b = false -> forall s mo, P s mo -> Q tt s mo) -> mspecL P (mwhen b m) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "p'0h02H1h12H2h22moh31sh41Ph51Qh61bi001bh71mp;2p;1p;3p;4p;5g00Q4j27Tg00OGj16Tg00Ukj30Tg00P;j41Tg00L=j35Tg00VEj22Tg00_aj54Tg00`^j33Tg00^AR0p,2StR1g00Y;R2'7R3%61R4P4\2R5f3R6g00^aR7500P2f2R8P6f1R9C1[f4R:g00_AR;500g009bR<f5R=P9f0R>O2P=g00ZOR?P8P9O3[]2^31[P0A00>7P2P=f6R@P:C1[A009;f8RAP9P>O2PAP?P8P9O3[^2<^31[P2P@P0P3P8f7R@A512?n0110000020000P=C1]1]0P=A0077P2P:P=P6C1RA[A007;P@P9P>O2P@P?P8P9O3[^2<^31R<[P91207O1W1W0A00;7PA[A00;;P<[P2P?P=P:P>120;O1D4W1W0n0110000020000P9P>O2P2P6A31=:P8C1eW1W0X55X44X73X60P6P8P9P>O4W5W4W7W6o"). Qed.

(* [comment removed for export] *)
Lemma mspecL_loop {X R} (body : X -> M St (X + R)) (I : X -> assn St) (Q : R -> assn St) :
  (forall x, mspecL (I x) (body x) (fun r s mo => match r with inl x' => I x' s mo | inr v => Q v s mo end)) ->
  forall fuel x, mspecL (I x) (mloop fuel body x) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "p'0h01si001sh12moh21xi011xh34fuelh41Ih51Qh61Rh71Xh84bodyh91ri021rh:1Hh;2Hbh<2IHh=1ah>1vi031vh?2x'i042x'p;2p;1p;4p;6p;3p;5p;9p200R0g00Q4R1p4p7210R2p8P0g00aSR3p4p7210p8P0g00P;R4p605311001R5p8P0g00bHR6p605311001R7p8p201R8P2p8P8P3p4p73110p8P8P5p8P8g00_aR5p605311000p8P8P7p8P8P6p6054111000p8P8g00cFR7p605311000p8g00dDR2j22TP1j23Tg00OGj19TP4j40TP3j61TP7j3:Tg00L=j34TP5j58TP6l97Tg00dcj16Tg00eBj45Tf1R6p,2StR5f2R7/26'3[R3%95\7R4f4R1f5R9/21R:P7f0R;O1f3R<P;O1g009bR=P2f8R>f7R?p-0R@P7f6RAP;P7P6O3P9P;P7P6O3n200110200021010410103W1X05X9:C0]2g00ecR:P?P9P;O1P5P>P?P6PAP;E1P1C0^2?RBX3:P1P;O1RC=:A<PAPCP5P?PAg00fBP9P;E1P<C0eX2Af9RD/2>REP>P?P;O1P2f:RFPD135FP;P5f;RGPFP1PDP;E1A45F;n200110000021010410102X0EPAP;O1RAP2f<RHPGP@P7PFP;P7P6O3RIPDP;P7P6O3n200110200021010410103X1=X05X9EP9PCP2PFPDPFP2f=PHP@P7PGP;P7P6O3PIn200110200021010410103X1=X05P2PGPF135GP;P5PHPGP9PFP;E1RHA45G;R2n200110000021010410102P?C0P;PCPGPGP7P6P;O3X1=X05PHP>C0eX?GP;O1PGP;PFP7P6P;O3RHX1=X05RCP>P;X:HX1=X05D8PGPCP2P>C0eX>FP;O1n200110000021010110102X=EM97P>PAP5PDP>%67P?P;E1P9C0eX2>X<BX3:P;C5W3W;X54X44X83X68X70P1P<P7P6P;O5X54W4W8X68X70o"). Qed.

Lemma mspecL_seq {A C} (m : M St A) (f : A -> M St C) (P R : assn St) (Q : C -> assn St) :
  mspecL P m (fun _ => R) -> (forall a, mspecL R (f a) Q) -> mspecL P (mbind m f) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "h01Ah11Ch21Ph31Qh41Rh51ah61fh71mh82Hfh92Hmp;2p;1p;4p;9p200R0g00Q4R1p4p7210R2p8P0p100RbR3p4p7210p8P0g00P;R4p605311001R5p8P0g00bHR6p605311001p8p201R7P2p8P7P3p4p73110p8P7P5p8P7P6p6054111000p8P1j21Tg00OGj13TP4j40TP6l92Tp,2StR6f1R4'1R1f2R51165[R3%36R6f4R2P6[R8f6R9P5P2P5V9C0f7R:P:f3R;f5R<f0R=O1P5C0]5f8R>P:P9P<P2P2V>P5P4P4P=O1X5>M92W8W9X38X46X26X63X71X17X00P9P<P2P;P5P4P=O7W3X46W2W6W7X17X00o"). Qed.

(* [comment removed for export] *)
Lemma mspecL_program {A} (P : assn St) (m : M St A) (Q : A -> assn St) s mo :
  mspecL P m Q -> P s mo ->
  forall {C} (f : A * St -> itree node (exc C)),
  (forall a s' mo', Q a s' mo' -> etwl B (f (a, s')) mo' (fun _ _ => True)) ->
  tlive B (ebind (m s) f) mo /\ tnf (ebind (m s) f) mo.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "p'0h01ai001ah13mo'h21Ah31Ph41Qh51mh62moh73mo1h81si011sh92s'h:1Ch;1Eh<2HPh=2HQh>2Hfh?2Hmh@2a0hA1fhB1pi021pp;1p;2p;4p;5p;3p;8p;6p200R0g00Q4R1p4p7210p8P0g00M1R2p6051002p8P0g00MmR3p6051002p8P0g00P;R4p605311001p8P0g00DlR5p4p7210p8p201R6g00@kR7p6051002p8P6P3p60521001p8P6g00faR8p6051001p8P6g00=4R9p4p710p8P6g00g^R:p6051001p8P6g00@8R;p4p710p8P6P5p4p73110p8g00OGj1ATP1j2@TP4j48Tg00QeR4j23Tg00B]j16Tg001^j2:Tg00SWj44TP7j50Tg00Njj32Tg00REj31TP2j87TP3j89TP5j55TP9j4?TP;j3>TP8j6;TP:j6<Tg0084j4=Tp,2StR:#AR8f1R;,@:R9f2R5P8[R3g009bR2f5R7f4R1f3R<P5C8P7P5P;O2f8R=/3:g008mR>%6;':[f9R?P?P5P;f0R@O3P7p,1BRAP1f=RBP:P<P5C4O1P;g00CUV2RCV7D0[^12^9:]0f:RD/3:REP5PAP=f6R=O1RFP;P7PCV5RGPEPAPFP7P?f<RH?2:;A1H:;P@O3X12XBEP1PAP<P;O1P@PCV1D0X72X0EP1P=P7P<O3P4f;R4P:PDA2B:;A1B:;P@O3P=PAP7P5O1P;PCV=D0[^72P@PBf@RDPDP:P5P;C4RH72:A1D:HP@O3f7RHP<P5P;P@O4W=X12X9:X0BP;P@O2n2001102000120100101X@EG7G9P5PAP>PEP5PFP;D5P7PGD0%6<RGPAP>134:P<P?PHO1P5D5RHP=C?A>GH=P<PAPHP=PCV<RCP@E;P<PAPHP=PCP@E<C=b;W>WAX:6W<W?X62X8:X43X59X38X20P7P1P<P5P;P@O6W6X8:W4W5W3X20o"). Qed.

(* [comment removed for export] *)
Fixpoint pure_tree {R} (t : itree node R) : Prop := match t with Ret _ => True | Vis _ _ => False end.

Lemma mspec_pure_tree_L {A} (P : assn St) (m : M St A) (Q : A -> assn St) :
  (forall s, pure_tree (m s)) -> mspec P m Q -> mspecL P m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_Logic ()) ["MSpecL"] "p'0h02Hmh11ri001rh23mo1h32Hph41Ah51Ph61Qh71mh83mo'h91ph:1sh;2HPh<1ai011ah=1ii021ih>1ki031kh?2moh@1ni041ni051ep;1p;2p;5p;3p;4p,2StR0p4p300g00hYR1p6051001R2p8p200R3g0000R4p6051002p8P3g00HNR5p4p710p8P3g00Q4R6p4p7210p8P3g00NjR7p4p710p8P3g00iUR8p4p7210p8P3g00P;R9p605311001p8P3P2p8g00OGj1?TP6j2>Tg00Qej20Tg00B]R6j11TP1j24TP8j5;TP7j32Tg00REj33Tg00IAj4:Tg001^R7j29TP5j45TP4j56Tg002Tj37Tg003Jj48Tg00@kj5=TP9j4<T%?0R9f1R4,>0R5f2R8P9[R1f4R2/00#1P8f0R:O1'4^:0P0P2f3R;P8P4D;g009bR<f6R=P4P:O2P;P8P4P:O3f8R>/00R?P=P8O1P4f7R@f:RA?204A3A04P:O3X8<X9?C:f5R?P;O1f9RB/00#1P@P;O1'4P>P2O1RCg008mRD10A0RE#1'9P7PDf;R7/00#1f<RF/00#1RG/4:f=RH/00#1RIP4P=P6f?R=/00RJp-0RKP4g00K`RLPHf@RH?20:A3H0:P4O3n10110000020010101X2<X1IC5f>RM/00#1RNp,1BROP8P@P610H0RPPKP4g00CURQPMfARR?20:RSA3R0:RTP4O3RUn10110000020010101X2<X1ND6]0]3P:A7DI:,4IPNA7DN4P@P6PPPKP4PLPUn10110000020010101X2<X1NC5P6PJP6PPPKP:PLPMPSPTPAO3RAn10110000020010101P610R0RRPKP4PQP=fBRT?20:RSA3T0:RMP7O3n10110000020010101]0P8g00?\X0LP:X0AX<PP:O1n10110500020010101P:O1%1JRJPOA7DJ8P>P6PRPKP4PQP=PSPMP4O3n10110000020010101X2<X1JD6eW0W3X1GP:O1g00:X19DJ[PDPJP4P:C8,4J%1PRPPDPPP8P4C8PBP610T0RJPKP4PLPHfCRH?20:A3H0:P4O3n10110000020010101X2<X1PC5PL%1JRJPOPDPJP2P;C8P7P6fD/00PKP4PQPTfERT?20:A3T0:P4O3n10110000020010101X2<X1JD6P4n010000000W0W3W>X@DP4P:O2n200110200021010020104103P4P8O2b=PEPOPCP;PBA2F04A3F04P:O3X8<X9ED=eb3b0W;W?X:0P?P2P;P8C<eW0W3X61X75X59X43P;P8P4P:O4W6W7W5X43o"). Qed.
End MSpecL.

Arguments mspecL {St} B {A} P m Q.
