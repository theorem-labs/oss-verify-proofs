(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Monad MSafe StepB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Keeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MSafeP () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib4Spec6MSafeP6nstepPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB7nf_nodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec5StepB2NFC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K59OSSVerify5KrLib3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums8positive03K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec5MSafe3twfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP4twfPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB3tnfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP<nstepP_of_NFC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe9twf_tsafeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP=twfP_transferC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib4Spec6MSafeP5etwfPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe4etwfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP8twf_twfPC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c59OSSVerify5KrLib4Spec6MSafeP9twfP_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP9twfP_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Keeps4tallC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec5MSafe;etwf_leavesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP9twfP_conjC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP:twfP_pathsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec5MSafe4assnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP:twfP_tpathC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP:etwf_etwfPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP:etwfP_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP;etwfP_ebindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP:etwfP_tallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP6mspecPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe5mspecC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4Spec6MSafeP=mspecP_conseqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mputC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec6MSafeP:mspecP_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mwhenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mloopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6MSafeP;mspecP_bindC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3sum00C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init5Logic7and_indc59OSSVerify5KrLib4Spec6MSafeP<etwfP_leavesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition nstepP (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo rsp mo' evs /\ (nf_node n -> errno_of (eff_ret rsp) = None).

Lemma nstepP_nstep : forall n mo rsp mo' evs, nstepP n mo rsp mo' evs -> nstep n mo rsp mo' evs.
Proof. intros n mo rsp mo' evs [H _]. exact H. Qed.

Lemma nstepP_of_NF : forall n mo rsp mo' evs, NF n mo -> nstep n mo rsp mo' evs -> nstepP n mo rsp mo' evs.
Proof.
  intros n mo rsp mo' evs HN Hst. split; [exact Hst|]. intros Hn.
  destruct n; cbn in Hn; try contradiction; exact (HN _ _ _ Hst).
Qed.

Lemma nstepP_other : forall n mo rsp mo' evs, ~ nf_node n -> nstep n mo rsp mo' evs -> nstepP n mo rsp mo' evs.
Proof. intros n mo rsp mo' evs Hn Hst. split; [exact Hst|]. intros H. exfalso. exact (Hn H). Qed.

Lemma tpath_nstep_of_nstepP : forall {R} (t : itree node R) mo tr r mo',
  tpath nstepP t mo tr r mo' -> tpath nstep t mo tr r mo'.
Proof.
  intros R t. induction t as [x|n k IH]; intros mo tr r mo' Hp; cbn [tpath] in *; [exact Hp|].
  destruct Hp as (rsp & mo1 & evs & tr' & [Hst _] & Hp & ->). exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [apply IH; exact Hp| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint twfP {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstepP n mo rsp mo' evs -> twfP (k rsp) mo' P
  end.

Lemma twf_twfP : forall {R} (t : itree node R) mo P, twf t mo P -> twfP t mo P.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P H; cbn in *; [exact H|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs [Hst _]. apply IH. eapply Hk. exact Hst.
Qed.

(* [comment removed for export] *)
Lemma twfP_transfer : forall {R} (t : itree node R) mo P, twfP t mo P -> tnf t mo -> twf t mo P.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P H HN; cbn in *; [exact H|].
  destruct H as [Hs Hk]. destruct HN as [HNF HNk]. split; [exact Hs|]. intros rsp mo' evs Hst.
  apply IH; [| exact (HNk _ _ _ Hst)]. apply (Hk rsp mo' evs). apply nstepP_of_NF; assumption.
Qed.

Lemma twfP_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twfP t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twfP t mo P'.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "h03evsh13mo'h23rsph31Ph42P'h52moh61rh71Hh82HPh91th:2Hkh;2Hsh<3Hsth=2IHh>1Rh?1kh@3mo1hA1np;2p;4p;3p;1p;5p;6p200R0g00JXR1p4p7210p8P0g00QDR2p4p710p8g00LDj23TP2j40Tg00M:j35Tg00N0j44Tg00R9j22Tg001<j19Tg001\j51Tg00:^R2j28Tg00HJj47TP1j66Tg007JR1f0R3'3P1f1R41314g008?R5f3R6p-0\5R7[R8f4R9P7[R:f5R;P6f2R<P4C0f6R=P9P4P3O2P9P<P4O2[^@5R>]6R?f7R@P;P9P<C0[[]4]3]5W9P;A51;6P<P4C0P3P;P9P4O3P@A51@;P9P<C0eX8?W7X4:X38X55X64g0095R81316[P7\;R:P7\=R7P@P9P6O1P<P4C0f8R?P>]6R>f9RAP=P;O1P9P<C0[[]4]3^55\8P@P1P@P;P9C4P<P4C0P212@9g009h#9R2f:RBP@P<P4P3D1f=RCPBP6O1P<P@C0[]0^15^2812?;f;R;P?P<P4P3D1f>RDP;P6O1P<P@C0[^02^15^28'8P412A=PCPBP<P4P3D1f@PCP6O1P<PBC0[^02^15^2812;?PDP;P<P4P3D1REfAPDP6O1P<PBC0[^02^15^28P4PCP6P<P;PBP9P6P<P4P3O4P?O6X<EX02X15X28C7W:W;P4P3O2n2001000000120000000PAP1PAP@P=C4P9P<C0eX8>W7X47X3:X55W=W?XA1P3E6W9X>0o"). Qed.

Lemma twfP_conj : forall {R} (t : itree node R) mo (P1 P2 : R -> Model -> Prop),
  twfP t mo P1 -> twfP t mo P2 -> twfP t mo (fun r mo1 => P1 r mo1 /\ P2 r mo1).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "h03evsh13mo'h23rsph31rh42P1h52P2h62moh73mo1h82H1h92H2h:1th;3Hk1h<3Hk2h=2Hsh>3Hsth?2IHh@1RhA2_HhB1khC1np;2p;4p;3p;1p;5p;6p200R0g00JXR1p4p7210p8P0g00QDR2p4p710p8g00LDj25TP2j40Tg00:^R2j23Tg00M:j34Tg00HJj47Tg00N0j46Tg00R9j22Tg001<j19Tg001\j51TP1j68Tg007JR1f0R3'5P1f1R41514g008?R5f3R6p-0\5R7[R8f4R9P7[R:f5R;P6f2R<P4C0f6R=P9P6P4C0f7R>P;P9P;P4P3O2P9P4P3O2'3X75R?X3>R@C0[[]5]4]6W:P;A41;6P<P4C0P=A41=9P6P4C0P6P;P9O2P<P;P9O2P4P3C7P>A41>;P9P@C0eW9W8X5:X48X65X34g0095R81516[P7\;R:P7\=R7P>P9P6O1P<P4C0f8R@P;P9O1P6P4C0f9RAP=P;O1P9P?X3AR?C0[[]5]4^65\8P>P1P>P;P9C6P<P4C0P@P1P@P=P;C6P6P4C0P212>9g009h#9RBf:RCP>P<P4P3D1f=RDPCP6O1P<P>C0[]0^15^2812@;f;REP@P<P4P3D1f>RFPEP6O1P<PCP4P3O2PAP4P3O2'3X75X3FC0[^0B^15^28'3P412A=PDPCP<P4P3D1f@RGPDP6O1P<PCC0[^0B^15^28P212E@PFPEP<P4P3D1fAREPFP6O1P<PCC0[^0B^15^28f<R2/2Af?RHP2P<P4P3D1fBRIPHP6O1P<PFP4P3O2PDP4P3O2'3X75X3IC0[^0B^15^28'3P912DCPEPFP<P4P3D1fDPEP6O1P<PDC0[^0B^15^2812H2PIPHP<P4P3D1R2fERDPIP6O1P<PEP4P3O2PGP4P3O2'3X75X3DC0[^0B^15^28P;PEP6P<PHPFP@P6P<P4P3O4P9P6P<P4P3O4O6X>2X0BX15X28C7W<WAP4P3O2n2001000000120000000W;W=P4P3O2n2001000000120000000PAP1PAP>P=C6P9P?C0eW9W8X57X4:X65W?WBXC1P3E8W:X@0o"). Qed.

(* [comment removed for export] *)
Lemma twfP_paths : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twfP t mo P -> (forall tr r mo', tpath nstepP t mo tr r mo' -> P r mo' -> P' r mo') -> twfP t mo P'.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "h03mo'h13evsh21rh33rsph42trh51Ph62P'h72moh83tr'h91Hh:2HPh;3mo1h<1th=3HPrh>2Hkh?2Hph@2HshA3HsthB2IHhC1RhD1khE4mo''hF1np;2p;4p;1p;3p;5p;6p;8p200R0g00JXR1p4p7210p8P0g00QDR2p4p710p8P0g00KPR3p4p73110p8g00LDj2<TP2j40Tg001<j1>Tg00M:j3=Tg00T]j1BTg0070j34Tg00:^R2j21Tg00O@j29Tg00HJj47Tg00N0j4;Tg00R9j28Tg001\R4j53Tg00Nfj26Tg00OZj4:TP1j6ATP3j8@Tg00P4j3?Tg007JR3P4f5R4f4R1f3R5f2R6f1R7f0R8G@p=2g009hR9??78p=51<38P3P71<37g008?R:p-0\:R;\5R<P;\1R=P4P5P6P7C0%>9R>f7R?f9R@P?f6RAP6P7P8E2PAP6P7O2PAP5P6O2[RB[^0:]2]4P?P4P1P6C0[[]6]5]7W<P4A=345P6P7C0P@A=3@?PAP6P7P8E2PB[^0:^2?^4>P8%B9R9P4P1A4?44A4:11RCA4>99RD'119?4PCPD19:119>9C7C7P7O5P?A=3?4P1P6C0eW:W9X6=X5<X7:X27g0095R<1<35[P;\4R=P;\AR;P?P1P5O1P6P7C0f;R9f8RDP?O1PAP6P7P8E2PB[^0:^2@^4>P@PAP4O1P1P6C0[[]6]5^7:\<P?P3P?P4P1C;P6P7C0P9P3P9P@PDC;PAP6P7P8E2PB[^0:^2@^4>P218?1f:R2P?P6P7P8D3f=RBP2P5O1P6P?C0[^1>^0:^3<18D4P9PDP6P7P8D3f>RCP9P5O1P6P?C0[^1>^0:^3<'1P718@APBP2P6P7P8D3f@PBP5O1P6P2C0[^1>^0:^3<189DPCP9P6P7P8D3REfARFPCP5O1P6P2C0[^1>^0:^3<P7PBP5P6P9P2P1P5P6P7P8O4fBRCfDRGPFPAO1P4P6P7P8E2f?P6P7O2PB15A1RBP5P6P<fHRHfERIP5P6P7D3fJfGRJP5O1P6P8P?PAE2152D1578RK54>'1'1X8>,6>X1>,6>X;:,6:X3<PDP:PJPGP9P6P7D3fIfFRLP9O1P6P8PAP4E215@?=4>K'1'1X8>,6>X1>,6>X;:P?P>PLfCR9P2P@P7D3PHPIP2O1P@P8P4P1E215DA=4>K'1'1X8>,6>X1>PAP>PIPCP@PDP?D3PJPGP@O1PDP8P1P5E215?415?854>'1'1X8>P1PGPFPDP?PAD3PLP9PDO1P?P1P5P6E2R5A4>BBRD'1P4P5PDP719>BC7C7C:C:C:C:P8O5W=W?XE:W2X4>O6XAEX1>X0:X3<C7W>W@P7P8O2n2001000000121000000P@P3P@P?PAC;P1P6C0eW:W9X6;X5=X7:WBWDXF3P8EAW<XC0o"). Qed.

Lemma twfP_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
  twfP t mo (fun a mo1 => twfP (f a) mo1 P) -> twfP (ITree.bind node t f) mo P.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "h03evsh13mo'h23rsph31Ph41ah51fh62moh73mo1h81Hh91th:1Ah;1Bh<2Hkh=2Hsh>3Hsth?2IHh@1khA1nhB1rp;2p;4p;3p;1p;5p;6p200R0g00JXR1p4p7210p8P0g00QDR2p4p710R3p8P0g00U=R4p4p7210p8p201R5P3p8P5P4p4p73110p8g00LDj22TP2j40Tg00M:j35Tg00N0j46Tg00R9j24Tg001<j1;Tg001\j53Tg00:^R2j2:Tg00HJj49TP1j67TP4j58Tg007JR4f3R1f2R3f1R6f0R7D8p=11246P4P312431241\1R8g008?R9f4R:p-0\9R;[R<f6R=P1P6f7R>P:P6O1R?P7P3C0X79X4=R@C0P=P>P=P:P1C1P3P6C0[]3]6]5W9P=A54=1P6P@C0P7P=P>P=A54>:P1C1P3P6C0eW8X3<X69X58XB3g0095R8124:[f5R<124<[R@P;\=R;f8RAP:P1O1P6f9RBP?P7P3C0X79X4AR?C0PAPBPAP<P:O1P1C1P3P6C0[]3^69]5\8PAP4PAP<P:C6P6P?C0P214=3g009h#;R2PBP<P3P6P7D3f=R?PBP1O1P3f>RCPBP6O1P7P>C0X79X4?C0[]0^19^2814>1f:R>P=P3P6P7D3P?PCP?P>P1O1PAC1P3P=C0[^02^19^28':P714A:f<RCPAP3P6P7D3f@RDPCP1O1P3fAREPCP6O1P7P>C0X79X4DC0[^02^19^2814>=P?PBP3P6P7D3R>PDPEPDP?P1O1f;R?C1P3PBC0[^02^19^28P6PCP1P?P3PBP:P1P3P6P7O4O5X>>X02X19X28C9W<W=P6P7O2n2001000000120000000PAPBPAP4PBP=P<C6P1C1P3P6C0eW8X3;X69X5@W?W@XA4P7E7W9X;5X:0o"). Qed.

Lemma twfP_tsafe : forall {R} (t : itree node R) mo P, twfP t mo P -> tnf t mo -> tsafe nstep nsafe t mo.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "h01Hh12HNh21Ph31Rh42moh51tp;2p;4p;3p;6p;5p200R0g00V0R1p4p710p8P0g00QDR2p4p710p8P0g00ViR3p4p710p8P0g00RmR4p4p710p8P0p100Wgp4p741110p8g00LDj24TP2j43TP4j30TP3j61TP1j52Tg007Jf0R1'4g008?R3f2R4p-0\3[f3R3P4f1R2P1C3f4R5?034f5R6P5P3P4P6P5P3P4P2P1E1D2W1W0W2W4W5X30o"). Qed.

Lemma twfP_tpath : forall {R} (t : itree node R) mo P tr r mo',
  twfP t mo P -> tpath nstepP t mo tr r mo' -> P r mo'.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "p'0h03evsh13tr'h21Hh33mo'h41rh52H0h61Ph72moh83mo1h93rsph:2trh;2Hph<2_Hh=1th>2Hkh?3Hsth@2IHhA1RhB1khC1nhD2r0i001xp;2p;1p;4p;3p;6p;5p;8p200R0g00X[R1p4p710p8P0g00JXR2p4p7210p8P0g00QDR3p4p710p8P0g00KPR4p4p73110p8g00LDj29Tg001<j1DTP3j46Tg00M:j3>Tg0070j30Tg00T]j1BTg00:^R3j28Tg000^j6@TP1j6?Tg00N0j4;Tg00R9j2:Tg001\R1j57Tg00NfR5j21TP2j6CTP4j8=Tg00P4j3ATg007JR4P1f5R2f4R6f3R7f2R8f1R9f0R:G=p=5A089:,87p=<g009hR;?A9:p=4P4P1f6R1P2P6P7P8P9G=/8:p=2P2P6P7P8P9D7/8:p=3194:P4P91949g008?R<p-0\<R=\7R>%D;R?f7R@P2P6P7C6f8RAP1P2P7P8P9E5P2P7P8O2RB[[^3<^42]:]6]7W=P@A>4@2P6P7C6PAA>4A1P2P7P8P9E5P3f9RC?0@7A0<81P?P6%B;R;C<P1P6P7O2RDP:f;RE?0C2f<RFf:RGA0<1GRHA0?A;RI'8PGP9P@O2[X4FA0<2CP?P@P;C<P3PHPIPGPFP@O2P:A0<AFP<f=RIA0?F;f>RHf@RJP9O2[X3<A0?E;PCW5PCP:E@W5P9P:O2n2001000000120000000W5P1P:E?W5P9P:O2n2001000000120000000PBeW;W2X3<X42X:?X6>X7<XD9g0095R>1947[P=\2R=PCP1P2O1P6P7C6PGP@P1O1P2P7P8P9E5PB[[^3<^4@^:?]6^7<\>PCP4PCP@P1C;P6P7C6PGP4PGPAP@C;P2P7P8P9E5P31:C1PFPCP8P9P:D7f?R;PFP7O1P8PCC6[^0?^3<^9>PDP91:EAP;PFP8P9P:D7fBRDP;P7O1P8PFC6[^0?^3<^9>P5P>fARKPHP7P8P9fCRLPJP7O1P8P:PEPG149:RM90?FF2E3X1?,1?X0?,1?X8<,1<X9>PGPAP@O2P6PLPJP7P8P9fERNPDP7O1P8P:PIPFA0?HMF2E3X1?,1?X0?,1?X8<,1<P5P<fDROPKP6P8P9fFRPPLP6O1P8P:PHPIA0?;MF2E3X1?,1?X0?,1?X8<PHPFPEO2P:PPPLP1P8P9fHRHPNP1O1P8P:PJP;A0?KMF2E3X1?,1?X0?,1?P5P?fGRQPOP@P7P9fIRRPPP@O1P7P:PKPJA0?DMF2E3X1?,1?X0?PDPJP;O2P:PRPPPCP2P9fKR7PHPCO1P2P:PLPDA0?OMF2E3X1?,1?P5P?fJR5PQPGP1P8fLRMPRPGO1P1P:POPL148:90?NF2E3X1?PPPOPLO2P:PMPRPFPAP6fNROP7PFO1PAP:PPPN146:90?QF2E3P3fMR8P5PIPCP2D7fOR1PMPIO1PCP9PQPP142990?HF2P5PHPQO2P:P1PMP;PEP@D7fRREP1PJO1PFP6P5PR14A690?7F2P3fSR3fPPKO1PIP2P7P5E514C290?MPOPMP7O2P:fUPEPLO1P;P@P8PME514FA90?1P3PNPKfQPCP1POPHPNPKPIP2O4P9O8W<W;P9P:O2n2001000000120000000W2W?P9P:O2n2001000000120000000W2X1?P9P:O2n2001000000120100000W2X0?P9P:O2n2001000000120100000W2X8<P9P:O2n2001000000121100000W2X9>P9P:O2n2001000000121100000W>W<P9P:O2n2001000000121000000PBeW;W2X3<X4@X:?X6=X7<W@WBXC4P:ECW=XA0o"). Qed.

(* [comment removed for export] *)
Definition etwfP {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  twfP t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Lemma etwf_etwfP : forall {A} (t : itree node (exc A)) mo Q, etwf t mo Q -> etwfP t mo Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "p'0h01Ah11Hh21Qh32moh43mo1h51ri001rh61ti011ap;1p;2p;4p;5p100Y7p4p710R0p100QDp4p710p8p200R1g00YmR2p4p710p8P1g00ZaR3p4p710p8P1P0p8g00[ZR0j10Tg00LDj23TP2j42TP3j51Tg007Jf0R3#0'3g008?R2f2R4p-0R5\2[f3R6P4f1R7P3C2f4R8#0R9P6P4P0f6P5P7g00\RP8P3P7O2n10110000020010101X42X59P3D1W1W2W3W6X01o"). Qed.

Lemma etwfP_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
  etwfP t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwfP t mo Q'.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "p'0h03mo1h11ri001rh22H0h31ai011ah41Ah51Hh62HQh71Qh82Q'h92moh:1ti021ep;1p;2p;4p;7p200R0g00\oR1p4p710p8P0g00Y7R2p4p710p8g00[ZR3j11Tg00LDj23TP2j40TP1j72Tg007Jf0R1#1'3g008?R2f2R4p-0R5\2R6[f3R7P6[f4R6P7P4f1R7C0f5R8P6P7P1O2P6P4P7O2[^02]3f6R9#1R:P8P6P3f8R;P5P7g00\RR<P9P1P7O2n10110000020010101X02X1:P3P;P5P7P<P8P1P7O2n10110000020010101X02X1:P7P3f7R=P3f9P5P7P<P=P1P7O2n10110000020010101P3f:P5P4P<P=P1P4O2n10110000020010101[^02P1P1X2<P<\<eX02P=P7P1O2R<P8P4P7P1O3W2P=P4P7O2\<eX02X3;P1O1n10110200020010101X1:F2P9P8P6P4C0eW6W5W8W7W9W:X40o"). Qed.

Lemma etwfP_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
  etwfP t mo (fun a mo1 => etwfP (f a) mo1 Q) -> etwfP (ebind t f) mo Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "p'0h03mo1h11ri001rh21ai011ah32Hah41Ah51Bh61Hh71Qh81fh92moh:1ti021ep;1p;2p;4p;3p;7p;5p200R0g00\oR1p4p710p8P0g00]iR2p4p710p8P0g00Y7R3p4p710R4p8P0g00^cR5p4p7210p8p201R6g00QDR7p4p710p8P6P2p4p7210p8P6P4p8P6P5p4p73110p8g00[ZR4j10Tg00LDj22TP3j45Tg00_Wj13Tg00M:j34TP7j41TP1j78TP2j77TP5j56Tg007JR5f1R2#0'2f2R1%01,25[g008?R7f3R3p-0R8\7[f5R9P3P2f6R:f4R;P2O1f0R<P1C5X07X29C5%0:R=%09R>P;P4f7R?%0?R@,25P<%3:945=P9P<O1n10110000020010101X1=P1P4P?P8P2g00\RRAP;P<P2O2n10110000020010101X07X1>P=P;P1P4f8R>P8P2PA%0>RBP:P<O1RCP2P4f:RDP8P2PAP?P<P2O2n10110000020010101X07X1BREC1n10110000020010101X07X1=P@P4P>125BP2%3?945@PCn10110000020010101P<P4f9RCP8P2PAP:P<P2O2n10110000020010101X07X1@C1X07X2=P<P4P?P4PCP8P2PA%0CR@P?P<O1P2P4f;P8P2PAP>P<P2O2n10110000020010101X07X1@RFC1n10110000020010101P@P4PD%0DRD,25P1%3C945@P>P<O1n10110000020010101P2PFC1[^07P<PAPAP<n010000000PB%3>945BP2PEC1eX3AX07P@P?P2O1P<PFC1P<PDP>P1O1P2P4f<P8P2PAPCP<P2O2n10110000020010101X07X1DC1eW3X07X2>P<O1n10110200020010101X1=F8F7P9P5P:P9P;P3D6P1P2C5eW6W7W9W8W:X56X40o"). Qed.

Lemma etwfP_ret : forall {A} (a : A) mo (Q : A -> Model -> Prop), Q a mo -> etwfP (Ret (Ok a)) mo Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "h01Ah11Hh21Qh31ah42mop200R0p100Y7p4p710p8f0R1g008?R2f2R3p-0\2[P1P3f1O2P1W1W2W4W3X00o"). Qed.

(* [comment removed for export] *)
Lemma etwfP_tall : forall {A} (t : itree node (exc A)) mo (Q : A -> Model -> Prop) (Phi : A -> Prop),
  etwfP t mo Q -> tall Phi t -> etwfP t mo (fun a mo1 => Q a mo1 /\ Phi a).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "p'0h01Hh12Hth23evsh33mo'h43mo1h51ri001rh63rsph73Phih81Qh92moh:1ai011ah;1th<1Ah=2Hkh>2Hsh?3Hsth@2IHhA1khB1ni021ei032r0p;1p;2p;4p;3p;5p;6p200R0g00`OR1p4p710p8P0g00JXR2p4p7210p8P0g00Y7R3p4p710p8g00[ZR4j10Tg00LDj28TP3j41TP1j35Tg00:^R1j22Tg00M:j39Tg00HJj4:Tg00N0j47Tg00R9j24Tg001<j1<Tg001\j53Tg00QDj46TP2j6;Tg007JR2f0R3#0'8P2f1R5#0R61826g008?R7f3R8p-0R9\7R:[R;f4R<P9[R=f5R>P8f2R?P5C1f6R@?55<f7RAP>P<P>P5P3O2P<P5O1'2X47RBX:ARCC1[[]7]8]9W;P>%0>=928P?P5C1%0@=92<95@5P4PAP4f8RDP9P3g00\RREP>P3P@O2RFn10110000020010101P4f9RGP9P5g00aERHP>P3O1n10110300020010100P4f:RIP9P?PEPAP3PDO2P@P3O1'2n10110000020010101]1]0P>P5PEeX1HX0EP>P5O1PAP?PDO2RHP@P?O1RJP5P3C:12HJeW1X0FX:DP3O1n10110200020010101P5P3O2PA%0ARF=92>P<PCC1eW1W0X7=X8;X97X56g0095R6%08,82[P:\>R:P9\@R;PAP<P8O1P?P5C1P>P<O195D5PGP@P>O1P<PBX:GRBC1[[]7]8^97\6PAP2PFP>P<C7P?P5C1P2%0DP@P>C795D5P114A<g009h#<R1PIPAP?P5P3D3f=RF#0R=PIP8O1P?P4f?P9P5PEPIP3P5O2n10110000020010101X47X5=C6[]2^37^6614D>f;R>PDP?P5P3D3f>R=#0RCP>P8O1P?P4f@RJP9P5PEP>P3P5O2PIP3O1'2n10110000020010101X47X5CC6[^21^37^66'2P514G@PFPIP?P5P3D3%0JRJPFP8O1P?P4fBP9P5PEPFP3P5O2n10110000020010101X47X5JC6[^21^37^6614>DP=P>P?P5P3D3RJfA#0RCP=P8O1P?P4fCP9P5PEP=P3P5O2PFP3O1'2n10110000020010101X47X5CC6[^21^37^66P5PFP8P?P>PIP<P8P?P5P3O4PDP8O1O6X?JX21X37X66C:W=W>P5P3O2n2001000000120000000PGP2%0GPAP@C7P<PBC1eW1W0X7;X8:X97W@WAXB2P3E;W;X<0o"). Qed.

(* [comment removed for export] *)
Lemma etwfP_leaves : forall {A} (t : itree node (exc A)) mo,
  etwfP t mo (fun _ _ => False) -> tnf t mo -> leaves_unreachable_m nstep t mo /\ tsafe nstep nsafe t mo.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) [] "p'0h01Ah11Hh22HNh32moh43mo1h51ri001rh61ti011ap;1p;2p;4p;3p;6p200R0g00ViR1p4p710p8P0g00RmR2p4p710p8P0g00aaR3p4p710p8P0g00Y7R4p4p710p8P0p100Wgp4p741110p8P0p100b\p4p73110p8g00[ZR5j10Tg00LDj26TP4j42TP2j31TP1j65Tg00Ymj44TP3j43Tg007Jf0R3#0'6g008?R1f2R2f1R4P3g00\RR6V1R7V2C2f3R8#0?124f4R9P8P2%09R:P8P2P5f6p-0P4P6P6n10110000020010101X41X5:P4P3E5P9P8P2P7V9C4eC3W2W1W3W6X00o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MSpecP.
Context {St : Type}.

Definition mspecP {A} (P : assn St) (m : M St A) (Q : A -> assn St) : Prop :=
  forall s mo, P s mo -> etwfP (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

(* [comment removed for export] *)
Lemma mspec_mspecP {A} (P : assn St) (m : M St A) (Q : A -> assn St) : mspec P m Q -> mspecP P m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ah11Ph21Qh31mh41Hh52HPh62moh73mo'h81ph91sp;1p;2p;5p;3p;4p,2StR0p4p300R1g00c_R2p4p710p8P1p100`Op4p710p8P1p100\op6051002p8P1p100dPp6051002p8P1p100eJp6051002p8P1g00fER3p4p7210p8P1g00fbR4p4p710p8P1p100gVp6051001p8P1p100Y7p6051002R5p8P1g00hQR6p6051001R7p8P1p100iLp6051002p8P1p100jGR8p6051002p8P1P8p60521001p8P1p100kCp6051002p8P1g00l>R8p60521001R9p8P1p100KPp4p73110p8P1p100^cp4p7210p8P9P2p4p7210R1p8P9P3p4p710p8P9P5p8p200R5P1p8P5g00m5R1p4p7210p8P5P7p8P5P9p8P4j17TP2j26TP1j50Tg00mjj21TP3j35Tg00nJj32TP6j53TP8j44T%70R8f1R6,60R3f2R1P8[R2P0f3R4P1P6f0R9D0g008?R7f5R:P6P9O2f7/10R;P:P1O1P6f6f9R:?506A2:06P9O3X77X8;P4P1P6P9O3D3W5W6X90f4P4P1P6C4eW4X22X33X18X05P4P1P6P9O4W2W3W1X05o"). Qed.

Lemma mspecP_ret {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecP P (mret a) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ah11Ph21Qh31ah42moh51sh61Hh72HPh83mo'h91pp;1p;2p;4p;3p200R0g00ngR1p4p7210p8P0g00l>R2p60521001p8g00fbj17Tg00mjj26TP1j40j33Tg00fEj31Tg00nJj35Tg00Y7j42TP2j44Tf0R2p,2StR1#7R3f2R4P3[R5g008?R6f3R7f1R8P2O2P7f5P4P8O3[]4^51f4R9P8P2O2P7P4P8P2O3f7R:/61R;P1P:f6R:P4C0P8P:f9R:?118A5:18P2O3X86X9;C2eW7X46X51P9P4A3197P8C4eW6X25X13X32X00P7P4P8P2O4W2W1W3X00o"). Qed.

Lemma mspecP_bind {A B} (m : M St A) (f : A -> M St B) (P : assn St) (Q1 : A -> assn St) (Q : B -> assn St) :
  mspecP P m Q1 -> (forall a, mspecP (Q1 a) (f a) Q) -> mspecP P (mbind m f) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h01pi001ph13mo'h21ai011ah33mo1h41Ah51Bh61Ph71Qh82Q1h91fh:1mh;2H1h<2HPh=2Hfh>2Hmh?2a0h@2mohA1si021shB2s1p;2p;1p;4p;3p;7p;6p;5p200R0g00c_R1p4p7210R2p8P0g00o[R3p4p7210p8P0g00fER4p4p710R5p8P0g00iLR6p6051002p8P0g00jGR7p6051002p8P0g00l>R8p60521001R9p8p201R:P2p8P:P3p4p73110p8P:P5p8P:g00Y7R5p6051002p8P:P7p60521001p8P:P9p8P1j26Tg00fbj1;TP8j44Tg00mjR8j22TP4j31Tg00nJj30TP5j43Tg010Pj45TP6j7:TP7j79TP3j67j58Tp,2StR3f1R7'6R6f2R51635[R4%;3R1f4R9P1[R2f6R;P5P9P7C4f7R<P<f3R=f0R>O1f5R?P>O1P5C4]2g008?R@P;P7P>O2f;RA/23RBf:RC/23RDf9REP5O1RFPEf<RG?13>A0G3>O2X0BP7P<A1G37A0G37P>O3X1@X0DRHPBPFP7f8RFf=RI?137RJA0I37RIP>O3X1@X0B12G3RKPCPJPIO2P>PEf>RI?137A0I37P>O3RJX1@X0KC3X3@X2BP9P5P7P>O3P8PGP312I3R8PGf?RK?135A0K35O2P7PAf@RL?137A0L37P>O3X1@X08C3\J^3@P>PGfARGPGP3P5P7C5RJ713A0G3JP>O3PCP=P5P7P>O412G3RGPKfBRKPKP3P=P5C5RJ713A0K3JO2P7PIfCRJ?137A0J37P>O3X1@X0GC3eW;X3@XB3X2IP7P>O2n2001100000120101102X?BF:F9PDP3PAPCPEPFP5E7P7PHC3eW<W@XA3P<P9P3PFP<P;P?D8P5C4eW=W>X72X82X61X94X:6X5:X40P;P?P9P=P5P7P>O7X72W8W6W9W:X5:X40o"). Qed.

Lemma mspecP_conseq {A} (m : M St A) (P P' : assn St) (Q Q' : A -> assn St) :
  mspecP P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecP P' m Q'.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h02moh11si001sh21Ah31Ph42P'h51Qh62Q'h71ai011ah81mh93mo'h:3mo1h;1pi021ph<1Hh=2HPh>3HP'h?2HQh@2HmhA2a0hB2s1p;2p;1p;4p;3p;7p200R0g00c_R1p4p7210p8P0g00fER2p4p710p8P0g00iLR3p6051002p8P0g00l>R4p60521001p8P1j27Tg00fbj16TP4j42Tg00mjR4j24TP2j31Tg00nJj30Tg010Pj43TP3j75Tp,2StR3f0R2'7R1%63R5f3R6P5[R7f4R8P5[R9f5R:P6P8f1R;C2g008?R<P:P;P2O2f7R=f2R>P;O2[]0^13f6R?P>P;P2O3P?P6P>P;O3[^0<^13^7=P=P;P2O2f;/43R?f:R@P>O1P;f9f=RA?13;RBA0A3;RCP2O3X9<X;?f8RDPBPCP2O3X9<X;?P:P>P;P8P>P;P2O3O3P4f<P3P@f>R4?13;A043;P2O3P@f?RC?13>A0C3>P;O3[^:<P2PAP>P;P2O3P@P6P>P;P2O4W<PAfAR@P@P3P>P;C3RC713A0@3CP2O3PAfBRAPAP3P6P>C3RC713A0A3CP;O3[eX:<XB3X74P;P2O2n2001102000120101100XA?F5W>X0<X13PDP:P=P6C2eW?W=W@X69X57X45X35X81X20P:P8P6P>P;P2O6W6W5X45W3W8X20o"). Qed.

Lemma mspecP_pre {A} (m : M St A) (P P' : assn St) (Q : A -> assn St) :
  mspecP P m Q -> (forall s mo, P' s mo -> P s mo) -> mspecP P' m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ah11Ph22P'h31Qh41mh52moh61sh71Hh82HPh92Hmh:1ap;2p;1p;4p;9p200R0g00c_R1p4p7210p8P0g00l>R2p60521001p8P0g0110R3p60521000p8P1j23Tg00fbj12TP2j40TP3l91Tp,2StR3f0R2'3R1%23R4f3R5P4[R6f4R7f2R8P5P2C0g008?R9P7f1R:P2O2f6R;P8P:O2[]5^63P;f5R<P7P5P8P8P:P2P<P8P:P2O3P2W7X59X63X:;M91W8W9X36X24X14X41X00P7P5P8P:P2O5W3X24W1W4X00o"). Qed.

Lemma mspecP_post {A} (m : M St A) (P : assn St) (Q Q' : A -> assn St) :
  mspecP P m Q -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspecP P m Q'.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ah11Ph21Qh32Q'h41mh52moh61sh71Hh82HQh92Hmh:1ap;2p;1p;4p;9p200R0g00c_R1p4p7210p8P0g00l>R2p60521001p8P0g0110R3p60521000p8P1j23Tg00fbj12TP2j40TP3l91Tp,2StR3f0R2'3R1%23R4f2R5P4[R6f3R7P4[R8f4R9P5P7f1R:C0f5R;g008?R<P;P5P:P2O3P;P7P5P:O3[]5^63]:f6R=P;P9P9P7P5P:P=P:P2O2P2W7X5<X63P2M91W8W9X38X26X14X41X00P9P7P5P:P2O5W3W2W1W4X00o"). Qed.

Lemma mspecP_munr {A} (Q : A -> assn St) : mspecP (fun _ _ => False) munr Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ah11Qh21Hh32moh43mo'h51ph61sp;1p;2p;3p;4p200R0g011nR1p4p7210p8P0g00l>R2p60521001p8g00fbj17Tg00mjj26TP1j30j23Tg00fEj31Tg00nJj35Tg00Y7j42TP2j44Tf0R2p,2StR1#7[R3g008?R4g00\RR5P5f5R6/61R7f39016f2f6f7R6f1R8711A5618P2O3X44X57C2P2n010000000W2W3X61P8P5V4V11318P2C4eX13X00P8P2O2W1X00o"). Qed.

Lemma mspecP_false {A} (m : M St A) (Q : A -> assn St) : mspecP (fun _ _ => False) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ah11Qh21mh31Hh42moh53mo'h61ph71sp;2p;1p;3p;4p200R0g00c_R1p4p7210p8P0g00l>R2p60521001p8P1j26Tg00fbj15Tg00mjj20Tg00fEj31Tg00nJj34Tg00Y7j42TP2j43Tp,2StR2f0R1'6R3f1R4%52[R5g008?R6g00\RR7P7f6R8/02R9f5f3O1f2R:P8f8R8?124A4824P1O3X56X69C2P1n010000000W3W4X72P:P7V6V2P4P1C3eX15X23X00P:P4P1O3W1W2X00o"). Qed.

Lemma mspecP_get (P : assn St) : mspecP P mget (fun s' s mo => s' = s /\ P s mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ph12moh21sh32HPh43mo'h51ph62s'p;1p;3p;2p;4g00fbj1;Tg0070j30Tg00O@j23Tg00HJj42Tg00mjj2:Tg012bj29j17Tg00fEj35Tg00nJj34Tg00:^j21Tg00Y7j46Tg00l>j48Tp,2StR0#;R1g008?R2f2R3f1R4f0R5O2A0033f3R6P3P4O21303P5C21:00R71903P4A5004A4004R8500f5P8P5O2'1X42X57C6eW3W1X20P0P5%70A0034P6P4P5O2'1X12X20X60C8eX01P5O1W0o"). Qed.

Lemma mspecP_put (P : assn St) (s1 : St) : mspecP P (mput s1) (fun _ s mo => s = s1 /\ exists s0, P s0 mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h02s0h11Ph22moh31sh42s1h52HPh63mo'h71pp;1p;3p;2p;4g00fbj1<Tg0070j31Tg00Nfj20Tg00O@j23Tg00OZj4;Tg00HJj4:Tg00mjj26Tg013Vj34j28Tg00nJj35Tg00:^j22Tg00Y7j47Tg00l>j49Tp,2StR0#<R1g008?R2f3R3f1R4f0R5O2A1033f5R6P5f2R7O2X00R8,001303P0P8P7P5C;C:g014JR8/60R9A4037P4A5804=106f7P5P4O2X00,00'2X62X79C7eW5W2X30P8P41805A1043P6P5P4O2X00,00'2X22X30V8C9eX40X11P4P5O2X40W1o"). Qed.

Lemma mspecP_upd (P : assn St) (f : St -> St) : mspecP P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h02s0h11Ph21fh32moh41sh52HPh63mo'h71pp;1p;3p;2p;4g00fbj1<Tg0070j30Tg00:^j21Tg00O@j23Tg00HJj4;Tg00OZj4:Tg00mjj26Tg014jj34j28Tg00nJj35Tg00Nfj22Tg00Y7j47Tg00l>j49Tp,2StR0#<R1P0\0R2g008?R3f3R4f1R5f0R6O2P0f4R7P4O1P7P6O1R8500f5R9P6f2R:O2'1X00P:P4P:O1R;=00;P7P:P5O2130;P6C;C:g014JR;/60R7A404:P5A5;0:f6P6O1500f7P6P5O2'1X00,20X63X77C7eW5W3X40P;P51806A00:8P9P6P5O2'1X00,20X33X40V;C9eX22X11P5P6O2W2W1o"). Qed.

Lemma mspecP_upd' (P : assn St) (Q : unit -> assn St) (f : St -> St) :
  (forall s mo, P s mo -> Q tt (f s) mo) -> mspecP P (mupd f) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ph11Qh21fh32moh41sh51Hh62HPh73mo'h81pp;1p;2p;3p;4g00fbj17Tg00mjj26Tg014jj30j23Tg00fEj31Tg00nJj35Tg00Y7j42Tg00l>j44Tp,2StR0#7R1g014JR2P1[R3P0\0R4g008?R5f4R6f1R7f0R8O2P6g015^f3R9f2R:O1P7O3[]3^40f5P7P8O2P9P:P7P8O31620R;A006:P7f7A1207A5207P8O3X75X8;C2eW6X35X40P2P91307P:C4eW5X24X13X01P:P7P8O3W2W1W0o"). Qed.

(* [comment removed for export] *)
Lemma mspecP_sys {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo ->
     nsafe n mo /\
     forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
  mspecP P (msys n dec) Q.
Proof.
  intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
  intros rsp mo' evs [Hst _]. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

(* [comment removed for export] *)
Lemma mspecP_sysP {A} (n : node) (dec : resp -> option A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo ->
     nsafe n mo /\
     forall rsp mo' evs, nstep n mo rsp mo' evs -> (nf_node n -> errno_of (eff_ret rsp) = None) ->
       exists a, dec rsp = Some a /\ Q a s mo') ->
  mspecP P (msys n dec) Q.
Proof.
  intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
  intros rsp mo' evs [Hst HnP]. destruct (Hk rsp mo' evs Hst HnP) as (a & -> & HQ). exact HQ.
Qed.

Lemma mspecP_if {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  (b = true -> mspecP P m1 Q) -> (b = false -> mspecP P m2 Q) -> mspecP P (if b then m1 else m2) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h02H1h12H2h21Ah31Ph41Qh51bi001bh62m1h72m2p;2p;1p;3p;4p200R0g00c_R1p4p7210p8P0g00l>R2p60521001p8P1j22Tg00fbj14Tg0070j30TP2j41Tg00O@j23Tg019@R2p,2StR1f1R3'2R4f2R5,21R6%41R7f4R8P7[R9g019`R:9028f6R;P5P8P3C1[f5R<g01:@R=502f7R>f3R?P8P5C1[P2f0R@=02:f9RAP<P>P8C1[A023=f:RBP;P>P<C1[PBP;P2f;,21P5f8R1P>n0110000020000P<C1]1]0P;A02::P1P8P;P?C1R1[A02:=PAP<P;P8C1R;[P3132:O1W1W0A02=:P1[A02==P;[P@132=O1W1W0n0110000020000P3P@O2W1W0X49X37X76X64X52X20P<P8P?P5P3P@O6W4W3W7W6W5X20o"). Qed.

Lemma mspecP_if_pre {A} (b : bool) (m1 m2 : M St A) (P : assn St) Q :
  mspecP (fun s mo => P s mo /\ b = true) m1 Q -> mspecP (fun s mo => P s mo /\ b = false) m2 Q ->
  mspecP P (if b then m1 else m2) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h02moh11sh22H1h32H2h41Ah51Ph61Qh71bi001bh82m1h92m2h:2HPh;3mo'h<1pp;2p;1p;3p;4p200R0g00c_R1p4p7210p8P0g00fER2p4p710p8P0g00Y7R3p6051002p8P0g00l>R4p60521001p8P1j23Tg00fbj1:Tg0070j32Tg00:^j21TP4j40Tg00mjj29TP2j38Tg00nJj37TP3j46Tg00O@j25Tg00HJj44Tg019@R3p,2StR2f1R4'3R1f2R5,32R6%:2R7f4R8P7[R9f5R:g008?R;f3R<P4f0R=O2f6R>g019`R?523'1W0X12P<P=C0P>P8P4P=O2f7R@g01:@RA523'1X0;X12P<P4C0P:P4P=O2P3f;RBf9RCP4P=O2RDA235?'1X0;X12PCP>C0f<f:REP4P=O2A23<A'1X0;X12PCP@C0f=/92RFP3f>,32P5PBPEn0110000020000P:O1P8PEf?RG?824A7G24P=O3X;;X<FC6]3]2PCPEf8RCP4P=O2RFA23??RG'1X0;X12PCP:C0PBA23?A,1DX0;X12PCP>C0P4P8P<PCP8P<O2RHPGP5153?C4O3W3W2PEA23A?,1FX0;X12PCP:C0PBA23AARB,1DX0;X12PCP>C0P=P8P<PHPBP5153AC4O3W3W2n0110000020000P8P<O2W:X0;X12P@P<P3132CP>P:P8n0110000020000P5C0eW3W2X69X57X96X81X73X40P:P8P<P5P4P=O6W6W5W9W8W7X40o"). Qed.

Lemma mspecP_exI {A X} (P : X -> assn St) (m : M St A) (Q : A -> assn St) :
  (forall x, mspecP (P x) m Q) -> mspecP (fun s mo => exists x, P x s mo) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h01xi001xh11Ah21Ph31Qh41Xh51mh62moh71sh81Hh92H0h:2HPh;3mo'h<1pp;1p;2p;4p;3p200R0g00c_R1p4p7210p8P0g00l>R2p60521001p8g00fbj17TP1j26TP2j40Tg00NfR2j21Tg00mjj25Tg00fEj34Tg00nJj33Tg00Y7j42Tp201R1f0R3p,2StR4#7R5[R6f2R7,64R8f3R9P5[R5f5R:P9P3O1P7f1R;C0^09g008?R<f6R=P=P3P7P;O3X0='1R>P2f7R2P2P3P9P7O3X02f9R?/54R@P=P9O1P7P2f;RA?44;A3A4;P3O3X;<X<@C2P3P?P3P:f4R@O3P2P;P=P:P3O4W:X0?P;P3O2n2001000000120100000W9W6X74P:P>X6<X74P7P;C0eW8X35X58X26X41X10P@P9P7P;P3O5W3W5W2W4X10o"). Qed.

Lemma mspecP_pure {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
  (phi -> mspecP P m Q) -> mspecP (fun s mo => P s mo /\ phi) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ah11Ph21Qh31mh42moh53phih61sh71Hh82H0h92HPh:4Hphih;3mo'h<1pp;1p;2p;4p;3p200R0g00c_R1p4p7210p8P0g00l>R2p60521001p8g00fbj17TP1j26TP2j40Tg00:^R2j21Tg00mjj25Tg00fEj34Tg00nJj33Tg00Y7j42Tp,2StR1#7R3p-0R4f2R5,61R6f3R7P3[R8f5R9f4R:P5f1R;C0\5g008?R<f6R=P;f0R>O2/19R?P2f7R2P5P;O2P=f9R@/51RAP=P7O1P5P2f;RB?41;A3B1;P>O3X;<X<AC2P>P@P:P7O2P2P>P=P9P;O4X:@W9P;P>O2n2001000000120000000W8W4X61P9P?X4<X61P5P;C0eW7X28X36X54X13X00P:P7P5P;P>O5W2W3W5W1X00o"). Qed.

Lemma mspecP_pure_l {A} (P : assn St) (phi : Prop) (m : M St A) (Q : A -> assn St) :
  (phi -> mspecP P m Q) -> mspecP (fun s mo => phi /\ P s mo) m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ah11Ph21Qh31mh42moh53phih61sh71Hh82H0h92HPh:4Hphih;3mo'h<1pp;1p;2p;4p;3p200R0g00c_R1p4p7210p8P0g00l>R2p60521001p8g00fbj17TP1j26TP2j40Tg00:^R2j21Tg00mjj25Tg00fEj34Tg00nJj33Tg00Y7j42Tp,2StR1#7R3p-0R4f2R5,61R6f3R7P3[R8f5R9f4R:P5f1R;C0\5g008?R<f6R=P;f0R>O2,19R?P2P=f7R2P5P;O2f9/51R@P=P7O1P5P2f;RA?41;A3A1;P>O3X;<X<@C2P>f8f:P9P:O2P2P;P=P9P>O4W9W:P;P>O2n2001000000120000000W8W4X61P9P?X4<X61P5P;C0eW7X28X36X54X13X00P:P7P5P;P>O5W2W3W5W1X00o"). Qed.

Lemma mspecP_pointwise {A} (P : assn St) (m : M St A) (Q : A -> assn St) :
  (forall s mo, P s mo -> mspecP (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspecP P m Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ah11Ph21Qh31mh42moh51sh61Hh72HPh83mo'h92s'p;1p;2p;3p;4p200R0g00c_R1p4p7210p8P0g00l>R2p60521001p8g00fbj16TP1j25Tg0070j30Tg00:^j23TP2j42Tg00O@j21Tg00HJj44Tp,2StR2#6R1f1R3,52R4f2R5P1[R6g008?R7f4R8P3f0R9O2f6A0238f3R:9079'3X87X92P8P:C2[]4^52f5P3P9O2P:P5P3P9P5P3A0255A073311251173C4O6W7X47X52P8P:P5P3C2eW6X26X34X11X00P:P5P3P9O4W2W3W1X00o"). Qed.

Lemma mspecP_when (b : bool) (m : M St unit) (P : assn St) (Q : unit -> assn St) :
  (b = true -> mspecP P m Q) -> (b = false -> forall s mo, P s mo -> Q tt s mo) -> mspecP P (mwhen b m) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h02H1h12H2h22moh31sh41Ph51Qh61bi001bh71mp;2p;1p;3p;4p;5g00c_j27Tg00fbj16Tg0070j30Tg00l>j41Tg00ngj35Tg00O@j22Tg01:`j54Tg01;[j33Tg019@R0p,2StR1g014JR2'7R3%61R4P4\2R5f3R6g019`R7500P2f2R8P6f1R9C1[f4R:g01:@R;500g008?R<f5R=P9f0R>O2P=g015^R?P8P9O3[]2^31[P0A00>7P2P=f6R@P:C1[A009;f8RAP9P>O2PAP?P8P9O3[^2<^31[P2P@P0P3P8f7R@A512?n0110000020000P=C1]1]0P=A0077P2P:P=P6C1RA[A007;P@P9P>O2P@P?P8P9O3[^2<^31R<[P91207O1W1W0A00;7PA[A00;;P<[P2P?P=P:P>120;O1D4W1W0n0110000020000P9P>O2P2P6A31=:P8C1eW1W0X55X44X73X60P6P8P9P>O4W5W4W7W6o"). Qed.

Lemma mspecP_loop {X R} (body : X -> M St (X + R)) (I : X -> assn St) (Q : R -> assn St) (meas : X -> nat) :
  (forall x, mspecP (I x) (body x)
     (fun r s mo => match r with
                    | inl x' => I x' s mo /\ (meas x' < meas x)%nat
                    | inr v => Q v s mo
                    end)) ->
  forall fuel x, (meas x < fuel)%nat -> mspecP (I x) (mloop fuel body x) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h01si001sh12moh21xi011xh34__x1h44fuelh51Hh62Hfh73Hf0h81Ih91Qh:1Rh;1Xh<7__arithh=4__ffh>4__p1h?8__varmaph@5__withA4__x2hB4__x3hC4bodyhD4cstrhE4meashF1ri021rhG2HIhH2HbhI2HmhJ3Hm0hK2IHhL1ahM5cstr0hN5cstr1hO3mo'hP1phQ1vi031vhR2x'i042x'p;2p;1p;4p;6p;3p;7p;5p;9p;<p;8p200R0g00c_R1p4p7210R2p8P0g01<PR3p4p7210p8P0g00l>R4p60521001R5p8P0g01=ER6p60521001R7p8p201R8P2p8P8P3p4p73110p8P8P5p8P8g01:`R5p60521000p8P8P7p8P8P6p605311000p8g01>AR7j2@TP1j2ATg00fbj1XTg01>`R1j21Tg00:^R2j2;TP4j43TP3j67j7PTg01?8R3j10Tg01?XR4j22Tg00O@j2>Tg01@4j4=Tg01@[j1:Tg01A@j28Tg00T]j1iTg001<j1^Tg01A\j2BTg01B:j1[Tg01BXj1ZTg01CCj2HTg01Cfj2?Tg01DIj4GTg006Nj1WTg01E4j6VTg01EXj2UTg01F:j2TTg0070j3QTg01Ffj3NTg01GEj4MTg01H7R9j15Tg00ngj3FTg00mjj2OTg00fEj3KTg00nJj3RTg00Y7j4STg01HVj1kTg01I4j2CTg01IQj2DTg01J:j3JTg01Jcj2hTg01KOj3gTg01Koj4eTg01LMj1]Tg00<Ij1_Tg01M2j3`Tg01MUj4\TP5j5aTP6l9bTg01N@j4cTg01Nal<ITg01OFj7dTg01Ojj8YTg01PNl<fTg00;9R6f0R5'>p=4g01Q3R:P6P1P3P4g01QRR;f3R<f2R=f1R>g01R4R?g01RSR@P5M<Ip=LP>g01S1RAg014JRBPBg01SPRCP5g015^Fdp=6P6P>g01T0P5CGp=9P<PAPBPBPCP=P>P5GYp=<P:P6P1P3P4P;f5R;f4R4P<P=P>P5M<Ip=EP:P:P6P6P9P3P3P<g01TWP=P>P5M<fp=jp,2StR31@=>'A\>R9%X3\=R1P:\4RDf6RE/@;RFP<P5O1RGP4P5O1RHg008?RIP7f9RJf8RKp-0RLP=f7RMP5P=P>O3P;P5O1RNP;P4O1'1';PEP5P=P>O3n200110200021010410103W1X03XFFC3^2;11H>PJPMP>O1P3f:RHPJP=PKP>E7PEC3[^2KRFX4:11G?P4P>O1RG/1?%0GRO/2@RPPGPO%4O1>6@CLP5C=PPP;P=O1RP#:%0P,8@g01U;RP#iRO%^PRG1B6>%[6RQ%Z6RRP61H6@RSg01Ugg00HeRT,?6RUCG,6R%WBRVPR19US,6RPVPRPAPBPBPCP<EVC<C<1URCRCP5P=g019@RBg019`RA'>1T5==QBAdAN6@>CMRAb=b?b@X36X>L18@512>@P<[[^36^>LP5f;RBPJP4O1P3f<RSPBP?PHP4E7PKC3PMP4O1#0P>P=O4b<bDb7W6X2M%5=,1N1@BHRNPHPJP>O1P7PSPB1A3SP5P3f=RWPSP;PBP5E7AF3S5n200110000021010410102X0NPKP>O1RKP7f>RXPWPLP=PSP5P=P>O3RYPHP5O1PHP;O1'1';PBP5P=P>O3n200110200021010410103X1IX03XFNPMP;P>O1P7PSPBPSP7f?RZPXPLP=PWP5P=P>O3PBP5O1PBPEO1RL'1';PYn200110200021010410103X1IX03P7PWPS1A3WP5P3PXPWPEPSP5E7R7AF3W5RYn200110000021010410102PJC3P5PWP=P>P5O3PBP=O1/1L';RLP2PXP<P=P>O3PSP<O1PSPMO1'1fAR2/O3R[P3fBP2PHf@R\P4P<FPP=P\fCR]?K3>AR]3>P5O3XOIXP[CSP5P\P;P4P<O3PZPEO1PZPHO1'1PSPMP\PMO1R[/1W%0[R^%0WR_'2P[P^%4^R`PWP_%4_EEP\PBO1R\,1[%0\R_,2^RaP[P^P`P\P_%4_EEP5C=PaP2PSO1Ra%5XR_'1%0aR\%0XR`%kTR^'C'2R[PaP\%4\P_1C5^X26R_P`O1P_PXP`%4`CjEEPBC=P[%:Z%0Z,8@P]PHO1R[#:%0[,8@fDPZO1RZ#:%0Z,8@%5?R@#5,D61D6@1D6?5J65J6g01VN'h=gPOPGP61B6=P>1B6<CePQPR%]T,?6RQ%_T,?6RT1H6^5`6'9,6RPVPR19UQ,6RPV19UT,6RC<C<PCPAb=b?b@X36XA6XB61C>^,2=12><12=<[[^36^A6^B6P5fFR6P2O1#0%0]P6PWO1#0P4P;O5b<bNbMbDb7bJC\PEP;P>O5WIWGP>P5O2n2001000000121000000W5X1IX03PWPLX1IX03P7PHC3R7eP7eXRWP5O1PWP5PSP=P>P5O3R7X1IX03RLPHP5X57X1IX03DaPWPLPYPHC3eXQSP5O1n200110000021110110102XLNM9bPHPKP3PBPH%5<PJP>E7PMC3eW6X2JXKFX4:P5CcX4:WHXEDX91X81XC9X:8X;0P;P4P<P=P>P5O6WEX91W8WCX:8X;0o"). Qed.

Lemma mspecP_seq {A B} (m : M St A) (f : A -> M St B) (P R : assn St) (Q : B -> assn St) :
  mspecP P m (fun _ => R) -> (forall a, mspecP R (f a) Q) -> mspecP P (mbind m f) Q.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "h01Ah11Bh21Ph31Qh41Rh51ah61fh71mh82Hfh92Hmp;2p;1p;4p;9p200R0g00c_R1p4p7210R2p8P0p100o[R3p4p7210p8P0g00l>R4p60521001R5p8P0g01=ER6p60521001p8p201R7P2p8P7P3p4p73110p8P7P5p8P7P6p605311000p8P1j21Tg00fbj13TP4j40TP6l92Tp,2StR6f1R4'1R1f2R51165[R3%36R6f4R2P6[R8f6R9P5P2P5V9C0f7R:P:f3R;f5R<f0R=O1P5C0]5f8R>P:P9P<P2P2V>P5P4P4P=O1X5>M92W8W9X38X46X26X63X71X17X00P9P<P2P;P5P4P=O7W3X46W2W6W7X17X00o"). Qed.

(* [comment removed for export] *)
Lemma mspecP_conj {A} (P : assn St) (m : M St A) (Q1 Q2 : A -> assn St) :
  mspecP P m Q1 -> mspecP P m Q2 -> mspecP P m (fun a s mo => Q1 a s mo /\ Q2 a s mo).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h03mo1h11ri001rh23mo'h31pi011ph41Ah51Hh62H0h72H3h81Ph92Q1h:2Q2h;1ai021ah<1mh=2moh>1si031sh?2H1h@2H2hA2HPhB2a0hC2s1i041ep;1p;2p;4p;3p;7p;5p200R0g00c_R1p4p7210p8P0g00\oR2p6051002p8P0g00dPR3p6051002p8P0g00fER4p4p710p8P0g00l>R5p60521001p8g00fbj1>TP1j2=TP5j44Tg00mjR5j23Tg00[ZR1j1<TP4j31Tg00nJj32Tg00:^j20TP3j79Tg00>dj28Tg01W:j55Tg00HJj47Tg010Pj46TP2j7;Tg00Y7j4:Tp,2StR2#>R3f1R4,=2R6f2R7P3[R8f3R9P3[R:f4R;P9P7P4C4f5R<P;P9P4C4g008?R=f7R>P4f0R?O2f9R@/32RA#<RBP>P7O1RCP4P1f;RD/32REp-0RFP4g00\RRGP@f<RH?12?RIA2H2?RJP4O3RKn10110000020010102P1PEPFP4PGf8RLPIPJP4O3RJn10110000020010102'0X0=X1BP1PEPFP4PG10KJn10110000020010102X0=X1BPBPCP4P1PEPFP4PG13H2RJPDf>RK?124RIA2K24RMP?O3RNX2=W3P?P4O2n10110000020010102X0=X1BP1PEPFP4PGf:ROPIPMP?O3RMX2=X3JP?P4O2n10110000020010102X0=X1BP;P7P4P?O3P9P7P4P?O3F9P113O2P1PJPFP4PGPOf=RI?12?RPA2I2?RQP4O3n10110000020010102P1PJPFP4PGP@PPPQP4O3n10110000020010102'0P113I2PFP7PGPDA1K2?RFA2K2?R1P7O3POPFP1P7O3'0n10110000020010102[^0=P?10GGR1PGPGPG18G4X7GX6GP?D5W5PG\1eX0=P5PHP210NMPHf?RH?127RMA2H27RNP4O3PDPMPNP4O3'0[^0=P?PKP7P4P?O3PIP7P4P?O3'0PHP9P7P4O3RNPKP9P7P4O3RM10NMPHP;P9P7O3fARMP<P;P9O3f@P<P;P9O3P4P?C7W7X6NP?D5W5PKPMP2P7P4C6RN91M2R5A2M2NRNP?O3PIP5PNP?O3'0PHfBRHPHP2P9P7C6RN712R5A2H2NRNP4O3PKP5PNP4O3'0[eX0=XC2X;KP4P?O2n2001101000120102103XBEP?O1n10110400020010102X1BF;PAPCP4PLA1D24RLA2D24RDP?O3P>PLPDP?O3'0X2=X3AC:eWAW=X>2f6RAP<P;PAP7P4P?O3P<P7P4P?O3'0X==X>2X;AC4eW@W?X::X98X<6X83X40P;P9P7P4P?O5W:W9W<W8X40o"). Qed.

(* [comment removed for export] *)
Lemma mspecP_paths {A} (P : assn St) (m : M St A) (Q : A -> assn St) (Phi : A -> St -> Prop) :
  mspecP P m Q ->
  (forall s mo tr a s' mo', P s mo -> tpath nstepP (m s) mo tr (Ok (a, s')) mo' -> Phi a s') ->
  mspecP P m (fun a s mo => Q a s mo /\ Phi a s).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h03mo'h11ai001ah22moh31ri011rh41si021sh51Ah61Hh72Hph81Ph93Phih:1Qh;1mh<3mo1h=1pi031ph>2s'h?2trh@2HPhA4HPhihB2HmhC2a0i041ep;1p;2p;4p;3p;7p;8p200R0g00c_R1p4p7210p8P0g00eJR2p6051002p8P0g00fER3p4p710p8P0g00l>R4p60521001p8P0g00KPR5p4p73110p8g00fbj1@TP1j2?TP4j48Tg001<j19Tg00mjR4j22Tg00[ZR1j14Tg010Pj46Tg017Tj27TP3j30Tg00nJj31Tg00:^j23Tg00_Wj1:Tg00HJj4>TP2j7=Tg00Y7j4<TP5j8;Tg007Jg001\f5R5f4R2f3R3f2R6f1R7f0R8G;p=5p,2StR9#@R:1?97R;P:\6R<p-0R=\9\3R>P2P3P6P7C8g008?R?g009h#9R@f8RAf:RBP5P2O2f<RC/29RD#4REPBf6RFO1P5P2PCP9P3P6C6,7DP7E5f9RGP2P3O2[[^0?^>9]1]?]2^49f7RHP7P8O212G9RI#4RJPHP6O1RKP7P1f;RL/29RMP=P7g00\RRNPLf>RO?097A1O97P8O3X0?X=DP8P7O2n10110100020010100X<?X3JP1PMP=P7PNPGA0C98RGA1C98RPP7O3PAPGPPO2'3n10110100020010100X<?X3JP2P6P7P8O312B9#4P1PMf=RM/29#4PLPFO1P5P3P7P8E5P112O9P=P6PNPCf?RJ?098A1J98P6O3n10110100020010100P112J9R1P=P3PNPMf@R=?098RPA1=98RGP3O3PCPPPGO2'3n10110100020010100[[^0?P8PEPBP5O1P2P6%:DP8E5P8PNeX6NW7X0?P4PMP9%41PMPAO1PHP51717P8E5PMA0=96A1=96P7O3POfAR1?093R4A1193RNP6O3PMP4PNO2'3[[^0?P8fBRN/29R4#4P=PLO1PBPAPNP9P6P7C6,74P8E5P=fCR4P4P9P3P6C6RN709A149NP7O3P1P2P3P6O3P=P2P3O2P8POPMPCPBP2P3P6PLP7O8C>P1fDR1P1P9P2P3C6RB709RCA119BRBP6O3P=PCPBO2'3eW6W7X0?X>9X1JP7P8O2n2001103000120100102XCDP8O1n10110400020010100W3X?@F=PIPKP7PAA0L97RAA1L97RLP8O3PHPAPLO2'3X0?X=IC<eW@X2?X49PFP5P2PFP6P7P8O3P5P6P7O2'3X2?X49X1FC8eWAWBX9>X:<X;;X8:X50P2P3P6P7P8O5W9W:W;W8X50o"). Qed.

(* [comment removed for export] *)
Lemma mspecP_tall {A} (P : assn St) (m : M St A) (Q : A -> assn St) (Phi : A -> St -> Prop) :
  mspecP P m Q -> (forall s, tall (fun p => Phi (fst p) (snd p)) (m s)) -> mspecP P m (fun a s mo => Q a s mo /\ Phi a s).
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h01pi001ph11ai011ah23mo'h31si021sh41Ah51Ph63Phih71Qh81mh92moh:3mo1h;1Hh<2H1h=2H2h>2HPh?2Hmh@2HthA2a0hB2s'p;1p;2p;4p;3p;7p200R0g00`OR1p4p710p8P0g00c_R2p4p7210p8P0g00fER3p4p710p8P0g00iLR4p6051002p8P0g00kCR5p6051002p8P0g00l>R6p60521001p8g00fbj1;TP2j2:TP6j44Tg00mjR6j25TP3j31Tg00nJj30TP1j39Tg00:^R1j22TP5j77Tg010Pj43Tg00HJj46TP4j78Tp,2StR4#;R5f1R3,:4R2f2R7P5[R8f3R9p-0\4[R:f4R;P9P7P3C4f6R</54R=P9f7R>f0R?714A0>4?O2X0=P;P?O139^34g008?R=P>P3P?O2f9R@/54RAP>P7O1RBP3f8RCf;RD?143REA0D43RFP?O3RGP>PEPFO2'2RFX:=X1APFX2=X0APAPBP3PGX2=X0AP<f:RG?14?A0G4?O2X0AP;P7P3P?O3P9P7O1F7P6PGP4P@f<R6?143RBA0643RFP?O3PCPBPFO2'2PGf=RG?147RFA0G47RBP3O3P@PFPBO2'2[^:=P?P6f?RBPBP4P7P3C3RF714R@A0B4FRFP?O3PDP@PFO2'2P1PGf@R1P1P4P9P7C3RF714R@A014FRFP3O3P6P@PFO2f>fARFPFP4P;P9C3R@714RDA0F4@R@P7O3PGPDP@O2'2P?PBfBR@P@P4f5RDP;C3RG714A0@4GP9O3PBfCRBPBP4P<PDC3RG714A0B4GO2PFP>P<PDO3P1P>P<O2P3P?C6PFfDRFPFP4P>P<C3R>714RGA0F4>R>PDO3P1PGP>O2'2eW=W<P3P?O2n2001000000120000000W;X2=XB4X16P3P?O2n2001100000120101102XAAF8W>W9X34P<PDP;P<P7P3P?O3PDP7P3O2'2X9=X34X1<C4eW@W?X6:X78X82X55X40P;P9P7P3P?O5W6W7W8W5X40o"). Qed.

(* [comment removed for export] *)
Lemma mspecP_tpath {A} : forall (P : assn St) (m : M St A) Q s mo tr a s' mo',
  mspecP P m Q -> P s mo -> tpath nstepP (m s) mo tr (Ok (a, s')) mo' -> Q a s' mo'.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h01Ah13mo'h21Hh32HPh42Hmh52Hph61Ph71Qh81ai001ah91mh:2moh;3mo1h<1ph=1ri011rh>1sh?2s'h@2trp;1p;2p;4p;8p;3p;9p200R0g00c_R1p4p7210p8P0g00gVR2p6051001p8P0g00l>R3p60521001p8P0g00KPR4p4p73110p8g00fbj1;TP1j2:Tg001<j15TP3j44Tg00mjj20Tg00[ZR3j13Tg010Pj42Tg017Tj21TP4j86Tg00fEj37Tg00nJj38TP2l99Tp,2StR2#;R4f1R1,:2f2R5P4[g008?R4g009h#5f6R6f9R7f8R8f7R9P6C4P7P6f5R:O2g007Jg001\f;R;/02R<#3P7P9O1P6P:P;P2f4R;f3R7C2,1<P5G6f<R</02R=#3R>f:P8O1P9P3f>R3/02p-0P1g00\Rf?/02P3fAR3?721A8321f0R3O3X14W<P3P1O2n10110100020010100X;4X=>R>P6P<P2P:P;C2,1=R=P7P5P8P9P1O3P3M99P>P=P7O2P3b2W5W3W4X14X?2W8W@W:X>2W7W9W6X00P3O1X00o"). Qed.

(* [comment removed for export] *)
Lemma mspecP_program {A} (P : assn St) (m : M St A) s mo :
  mspecP P m (fun _ _ _ => False) -> P s mo ->
  forall {B} (f : A * St -> itree node (exc B)),
  tnf (ebind (m s) f) mo ->
  leaves_unreachable_m nstep (ebind (m s) f) mo /\ tsafe nstep nsafe (ebind (m s) f) mo.
Proof.
ltac2:(KReplay.run1 (kr_t_MSafeP ()) ["MSpecP"] "p'0h01Ah11Ph21ai001ah31mh42moh53mo'h63mo1h71si011sh81Bh91Hh:2HNh;2HPh<2Hmh=2a0h>1fh?1pi021ph@2s'p;1p;2p;4p;5p;3p;7p200R0g00c_R1p4p7210p8P0g00iLR2p6051002p8P0g00jGR3p6051002p8P0g00l>R4p60521001p8P0g00^cR5p4p7210p8p201R6g00RmR7p4p710p8P6g00Y7R8p6051002p8P6P3p60521001p8P6g01WWR9p6051000p8P6p100Wgp4p741110p8P6p100b\p4p73110p8P6P5p4p73110p8g00fbj1>TP1j2=TP4j44Tg00mjR4j21Tg00[Zj1<Tg00LDj28TP5j52TP7j35Tg00fEj36Tg00nJj37TP8j40Tg010Pj43TP2j79TP3j7;TP9j5:Tp,2StR9#>R3f1R2,=9R8g008?R7f4R5f3R1f2R:g00\RR;V7R<V9R=V5C4P5P:P2O2f7R>/19g007JR?%<2R@'8[P?f8/19P2f6RAf5RBO1f0RCD2=5@5P:P?f9R?/19R@P:P>PAO1R>P2D2PBP@P:P>P2PBP<V:P@P>PBf;R>P=UA6>92A7>92PCO3X57X?@P5P1P2O1PCP<V5C0X67X2@P5PAPBP1O3P4f:R4P9PAPBP:O1P2P<VAC0\;^67PCf<P;P4P?fAP9P5P1C3O1P:P<V4C0PCn010000000X9;X57X@9W2P2PCO2n2001102000120100101X=@F9F;PCD:W:W>X86W;W<X47X79X38X13X00P5P1P:P2PCO5W4X79W3W1X00o"). Qed.

End MSpecP.

Arguments mspecP {St A} P m Q.
