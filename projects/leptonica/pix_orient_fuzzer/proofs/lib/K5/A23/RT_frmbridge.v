(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader premise of impl_realizes_f, passed on to impl_realizes, with impl_realizes_f's recorded proof replaced by a plain proof; ARTM_PMfd_reader gives that premise at the fd frame PMfd). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import CatSim ShapeAlg AsanAcct AsanAcctShape.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode RelSpec RzCPS NodesA NodesA_wv FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import X_bridge.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import FrmExec FrmRun RT_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_frmbridge () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrK47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K53Lib5ITree4respC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib2K53Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree4implC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib2FP4frm0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K69OSSVerify5KrLib2K53Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236FrmRun8evt_frm0C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree4nretC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23<RT_frmbridge9nret_fcsrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG8X_bridge2TTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23<RT_frmbridge8impl_frmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG8X_bridge3tokC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG8X_bridge=impl_realizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree9impl_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree5epostC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I79OSSVerify5KrLib2K53Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53Lib5RzCPS:mat_stableC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53A238RT_iface4frmWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3ASTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC69OSSVerify5KrLib2K53Lib5RzCPS5macctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS2HZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:AST_conseqC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K53Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K53Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3HIDC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC69OSSVerify5KrLib2K52AS8AsanAcct8restrictC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K53Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init5Logic4True01".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma nret_fcsr : forall ms eff, ms_fcsr (nret ms eff) = ms_fcsr ms.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_frmbridge ()) [] "h03effh12msp;1p;2p10000p4p7210R0p1000\p4p710p8P0p10018p4p710p8g001Vj10Tg002;j14Tg002Yj12Tg003<j11Tg004;j23Tg004Ug005\g006R#0#0#0#0#0#4#2f1#1'3W0W1o"). Qed.

Section Bridge.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.
Hypothesis Hrom : rom_frm_ok segs = true.

(* [comment removed for export] *)
Lemma impl_frm : forall {nd : Type} (atn : nd -> machine_state -> Prop) {R} (t : itree nd R) Q ms,
  impl segs atn t Q ms -> frm0 (ms_fcsr ms) -> impl segs atn t (fun r ms' => Q r ms' /\ frm0 (ms_fcsr ms')) ms.
Proof using Hrom.
ltac2:(KReplay.run1 (kr_t_RT_frmbridge ()) ["Bridge"] "h03rsph13ms'h21rh33ms1h41Qh52msh62F0h71Hh82H0h91th:2F1h;2H'h<3Hath=2Hkh>2IHh?1Rh@3atnhA1bhB1khC1nhD2ndp;2p;7p;1p;3p;6p;4p200R0g0077R1p4p710p8p202R2g0080R3p4p7210p8P2g008kR4p4p741110p8P1j26TP4j70Tg003<j13Tg009aj15Tg00:TR4j21Tg00:oj39Tg00;hj68Tg00<cj47Tg00=\j22Tg00>Rj3<Tg001Vj14Tg002;j1;Tg002Yj1:Tg00?Fj2ATg0018j6@Tg00@Hj4?Tg00@cj6=TP3j6>Tf0R3g004UR1p-0[R5[f2R6/63f3R7f1R81678P5\6R9f6R:p,4segsR;f5R<f4R=P6P8P3F0%38#5R>f8R?P;f7R@P:P=P<P8P3O2%33#5RA'1X11RBX2:RCP6F0[[^51]4W9P:P;P<P=A9:=6P8P3F0P;p,4HromRDP7P=O1P6P8P3E8P?P;P@P:A9?:=PCP6F0eX6>W7X51X49X28g005\R916<7[P5\=R5P?P;P@P:P7P6O1P8P3F0f:RCP;f9REP?P<P=O1PBX2?RBP6F0\>[^51]4\9P?P;P@P:P?P:P=P7C7P8P3F0P;PDPCP@P3O2f<RDP;f;RFPCP@P3O1P<1283RGF0^09'1X31P6P8P3E8PFP?P3O2RHf=RIP;PDPFP?P3O1RJP:PGF0^09'1X31P3O1/1AX11=<;6P;PDPEP3O2f>RKP;PIPDPEP3O1RLP@PGF0^09'1X31P3O1/1AX11PIP;PDPFPJP?P8P3O2/1AX11X2FPGF0^09,1HX31P7P3PIPCP3O2f?RHP;PKPIPCP3O1RJP?PGF0^09'1X31P3O1/1AX11P3O1P4PDPEP8O2PKP;PIPDPLP@1263F0^09'1P>PIPCP6O2PHP;PKPIPJPCP8P3O2/1AX11X2I1273F0^09'1P3PKPFP7O2f@RJP;PHPKPFP3O1PE12=3F0^09'1P4PHPDP=O2fAR=P;PJPHPDP3O1PC12<3F0^09%3<#5P=PKP:O2RDfCR4P;fBRFP=PKP3O1PKP8P3O2/1AX11X2=12@3F0^09'1[P3fDR@P;P4PFPHP3O1PI12?3F0^09%3?#5P@P=PEO2fFP;fEP@P=P3O1P=P8P3O2/1AX11X2@12C3R@F0^09P6PJP3PHP@P6P3O1g006R#4#4#4#4#4#;#:RH%3C%53XAHP8%3@1AC3E@O5X09C?W:W=X<DP8P3O2n2001000000120000000W8P8P3O2n2001000000120000000W8X31E=b;PCP;PEP?PCP?P:P<C7PBP6F0eX6>W7X51X45W>WBXC7P3E>W9X?2W@XD0o"). Qed.

Theorem impl_realizes_f : forall {X : Type} (chans : list Z) (t : itree node (exc X)) A PM (Q : X -> machine_state -> Prop)
    (T : X -> TSet) ms c,
  mat_stable PM ->
  (forall mo fd, PM mo -> In fd chans -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd))) ->
  (* LPS 08b1429: a nonempty writev needs the channel's reader, as in [impl_realizes] *)
  (forall mo, PM mo -> m_channel_reader mo = true) ->
  tok chans t -> AST segtop A (frmW (eq ms)) PM c -> impl segs (at_node segs) t (epost Q) ms ->
  (forall x ms' c', Q x ms' -> AST segtop A (frmW (eq ms')) PM c' -> realizes segs c' (T x)) ->
  realizes segs c (TT t T).
Proof using Hwx Hsegs Hrom.
  intros X chans t A PM Q T ms c HPM HFD HRD Htok Hc Him HK.
  assert (F0 : frm0 (ms_fcsr ms)).
  { destruct Hc as (_ & [E HF] & _ & _). rewrite E. exact HF. }
  apply (impl_realizes segs segtop Hwx Hsegs chans t A PM (fun x ms' => Q x ms' /\ frm0 (ms_fcsr ms')) T ms c HPM HFD HRD Htok).
  - eapply AST_conseq; [exact Hc | | intros mo Hmo; exact Hmo]. intros ms0 [H _]. exact H.
  - eapply impl_mono; [exact (impl_frm (at_node segs) t (epost Q) ms Him F0)|].
    intros [|x] ms' [H1 H2]; cbn [epost] in *; [exact I | exact (conj H1 H2)].
  - intros x ms' c' [HQ HF] Hc'. apply (HK x ms' c' HQ).
    eapply AST_conseq; [exact Hc' | | intros mo Hmo; exact Hmo]. intros ms0 E. split; [exact E | subst ms0; exact HF].
Qed.

End Bridge.

(* LPS 08b1429: the channel-reader premise of [impl_realizes_f] at the callers' fd frame: the third
   conjunct of [PMfd]. The recorded proofs of I_fwrite and X_exit pass it. *)
Lemma ARTM_PMfd_reader : forall RT Σ F0 fs0 mo, ARTM RT Σ mo /\ PMfd F0 fs0 mo -> m_channel_reader mo = true.
Proof. intros RT Σ F0 fs0 mo (_ & _ & _ & H). exact H. Qed.
