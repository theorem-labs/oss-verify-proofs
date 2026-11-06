(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Image ZBridge Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface
     ADepot_iface ARep ALayout AHeapP AFake_iface AFake_arep AFake0k_iface AFake_arep0k AF_fse_rd_iface AF_fse_rd.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_fse_rd_closedF () := "C46Stdlib5Lists4List2hdC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5AsanW<AFake_arep0k<fake_flag_AIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AFake_arep0k?fake_release_AIC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib5AsanW<AFake_arep0kBstack_malloc_0k_AIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9AF_fse_rd?fse_readk_proofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5AsanW;AFake_iface5fflagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface9afake_rngC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Inst.
  Variable DI : ADepotIface.
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
  Hypothesis HL : ahole_laws (AH DI AQ ASEC).
  Variable CI : list (Z * Z).
  Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P (AH DI AQ ASEC).
  Hypothesis EC : aci AI = CI.

  (* [comment removed for export] *)
  Theorem fse_readk_closedF : forall k, Z.of_nat k < 16383 -> fse_readk_stmtA AI afake_rng k.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd_closedF ()) ["CANSEC1"; "Inst"] "h01xh14__x1h22Hkh37__arithh44__ffh58__varmaph65__with74cstrh81kh91yp;1p;2p;9p;7p;<p;4p;3p;8p-1p10000p4p710p8g000GR0j14Tg000gj18Tg001Lj17Tg001jR1j21Tg002Fl9STg003Jj7ITg004QR2j1DTg0050j25Tg005Mj1@Tg005kj23Tg006El<VTg006jj1UTg007Oj2RTg007kj1QTg008Kj1NTg008kj2HTg009Ij1FTg009gj1ETg00:Rj2CTg00;5j26Tg00;Xj49Tg00<Cj1BTg00<ej3GTg00=Hj8ATg00=lj2JTg00>Nj2KTg00?:j3?Tg00?Tj3LTg00@3j4MTg00@ej4>Tg00APl<OTg00BZj8PTg00C^j1;Tg00DCl<<Tg00Dhj7TTf0R3#8#8p=2%;3#;p=0g00ELR4P4g00EkR5P5P2P0P0f3R2g00FIf2R6f1R7P3M<<p==P4P5P5P5P0P0f5f4P2P6P7P3M<<p=WP7g00FmR0g00GLR8P8g00GlR9P3g00HLFTp=:%43R:g00HlR;#8#2#2#2#2#2#2#7R<'1p,2rcR=p,2AIR>g00IQg00JMP7P=p,2DIR?p,2AQR@p,4ASECRAp,2CIRBp,5CI_OKRCP>p,1ERDp,2ECREM9SP=P?P@PAp,2HLRFP>PDFIP=P?P@PAPFPBPCP>PDPE%D7RE%4ERD%0;#0#0#0#0#0#0#7R>'1%47RC%7;RB'5RF/1>P5P5P1P3X05RAP11173#@X95X05PDPFPAPA135:X04PEPF153BX05P7PC135CC=EWP>P>135>M<V%U7g00KMRF/RCg00KkRC#Q%NC1H57%F5%E5RCP0P8P8P9P51C5;R;g00LWR0165<C9,:C%B8P5165B9G5;P0165>C9,:CGA1JC9P3P6g00M>RCg00M^R9'31K36=?C9dAL5F7CMb4b5b6X15113<157B/1>[^15P3%42P6O2b3b7C>M<OGPW2X84o"). Qed.
End Inst.
End CANSEC1.
