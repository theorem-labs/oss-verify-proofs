(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
     ADepot_iface ARep ALayout AHeapP AFake_iface AFake_arep AFake0k_iface AFake_arep0k AF_fse_rd_iface AF_fse_rd_closedF
     AF_huf_tbl_iface AF_huf_tbl_iface2 AF_huf_bdt AF_huf_sdec AF_huf_fdec AF_huf_fdw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_fdwc () := "C46Stdlib5Lists4List2hdC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5AsanW<AFake_arep0k<fake_flag_AIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<AFake_arep0k?fake_release_AIC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib5AsanW<AFake_arep0kBstack_malloc_0k_AIC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib5AsanWAAF_fse_rd_closedFAfse_readk_closedFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:AF_huf_bdt@fse_build_proofAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AF_huf_sdec9safe_decAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AF_huf_fdec9fast_decAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:AF_huf_fdwAfse_decomp_proofAC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5AsanW;AFake_iface5fflagC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AFake_iface9afake_rngC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
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
  Theorem fse_decomp_closedA : forall k, Z.of_nat k < 16382 -> fse_decomp_stmtA AI afake_rng k.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_fdwc ()) ["CANSEC1"; "Inst"] "h04__x1h11xh27__arithh34__ffh48__varmaph55__with64cstrh72Hkh81kh91yp;1p;2p;9p;7p;3p;4p;<p;8p-1p10000p4p710p8g000GR0j14Tg000gj1;Tg001Lj16Tg001jR1j20Tg002Fl9VTg003Jj7LTg004Qj1ETg0056j2CTg005Rj1BTg0062j1ATg006Rj2?Tg0070j1>Tg007Nj1]Tg0089j2YTg008\j25Tg009?j1UTg009aj2KTg00:Cj23Tg00:]j2DTg00;Ij3FTg00;cj3GTg00<Bj4HTg00=4l<ITg00>>R2j1JTg00>]j18Tg00?Bj29Tg00?_j1@Tg00@=l<OTg00@bj3PTg00AEj4QTg00B0l<RTg00C>j2STg00DDj1TTg00EDj1\Tg00FDl<[Tg00GKj4ZTg00H6j7XTg00HZj8WTg00I>l<=Tf0R3#8#8p=2g00IcR4f1R5g00JAP3CZp=:P5g00JhR6g00KGR7P7g00KgR8P3g00LGFXp=7%;3#;p=1f3R9P6P7P7P8f2R6P5P3GWp=<g00LgR:P:P4P4P2P0P0P9g00MFP6P5P3M<=p=MP:P4P4P4P0P0f5f4P9P6P5P3M<=p=N%43R0g00MjR2#2#2#2#2#2#2R;#;#6R<'0p,2rcR=p,2AIR>g00NOg00OKP=p,2DIR?p,2AQR@p,4ASECRAp,2CIRBp,5CI_OKRCP>p,1ERDp,2ECREM9VP=P?P@PAp,2HLRFP>PDFLP5P=P?P@PAPFPBPCP>PDPEP5%E5RGg00PKRH%45RI'CRJg00PiRK#BRL%AKRK1?45RM%>4RN%]4RO1Y42RP154<':,7ORQ%U7R7%12#1#1#1#1#1#1#6RR,54,:P,7OC<1KO8R8P3P6g00QURSg00R5RT'31D36=FSTdAG4H5CHRHb3b4b5X04103<R<105R[^04P3%49P6O2R6b2b6M<IP=P?P@PAPFPBPCP>PDPE%J5RE%4ERD%8;#6R;'0%62R2,9IRC/0;P4P4P1P3X14RBP11053#@X94X14PDPCPBPB1340X1:PEPC1932X14P5PI134ICMENP;P;134;M<OPGPJPLPKPMPNPOPQP715429P4P154;':,7OC<P8PHb3b4b5X041952/0;\<^04P6b2b6CQM<R1S=>%T=%\=M<[W7X8:o"). Qed.
End Inst.
End CANSEC1.
