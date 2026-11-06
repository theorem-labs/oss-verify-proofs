(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface D_iface D_defs I_iodefs X_xdefs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import HandoffKit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_HandoffA () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib2K52AS8AsanInit5argH0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K52AS8AsanInit:argH0_highC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K52AS8AsanInit5SINV0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6cs_ispC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC45stdpp9bitvector;definitions;bv_unsignedC79OSSVerify5KrLib2K52AS=AsanPlanSound3APS2uEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS7co_sinvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit8SINV0_spC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C79OSSVerify5KrLib2K52AS8AsanPlan2AP5e_sp0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC47Corelib4Init5Peano2ltC79OSSVerify5KrLib2K52AS:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit2E0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K52AS8PropExec8wrap_memC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC79OSSVerify5KrLib2K52AS8AsanPlan2AP3NX0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP6V_ARGCC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53A02<HandoffImage:hs_regs_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage8hs_ro_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC69OSSVerify5KrLib2K53A02<HandoffImage9hs_stk_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;HandoffArgv:hs_argv_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:HandoffCLX9hs_clx_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP4a_fdC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC69OSSVerify5KrLib2K52AG:HandoffKit9canon_cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs5STARTC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK79OSSVerify5KrLib2K52AS8AsanPlan2AP3afd02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib2K53A02<HandoffImage7hi_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53A02<HandoffImage6hi_uspC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib2K53A028RT_iface8rt_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage:hi_mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:HandoffCLX6hi_clxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;HandoffArgv7hi_argvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage6hi_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG:HandoffKit2mHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53A02<HandoffStart@start_of_handoffC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS8AsanPlan2AP3afd00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS8AsanPlan2AP3afd01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028HandoffA7hsa_sp0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib2K53A028I_iodefs8OUT_repAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_iodefs8ERR_repAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs5XENVAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028HandoffA5hs_fxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026Layout6a_mainC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K79OSSVerify5KrLib2K52AS8AsanPlan2AP3afd03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs7MAIN_RAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage7USP_OFFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028HandoffA8hsa_argcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028HandoffA=hsa_argH_highC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG:HandoffKit=hole_of_canonC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6cfg_ofC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K52AS=AsanPlanSound>asanreflect_fxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028HandoffA8hs_startC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hs_fx : PropExec.FPState := PropExec.fx0.

(* [comment removed for export] *)
Definition hs_start_ok (ch : acs) : bool :=
  (hs_regs_ok ch && hs_ro_ok asegs ch && hs_stk_ok ch && hs_argv_ok ch && hs_clx_ok ch
   && match a_fd ch with FdStd => true | _ => false end)%bool.

Section Start.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).
#[local] Notation usp := (bv_unsigned sp).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH fs E ch R FULL model.
Hypothesis HT : hs_start_ok ch = true.

(* [comment removed for export] *)
Variables (RT : rt_sig) (LIB : mem -> Prop) (Σ : rts RT).
Hypothesis Hallow : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb (rt_allow RT Σ) p = true.
Hypothesis Hawf : A_wf (rt_allow RT Σ).
Hypothesis Hminv : MInv (rt_allow RT Σ) model.
Hypothesis Hartm : ARTM RT Σ model.
Hypothesis Hsp0 : rt_sp0 RT Σ = usp.
#[local] Notation m := (mH FULL model (rt_allow RT Σ)).
Hypothesis Hart : ART RT Σ m.
Hypothesis Hsig : sigma0_ok RT Σ (usp - USP_OFF).
Hypothesis HLIB : LIB m.

Lemma hsa_argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffA ()) ["Start"] "h02E1h11Hh21ap;1p;9p;3p;<g0000j10Tg000Uj15Tg0013j12Tg001Vl91Tg002Oj34Tg002il<3Tg003gg004f#0#0#0#0#0#0#5#2g005Kp,2phR0p,2spR1p,5rdrawR2p,4argvR3p,4envpR4p,3uidR5p,2hwR6f1R7f0R8M91g005k34P0P1P2P3P4P5P6p,3Hspp,3Hvaf2P7P8M<3W1W2W0o"). Qed.

(* [comment removed for export] *)
Lemma hsa_sp0 : bv_unsigned (vm_init_sp (m_vmmaps model)) = usp.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffA ()) ["Start"] "h02I1h12_Hh21ah31zp;8p;7p;=p;1p;2p;3p;?p;6g006Kj8>Tg001Vj7=Tg007Dl=7Tg0000j10Tg000Uj1<Tg008Gj19Tg009>j18Tg00:7j23Tg00:aj26Tg002Oj31Tg00;`j22Tg00<<R0j24Tg00<Wl=5Tg00=[l?;Tg00>Wj6:Tg00?5R1p,1AR2p,3nx0R3p,5LIMITR4p,2phR5p,2spR6p,5rdrawR7p,4brk0R8p,4argvR9p,4envpR:p,3uidR;p,2hwR<G>R=P5P6P7P9P:P;P<F=R>p,2fsR?p,1ER@p,2chRAp,1RRBp,4FULLRCp,5modelRDp,2HCREM=7g00?mRFg004f#0#0#0#0#0#0#<RG%9D#8'3RHg00@K,6@RI31RJg00AG/2Hg00BB,2H'4RK'4P0PJPK13G6RG91FHf0R0PFPIA1F0GX3FP5P6P7P8P9P:P;P<p,3Hspp,3Hvap,3Hvep,4HfitP@PCP1P2P3P4P=P>P?P@PAPBPCPDPEM=5M?;PHf1RHE:X1KX0JPHP0O2n2001000000120000000b2o"). Qed.

Lemma hsa_argc : ev E V_ARGC = Z_to_bv 64 (Z.of_nat (length argv)).
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffA ()) ["Start"] "h02Hvh12_Hh27__arithh34__ffh48__varmaph55__with61ah71bh81nh91sp;8p;7p;=p;2p;1p;3p;9p;4p;6p;<g006Kj8VTg001Vj7Ul9?Tg00<Wl=CTg00C=R0j26Tg0000j10Tg000Uj19Tg0013j18Tg00CUj24Tg00DQj8ATg002Oj31Tg00EGj1=Tg00Eij8<Tg00<<R1j2TTg00Fej1;Tg00GEj2STg00GeR2j1JTg00HEj2ITg00Hkj25Tg00IEj12Tg00Idj17Tg00JBj1BTg00JgR3j2DTg00KCj1FTg00Kcj1GTg00LAj1HTg00L_j1@Tg00MJj2:Tg00Mmj4KTg00NXj7>Tg00O<j2LTg00O^j2MTg00PJj3NTg00Pij4OTg00Q[j4PTg00>Wj6QTg00RFl<RTf0R4#2#2p=3g00RkR5g00?mR6P0P2P3g00SJf5f4f3f2R3f1R2P4M<Rp=Eg00?5p,1Ap,3nx0p,5LIMITp,2phR0p,2spR7p,5rdrawR8p,4brk0R9p,4argvR:p,4envpR;p,3uidR<p,2hwR=GVP0P7P8P:P;P<P=FUp,2fsp,1ER>p,2chp,1Rp,4FULLR?p,5modelp,2HCM=Cg00SlR@,64g004fRA#0RB#0#0RC#0#0#0#9RD#8RE14>2P0P7P8P9P:P;P<P=GAR9/4231[^85R5g005KRFP0P7P8P:P;P<P=P>P4M9?g005kRG31%9C#8RC#=P?P2O1P0P7P:P;P<P=P8P2G<31[^6ER8'TP1P5P8g00TfR1,4>R>%;C/S:#J,IDRD51EP4PE1491A1E4DX7E15EDP>P2P1g00Uc#2R>%2>#3#3#3#3RD'6%7ARA%BB#0#7RB'DREP>PA156APDPB156BEEg00VBRD#F%;D%G6%H6%@6RDg00Vng00WMR>P>g00WmR>P61:6Ag00XM1:6BCKg00Y4F>1LD>P4P315FG1M43=1FGdg00YT=N62COb3b4b5PEP4b2CP161@eO2EQX18X05P2P4O2n2001000000121000000b9o"). Qed.

Theorem hs_start : START RT OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg asegs R a_main FULL model).
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffA ()) ["Start"] "p'0h01zh11Hh23Hfdh34__x1h42H3h52H4h62H5h72H6h83R10h93R11h:2R2h;1Sh<2U1h=2U2h>2U3h?2U4h@2U5hA7__arithhB4__ffhC7__sat12hD8__varmaphE5__withF1ai001ahG2HThH5HargvhI4HclxhJ4Hfd'hK5HregshL3HrohM4HstkhN2R1hO2R4hP1bi011bhQ1ehR1ki021khS3leni033lenhT3offi043offi051xp%0p;1p;2p;3p;6p;8p;7p;>p;Cp;Dp;Kp;Bp;4p;Xg00Z2j1zTg00[5j2yTg00\6j2ETg00\Tj1[Tg00]Vj1xTg00^Xj1rTg00_Xj1cTg00`Sj3?Tg00<<R0j21Tg00a6j6ZTg00b5j8WTg002Oj36Tg00Hkj2UTg00bmj6HTg00cIj3qTg00dEj2PTg006Kj8kTg001Vj7bTg00ddl>aTg0000j10Tg000Uj1ITg0013j1STg00JBj1>Tg00Idj15Tg00HEj2;Tg00edj2<Tg00CUj2\Tg008Gj1YTg009>j1XTg00:7j2KTg00f\j28Tg00g9j24Tg00gVl>VTg00hUj2FTg00Jgj2=Tg00;`j22Tg00Fej1TTg00GEj2wTg00Gej1vTg00i5j2tTg00j2lCpTg00k5lDoTg00l2lKnTg00m1lBmTg00n0j3lTg00nhj4@Tg00o]j2jTg00>Wj6OTg010Xj2dTg00KCj1eTg011Ij2fTg00LAj1gTg00L_j1hTg011gj2iTg00MJj2CTg012Jj3NTg012mj3QTg00Mmj4RTg00O<j2`Tg00O^j2_Tg00PJj3^Tg00Pij4sTg013Pj4LTg013klX]Tg00NXj7uTg005KR1f0R2g005kR336p=3g0154R4g0160R5762p=G%02#0p=Bf3R6f2R7f1R8/;236p=7g00?mR9g00YTR:762p=D%02#0#0#0p=J%02#0#0#0#0#0#0#0p=A%>2#>p=:P9P6P7P8P2g016lEHp=9P8g00Vng00WMR;P;g00WmR;P2g00Y4Fup=Mp,2chR<#zR=g00?5R>/y<R?'ER@%[<RA'ERB%x<RC'ERD%r<RE'ERFP4P1%c<RGP3g017hRHPHn011050003003010210310400RIp,2HT3?%3FRF%3IRI'1P0PFPIp,2RTRJg018HS00g019ES01g01:BS02p,3LIBRKp,4argvRLp,2fsRMg01;;P>p,1RRNg01<5p,4FULLROp,5modelRPEZGWRQP2A?DE8%3DRD%3ERE'1P0PDPEPQP2A?BC8%3BRB%3CRC'1P0PBPCPQP2A?@A8%3@R@%3ARA'1P0P@PAPQP2A?=?8%3=R=%3?R?'1P0P=P?PQP2PGP4P4P4P1P2P3PHPHn011050003003010210310400#3%G8]2P2A61331U45W2g00Rkg01<nRRA61H3RSP1PHP1p-0P2g01=nRHg01>Kn0110100020000XQ1g01>gP3P2EHRTPHf4?q67#G/P2b1W2XTRWSWRP7P8P2O3PTPHg01?C=645/P2b1X2Sn011000003003010210310400fEO1bF%GGP>p,1ARGp,3nx0RSp,5LIMITR5p,2phR4p,2spRHp,5rdrawRTp,4brk0S03PLp,4envpRRp,3uidR6p,2hwRUGkRVP4PHPTPLPRP6PUFbRWPMp,1ERXP<PNPOPPp,2HCRYP7M>ag004fRZ#0R[#0R\#0R]#0R^#BR_#IR`#SRa%>[Rb#IRc%5Z';,<NP`g01@?C7RdPa%5\,;c,<NP`g01A9C7R\%0b#5,;c,<NReg00Tf,\XS0456aRfPa%>b#5,;c,<NRbP`%YP#X,K`Rg%5]Rh'8RiC7RjPa%5[,;c,<NRcP`g01B0R[,4gRkC7Rl'1Rm'1Rn'1Ro'1P0PdPoPQP2P0P\PnPQP2P0PfPmPQP2P0PjPlPQP2P>PGPSP5PVPWPMPXP<PNPOPPPYfCM>V%5^R^,Fk#DRp1=kiRig01C0Rq,4g%B_#J#AR_#5Rr'8/2kRs12kgRt%>ZRu#:#:#:#:#:#:#:#0#B#J#A#A#A#5Rv/2gRw'1Rx'1Ry'1Rz'1P0PpPzPQP2P0PiPyPQP2P0PsPxPQP2P0PtPwPQP2PgPaPbP`182hRQC7X09fBR01K`HR{C9PaPbP`18{hRbC7PgPaPcP`142[R|C7X09P0P{C9PaPcP`14{[R[C7Pg1F|^#DX09f?P{C91F[^#DRcPg1=|QX09f<P{C91=[bR0Pg142qS05/8rR}/2|X09f9P{C914{qS06/8r/2[RqPg12|2X09f6R~P{C912[{Pg12v2X09P~P{C912v{PaQ04A6ae2XPafM%I]#S#T/wL#v,;`R`g01CnEHA6ae`PGPSP5PVPWPMp,7HULL_okR`p,7HsegtopPXP<PNPOPPPYPJQ00Q01Q02PKPLp,2ΣRep,6HallowRap,4Hawfp,5Hminvp,5HartmfZP[PbfVP~fRP2f7p,4HartP>PGPSP5PVPWPMp,<SEGS_in_hullR~P`g01DkR]PXP<PNPOPPPY1tJeRvPaf[MCpPGPSP5PVPWPMP~P`P]PXP<PNPOPPPYPvPaPKp,4HLIBfjMDoPGPSP5PMP4PHPTQ03PLPRP6PUp,3Hspp,3Hvap,3Hvep,4HfitP~P`PXP<PNPOPPPYPvPafeMKnP>PGPSP5PVPWPMP~P`PXP<PNPOPPPYPvPaf`MBmP>AlOPvRv%0_#B#5R_,4gPkC@PgP>Pv142_RgP|C@X09P2P{C9P>Pv14{_R|P[C@P9P{P>PvQ05P[C@X09P2P>PvQ06P[C@e1jJeRep,4Hsp0RJEOb;b;p,4HsigP9P{12}[,10,1cX09%Ju#5Ru,4{R}/F^R[#D1=}bRb18|r/2}R|'1f5PbP|1d}^R|12:}12:^12:[[[R[g00VBR^#eR}%T^R^1f98Rb%g9Rv%h9R>P91i9ZRZ1C9u5N9Rkg00XM1C9h9Q9ZCR'M1`>;R;P2P71U131_27#3dA^9:8CsR:bBbDbEX39142uRu/=Q^39P2P{O1R{bAbCP|P[P}P^PbPvP91C9_9N9Z1C9r5Q9g01EmPkCR,M>P;P:bBbDbEX3918gr/2u^39P{bAbCCLCL110q,1cePePJEOMX]b8b@b?b>b=b<b:b9X@wX?tP8P2O2n2001000000121000000X1xX>sP8P2O2n2001000000121000000X1yX=iP8P2O2n2001000000121000000X1zX<pP8P2O2n2011000000121000000b1X:lX9jP8P2O2n2001000000121000000X1mX8fP8P2O2n2001000000121000000X1nXO\P8P2O2n2001000000121000000X1oXNdP8P2O2n2001000000121000000bFbJXL?XK=P8P2O2n2001000000121000000b4XMAX4@P8P2O2n2001000000121000000b5XHCX5BP8P2O2n2001000000121000000b6XIEX6DP8P2O2n2001000000121000000b7X2IX7FP8P2O2n2001000000121000000bGo"). Qed.

(* [comment removed for export] *)
Theorem hs_hole : forall T,
  (forall c, START RT OUT_repA ERR_repA XENVA LIB argv fs c -> realizes asegs c T) ->
  srealizes asegs (APS.cfg_of asegs R a_main FULL model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffA ()) ["Start"] "h05Hmainh11Th21cp;8p;3p;6p;5g00b5j85Tg01FTj34Tg00a6j60Tg01GRj81Tg01HUj53Tg01IXj32Tg01JVg01KNp,2RTg018Hg019Eg01:Bp,3LIBp,4argvp,2fsf0R0G5g00?5R1f1R2f234[]2g01LCR3P1p,1RR4g01<5R5p,4FULLR6p,5modelR7P2P0P3P1P4P5P6P7E0g01MJO2G1P1P4P5P6P7D3=212eW0W1o"). Qed.

End Start.
