(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs StackLayout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface D_iface D_defs I_iodefs X_xdefs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import HandoffKit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import HandoffStart HandoffImage HandoffArgv HandoffCLX HandoffA RT_state RT_rep RT_init RT_init_mem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_HandoffRT () := "C69OSSVerify5KrLib2K53A028HandoffA=hsa_argH_highC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib2K52AS8AsanInit5argH0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K52AS8AsanInit5SINV0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;RT_init_mem<rt_init_glueC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6allowAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027RT_init6sigma0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state9rtA_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct4A_wfC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep6ARTM_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_state7rtA_sp0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K52AG:HandoffKit2mHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026RT_rep5ART_AC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53A026D_defs9sigma0_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K52AG:HandoffKit9canon_cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026D_defs5STARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028HandoffA7hsa_sp0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib2K53A028HandoffA8hs_startC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I79OSSVerify5KrLib2K52AS:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C79OSSVerify5KrLib2K52AS8AsanPlan2AP4CEILC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53A026RT_rep3RTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02<HandoffImage7USP_OFFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_iodefs8OUT_repAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028I_iodefs8ERR_repAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A027X_xdefs5XENVAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A029HandoffRT6hrt_fxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A026Layout6a_mainC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG:HandoffKit=hole_of_canonC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6cfg_ofC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K52AS=AsanPlanSound>asanreflect_fxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A029HandoffRT;hs_start_rtC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hrt_fx : PropExec.FPState := PropExec.fx0.

Section StartRT.
Variables (A : atable) (nx0 : nat) (LIMIT : Z) (fs : Fs).
Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hlim : LIMIT = VMLIMIT.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).

Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH fs E ch R FULL model.
Hypothesis HT : hs_start_ok ch = true.
Hypothesis HTR : hs_rt_ok A ch = true.

Variable LIB : mem -> Prop.
#[local] Notation Σ0 := (sigma0 A E ch model).
Hypothesis HLIB : LIB (mH FULL model (rtA_allow Σ0)).

Theorem hs_start_rt : START RTA OUT_repA ERR_repA XENVA LIB argv fs (canon_cfg asegs R a_main FULL model).
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffRT ()) ["StartRT"] "h01Hh14Hsigh24Hsp0h31ah41zh52AHh61Eh76Hallowh84Harth95Hartmh:4Hawfh;5Hminvh<4Husph=1pp;9p;1p;2p;8p;7p;Cp;3p;4p;6p;Fp;Ug0000l9OTg0012j10Tg001Wj1?Tg0025j1;Tg002Xl9Nj7<Tg003Qj23Tg004;j2>Tg004Wj8=Tg005PlC:Tg006Tj39Tg007Wj27Tg008Xj4MTg009Rj1LTg00:Pj1JTg00;Hj2FTg00<Bj2ETg00=;j1DTg00>7j1@Tg00>nj1ATg00?gj32Tg00@Aj3BTg00A9j2CTg00B1j25Tg00BNj36Tg00CJR0j21Tg00Cej6GTg00Ddj8HTg00E\lFITg00FXj68Tg00G4lUKTg00H1f0R1g00HQ32p=4p,2phR2p,2spR3p,5rdrawR4p,4argvR5p,4envpR6p,3uidR7p,2hwR8p,3HspR9p,3HvaR:M9Og00I1g00J0#0#0#0#0#0#0#?R;#;R<P2P3P4P5P6P7P8f1R=P1M9N#4g00JU13;='>[]3]6p,1AR>p,3nx0R?p,5LIMITR@P2P3P4p,4brk0RAP5P6P7P8G=P2P3P4P5P6P7P8F<p,2fsRBp,<SEGS_in_hullRCp,7HULL_okRDP1p,7HsegtopREp,6Hshoffp,4Hlimp,1ERFp,2chRGp,1RRHp,4FULLRIp,5modelRJp,2HCRKp,3HTRMC:A9>FG/71#4P>PFPGPJCMRL#LRM/7=#4[^=<R<%JMRN1FMJRO1ELJRPg00KPRQ%DLRR%@J#A,3;RS32RTABIJM,CLRMg00KnRUg00LdRV,5S76LRW'1RX'1RY'1RZ'1R['1R\'1P0P<P\PUg00Mdg00Nag00O^p,3LIBR]P5PBg00PWg00QSPHg00RKPIPJEGGHR^P1P0PNP[P^P1P0POPZP^P1P0PPPYP^P1P0PTPXP^P1P0PMPWP^P1P>P?P@PBP2P3P4PAP5P6P7P8P9P:p,3HveR^p,4HfitR0PFPGPHPIPJPKMFI13;3R;92QSPQPSA2QR1X4Qf6P;P1E8A2QR;PQPS151V96ULX4Qf2P;P=E815;V96ULP>P?P@PBP2P3P4PAP5P6P7P8P9P:P^P0PCPDPEPFPGPHPIPJPKp,2HTPUP]PLfHfDf@f<P=f4P1p,4HLIBMUKb1b2b<X1WX8MP=P1O2n2001000000121000000X0XX2TP=P1O2n2001000000121000000X0YX9PP=P1O2n2001000000121000000X0ZX;OP=P1O2n2001000000121000000X0[X:NP=P1O2n2001000000121000000X0\X7<P=P1O2n2001000000121000000b3b5o"). Qed.

(* [comment removed for export] *)
Theorem hs_hole_rt : forall T,
  (forall c, START RTA OUT_repA ERR_repA XENVA LIB argv fs c -> realizes asegs c T) ->
  srealizes asegs (APS.cfg_of asegs R a_main FULL model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffRT ()) ["StartRT"] "h05Hmainh11Th21cp;8p;3p;6p;5g00Ddj85Tg00SDj34Tg00Cej60Tg00TBj81Tg00UEj53Tg00VHj32Tg00WFg00X>g00Kng00Mdg00Nag00O^p,3LIBp,4argvp,2fsf0R0G5g00QSR1f1R2f234[]2g00Y3R3P1p,1RR4g00RKR5p,4FULLR6p,5modelR7P2P0P3P1P4P5P6P7E0g00Z:O2G1P1P4P5P6P7D3=212eW0W1o"). Qed.

End StartRT.
