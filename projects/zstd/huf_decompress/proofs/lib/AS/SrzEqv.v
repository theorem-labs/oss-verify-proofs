(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SimInv ShapeAlg DivergeSim SpinAlg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import RegsEqv0.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_SrzEqv () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init6Specif9proj1_sigC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC59OSSVerify5KrLib2AS8RegsEqv07cfg_eqvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC59OSSVerify5KrLib2AS8RegsEqv06ms_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib2AS8RegsEqv0;ms_eqv_reflC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib2AS8RegsEqv0<ms_eqv_transC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C59OSSVerify5KrLib2AS8RegsEqv0Csstep_cfg_eqv0_scfgC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS8RegsEqv06to_eqvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02C59OSSVerify5KrLib2AS:DivergeSim;silent_loopC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC59OSSVerify5KrLib2AS8RegsEqv09regs_eqv0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC59OSSVerify5KrLib2AS8RegsEqv08regs_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib2AS8RegsEqv0Cmi_account_step_eqvC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlgEsrealizes_of_realizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS6SrzEqv=srealizes_eqvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlgErealizes_of_srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib2AS8RegsEqv0=regs_eqv_reflC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Instance srz_fx_as : OSSVerify.Proofs.zstd.huf_decompress.lib.AS.PropExec.FPState := OSSVerify.Proofs.zstd.huf_decompress.lib.AS.PropExec.fx0.
Local Instance srz_fx_lib : OSSVerify.Proofs.zstd.huf_decompress.lib.Lib.PropExec.FPState := OSSVerify.Proofs.zstd.huf_decompress.lib.Lib.PropExec.fx0.
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

Lemma cfg_eqv_refl : forall c, cfg_eqv c c.
Proof.
ltac2:(KReplay.run1 (kr_t_SrzEqv ()) ["WithSegs"] "p'0h01ci001ch12moh22msi019cfg_modeli026cfg_msp;2p;1p;3p;4p10000p4p70R0p1000`p4p710R1p8P0p1001<p4p710R2p8P0p1001Zp4p710R3p8P0p1002:p4p710R4p8P0p1002Xp4p7210R0p8p10035p4p70R5P1p8P5P2p8P5P3p8P5P4p8P5P0p8p1003cp4p7210R5P1p8P5P3p8P5P4p8P5P0p8p1004Op4p70R5P1p8P5P2p8P5P3p8P5P4p8P5P0p8g005Ej28Tg006=j27Tg0072j10Tg007ej21Tg008\j16Tg009Rj32Tg009lj13Tg00:hj24Tg00;Bj45Tg00;]R0P0f0R0/80P0g00<Rg00=YR5f1R4/70R3#0R2/12%63R3=253%321453C5W1W2P4P0O2n01100000120102101W0o"). Qed.

Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
Proof.
ltac2:(KReplay.run1 (kr_t_SrzEqv ()) ["WithSegs"] "p'0h01ci001ch11Hh21bh32G1h42G2h52H1h62H2h71ah89cfg_modeli019cfg_modelh9:cfg_model0h::cfg_model1h;6cfg_msi026cfg_msh<7cfg_ms0h=7cfg_ms1p;2p;1p;3p;5p;6p;4g005Ej21Tg006=j20Tg0072j12Tg007ej24Tg008\j13Tg009Rj35Tg00>Oj58Tg001<j67Tg00;Bj46Tg00;]R0P0f2R1f1R2'1R3f4R4/11\3[^00^20f0R5g00<RR6g00=YR7P0f3R8,04R4/12R9f6R:f5R;'0R</11\3[^00P5P0f8R3f7R='0R>1081'1R8f:R?f9R@'0RA/11\9[P5f;R9/0?R?/1<R<g00?LR1f</09R9#210=:R=#2'4RB%39%3=557R=f>R9f='0RC/14\8P5%2C10@3#2'4R@f?R3/09#3%3A557RAP1PBP=fBfA'0/1>P5fEfD'0R>#2R=%2?RB'4%3>R1%3?R9557P=f@PBP:P2D8P7P1P3P9P;P5E7C611>?eX4AX3@P2P5O2n2001000000120000000X1<W6W5P2P5O2n2001000000120000000W1X:7X=6P2P5O2n01100000120102101X00X97X<6P2P5O2n01100000121102101X20W8W;P2P5O2n01100000121102101W7o"). Qed.

(* [comment removed for export] *)
Lemma sstep_next_eqv : forall c c' e c2,
  cfg_eqv c c' -> sstep_cfg segs ACFG c e (SNext c2) -> exists c2', sstep_cfg segs ACFG c' e (SNext c2') /\ cfg_eqv c2 c2'.
Proof.
  intros c c' e c2 Heqv Hss.
  destruct (sstep_cfg_eqv0_scfg segs ACFG c c' e (SNext c2) Heqv Hss) as (X' & Hss' & HX).
  destruct X' as [c2'| ]; cbn in HX; [|contradiction].
  exists c2'. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma silent_loop_eqv : forall P : config -> Prop,
  silent_loop segs P -> silent_loop segs (fun d => exists c, P c /\ cfg_eqv c d).
Proof.
ltac2:(KReplay.run1 (kr_t_SrzEqv ()) ["WithSegs"] "p'0h06model'h13ms'h21ci001ch31Hh41Kh54Heqvh62HPh74Hacch82Hhh94Hsvch:1dh;1mi011mh<3mo'h=4mo1'h>2HLh?3HP1h@3HeqhA3HmohB3HmshC3HsvhD1PhE2_HhF3_H0hG3_H1hH3_H2hI3_H3hJ3_H4hK3_H5hL1ai021ahM2mohN3mo1hO2mshP3ms1hQ4ms1'hR6resulti036resulti041bi059cfg_modeli066cfg_msi073moai083mobi091pi0:7result0i0;1xp;2p;1p;3p;4p;6p;5g00HVj2lTg005Ej2>Tg00?LR0j20Tg00ITj1QTg00J9j1`Tg00JWj1_Tg00K:j1eTg008\j16Tg00K\j1oTg0072j14Tg00L>R1j2xTg00L^R2j1wTg006=j25Tg009Rj32Tg007ej2ATg00Mfj17Tg00Nlj1ZTg00Okj2kTg00Pej1JTg00Qej2XTg00R^j1?Tg00S_j1:Tg00T^j19Tg00U]j1<Tg00V[j1@Tg00WYj3;Tg00XUj4vTg001<j6uTg00Y1j5sTg000`j6[Tg00Z5j2fTg00:hj2dTg00;Bj4TTg00B[j4^Tg00[=j1rTg00Cmj2cTg00\Ej1qTg00BAR3j2ITg00]Mj1aTg00^Dj4tTg00;]R4f0R5'Ip=Ff2R6f1R7#a;25p=R%77=265p=H%47%655;6p=jg00<RR8g00=YR9P7P5Ct,f6p==f3R:?2671I45'0p=C1I95p=11I85p=31075,06p=Sf4R;A;:67;25p=]1I45,07p=p%65#ap=P%45#7p=Mf5R<%4:%665;;;27/05p=Gf6R=?2<;A2:67/05'0p=81I85,07p=n%76=2:7/05p=L%a6=2:7/05p=BA;;:6=2<7/05p=\A2:671I85'0p=O%659;67p=bA2:67/05p=U%47=;65p=mA2975p=DA;;:6=2<71I45'0p=K%@7=265p=E%<6=2:7/05p=N%9792:6/05p=W%@59267p=Y%<792:6/05p=V%:7=265p=i%97=265p=h%<7=265p=gp-0R>\4p,4segsR?/l5P:P5O11>57'0X24#FR@P3P4P;P5O11>56'0X24g00^d#Q#Q#QRA#Q#QRB#Q#`#_RC#eRD%66%oCRE3RRF%46=HDE1x89RG#wRHAj?;;RIA=G75RJf7RKP5O11567RL,>5RM'0X24CCX09#1X18#33SP5P=P5O11>5;'0P0PKP7O11>7<%6==RDERN%4==HDEROPHP?f8RP#4%6PRQPJD]RRf;RSP5O1/0MX24'pX09#1X18#33SP5f9RTP:O11>;Pf:RUP<P7O2PD%P<PEPD%M<PEPHP?PKPKPJf=RV1575RWO1EGX09#1X18#3F8P0PNf>RNPWO1,0RX09#1X18,nOPD%6SROPEPD%4SRRPEPHP?PVPVPJf@RXP5O1/0MX24#FEGX09#1X18#3CLCBP5ARDQEPD%MTPEPHP?PRPOPJfAROPWO1E\X09#1X18COP0%4U=HDEPHf<RR#4RQ=b?RPJfBRYPWO1CUX09#1X18#3PDf?RZ#6R[PEPD%4ZR\PEPHP?POPOPJfDR]P5O1/0MX24#FEGX09#1X18#3CLCBP5AHDQEPHP?P\P[PJfER[PWO1E\X09#1X18#3P3P8PHP?PXPXPJfFR\PWO1EGX09#1X18PDfCRQ#6R^PEPD%4QR_PEPHAj?[[R`PJfHRaP5O1/0MX24CCX09#1X18#3CLCBP5PHP?PYPYPJPaPWO1EGX09#1P3P9PHP?P_P^A=G65fIR^1565O1E\X09PDfGR_#PPEPD%M_PEPHP?P^P^PJfLR3P5O1/0MX24#FEGX09#1X18#3F8P5PHP`A=G;5fKR`15;5O1CUP0PHP?%4\%6\A=G<7D]P315<7O1PD%P`PEPD%M`PEPHP?fMRbPbPJfPRcP5O1/0MX24#FEGX09#1X18#3F8P5PHP?%4a%6aA=GK:D]fORd15P;O1P4fQReP5O11>7c%4:Rf=HDEA=GNU92HIPDfTRI#PPEPD%MIPEPHP?fVRgPgPJfYP5O1/0MX24#FEGX09#1X18#3F8]7]9^8F]5]6fJRFPIPWO1fSRh,>L15:6Ri#6=RDERj15;:#4Rk=HDE15<;Rl%6lRl5m?RmA=GOV52HP415K=/>5PD%P7PEPD%M7PEPHAb?f:PJf^RfP5O1/0MX24CCX09#1X18#3F8]5fWRn15UT/>WP015SURW#4%4L'A%6W%6L'D%4i=HDEPHPmPJfbP5O1/0MX24CCX09#1X18#35SjP515VR#4/Ak15NV#6/DlP9PNPDP5PEPD%7KRlPEPHP?PTP6PJffP5O1/0MX24EKX09#1X18COCBX<9P71AZ=P0%ZX%ZK'k%JX%JK'X%?X%?K52CPD%7XRkPlPD%:X%:K%`B#_RB%9XPK%`A#_#e\CRAPX%<K%@K9EAXCNCWF83SPDPXPEPDPPPEPHP?PUPYPJfgP5O1/0MX24EKX09#1X18#3CLCBP5%ZY%ZT'k%JQ%JU'X%?Q%?U52CPD%7QRX%7UPD%:QRl%:UPB%9QRjPUPA%<QRmPU%@QRQ=YAUCVCWF83SP0%J]%JS'XPC%?]%?SPD%7]RU%7SPD%:]%:SPB%9]%9SPAP]%<S%@S9EA]CNF8F8PDP]PEPDPRPEPHP?PNP\PJfkRRP5O1/0MX24EKX09#1X18#3CLCBP5%J\%JV'XPC%?_%?NPD%7_%7NPD%:_R]%:NPB%9_RS%9NPA%<_RiPN%@_R_=YANCVF8F8P0%?a%?Z52CPD%7aRN%7ZPD%:a%:ZPB%9aPZPAPa%<Z%@Z9EAaCNCWF8PDPaPEPDPkPEPHP?PYPFPJfoRkP5O1/0MX24EKX09#1X18COCBP5%?F%?O52CPDP`%7YPD%:`%:YPB%9`RC%9YPA%<`RaPY%@`R`=YAYCVF8CLP0%73RY=2DXPD%:3PlPB%93PjPAP3PmAEA3QCNF8PDP3PEPDPUPEPHP?P\fNRUPJfsR3P5O1/0MX24EKX09#1X18COCBP5%7[9HDUPD%:d%:\PB%9d%9\PA%<dRQP\%@dRd=YA\CVF8P0AiDc]PB%9cPSPA%<cPiAEAc_F8PDPcPEPDPNPEPHP?PFfRRNPJfwP5O1/0MX24EKX09#1X18COCBP5%:^9iDNPB%9hPFPAPh%<F%@F9EAhCNCWP0AhBICPAPIPaAEAI`CNPDPIPEPDPYPEPHP?PUPgPJf{P5O1/0MX24EKX09#1X18COCBP5%9b9hBgPAPn%<U%@U9EAnCNP0fXRB=gAQAEABdPDPBPEPDPcPEPHP?PNfZRcPJp+01@P5O1/0MX24EKX09#1X18#3CLCBP5%<e9gAcf[Rc%@N5EAARDcE%7hRA=2DERNPHfUf]Re5;?RdPJp+01CP5O1/0MX24CCX09#1X18#3RQ'0PBPNPQPDPAf\RQ#7RNPEPDPNPAPVCvPnEuP?PQPhPcPUDsP2PGP>A;?QcP1P8P9P>P5P2PGP>A;?gfP1P8P9P>P51A;71D:5'0n200110:000120104108Rfg00_IRgPgn10110;00031010:0000n2001103000120102107P2PGP>A;?hcRcPgg00_fRhPgn10110;0003101030000P2PGP>PcPgPgPhn10110;0003101030000n10110;0003101030000PHA;?eQP2PGP>P5P1P8P9P>P5P2PGP>f`9;?BPfPgPgn10110;00031010:0000n2001103000120102107P2PGP>PdPgPhPgn10110;0003101030000P2PGP>PdPgPgPhn10110;0003101030000n10110;0003101030000X;HP5fifeRh5=GPnE[P2PGP>A;?IQP1P8P9P>P5flRQ/A7fh/D5'0n200110:000120104108PgPgn10110;00031010:0000PdPHP2PGP2PGP>P5P1P8P9P>P51Ak71DR5'0n200110:000120104108PgPgn10110;00031010:0000PHP:PJp+01HP5O1/0MX24CCX09#1X18#3]4P5P1P8P9P1P8P9P>P5fp/A71DQ5'0n200110:000120104108PH1fG:PJp+01JP5O1/0MX24CCX09#1X18#3]4P5fqRQ/A7fmR>/D5'0P0frR0/A6fn/D7PHA=G<;PJp+01NR1P5O1/0MX24CCX09#1X18#3P5ftRR/A;1DQ;P9P0PHA=GT6PJp+01RP5O1/0MX24CCX09#1X18#3X=9P8PHA=GPRPJp+01QP5O1/0MX24CCX09#1X18P=P9PHA=GK3A=GK5p+01PP5O115P7,>5'0X24CCX09P0A=G=0RR=2HRp+01OP5O115K3,>5'0X24R3#F1dHRP4P3fv/50R3P1P3O115=0R0,>3P>%43%40'A%63%60R0'DP71d90CTCTC^CTC^C^P<P5E[W3W@P7P5O2n2001000000121000000W4X=9XQ8P7P5O2n2001109000121101101XRGP5O1PH%rGPJp+01GP5O1/0MX24#FR0CUX09#1X18#3/c5X4gPH%qGPJP0CUX09#1X18#3/c5X4gn1011010003111030000P7O1b;b4b4CTCTWKWJP7P5O2n2001000000121000000W3WIP7P5O2n2001000000121000000W3WHP7P5O2n2001000000121000000W3WCP7P5O2n2001000000121000000W3WGP7P5O2n2001000000121000000W3WFP7P5O2n2001000000121000000W3WEP7P5O2n2001000000121000000b3P<P5E[PD15=<R=#PPEPD%M=PEPHP?15PKRPPPPJPhP5O1/0MX24#FEGX09#1X18#3F8eWAWBP7P5O2n2001000000121000000W5X<9X18P7P5O2n01100000121106105P:O1W7W9W8W5W6XM9XO8P7P5O2n01100000121106105P\P[POPVP7O5W?W7P7P5O2n2001000000121000000W3XN9P7P5O2n200100000012110;000W3XP8P7P5O2n200100000012110;000W3W9P7P5O2n2001000000121000000W3W8P7P5O2n2001000000121000000bLW5W6P7P5O2n2001000000121000000W3X24P7P5O2n200100000012110;000W3X:4P@X:4,l?eW>WDo"). Qed.

Theorem srealizes_eqv : forall c T, srealizes segs c T -> forall c', cfg_eqv c c' -> srealizes segs c' T.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct Hnode as [Hfwd Hexact].
    set (I' := { p : I * config | sstep_cfg segs ACFG c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
    destruct (sstep_next_eqv c c' (evs i0) (nx i0) Heqv (Hfwd i0)) as (c20 & Hs0 & He0).
    pose (q0 := (exist _ (i0, c20) (conj Hs0 He0) : I')).
    apply (srz_conseq segs c' (t_alt (fun q : I' => t_emit (evs (fst (proj1_sig q))) (T (fst (proj1_sig q)))))).
    + apply (srz_node segs c' I' (fun q => evs (fst (proj1_sig q))) (fun q => snd (proj1_sig q))
                      (fun q => T (fst (proj1_sig q))) q0).
      * split.
        -- intros [[i c2] [Hs He]]. cbn. exact Hs.
        -- intros e st Hss.
           destruct (sstep_cfg_eqv0_scfg segs ACFG c' c e st (cfg_eqv_sym c c' Heqv) Hss) as (X & HssX & HX).
           destruct (Hexact e X HssX) as (j & -> & ->).
           destruct st as [c2|]; cbn in HX; [|contradiction].
           exists (exist _ (j, c2) (conj Hss (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
      * intros [[i c2] [Hs He]]. cbn. exact (IH i c2 He).
    + (* [comment removed for export] *)
      intros tr. split.
      * intros [[[i c2] [Hs He]] Ht]. cbn in Ht. exists i. exact Ht.
      * intros [i Ht].
        destruct (sstep_next_eqv c c' (evs i) (nx i) Heqv (Hfwd i)) as (c2 & Hs & He).
        exists (exist _ (i, c2) (conj Hs He)). cbn. exact Ht.
  - (* [comment removed for export] *)
    apply srz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
  - (* [comment removed for export] *)
    eapply srz_conseq; [apply IH; exact Heqv | exact Heq].
Qed.

(* [comment removed for export] *)
Corollary realizes_eqv : forall c T, realizes segs c T -> forall c', cfg_eqv c c' -> realizes segs c' T.
Proof. intros c T H c' He. apply realizes_of_srealizes. exact (srealizes_eqv c T (srealizes_of_realizes segs c T H) c' He). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mkst_MS : forall R pc m ro,
  OSSVerify.Proofs.zstd.huf_decompress.lib.AS.PropExec.mkst R pc m ro = MS R bvmap_empty pc (Z_to_bv 32 0) None m ro.
Proof.
ltac2:(KReplay.run1 (kr_t_SrzEqv ()) ["WithSegs"] "h01Rh11mh22pch32rop;1p;2p;7g00ITj10Tg00e8j1:Tg00J9j11Tg00JWj12Tg003cj29Tg00K:j18Tg00e]j27Tg00fOj24Tg00K\j15Tg00g5j76Tg00:hj23Tg00^d#0R0#:#1R1%00#0R0#0#0R2#0#1#2R3'9%10#2#8\3R0g00<Rf31713f2%12g00gg'4%53f1f0F6'3X30W1X23W0o"). Qed.

Lemma cfg_eqv_regs : forall R R' F pc fc rv m ro mo,
  regs_eqv0 R R' -> cfg_eqv (mkCfg (MS R F pc fc rv m ro) mo) (mkCfg (MS R' F pc fc rv m ro) mo).
Proof.
ltac2:(KReplay.run1 (kr_t_SrzEqv ()) ["WithSegs"] "h01Fh11Rh22R'h32fch41mh52moh62pch72roh82rvp;1p;2p;7p;3p;4g00ITj14Tg00e8j1ITg00J9j15Tg00JWj16Tg003cj2HTg00K:j1<Tg00Okj2;Tg00g5j7:Tg006=j29Tg0072j18Tg007ej2ETg008\j17Tg009Rj32Tg00Nlj1DTg00Pej1CTg00Qej2GTg00R^j1=Tg00Mfj1>Tg00S_j1?Tg00T^j1@Tg00U]j1ATg00V[j1BTg00?Lj23Tg00hEj1FTg00:hj21Tg00;Bj40Tg00^d#4R0#I#5%40#4R0#4#4R1#4#5#6R2'HR3%51#6R1%<2R4%50#6#<\2R0g00=YR5f8R6f7R7';f9P7f6R8f5R9f4R:f3R;f2R<F:f1R='9R>#8R?P6P7P8P9P:P;P<F:/9=R=#8R<'E%7>%7=R=525%D?%D<';%C?%C<R>'GR;%=?%=<R:522R9%>?%><R8524R7%??%?<R6524R@%@?%@<RA521RB%A?%A<RC520RD%B?%B<R<520R?'3RE'3RF'3RG'3RH'3RI'3f0P;PI%F>P9PH112:P7PG1148P@PF1146PBPE111APDP?110C110<C0C0C0C0C0C0C0115=C0UW5X70W4W8W3X62X03X23W1o"). Qed.

End WithSegs.
