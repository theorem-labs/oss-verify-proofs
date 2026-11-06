(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env Pm_iface Pm_iface2 RT_fk RT_fk_iface D_iface D_defs Bi_fktw RT23_iface Po_rows Po_iface Po_kit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_udd_defs () := "C46Stdlib5Lists4List2hdI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53A23=RT_gaps_iface8chain_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2K53A235D_kit8agree_onC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums1Z03I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Logic8iff_reflK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53A235D_kit9agree_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_kitArw_cells_agree_nwC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes8list_indC45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53A238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib2K53A23;Po_udd_defsEpixUpDownDetect2_caseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib2K53A238RT_iface9fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:mat_stableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface5pix1cC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subK69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4uctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface7po_rowsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4LSTKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4lenvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4lresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface6LIB_POC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4LIBHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6io_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53A238RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235RT_fk7ret_stFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface7lpost_fC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53A23:Lept_iface5keepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K53A238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib2K53A23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A23:Lept_iface5cmapv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_ifaceAe_pixUpDownDetectC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface8UDD_COSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface8UDD_SECBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00c69OSSVerify5KrLib2K53A23;Po_udd_defsDpixUpDownDetect2_cpsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition udd_sc : Z := e_pixUpDownDetect + 0x1f4.   (* [comment removed for export] *)
Definition udd_b1 : Z := e_pixUpDownDetect + 0x52c.   (* [comment removed for export] *)
Definition udd_b2 : Z := e_pixUpDownDetect + 0x5ec.   (* [comment removed for export] *)
Definition udd_t  : Z := e_pixUpDownDetect + 0x6b0.   (* [comment removed for export] *)
Definition udd_j  : Z := e_pixUpDownDetect + 0x70c.   (* [comment removed for export] *)
Definition udd_d  : Z := e_pixUpDownDetect + 0x7ac.   (* [comment removed for export] *)
Definition udd_ep : Z := e_pixUpDownDetect + 0x7e0.   (* [comment removed for export] *)
Definition udd_sf : Z := e_pixUpDownDetect + 0x828.   (* [comment removed for export] *)
Definition udd_fl : Z := e_pixUpDownDetect + 0x82c.   (* [comment removed for export] *)
Definition udd_fs : Z := e_pixUpDownDetect + 0x830.   (* [comment removed for export] *)
Definition udd_fz : Z := e_pixUpDownDetect + 0x834.   (* [comment removed for export] *)
Definition udd_rr : Z := e_pixUpDownDetect + 0x928.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition udd_ra_sm3 : Z := e_pixUpDownDetect + 0x088.
Definition udd_ra_sel (k : Z) : Z := e_pixUpDownDetect + match k with 1 => 0x28c | 2 => 0x2a8 | 3 => 0x2c4 | _ => 0x2e4 end.
Definition udd_ra_pmcs : Z := e_pixUpDownDetect + 0x304.
Definition udd_ra_hmt (i : Z) : Z := e_pixUpDownDetect + match i with 1 => 0x54c | 2 => 0x560 | 3 => 0x608 | _ => 0x628 end.
Definition udd_ra_or (b : Z) : Z := e_pixUpDownDetect + (if b =? 1 then 0x578 else 0x63c).
Definition udd_ra_casc (b : Z) : Z := e_pixUpDownDetect + (if b =? 1 then 0x5a8 else 0x66c).
Definition udd_ra_cnt (b : Z) : Z := e_pixUpDownDetect + (if b =? 1 then 0x5b8 else 0x67c).
Definition udd_ra_dfd (b : Z) : Z := e_pixUpDownDetect + (if b =? 1 then 0x5d0 else 0x698).
Definition udd_ra_des (b i : Z) : Z := e_pixUpDownDetect + (if b =? 1 then match i with 1 => 0x5d8 | 2 => 0x5e4 | _ => 0x5ec end
                                                                      else match i with 1 => 0x6a0 | 2 => 0x6a8 | _ => 0x6b0 end).
Definition udd_ra_des0 : Z := e_pixUpDownDetect + 0x7b4.   (* [comment removed for export] *)
Definition udd_ra_desm : Z := e_pixUpDownDetect + 0x7bc.   (* [comment removed for export] *)
Definition udd_ra_sdes (k : Z) : Z := e_pixUpDownDetect + match k with 1 => 0x7c4 | 2 => 0x7cc | 3 => 0x7d4 | _ => 0x7dc end.
Definition udd_ra_sf : Z := e_pixUpDownDetect + 0x82c.

Definition UDD_STOPS : list Z :=
  [e_stack_malloc_x 3%nat; e_selCreateFromString; e_pixMorphCompSequence; e_pixHMT; e_pixOr; e_pixReduceRankBinaryCascade; e_pixCountPixels;
   e_pixDebugFlipDetect; e_pixDestroy; e_selDestroy; e_set_shadow 245; e_lept_stderr; e_returnErrorInt; udd_b1; udd_b2; udd_t; udd_d; udd_fl].

(* [comment removed for export] *)
Lemma chain_ok_keep_above : forall ras (m m' : mem) lo f p, chain_ok m lo f ras -> p + 16 <= f ->
  agree_on (fun a => p <= a < USTACK_TOP) m m' -> chain_ok m' lo f ras.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_udd_defs ()) [] "p'0h03fp1h11Hh21mh31xi001xh41fh52loh62m'h71ph82H7h92IHh:4__x1h;4__x2h<4__x3h=1ah>3rash?2AGh@2HPhA2HahB7__arithhC4__ffhD7__sat11hE6__sat8hF8__varmaphG5__withH4__x4hI2H1hJ2H2hK2H3hL2H4hM2H5hN2H6hO2H8hP2HxhQ3Hx0hR2_HhS7__sat10hT6__sat6hU6__sat7hV6__sat9hW1nhX3ra1hY3ra2hZ4ras'h[1yi011li021zp%0p&0p;1p;4p;2p;3p;<p;6p;7p;5p;Bp;8p-1p10000p4p710p8g000GS00j1hTg000gj19Tg001Lj1gTg001jj1`Tg002Mk10?Tg002oj40Tg0041j1MTg004OR0j21Tg004lj23Tg005HR1j24Tg005dj3mTg006^j1TTg007>j38Tg007^k20>Tg008;k102Tg008YR2j22Tg0094j1jTg00:0R3j1STg00:Pj1DTg00:oj1iTg00;Mj2ATg00;gk40=Tg00<Jm<0:Tg00<ok607Tg00=Xk405Tg00>?k204Tg00>gk303Tg00?Kj2fTg00@<j2KTg00@\k201Tg00A=j2LTg00Afj3NTg00BOj2]Tg00C;j2XTg00CYj1|Tg00D7j4OTg00DUj1{Tg00E3j1zTg00E^j1dTg00FCj2JTg00Ffj2cTg00GIj3GTg00Glj4VTg00HWj1xTg00I9j2wTg00I[j2vTg00JGj3PTg00Jaj3uTg00K@j4tTg00L2j6yTg00Lmj7sTg00N0j4BTg00NKk400Tg00Nej5qTg00OGj2[Tg00Omj1^Tg00Pej4ITg00Q^R4j2\Tg00R8m<06Tg00R]lBoTg00SCk708Tg00Sgk709Tg00TKj8nTf2R5f1R6'3f0R7'2p=6g00ToR8/37p=:1467,25p=R1[67#^p=Yg00UMR9f3R:1[56#^=89738p=5f5R;g00VER<f4R=11:5P6CI/27'2p=713=:1456'2g00W=R>/\7'2p==1K=:=P>81156g00W[R?'3/27'2p=?1\>7p=>13:?1256/27'2p=U1K56=P>8/27p=W1K67=P>8p=Z11;=/3?13:5/26/27'2p=e1167/3?p=a137?p=p1[56#^=897p=;P<P:P5A8967CIp=FP:P5P6P7C0,2=,2;p=QP<P:P5P6CI/27p=_P<P:1156P7CIp=l1156/37p=EP<P5P6P7CIp=k%D7#Dp=Cg00XZR@P>P>P>P3P3P;P=P:P5P6P7N<06p>0<P>P>P>P>P>P>P0P7P6P5P0P:P=P;f6R0f7R3f8RAf9RBMBop>0;P>P6g00Y9P7CVp=@P6g00Y`RCg00Z?RDPDg00Z_REP7g00[?K08p=<P5PCPDPDPEP6P7K09p=bP:PCPDPDPEP5P6P7Gnp=HA8967p=}13:5/261\>7'2p=~A89679895p=r%h>RCP>g00[_RF#9RG#9RH#9RI#9RJ#9#9RK#gRL#`%gI#`$0?[RMP=P5P6P;C0%MJRN,16RO/35RP147?RQ96:7X=>?m0;RRP0P;P=PAC0[[[^7>^4>^5>^6M]2RSX>CP=P5P6%T>RTC0RUP5P0P;P=PTC0S01eX?RX@PW1X7>X4>X5>X6MX2MP=P5P6A8>30C0P211;NRV/3=RWP=%MIRIP=PN%9K#9#9#9#9#9#MRXf:RYPY%MGRZ%MKRK+0>R[%:7?R7[R\PAP;&02JRJ1YL7R]PLf;R^%T9R9C5PAP;P7PYC0E7X0>D=D?110NPV13X^14^[P\PAP0PJP]PLf<RVP9C5PAP0P7P^C0E7X0>#>CU9W;I76;P5113NR_/30P_f=R_,3X14_[P\P^PAPJP]PLf>R`P9C5P^PAP7P_C0E7X0>#>CU9W3IP21ZAIPAPNPXP`14`[P\PVPBPJP]PLf?RaP9C5PVPBP7P`C0E7X0>#>Ee11YNPBPIPBPNPXPaPaP[P\PVPYPJP]PLf@RbP9C5PVPYP7PaC0E7X0>D=D?76BP71ZYIP^PNPXfARc14c[P\PaPVPJP]PLfBRdP9C5PaPVP7PcC0E7X0>#>EeP21aVNPXPdPdP[P\PbP_PJP]PLfCReP9C5PbP_P7PdC0E7X0>D=11`NRfP_PIP_PNPXPePeP[P\PbP`PJP]PLfDRgP9C5PbP`P7PeC0E7X0>D=D?76_P7%pfPXfERfPfP[P\Pe11bJS02P]fFRh=;L9CFPePbP7PfEQX0>D=P214h[96XhP\PgPcPJP]PLfGRiP9C5PgPcP7PhC0E7X0>#>11dNS03PcPIPcPNPXPiPiP[P\PgPdPJP]PLfHRjP9C5PgPdP7PiC0E7X0>D=D?76cP714j[96XjP\PiPgPJP]PLfJRkP9C5PiPgP7fIRgC0E7X0>#>P4P>P\PjPfPJP]PLfKR4P9C5PjPfP7PkC0E7X0>11hNPfPIPfPNPXP4P4P[P\PjPhPJP]PLfLRlP9C5PjPhP7P4C0E7X0>D=D?76fP7P\PkPiPJP]PLfMRhP9C5PkPiP7PlC0E7P2%:6?R6[P411jJfNRi=;L99;L6P4PjP6PhC0C_11kNPgPIPgPNPXfORmPmP[P\PlPkPJP]PLfPRnP9C5PlPkP7PmC0E7X0>D=D?76gP7%::14:[S04'2Pi114J1YL=RkPLfQRoP9C5PiP4P=PnC0C_P2PmPlPJfRR4=;L99;L;ClPmPlP;PoC011iNPhPIPhPNPXfSRpPpP[P\Pn11iJRqP]fTRr=;L9RsCFPnPiP7PpEQX0>D=D?76hP7PoPq1YL3RqPsCFP4PmPAPrC0AEoNn1ZnIRm1anNRsfVRh14h[56XRiP\Pp11oJRtP]fWRu=;L9RvCFPpPoP7PhEQX0>Rw#>Rx'2Ry'2Rz'2PgPmPzPfPsPyPcPiPxP_P>PwPB%:B?RB[11nJRwA;Lh99;LBR_5k4RxP4PnPBfURiC0Ry'2P;PxPyP<PpP4PwP_P6A6n7QX=>A;LYv#j#S,1t,4796t7RtX3>PpP4Pl114JRl/36Rvg00\DRL#DRn#DR_#DRw#DR<#C#C#C#C#C#CRy#SRx,1lRs,46Rf'211lN9Rv6RzPvPfPvP7X3>RfPNO1Rm,1lR{,46%ivP>P>P1PfP11467#iX[>X3>P6P61A>6PsP{PfPfPfP>P>g00\c1167H0=,A>X2>XW>PlPl1A>lPxPmPfPf%S7,A>X3@PyPN1A>NJ0<N:0;N<0:J07P7H05Pz204ZKRz148ZRy%:K148[[R@[Rf%:ZRmg00]GRxB03ZK6UWARK%:[\x^AmRm1fiI%:i%:IRx1KuI#:[[P5g00]c2018Z'APyeO1RyP@g00^IRZ1L>w1L>n1L>LRL5N>Rn5N>g00_5Rw']1L><1L>_R_=N>L5N>/]w%TZRL58Z38%hZR<P>1X>5P6P>1X>=P:%|>RlCOCO%{>R{%z>Rs%dG,J>R11c>J5G>Rv1J>GRG'@,<sP>PGg00_aR|1c>NR}9G>vCV,<s5bs%xDRDPs1J>FRv=G>}R~/@1,<sPDPsAG>1}%dF,J>RF'@,<sPD1@vG,<sP>PGP|PFCV,<s5bsCHCHCH1wsEREP7P5g00`HRFg00`hR|'A1v75=PF|dAu>86CtR8bCbFbGX:>X;>X<>XH>11:JR|11|N,4676613O=14=;96:=\W[[^:>^;>^<>^H>P7fXRWP?P3PuP;PiPgO7bBbEbTbUbEbQXPtX3>A647QX=>P6O1\t^3>eEyFsQ00P>PiP4P^P6C0PiPpPVP5C0]8^9SPiQ01\R\P\U^7>^4>^5>^6M^2MPrPoPYPTC0P7PrP4P^PTC0eW8W9P=P5P6A8>0;C0P0P;P=A8>BAC0\R\P[^7>^4>^5>^6M^2MPWPiP`A8>56C0P6fYPWPhPaPiP7P211hNRh/3aPaPIPaPNPXP:Q04P\fZRaQ02P]1}k9CFPaPbP7P:EQX0>C~D?13hbP7AEWNcQ0313X0140[P\f]R\PePJAr]q9P\PeP7P0C0E7X0>#>CU9WdIPzPfPKPmf\Rm/fI%:mf^RK/KI#:\x[PyP@AN>_n/]w=8ZLP<P>P>1X>:P5PlCOP6PlCOP{Ps1J>HRH,@~,<sPDPsAG>H}/@G,<sPD1@~G,<sCHCHPEP8bCbFbGX:>X;>X<>AE7N5AE:N5AE5N:[[^:>^;>^<>P7f_PjPKPmP0O5bBbDbVbSbDWRWOP6P7O2n2001000000121000000P4O8W8W9XZCXY>P6P7O2n10110100020021102101PrP7O2CBCBH00CBCBCBCBW8WNP6P7O2n2001000000121000000W1WMP6P7O2n2001000000121000000W1X0>P6P7O2n2001000000121100000W1WLP6P7O2n2001000000121000000W1WKP6P7O2n2001000000121000000W1WJP6P7O2n2001000000121000000W1WIP6P7O2n2001000000121000000P0P;P=A8>YBC0eX?RX@PW1X7>X4>X5>X6MX2MX9SX>CXX>P7DqW>o"). Qed.

Section UddDefs.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition pixUpDownDetect2_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs pconf : Z) (vs : pixv) (cvs : cmapv) (x : word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 pconf -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 0 ->
  pix1c (rt_live RT Σ) m pixs vs cvs ->
  bv_unsigned sp <= pconf -> pconf + 20 <= bv_unsigned s0 -> pconf + 4 <= USTACK_TOP - 16 -> pconf mod 4 = 0 -> rw_cells asegs m pconf [C4 x] ->
  uctx m sp s0 ras -> po_rows e_pixUpDownDetect ra ras ->
  lenv RT Σ m sp lo (LSTK 17) -> lres RT Σ 14 80 UDD_COST -> sec_bytes (rt_live RT Σ) + UDD_SECB <= SEC_BYTES -> LIB_PO m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixUpDownDetect m)))
    (fun c => exists (Σ' : rts RT) (confbits : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pconf, pconf + 4); (pixs + 20, pixs + 24)] m m'
          /\ rw_cells asegs m' pconf [C4 confbits] /\ pix1c (rt_live RT Σ') m' pixs vs cvs) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - UDD_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixUpDownDetect2_case (AL : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs pconf : Z) (vs : pixv) (cvs : cmapv) (x : word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 pconf -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 0 ->
  pix1c (rt_live RT Σ) m pixs vs cvs ->
  bv_unsigned sp <= pconf -> pconf + 20 <= bv_unsigned s0 -> pconf + 4 <= USTACK_TOP - 16 -> pconf mod 4 = 0 -> rw_cells asegs m pconf [C4 x] ->
  uctx m sp s0 ras -> po_rows e_pixUpDownDetect ra ras ->
  lenv RT Σ m sp lo (LSTK 17) -> lres RT Σ 14 80 UDD_COST -> sec_bytes (rt_live RT Σ) + UDD_SECB <= SEC_BYTES -> LIB_PO m ->
  bv_unsigned sp mod 32 = AL ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixUpDownDetect m)))
    (fun c => exists (Σ' : rts RT) (confbits : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pconf, pconf + 4); (pixs + 20, pixs + 24)] m m'
          /\ rw_cells asegs m' pconf [C4 confbits] /\ pix1c (rt_live RT Σ') m' pixs vs cvs) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - UDD_COST <= rt_credit RT Σ').

Lemma pixUpDownDetect2_of_cases : pixUpDownDetect2_case 0 -> pixUpDownDetect2_case 16 -> pixUpDownDetect2_cps.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_udd_defs ()) ["UddDefs"] "p'0h01Hh12ALh22H5h32H0h42H1h52H2h62H3h72H4h82H6h92H7h:2H8h;4__x1h<4__x2h=4__x3h>4__x4h?4__x5h@2C0hA3C16hB3ENVhC1FhD3H10hE4H10bhF3H11hG3H12hH3H13hI3H14hJ3H15hK3H17hL3H18hM3H19hN2H9hO3PMchP3SPAhQ2_HhR3_H0hS3_H1hT3_H2hU3_H3hV3_H4hW3_H5hX3_H6hY3_H7hZ7__arithh[4__ffh\8__varmaph]5__with^2a0h_2a1h`2a2ha2a3hb2a4hc2a5hd2a6he2a7hf1chg8confbitshh3cvshi2fchj2gphk2lohl1mhm2m'hn2msho5pconfhp4pixshq1qhr2q0hs1rht2r0hu2rahv3rashw2s0hx2s1hy3s10hz3s11h{2s2h|2s3h}2s4h~2s5i002s6i012s7i022s8i032s9i042spi052t0i062t1i072t2i082t3i092t4i0:2t5i0;2t6i0<2tpi0=2vsi0>1xi0?2Σi0@3Σ'p%0p&0p;1p;2p;3p;5p;4p;6p;7p;Sp;Dp;8g00aHk100Tg000gj13Tg0041j1@Tg00bUk10;Tg001Lj1XTg001jj1dTg00E^j1RTg00cMk20UTg002Mk10QTg000Gj1PTg00d9k10:Tg00e7k106Tg00OGj2bTg00JGj34k20@Tg00f3j2OTg00foj5~Tg00gij20Tg004lj22Tg00hSj2TTg00i0j1rTg006^j1_Tg007>j3GTg00Pej4pTg00ihk40PTg00jck30NTg00k_k10JTg00lZk60ITg00mUk50GTg00nPk10FTg00oNk109Tg010Ij1hTg011Dj1QTg012?j3FTg0137j21Tg0142S00j2eTg014Lj2zTg014mj1yTg015Fj2JTg015cj2VTg00@<j26Tg004Oj25Tg016@j2xTg005Hj2;Tg016gj2wTg017Nj2uTg0184j2tTg00@\j2sTg00;Mj2`Tg008;k10VTg018Zk20TTg00:Pj1CTg019;j3^Tg00A=j2qTg00BOk20STg019dj2UTg00C;j2nTg00CYk10OTg00D7j4cTg00DUk10MTg00E3k10LTg00Ffj2ZTg00HWk10HTg00FCj2MTg01:Pj3kTg00GIj3jTg00Glj4[Tg00Sgk70ETg01;3k70DTg00I9k20CTg00I[k20<Tg00Jak30=Tg00K@k40>Tg01;WmS0?Tg01<Tk407k504Tg01=MmD0ATg01>Fk70BTg01?Dj2oTg01?dj4iTg01@Dk705Tg00Q^j2\Tg01A@j2gTg01B>j2mTg01C<k303Tg01D1k20KTg01Dhj4fTg008YR0j28Tg00Afj3]Tg00SCk702Tg01E]k601Tg00TKk80RTf2R1f1R2'5f0R3'2p=Kg00W=R41623g00ToR534p=ag00VER600K3p=AP6P1P2P3Cfp=Hf5R7f4R8'5g00W[R9'2f3R:/61=4451223'8'8p=9g01FAR;,T7/2815:1/22/83'8p=<1823,81p=71012/63p=:A4435p=DA4423p=?P6P:P1P2Cf/83p=YA4415A4423'ep==1T2;/23p=}16:1=4451223'8p=W1578/2:1512/29/83'8p=|1523/29p={1212/83p=L1223,81p=v1q43p=IA]423p=NA]4239]41p=SP4P2g01G?P3C[p=BP2g00Y`R;g00Z?R<P<g00Z_R=P3g00[?K02p=>P2P;P<P<P=P3J01p=lP:P;P<P<P=P1P2P3L0Rp=EA4423,e1p>08&005g00[_R>#3R?#3R@#3RA#3RB#@RC$00p,2RTRD$0;REg01Gfp-0[%3BRB#3#XRF#dRG%R?RH#X00UG%XB#d%XA#d$0Q\GRIg01H\g01IY%P4fYRJ$0:fZRK$06fWRLg01JW,bF54GfRRMf8RN,bF54GS01Q011bF5S0294GMROfbRP,ODf?RQf=RRf;RSf:RTD~f`RU,0F/2Rf>RV%3H#3RW#@S03f[RX,0F3K%@@RY1T9C5KQf@R9/aYP6fDS04fAS05g00UMRZ%rV%_ZS063GCpfES07feR[f_R\PVH0Pg01KNS08fgR]<0NQPDfjR^fGS09P]fFS0:%RA#@$0JRAJ0IPDfkR_%R>R`#R#3#@%3W#3#@g01LTS0;I0GflRW,OD$0Fg01MQg01NN3KfJRa$09P0fKRb#h%QbfnRc=FDb%Ab10F_Rd9Hba11DcRePaPaPAPdPdPCPdPCPdPeE9E<3737%@BRB9:FWRe#DS0<1?eCS0='eP:fMRe#hfNRf#QfqRg=FDf%Af10FcRh9Hfe11DgRiPePePAPhPhPCPhPCPhPiE9E<3737P0fORi#QfrRh=FDi%AiPiPffoRj,0FRk11DhRlPfPfPAPkPkPCPkPCPkPlE9E<CY37fpRl=:FBRk?=kCP3fQRk#QfuRm=FDM%AMPMPk10FhRn11DmRoPkPkPAPnPnPCPnPCPnPoE9E<CY37P0fvRofSRn5FD%AnfsRp,0FRq9HnM11DoRrPMPMPAPqPqPCPqPCPqPrE9E<37ft=:FBRr?=rCP3fxRrfURq5FDfVRs#A10FoRo9Hsqfy,1DRtPqPqPAPoPoPCPoPCPoPtE9E<37P0%ALPLPsfw,0FRtfzRo,1DRuPsPsPAPtPtPCPtPCPtPuE9E<CYA:FrBRr?=rCP3%AJPKPJ10FoRof}Rr,1DRuPJPJPAPoPoPCPoPCPoPuE9E<CYP0f{,0FRu9HXKf~Ro,1DRtPKPKPAPuPuPCPuPCPuPtE9E<f|=:FBRt?=tCP3f]Rtf\Ru10Fr3Hp+01B,1DRrPtPtPA10FoRoPoPCPoPCPoPrE9E<P0p+01CRr,1DRof^Rv'}PvPAp+01@,0FRwPwPCPwPCPwPoCWE|p+01A=:FBRo?=oCP3p+01ERo,1D/}UfaRwPA10FrRrPrPCPrPCPrp+01FRr,1DCWE|P0p+01D,0FRx9KPAPxPCPxPCPxp+01GRx,1DE9A:FoBRo?=oCP3fdRo10Fr7KA10FxRxPCPxPCPxp+01JRx,1DE9P0p+01H,0FRA/{CPAPCPAp+01KRA,1DCWp+01I=:FBRr?=rCP310Fx/{C10FARAPCPAp+01NRA,1DCWP0p+01L,0FR0/aCp+01ORx,1D,20p+01M=:FBR0?=0CP310FA/aC10Fxp+01RRx,1D'2p+01P,0F/zB%DBRA#yp+01Q,0FR01J0B,VB160B'5'?[1x0B1;5BR010FxRx/6BRr1;rB5L5[1wxB1;B5p+01S,0FRx/6BRr,;B?vr5[1uxBp+01T,0FRx/JB#D\A1txBp+01U,0FRx/6B/?x\A1JxBP4p+01V=:FBP4p+01W,0F/zC%DCRx#yp+01X,0FRr1JrC,VC16rC'5'?[1xrC1;5CRrp+01Y,0FRy/6CRz1;zC5L5[1wyC1;C5p+01Z,0FRy/6CRz,;C?vz5[1uyCp+01[,0FRy/JC#D\x1tyCp+01\,0FRy/6C/?y\x1JyCP4p+01]=:FCP4P7g00]cRy1s5C'`PreO11;3C9L53PR1s5B,`yP0eO11;NB9L5Ng00^IR0&0V>-0T4Ryg00\DRr#CS0>#CRz#CR{#CR|#C#CR}#I5^4S0?%I{R{%IzRz9^4yR~1q4rRr'N3S%C}#IR}%I|R|9^4yRy1N{z3SQ0>#IRz/Nrg00_5+0SRr'U'UQ0?1N{~7S|1N{z9S}y/Ur'U%_05G03G%P0P4P41n48P1&0O4R0CcP2P41n47P:P0CcCc&0M4&0L4R0P01Z4CRr1Z45Ry'B,>0,l0&0H<R}1M4`Rz1M4H9k4r1M4?R?5j4'B,>0CEP}P0P0P;P<P<P=P4Pyg00Y91M4>R>C[,>0P4P>g00_a1Z4BRHC[,>0K0EP}P0P01BHy,>0,l0P}1M4@9k4H=j4>,Bz,>0CEP}P01B?y,>0P}P0P;P<P<P=1B>y,>01B>r,>0K0DCECECECE20C0=P3P1g00`HR0g00`hR='`20<31=40=dB0=452H0>b[b\b]X;4X<4X=4X>4X?4g01OLR=\x1VC7/51,?:[1;2B9L52P=\Af6RA,VB/5:,?7[%D8R=B08=8C[[[[^;4^<4^=4^>4^?4P3P8PSp+01a,0FP:PTf9R=P2P9fBR5O9bZb3b2btbrb:b9b8b2b7bsbqb6b5b4b3b0WYWPP2P3O2n2001000000121000000W0WXP2P3O2n2001000000121000000W0WWP2P3O2n2001000000121000000W0WVP2P3O2n2001000000121000000W0WUP2P3O2n2001000000121000000W0WTP2P3O2n2001000000121000000W0WSP2P3O2n2001000000121000000W0WRP2P3O2n2001000000121000000W0WQP2P3O2n200100000012100000016dBRd?=dCQ00Q0<Q0=PDPlPjg01OiRdPcfmRxPWP_P^fiR0fhR>P]ffRrP[PofcRyPPPwPUP\PvPtPuPXPKPJfXR<PLPsPqfTR;PnPMPkfPR}PiPfQ08PeNS0?+0@H07g01Q0PDP2PhPpPhPgPlPWP_PPPwPUP\PvPtPuPXPKPJQ02P;P3P2ND0APDPmP:PMP3PhPkK0BPDPmP:Ph1o44RmP4P4Pi15iYCiP4P4Q03,5}%3`#3#3#@,5}Ci%_m5Gm3GPMP3K05P6P3Pi%r1Q065GZCp1OD:P3P}PfPeD~3737XmI,\IXndP1I04%Pm1OD21ODp34g00XZ,o4#P1gD21gDp3411D211Dp'?1mDpQ0;'T1mD2'23737XgG,\GZ0@E,\EWf6036P3A:FxBRB#DPpPgPlPjPcPxPWP_P^P0P>P]PrP[PoPyPPPwPUP\PvPtPuPXPKPJP<PLPsPqP;PnPMPkP}PiPfPefLRpPbPafIRFfHR6Q09Q0:Q07Q04fCREP5Q05P9PQPVPRf<RDPSPTP=PNf7R2PAP7P8P:P3OpW1P3O11?BCPhPgPlPjPcPxPWP_P^P0P>P]PrP[PoPyPPPwPUP\PvPtPuPXPKPJP<PLPsPqP;PnPMPkP}PiPfPePpPbPaPFP6Q09Q0:Q07Q04PEP5Q05P9PQPVPRPDPSPTP=PNP2PAP7P8P:P3OpW1P3O1n200100001021000010000b1WMWLWKWBWJWIWHWGWFWEWDWNX:OX9OW8W2W7W6W5W4WvZ0>GWhY0=Xo4Xp4Xk4WlWiWCZ0;GZ0:GZ09GZ08GXzGXyGZ03GZ02GZ01GZ00GX~GX}GX|GX{GXeGXdGXcGXbGXaGX`GX_GX^GXxGXwGZ07GZ06GZ05GZ0<GXjGZ04GWuWOY0?g01QeeWAW@o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition udd_pmcs_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 A_SEQ_TEXT -> a2 = Z_to_bv 64 0 -> pix1c (rt_live RT Σ) m pixs vs cvs ->
  uctx m sp s0 ras -> po_rows e_pixMorphCompSequence ra ras ->
  lenv RT Σ m sp lo (LSTK 15) -> lres RT Σ 13 50 MCS_COST -> sec_bytes (rt_live RT Σ) + MCS_SECB <= SEC_BYTES -> LIB_PO m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixMorphCompSequence m)))
    (fun c => exists (Σ' : rts RT) (pix1 : Z) (v1 : pixv) (cv1 : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix1) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix1c (rt_live RT Σ') m' pixs vs cvs /\ pix1 <> 0 /\ pix1c (rt_live RT Σ') m' pix1 v1 cv1
          /\ p_w v1 = p_w vs /\ p_h v1 = p_h vs /\ (p_cmap vs = 0 -> p_cmap v1 = 0)
          /\ (p_cmap v1 <> 0 -> c_n cv1 = c_n cvs /\ c_nalloc cv1 = c_nalloc cvs /\ c_depth cv1 = c_depth cvs)
          /\ List.NoDup (pix_chunks pix1 v1 cv1 ++ pix_chunks pixs vs cvs)) c
       /\ rt_live RT Σ' = pix_copy_live pix1 v1 cv1 (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - MCS_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition udd_hmt_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs sel : Z) (vs : pixv) (cvs : cmapv) (sv : selv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> a2 = Z_to_bv 64 sel ->
  pix1c (rt_live RT Σ) m pixs vs cvs -> sel_obj (rt_live RT Σ) m sel sv -> (exists k, 1 <= k <= 4 /\ tsel_shape k sv) ->
  (forall c, In c (sel_chunks sel sv) -> c <> pixs) ->
  uctx m sp s0 ras -> po_rows e_pixHMT ra ras ->
  lenv RT Σ m sp lo (LSTK 11) -> lres RT Σ 8 4 HMT_COST -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixHMT m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pixs + 20, pixs + 24)] m m'
          /\ pix1c (rt_live RT Σ') m' pixs vs cvs /\ pixd <> 0
          /\ pix1c (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs /\ p_h vd = p_h vs
          /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
          /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs)) c
       /\ rt_live RT Σ' = pix_copy_live pixd vd cvd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - HMT_COST <= rt_credit RT Σ').

End UddDefs.
