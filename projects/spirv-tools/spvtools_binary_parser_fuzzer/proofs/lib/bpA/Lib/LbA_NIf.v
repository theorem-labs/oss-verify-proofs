(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil HMState HMem HCells HArr HExec HLFrame TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 FakeStackRep AllocRepX RtA_IMemset RtA_Td.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Bridge LbA_Conv LbA_Call LbA_DStat LbA_NBr LbA_NMc LbA_NLeaf LbA_NPc1 LbA_NLoops LbA_NSnp LbA_NKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_DPdK LbA_PqK LbA_DRep LbA_DiagStmt LbA_PcStmt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail SumWalkTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumTac NumLeaf.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbA_NIf () := "C46Stdlib5Lists4List2hdC69OSSVerify5KrLib3bpA3Lib9LbA_NLeaf4ninvC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib4HMem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsConst6ACONSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsStack06stack0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_NBr;relro_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibCont7ContLib9stores_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib<LbA_DiagStmt7app_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsShadow5aceilC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C69OSSVerify5KrLib3bpA2Rt8AsShadow;aceil_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib3bpA2HF8HeapCeil5hceilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib3bpA2Rt8AsShadow2shC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_NBrBmunch_of_stores_inC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_NBrBwmono_of_stores_inC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_NBr:mem_inv_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DPdK<aconst_ok_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsConst9aconst_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DPdK<aconst_ok_loC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib3bpA2Rt7AsConst<ACONST_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsStack09stack0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsStack0=stack0_ok_appC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib3bpA2Rt8AsStack0@stack0_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_NBr>relro_clear_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I69OSSVerify5KrLib3bpA2HF8HeapCeil8HeapCeil00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt5ASegs5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib3bpA2Rt5ASegs8AIMG_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsShadow9ALOWSH_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsShadow6AHI_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsShadow7AAPP_HIC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapi69OSSVerify5KrLib3bpA3Lib7LbA_NIf4nmid00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib3bpA3Lib7LbA_NIf5nmidP00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC49OSSVerify5KrLib8LibIface4zwinC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibCont4CRep3fldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibDiag7DiagTac5slotsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib3bpA3Lib:LbA_Bridge5rfullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_NSnp:tdl_pinnedC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib3bpA3Lib7LbA_NIf5nmidP01C1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic4True01c69OSSVerify5KrLib3bpA3Lib7LbA_NIf4NWINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt6RtA_Td6ATDLOCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_NKit<A_PAD_XS_RETC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation SEGS := asegs (only parsing).

Definition NWIN : Z := 8192.
Definition A_CTYPE_ID : Z := 0x6c2a10.
Definition A_NUMPUT_ID : Z := 0x6c2798.
Definition A_NUMPUT_OBJ : Z := 0x6c2ae0.
Definition VT_NUMPUT : Z := 0x182088.
Definition VT_CTYPE : Z := 0x1814c0.
Definition FACETS_BEG : Z := 0x6c2d80.
Definition FACETS_END : Z := 0x6c2e70.
Definition DPU_RETPC : Z := 0x13128c.
Definition DPL_RETPC : Z := 0x130d58.
Definition PADRA_UL : Z := 0x13126c.
Definition PADRA_L : Z := 0x130d38.

Definition NKEPT : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition NCS : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma ninv_obj {HCEIL : HeapCeil} : forall lo shi M M' (W : Z -> Prop) O n, ninv lo shi M -> stores_in W M M' ->
  LbA_DiagStmt.app_obj O n -> 0 <= n ->
  (forall a, W a -> aceil <= a < 2 ^ 63 \/ O <= a < O + n) -> ninv lo shi M'.
Proof.
ltac2:(KReplay.run1 (kr_t_LbA_NIf ()) [] "h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with74__p1h84__x3h91ah:2O2h;2Hah<6__sat4h=6__sat5h>2H0h?5HCEILh@2HxhA4__p2hB6__sat6hC6__sat7hD1ohE1xhF2A1hG2A2hH2AChI2H1hJ2H2hK2H3hL2HWhM2HnhN1MhO2M'hP2MIhQ2MUhR1OhS2O1hT2O3hU2RRhV2S0hW2SHhX2SThY1WhZ2WMh[2_Hh\2loh]1nh^1qh_1rh`3ship%0p&0p;4p;2p;1p;3p;6p;7p;:p;8p-1p10000p4p710p8g000Gj4?Tg001Bj2jTg002>j1TTg0038j4GTg0043j1ITg0053j3^Tg0061j2]Tg0072j12Tg007lj11Tg008Qj1PTg008oj18Tg009Tj2uTg00:1j29Tg00:MR0j24Tg00:hj25Tg00;Ej20Tg00;aR1j2ETg00<;k10@Tg00=;j2=Tg00=[j1ZTg00>Uj2}Tg00?6j1HTg00?Oj2fTg00?lj2sTg00@Ij3WTg00@cj2vTg00AJk20TTg00B1k20STg00BWk20RTg00C=k20QTg00C^j2tTg00D8j1iTg00DWj2aTg00E@k20NTg00Eik30MTg00FRj3VTg00G;j2qTg00Ggj1pTg00HGj3OTg00Hgk10KTg00IGj2hTg00Iek10JTg00JCk10ITg00Jnj2_Tg00KQk10FTg00L3j2oTg00LVj4`Tg00MAk30ATg00Mdj3\Tg00NGk20?Tg00Nik20>Tg00OUk30=Tg00P4k40<Tg00Pfj1QTg00Q]k20;Tg00R=j2nTg00Rej3lTg00SIk10:Tg00Sgk109Tg00TEk306Tg00Thk205Tg00Ugk604Tg00Vnk303Tg00Wkk407Tg00Y2k308Tg00Yok602Tg00Znj3mTg00\0R2k101Tg00\mk400Tg00]oj2kTg00^Pj6YTg00_1j7~Tg00`1k10Bk20GTg00`ok40CTg00b1k30DTg00bKk30ETg00bej3|Tg00cBj3{Tg00c_l:zTg00ddk60HTg00egj4gTg00fBj4yTg00f`k60LTg00gDj7rTg00ghj7xTg00hLj6wTg00i0k80OTg00iTk40PTf2R3f1R4f0R5'4'4p=Dg00j4R6/05p=7%85#8#8#8p=:f4R7f3R8'01545,93'4p=B1083/44/E5p=C10831945'4p=A%15#8p=[%85#8p=c%15#1#1#1#1#1#1#1p=F%15#1#1#1#1#1#1#Pp=>1034/45p=<g00jRR9?W56p=L1545,93p=b1945,43p=XP9P3P4P5Cyp=MP4g00k0R:g00kOR;P;g00koR<P5J0Lp=e1o95p=;P9P4g00lOP5C`p=dP4P:P;P;P<P5g00m6R=Frp=SP3P:P;P;P<P4P5Fxp=@P4P:P;P;P<P5Ewp=UP8P:P;P;P<P3P4P5L0Op=3P3P:P;P;P<P9P4g00mVP5C`P=Frp=6%15#1p=N%15#1#1#1p=JP9P9P4P5H0Pp=R%85#1p=Kg00n=S00Q00g00o<S01Q01p-0R=\9f7R:f6R>f5R?P7C?P0g00omR@/j?%T?f8RAP?P:P>CG%I?3DA^7>?1]78%77PAP5O1f>RB#2P4g010dRC#1RD#PRE%8CRF#:RG#PRH'uRI,94RJPAP4P4PAP:DBCC[^99f=RKf<RLf;RMf9RNC?[[[[P51j@:%TAPMPAf:ROPNCG%IA3DP0%TNPLPNPMPOCG%IN'4A^AON1]A:%7APLP5O1fBRO#2P4PJPLP4P4PLPMDBCC[^99fARPf@RQf?RRPKC?[[[[P5%TMPRPLPBPKCG%IL'4P0PQPKPRPBCG%IKA^LBK1]LM%7LPQP5O1fFRK#2P4PJPQP4P415QRRSCACC[^99fERTfDRUfCRVPPC?[[[[P5POPRPPPQCG%IQA^RPQ1]RBP0g011IRP/0Qg012CRW,0Sg013ARX/0Q'Eg014<RY,0S'4%7QPUP5O1fJRQ#2P4PJPUP4P415UVRSCACC[^99fIS02fHRZfGR[PTC?[[P510PO15VORO/0W10XV'E10OY'4P010SW10XU'E10SY%7UPZP5O1fNRU#2P4PJPZP4P4PZP[DBCC[^99fMS03fLfKRSQ02C?[[P515KT/0W10XK'E15[K/0Y%7[PSP5O1fQRY#2RWP4PJPSP4P4PSPQDBCC[^99fPRQ$0@%8G#:#:RS#[#cS04#8#:#F#F#>RO%2QRV%8SRS#:#:#F#F#>R\,0V3<%1DS05#1R]#1#FS06#PR^,=V#LPV%ZQR_P_PVP^DB3DP010W\9<OW1=W^#L%ZYRV,0WAbVW^3DfRRVPYPQPUC?P5fSRU#2RQ10Q\5<OP0fTR0#2RQ,0O10Q\fURQ#2RW/=^#L%ZQR_,0WAb_W^3DfVR_PQP0PVC?[P5%2_,0OfWRV#2/0\fXR\#2RW/=^#L%Z\R`,0WAb`W^3DfYR`#2RW%P]R]'}%L]R^#HfZRa#2Rb1fb],s]1=b]'55W9[1vb]196]Rcf[Rd#2Re/=]Rf#7?Xf][20Te]19]6f\Re#2Rf/=]Rg,9]10g6'4[20Sf]f]#2Rg/f]#L\^20Rg]f^#2Rh/=]=W9h\^1fh]P9f_S07#2Ri/=]P9P?g015820Q6]'tPceO1%75?X5]g015^Rcg016JRj#iRk#iRl#i,a91a9lS081a9kS0920N9]1a9jS0:60M95V95V95V9g016iS0;'q%pcRj3O&0KcRk1h93Rl1h98Rm7M4S0<&0J9Rn&0I9Ro1eo?Rp1_9FRq%;]Rr'd,So5@o&0F;R;PoPoP9Prg017URs1o96C`,So,UoP;P91_9DRtPs1_9CRs:0A9r=\9qC`,SoC3P;Po%;ORr=6otP;%1SS0=#1#N#J#>RS#;RuA\9us56oC3C3C320?o<R<P5P3g018<Rvg018\Rw't20>53=WvwdB0=964H0<Rwb4b5b6X09X19X89X7=AX83]g019<Rv\^1s]3/579W98[10O815S8,0S[[[^09^19^89^7=P5%73P3fb#2R]P8P4PAPMO7b3b>b_b^bKbJbIb>b2%QW,0SRWePWPQ20;99RW1RbI150U,R0%pWR05OW3ORUPVP_PTP_P5O1PLP4P5O2PfP4PJP_P4P415_QRQCACCP1193IRL9<g3PVP3P315V_RTCA198IRb9<h8RM#HP\P8P815\VRACAR^#Hg019YRx3D#HP51nEHRy196ERz%7H196I[[R{%7ER|AlEH4VxW;RH%7I\x^;|R}PjPk&0:9R~9Ml4S0>PnPoA6ost%;E&09G6069,dt,So5@oRGP;1UoG1eo7RG5@o,UoC3P<Pwb4b5b6X09X19X7=A<54JA<43LPv[/48Pv[[^09^19^7=P5PeP:P:PePdDB#H/4xP:P]P8O4b3b<b=X2MP5O1PyP{PHP}PjPkAMm4~?M8lPnPoA6oqtQ05,_9Rm9\9q,dt,So5@oRMP;1UoM1eo>5@o9@op,UoC3P<Pwb4b5b6X09X19X89X7=XA=1045Rp1543RM7X5P3P4P41538S05CAPv[=D7?Pv[[^09^19^89^7=^A=P5PxP]P:P:PICA#HPdPeP:P8O6b3b<b=X2^P5O1n200100000021100011000bD1RfIR^1R_QR:=OW0R]5OWRv0054#HeW@XE9J04B03UV_P_P\PVPKH07B08@\V1j@\%T\R@PeP\PdPaCGS0?%I\S0@'4RU'4PVP`P\PYP[P\P5O1PBP4P5O2PhP4PJP\P4P4PACACCP1A<i3LP`P3P3P`P\DB%JF#K#K#J#>RF/08P5f`RL#2?<8bPyP{PHP}%:D#PRD,nERb%7D1uEDRJ,96[\zRzAlED4VxX;|RD%7J\x^;|R|Q08Q09Q0:5V95V9Q0;'q=OcjRcPkAMl3~?M4~PnPoA6oms=@oGP;PoA6ormP;%;F=6osRmC3C3P<Pwb4b5b6X09X19X7=14p3Rp10O310F3RF[[^09^19^7=P519NIff#2PNP?PRO5b3b<b=bBbCW2P5O1PaP8P8PaP`DBPyP{PHP}PbPzPDP|PcPkQ0>PnPoA6ots=@oGP;Po%8C#[#c#N#c#N#J#>RG#;R|=6otP;PmC3C3P<Pwb4b5b6X09X19X7=10G3PF[\p^09^19^7=P5Q079bNLPLPNP?Q03O5b3b<b=bBbCW2P5O1n200100000021100011000bDW@XE9RNJ02P@PUPvP`P\Q03P4P5PWP2P^P]PjPk1h94RUPnPoA6orsRrP;%NC#F#[#K#K#K#[#K#N#>RC#;=6osR@C3P<Pwb4b5b6X0910O5RO10C4RL[^09P5PgP>O2R>b39mfIPWP2P:P0P1Q04#1#J#>R=,0QRQQ06#1#:#:#:#:#F#>Rp/0_R_1RVT$01PR10T=RFP\PAPjPkPUPnPoA6o|sR|P;P|C3P<Pwb4b5b6X0910G510G4[^09P5P`PKO2b310P\ePjPkQ0>PnPoA\9stRt%;=56oRPP;Q0=#8#N#J#>RK#;96otC3P<Pwb4b5b6X09X191554/0=10MK[^09^19P5P\P`P4O3b310AKeH00W:P5O110pVRKPjPkPUPnPo%;p=6osRsP;P@C3P<Pwb4b5b6X0910p5R@PL[^09P5P`P4O2RLb310C\e9m\AW:P5O1n2001000000211000110001kW2EYEYF~Q0?Q0@PePvP`P\PdPaQ02P4P5PW&0BeRvP^P]PePfPIPjPkPUPnPoPrP;PsC3P<Pwb4b5b6X0910p4Rr\O^09P>b310XfeH0CPWPvP:P0P1PQP_%Qg,0T,EKPR10p\RR%Qh,0ARAPcPkQ0<PnPoA6ouqP;PoPPP;A6otqC3C3P<Pwb4b5b6X09X19X8910S310M=Q05/07[[^09^19^89P5%QiP\P`P?P4O5b340DX:FP5O1PjPkPUPnPoPsP;PsC3P<Pwb4b5b6X09Pr\@^09PLb3:0ERAX:KP5O1n200100000021100011000A|99:,0pA{99:%Qf'0'Ee20Ge:e1kWvEYEYM:zPVP`P\PZP[PNJ0HCgCgCgPePdPaP\C?ebZbQbWW[WGWFP4P5O2n2001000000121000000W2P4P5O2n2001000000121000000b2WLWMWTW:P4P5O2n2001000000121000000W2WSP4P5O2n2001000000121000000W2WXWUWVP4P5O2n2001000000121000000W2WHP4P5O2n2001000000121000000W2WPP4P5O2n2001000000121000000W2X]9XR9WYWOWNX`9X\9W?P5O1W?o"). Qed.

Section NIf.
  Context {HCEIL : HeapCeil}.
  Variables (R : bvmap 5 word) (M : mem) (sp ds xenc fl fill ret lo shi gd FR : Z).

  Record npre : Prop := NPRE {
    np_ra : getr R 1%bv = Z_to_bv 64 ret; np_ret : ret_ok (Z_to_bv 64 ret); np_retr : 0 <= ret < 2 ^ 64;
    np_sp : getr R 2%bv = Z_to_bv 64 sp; np_tp : getr R 4%bv = Z_to_bv 64 ATP;
    np_a0 : getr R 10%bv = Z_to_bv 64 ds; np_a1 : getr R 11%bv = Z_to_bv 64 xenc;
    np_slo : 2 ^ 33 <= sp - (FR + NWIN); np_shi : sp <= 2 ^ 47; np_al : sp mod 16 = 0;
    np_md : mdef M (sp - (FR + NWIN)) (FR + NWIN);
    np_ds : AIMG_TOP <= ds /\ ds + 392 <= 2 ^ 47 /\ ds mod 8 = 0;
    np_dj : ds + 392 <= sp - (FR + NWIN) \/ sp <= ds;
    np_dsd : mdef M ds 392; np_app : LbA_DiagStmt.app_obj ds 392;
    np_vt : fld SEGS M ds 8 LbA_DRep.VT_OS_A; np_vsb : fld SEGS M (ds + 8) 8 LbA_DRep.VT_SB_A;
    np_fl : fld SEGS M (ds + 120) 4 fl; np_flr : fl = LbA_DiagStmt.DS_FL0 \/ fl = LbA_DiagStmt.DS_FLHEX;
    np_wid : fld SEGS M (ds + 136) 8 0; np_st : fld SEGS M (ds + 144) 4 0; np_rdb : fld SEGS M (ds + 152) 8 (ds + 8);
    np_loc : fld SEGS M (ds + 160) 8 LbA_DRep.LOC_IMP_A; np_tie : fld SEGS M (ds + 248) 8 0;
    np_fill : fld SEGS M (ds + 256) 4 fill; np_fillr : fill = 2 ^ 32 - 1 \/ fill = 32;
    np_dt : dstat_rs D_DIAG_A M;
    np_can : fld SEGS M A_CANARY 8 gd; np_gd : 0 <= gd < 2 ^ 64;
    np_rf : rfull R; np_ni : ninv lo shi M; np_stk : stk asegs M lo sp; np_ceil : aceil <= lo;
    np_los : lo + (FR + NWIN) <= sp; np_shi' : sp <= shi }.

  Variables (padra opret : Z) (fillw : word) (SVop : list word) (sv9 sv18 sv19 sv20 sv21 sv22 sv23 : word).
  Record nmid (nc : Z) (R1 : bvmap 5 word) (M1 : mem) : Prop := NMID {
    nm_st : stores_in (fun a => zwin (sp - (FR + NWIN)) sp a \/ zwin (ds + 256) (ds + 260) a \/ zwin ATDLOC (ATDLOC + 8) a) M M1;
    nm_fill : fld SEGS M1 (ds + 256) 4 32;
    nm_svop : slots SEGS M1 sp SVop;
    nm_sv : slots SEGS M1 (sp - FR) [Z_to_bv 64 opret; Z_to_bv 64 ds; sv9; sv18; sv19; sv20; sv21];
    nm_padsv : slots SEGS M1 (sp - FR - 160) [Z_to_bv 64 padra; fillw; Z_to_bv 64 (ds + 112); Z_to_bv 64 (ds + 8); Z_to_bv 64 (sp - FR - 88 + nc);
                                              Z_to_bv 64 (sp - FR - 88); Z_to_bv 64 0x6c2920; sv22; sv23];
    nm_r1 : getr R1 1%bv = Z_to_bv 64 A_PAD_XS_RET; nm_r2 : getr R1 2%bv = Z_to_bv 64 (sp - FR - 256);
    nm_r3 : getr R1 3%bv = getr R 3%bv; nm_r4 : getr R1 4%bv = getr R 4%bv;
    nm_r8 : getr R1 8%bv = Z_to_bv 64 (ds + 8); nm_r9 : getr R1 9%bv = Z_to_bv 64 (ds + 112);
    nm_r10 : getr R1 10%bv = Z_to_bv 64 (ds + 8); nm_r11 : getr R1 11%bv = Z_to_bv 64 (sp - FR - 133); nm_r12 : getr R1 12%bv = Z_to_bv 64 nc;
    nm_r19 : getr R1 19%bv = Z_to_bv 64 nc;
    nm_cs : forall r, In r [24; 25; 26; 27]%bv -> getr R1 r = getr R r;
    nm_nc : 1 <= nc <= 21;
    nm_rf : rfull R1;
    nm_td : tdl_pinned M1 }.

  Record nmidP (nc : Z) (R1 : bvmap 5 word) (M1 : mem) : Prop := NMIDP {
    nq_st : stores_in (fun a => zwin (sp - (FR + NWIN)) sp a \/ zwin (ds + 256) (ds + 260) a \/ zwin ATDLOC (ATDLOC + 8) a) M M1;
    nq_fill : fld SEGS M1 (ds + 256) 4 32;
    nq_r1 : getr R1 1%bv = Z_to_bv 64 A_PAD_XS_RET; nq_r2 : getr R1 2%bv = Z_to_bv 64 (sp - FR - 256);
    nq_r3 : getr R1 3%bv = getr R 3%bv; nq_r4 : getr R1 4%bv = getr R 4%bv;
    nq_r10 : getr R1 10%bv = Z_to_bv 64 (ds + 8); nq_r11 : getr R1 11%bv = Z_to_bv 64 (sp - FR - 133); nq_r12 : getr R1 12%bv = Z_to_bv 64 nc;
    nq_nc : 1 <= nc <= 21;
    nq_rf : rfull R1;
    nq_td : tdl_pinned M1 }.
  Lemma nmidP_of_nmid : forall nc R1 M1, nmid nc R1 M1 -> nmidP nc R1 M1.
Proof.
ltac2:(KReplay.run1 (kr_t_LbA_NIf ()) ["NIf"] "p'0h01Hh12M1h22R1h31ah42nch56nm_cs0h68nm_fill0h76nm_nc0h89nm_padsv0h96nm_r13h:6nm_r14h;6nm_r15h<6nm_r16h=6nm_r17h>6nm_r18h?6nm_r20h@5nm_r5hA5nm_r6hB5nm_r7hC6nm_rf0hD6nm_st0hE6nm_sv0hF8nm_svop0hG6nm_td0hH1ri005nm_csi017nm_filli025nm_nci038nm_padsvi045nm_r1i056nm_r10i066nm_r11i076nm_r12i086nm_r19i095nm_r2i0:5nm_r3i0;5nm_r4i0<5nm_r8i0=5nm_r9i0>5nm_rfi0?5nm_sti0@5nm_svi0A7nm_svopi0B5nm_tdp;1p;2p;3p;5p;4p;?g007lj10Tg008oj11Tg00Sgj1BTg01:5j1FTg01:Xj2QTg01;DR0j3NTg01<?j3MTg00:hj28Tg01=;j2:Tg01=Xj3?Tg008Qj17Tg00;aj2@Tg0053j3PTg00D8j1=Tg01>Jj5OTg01??j4>Tg01@9j22Tg00Ggj1ETg00HGj3<Tg01@_j2;Tg01AQj3JTg00;Ej2ATg00:Mj2ITg01Ahj1KTg01Bej1LTg01Cel?HTg01Daj3DTg00@Ij3GTf0R1#0#7p=9f4R2f3R3f2R4f1R5;<13<p=5%01#0p=6g01EDR69D51p=C1;45=G31p=4%71=D56p=3g00jRR6g010dR7#0R8#1R9#BR:%08R;#0R<#0R=#0R>#0R?#BR@#FRA'Qg00o<AN451P0P3P4P5AM234P1p,2spR0p,2FRRBg01E`'8':??01p,2dsRC%0?#9R?'8RD%1>#0#9,8C;?1g01FYRE%7<R<,8E;?1'@'@X36p,1MfD3Pg00omR6fEPDg016J#=#=#=#=%7>DOP6fFP0p,4SVopC>P6fG1:0BRBPAp,5opret,2@PA12@CPAp,3sv9PAp,4sv18PAp,4sv19PAp,4sv20p,4sv21%EAR05<AD5D5D5C>P6fH%09R6#0#6#9,:BPAp,5padra,2@PAp,5fillwPA%17R>#1#0#6#9,8C,2@RDPA18C<,2@RCPA%19R9#6#9,:BREfJRF'8,2@PA12@EPA%0>RE#1RG#1RH#6#6#1#0#1#6#1#6#1#6#6#9,2@PAp,4sv22p,4sv23=<A0D5D5D5D5C>PAPF%77R7,C:g01GR,2@C4PAfK13:81:B?,2@C4PAfL13:>R>p,1RR?/;>C4PAfM13:;R>1;?>C4PAfN1C:<PCC4PAfO%1;R;,3:PDC4PAfP13:6PCC4PAfQ13:9%1=#0#1#7,:B,2@C4PAfR%0ERE,3:fSRB,2@C4PAPB%1;,3:fT,2@C4%F:R@P@%0E,3:P@%1E,3:P@%0G,3:P@13:H%E@D5D59J@1PAfVRAP51;?5C4[]H1A7A%16#7,AA'I%KA%LAfYfXfWfBRAfAR6f=R7f<R?f;R@f:RHf7R:f6RGf5REP4P5P1M?HWGWCW7W5W?W>W=W<W;W:W9WBWAW@W8WEWFW6WDPAP6f@f?f>P7P?P@PHf9f8P:PGPEP2P3P4P5P1OCn300010000001C110?10110A10@10310410910:10;10<10=10510610710810010210>10BW0W1W2W4o"). Qed.

  Record nback (nc : Z) (R1 : bvmap 5 word) (M1 : mem) (R' : bvmap 5 word) (M' : mem) : Prop := NBACK {
    nb_kept : forall r, In r NKEPT -> getr R' r = getr R1 r;
    nb_r10 : getr R' 10%bv = Z_to_bv 64 nc;
    nb_rf : rfull R';
    nb_ag : agree_on (zwin (sp - FR - 256) sp) M1 M';
    nb_md : mdef M' (sp - (FR + NWIN)) (FR + NWIN);
    nb_dsd : mdef M' ds 392;
    nb_vt : fld SEGS M' ds 8 LbA_DRep.VT_OS_A; nb_fl : fld SEGS M' (ds + 120) 4 fl;
    nb_st : fld SEGS M' (ds + 144) 4 0; nb_rdb : fld SEGS M' (ds + 152) 8 (ds + 8);
    nb_ni : ninv lo shi M' }.

  Record nfin (M' : mem) (R4 : bvmap 5 word) (M4 : mem) : Prop := NFIN {
    nf_st : stores_in (fun a => zwin (sp - (FR + NWIN)) sp a \/ zwin (ds + 136) (ds + 144) a) M' M4;
    nf_wid : fld SEGS M4 (ds + 136) 8 0;
    nf_r1 : getr R4 1%bv = Z_to_bv 64 ret; nf_r2 : getr R4 2%bv = Z_to_bv 64 sp; nf_r10 : getr R4 10%bv = Z_to_bv 64 ds;
    nf_cs : forall r, In r NCS -> getr R4 r = getr R r;
    nf_rf : rfull R4 }.
End NIf.
