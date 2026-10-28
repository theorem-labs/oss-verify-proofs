(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BMState BMem BCells BArr BExec BLFrame BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BakeStackRep BllocRepX RtB_IMemset RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Bridge LbB_Conv LbB_Call LbB_DStat LbB_NBr LbB_NMc LbB_NLeaf LbB_NPc1 LbB_NLoops LbB_NSnp LbB_NKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DPdK LbB_PqK LbB_DRep LbB_DiagStmt LbB_PcStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail SumWalkTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumTac NumLeaf.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_NIf () := "C46Stdlib5Lists4List2hdC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_NLeaf4ninvC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack06stack0C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_NBr;relro_clearC5ARocqVerifyHarness?AgentSubmission7LibCont7ContLib9stores_inC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_DiagStmt7app_objC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow5aceilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow;aceil_factsC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil5hceilC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame7outsideC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_NBrBmunch_of_stores_inC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_NBrBwmono_of_stores_inC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_NBr:mem_inv_hiC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DPdK<aconst_ok_hiC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst9aconst_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DPdK<aconst_ok_loK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst<ACONST_frameC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack09stack0_okC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0=stack0_ok_appK47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsStack0@stack0_transportC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_NBr>relro_clear_hiK47Corelib4Init5Logic3and01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil8HeapCeil00C4ARocqVerifyHarness?AgentSubmission8LibIface3memC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsK47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs8AIMG_TOPC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow9ALOWSH_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow6AHI_LOC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow7AAPP_HII47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapi6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_NIf4nmid00i6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_NIf5nmidP00C56Stdlib6ZArith6BinInt1Z3subC4ARocqVerifyHarness?AgentSubmission8LibIface4zwinC5ARocqVerifyHarness?AgentSubmission7LibCont4CRep3fldC5ARocqVerifyHarness?AgentSubmission7LibDiag7DiagTac5slotsC45stdpp9bitvector;definitions7Z_to_bvC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC46Stdlib5Lists4List2InC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_NSnp:tdl_pinnedk6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_NIf5nmidP01K45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic4True01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_NIf4NWINC6ARocqVerifyHarness?AgentSubmission3bpB2Rt6RtB_Td6ATDLOCC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_NKit<A_PAD_XS_RET".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation SEGS := asegs (only parsing).

Definition NWIN : Z := 8192.
Definition A_CTYPE_ID : Z := 0x6c4350.
Definition A_NUMPUT_ID : Z := 0x6c40d8.
Definition A_NUMPUT_OBJ : Z := 0x6c4420.
Definition VT_NUMPUT : Z := 0x183a48.
Definition VT_CTYPE : Z := 0x182e80.
Definition FACETS_BEG : Z := 0x6c46c0.
Definition FACETS_END : Z := 0x6c47b0.
Definition DPU_RETPC : Z := 0x132c30.
Definition DPL_RETPC : Z := 0x1326fc.
Definition PADRA_UL : Z := 0x132c10.
Definition PADRA_L : Z := 0x1326dc.

Definition NKEPT : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition NCS : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma ninv_obj {HCEIL : HeapCeil} : forall lo shi M M' (W : Z -> Prop) O n, ninv lo shi M -> stores_in W M M' ->
  LbB_DiagStmt.app_obj O n -> 0 <= n ->
  (forall a, W a -> aceil <= a < 2 ^ 63 \/ O <= a < O + n) -> ninv lo shi M'.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_NIf ()) [] "h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with74__p1h84__x3h91ah:2O2h;2Hah<6__sat4h=6__sat5h>5HCEILh?2H0h@2HxhA4__p2hB6__sat6hC6__sat7hD1ohE1xhF2A1hG2A2hH2AChI2H1hJ2H2hK2H3hL2HWhM2HnhN1MhO2M'hP2MIhQ2MUhR1OhS2O1hT2O3hU2RRhV2S0hW2SHhX2SThY1WhZ2WMh[2_Hh\2loh]1nh^1qh_1rh`3ship%0p&0p;4p;2p;1p;3p;6p;7p;:p;8p-1p10000p4p710p8g000Gj4?Tg001Bj2jTg002>j1OTg0038j4GTg0043j1ITg0053j3^Tg0061j2]Tg0072j12Tg007lj11Tg008Qj1NTg008oj17Tg009Tj2uTg00:1j29Tg00:MR0j24Tg00:hj25Tg00;Ej20Tg00;aR1j2FTg00<;k10@Tg00=;j2>Tg00=[j1XTg00>Uj2}Tg00?6j1HTg00?Oj2fTg00?lj2sTg00@Ij3UTg00@cj2vTg00AJk20TTg00B1k20STg00BWk20RTg00C=k20QTg00C^j2tTg00D8j1iTg00DWj2aTg00E@k20NTg00Eik30MTg00FRj3TTg00G;j2qTg00Ggj1pTg00HGj3LTg00Hgk10KTg00IGj2hTg00Iek10JTg00JCk10ITg00Jnj2_Tg00KQk10FTg00L3j2oTg00LVj4`Tg00MAk30ATg00Mdj3\Tg00NGk20?Tg00Nik20>Tg00OUk30=Tg00P4k40<Tg00Pfj1PTg00Q]k20;Tg00R=j2nTg00Rej3lTg00SIk10:Tg00Sgk109Tg00TEk306Tg00Thk205Tg00Ugk604Tg00Vnk303Tg00Wkk407Tg00Y2k308Tg00Yok602Tg00Znj3mTg00\0R2k101Tg00\mk400Tg00]oj2kTg00^Pj6WTg00_1j7~Tg00`1k10Bk20GTg00`ok40CTg00b1k30DTg00bKk30ETg00bej3|Tg00cBj3{Tg00c_l:zTg00ddk60HTg00egj4gTg00fBj4yTg00f`k60LTg00gDj7rTg00ghj7xTg00hLj6wTg00i0k80OTg00iTk40PTf2R3f1R4f0R5'4'4p=Eg00j4R6/05p=8%75#7#7#7p=:f4R7f3R8'01545,93'4p=C1083/44/F5p=D10831945'4p=B%15#7p=Z%75#7p=c%15#1#1#1#1#1#1#1p=@%15#1#1#1#1#1#1#Np=<1034/45p==g00jRR9?U56p=J1545,93p=b1945,43p=VP9P3P4P5Cyp=KP4g00k0R:g00kOR;P;g00koR<P5J0Lp=e1o95p=;P9P4g00lOP5C`p=dP4P:P;P;P<P5g00m6R=Frp=RP3P:P;P;P<P4P5Fxp=AP4P:P;P;P<P5Ewp=SP8P:P;P;P<P3P4P5L0Op=3P3P:P;P;P<P9P4g00mVP5C`P=Frp=6%15#1p=[%15#1#1#1p=MP9P9P4P5H0Pp=Q%75#1p=Yg00n=R=g00o<S00Q00p-0R:\9f7R>f6R?f5R@P7C?P0g00omRA/j@%O@f8RBP@P>P?CG%I@3EA^7?@1]78%87PBP5O1f>RC#2P4g010dRD#1RE#NRF%7DRG#:RH#NRI'uRJ,94RKPBP4P4PBP>DCCD[^99f=RLf<RMf;RNf9ROC?[[[[P51jA>%OBPNPBf:RPPOCG%IB3EP0%OOPMPOPNPPCG%IO'4A^BPO1]B>%8BPMP5O1fBRP#2P4PKPMP4P4PMPNDCCD[^99fARQf@RRf?RSPLC?[[[[P5%ONPSPMPCPLCG%IM'4P0PRPLPSPCCG%ILA^MCL1]MN%8MPRP5O1fFRL#2P4PKPRP4P415RSRTCBCD[^99fERUfDRVfCRWPQC?[[[[P5PPPSPQPRCG%IRA^SQR1]SCP0g011IRQ/0Rg012CRX,0Tg013ARY/0R'Fg014<RZ,0T'4%8RPVP5O1fJRR#2P4PKPVP4P415VWRTCBCD[^99fIS01fHR[fGR\PUC?[[P510QP15WPRP/0X10YW'F10PZ'4P010TX10YV'F10TZ%8VP[P5O1fNRV#2P4PKP[P4P4P[P\DCCD[^99fMS02fLfKRTQ01C?[[P515LU/0X10YL'F15\L/0Z%8\PTP5O1fQRZ#2RXP4PKPTP4P4PTPRDCCD[^99fPRR$0@%7H#:#:RT#Z#cS03#7#:#@#@#<RP%2RRW%7TRT#:#:#@#@#<R],0W3=%1ES04#1R^#1#@S05#NR_,>W#JPW%XRR`P`PWP_DC3EP010X]9=PX1>X_#J%XZRW,0XAbWX_3EfRRWPZPRPVC?P5fSRV#2RR10R]5=PP0fTR0#2RR,0P10R]fURR#2RX/>_#J%XRR`,0XAb`X_3EfVR`PRP0PWC?[P5%2`,0PfWRW#2/0]fXR]#2RX/>_#J%X]Ra,0XAbaX_3EfYRa#2RX%N^R^'}%J^R_#HfZRb#2Rc1fc^,s^1>c^'55U9[1vc^196^Rdf[Re#2Rf/>^Rg#8?Vg^[20Tf^19^6f\Rf#2Rg/>^Rh,9^10h6'4[20Sg^f]#2Rh/f^#J\_20Rh^f^#2Ri/>^=U9i\_1fi^P9f_S06#2Rj/>^P9P@g015820Q6^'tPdeO1%85?V5^g015^Rdg016JRk#iRl#iRm#i,a91a9mS071a9lS0820N9^1a9kS0960M95T95T95T9g016iS0:'q%pdRk3L&0KdRl1h93Rm1h98Rn7K4S0;&0J9Ro&0I9Rp1ep@Rq1_9GRG%;^Rr'd,Rp5Ap&0F;R;PpPpP9Prg017URs1o96C`,Rp,SpP;P91_9ERtPs1_9DRs:0A9r=\9GC`,RpC3P;Pp%;PRr=6ptP;%1TS0<#1#[#M#<RT#;RuA\9us56pC3C3C320?p<R<P5P3g018<Rvg018\Rw't20>53=UvwdB0=964H0<Rwb4b5b6X09X19X89X7:AV83^g019<Rv\_1s^3/579U98[10P815T8,0T[[[^09^19^89^7:P5%83P3fb#2R^P8P4PBPNO7b3b?b_b^bKbJbIb?b2%PX,0TRXePXPR20;99RX1QcJ150V,Q0%pXR05LX3LRVPWP`PUP`P5O1PMP4P5O2PgP4PKP`P4P415`RRRCBCDP1193JRM9=h3PWP3P315W`RUCB198JRc9=i8RN#HP]P8P815]WRBCBR_#Hg019YRx3E#HP51nFIRy196FRz%8I196J[[R{%8FR|AlFI4VxW;RI%8J\x^;|R}PkPl&0:9R~9Km4S0=PoPpA6pst%;F&09H6069,dt,Rp5ApRHP;1SpH1ep7RH5Ap,SpC3P<Pwb4b5b6X09X19X7:A=54KA=43MPv[/48Pv[[^09^19^7:P5PfP>P>PfPeDC#H/4xP>P^P8O4b3b<b=X2NP5O1PyP{PIP}PkPlAKn4~?K8mPoPpA6pGtQ04,_9Rn9\9G,dt,Rp5ApRNP;1SpN1ep?5Ap9Apq,SpC3P<Pwb4b5b6X09X19X89X7:XA:1045Rq1543RN7V5P3P4P41538S04CBPv[=E7@Pv[[^09^19^89^7:^A:P5PxP^P>P>PJCB#HPePfP>P8O6b3b<b=X2_P5O1n200100000021100011000bD1QgJR_1Q`RR>=LX0R^5LXRv0054#HeW@XE9J04B03VW`P`P]PWPLH07B08A]W1jA]%O]RAPfP]PePbCGS0>%I]S0?'4RV'4PWPaP]PZP\P]P5O1PCP4P5O2PiP4PKP]P4P4PBCBCDP1A=j3MPaP3P3PaP]DC%7D#M#c#[#M#<RM/08P5f`RK#2?=8cPyP{PIP}%:E#NRE,nFRc%8E1uFERC,96[\zRzAlFE4VxX;|RE%8C\x^;|R|Q07Q08Q095T95T9Q0:'q=LdkRdPlAKm3~?K4~PoPpA6pns=ApHP;PpA6prnP;%;M=6psRnC3C3P<Pwb4b5b6X09X19X7:14q3Rq10P310M3RM[[^09^19^7:P519OJff#2POP@PSO5b3b<b=bBbCW2P5O1PbP8P8PbPaDCPyP{PIP}PcPzPEP|PdPlQ0=PoPpA6pts=ApHP;Pp%7D#Z#c#Z#@#<RH#;R|=6ptP;PnC3C3P<Pwb4b5b6X09X19X7:10H3PM[\q^09^19^7:P5Q069bOKPKPOP@Q02O5b3b<b=bBbCW2P5O1n200100000021100011000bDW@XE9ROJ02PAPVPvPaP]Q02P4P5PXP2P_P^PkPl1h94RVPoPpA6prsRrP;%[D#@#Z#Y#Y#Y#Y#M#<RD#;=6psRAC3P<Pwb4b5b6X0910P5RP10D4RK[^09P5PhP?O2R?b39mgJPXP2P>P0P1Q03#1#M#<R:,0RRRQ05#1#:#:#:#:#@#<Rq/0`R`1QWU$01PS10U:RMP]PBPkPlPVPoPpA6p|sR|P;P|C3P<Pwb4b5b6X0910H510H4[^09P5PaPLO2b310Q]ePkPlQ0=PoPpA\9stRt%;:56pRQP;Q0<#7#[#M#<RL#;96ptC3P<Pwb4b5b6X09X191554/0:10NL[^09^19P5P]PaP4O3b310BLeH00W:P5O110qWRLPkPlPVPoPp%;q=6psRsP;PAC3P<Pwb4b5b6X0910q5RAPK[^09P5PaP4O2RKb310D]e9m]BW:P5O1n2001000000211000110001kX2EWEWF~Q0>Q0?PfPvPaP]PePbQ01P4P5PX&0BfRvP_P^PfPgPJPkPlPVPoPpPrP;PsC3P<Pwb4b5b6X0910q4Rr\P^09P?b310YgeH0CPXPvP>P0P1PRP`%Ph,0U,FLPS10q]RS%Pi,0BRBPdPlQ0;PoPpA6puGP;PpPQP;A6ptGC3C3P<Pwb4b5b6X09X19X8910T310N:Q04/07[[^09^19^89P5%PjP]PaP@P4O5b340DX:MP5O1PkPlPVPoPpPsP;PsC3P<Pwb4b5b6X09Pr\A^09PKb3:0ESBX:LP5O1n200100000021100011000A|99>,0qA{99>%Pg'0'Fe20Gf>e1kXvEWEWM:zPWPaP]P[P\POJ0HCgCgCgPfPePbP]C?ebZbQbWW[WGWFP4P5O2n2001000000121000000W2P4P5O2n2001000000121000000b2WLWMWTW:P4P5O2n2001000000121000000W2WSP4P5O2n2001000000121000000W2WXWUWVP4P5O2n2001000000121000000W2WHP4P5O2n2001000000121000000W2WPP4P5O2n2001000000121000000W2X]9XR9WYWOWNX`9X\9X>=P5O1X>=P5O1W>o"). Qed.

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
    np_dsd : mdef M ds 392; np_app : LbB_DiagStmt.app_obj ds 392;
    np_vt : fld SEGS M ds 8 LbB_DRep.VT_OS_A; np_vsb : fld SEGS M (ds + 8) 8 LbB_DRep.VT_SB_A;
    np_fl : fld SEGS M (ds + 120) 4 fl; np_flr : fl = LbB_DiagStmt.DS_FL0 \/ fl = LbB_DiagStmt.DS_FLHEX;
    np_wid : fld SEGS M (ds + 136) 8 0; np_st : fld SEGS M (ds + 144) 4 0; np_rdb : fld SEGS M (ds + 152) 8 (ds + 8);
    np_loc : fld SEGS M (ds + 160) 8 LbB_DRep.LOC_IMP_A; np_tie : fld SEGS M (ds + 248) 8 0;
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
                                              Z_to_bv 64 (sp - FR - 88); Z_to_bv 64 0x6c4260; sv22; sv23];
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
ltac2:(KReplay.run1 (kr_t_LbB_NIf ()) ["NIf"] "p'0h01Hh12M1h22R1h31ah42nch56nm_cs0h68nm_fill0h76nm_nc0h89nm_padsv0h96nm_r13h:6nm_r14h;6nm_r15h<6nm_r16h=6nm_r17h>6nm_r18h?6nm_r20h@5nm_r5hA5nm_r6hB5nm_r7hC6nm_rf0hD6nm_st0hE6nm_sv0hF8nm_svop0hG6nm_td0hH1ri005nm_csi017nm_filli025nm_nci038nm_padsvi045nm_r1i056nm_r10i066nm_r11i076nm_r12i086nm_r19i095nm_r2i0:5nm_r3i0;5nm_r4i0<5nm_r8i0=5nm_r9i0>5nm_rfi0?5nm_sti0@5nm_svi0A7nm_svopi0B5nm_tdp;1p;2p;3p;5p;4p;?g007lj10Tg008oj11Tg00Sgj1BTg01:5j1DTg01:Xj2RTg01;DR0j3PTg01<?j3NTg00:hj27Tg01=;j29Tg01=Xj3?Tg008Qj18Tg00;aj2GTg0053j3QTg00D8j1>Tg01>Jj5OTg01??j4@Tg01@9j22Tg00Ggj1ETg00HGj3=Tg01@_j2<Tg01AQj3MTg00;Ej2ATg00:Mj2LTg01Ahj1KTg01Bej1JTg01Cel?ITg01Daj3FTg00@Ij3HTf0R1#0#8p=:%11#0p=;f4R2f3R3f2R4f1R5;=13=p=6%01#0p=5g01EDR69F51p=C1<45=H31p=4%81=F56p=3g00jRR6g010dR7#0R8#1R9#BR:%08R;#0R<#0R=#0R>#0R?#BR@#DRA'Rg00o<AP451P0P3P4P5AN234P1p,2spR0p,2FRRBg01E`'7'9??01p,2dsRC%0?#:R?'7RD%;>#:,7C;?1g01FYRE%8<R<,7E;?1'G'GX36p,1MfD3Qg00omR6fEPDg016J#>#>#>#>%8>DOP6fFP0p,4SVopC@P6fG190BRBPAp,5opret,2@PA12@CPAp,3sv9PAp,4sv18PAp,4sv19PAp,4sv20p,4sv21%EAR05=AD6D6D6C@P6fH%09R6#0#5#:,9BPAp,5padra,2@PAp,5fillwPA%17R>#;#5#:,7C,2@RDPA17C<,2@RCPA%19R9#5#:,9BREfJRF'7,2@PA12@EPA%;7#1#;#5#1#5#5#1#5#1#1#5#5#:,2@PAp,4sv22p,4sv23==A0D6D6D6D6C@PAPF%87R7,C:g01GR,2@C4PAfK13:819B?,2@C4PAfL13:>R?p,1RR8/<?C4PAfM13:;R?1<8?C4PAfN1C:<PCC4PAfO%1;R;,3:PDC4PAfP13:6PCC4PAfQ13:9%;=#1#8,9B,2@C4PAfR%0>R>#0RB,3:fSR=,2@C4PAP=%1;,3:fT,2@C4%D:R@P@%0B,3:P@%1B,3:P@%1>R>#0,3:P@%1>,3:%E@D6D69M@1PAfVRAP51<85C4[]H1A7A%16#8,AA'L%KA%JAfYfXfWfBRAfAR6f=R7f<R8f;R@f:R:f7R>f6RBf5R;P4P5P1M?IWGWCW7W5W?W>W=W<W;W:W9WBWAW@W8WEWFW6WDPAP6f@f?f>P7P8P@P:f9f8P>PBP;P2P3P4P5P1OCn300010000001C110?10110A10@10310410910:10;10<10=10510610710810010210>10BW0W1W2W4o"). Qed.

  Record nback (nc : Z) (R1 : bvmap 5 word) (M1 : mem) (R' : bvmap 5 word) (M' : mem) : Prop := NBACK {
    nb_kept : forall r, In r NKEPT -> getr R' r = getr R1 r;
    nb_r10 : getr R' 10%bv = Z_to_bv 64 nc;
    nb_rf : rfull R';
    nb_ag : agree_on (zwin (sp - FR - 256) sp) M1 M';
    nb_md : mdef M' (sp - (FR + NWIN)) (FR + NWIN);
    nb_dsd : mdef M' ds 392;
    nb_vt : fld SEGS M' ds 8 LbB_DRep.VT_OS_A; nb_fl : fld SEGS M' (ds + 120) 4 fl;
    nb_st : fld SEGS M' (ds + 144) 4 0; nb_rdb : fld SEGS M' (ds + 152) 8 (ds + 8);
    nb_ni : ninv lo shi M' }.

  Record nfin (M' : mem) (R4 : bvmap 5 word) (M4 : mem) : Prop := NFIN {
    nf_st : stores_in (fun a => zwin (sp - (FR + NWIN)) sp a \/ zwin (ds + 136) (ds + 144) a) M' M4;
    nf_wid : fld SEGS M4 (ds + 136) 8 0;
    nf_r1 : getr R4 1%bv = Z_to_bv 64 ret; nf_r2 : getr R4 2%bv = Z_to_bv 64 sp; nf_r10 : getr R4 10%bv = Z_to_bv 64 ds;
    nf_cs : forall r, In r NCS -> getr R4 r = getr R r;
    nf_rf : rfull R4 }.
End NIf.
