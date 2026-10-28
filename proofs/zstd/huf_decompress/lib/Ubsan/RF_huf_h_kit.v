(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_h_kit () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission6Common:Stdio_pure>impl_post_evt'C47Corelib4Init9Datatypes3fstC5ARocqVerifyHarness?AgentSubmission3Lib5ITree5epostC5ARocqVerifyHarness?AgentSubmission4Spec5Monad5implMC46Stdlib5Lists4List8map_consC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtI47Corelib4Init9Datatypes4prod00I6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc00C47Corelib4Init9Datatypes3sndK6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_doneK6ARocqVerifyHarness?AgentSubmission3Lib5ITree3Exc3exc02K47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsK47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps4bptrC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3appI46Stdlib5Lists4List5NoDup00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RATPC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep6RERRNOC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks5blockI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface<rclient_addrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface:rheap_presC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface5RHEAPC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPI47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface@rclient_write_okI47Corelib4Init5Logic2or00C46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks8blk_addrC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks8blk_sizeI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01C46Stdlib5Lists4List;Forall_implC5ARocqVerifyHarness?AgentSubmission5Ubsan>RMalloc_ifacePARHEAP_frame_proofI5ARocqVerifyHarness?AgentSubmission4Spec6PState6PState00C5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree3memC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep5RLIBCC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RCTXC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep:RSSP_GUARDC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep8RGOT_SSPC5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree8rauxv_okC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission5Ubsan;RMallocTree>rauxv_ok_frameK46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg:RAUXV_CELLK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RMalloc_ifacePHRHEAP_blocks_nodup_proofK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5Ubsan>RMalloc_ifacePKRHEAP_blocks_disjoint_proofC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks6blk_idC47Corelib4Init5Logic9False_indC46Stdlib5Lists4List:in_map_iffK47Corelib4Init5Logic2ex01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C46Stdlib5Lists4List:in_app_iffC46Stdlib5Lists4List8in_splitC46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List>NoDup_remove_2C46Stdlib5Lists4List7map_appC47Corelib4Init9Datatypes8list_indC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kit8fh_fp_okC5ARocqVerifyHarness?AgentSubmission5Ubsan>RMalloc_ifacePGRHEAP_block_range_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface<rblock_rangeC5ARocqVerifyHarness?AgentSubmission6Malloc<Malloc_iface8in_blockC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_donec5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kitHblocks_distinct_disjointc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kitAoutside_of_forallK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC56Stdlib6ZArith6BinInt1Z6of_natc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kitGdisjoint_from_of_forallC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface=ralloc_staticC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kitCrheap_pres_of_munchK46Stdlib9micromega5Tauto8GFormula07I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition hideP (P : Prop) : Prop := P.

(* [comment removed for export] *)
Lemma implM_post_evt : forall {St A} (c : Monad.M St A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  implM usegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt usegs (Q' a s') ms') ->
  implM usegs c s Q' ms.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_kit ()) ["CANSEC1"] "p'0h01pi001ph13ms'h22H'h31ai011ah42s'h51Ah61Hh72HQh81Qh92Q'h:2Sth;2a0h<1ch=2msh>1rh?1si021si031ep;2p;7p;3p;1p;4p;8p10000p4p710p1000Mp4p710R0p8p200R1g000iR2p4p710p8P1g001ZR3p4p7210R4p8P1g002_R5p4p7210p8P1g003<R6p4p710R7p8p201R8P2p4p7210p8P8P5p4p710p8P8P4p8P8g0040R4p4p73110p8P8P7p8p1004ep4p7210P0p8P2j2>TP4j79Tg005Bj33Tg0063R4j22Tg006SR2j1=TP5j31Tg007Kj30TP6j28j45j34Tg007hj17Tg008`j4;Tg009Vj26Tg00:Nj4:TP3j8<Tf1R3f0R6'>f2R5f4R0g00:nR7p-0[R9[\5f3R:f5R;P9[[f6R9g00<5R<P;P0P:P5P6F9f8R=P9P5P3P6O3P9P:P5O2=3<3[^17]4^39P<f7R>/2=R?#=R@P9P;O1P;f9RA=1=6RBA0=A6RCO2X0?,8?P0PBPCO2X0?,8?P5P3P212=Af:R2f;R?'2RCP=f<RB=1?6R0A0?B6RDO2X0CP3P6C512?BREP=f=RF=1B6A0BF6O2X0E;45=3<3[^17P612A2REP>A12?6A02?6O2X0E%7EP6C5P<P>P0PDO2X0C%7C54CRCP3g00<jC;A3<C3eW2X17P4P2P?12BFR?P2f>R4=1F6A0F46O2X0?16?3P6C512F4R?P2f?R2=146A0426O2X0?16?534=3<3[^17P6f@R?,22RCPFfARD=1?6A0?D6O2X0CP2P?P5P3C:,6CP6C5PAP?PDP:P5C:RA91?DA0?DAP3P6O412?DR?PFfBRF=1D6A0DF6O2X0?16?A34=3<3eW2X17X44X3BP3P6O2n2001100000120101102X;EP6O1n10110300020010101X>@G<P=P<P>P9P;P:P5F9eW7W6X=7W9W8W?W<X58X:1o"). Qed.

(* [comment removed for export] *)
Lemma errno_lit : bv_unsigned (Z_to_bv 64 RATP) + -164 = RERRNO.
Proof.
  unfold RATP, RERRNO. rewrite unsigned_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rheap_pres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) ->
  rheap_pres LB SP m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_kit ()) ["CANSEC1"] "h04__x1h11ah22Hah32Hch42Hvh52LBh62MUh73OUTh82SPh91Wh:2WMh;7__arithh<4__ffh=8__varmaph>5__with?1mh@2m'hA1zp;1p;3p;2p;4p;7p;8p;6g00YDR0p4p70R1p100>?p4p710p8P1p100>Vp4p710p8P1p10000p4p710p8P1g00?mR2p4p710p8P1p100@Kp4p710p8P1p1004ep4p710p8g00Fij13Tg00BGj10Tg00D[j14Tg00ZBj1@Tg00Zej1YTg00[Gj3VTg00\;j3UTg00Mdj2;Tg00Aij16Tg00N@j2GTg00N]j2ATg00O9j29Tg00\oj3<Tg00^4j22Tg00^jj1BTg00Cgj31Tg00_Yj3=Tg00`Vj1>Tg00a8j1?Tg00E9j2TTg00E_j27Tg00FIj1QTg00aQj2MTg00Ggj1LTg00HEj1KTg00I0j25Tg00aoj2HTg00ISj4:Tg00J>j3ITg00Jaj7JTg00bRj8FTg00KEj2ETg00DAj2NTg00Kgj2DTg00LSj3OTg00M2j4PTg00OTj2CTP2j6RTg00c6j4STg00cQj4XTg00PPj7WTf1R2g00Q4R1g00QSR3P3g00R3R4f0R5g00RSFWp=8%30g00S3R0g00dT#3g00SQR6#0R7#0#0R8#0#0#0R9#4R:#@%48#@R8#YR;[R<f2R=?V25g00<5R>?U=2g00TbR?/;5%67R7%69'GR9,A5'9R@f8RAf7RB;<212B=[[^10f9RC?<A2f6RD%B=REO1PBPEO151;A=>BE%>8R851;#?RFf3RG#BRH9=>B=1;8#?[f5R8PEP0P=12C5XA0PGP=P2P5O31T:=,7:g00T6RC#Q%3C1M02%L0%K0RCP1P3P3P4PCP1P3P3P4P0150?g00U@1H06R6C:,8CP0P6g00Ug1507=I0:C:,8CFJR7%>3P7GF1EC4P5P=g00VNRCg00VnR4'N1D5==1C4dAO0?2CPb<b=b>X001;?21A29'9\@^00P5PGP=O2b;,C=ER17:E,2AeO2P8PHP5O2X4FCSW3X2@X10PBPDf4PGCXeW7W:W6X@<W?W9W8W5o"). Qed.

(* [comment removed for export] *)
Lemma RHEAP_stack_frame : forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv => ATOP <= fst iv) W -> RHEAP s LB m'.
Proof.
  intros s LB m m' W HP MU WM FW.
  eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
  eapply Forall_impl; [| exact FW]. intros iv H. unfold rclient_write_ok. left. exact H.
Qed.

Lemma rauxv_ok_stack_frame : forall m m' B W,
  rauxv_ok m B -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv => ATOP <= fst iv /\ snd iv <= B) W -> rauxv_ok m' B.
Proof.
  intros m m' B W AU MU WM FW.
  eapply rauxv_ok_frame; [exact AU| exact MU| exact WM|].
  eapply Forall_impl; [| exact FW]. intros iv [H1 H2]. split; [exact H2|]. right. unfold RAUXV_CELL. lia.
Qed.

(* [comment removed for export] *)
Lemma RHEAP_disjoint_head : forall s p P n LB m b,
  RHEAP s ((p, P, n) :: LB) m -> In b LB -> P + n <= blk_addr b \/ blk_addr b + blk_size b <= P.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_kit ()) ["CANSEC1"] "p'0h01Hh12H0h21li001lh33ND'h42NIh51xi011xh61eh71Ah81Bh91bi021bh:1fh;1ph<1yh=1Dh>1Eh?2H1h@2HPhA2HbhB2LBhC2NDhD1PhE1mhF1nhG1sp;2p;1p;4p;3p;5p;9p;6g0063j2FTg00FiR0j1?Tg00:Nj47Tg0186j3;Tg00eFj4PTg00i>j30Tg01=ij5NTg00@hR1j2:Tg00Cgj31Tg00DAj2<Tg00l1j3GTg01?;j3RTg01?Ul9QTg01@jR2j15Tg00a8j16Tg00iUj1ETg00jVj1DTg00CJj2CTg00Mdj2BTg00hdj2MTg00FIj1LTg000Mj6KTg01Aij2JTg00?Pj6ATg00>Vj48Tg00O9R3j2=Tg00kWj2@Tg01BHj5ITg00c6j4HTg01Bgj4OTg00?mj6>Tg00=FR4g00S3R5f1R6f0R7C7p=9g00YDR8P4P2P7C8p=2A1467p=4A;467p=3g00n61F45R9/F5R:#?g00nop,2rcR;f6R<P9P5f5R=f4R>'9f3R?C7f2R@5;:P6CPA0:6?P;f8RAP9P5f7RB/9<P=C7=;:>RCP?P6DN%2C,:4P;f9R;P9P519ABP<C7RC=;:=P>PCP?P@A18CCA08C=1<8C3GA18C?A08?=;R6M9Q%5C%5?'4#6P9P519;APBC7R9#ERC%D9'C%E>R9'B%D>,C9/BC'M[P7P1P4%?4R1f;RC%2A'3R9716f<%5B'4#6RD[P6%L4RE%2<,3;RF511f:RG%2B'3RH911EP1PEP0P4p-0P7g01CAg01C]REn10110000020020000000X61g00<jP9P7EKPE1JD7b1W0P7O1W0A0467#61:46RD13?@fAREf>#2'351113>?fBf?#2'3511P1P1P0P4P1P7P=P7n10110000020020102100X6113=>fCf@#2R9'3P7EAA11>9P1P4P0P4P4P7PBP6n10110000020020102100X6113<=fDR0%2E'3P6EA14<0fERE,4BP7fFRB,4AP4fGR9%2E911;REA046G#61:4CfKRI%5B'4RJ#6RK]3]4[X94%20911AP7PEP1%2BREfJRA=047#6fLR0%59RL'4#6^3D]4X21fIRD=04E#6%29,:4P@P4PL%2A9047X;4g004eRLp4p710R9PLp4p7210RLP6\6RE%?@RMP3P>P?P@P6C890?7P>P7O1=1=@A0<7?'=X5=,@=R3[P?P7O1=1>6A0=7@'=X5>,@>P=P>P?P@C890>6[RNP<P=P>P?C890=@\3P>P?P@P6P7DIP7n2001000000120000000X<@W2W:W8W7PN^<@^2M^:E^8L^79P7P8P4P2PAfHR2#5R9P8%57%5D'4A087I'=X58P21499A082A1<49PBCHCOO6b0P0P7E>O1X>JPKeW3W4PGP7E>b?W1P;P7E>b1W0P7O1b1P7O1b1W0P7P@P6O3W0W3W4X21X54P?P@P6P7O4n10210000000020041101100000000A117H%5<,4C#6[X21PFO1P71<1HO1b0O1b=bCWAW@X9:WEWBXF5XD5X;4WGo"). Qed.

Lemma blocks_distinct_disjoint : forall s LBX LB m b b',
  RHEAP s (LBX ++ LB) m -> In b LBX -> In b' LB ->
  blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_kit ()) ["CANSEC1"] "p'0h01Hh12NDh21lh32l2h41Ah52HPh63Hb'h72l1h81xi001xh91Bh:2LBh;1ah<1bh=1fh>2l'h?1yh@1EhA2HbhB3LBXhC2b'hD1ehE1mhF1sp;1p;4p;5p;6p;3p;2p;9p;:g00Fij1<Tg00eFj4?Tg01=ij5TTg000Mj6>Tg00@Kj39Tg00i>j31Tg00hdj2CTg01D:j4STg00l1j3BTg01?;j3RTg01@jR0j13Tg00Cgj34Tg01DYj4OTg00kWR1j2;Tg0186j3ATg01E6j4KTg01ETj5JTg00a8j1DTg00>Vj4=Tg00O9R2j2@Tg01BHj5ITg00DAj2LTg00c6j4HTg01Bgj4GTg00?ml9NTg01?Ul:FTg00@hj2PTg01F7j5QTg00YDR3f1R4f0R539p=8A1345p=5P3g00=FR6P0P5C=p=01P65p=6A9645p=2P3P6P0P4P5DQp=Ef2R7AA345593p=7AA345p=MA1645p=:g00n6%<3R8g00nop,2rcR9f5R:f4R;f3R<'8P7C?157:R=P9f8R>f7R?f6R@'8RAP:P7DT%0A#6%<6RA18>?#0%65X2ARBP5%0>RC%0?'2RD1E>?E>%6DP9f:RDf9RE/8>P?P@P:P;g0000p4p710RF%<5RG%<4RHP2A9<7491<5A1;4<A1;47'CRI[A1<57A1<54'CA9;<791;4[RJA9:;<91:7\IP<P7P4P5CSP5n2001000000120000000X;7W>W2W4RIPJ^;7^>H^2G^4FRFP5P3PDPEP?15?D15?E;B;O5b0PIPFP5P3PDPEP@15@D15@E;R<O5b0%3@%3:546RGP3P@PEP<COf;RHA74>5548X38,;8X78,;8P1P8f<RJA74E5548X38,;8X78g01C]RKP5f>RLA74H5548X38,;8P1P8f?R1A77J5548X38PKP5fARHA7;L5548P8A7:14R1P9fERMfDRN/85fBROC?15H4fFRP#0RQ%07'2#6PK]1]6]5X:8P9PNfCR9/81PHC?f@R1A7@17'5%0MA7?H<#0'2#6PA1MO;R?,8>#0fGRM#0R1/25#6X2AP5%0?,2CRK1E>?E>12QK#6PA%0ERE%39%0:5A6R9'2,21PBP5121E/29RBP6P1PEP9CKE>%6BP6fHRB#0%0D'2R9%0@RE%3NRNP5DJ129E,:N#DP5PIPFP5P6fJRN#0%0J'2REPC%3PR91:9E1:9CPIPFP5P6fK#0RFf=#0RI%3MRM1:MF1:MIP6%3BfLRB#0,:5X<6g004eRIp4p710RFPIp4p7210RIP4\4R9%<7RCP2P;P<P7P4C=91<5P;P5O1=4:7A1@5<'@X8:,;:R2[P<P5O1=4;4A1:57'@X8;,;;P:P;P<P7C=91;4[REP@P:P;P<C=91:7\2P;P<P7P4P5DIP5n2001000000120000000X?7W2W=W9W4PE^?7^2C^=9^9I^4FP5P3P6P0PBfIR0#3RFP3%35%3N546fM,55'@X83P0A46FF150B1L6FPPCHCGO6b0PMPHE>3BO5b03BO5b0O1b1b1b1W1W6W5POP5PLPJPDM9NW0X38P4P5O2n2001000000121100000W0X78P4P5O2n2001000000121100000bDW@%DGeM:Fb1b1X6=WAW5XC3X<3WEX:8WBWFo"). Qed.

Lemma outside_of_forall : forall W x, (forall iv, In iv W -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_kit ()) ["CANSEC1"] "p'0h02ivh11xh21Wh31Hh43Hivh52IHh61ah72hih81lh92loi001pi011zp;2p;1p;3p;4p;5g0063R0j2BTg00Fij1ATg00i>j30Tg002_j3:Tg00Mdj26Tg007Kj3;Tg00N]j24Tg00O9j23Tg00a8j15Tg00^4j21Tg00FIj19Tg0186j32Tg00:Nj47Tg00Cgj38Tg00DAj2@Tg00l1j3?Tg01?;j3<Tg00c6j4=Tg01FSj5>Tg00S3R1/B1R2#AR3P2f0R4f2R5502f1R69:11/65A;116,45'3#5R7[^021156[^11R8X23%92R99024P7[^02g00<j1196eW3X11P0P1P1f4R0f3R9522R:9024P7[^0211:6[^11\8^83P4P1P1f5R:P0C7R;=229R<9024P7[^0216:61460'3#51196P4P;A82;;A02;91@2;3?O2P5P6A0240P5P6P1P1f7f6C7=826A026:;<4O2W4X02O2C=11<6eW3X11X58X23X71X91P6P4O2n2001100000120101101X62P4D>W2o"). Qed.

Lemma disjoint_from_of_forall : forall W a n, (forall iv, In iv W -> a + n <= fst iv \/ snd iv <= a) -> disjoint_from W a n.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_kit ()) ["CANSEC1"] "p'0h01ah12ivh21nh31Wh41Hh53Hivh62IHh72hih81lh92loi001pi011zp;2p;1p;3p;4p;5g0063R0j2ATg00Fij1@Tg00i>j30Tg00CJj23Tg002_j3?Tg00Mdj22Tg007Kj39Tg00hdj24Tg01G5j31Tg00FIj18Tg0186j36Tg00:Nj45Tg00Cgj37Tg00DAj2>Tg00l1j3<Tg01?;j3;Tg00c6j4:Tg01FSj5=Tg00S3R1/A1R2#@R3P2f0R4f3R5502f2R6,35f1R79?11'2A9117/25'4R8[^12A1567[^21^01R9X33%82R:9024P8[^12g00<jA1:67eW4X21X01P0P1P1f5R0f4R:562R;9024P8[^12A1;67[^21^01\9^83P4P1P1f6R;P0C5R<=62:R=9024P8[^121367/2;1206'4A1:67P4P<A72<<A02<:1>2<3<O2P5P6P7A0240P6P7P1P1f8f7C5=727A027;;;4O2W5X12O3C:A1=67eW4X21X01X69X33X71X91P7P4O2n2001100000120101101X02P4D=W3o"). Qed.

(* [comment removed for export] *)
Definition fh_fp_ok (LBX : list block) (SPC : Z) (iv : Z * Z) : Prop :=
  (ATOP <= fst iv /\ snd iv <= SPC)
  \/ (exists b, In b LBX /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Lemma fh_transport : forall s LBX LB m m' W AB SPC,
  RHEAP s (LBX ++ LB) m -> munch W m m' -> wmono usegs m m' ->
  Forall (fh_fp_ok LBX SPC) W -> ATOP <= SPC <= AB ->
  RHEAP s (LBX ++ LB) m'
  /\ (rauxv_ok m AB -> rauxv_ok m' AB)
  /\ (forall errv, rw_cells usegs m RERRNO [C4 errv] -> rw_cells usegs m' RERRNO [C4 errv])
  /\ rheap_pres LB SPC m m'.
Proof.
  intros s LBX LB m m' W AB SPC HP MU WM FW [SA SB].
  assert (BR : forall b, In b LBX -> rblock_range (blk_addr b) (blk_size b)).
  { intros b Hb. eapply RMalloc_ifaceP.RHEAP_block_range_proof; [exact HP| apply in_or_app; left; exact Hb]. }
  pose proof FW as FW'. rewrite Forall_forall in FW'.
  split; [| split; [| split]].
  - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros iv [[H1 H2]|(b & Hb & H1 & H2)]; unfold rclient_write_ok.
    + left. exact H1.
    + right. right. exists b. split; [apply in_or_app; left; exact Hb| lia].
  - intros AU. eapply rauxv_ok_frame; [exact AU| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros iv [[H1 H2]|(b & Hb & H1 & H2)].
    + split; [lia| right; unfold RAUXV_CELL; lia].
    + destruct (BR b Hb) as (B1 & B2 & B3 & B4 & B5). unfold RAUXV_CELL. lia.
  - intros errv EC. eapply rw_cells_transport; [exact EC| exact MU| exact WM|].
    apply disjoint_from_of_forall. intros iv HI.
    destruct (FW' iv HI) as [[H1 H2]|(b & Hb & H1 & H2)].
    + unfold RERRNO. cbn. lia.
    + destruct (BR b Hb) as (B1 & B2 & B3 & B4 & B5). unfold RERRNO. cbn. lia.
  - apply (rheap_pres_of_munch LB SPC W m m' MU WM). intros a Ha HC.
    apply outside_of_forall. intros iv HI.
    destruct (FW' iv HI) as [[H1 H2]|(b & Hb & H1 & H2)].
    + unfold rclient_addr in HC. destruct HC as [HC|[[HC1 HC2]|(b' & Hb' & HB')]].
      * lia.
      * lia.
      * pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ b' HP ltac:(apply in_or_app; right; exact Hb'))
          as (C1 & C2 & C3 & C4 & C5). lia.
    + destruct (BR b Hb) as (B1 & B2 & B3 & B4 & B5).
      unfold rclient_addr in HC. destruct HC as [HC|[[HC1 HC2]|(b' & Hb' & HB')]].
      * lia.
      * lia.
      * pose proof (blocks_distinct_disjoint s LBX LB m b b' HP Hb Hb') as DJ. lia.
Qed.

End CANSEC1.
