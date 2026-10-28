(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PiStmt LbB_PiExit LbB_RwKit LbB_PiInit LbB_HStKit LbB_DKit LbB_HKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PmLH () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List2InI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbI6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4pmwA00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4prod00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PmCut9regs_tblXc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH7rt_subbC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC46Stdlib5Lists4List=Forall_forallC47Corelib7Classes9MorphismsDiff_impl_subrelationc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH7rt_membC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28expr_eqbC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions5bv_eqC5ARocqVerifyHarness?AgentSubmission8SymExec33SX2=expr_eqb_trueC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase9wenv_valsC47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes3sndC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotK47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00I47Corelib7Numbers7BinNums1Z00I6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil8HeapCeil00I6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3asr00K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationI47Corelib7Numbers7BinNums1N00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH;lexit_stmtAc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH:body_stmtAC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_StC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase4wa_nC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase6c_widxC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_nati6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH3LIA00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5as_SRC47Corelib4Init5Peano2ltC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00K47Corelib4Init9Datatypes4list01c6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH4la_xC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase7xa_scalC56Stdlib6ZArith6BinInt1Z2leC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_icountC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase8c_endianK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase9c_reqconvI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init2WfFwell_founded_inductionC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C46Stdlib5Arith6Wf_nat5lt_wfC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface5blockC4ARocqVerifyHarness?AgentSubmission8LibIface3memI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I5ARocqVerifyHarness?AgentSubmission6LibPrs6PmBase3pmc00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PmBase8S_MODULEc6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PmLH9TBL_EE648I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op204".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition RT_EE648 : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, ELit SHBASE); (20%bv, SH_FF);
   (22%bv, ELit 18446744073709551608); (24%bv, WADD WV_P 80); (26%bv, WADD WV_FF 10416); (27%bv, WADD WV_FF 10496)].

Definition TBL_EE648 : list (Z * expr) :=
  [(1056, EVar 33); (968, EVar 33); (1040, EVar 33);
   (1048, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880));
   (1000, EAlu ALU_ADD (EVar 32) (ELit 48));
   (1008, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880));
   (936, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880));
   (944, EAlu ALU_ADD (EVar 32) (ELit 56)); (960, EAlu ALU_ADD (EVar 33) (ELit 11488));
   (712, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 92)) (ELit 3)) (ELit 2147450880));
   (632, EAlu ALU_ADD (EVar 32) (ELit 92)); (848, EAlu ALU_ADD (EVar 32) (ELit 88)); (800, EAlu ALU_ADD (EVar 33) (ELit 10512));
   (976, ELit 2147450880); (720, EAlu ALU_ADD (EVar 33) (ELit 10496)); (784, EAlu ALU_ADD (EVar 33) (ELit 10416)); (808, EVar 32);
   (792, EAlu ALU_ADD (EVar 32) (ELit 80)); (344, EAlu ALU_ADD (EVar 33) (ELit 10432)); (440, EAlu ALU_ADD (EVar 33) (ELit 10436));
   (216, EAlu ALU_ADD (EVar 33) (ELit 6737)); (488, EAlu ALU_ADD (EVar 33) (ELit 6736)); (888, EAlu ALU_ADD (EVar 33) (ELit 10426));
   (648, EAlu ALU_ADD (EVar 33) (ELit 11024)); (520, EAlu ALU_ADD (EVar 33) (ELit 9312)); (728, EAlu ALU_ADD (EVar 33) (ELit 10992));
   (704, EAlu ALU_ADD (EVar 33) (ELit 10528)); (688, EAlu ALU_ADD (EVar 33) (ELit 10352)); (736, EAlu ALU_ADD (EVar 33) (ELit 10288));
   (640, EAlu ALU_ADD (EVar 33) (ELit 10224)); (608, EAlu ALU_ADD (EVar 33) (ELit 10160)); (680, EAlu ALU_ADD (EVar 33) (ELit 10096));
   (592, EAlu ALU_ADD (EVar 33) (ELit 10032)); (528, EAlu ALU_ADD (EVar 33) (ELit 9968)); (496, EAlu ALU_ADD (EVar 33) (ELit 9904));
   (504, EAlu ALU_ADD (EVar 33) (ELit 9840)); (296, EAlu ALU_ADD (EVar 33) (ELit 9376)); (392, EAlu ALU_ADD (EVar 33) (ELit 9344));
   (776, EAlu ALU_ADD (EVar 33) (ELit 9280)); (128, EAlu ALU_ADD (EVar 33) (ELit 7264)); (536, EAlu ALU_ADD (EVar 33) (ELit 8816));
   (584, EAlu ALU_ADD (EVar 33) (ELit 8784)); (144, EAlu ALU_ADD (EVar 33) (ELit 8752)); (232, EAlu ALU_ADD (EVar 33) (ELit 8288));
   (304, EAlu ALU_ADD (EVar 33) (ELit 8256)); (576, EAlu ALU_ADD (EVar 33) (ELit 8224)); (696, EAlu ALU_ADD (EVar 33) (ELit 7760));
   (672, EAlu ALU_ADD (EVar 33) (ELit 7728)); (112, EAlu ALU_ADD (EVar 33) (ELit 6800)); (136, EAlu ALU_ADD (EVar 33) (ELit 4816));
   (24, EAlu ALU_ADD (EVar 33) (ELit 6272)); (72, EAlu ALU_ADD (EVar 33) (ELit 5808)); (224, EAlu ALU_ADD (EVar 33) (ELit 5344));
   (32, EAlu ALU_ADD (EVar 33) (ELit 5312)); (48, EAlu ALU_ADD (EVar 33) (ELit 4848)); (256, EAlu ALU_ADD (EVar 33) (ELit 4352));
   (248, EAlu ALU_ADD (EVar 33) (ELit 2400)); (184, EAlu ALU_ADD (EVar 33) (ELit 4336)); (56, EAlu ALU_ADD (EVar 33) (ELit 3872));
   (152, EAlu ALU_ADD (EVar 33) (ELit 3840)); (64, EAlu ALU_ADD (EVar 33) (ELit 3824)); (320, EAlu ALU_ADD (EVar 33) (ELit 3792));
   (240, EAlu ALU_ADD (EVar 33) (ELit 3328)); (40, EAlu ALU_ADD (EVar 33) (ELit 2864)); (360, EAlu ALU_ADD (EVar 32) (ELit 32));
   (336, EAlu ALU_ADD (EVar 32) (ELit 152)); (312, EAlu ALU_ADD (EVar 32) (ELit 168)); (400, EAlu ALU_ADD (EVar 32) (ELit 160));
   (384, EAlu ALU_ADD (EVar 32) (ELit 144)); (448, EAlu ALU_ADD (EVar 32) (ELit 136)); (352, EAlu ALU_ADD (EVar 32) (ELit 96));
   (208, EAlu ALU_ADD (EVar 32) (ELit 176)); (600, EAlu ALU_ADD (EVar 32) (ELit 93)); (544, EAlu ALU_ADD (EVar 32) (ELit 280));
   (864, EAlu ALU_ADD (EVar 32) (ELit 272)); (952, EAlu ALU_ADD (EVar 32) (ELit 264)); (872, EAlu ALU_ADD (EVar 32) (ELit 8));
   (752, EAlu ALU_ADD (EVar 32) (ELit 40)); (856, EAlu ALU_ADD (EVar 32) (ELit 232)); (896, EAlu ALU_ADD (EVar 32) (ELit 224));
   (768, EAlu ALU_ADD (EVar 32) (ELit 216)); (992, EAlu ALU_ADD (EVar 32) (ELit 256)); (928, EAlu ALU_ADD (EVar 32) (ELit 248));
   (920, EAlu ALU_ADD (EVar 32) (ELit 240)); (432, EAlu ALU_ADD (EVar 33) (ELit 12480)); (424, EAlu ALU_ADD (EVar 33) (ELit 12016));
   (552, EAlu ALU_ADD (EVar 33) (ELit 11552)); (568, EAlu ALU_ADD (EVar 33) (ELit 11520)); (176, EAlu ALU_ADD (EVar 33) (ELit 1936));
   (160, EAlu ALU_ADD (EVar 33) (ELit 1472)); (168, EAlu ALU_ADD (EVar 33) (ELit 1008)); (912, EAlu ALU_ADD (EVar 33) (ELit 944));
   (80, EAlu ALU_ADD (EVar 33) (ELit 928)); (96, EAlu ALU_ADD (EVar 33) (ELit 896)); (88, EAlu ALU_ADD (EVar 33) (ELit 880));
   (264, ELit 16843009); (272, ELit 252645135); (280, ELit 858993459); (288, ELit 1431655765); (368, ELit 18446744072850558157);
   (120, ELit 65535); (200, ELit 262140); (104, EAlu ALU_ADD (EVar 33) (ELit 848)); (656, EAlu ALU_ADD (EVar 33) (ELit 784));
   (616, EAlu ALU_ADD (EVar 33) (ELit 720)); (624, EAlu ALU_ADD (EVar 33) (ELit 656)); (512, EAlu ALU_ADD (EVar 33) (ELit 592));
   (464, EAlu ALU_ADD (EVar 33) (ELit 528)); (472, EAlu ALU_ADD (EVar 33) (ELit 464)); (984, EAlu ALU_ADD (EVar 33) (ELit 448));
   (408, EAlu ALU_ADD (EVar 33) (ELit 384)); (456, EAlu ALU_ADD (EVar 33) (ELit 320)); (328, EAlu ALU_ADD (EVar 33) (ELit 256));
   (416, EAlu ALU_ADD (EVar 33) (ELit 192)); (480, EAlu ALU_ADD (EVar 33) (ELit 128)); (376, EAlu ALU_ADD (EVar 33) (ELit 64));
   (192, EAlu ALU_ADD (EVar 33) (ELit 32));
   (1016, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880));
   (1024, EAlu ALU_ADD (EVar 32) (ELit 72)); (560, EAlu ALU_ADD (EVar 32) (ELit 16))].

Definition rt_memb (re : reg * expr) (RT : list (reg * expr)) : bool :=
  existsb (fun re' => (bv_eqb (fst re) (fst re') && expr_eqb (snd re) (snd re'))%bool) RT.
Definition rt_subb (RT' RT : list (reg * expr)) : bool := forallb (fun re => rt_memb re RT) RT'.
Lemma regs_tbl_sub {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X R RT RT',
  regs_tblX w X R RT -> rt_subb RT' RT = true -> regs_tblX w X R RT'.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PmLH ()) [] "p'0h01xi001xh12reh23Hinh32K1h42K2h52H0h61Kh72b1h82b2h91nh:4Hin'h;1Ah<1Hh=5HCEILh>2HTh?1ei011eh@1fhA1lhB5lemmahC1mhD1rhE3re'hF2HshG1RhH2RThI3RT'hJ1XhK2e'hL2r'hM1whN1yi021bi031pp;1p;2p;6p;3p;7p;4p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g001:R1p4p710p9P0g001\R2p4p710p8P0g0023R3p4p710p8P0g002TR4p4p710p8P0P4p4p7210p8P0g0031R0p4p710R5p8g003Mj1dTg004Kj1>Tg0050j1HTg005Nj1<Tg0061j1DTg006Qj1[Tg0076j2XTg007bR6j2UTg008Bj6FTg009Bj2PTg00:?j2MTP3j3BTP2j33Tg00;1R2j2KTg00;Jj2WTP1j7VTg00;hj3JTg00<Jj3TTg00=;j2@Tg00>8j3GTg00>Tj3RTg00?7j6QTP0j3ITg00?RR0j2ATg00?lj3OTg00@Oj38Tg00A<j29Tg00B6j2;Tg00BTR1j2CTg00Boj2NTg00CPj2ETg00Cmj2STg00DMj2?Tg00E7j34Tg00EQj3cTg00F5j3bTg00G4j7LTP4j3aTg00GRj2`Tg00HSj3_Tg00I0j3\Tg00IMj2ZTg00J?j2]Tg00K6j2^Tg00Knj4YTg00LNR4f0R3g00LnR734p=2f1R8g00MNR9;a3p=1f3R:f2R;/`8;_3p=6A\893p=0f5R<f4R=/Z:1];8/^334p=7A4437,C8p=:g00NFR7?483p==P;P9P8P3CYp=5g00NdR>g00OcR?%d3g00P\#>R@#>#>#>#>#>#H#<RA#D%[@#HR@/XA%<@RB/U9RC#DRDf6REP<P=P:P;P8EF1P8;#2PAP<11B3RF1M@ARGPAf8RHf7RIPEC610B3RJE7X1CRK=BC;A3C3:PAPIPFPGPAf:RLf9RMPHC6PJE7X1CP8O1RN[^0C'Kp-0ROP21W38XNOX0Og00QAPAPEPFPGPAPMPHPIC6PJE7X1CRO=BC:A3C3=R2PAPHPFPGPAf;RPPLPMC6PJE7X1CP8O1RQ[^0CP3FVWBAJCK;ABCK:PN\2^0CRN'KABCO=A3C3<PQ[^0C;T3WBAJCK:P8O2PN1@3IX1CRN=GC<#2A3C3I1@3LX1CP8O1#2[^0C[A3C3E1@3MX1CP8O1#2[^0C1@3HX1C=GCE#2[ARCN<P:P8P3EQPNP8O1#2P4\3RN%D8RKP1AI;83#2A3=3;P:P3O1':X0:,A:[RQA3:38P;P3O1':X0;,A;AI:;8#2RO[A3<3:P=P3O1':X0=,A=\OAO;83P8n2001000000120000000WAW@X;5PQ^AK^@N^;5P3PC11B=R5=8@F10B=RN/9J';RKXECPHP8O4A3C3M/:KX0C,ACP0PCA3C3L11B<R0=8@F10B<RK/9J';':X0CPAPPP0PGPAf>R0f=RQf<ROC6PKE7P3A3C3O11BIRK=8@F10BIRF/9J';':P1A3C8Q11BH11B8RJ58@10BH10B8'9';#2PAf?RR11BMRSPGPAfBRTfARUf@RVC610BME7P3A3C:R11BP=8@510BP/9N';#2P11;83#2%2;RN%28R5'C[RW1:531;;8#2R5[%2:/CN\51N83P8n2001000000120000000X84X74PW^84^74P311BQ11BE58@R410BQ10BE'9RQP8O3%24/:QP111B0RQ=8@K#210B0/9F#2PAfERF11BRPGPAfHfGR0fFRKC610BRRRE7P311BV=8@S#210BU10BL'9#2P11E83#21=;8[RU1=831E;8#2RS[1=:;\S1S83P8n2001000000120000000XC7X97PU^C7^97P3fCR7,1B,?@RU11BO,?@RSP;O31=USg00R7RS%<3RU%<8RVP1%<;?4831?:;1?:8'=R1[1?;81?;3'=%<:?4;8[R4%<=?4:;\1Ac;83P3n2001000000120000000W8W7W9P4^8V^7U^9SP3P@11BFRFPQP8O4A4BFQ10BKRQ?bR=A49QRP6PBP9fL93C311BT94BJ10B;RT10B7549PAfQ11B:PGPAfTRRfSfRC610B:E7]4]3]2P0A5B83R@fO53CA5B;8,1BRS=4BFA5B:;,0BR:=49QP6PBP9A3C3RA5BE<RR,1B=4BJA5BIE,0B=49TPAfXRTA5BHIRJ,1BPGPAf[R6fZRQfYRFC610BJE7]4]3]:P0fW93C@A5BMH,1B=4BSA5BLM,0B=49:PBP=A5B3P=3CQPAf]R:P8PGPAf`RSf_R@f^R0C6POE7]2XDBA5B=L=3CFP9P=A5BE3=3C6PAP0PIPGPAfaPSP@C6P8E7]2X?9A5B<==3CQPTPRP=O2W2PPP8P3FLW2PPP8PMFLPAP6A5BPLRP,1BPGPAP0P:f\C610BPE7eW4W3W:XK9XLBP8P3O2n2001103000121102101P7P8P3O3W4W3W2X?9XDBP8P3O2n2001103000121102101PKP8P3O3b4b3b5b3b5W4W3P8P3O2n2001000000121000000b6b5W6W:P8P3O2n2001000000121000000W5XECP8P3O2n2001000000121100000b6b5b6X22X1Cb>O2PHPIPEP<P=P;EFeWFW>XIDWHWGWJWMX<?X=>P8P3O2W<W=o"). Qed.

Definition nodesA (c : pmc) : Z := Zlen (t3c (c_m1 c)) + Zlen (t3c (c_m2 c)) + Zlen (t3c (c_m3 c)).
Definition m3okA (ents : list (Z * (Z * Z))) : Prop := Forall (fun e => 0 <= snd (snd e) < 2 ^ 31) ents.
Definition macctA (c : pmc) : Prop :=
  8 * t3b (c_m1 c) <= 16 * Zlen (t3c (c_m1 c)) + 504 /\ 8 * t3b (c_m2 c) <= 16 * Zlen (t3c (c_m2 c)) + 504 /\
  8 * t3b (c_m3 c) <= 16 * Zlen (t3c (c_m3 c)) + 504 /\ m3okA (t3c (c_m3 c)).
Definition laccA (c : pmc) : Prop :=
  2 * Zlen (t3c (c_m1 c)) <= c_widx c /\ 2 * Zlen (t3c (c_m2 c)) <= c_widx c /\ 3 * Zlen (t3c (c_m3 c)) <= c_widx c.

Definition BP_INIT : Z := 0xec0b4.
Definition BP_HEAD : Z := 0xec0bc.
Definition BP_RA : Z := 0xec0d0.
Definition BP_EXIT : Z := 0xec0e0.

Definition st5 (st : stateC) : stateC :=
  {| st_words := st_words st; st_nwords := st_nwords st; st_diag := st_diag st; st_widx := 5;
     st_icount := st_icount st; st_endian := st_endian st; st_flags := st_flags st;
     st_m1 := st_m1 st; st_m2 := st_m2 st; st_m3 := st_m3 st; st_v1 := st_v1 st; st_v2 := st_v2 st; st_v3 := st_v3 st |}.
Definition pc5 (c : parserC) : parserC := {| pc_cons := pc_cons c; pc_user := pc_user c; pc_state := st5 (pc_state c) |}.

Section BPLoop.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis PI : parse_inst_stmtB H LINV.
  Lemma HHl : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Variable w : piw H.
  Variable LF : list fframe.
  Variable CH : list (Z * Z).
  Variables sp gp tp s0 s1 s3 s4 s5 s6 s7 s9 s10 s11 : word.
  Variable FR : mem -> Prop.
  Hypothesis FR_keep : forall m m' XS, FR m -> Forall (fs_scratch H LF) XS ->
    xpres H (pw_LB0 H w) (bv_unsigned sp) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (pw_p H w, pw_p H w + PARSER_SIZE) :: XS) m m' ->
    stk asegs m' (pw_lo H w) (bv_unsigned sp) -> as_RFS H LF m' -> FR m'.
  Hypothesis Htp : tp = Z_to_bv 64 ATP.
  Hypothesis Hsp16 : bv_unsigned sp mod 16 = 0.
  Hypothesis HspB : bv_unsigned sp <= pw_B H w.
  Hypothesis HspS : bv_unsigned sp <= pw_shi H w.
  Hypothesis Hlo1 : aceil <= (pw_lo H w).
  Hypothesis Hlo2 : (pw_lo H w) <= bv_unsigned sp - APM_STACK.
  Hypothesis HLF : (length LF + PM_FRAMES <= AFS_MAXLIVE_BP)%nat.
  Hypothesis HPF : pf_ok (as_TR H) PM_PF BP_RA CH.
  Hypothesis HCH : forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp'.
  Hypothesis HTR : pm_tr_ok H.

  Definition bp_regs (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) : bvmap 5 word :=
    mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

  Definition bp_exit_k (Q : config -> Prop) (mo0 : Model) : Prop :=
    forall s LB LBs m mo msF (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (r : Z),
      as_VIS H s msF = MS (bp_regs ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 r) t3 t4 t5 t6) F (Z_to_bv 64 BP_EXIT) fc None m
                          (seg_rom asegs) ->
      - 2 ^ 31 <= r < 2 ^ 31 -> frm_zero fc ->
      as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
      (exists c', pi_err H LINV w s LB LBs m c') -> piw_ok H w LF m -> FR m ->
      stk asegs m (pw_lo H w) (bv_unsigned sp) -> as_RFS H LF m -> as_chain H m (bv_unsigned s0) CH ->
      as_SR H Q (mkCfg msF mo).

  Definition bp_head_at (Q : config -> Prop) (mo0 : Model) (c : pmc) : Prop :=
    forall s LB LBs m mo msF (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) F fc,
      as_VIS H s msF = MS (bp_regs ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6) F (Z_to_bv 64 BP_HEAD) fc None m
                          (seg_rom asegs) ->
      frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
      PIX H LINV w s LB LBs m c -> piw_ok H w LF m -> FR m ->
      stk asegs m (pw_lo H w) (bv_unsigned sp) -> as_RFS H LF m -> as_chain H m (bv_unsigned s0) CH ->
      as_SR H Q (mkCfg msF mo).

  Lemma bp_exit_step : forall Q mo0 c, bp_exit_k Q mo0 -> pw_n H w <= c_widx c -> bp_head_at Q mo0 c.
  Proof.
    intros Q mo0 c K Hn s LB LBs m mo msF ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 F fc
           VIS FZ KR MP X K0 FRm STK RFS CHN.
    pose proof (pk_papp _ _ _ _ K0) as (PA & PA0 & PA16).
    pose proof (aapp_below_aceil _ _ PA) as PR2.
    pose proof (aapp_bounds _ _ PA ltac:(unfold PARSER_SIZE; lia)) as (AB1 & AB2 & AB3 & AB4 & AB5).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (px_scal _ _ _ _ _ _ _ _ X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (pk_n _ _ _ _ K0) as Hn24.
    unfold bp_regs in VIS.
    set (R := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) in VIS.
    assert (RF : rfull R) by (unfold R; apply rfull_mkR).
    pose (E := Eseed R [Z_to_bv 64 (pw_p H w); Z_to_bv 64 (pw_n H w); Z_to_bv 64 (c_widx c)]).
    assert (HR : regs_ok E (srs sr_id [(18%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      split; [intros Hx; discriminate Hx | reflexivity]. }
    assert (UP : bv_unsigned (edenot E (EVar 32)) = pw_p H w)
      by (change (edenot E (EVar 32)) with (Z_to_bv 64 (pw_p H w)); apply u64_of_Z; unfold AAPP_HI, PARSER_SIZE in *; lia).
    assert (HK : know_ok asegs E m [KWord (SA (EVar 32) 56) 8 (EVar 33); KWord (SA (EVar 32) 72) 8 (EVar 34)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - eapply (kword_of_fld E m (pw_p H w + O_N) 8 (pw_n H w)); [exact (px_n _ _ _ _ _ _ _ _ X) | lia | | | |].
        + unfold estart. cbn [a_base a_off]. rewrite UP. unfold O_N. lia.
        + unfold O_N. lia.
        + unfold O_N, AAPP_HI, PARSER_SIZE in *. lia.
        + reflexivity.
      - eapply (kword_of_fld E m (pw_p H w + O_WIDX) 8 (c_widx c)); [exact (px_widx _ _ _ _ _ _ _ _ X) | lia | | | |].
        + unfold estart. cbn [a_base a_off]. rewrite UP. unfold O_WIDX. lia.
        + unfold O_WIDX. lia.
        + unfold O_WIDX, AAPP_HI, PARSER_SIZE in *. lia.
        + reflexivity. }
    xrun_at (PropExec.mkFP F fc) asegs R BP_HEAD m (seg_rom asegs) HR HK 10%nat [BP_EXIT; APM_ENTRY] (SCR [true] [] []) 35%N.
    { split_scs; cbn [sc_denot].
      - change (edenot E (EVar 34)) with (Z_to_bv 64 (c_widx c)). change (edenot E (EVar 33)) with (Z_to_bv 64 (pw_n H w)).
        rewrite br_geu by lia. apply Bool.negb_true_iff, Z.ltb_ge. lia.
      - unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite UP. change (edenot E (ELit 8)) with (Z_to_bv 64 8).
        rewrite u64_of_Z by lia. unfold AAPP_HI, PARSER_SIZE in *. lia.
      - unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite UP. change (edenot E (ELit 8)) with (Z_to_bv 64 8).
        rewrite u64_of_Z by lia. unfold AAPP_HI, PARSER_SIZE in *. lia. }
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    assert (RF' : rfull R') by exact (msteps_full asegs _ _ Hms RF).
    assert (HRe : R = mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      by reflexivity.
    readback HR' RF' HRe HRB.
    assert (Y24 : getr R' 24%bv = Z_to_bv 64 0) by (rewrite (HR' 24%bv); reflexivity).
    assert (Y18 : getr R' 18%bv = Z_to_bv 64 (pw_p H w)) by (rewrite (HR' 18%bv); reflexivity).
    eapply (ahh_evt_then H HHl (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (getr R' 10%bv) (getr R' 11%bv) a2 a3 a4 a5 a6 a7
                                                     (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 (Z_to_bv 64 0) s9 s10 s11 t3 t4 t5 t6)
                                         F (Z_to_bv 64 BP_EXIT) fc None m (seg_rom asegs)) _ s msF _ mo KR VIS).
    { eapply evt_of_msteps_done; [exact Hms|]. rewrite HRB, Y24, Y18. reflexivity. }
    intros msF1 mo1 KR1 MP1 VIS1.
    destruct (pi_exit H HHbp LINV w LF s LB LBs m c K0 X Hn) as [c' PE].
    eapply (K s LB LBs m mo1 msF1 ra t0 t1 t2 (getr R' 10%bv) (getr R' 11%bv) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc 0);
      [exact VIS1 | lia | exact FZ | exact KR1 | eapply (ah_mpres_trans H HHl); [exact MP | exact MP1]
      | exists c'; exact PE | exact K0 | exact FRm | exact STK | exact RFS | exact CHN].
  Qed.
  Lemma bp_call_step : forall Q mo0 c, bp_exit_k Q mo0 -> c_widx c < pw_n H w ->
    (forall c', c_widx c < c_widx c' -> c_widx c' <= pw_n H w -> bp_head_at Q mo0 c') ->
    bp_head_at Q mo0 c.
  Proof.
    intros Q mo0 c K Hlt IH s LB LBs m mo msF ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 F fc
           VIS FZ KR MP X K0 FRm STK RFS CHN.
    pose proof (pk_papp _ _ _ _ K0) as (PA & PA0 & PA16).
    pose proof (aapp_below_aceil _ _ PA) as PR2.
    pose proof (aapp_bounds _ _ PA ltac:(unfold PARSER_SIZE; lia)) as (AB1 & AB2 & AB3 & AB4 & AB5).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (px_scal _ _ _ _ _ _ _ _ X) as (Sc1 & Sc2 & Sc3 & Sc4).
    pose proof (pk_n _ _ _ _ K0) as Hn24.
    unfold bp_regs in VIS.
    set (R := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) in VIS.
    assert (RF : rfull R) by (unfold R; apply rfull_mkR).
    pose (E := Eseed R [Z_to_bv 64 (pw_p H w); Z_to_bv 64 (pw_n H w); Z_to_bv 64 (c_widx c)]).
    assert (HR : regs_ok E (srs sr_id [(18%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      split; [intros Hx; discriminate Hx | reflexivity]. }
    assert (UP : bv_unsigned (edenot E (EVar 32)) = pw_p H w)
      by (change (edenot E (EVar 32)) with (Z_to_bv 64 (pw_p H w)); apply u64_of_Z; unfold AAPP_HI, PARSER_SIZE in *; lia).
    assert (HK : know_ok asegs E m [KWord (SA (EVar 32) 56) 8 (EVar 33); KWord (SA (EVar 32) 72) 8 (EVar 34)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - eapply (kword_of_fld E m (pw_p H w + O_N) 8 (pw_n H w)); [exact (px_n _ _ _ _ _ _ _ _ X) | lia | | | |].
        + unfold estart. cbn [a_base a_off]. rewrite UP. unfold O_N. lia.
        + unfold O_N. lia.
        + unfold O_N, AAPP_HI, PARSER_SIZE in *. lia.
        + reflexivity.
      - eapply (kword_of_fld E m (pw_p H w + O_WIDX) 8 (c_widx c)); [exact (px_widx _ _ _ _ _ _ _ _ X) | lia | | | |].
        + unfold estart. cbn [a_base a_off]. rewrite UP. unfold O_WIDX. lia.
        + unfold O_WIDX. lia.
        + unfold O_WIDX, AAPP_HI, PARSER_SIZE in *. lia.
        + reflexivity. }
    xrun_at (PropExec.mkFP F fc) asegs R BP_HEAD m (seg_rom asegs) HR HK 10%nat [BP_EXIT; APM_ENTRY] (SCR [false] [] []) 35%N.
    { split_scs; cbn [sc_denot].
      - change (edenot E (EVar 34)) with (Z_to_bv 64 (c_widx c)). change (edenot E (EVar 33)) with (Z_to_bv 64 (pw_n H w)).
        rewrite br_geu by lia. apply Bool.negb_false_iff, Z.ltb_lt. lia.
      - unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite UP. change (edenot E (ELit 8)) with (Z_to_bv 64 8).
        rewrite u64_of_Z by lia. unfold AAPP_HI, PARSER_SIZE in *. lia.
      - unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite UP. change (edenot E (ELit 8)) with (Z_to_bv 64 8).
        rewrite u64_of_Z by lia. unfold AAPP_HI, PARSER_SIZE in *. lia. }
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
    assert (RF' : rfull R') by exact (msteps_full asegs _ _ Hms RF).
    assert (HRe : R = mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      by reflexivity.
    readback HR' RF' HRe HRB.
    assert (Y1 : getr R' 1%bv = Z_to_bv 64 BP_RA) by (rewrite (HR' 1%bv); reflexivity).
    assert (Y10 : getr R' 10%bv = Z_to_bv 64 (pw_p H w)) by (rewrite (HR' 10%bv); reflexivity).
    assert (Y18 : getr R' 18%bv = Z_to_bv 64 (pw_p H w)) by (rewrite (HR' 18%bv); reflexivity).
    eapply (ahh_evt_then H HHl (fun ms => ms = MS (mkR (Z_to_bv 64 BP_RA) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pw_p H w)) (getr R' 11%bv)
                                                     a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                         F (Z_to_bv 64 APM_ENTRY) fc None m (seg_rom asegs)) _ s msF _ mo KR VIS).
    { eapply evt_of_msteps_done; [exact Hms|]. rewrite HRB, Y1, Y10, Y18. reflexivity. }
    intros msF1 mo1 KR1 MP1 VIS1.
    assert (RA2 : bv_unsigned (Z_to_bv 64 BP_RA) mod 2 = 0) by (rewrite u64_of_Z by (unfold BP_RA; lia); reflexivity).
    eapply (ah_seq H HHl).
    { exact (PI (Z_to_bv 64 BP_RA) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pw_p H w)) (getr R' 11%bv) a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF1 m mo1 w s LB LBs LF CH c
               VIS1 FZ eq_refl Htp K0 X Hlt KR1 Hsp16 HspB HspS STK Hlo1 Hlo2 RA2 RFS HLF CHN HPF HCH HTR). }
    intros [msF2 mo2] POST.
    destruct POST as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & s' & LB' & LBs' & XS
                      & F' & fc' & VIS2 & FZ2 & Hr & KR2 & MP2 & STK2 & RFS2 & PK2 & FXS & XP & ALT).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite (ret_pc_even BP_RA ltac:(unfold BP_RA; lia) eq_refl) in VIS2.
    assert (CHN2 : as_chain H m' (bv_unsigned s0) CH).
    { eapply (chain_via_xpres H HHl); [exact CHN | exact XP | exact HCH |].
      intros fp ra' IN. pose proof (ah_chain_range H HHl _ _ _ _ _ CHN IN) as (R1 & R2 & R3).
      apply Forall_cons; [cbn [fst snd]; unfold RtB_Td.ATDLOC, AIMG_TOP in *; lia|].
      apply Forall_cons; [cbn [fst snd]; lia|].
      eapply Forall_impl; [| exact FXS]. intros iv Hiv. pose proof (scratch_below H HHl LF m' iv RFS2 Hiv). cbn beta. lia. }
    assert (FR2 : FR m') by exact (FR_keep m m' XS FRm FXS XP STK2 RFS2).
    assert (MP02 : as_MPRES H mo0 mo2)
      by (eapply (ah_mpres_trans H HHl); [exact MP | eapply (ah_mpres_trans H HHl); [exact MP1 | exact MP2]]).
    rename R' into R1. rename HR' into HR1. rename Hlf into Hlf1. rename Hms into Hms1.
    set (R2 := mkR (Z_to_bv 64 BP_RA) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pw_p H w))
                   s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') in VIS2.
    assert (RF2 : rfull R2) by (unfold R2; apply rfull_mkR).
    pose (E2 := Eseed R2 []).
    assert (HR2 : regs_ok E2 sr_id R2) by apply regs_ok_seed.
    assert (HK2 : know_ok asegs E2 m' []) by apply Forall_nil.
    assert (HRe2 : R2 = mkR (Z_to_bv 64 BP_RA) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pw_p H w))
                            s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') by reflexivity.
    destruct ALT as [(R0 & c' & PX' & Hlt') | (R0 & c' & PE')].
    - subst r.
      xrun_at (PropExec.mkFP F' fc') asegs R2 BP_RA m' (seg_rom asegs) HR2 HK2 5%nat [BP_HEAD; BP_EXIT] (SCR [true] [] []) 32%N.
      { split_scs; cbn [sc_denot]; vm_compute; reflexivity. }
      lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
      assert (RF3 : rfull R') by exact (msteps_full asegs _ _ Hms RF2).
      readback HR' RF3 HRe2 HRB3.
      eapply (ahh_evt_then H HHl (fun ms => ms = MS R2 F' (Z_to_bv 64 BP_HEAD) fc' None m' (seg_rom asegs)) _ s' msF2 _ mo2 KR2 VIS2).
      { eapply evt_of_msteps_done; [exact Hms|]. rewrite HRB3. reflexivity. }
      intros msF3 mo3 KR3 MP3 VIS3.
      pose proof (px_scal _ _ _ _ _ _ _ _ PX') as (Sd1 & _ & _ & _).
      eapply (IH c' Hlt' ltac:(lia) s' LB' LBs' m' mo3 msF3 (Z_to_bv 64 BP_RA) t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                 s8 t3' t4' t5' t6' F' fc');
        [exact VIS3 | exact FZ2 | exact KR3 | eapply (ah_mpres_trans H HHl); [exact MP02 | exact MP3]
        | exact PX' | exact PK2 | exact FR2 | exact STK2 | exact RFS2 | exact CHN2].
    - xrun_at (PropExec.mkFP F' fc') asegs R2 BP_RA m' (seg_rom asegs) HR2 HK2 5%nat [BP_HEAD; BP_EXIT] (SCR [false] [] []) 32%N.
      { split_scs; cbn [sc_denot].
        change (edenot E2 (EVar 10)) with (Z_to_bv 64 r).
        lazymatch goal with |- branch_taken BC_EQ _ ?z = false => replace z with (Z_to_bv 64 0) by (vm_compute; reflexivity) end.
        cbn [branch_taken]. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        apply Z.eqb_neq. intros E0. rewrite Zmod_0_l in E0. apply R0. Z.div_mod_to_equations. lia. }
      lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
      assert (RF3 : rfull R') by exact (msteps_full asegs _ _ Hms RF2).
      readback HR' RF3 HRe2 HRB3.
      assert (Z24 : getr R' 24%bv = Z_to_bv 64 r) by (rewrite (HR' 24%bv); reflexivity).
      eapply (ahh_evt_then H HHl (fun ms => ms = MS (mkR (Z_to_bv 64 BP_RA) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                                       (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 (Z_to_bv 64 r) s9 s10 s11 t3' t4' t5' t6')
                                           F' (Z_to_bv 64 BP_EXIT) fc' None m' (seg_rom asegs)) _ s' msF2 _ mo2 KR2 VIS2).
      { eapply evt_of_msteps_done; [exact Hms|]. rewrite HRB3, Z24. reflexivity. }
      intros msF3 mo3 KR3 MP3 VIS3.
      eapply (K s' LB' LBs' m' mo3 msF3 (Z_to_bv 64 BP_RA) t0' t1' t2' (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' r);
        [exact VIS3 | exact Hr | exact FZ2 | exact KR3 | eapply (ah_mpres_trans H HHl); [exact MP02 | exact MP3]
        | exists c'; exact PE' | exact PK2 | exact FR2 | exact STK2 | exact RFS2 | exact CHN2].
  Qed.

  Lemma bp_loop : forall Q mo0, bp_exit_k Q mo0 -> forall c, bp_head_at Q mo0 c.
  Proof.
    intros Q mo0 K.
    assert (G : forall k c, (Z.to_nat (pw_n H w - c_widx c) <= k)%nat -> bp_head_at Q mo0 c).
    { induction k as [|k IHk]; intros c Hk.
      - destruct (Z_lt_le_dec (c_widx c) (pw_n H w)) as [Hl|Hl]; [lia|]. exact (bp_exit_step Q mo0 c K Hl).
      - destruct (Z_lt_le_dec (c_widx c) (pw_n H w)) as [Hl|Hl]; [| exact (bp_exit_step Q mo0 c K Hl)].
        apply (bp_call_step Q mo0 c K Hl). intros c' H1 H2. apply IHk. lia. }
    intros c. exact (G _ c (Nat.le_refl _)).
  Qed.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma bp_entry : forall Q mo0, bp_exit_k Q mo0 ->
    forall s LB LBs m mo msF (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) F fc (c : parserC) (e : Z),
      as_VIS H s msF = MS (bp_regs ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6) F (Z_to_bv 64 BP_INIT) fc None m
                          (seg_rom asegs) ->
      frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
      piw_ok H w LF m -> parser_repA LB m (pw_p H w) c -> parser_sh m (pw_p H w) c ->
      pc_cons c = pw_cons H w -> pc_user c = pw_user H w -> st_diag (pc_state c) = pw_diag H w ->
      pi_hdr (st5 (pc_state c)) (pw_words H w) (pw_n H w) e ->
      state_own LB (pw_LB0 H w) LBs (pc_state c) -> lb_own LBs m ->
      as_RHEAP H s LB m -> mem_inv asegs m -> (exists errv : word, rw_cells asegs m (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
      as_rauxv_ok H m (pw_B H w) -> ACONST m -> stack0 m (pw_lo H w) (pw_shi H w) -> LINV m ->
      wr_at asegs m (pw_cons H w) 48 -> pw_words H w <> 0 -> 5 <= pw_n H w ->
      as_AL H s >= as_AL H (pw_s0 H w) - pm_phi (pi_c0 (st5 (pc_state c))) ->
      pm_cap (pi_c0 (st5 (pc_state c))) + PM_RESERVE <= po_cost (pw_n H w) -> po_cost (pw_n H w) <= as_AL H (pw_s0 H w) ->
      FR m -> stk asegs m (pw_lo H w) (bv_unsigned sp) -> as_RFS H LF m -> as_chain H m (bv_unsigned s0) CH ->
      as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q mo0 K s LB LBs m mo msF ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 F fc c e
           VIS FZ KR MP K0 PR PSH HC HU HD HDR SOWN LBOWN RH MI ERR RAUX AC S0 LI CWR HW HN AL1 AL2 AL3 FRm STK RFS CHN.
    pose proof (pk_papp _ _ _ _ K0) as (PA & PA0 & PA16).
    assert (P8 : pw_p H w mod 8 = 0) by (Z.div_mod_to_equations; lia).
    pose proof (aapp_bounds _ _ PA ltac:(unfold PARSER_SIZE; lia)) as (AB1 & AB2 & AB3 & AB4 & AB5).
    pose proof (pk_capp _ _ _ _ K0) as (CA & CA0 & CA16).
    pose proof (aapp_bounds _ _ CA ltac:(lia)) as (CB1 & CB2 & CB3 & CB4 & CB5).
    pose proof (pk_pcons _ _ _ _ K0) as PCD.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct (pk_pin _ _ _ _ K0) as (f & Hf & Pf1 & Pf2).
    pose proof (ah_RFS_range H HHl _ _ RFS) as [AFSB AFR].
    pose proof (AFR f Hf) as FRf. unfold aframe_range, AFS_HDR in FRf. unfold afsb_ok in AFSB.
    destruct AFSB as (FS1 & FS2 & FS3 & FS4).
    pose proof (fsz_pos (ff_class f) ltac:(lia)) as FSZ.
    unfold PARSER_SIZE, AAPP_HI in *.
    assert (VS : state_vstride (pc_state c)).
    { destruct HDR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E1 & E2 & E3 & _). cbn [st5 st_v1 st_v2 st_v3] in E1, E2, E3.
      unfold state_vstride. rewrite E1, E2, E3. rewrite !Z.sub_diag. split; [|split]; intros _; reflexivity. }
    unfold parser_repA in PR.
    destruct PR as [Pcons Puser Phdr Pins Phunk Pst Pdef Pal Prange Pconsf Pconsm Pconsd].
    assert (SC0 : scal_cells m (pw_p H w + ST_OFF) (pc_state c)) by (eapply scal_of_rep; exact (conj Pst VS)).
    assert (WR72 : wr_at asegs m (pw_p H w + 72) 8).
    { destruct SC0 as (_ & _ & _ & N3 & _). unfold ST_OFF in N3. replace (pw_p H w + 48 + 24) with (pw_p H w + 72) in N3 by lia.
      exact (proj2 (rw_cells_of_cellw8 _ _ _ N3 ltac:(lia) ltac:(lia))). }
    unfold bp_regs in VIS.
    set (R := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) in VIS.
    assert (RF : rfull R) by (unfold R; apply rfull_mkR).
    pose (E := Eseed R [Z_to_bv 64 (pw_p H w)]).
    assert (HR : regs_ok E (srs sr_id [(18%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      split; [intros Hx; discriminate Hx | reflexivity]. }
    assert (UP : bv_unsigned (edenot E (EVar 32)) = pw_p H w)
      by (change (edenot E (EVar 32)) with (Z_to_bv 64 (pw_p H w)); apply u64_of_Z; lia).
    assert (HK : know_ok asegs E m [KWr (SA (EVar 32) 72) (ELit 8)]).
    { apply Forall_cons; [| apply Forall_nil].
      eapply kwr_of_wr_at; [exact WR72 | unfold estart; cbn [a_base a_off]; rewrite UP; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite UP; change (edenot E (ELit 8)) with (Z_to_bv 64 8); rewrite u64_of_Z by lia; lia
        | unfold elenZ; change (edenot E (ELit 8)) with (Z_to_bv 64 8); rewrite u64_of_Z by lia; lia]. }
    xrun_at (PropExec.mkFP F fc) asegs R BP_INIT m (seg_rom asegs) HR HK 10%nat [BP_HEAD] (SCR [] [] []) 33%N.
    { split_scs; cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite ?UP;
        try change (edenot E (ELit 8)) with (Z_to_bv 64 8); rewrite ?u64_of_Z by lia; lia. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (DJ : forall a n, a + n <= pw_p H w + 72 \/ pw_p H w + 80 <= a -> disjoint_from [(pw_p H w + 72, pw_p H w + 80)] a n)
      by (intros a n D; cbn; split; [exact D | exact I]).
    assert (MU1 : munch [(pw_p H w + 72, pw_p H w + 80)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ?UP; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 (pw_lo H w) (bv_unsigned sp)) by (subst M1; apply stk_mem_denot; exact STK).
    assert (MD : forall a n, mdef m a n -> mdef M1 a n).
    { intros a n Hd i Hi. subst M1. apply mem_denot_defined. apply Hd. exact Hi. }
    assert (C72 : HRep.cellw asegs M1 (pw_p H w + 72) 8 5).
    { apply cellw8_of_rw_cells; [| lia | lia]. subst M1.
      eapply (rw_cells_mem_denot_C8 E m []); [exact Hlf | apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite UP; reflexivity | exact WR72]. }
    assert (WOK : aclient_write_ok H LB (pw_p H w + 72, pw_p H w + 80)) by (unfold aclient_write_ok; right; right; right; right; left; cbn [fst snd]; lia).
    assert (AOK : aconst_ok (pw_p H w + 72, pw_p H w + 80)) by (eapply aconst_ok_app; [exact PA | cbn; lia | cbn; lia]).
    assert (FOK : afs_write_ok H LF (pw_p H w + 72, pw_p H w + 80)) by (unfold afs_write_ok; right; exists f; cbn [fst snd]; split; [exact Hf | lia]).
    assert (RH1 : as_RHEAP H s LB M1)
      by (eapply (ah_RHEAP_frame H HHl); [exact RH | exact MU1 | exact WM1 | apply Forall_cons; [exact WOK | apply Forall_nil]]).
    assert (AC1' : ACONST M1)
      by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact AOK | apply Forall_nil]]).
    assert (RA1 : as_rauxv_ok H M1 (pw_B H w))
      by (eapply (ah_rauxv_frame H HHl); [exact RAUX | exact MU1 | exact WM1 | apply Forall_cons; [exact WOK | apply Forall_nil]]).
    assert (RFS1 : as_RFS H LF M1)
      by (eapply (ah_RFS_frame H HHl); [exact RFS | exact MU1 | exact WM1 | apply Forall_cons; [exact FOK | apply Forall_nil]]).
    assert (LI1 : LINV M1)
      by (eapply LINV_frame; [exact LI | exact MU1 | exact WM1 | apply Forall_cons; [cbn [fst]; lia | apply Forall_nil]]).
    assert (ERR1 : exists errv : word, rw_cells asegs M1 (errno_addr (Z_to_bv 64 ATP)) [C4 errv]).
    { assert (EA : errno_addr (Z_to_bv 64 ATP) + 4 <= pw_p H w + 72).
      { rewrite u64_of_Z by (unfold ATP; lia). unfold ATP, AIMG_TOP in *. lia. }
      destruct ERR as [errv ERR]. exists errv. eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |].
      apply DJ. left. exact EA. }
    assert (XP : xpres H LB (bv_unsigned sp) [(pw_p H w + 72, pw_p H w + 80)] m M1).
    { eapply xpres_of_munch; [exact HHl | exact RH | exact MU1 | exact WM1 |].
      apply Forall_cons; [| apply Forall_nil]. right. intros a Ha. cbn in Ha |- *. left. lia. }
    assert (S01 : stack0 M1 (pw_lo H w) (pw_shi H w)).
    { eapply stack0_xpres; [exact XP | exact S0 |]. apply Forall_cons; [| apply Forall_nil]. unfold stack0_ok. cbn [fst snd].
      destruct PA as [PL|PH]; unfold aapp_lo, aapp_hi in *; [right | left; lia].
      assert (ACP : 0 <= aceil) by lia. pose proof (sh_ge_lowsh _ ACP) as SGL. lia. }
    assert (LB0in : forall b, In b (pw_LB0 H w) -> In b LB).
    { intros b Hb. destruct SOWN as [SO1 _]. apply (Permutation_in _ (Permutation_sym SO1)). apply in_app_iff. left. exact Hb. }
    assert (BLK : forall q n, In (q, n) (state_blocks (pc_state c)) -> In (q, n) (lbl LB)).
    { intros q n Hq. destruct SOWN as [SO1 SO2]. apply (Permutation_in _ (Permutation_sym SO2)) in Hq.
      apply lbl_in_inv in Hq as [pid Hq]. apply (lbl_in LB pid).
      apply (Permutation_in _ (Permutation_sym SO1)). apply in_app_iff. right. exact Hq. }
    assert (BD : forall q n, In (q, n) (lbl LB) ->
              (q + n <= pw_p H w \/ pw_p H w + 288 <= q) /\ (sh q + nsh n <= pw_p H w \/ pw_p H w + 288 <= sh q)
              /\ 0 <= q /\ q + n <= 2 ^ 47).
    { intros q n Hq. apply lbl_in_inv in Hq as [pid Hq].
      pose proof (ah_blocks H HHl _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BA). cbn [blk_addr blk_size fst snd] in *.
      pose proof (aapp_bounds _ _ BA Bn) as (BB1 & BB2 & BB3 & BB4 & BB5).
      pose proof (aapp_disjoint_sh (pw_p H w) 288 q n PA ltac:(lia) ltac:(unfold AAPP_HI in *; lia) Bn) as SD.
      split; [lia|]. split; [exact SD|]. unfold AAPP_HI in *. lia. }
    assert (OSH : forall o n, pw_p H w <= o -> o + n <= pw_p H w + 288 -> 0 <= n -> o mod 8 = 0 ->
              forall a, sh o <= a < sh o + nsh n -> xclient H LB (bv_unsigned sp) [(pw_p H w + 72, pw_p H w + 80)] a).
    { intros o n O1 O2 O3 O4 a Ha. pose proof (aapp_disjoint_sh (pw_p H w) 288 o n PA ltac:(lia) ltac:(unfold AAPP_HI; lia) O3) as SD.
      unfold xclient. split.
      - unfold aclient_addr. right; right; right; right; right; left. unfold sh, nsh in *. Z.div_mod_to_equations. lia.
      - cbn. intros [D|D]; [lia | exact D]. }
    assert (OCL : forall a, pw_p H w <= a < pw_p H w + 288 -> ~ (pw_p H w + 72 <= a < pw_p H w + 80) ->
              xclient H LB (bv_unsigned sp) [(pw_p H w + 72, pw_p H w + 80)] a).
    { intros a Ha Hn. unfold xclient. split.
      - unfold aclient_addr. right; right; right; right; left. lia.
      - cbn. intros [D|D]; [lia | exact D]. }
    assert (OX : OBJX H LB (bv_unsigned sp) [(pw_p H w + 72, pw_p H w + 80)] (pw_p H w + ST_OFF) 0 46).
    { intros a Ha Hn. apply OCL; unfold ST_OFF in *; lia. }
    assert (BX : BLKX H LB (bv_unsigned sp) [(pw_p H w + 72, pw_p H w + 80)] LB (state_blocks (pc_state c))).
    { apply blkx_intro. intros q n Hq. pose proof (BLK q n Hq) as Hl. pose proof (BD q n Hl) as (D1 & _).
      split; [exact Hl|]. split; [exact Hl|]. intros a Ha. cbn. intros [D|D]; [lia | exact D]. }
    assert (BS : BLKSH H LB (bv_unsigned sp) [(pw_p H w + 72, pw_p H w + 80)] (state_blocks (pc_state c))).
    { apply blksh_intro. intros q n Hq. pose proof (BLK q n Hq) as Hl. pose proof (BD q n Hl) as (_ & D2 & _).
      split; [exact Hl|]. intros a Ha. cbn. intros [D|D]; [lia | exact D]. }
    assert (SC1 : scal_cells M1 (pw_p H w + ST_OFF) (st5 (pc_state c))).
    { destruct SC0 as (N0 & N1 & N2 & N3 & N4 & N5 & N6). unfold ST_OFF in *. cbn [st5 st_words st_nwords st_diag st_widx st_icount st_endian st_flags].
      split; [eapply cellw_xp; [exact XP | exact N0 | intros i Hi; apply OCL; lia | lia | lia]|].
      split; [eapply cellw_xp; [exact XP | exact N1 | intros i Hi; apply OCL; lia | lia | lia]|].
      split; [eapply cellw_xp; [exact XP | exact N2 | intros i Hi; apply OCL; lia | lia | lia]|].
      split; [replace (pw_p H w + 48 + 24) with (pw_p H w + 72) by lia; exact C72|].
      split; [eapply cellw_xp; [exact XP | exact N4 | intros i Hi; apply OCL; lia | lia | lia]|].
      split; [eapply cellw_xp; [exact XP | exact N5 | intros i Hi; apply OCL; lia | lia | lia]|].
      eapply cellw_xp; [exact XP | exact N6 | intros i Hi; apply OCL; lia | lia | lia]. }
    assert (RS1 : state_repA LB M1 (pw_p H w + ST_OFF) (st5 (pc_state c))).
    { exact (rep_upd_scal H LB LB LB (bv_unsigned sp) _ m M1 _ (pc_state c) (st5 (pc_state c)) (conj Pst VS) XP OX BX SC1
               ltac:(unfold ST_OFF; lia) ltac:(unfold ST_OFF; lia)). }
    assert (PR1 : parser_repA LB M1 (pw_p H w) (pc5 c)).
    { unfold parser_repA. destruct RS1 as [RS1 _]. constructor; cbn [pc5 pc_cons pc_user pc_state].
      - eapply fld_munch; [exact Pcons | exact MU1 | apply DJ; cbn; lia | lia | cbn; lia].
      - eapply fld_munch; [exact Puser | exact MU1 | apply DJ; cbn; lia | lia | cbn; lia].
      - eapply fld_munch; [exact Phdr | exact MU1 | apply DJ; cbn; lia | lia | cbn; lia].
      - eapply fld_munch; [exact Pins | exact MU1 | apply DJ; cbn; lia | lia | cbn; lia].
      - eapply fld_munch; [exact Phunk | exact MU1 | apply DJ; cbn; lia | lia | cbn; lia].
      - exact RS1.
      - exact (MD _ _ Pdef).
      - exact Pal.
      - exact Prange.
      - eapply fld_munch; [exact Pconsf | exact MU1 | apply DJ; cbn; rewrite HC; lia | rewrite HC; lia | cbn; rewrite HC; lia].
      - exact (MD _ _ Pconsm).
      - exact Pconsd. }
    assert (PSH1 : parser_sh M1 (pw_p H w) (pc5 c)).
    { destruct PSH as (SHp & SHc & SHs). cbn [pc5 pc_cons pc_state]. split; [|split].
      - eapply addressable_xp; [exact XP | exact SHp |]. apply OSH; unfold PARSER_SIZE; lia.
      - change (addressable M1 (pc_cons c) 48). rewrite HC in SHc |- *. destruct (pk_cin _ _ _ _ K0) as (f2 & Hf2 & Cf1 & Cf2).
        pose proof (AFR f2 Hf2) as FRf2. unfold aframe_range, AFS_HDR in FRf2. pose proof (fsz_pos (ff_class f2) ltac:(lia)) as FSZ2.
        eapply addressable_xp; [exact XP | exact SHc |]. intros a Ha.
        pose proof (aapp_disjoint_sh (pw_p H w) 288 (pw_cons H w) 48 PA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as SD.
        unfold xclient. split.
        + unfold aclient_addr. right; right; right; right; right; left. unfold sh, nsh in *. Z.div_mod_to_equations. lia.
        + cbn. intros [D|D]; [lia | exact D].
      - change (state_sh M1 (pc_state c)). eapply sh_keep; [exact (conj Pst VS) | exact SHs | exact XP | exact BS]. }
    assert (K1 : piw_ok H w LF M1).
    { destruct K0 as [k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12]. constructor; try assumption.
      destruct k9 as (pw & k & Hin & Hk & W0 & W16 & Wtop & WD & WS).
      exists pw, k. split; [exact Hin|]. split; [exact Hk|]. split; [exact W0|]. split; [exact W16|]. split; [exact Wtop|].
      split; [exact (MD _ _ WD)|].
      pose proof (BD _ _ (lbl_in _ _ _ _ (LB0in _ Hin))) as (_ & SD & _).
      eapply SHAD_xp; [exact XP | exact WS |]. rewrite cc_gen_length by lia. intros a Ha. unfold xclient. split.
      - unfold aclient_addr. right; right; right; left. exists (pw, pw_words H w, k). cbn [blk_addr blk_size fst snd]. split; [exact (LB0in _ Hin) | lia].
      - cbn. intros [D|D]; [lia | exact D]. }
    assert (CHN1 : as_chain H M1 (bv_unsigned s0) CH).
    { eapply chain_via_xpres; [exact HHl | exact CHN | exact XP | exact HCH |].
      intros fp ra' Hin. pose proof (HCH fp ra' Hin). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right. pose proof Hlo1. pose proof Hlo2. unfold APM_STACK in *. lia. }
    assert (FR1 : FR M1).
    { eapply (FR_keep m M1 []); [exact FRm | apply Forall_nil | | exact ST1 | exact RFS1].
      eapply xpres_weaken; [exact XP | lia | exact LB0in |]. intros a Ha. cbn in Ha |- *. right; left. lia. }
    assert (LBOWN1 : lb_own LBs M1).
    { unfold lb_own in *. eapply Forall_impl; [| exact LBOWN]. intros b Hb. subst M1. apply wr_at_mem_denot. exact Hb. }
    assert (CWR1 : wr_at asegs M1 (pw_cons H w) 48) by (subst M1; apply wr_at_mem_denot; exact CWR).
    assert (SOWN5 : state_own LB (pw_LB0 H w) LBs (st5 (pc_state c))) by exact SOWN.
    assert (PX : PIX H LINV w s LB LBs M1 (pi_c0 (st5 (pc_state c)))).
    { change (pi_c0 (st5 (pc_state c))) with (pi_c0 (pc_state (pc5 c))).
      eapply (pi_init H LINV w s LB LBs LF M1 (pc5 c) e); try eassumption.
      exact (ah_blocks H HHl). }
    assert (RF' : rfull R') by exact (msteps_full asegs _ _ Hms RF).
    assert (HRe : R = mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pw_p H w)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      by reflexivity.
    readback HR' RF' HRe HRB.
    assert (Y18 : getr R' 18%bv = Z_to_bv 64 (pw_p H w)) by (rewrite (HR' 18%bv); reflexivity).
    eapply (sr_blk H HHl); [exact KR | exact VIS | exact RF | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1.
    rewrite <- MS_full_eq in VIS1 by exact RF'. rewrite HRB, Y18 in VIS1.
    eapply (bp_loop Q mo0 K (pi_c0 (st5 (pc_state c))) s LB LBs M1 mo1 msF1 ra t0 t1 t2 (getr R' 10%bv) a1 a2 a3 a4 a5 a6 a7 s8
              t3 t4 t5 t6 F fc);
      [exact VIS1 | exact FZ | exact KR1 | eapply (ah_mpres_trans H HHl); [exact MP | exact MP1]
      | exact PX | exact K1 | exact FR1 | exact ST1 | exact RFS1 | exact CHN1].
  Qed.
End BPLoop.
