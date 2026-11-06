(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbA_PmLH () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List2InI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbI69OSSVerify5KrLib3bpA3Lib:LbA_PmBase4pmwA00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib3bpA3Lib9LbA_PmCut9regs_tblXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Lib8LbA_PmLH7rt_subbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC46Stdlib5Lists4List=Forall_forallC47Corelib7Classes9MorphismsDiff_impl_subrelationc69OSSVerify5KrLib3bpA3Lib8LbA_PmLH7rt_membC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib8SymExec33SX28expr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib8SymExec33SX2=expr_eqb_trueC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib3bpA3Lib:LbA_PmBase9wenv_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes3sndC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib5EseedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib3bpA2HF8HeapCeil8HeapCeil00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA2Rt7AsIface3asr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationI47Corelib7Numbers7BinNums1N00c69OSSVerify5KrLib3bpA3Lib8LbA_PmLH;lexit_stmtAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Lib8LbA_PmLH:body_stmtAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface5as_StC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_PmBase4wa_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase6c_widxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_nati69OSSVerify5KrLib3bpA3Lib8LbA_PmLH3LIA00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib3bpA2Rt7AsIface5as_SRC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC46Stdlib6ZArith:ZArith_dec;Z_lt_ge_decC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2geI47Corelib4Init6Specif7sumbool00K47Corelib4Init9Datatypes4list01c69OSSVerify5KrLib3bpA3Lib8LbA_PmLH4la_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_PmBase7xa_scalC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib6LibPrs6PmBase8c_icountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs6PmBase8c_endianC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib6LibPrs6PmBase9c_reqconvC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init2WfFwell_founded_inductionC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C46Stdlib5Arith6Wf_nat5lt_wfC69OSSVerify5KrLib3bpA2Rt7AsIface5blockC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I59OSSVerify5KrLib6LibPrs6PmBase3pmc00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib3bpA3Lib:LbA_PmBase8S_MODULEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Lib8LbA_PmLH9TBL_EE648C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op204".
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
ltac2:(KReplay.run1 (kr_t_LbA_PmLH ()) [] "p'0h01xi001xh12reh23Hinh32K1h42K2h52H0h61Kh72b1h82b2h91nh:4Hin'h;1Ah<1Hh=5HCEILh>2HTh?1ei011eh@1fhA1lhB5lemmahC1mhD1rhE3re'hF2HshG1RhH2RThI3RT'hJ1XhK2e'hL2r'hM1whN1yi021bi031pp;1p;2p;6p;3p;7p;4p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0g001:R1p4p710p9P0g001\R2p4p710p8P0g0023R3p4p710p8P0g002TR4p4p710p8P0P4p4p7210p8P0g0031R0p4p710R5p8g003Mj1dTg004Kj1>Tg0050j1HTg005Nj1<Tg0061j1DTg006Qj1[Tg0076j2XTg007bR6j2UTg008Bj6FTg009Bj2PTg00:?j2MTP3j3BTP2j33Tg00;1R2j2KTg00;Jj2WTP1j7VTg00;hj3JTg00<Jj3TTg00=;j2@Tg00>8j3GTg00>Tj3RTg00?7j6QTP0j3ITg00?RR0j2ATg00?lj3OTg00@Oj38Tg00A<j29Tg00B6j2;Tg00BTR1j2CTg00Boj2NTg00CPj2ETg00Cmj2STg00DMj2?Tg00E7j34Tg00EQj3cTg00F5j3bTg00G4j7LTP4j3aTg00GRj2`Tg00HSj3_Tg00I0j3\Tg00IMj2ZTg00J?j2]Tg00K6j2^Tg00Knj4YTg00LNR4f0R3g00LnR734p=2f1R8g00MNR9;a3p=1f3R:f2R;/`8;_3p=6A\893p=0f5R<f4R=/Z:1];8/^334p=7A4437,C8p=:g00NFR7?483p==P;P9P8P3CYp=5g00NdR>g00OcR?%d3g00P\#>R@#>#>#>#>#>#H#<RA#D%[@#HR@/XA%<@RB/U9RC#DRDf6REP<P=P:P;P8EF1P8;#2PAP<11B3RF1M@ARGPAf8RHf7RIPEC610B3RJE7X1CRK=BC;A3C3:PAPIPFPGPAf:RLf9RMPHC6PJE7X1CP8O1RN[^0C'Kp-0ROP21W38XNOX0Og00QAPAPEPFPGPAPMPHPIC6PJE7X1CRO=BC:A3C3=R2PAPHPFPGPAf;RPPLPMC6PJE7X1CP8O1RQ[^0CP3FVWBAJCK;ABCK:PN\2^0CRN'KABCO=A3C3<PQ[^0C;T3WBAJCK:P8O2PN1@3IX1CRN=GC<#2A3C3I1@3LX1CP8O1#2[^0C[A3C3E1@3MX1CP8O1#2[^0C1@3HX1C=GCE#2[ARCN<P:P8P3EQPNP8O1#2P4\3RN%D8RKP1AI;83#2A3=3;P:P3O1':X0:,A:[RQA3:38P;P3O1':X0;,A;AI:;8#2RO[A3<3:P=P3O1':X0=,A=\OAO;83P8n2001000000120000000WAW@X;5PQ^AK^@N^;5P3PC11B=R5=8@F10B=RN/9J';RKXECPHP8O4A3C3M/:KX0C,ACP0PCA3C3L11B<R0=8@F10B<RK/9J';':X0CPAPPP0PGPAf>R0f=RQf<ROC6PKE7P3A3C3O11BIRK=8@F10BIRF/9J';':P1A3C8Q11BH11B8RJ58@10BH10B8'9';#2PAf?RR11BMRSPGPAfBRTfARUf@RVC610BME7P3A3C:R11BP=8@510BP/9N';#2P11;83#2%2;RN%28R5'C[RW1:531;;8#2R5[%2:/CN\51N83P8n2001000000120000000X84X74PW^84^74P311BQ11BE58@R410BQ10BE'9RQP8O3%24/:QP111B0RQ=8@K#210B0/9F#2PAfERF11BRPGPAfHfGR0fFRKC610BRRRE7P311BV=8@S#210BU10BL'9#2P11E83#21=;8[RU1=831E;8#2RS[1=:;\S1S83P8n2001000000120000000XC7X97PU^C7^97P3fCR7,1B,?@RU11BO,?@RSP;O31=USg00R7RS%<3RU%<8RVP1%<;?4831?:;1?:8'=R1[1?;81?;3'=%<:?4;8[R4%<=?4:;\1Ac;83P3n2001000000120000000W8W7W9P4^8V^7U^9SP3P@11BFRFPQP8O4A4BFQ10BKRQ?bR=A49QRP6PBP9fL93C311BT94BJ10B;RT10B7549PAfQ11B:PGPAfTRRfSfRC610B:E7]4]3]2P0A5B83R@fO53CA5B;8,1BRS=4BFA5B:;,0BR:=49QP6PBP9A3C3RA5BE<RR,1B=4BJA5BIE,0B=49TPAfXRTA5BHIRJ,1BPGPAf[R6fZRQfYRFC610BJE7]4]3]:P0fW93C@A5BMH,1B=4BSA5BLM,0B=49:PBP=A5B3P=3CQPAf]R:P8PGPAf`RSf_R@f^R0C6POE7]2XDBA5B=L=3CFP9P=A5BE3=3C6PAP0PIPGPAfaPSP@C6P8E7]2X?9A5B<==3CQPTPRP=O2W2PPP8P3FLW2PPP8PMFLPAP6A5BPLRP,1BPGPAP0P:f\C610BPE7eW4W3W:XK9XLBP8P3O2n2001103000121102101P7P8P3O3W4W3W2X?9XDBP8P3O2n2001103000121102101PKP8P3O3b4b3b5b3b5W4W3P8P3O2n2001000000121000000b6b5W6W:P8P3O2n2001000000121000000W5XECP8P3O2n2001000000121100000b6b5b6X22X1Cb>O2PHPIPEP<P=P;EFeWFW>XIDWHWGWJWMX<?X=>P8P3O2W<W=o"). Qed.

Definition nodesA (c : pmc) : Z := Zlen (t3c (c_m1 c)) + Zlen (t3c (c_m2 c)) + Zlen (t3c (c_m3 c)).
Definition m3okA (ents : list (Z * (Z * Z))) : Prop := Forall (fun e => 0 <= snd (snd e) < 2 ^ 31) ents.
Definition macctA (c : pmc) : Prop :=
  8 * t3b (c_m1 c) <= 16 * Zlen (t3c (c_m1 c)) + 504 /\ 8 * t3b (c_m2 c) <= 16 * Zlen (t3c (c_m2 c)) + 504 /\
  8 * t3b (c_m3 c) <= 16 * Zlen (t3c (c_m3 c)) + 504 /\ m3okA (t3c (c_m3 c)).
Definition laccA (c : pmc) : Prop :=
  2 * Zlen (t3c (c_m1 c)) <= c_widx c /\ 2 * Zlen (t3c (c_m2 c)) <= c_widx c /\ 3 * Zlen (t3c (c_m3 c)) <= c_widx c.

Section LH.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Record LIA (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc)
             (msF : machine_state) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) : Prop := MKLIA {
    la_x    : PMXA H LINV w s LB LBs m mo c S_MODULE TBL_EE648 [];
    la_kr   : as_AKREL H s (mkCfg msF mo);
    la_vis  : as_VIS H s msF = MS R F (Z_to_bv 64 0xee7d8) fc None m (seg_rom asegs);
    la_rf   : rfull R;
    la_fz   : frm_zero fc;
    la_rt   : regs_tbl w R RT_EE648;
    la_gp   : PropExec.getr R 3%bv = wa_gp w;
    la_tp   : PropExec.getr R 4%bv = wa_tp w;
    la_tr   : c_tr c = [];
    la_bsz  : forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40;
    la_ic   : c_icount c + 5 <= c_widx c;
    la_end  : c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1);
    la_w    : wa_words w <> 0 /\ 5 <= wa_n w;
    la_bud  : pm_bud (wa_n w) c;
    la_acc  : nodesA c + 1 <= c_widx c + 3 /\ macctA c /\ laccA c
  }.

  Definition body_stmtA (w : pmwA H) (Q : config -> Prop) : Prop :=
    forall s LB LBs m mo c msF R F fc,
      LIA w s LB LBs m mo c msF R F fc -> c_widx c < wa_n w ->
      (forall s' LB' LBs' m' mo' c' msF' R' F' fc', LIA w s' LB' LBs' m' mo' c' msF' R' F' fc' -> c_widx c < c_widx c' ->
         as_SR H Q (mkCfg msF' mo')) ->
      as_SR H Q (mkCfg msF mo).

  Definition lexit_stmtA (w : pmwA H) (Q : config -> Prop) : Prop :=
    forall s LB LBs m mo c msF R F fc,
      LIA w s LB LBs m mo c msF R F fc -> wa_n w <= c_widx c -> as_SR H Q (mkCfg msF mo).

  Lemma pm_loopA : forall (w : pmwA H) (Q : config -> Prop),
    lexit_stmtA w Q -> body_stmtA w Q ->
    forall s LB LBs m mo c msF R F fc, LIA w s LB LBs m mo c msF R F fc -> as_SR H Q (mkCfg msF mo).
Proof.
ltac2:(KReplay.run1 (kr_t_LbA_PmLH ()) ["LH"] "p'0h01Fh12LBh23LBsh31Rh41ch52fch61mh72moh83msFh91si001sh:4__x1h;4__x2h<1kh=1xh>2H0h?2HLh@3Hk0hA7__arithhB4__ffhC4__p1hD4__p2hE4__p3hF8__varmaphG5__withH4__x3hI4__x4hJ4__x5hK4__x6hL4cstrhM1yhN2B1hO4BODYhP4EXIThQ2F'hR2H2hS2H3hT3HL'hU3HgehV2HkhW3HlthX5HproghY2IHhZ3INDh[3LB'h\4LBs'h]1Qh^2R'h_2_Hh`2c'ha3fc'hb2m'hc3mo'hd4msF'he2s'hf2s0hg1whh2z0hi2z2hj2z3i011gi021lp&0p;1p;2p;;p;3p;<p;@p;4p;6p;7p;8g003Mk10=Tg00RUk20<Tg00SVj2uTg00TVj1jTg0061j1gTg004Kj1@Tg006Qj1\Tg0050j1VTg005Nj1aTg0076j2nTg00UOj26Tg00VKj11Tg00WDj2:Tg00WaR0j1>Tg00XAl;ETg00Y<j2cTg00Z1j3HTg00ZjR1j2_Tg00[Bj2{Tg00[iR2j22Tg00\Ej2NTg00\aR3j2tTg007bj2sTg00]Aj1TTg00]al<pTg00^[l@oTg00_Zj23Tg00`6j1XTg00a1j1STg00alj1RTg00bJj2iTg00bgj1QTg00ccj2<Tg00BTR4j20Tg00d=R5j1BTg00d]j2=Tg00E7j1hj3PTg00e7k20:Tg00eZk308Tg00f7j4dTg00f^j1bTg00gCj2WTg00gek104Tg00hCk203Tg00hdj1ITg00iCj2FTg00ilk302Tg00jUj2^Tg00kAj3]Tg00kaj2MTg00l?j4JTg00l]j1zTg00m;j1yTg00mYj1xTg00nDj2wTg00ngj2CTg00oJj3ZTg00omj4GTg010Xj1vTg011:j2rTg011\j2qTg012Hj3|Tg012gj4}Tg013Yj4~Tg014Dk600Tg014mk201Tg015Jl<mTg015ol<fTg016Tk305Tg017=j7lTg017ak706Tg018Ek607Tg018ij7kTg019Mk809Tg01:1R6f1R7f0R83Pp=Af2R9/67/:8p=7g01:PR:/37/08p=9g00NFR;?P8:p=?AP;78p=4201:8p=8P;P6P;P;P0f4R0P5f3R<g01:nP9P7P8M<mp=YP6P;P1P5P2g01;[f5R2P0P<P9P7P8M<fp>0;P6P;P8P5P7P9P<P0P2f6R5f7R=f8R>M<fp=e13:8p=`B05;78p=;P;P7g01<=P8CGp=KP7g01<dR?g01=CR@P@g01=cRAP8g01>CFlp=5P;P7g01>cP8CGp=LP9P?P@P@PAP7P8K06p=OP7P?P@P@PAP8J07p=UP9P?P@P@PAP7P8Fkp=[P<P?P@P@PAP9P7P8L09p=Dp,1HR?$0=g01?Jp-0RB[20<781u97P6P1g01@?%j?R1g01@[RC#gRDg01ATREg01BERFg01C;RGg01D3RHg00P\RI#@RJ#\RK#V%@JRL#@#@#@RM#@#V#a'nRN%VM#aROf?RP,6?RQ%10RR':#>f:RS'Af@RTPSf9RUP>P=P5P2P0P<P9P7M;E1c2=RV9H?T[[]5^0N]3]8]4]7]6^2D]1]9X<61_87fARW=7?R#>f;RX'AfBRYPSPUP>P=P5P2P0P<P9P7M;EAH?YV[[^5O^0N^3N^8H^4G^7F^6E^2D^1D^91[^M6A7?TR#>/AXPWPSPUP>P=P5P2P0P<P9P7M;E%15RZ16?YR['{12Z[1NZ['tP3%1=R3fCR[,6?R\'21N3\1c=UR\9H?[P8%1>R]fDR^,6?R_'2PYf>R`f=Raf<RbPXPSPUP>P=P5P2P<P8fORcPUP>P=P5P2P0P<P9P7P8M;E%1^%12R^'2p,5HCEILP?p,4LINVfQRdPXPSPUP>P=P5g01E:g01F:g00MN,s;#T%TCP:PdPXPSPUP>P=P5P2P0P<P9P7M<pM@o16?d,3Z,9Z%X5RC13CZ'9%S5RC%RJ%RM'iRM,2C'9%Q5RC#?%RIRZ,4C'<'0'0'0P4fRR4,6?,33,93%X=RC13C3'9%S=RC12CM'9%Q=RC#?14CZ'<'0'0AH?4\P8%1UR\fT,6?,3\'9%XSRC%1S,3C'9%SSRC12CM'9%QSRC#?14CZ'<'0'0fPfV,6?RC%1XRZ':RM#>R31_3d%8MRe%BdRf'2P3PeP8X=;Re%88X=;RgPMPM1=;MDYPdPf1=;fRMJ0;fJRh#1,:CRC#>Ri/Ad%8C/4fRj%h6Rk%h;Rl%B7%B8'41A7820:78408XM6X=6RmPiPgPCO1PePgPCPC1=;CDYPdPfPMM9efERMCdPj%b4%B4#`fXR4%1a57?Rj,W:12:j%8jRf/4j'013j:%?f'0'<fY%1`Rf57?#8P;fZfN#157?Rj,W:12:j%8jRC/4j'013j:%?C'0'<f[%1c57?#8P;g01G9Rc&04I-03;g01GeRC#IRj#IRi#IRn#IRo#I,F;602;Rp1F;oRo1F;nRn1F;i1F;CRC';';';';g01HDRi'^1F;j1;nC,;o,;p';/^i%TcRi5]c3]%gcRcP;P;1M;0P91M;5CJP7P;1M;2P<%z;RpCJCJ%y;Ro%x;RC1w;:Rn1C;LRL%\IRj,C;Rq5Z;Rr'K,5C%@j,C;Rj/Lr,5C5OCP;Prg01I0RrPnCG,5C1UC>5OC5[C%v@R@PC1UCU1C;IRI1C;KRK9Z;L'L,5C5OC1UCS1LIn,5C5OC5[CP@PC1C;JRJ,Lj,5CP@PC1KqK,5CP@PC1KqL,5CP@1KIJ,5CCDCDCDCDCD1rCARAP8P9g00LNRqg00LnRL'=1q89=PqLdA|;:7C}RLbBbFbGX:;X;;XH;XI;XJ;XK;XCBXDBXEB1:<9Rq,2:142q'013q:/05'<1:02,47,0>%?7Rq,0U'<14=<122=125=1225[[[[[^:;^;;^H;^I;^J;^K;^CB^DB^EBP8f],6?RB%1YRY':RK/3:12:KPqP7PYPB%1d%B4P<P9P0P5PbfHR4O>bAbjbSbibRbLb@C~PTPPP`PaPbPXPSPUP>P=1=63P5O>W_WNP7P8O2n2001000000121000000b>WXWTXaOXQNX^NXdHX`GXcFXbEX\DX[DXe1O=WWP8O11N]_P[P`PaPbPXPSPUP>P=P5P2P<A7?M\RM#>R\/AT%8M%BTRa'4R[PkPlPmP\PgPMO1PePgPMPM1=;MDYPTPa1=;aM9eP0CdP[%bW%BW#`fG=7?ZRZ,W:12:Z%8ZRW/4Z'013Z:%?W'0'<%1b97?4#8P;PiPcP;1M;9P7PpCJPoPCP;PJg01IWPICG,5CP@P;PIPrPJCG,5CCDPAPLbBbFbGX:;X;;1N781379[^:;^;;P8Pf16?hP2O3bAbhb>bLb@O<WUP8O1n200110000021110211101bfW?WVX5OX0NX3NX8HX4GX7FX6EX2DX1DX91WYX<6P8J00X<6A7?`R#>/ASPPPSPUP>P=P5P2P0P<P9P7M;EAH?PV[[^5O^0N^3N^8H^4G^7F^6E^2D^1D^91^<6P`PUP>P=P5P2P0P<P9P7P8M;EPX1:Q^#>R^PSPUP>P=P5P2P0P<P9P71=6^P8O=W?X5OX0NX3NX8HX4GX7FX6EX2DX1DX91bZWOWPW]Wgo"). Qed.
End LH.
