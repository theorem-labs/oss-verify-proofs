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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PcStmt LbB_PqK LbB_PqK2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK LbB_PcOvf LbB_PcXsp.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PqR () := "C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4fentC47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes3appI46Stdlib5Lists4List6Exists00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK7q1_numsK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_ltC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv3Sem<branch_takenK46Stdlib9micromega6VarMap1t01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PcXsp6br_gexC47Corelib4Init5Logic8eq_ind_rC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK22W2C5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K47Corelib4Init9Datatypes4bool02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR7n_smallK46Stdlib9micromega=RingMicromega3Op201K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK2W1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4rtblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4ftblC56Stdlib6ZArith6BinInt1Z3divC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK3P1xC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK7q1_valsI47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSK47Corelib4Init9Datatypes3nat02C5ARocqVerifyHarness?AgentSubmission7LibCont4CRep3fldC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK3QW1I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK2tAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK3tD2K47Corelib4Init9Datatypes4prod01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK3tF1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK3tH1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK8tabs_wf1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK8P1x_stepK47Corelib4Init9Datatypes4list02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry04K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit6wboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8rtbl_okbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK8tabs_ok1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK6P1x_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK7kst1_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4fknTC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotK47Corelib5Lists7ListDef6Forall01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN6swinsTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8rtbl_chkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4tupdC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5ftblsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5winsTC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List?Forall_cons_iffC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcI6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK3qf100C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN6re_eqbC46Stdlib5Lists4List7existsbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN8rtbl_subC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit7fent_inC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN8ftbl_subC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4wenvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit=fld_of_4bytesK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec8evt_doneC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN7dk_runNC46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit;fld_of_ftblC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec3evtK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit3finC46Stdlib5Lists4List7forallbC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI47Corelib4Init9Datatypes3nat00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN3tabK4ELinuxProcessSemantics5Riscv5Instr5aluop01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00K4ELinuxProcessSemantics5Riscv5Instr5aluop07I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00K47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK4RTQ2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR4DT2Nc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR4DT2Sc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR4FT20C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface<AFS_MALLOC_1c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR5RTQ2Ec6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR3AT2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR3FT2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR3HT2C5ARocqVerifyHarness@ProcessOversightVTgt_spvtools_binary_parser_fuzzer_both1M?loaded_segmentsK47Corelib4Init9Datatypes3nat01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK6APQ_P2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK4kst1K47Corelib7Numbers7BinNums1N01I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEI5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK3qx200C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK22uAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23uD1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23uF2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23uH2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK29tabs_wf2xC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23P2xC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK29P2x_step4K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK29tabs_ok2xC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK26P2x_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK27kst2_okc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR4br_nC56Stdlib6NArith6BinNat1N3ltbC56Stdlib6ZArith6BinInt1Z4of_NC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evK47Corelib5Lists7ListDef6Forall02c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR4QW2xc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR4RTQ3c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR3DT3c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR4FT30C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_PcStmt4AXSPc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR4RTQXc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR3AT3c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR3FT3c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR3HT3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK4kst2I47Corelib7Numbers7BinNums1N00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK6APQ_P3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23uL2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK28tabs_wf2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK28P2x_stepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23QW2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK28tabs_ok2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK7APQ_P4Bc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR4RTQ4c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR3LTZc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR5RTQXRC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK8APQ_XSRAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23P3xC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK22uSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23uF1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23uH1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23uL1C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK28tabs_wf3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK28P3x_stepC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK23QW3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK28tabs_ok3C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK26P3x_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_PqK27kst3_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK3TS0c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR7APQ_RETc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqR4RTQFC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_PqK4kst3".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition FT20 : list fent := [(24, 8%nat, EVar 54); (120, 8%nat, EVar 52)].

Definition DT2N : list fent := [(256, 4%nat, ELit 4294967295)].
Definition DT2S : list fent := [(256, 4%nat, ELit 32)].

Definition RTQ2E : list (reg * expr) :=
  [(1%bv, ELit 1009780); (2%bv, EAlu ALU_ADD (EVar 54) (ELit (-192))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 54);
   (9%bv, EAlu ALU_ADD (EVar 54) (ELit (-192))); (10%bv, ELit 96); (13%bv, EAlu ALU_ADD (EVar 35) (EVar 36));
   (14%bv, EAlu ALU_ADD (EVar 32) (ELit 112)); (15%bv, ELit 32); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EVar 51);
   (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EVar 35) (EVar 36)); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 112));
   (23%bv, ELit 32); (24%bv, EAlu ALU_ADD (EVar 51) (ELit 64)); (25%bv, EVar 35); (26%bv, EVar 35); (27%bv, EVar 51)].
Definition AT2 : list fent :=
  [(80, 8%nat, EVar 51); (56, 8%nat, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880)); (-192, 8%nat, ELit 0);
   (-8, 8%nat, ELit 1009124); (-16, 8%nat, EVar 33); (-24, 8%nat, EVar 54); (-32, 8%nat, EVar 32); (-40, 8%nat, EVar 51);
   (-48, 8%nat, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 256)) (ELit 3)) (ELit 2147450880));
   (-56, 8%nat, EVar 35);
   (-64, 8%nat, EAlu ALU_ADD (EVar 32) (ELit 256)); (-72, 8%nat, EAlu ALU_ADD (EVar 32) (ELit 259)); (-80, 8%nat, EAlu ALU_ADD (EVar 51) (ELit 64));
   (-88, 8%nat, ELit 2147450880); (-96, 8%nat, EAlu ALU_ADD (EAlu ALU_SRL (EVar 51) (ELit 3)) (ELit 2147450880)); (-104, 8%nat, EVar 51)].
Definition FT2 : list fent :=
  [(24, 8%nat, EVar 54); (120, 8%nat, EVar 52); (0, 8%nat, ELit 1102416563); (8, 8%nat, ELit 142616); (16, 8%nat, ELit 1008288);
   (72, 8%nat, EVar 32); (64, 1%nat, ELit 1)].
Definition HT2 : list fent :=
  [(2147450884, 1%nat, ELit 18446744073709551608); (2147450885, 1%nat, ELit 18446744073709551602);
   (2147450886, 1%nat, ELit 18446744073709551602); (2147450887, 1%nat, ELit 18446744073709551602);
   (2147450880, 1%nat, ELit 18446744073709551601); (2147450881, 1%nat, ELit 18446744073709551601);
   (2147450882, 1%nat, ELit 18446744073709551601); (2147450883, 1%nat, ELit 18446744073709551601);
   (2147450888, 1%nat, ELit 0); (2147450889, 1%nat, ELit 0); (2147450890, 1%nat, ELit 18446744073709551603);
   (2147450891, 1%nat, ELit 18446744073709551603)].

Definition RTQ3 : list (reg * expr) :=
  [(1%bv, ELit 1009780); (2%bv, EAlu ALU_ADD (EVar 54) (ELit (-192))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 54);
   (9%bv, EAlu ALU_ADD (EVar 54) (ELit (-192))); (10%bv, EVar 55); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EVar 51);
   (20%bv, ELit 2147450880); (21%bv, EAlu ALU_ADD (EVar 35) (EVar 36)); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 112));
   (23%bv, ELit 32); (24%bv, EAlu ALU_ADD (EVar 51) (ELit 64)); (25%bv, EVar 35); (26%bv, EVar 35); (27%bv, EVar 51)].
Definition DT3 : list fent := [(136, 8%nat, ELit 0)].
Definition FT30 : list fent := [(24, 8%nat, EAlu ALU_ADD (EVar 54) (ELit (-192))); (120, 8%nat, EVar 56)].

Definition RTQX : list (reg * expr) :=
  [(1%bv, ELit 1010580); (2%bv, EAlu ALU_ADD (EVar 54) (ELit (-192))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 54);
   (9%bv, EAlu ALU_ADD (EVar 54) (ELit (-192))); (10%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (11%bv, EVar 35); (12%bv, EVar 36);
   (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EVar 55); (20%bv, ELit 2147450880); (21%bv, EVar 36);
   (22%bv, EAlu ALU_ADD (EVar 32) (ELit 136)); (23%bv, ELit 32); (24%bv, ELit 0); (25%bv, EVar 35);
   (26%bv, ELit 0); (27%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 55) (ELit 3)) (ELit 2147450880))].
Definition RTQXR : list (reg * expr) :=
  [(2%bv, EAlu ALU_ADD (EVar 54) (ELit (-192))); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 54);
   (9%bv, EAlu ALU_ADD (EVar 54) (ELit (-192))); (10%bv, EVar 36); (18%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (19%bv, EVar 55);
   (20%bv, ELit 2147450880); (21%bv, EVar 36); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 136)); (23%bv, ELit 32); (24%bv, ELit 0);
   (25%bv, EVar 35); (26%bv, ELit 0); (27%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 55) (ELit 3)) (ELit 2147450880))].
Definition AT3 : list fent :=
  AT2 ++ [(-112, 8%nat, EVar 55); (-152, 8%nat, EAlu ALU_ADD (EVar 35) (EVar 36)); (-144, 8%nat, EVar 35);
          (-160, 8%nat, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 136)) (ELit 3)) (ELit 2147450880));
          (-136, 8%nat, EVar 55)].
Definition FT3 : list fent :=
  [(24, 8%nat, EAlu ALU_ADD (EVar 54) (ELit (-192))); (120, 8%nat, EVar 56); (0, 8%nat, ELit 1102416563); (8, 8%nat, ELit 92702);
   (16, 8%nat, ELit 1009648)].
Definition HT3 : list fent :=
  [(2147450884, 1%nat, ELit 18446744073709551608); (2147450885, 1%nat, ELit 18446744073709551608);
   (2147450886, 1%nat, ELit 18446744073709551608); (2147450887, 1%nat, ELit 18446744073709551603);
   (2147450880, 1%nat, ELit 18446744073709551601); (2147450881, 1%nat, ELit 18446744073709551601);
   (2147450882, 1%nat, ELit 18446744073709551601); (2147450883, 1%nat, ELit 18446744073709551601);
   (2147450888, 1%nat, ELit 18446744073709551603); (2147450889, 1%nat, ELit 18446744073709551603);
   (2147450890, 1%nat, ELit 18446744073709551603); (2147450891, 1%nat, ELit 18446744073709551603)].

Definition RTQ4 : list (reg * expr) :=
  [(2%bv, EVar 54); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 33); (9%bv, EVar 54); (10%bv, EAlu ALU_ADD (EVar 32) (ELit 8));
   (18%bv, EVar 32); (19%bv, EVar 51); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 256)) (ELit 3)) (ELit 2147450880));
   (22%bv, EAlu ALU_ADD (EVar 32) (ELit 256)); (23%bv, EAlu ALU_ADD (EVar 32) (ELit 259)); (24%bv, EAlu ALU_ADD (EVar 51) (ELit 64));
   (25%bv, ELit 2147450880);
   (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 51) (ELit 3)) (ELit 2147450880)); (27%bv, EVar 51)].
Definition LTZ : list fent := [(0, 1%nat, ELit 0)].

Definition RTQF : list (reg * expr) :=
  [(1%bv, EVar 34); (2%bv, EVar 33); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 37); (9%bv, EVar 38); (10%bv, EVar 32);
   (18%bv, EVar 39); (19%bv, EVar 40); (20%bv, EVar 41); (21%bv, EVar 42); (22%bv, EVar 43); (23%bv, EVar 44);
   (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48)].
Definition APQ_RET : Z := 0xf6720.

Section QR.

  Local Notation APQ_P2 := LbB_PqK.APQ_P2 (only parsing).
  Local Notation APQ_PAD := LbB_PqK.APQ_PAD (only parsing).
  Local Notation APQ_P3 := LbB_PqK.APQ_P3 (only parsing).
  Local Notation APQ_XSRA := LbB_PqK.APQ_XSRA (only parsing).
  Local Notation APQ_P4B := LbB_PqK.APQ_P4B (only parsing).
  Local Notation wnd := LbB_PqK.wnd (only parsing).
  Local Notation kdj := LbB_PqK.kdj (only parsing).
  Local Notation kdisj_pairs := LbB_PqK.kdisj_pairs (only parsing).
  Local Notation kdisj_vs := LbB_PqK.kdisj_vs (only parsing).
  Local Notation kwrs := LbB_PqK.kwrs (only parsing).
  Local Notation shb := LbB_PqK.shb (only parsing).
  Local Notation shw := LbB_PqK.shw (only parsing).
  Local Notation kshp := LbB_PqK.kshp (only parsing).
  Local Notation kshps := LbB_PqK.kshps (only parsing).
  Local Notation wS := LbB_PqK.wS (only parsing).
  Local Notation wA := LbB_PqK.wA (only parsing).
  Local Notation wD1 := LbB_PqK.wD1 (only parsing).
  Local Notation wD2 := LbB_PqK.wD2 (only parsing).
  Local Notation wDS := LbB_PqK.wDS (only parsing).
  Local Notation wF1 := LbB_PqK.wF1 (only parsing).
  Local Notation wH1 := LbB_PqK.wH1 (only parsing).
  Local Notation wL1 := LbB_PqK.wL1 (only parsing).
  Local Notation wF2 := LbB_PqK.wF2 (only parsing).
  Local Notation wH2 := LbB_PqK.wH2 (only parsing).
  Local Notation wL2 := LbB_PqK.wL2 (only parsing).
  Local Notation WS1 := LbB_PqK.WS1 (only parsing).
  Local Notation WS2 := LbB_PqK.WS2 (only parsing).
  Local Notation WS3 := LbB_PqK.WS3 (only parsing).
  Local Notation SHP1 := LbB_PqK.SHP1 (only parsing).
  Local Notation SHP2 := LbB_PqK.SHP2 (only parsing).
  Local Notation SHP3 := LbB_PqK.SHP3 (only parsing).
  Local Notation LC := LbB_PqK.LC (only parsing).
  Local Notation klc := LbB_PqK.klc (only parsing).
  Local Notation vtkn := LbB_PqK.vtkn (only parsing).
  Local Notation kbase := LbB_PqK.kbase (only parsing).
  Local Notation kds := LbB_PqK.kds (only parsing).
  Local Notation kgeo1 := LbB_PqK.kgeo1 (only parsing).
  Local Notation kgeo2 := LbB_PqK.kgeo2 (only parsing).
  Local Notation kst1 := LbB_PqK.kst1 (only parsing).
  Local Notation kst2 := LbB_PqK.kst2 (only parsing).
  Local Notation kst3 := LbB_PqK.kst3 (only parsing).
  Local Notation zdisj := LbB_PqK.zdisj (only parsing).
  Local Notation wval := LbB_PqK.wval (only parsing).
  Local Notation wlen_ok := LbB_PqK.wlen_ok (only parsing).
  Local Notation elenZ_lit := LbB_PqK.elenZ_lit (only parsing).
  Local Notation kdj_ok := LbB_PqK.kdj_ok (only parsing).
  Local Notation kdisj_vs_ok := LbB_PqK.kdisj_vs_ok (only parsing).
  Local Notation kdisj_pairs_ok := LbB_PqK.kdisj_pairs_ok (only parsing).
  Local Notation kwrs_ok := LbB_PqK.kwrs_ok (only parsing).
  Local Notation vtkn_ok := LbB_PqK.vtkn_ok (only parsing).
  Local Notation gz_of_addr := LbB_PqK.gz_of_addr (only parsing).
  Local Notation outside_of := LbB_PqK.outside_of (only parsing).
  Local Notation TS0 := LbB_PqK.TS0 (only parsing).
  Local Notation RTQ2 := LbB_PqK.RTQ2 (only parsing).
  Local Notation kbase_ok := LbB_PqK.kbase_ok (only parsing).
  Local Notation WS_len := LbB_PqK.WS_len (only parsing).
  Local Notation stk_keep := LbB_PqK.stk_keep (only parsing).
  Local Notation DSF_FIELDS := LbB_PqK.DSF_FIELDS (only parsing).
  Local Notation wk_win := LbB_PqK.wk_win (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (ds p n fl lo : Z) (ff1 fp1 spa : Z).
  Hypothesis G1 : qg1 H sp ds p n fl lo ff1 fp1 spa.

  Local Notation W1 := (@LbB_PqK.W1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa) (only parsing).
  Local Notation q1_ranges := (@LbB_PqK.q1_ranges HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation q1_nums := (@LbB_PqK.q1_nums HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation q1_dj := (@LbB_PqK.q1_dj HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation evW1 := (@LbB_PqK.evW1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa) (only parsing).
  Local Notation q1_vals := (@LbB_PqK.q1_vals HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation wvals1 := (@LbB_PqK.wvals1 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation shp_val := (@LbB_PqK.shp_val HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation kds_ok := (@LbB_PqK.kds_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation kgeo1_ok := (@LbB_PqK.kgeo1_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation kwrs1_ok := (@LbB_PqK.kwrs1_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation kdisj1_ok := (@LbB_PqK.kdisj1_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation kshp_ok := (@LbB_PqK.kshp_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation shk_bounds := (@LbB_PqK.shk_bounds ds) (only parsing).
  Local Notation kshps1_ok := (@LbB_PqK.kshps1_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation klc1_ok := (@LbB_PqK.klc1_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation kst1_ok := (@LbB_PqK.kst1_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation QW1 := (@LbB_PqK.QW1 ds ff1 spa) (only parsing).
  Local Notation P1x := (@LbB_PqK.P1x ds ff1 spa) (only parsing).
  Local Notation P1x_refl := (@LbB_PqK.P1x_refl ds ff1 spa) (only parsing).
  Local Notation shb1_eq := (@LbB_PqK.shb1_eq ff1) (only parsing).
  Local Notation qw1_aconst := (@LbB_PqK.qw1_aconst HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation qw1_out_img := (@LbB_PqK.qw1_out_img HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation hull_nums := (@LbB_PqK.hull_nums HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation qw1_ds_sh := (@LbB_PqK.qw1_ds_sh HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation dsf_keep := (@LbB_PqK.dsf_keep ds fl) (only parsing).
  Local Notation q1_keep := (@LbB_PqK.q1_keep HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation P1x_ok := (@LbB_PqK.P1x_ok HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation tA := (@LbB_PqK.tA spa) (only parsing).
  Local Notation tD2 := (@LbB_PqK.tD2 ds) (only parsing).
  Local Notation tF1 := (@LbB_PqK.tF1 ff1) (only parsing).
  Local Notation tH1 := (@LbB_PqK.tH1 ff1) (only parsing).
  Local Notation tab1_vals := (@LbB_PqK.tab1_vals HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation tabs_wf1 := (@LbB_PqK.tabs_wf1 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation tabs_ok1 := (@LbB_PqK.tabs_ok1 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation P1x_step := (@LbB_PqK.P1x_step sp ds fl lo ff1 fp1 spa) (only parsing).
  Local Notation HHb := (@LbB_PqK.HHb HCEIL H HHbp) (only parsing).
  Local Notation afs1_ok_stack := (@LbB_PqK.afs1_ok_stack HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation afs1_ok_shadow := (@LbB_PqK.afs1_ok_shadow HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation afs1_ok_frame := (@LbB_PqK.afs1_ok_frame H ff1 fp1) (only parsing).
  Local Notation afs1_ok_ds := (@LbB_PqK.afs1_ok_ds H ds) (only parsing).
  Local Notation RFS_step1 := (@LbB_PqK.RFS_step1 HCEIL H HHbp sp ds p n fl lo ff1 fp1 spa G1) (only parsing).

  Notation spz := (bv_unsigned sp) (only parsing).
  Notation qf1 := (qf1 sp ds fl lo ff1 fp1) (only parsing).
  Notation dsf := (dsf ds fl) (only parsing).

  Ltac evw1 := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, W1;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Ltac fop tac := first [apply FOP_nil | apply FOP_cons; [repeat (apply Forall_cons; [tac|]); apply Forall_nil | fop tac]].

  Ltac zd NU := unfold zdisj, wval; cbn [fst snd wS wA wD1 wD2 wDS wF1 wH1 wL1 shw]; clear - NU; unfold sh in *; Z.div_mod_to_equations; lia.

  Ltac tnormq HX :=
    lazymatch type of HX with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in HX; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in HX; clear E
    end.

  Ltac dkrun1 HRT HAT HDT HFT HHT HQP HMI fuel stops dirs :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HAT with ftbl _ _ _ ?AT =>
      lazymatch type of HDT with ftbl _ _ _ ?DT =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
      lazymatch type of HQP with qf1 ?m0 /\ P1x _ _ =>
        let L0 := constr:([tA AT []; tD2 DT []; tF1 FT []; tH1 HT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (kst1 ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound W1) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 54) (s_log SSr) AT) in
          let ks2 := eval vm_compute in (nkeys (EVar 32) (s_log SSr) DT) in
          let ks3 := eval vm_compute in (nkeys (EVar 51) (s_log SSr) FT) in
          let ks4 := eval vm_compute in (nkeys (shb 51 0) (s_log SSr) HT) in
          eapply (dk_runN W1 [tA AT ks1; tD2 DT ks2; tF1 FT ks3; tH1 HT ks4]
                    (tabs_wf1 AT DT FT HT ks1 ks2 ks3 ks4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (fun mx => qf1 m0 /\ P1x m0 mx) (P1x_step m0 AT DT FT HT ks1 ks2 ks3 ks4)
                    Q R F pc fc m ro RT [] kst1 fuel stops (SCR dirs [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_ok1 m0); [exact HQP | exact HMI | exact HAT | exact HDT | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HQP | exact HMI | apply kst1_ok; [exact (P1x_ok m0 _ HQP HMI) | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end end
    end.

  Ltac tsplit4q HTS H1 H2 H3 H4 :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS; clear E end;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; clear HTS; cbn [fst snd] in H1, H2, H3, H4.
  Ltac tsplit5q HTS H1 H2 H3 H4 H5 :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS; clear E end;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; apply Forall_cons_iff in HTS as [H5 HTS]; clear HTS;
    cbn [fst snd] in H1, H2, H3, H4, H5.

  Ltac scs1 := split_scs; cbn [sc_denot edenot]; unfold HLib.Eseed, reg_ev, W1;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app]; rewrite ?LbB_PcOvf.w_mul_g, ?LbB_PcOvf.w_add_g.

  Variables (ff2 fp2 : Z).
  Hypothesis G2 : qg2 H ds ff1 fp1 ff2 fp2.

  Local Notation W2 := (@LbB_PqK2.W2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa ff2 fp2) (only parsing).
  Local Notation W2X := (@LbB_PqK2.W2X ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa ff2 fp2) (only parsing).
  Local Notation q2_nums := (@LbB_PqK2.q2_nums HCEIL H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation q2_dj := (@LbB_PqK2.q2_dj HCEIL H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation evW2 := (@LbB_PqK2.evW2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa ff2 fp2) (only parsing).
  Local Notation wvals2 := (@LbB_PqK2.wvals2 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation kgeo2_ok := (@LbB_PqK2.kgeo2_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation kwrs2_ok := (@LbB_PqK2.kwrs2_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation kwrs3_ok := (@LbB_PqK2.kwrs3_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation kdisj2_ok := (@LbB_PqK2.kdisj2_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation kdisj3_ok := (@LbB_PqK2.kdisj3_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation kshp2_ok := (@LbB_PqK2.kshp2_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2) (only parsing).
  Local Notation kshps2_ok := (@LbB_PqK2.kshps2_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation kshps3_ok := (@LbB_PqK2.kshps3_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation klc2_ok := (@LbB_PqK2.klc2_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation klc3_ok := (@LbB_PqK2.klc3_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation kst2_ok := (@LbB_PqK2.kst2_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation kst3_ok := (@LbB_PqK2.kst3_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation shb2_eq := (@LbB_PqK2.shb2_eq ff2) (only parsing).
  Local Notation QW2 := (@LbB_PqK2.QW2 ds spa ff2 fp2) (only parsing).
  Local Notation QW3 := (@LbB_PqK2.QW3 sp ff1 fp1 spa) (only parsing).
  Local Notation P2x := (@LbB_PqK2.P2x ds spa ff2 fp2) (only parsing).
  Local Notation P3x := (@LbB_PqK2.P3x sp ff1 fp1 spa) (only parsing).
  Local Notation P2x_refl := (@LbB_PqK2.P2x_refl ds spa ff2 fp2) (only parsing).
  Local Notation P3x_refl := (@LbB_PqK2.P3x_refl sp ff1 fp1 spa) (only parsing).
  Local Notation qw2_aconst := (@LbB_PqK2.qw2_aconst HCEIL H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation qw3_aconst := (@LbB_PqK2.qw3_aconst HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation qw2_out_img := (@LbB_PqK2.qw2_out_img HCEIL H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation qw3_out_img := (@LbB_PqK2.qw3_out_img HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation hull2_nums := (@LbB_PqK2.hull2_nums HCEIL H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation qw2_ds_sh := (@LbB_PqK2.qw2_ds_sh HCEIL H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation qw3_ds_sh := (@LbB_PqK2.qw3_ds_sh HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation q2_keep := (@LbB_PqK2.q2_keep HCEIL H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation q3_keep := (@LbB_PqK2.q3_keep HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation P2x_ok := (@LbB_PqK2.P2x_ok HCEIL H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation P3x_ok := (@LbB_PqK2.P3x_ok HCEIL H sp ds p n fl lo ff1 fp1 spa G1) (only parsing).
  Local Notation uA := (@LbB_PqK2.uA spa) (only parsing).
  Local Notation uD1 := (@LbB_PqK2.uD1 ds) (only parsing).
  Local Notation uF2 := (@LbB_PqK2.uF2 ff2) (only parsing).
  Local Notation uH2 := (@LbB_PqK2.uH2 ff2) (only parsing).
  Local Notation uL2 := (@LbB_PqK2.uL2 fp2) (only parsing).
  Local Notation uS := (@LbB_PqK2.uS sp) (only parsing).
  Local Notation uF1 := (@LbB_PqK2.uF1 ff1) (only parsing).
  Local Notation uH1 := (@LbB_PqK2.uH1 ff1) (only parsing).
  Local Notation uL1 := (@LbB_PqK2.uL1 fp1) (only parsing).
  Local Notation tab2_vals := (@LbB_PqK2.tab2_vals HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation tabs_wf2 := (@LbB_PqK2.tabs_wf2 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation tabs_wf3 := (@LbB_PqK2.tabs_wf3 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation tabs_ok2 := (@LbB_PqK2.tabs_ok2 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation tabs_ok3 := (@LbB_PqK2.tabs_ok3 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2) (only parsing).
  Local Notation tabs_wf2x := (@LbB_PqK2.tabs_wf2x HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation tabs_ok2x := (@LbB_PqK2.tabs_ok2x HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation P2x_step4 := (@LbB_PqK2.P2x_step4 sp ds fl lo ff1 fp1 spa ff2 fp2) (only parsing).
  Local Notation P2x_step := (@LbB_PqK2.P2x_step sp ds fl lo ff1 fp1 spa ff2 fp2) (only parsing).
  Local Notation P3x_step := (@LbB_PqK2.P3x_step sp ds fl lo ff1 fp1 spa) (only parsing).
  Local Notation afs2_ok_shadow := (@LbB_PqK2.afs2_ok_shadow HCEIL H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) (only parsing).
  Local Notation afs2_ok_frame := (@LbB_PqK2.afs2_ok_frame H ff2 fp2) (only parsing).

  Notation qf2 := (fun m => qf1 m /\ qx2 ff2 fp2 m) (only parsing).

  Ltac evw2 := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, W2, W1;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Ltac dkrun2 HRT HAT HDT HFT HHT HLT HQP HMI fuel stops dirs :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HAT with ftbl _ _ _ ?AT =>
      lazymatch type of HDT with ftbl _ _ _ ?DT =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HLT with ftbl _ _ _ ?LT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
      lazymatch type of HQP with _ ?m0 /\ P2x _ _ =>
        let L0 := constr:([uA AT []; uD1 DT []; uF2 FT []; uH2 HT []; uL2 LT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (kst2 ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound W2) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 54) (s_log SSr) AT) in
          let ks2 := eval vm_compute in (nkeys (EVar 32) (s_log SSr) DT) in
          let ks3 := eval vm_compute in (nkeys (EVar 55) (s_log SSr) FT) in
          let ks4 := eval vm_compute in (nkeys (shb 55 0) (s_log SSr) HT) in
          let ks5 := eval vm_compute in (nkeys (EVar 56) (s_log SSr) LT) in
          eapply (dk_runN W2 [uA AT ks1; uD1 DT ks2; uF2 FT ks3; uH2 HT ks4; uL2 LT ks5]
                    (tabs_wf2 AT DT FT HT LT ks1 ks2 ks3 ks4 ks5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (fun mx => qf2 m0 /\ P2x m0 mx) (P2x_step m0 AT DT FT HT LT ks1 ks2 ks3 ks4 ks5)
                    Q R F pc fc m ro RT [] kst2 fuel stops (SCR dirs [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_ok2 m0); [exact HQP | exact HMI | exact HAT | exact HDT | exact HFT | exact HHT | exact HLT | vm_compute; reflexivity .. ]
          | exact HQP | exact HMI | apply kst2_ok; [exact (P2x_ok m0 _ HQP HMI) | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end end end
    end.

  Ltac dkrun2x HRT HAT HDT HFT HHT HQP HMI fuel stops dirs :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HAT with ftbl _ _ _ ?AT =>
      lazymatch type of HDT with ftbl _ _ _ ?DT =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
      lazymatch type of HQP with _ ?m0 /\ P2x _ _ =>
        let L0 := constr:([uA AT []; uD1 DT []; uF2 FT []; uH2 HT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (kst2 ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound W2) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 54) (s_log SSr) AT) in
          let ks2 := eval vm_compute in (nkeys (EVar 32) (s_log SSr) DT) in
          let ks3 := eval vm_compute in (nkeys (EVar 55) (s_log SSr) FT) in
          let ks4 := eval vm_compute in (nkeys (shb 55 0) (s_log SSr) HT) in
          eapply (dk_runN W2 [uA AT ks1; uD1 DT ks2; uF2 FT ks3; uH2 HT ks4]
                    (tabs_wf2x AT DT FT HT ks1 ks2 ks3 ks4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (fun mx => qf2 m0 /\ P2x m0 mx) (P2x_step4 m0 AT DT FT HT ks1 ks2 ks3 ks4)
                    Q R F pc fc m ro RT [] kst2 fuel stops (SCR dirs [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_ok2x m0); [exact HQP | exact HMI | exact HAT | exact HDT | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HQP | exact HMI | apply kst2_ok; [exact (P2x_ok m0 _ HQP HMI) | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end end
    end.

  Ltac dkrun3 HRT HST HAT HFT HHT HLT HQP HMI fuel stops dirs :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HST with ftbl _ _ _ ?SX =>
      lazymatch type of HAT with ftbl _ _ _ ?AT =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HLT with ftbl _ _ _ ?LT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
      lazymatch type of HQP with _ ?m0 /\ P3x _ _ =>
        let L0 := constr:([uS SX []; uA AT []; uF1 FT []; uH1 HT []; uL1 LT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (kst3 ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound W2) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SX) in
          let ks2 := eval vm_compute in (nkeys (EVar 54) (s_log SSr) AT) in
          let ks3 := eval vm_compute in (nkeys (EVar 51) (s_log SSr) FT) in
          let ks4 := eval vm_compute in (nkeys (shb 51 0) (s_log SSr) HT) in
          let ks5 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) LT) in
          eapply (dk_runN W2 [uS SX ks1; uA AT ks2; uF1 FT ks3; uH1 HT ks4; uL1 LT ks5]
                    (tabs_wf3 SX AT FT HT LT ks1 ks2 ks3 ks4 ks5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (fun mx => qf1 m0 /\ P3x m0 mx) (P3x_step m0 SX AT FT HT LT ks1 ks2 ks3 ks4 ks5)
                    Q R F pc fc m ro RT [] kst3 fuel stops (SCR dirs [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_ok3 m0); [exact HQP | exact HMI | exact HST | exact HAT | exact HFT | exact HHT | exact HLT | vm_compute; reflexivity .. ]
          | exact HQP | exact HMI | apply kst3_ok; [exact (P3x_ok m0 _ HQP HMI) | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end end end
    end.

  Ltac scs2 := split_scs; cbn [sc_denot edenot]; unfold HLib.Eseed, reg_ev, W2, W1;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app]; rewrite ?LbB_PcOvf.w_mul_g, ?LbB_PcOvf.w_add_g.

  Lemma n_small : 0 <= n < 2 ^ 63.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PqR ()) ["QR"] "h02Hah14__p1h25__p10h35__p11h45__p12h55__p13h65__p14h75__p15h85__p16h95__p17h:5__p18h;5__p19h<4__p2h=5__p20h>5__p21h?4__p3h@4__p4hA4__p5hB4__p6hC4__p7hD4__p8hE4__p9hF7__sat10hG7__sat12hH7__sat14hI6__sat5hJ6__sat7hK4__x1hL2NUhM7__arithhN4__ffhO7__sat11hP7__sat13hQ7__sat15hR6__sat2hS6__sat3hT6__sat4hU6__sat6hV6__sat8hW6__sat9hX8__varmaphY5__witp;<p;1p;2p;3p;4p;8p;7p;6p10000p4p70R0p1000jp4p710p8P0p1001Fp4p710p8P0p1001cp4p710p8g002@l<kTg003<j10Tg003aj1LTg004?j2]Tg004ij12Tg005Gj2DTg005dj2MTg006@j25Tg006[j14Tg007@j23Tg007\j2ITg008<j2TTg008Yj1_Tg009Sj1ATg00:Jj2KTg00:gj2ETg00;Xj2CTg00<@j3@Tg00<dj2\Tg00=Ej2STg00=_j1[Tg00>?j1ZTg00>_j2YTg00?=j1jTg00?[j1iTg00@Fj2XTg00@ij2hTg00ALj4QTg00B7j3WTg00BZj1dTg00C<j8cTg00C`j2bTg00DBj2aTg00Dnj3UTg00EHj3`Tg00Egj4eTg00FYj7fTg00G=j7OTg00Gaj6NTg00HER0f0R1'3p=1%41#4#4#4p=8%41#0p=9%01#0#0#0p=F%01#0#0#0#0#0#0#0p==%01#0#0#2p=<%01#0p=>%01#2p=Vf2R2f1R3'K/31p=;%41#4p=Rg00HcR4?U10p=H1323/51p=:%01#4p=G%21,K3p=B1531,52p=^f4R5f3R61531,52'5'5p=71M01p=?P3g00IAR7g00I`R8P8g00J@R9P1g00J`Ffp=JP2P7P8P8P9P3P1FOp=PP3P7P8P8P9P1ENp=gf6R:P7P8P8P9f5R;P7P8P8P9P5ENP6P7P8P8P9P2P7P8P8P9P3ENP1FOFOp=6p,5HCEILp,1HR<p,2spR=p,2dsR>p,1pR?p,1nR@p,2flRAp,2loRBp,3ff1RCp,3fp1RDp,3spaREp,2G1M<kg00K@RF#0RG#0RH#0RI#0RJ#0RK#0RL#L/]=R=#1RM%2GRN%2LRO'DRP,M='5RQ%4FRR#8RS#8#8#9#8#8#F#=#=#<RT%0LRL#0RU#>RV#0RW#0RX#0RY#VRZ;;=R[%RGRG#R#2R\,DNR],3=R^%2JRJ,I=R_#HR`%2KRK,IERa#HRb%0RRR#9#<,T=%>RRR#<,T=,3E7:ERc%4F#G#R#G#F#=#<%_<R<'3Rd%>GRG#>#9#G#F#=,B<Re/3BRf13TBRTA;BZ=RZ%9H#=RH#0#>,B<RB/3CRg%2L=;CeRL1ICORh#HRi%2X=;<DRX%2F=;DBRB13<>RD%4RRj#<=;>eRk%2IRI,I>Rl#HRm%1?RnA;?@]R?%1@%2RRo,DNRp,3@'5%4V#V%4U#<,3A7:A%>F#=#G#9#9#9#9#=#<%A<R<'3%A>RA1B<H%ACRH1BAj%AeRe1KHJ1BeW%A=RW%8Y#8#8#8#F#=#<%2GRG,DNRY=;W=5:W3:7:e3:3:5:<3^R<'5D7D7D7D7D71E=J%1J%1_[\M%2SRM,CN%?NR_%1M1DNMRJ#?[R=[%1NReg00KeRWA@NM3UW0%1J\W^0e1CN\%1\%?][RM\_A@N\3VWX0e%1]\W^0e1CNG%1G%?Y[R]\_A@NG3VWX0e%1Y\W^0e1ECO%1C%1ORC%1h[[1CNO%?P\CRC\_A@NO3VWX0e%1P\W^0e1CNo%1o%?p[RP\_A@No3VWX0e%1p\W^0e1E>I%1>%1I%1l[[1EEK%1E%1K%1a[[P6g00LA1\0N'SP_eR_O1PPP:P_O1PCf:RCP_O1P]f=R]P_O1PMf@RMP_O1P=p-0R=g00LgR_#[%Z_1Y43%j4%i4R_P7P8P8P9P_P_P6P_P_P5P_P_P;P_P_P:P_P_f7R7P_P_f8RPP_P_f9RaP_P_PCP_P_f;RKP_P_f<REP_P_P]P_P_f>RlP_P_f?RIP_P_PMP_P_fAR>P_P_fBReP_P_fCRWP_P_fDRoP_P_fEROP_P_fFP41X40g00MSRh1h4FRFCQ,J_RYP4PFPh1X4NRN%LR5W4CQ,J_5P_fG,g_5P_F6F6F6F6F6F6F6F6F6F6%d8P4PFg00N:%LS9W4NCQ,J_9P_YGc1b_9P1P2g00NaR_g00OAR9'S1a12=U_9dA`403CebNbXbYXK4X1=X<=X?=X@=XA=XB=XC=XD=XE=X2=X3=X4=X5=X6=X7=X8=X9=X:=X;=X==W>P3P2P6P5P;P:P7PPPaPCPKPEP]PlPIPMP>PePWPo%11131p'5/5OD7D7D7D7D7%131M3J'5[^K4^1=^<=^?=^@=^A=^B=^C=^D=^E=^2=^3=^4=^5=^6=^7=^8=^9=^:=^;=^==^>=P1P<P?PnPmPkPDPBPXPiPLPgPZPTPfPdPcPbP`P^P[PQP@PoOGbMbHbGbFbJbIbRbSbTbIbUbJbVbWbFbObGbPbHbQbLo"). Qed.

  Lemma br_n : forall R X (t : bool), (if t then n = 0 else 0 < n) ->
    branch_taken BC_GE (edenot (HLib.Eseed R (W2 ++ X)) (ELit 0)) (edenot (HLib.Eseed R (W2 ++ X)) (EVar 36)) = t.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PqR ()) ["QR"] "p'0h04__x1h11bi001bh22H0h32Hth47__arithh54__ffh66__sat1h77__sat13h88__varmaph95__with:2Hah;6__sat0h<7__sat12h=1mh>1nh?1xh@1yhA2NShB1RhC1XhD1ti011tp;1p;2p;3p;4p;6p;Ip;7p;8g003<j12Tg006[j14Tg003aj1<Tg00Oaj1LTg00PDj2hTg00>?j1DTg00Dnj35Tg005dj20Tg004ij1BTg005Gj2KTg006@R0j29Tg00Q0j2:Tg00QMj1;Tg00Qkj1]Tg007@j28Tg00RLj2ZTg00;Xj2YTg00<@j3XTg00<dj2WTg00=Ej2CTg00=_j1VTg00>_j2UTg00?=j1RTg00?[j1QTg00@ij2NTg00@Fj2ATg00ALj4>Tg00BZj1MTg00C`j2JTg00DBj2OTg00EHj3PTg00Egj4ITg00Rlj1STg00SNj2TTg00Snj2HTg00TTj3GTg00UCj1gTg00B7j3fTg00Uaj4eTg00V^j6dTg00W<lI`Tg001Fj3\Tg00X4j2^Tg00Xkj1_Tg00Ycj2ETg00Z[j1[Tg00FYj7aTg00C<j8bTg00G=j7cTg00HER1f0R2'8p=7g00NaR3g00OAR4752p=1g00[S9532p=3f1R5g00IAR6g00I`R7P7g00J@R8P2g00J`Fap=6g00HcR9P5g00MSP2C>p==f3R:P6P7P7P8f2R;P5P2Gbp=?P9P5g00N:P2C>p=@P;P6P7P7P8P5P2Fcp=Fg00K@R6#2R<#4#<%2<R=#2#2#2#2#<R>#LR?'h%D?P3p-0P2p,1nR@=591RA101@RBn0110100020000RCg00\3%7@%B<R<%46#4#4#4#4RD#BRE'KRF,0@'9P31:1@RG#;RHA532:X13P3A53H5^3CP;P0%;2RC#1%35RH[%32%;5RI#1[RJ%;;RK#1\H%]2P2n2001000000120000000X13PJ^13P2PGP01:52RJ#3185;RH[18251:;5RL#3[RM1::;RN#3\H1Z52P2n2001000000120000000X@9X?9PM^@9^?9P2P1P@1Y<ERM101<RH%7E101FRO[RP[RQ%7<RRg00KeRSAX<E5UW:RE%7F\S^:RRRP5g00LA1W1<'CPHeO1RHPPg00LgRS#VRT%DSRS1U95RU%R9RV%Q9RWP91N96R6g00\o1A91RXC>,6W%M7R71=6X,6WC?1JW8R8P2P;1C341O2;#1dAP915CIR4b5b8b9X09A59211851[^09P2P@f6O2RYb4b7b<b7O3b2O2b2X3AP0%3C%15RC[%12%3I[RI%3K\C%S2P2n2001000000120000000X13PI^13P2PGP0%1J10;5RJ[1052%1L[RL%1N\J1T52P2n2001000000120000000X=9X>9PL^=9^>9P2P1P@PMPQPEPRPHPPPTPSPUPVPW1@X6,6WRLP7PLC?P8P4b5b8b9X0910121015[^09PYb4b7b<b7O3b2O2b2X3Bn0110000020101P5O1g00]VRB1H>11H>@3GP1P@PMPQPEPRPHPPPTPS%g9PV1=XX,6W1A9<%<D5f9RD,@X,6W5FWP8P4b5b8b91811/9OP2b4b6b;b6PMPQPEPRPHPPPTPSPUPVPW1=X6,6W1@6D,6W5FWRWP7PWC?P8P4b5b8b9X09%72102F'9%75105F'9[^09P2P@f4R2O2b4b6b;b6CeEdp,2rap,2spp,2gpp,2tpp,2s0p,2s1p,2s2p,2s3p,2s4p,2s5p,2s6p,2s7p,2s8p,2s9p,3s10p,3s11p,2dsp,1pP@p,2flp,3ff1p,3fp1p,3spap,3ff2p,3fp2MI`=\?:,^2R2%_1'E%4=#2#2#<#[,E25GB=53;ebAW3XD3WCWBo"). Qed.

  Lemma q_nx : (0 < p \/ n = 0) -> forall R m X,
    sc_denot asegs m (HLib.Eseed R (W1 ++ X))
      (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_SLTU (ELit 0) (EVar 35)) (EAlu ALU_SLTU (EAlu ALU_ADD (EVar 35) (EVar 36)) (ELit 1)))
         (ELit 0)).
Proof.
  intros HPN R m X. pose proof G1 as GG. destruct GG as [_ _ _ _ _ (P0 & PN & N0) _ _ _].
  assert (E35 : edenot (HLib.Eseed R (W1 ++ X)) (EVar 35) = Z_to_bv 64 p) by reflexivity.
  assert (EPN : edenot (HLib.Eseed R (W1 ++ X)) (EAlu ALU_ADD (EVar 35) (EVar 36)) = Z_to_bv 64 (p + n))
    by exact (LbB_PcOvf.w_add_g p n).
  destruct (Z.lt_ge_cases 0 p) as [HP | HP].
  - exact (HUbsan.sc_trap_nullxor asegs m _ (EAlu ALU_ADD (EVar 35) (EVar 36)) (EVar 35) p n E35 EPN HP
             ltac:(clear - N0; lia) ltac:(clear - PN; lia)).
  - assert (Z0 : p = 0) by (clear - P0 HP; lia).
    assert (Z1 : n = 0) by (clear - HPN Z0; destruct HPN; lia).
    assert (G : forall e1 e2 E, edenot E e2 = Z_to_bv 64 0 -> edenot E e1 = Z_to_bv 64 0 ->
              sc_denot asegs m E (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_SLTU (ELit 0) e2) (EAlu ALU_SLTU e1 (ELit 1))) (ELit 0))).
    { intros e1 e2 E H2 H1. cbn [sc_denot edenot]. rewrite H1, H2. vm_compute. reflexivity. }
    apply G; [rewrite E35, Z0; reflexivity | rewrite EPN, Z0, Z1; reflexivity].
Qed.

  Lemma q_wr : forall R m X,
    sc_denot asegs m (HLib.Eseed R (W1 ++ X)) (SCBr false BC_LTU (EAlu ALU_ADD (EVar 35) (EVar 36)) (EVar 35)).
Proof.
  intros R m X. pose proof G1 as GG. destruct GG as [_ _ _ _ _ (P0 & PN & N0) _ _ _].
  assert (E35 : edenot (HLib.Eseed R (W1 ++ X)) (EVar 35) = Z_to_bv 64 p) by reflexivity.
  assert (EPN : edenot (HLib.Eseed R (W1 ++ X)) (EAlu ALU_ADD (EVar 35) (EVar 36)) = Z_to_bv 64 (p + n))
    by exact (LbB_PcOvf.w_add_g p n).
  exact (HUbsan.sc_trap_wrap asegs m _ (EAlu ALU_ADD (EVar 35) (EVar 36)) (EVar 35) p n EPN E35 P0
           ltac:(clear - N0; lia) ltac:(clear - PN; lia)).
Qed.

  Lemma q_p2 : (0 < p \/ n = 0) -> forall (fneg : bool) m0 R m, rfull R -> rtbl W1 R RTQ2 ->
    ftbl W1 spa m [] -> ftbl W1 ds m (if fneg then DT2N else DT2S) -> ftbl W1 ff1 m FT20 -> ftbl W1 (ff1 / 8) m [] ->
    (qf1 m0 /\ P1x m0 m) -> mem_inv asegs m ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AFS_MALLOC_1) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl W1 R1 RTQ2E /\ ftbl W1 spa m1 AT2 /\ ftbl W1 ff1 m1 FT2 /\ ftbl W1 (ff1 / 8) m1 HT2
                  /\ CRep.fld ASEGS m1 (ds + 256) 4 32
                  /\ (qf1 m0 /\ P1x m0 m1) /\ mem_inv asegs m1 /\ munch QW1 m m1 /\ wmono asegs m m1)
        (MS R F (Z_to_bv 64 APQ_P2) fc None m (seg_rom asegs)).
Proof.
  intros HPN fneg m0 R m RF HRT HAT HDT HFT HHT HQP MI.
  destruct fneg; cbv iota in HDT.
  - dkrun1 HRT HAT HDT HFT HHT HQP MI 3000%nat [AFS_MALLOC_1] [false; false].
    { constructor; [apply (q_nx HPN) | constructor; [apply q_wr | constructor]]. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
    tsplit4q HTS1 HA1 HD1 HF1 HH1.
    cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
    split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HF1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HH1); vm_compute; reflexivity|].
    split; [eapply (fld_of_4bytes _ _ _ _ 256 (ELit 32) (ELit 0) (ELit 0) (ELit 0) 32 _ HD1);
            [vm_compute; reflexivity .. | reflexivity]|].
    split; [exact HP1|]. split; [exact HMI1|].
    split; [exact MU1 | exact WM1].
  - dkrun1 HRT HAT HDT HFT HHT HQP MI 3000%nat [AFS_MALLOC_1] [false; false].
    { constructor; [apply (q_nx HPN) | constructor; [apply q_wr | constructor]]. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
    tsplit4q HTS1 HA1 HD1 HF1 HH1.
    cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
    split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HF1); vm_compute; reflexivity|].
    split; [apply (ftbl_sub _ _ _ _ _ HH1); vm_compute; reflexivity|].
    split; [apply (fld_of_ftbl _ _ _ _ 256 4 (ELit 32) 32 HD1); [apply fent_in_In; vm_compute; reflexivity | reflexivity]|].
    split; [exact HP1|]. split; [exact HMI1|].
    split; [exact MU1 | exact WM1].
Qed.

  Definition QW2x : list (Z * Z) := [(spa + -192, spa + 88); (ds + 136, ds + 144); (ff2 + 0, ff2 + 128); (ff2 / 8 + SHBASE, ff2 / 8 + (SHBASE + 16))].

  Lemma q_p3x : 0 < n -> forall m0 R m, rfull R -> rtbl W2 R RTQ3 ->
    ftbl W2 spa m AT2 -> ftbl W2 ds m DT3 -> ftbl W2 ff2 m FT30 -> ftbl W2 (ff2 / 8) m [] ->
    (qf2 m0 /\ P2x m0 m) -> mem_inv asegs m ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AXSP) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl W2 R1 RTQX /\ ftbl W2 spa m1 AT3 /\ ftbl W2 ds m1 DT3 /\ ftbl W2 ff2 m1 FT3 /\ ftbl W2 (ff2 / 8) m1 HT3
                  /\ (qf2 m0 /\ P2x m0 m1) /\ mem_inv asegs m1 /\ munch QW2x m m1 /\ wmono asegs m m1)
        (MS R F (Z_to_bv 64 APQ_P3) fc None m (seg_rom asegs)).
Proof.
  intros HN m0 R m RF HRT HAT HDT HFT HHT HQP MI.
  dkrun2x HRT HAT HDT HFT HHT HQP MI 3000%nat [AXSP] [false].
  { constructor; [exact (br_n R [] false HN) | constructor]. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit4q HTS1 HA1 HD1 HF1 HH1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HF1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HH1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [exact MU1 | exact WM1].
Qed.

  Lemma q_p3z : n = 0 -> forall m0 R m, rfull R -> rtbl W2 R RTQ3 ->
    ftbl W2 spa m AT2 -> ftbl W2 ds m DT3 -> ftbl W2 ff2 m FT30 -> ftbl W2 (ff2 / 8) m [] -> ftbl W2 fp2 m [] ->
    (qf2 m0 /\ P2x m0 m) -> mem_inv asegs m ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 APQ_P4B) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl W2 R1 RTQ4 /\ ftbl W2 spa m1 AT3 /\ ftbl W2 ds m1 DT3 /\ ftbl W2 fp2 m1 LTZ
                  /\ (qf2 m0 /\ P2x m0 m1) /\ mem_inv asegs m1 /\ munch QW2 m m1 /\ wmono asegs m m1)
        (MS R F (Z_to_bv 64 APQ_P3) fc None m (seg_rom asegs)).
Proof.
  intros HN m0 R m RF HRT HAT HDT HFT HHT HLT HQP MI.
  dkrun2 HRT HAT HDT HFT HHT HLT HQP MI 3000%nat [APQ_P4B; AXSP] [true].
  { constructor; [exact (br_n R [] true HN) | constructor]. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit5q HTS1 HA1 HD1 HF1 HH1 HL1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HL1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [exact MU1 | exact WM1].
Qed.

  Lemma q_p4a : forall m0 R m, rfull R -> rtbl W2 R RTQXR ->
    ftbl W2 spa m AT3 -> ftbl W2 ds m DT3 -> ftbl W2 ff2 m FT3 -> ftbl W2 (ff2 / 8) m HT3 -> ftbl W2 fp2 m [] ->
    (qf2 m0 /\ P2x m0 m) -> mem_inv asegs m ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 APQ_P4B) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl W2 R1 RTQ4 /\ ftbl W2 spa m1 AT3 /\ ftbl W2 ds m1 DT3 /\ ftbl W2 fp2 m1 LTZ
                  /\ (qf2 m0 /\ P2x m0 m1) /\ mem_inv asegs m1 /\ munch QW2 m m1 /\ wmono asegs m m1)
        (MS R F (Z_to_bv 64 APQ_XSRA) fc None m (seg_rom asegs)).
Proof.
  intros m0 R m RF HRT HAT HDT HFT HHT HLT HQP MI.
  dkrun2 HRT HAT HDT HFT HHT HLT HQP MI 3000%nat [APQ_P4B] (@nil bool).
  { constructor. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit5q HTS1 HA1 HD1 HF1 HH1 HL1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HL1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [exact MU1 | exact WM1].
Qed.

  Lemma q_p4b : forall m0 R m, rfull R -> rtbl W2 R RTQ4 ->
    ftbl W2 spz m TS0 -> ftbl W2 spa m AT3 -> ftbl W2 ff1 m FT2 -> ftbl W2 (ff1 / 8) m HT2 -> ftbl W2 fp1 m [] ->
    (qf1 m0 /\ P3x m0 m) -> mem_inv asegs m ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 APQ_RET) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl W2 R1 RTQF /\ ftbl W2 fp1 m1 LTZ
                  /\ (qf1 m0 /\ P3x m0 m1) /\ mem_inv asegs m1 /\ munch QW3 m m1 /\ wmono asegs m m1)
        (MS R F (Z_to_bv 64 APQ_P4B) fc None m (seg_rom asegs)).
Proof.
  intros m0 R m RF HRT HST HAT HFT HHT HLT HQP MI.
  dkrun3 HRT HST HAT HFT HHT HLT HQP MI 3000%nat [APQ_RET] (@nil bool).
  { constructor. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit5q HTS1 HS1 HA1 HF1 HH1 HL1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HL1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [exact MU1 | exact WM1].
Qed.
End QR.
