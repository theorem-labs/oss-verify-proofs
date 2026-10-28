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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PqK LbB_DtK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK LbB_PcOvf LbB_PcXsp.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_DtR () := "C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4fentC47Corelib4Init5Logic6eq_indI46Stdlib5Lists4List6Exists00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK6d_numsC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3subC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface6as_FSBC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z2ltC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow2shC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission8SymExec33SX27ext_valC56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N3mulC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec;bv_swrap_hiC56Stdlib6ZArith6BinInt1Z7div_1_rC56Stdlib6ZArith6BinInt1Z7pow_0_rC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState<unsigned_litC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics5Riscv3Sem<branch_takenC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK2WDC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib5EseedK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr02K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr07C5ARocqVerifyHarness?AgentSubmission8SymExec33SX26edenotK5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK4d_djI47Corelib4Init5Logic2or00K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK6d_valsC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03C4ELinuxProcessSemantics5Riscv3Sem5alu64K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_PcOvf7bit_oddK46Stdlib9micromega=RingMicromega5Psatz06K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K46Stdlib9micromega:ZMicromega;ZArithProof01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_Bridge5rfullC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4rtblC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit4ftblI6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK2df00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK3LD6C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK9tabs_wfd6C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK8Dx_step6I47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLPropExec7seg_romC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BMState2MSC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK3QWDC46Stdlib5Lists4List:removelastI47Corelib4Init5Logic2ex00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK4kstdK5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX25saddr01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry04K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry06K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry05K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry07K5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit6wboundC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8rtbl_okbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit3finC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK9tabs_okd6C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK5Dx_okC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK7kstd_okC5ARocqVerifyHarness?AgentSubmission7LibHash4HLib3srsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4fknTC5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sym_execC5ARocqVerifyHarness?AgentSubmission=SymExec3Sound4SX2S8sc_denotc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR6br_errC56Stdlib6NArith6BinNat1N3ltbC56Stdlib6ZArith6BinInt1Z4of_NC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3subC47Corelib5Lists7ListDef3nthK5ARocqVerifyHarness?AgentSubmission8SymExec33SX23env01C5ARocqVerifyHarness?AgentSubmission8SymExec33SX22evK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN6swinsTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_FKit:sym_insideC5ARocqVerifyHarness?AgentSubmission8SymExec33SX25s_logC5ARocqVerifyHarness?AgentSubmission8SymExec33SX26s_regsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit8rtbl_chkC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN4tupdC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5ftblsC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN5winsTC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List?Forall_cons_iffC5ARocqVerifyHarness?AgentSubmission8SymExec33SX24s_pcC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK9winsT_LD6C6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN6re_eqbC46Stdlib5Lists4List7existsbC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN8rtbl_subC6ARocqVerifyHarness?AgentSubmission3bpB3Lib8LbB_DKit7fent_inC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN8ftbl_subK47Corelib4Init5Logic2ex01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec8evt_doneC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DKitN7dk_runNC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK2DxC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoK5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry01K5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry08K45stdpp9bitvector;definitions2bv01C46Stdlib5Lists4List7forallbC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BExec3evtK47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes3nat00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26sentry00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX26kentry00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK4RTD2C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK3TSDc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4FTD0I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK6ADT_D3c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4RTD3c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4ATD2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4D0T2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4D1T2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4FTD2c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4HTD2C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface7AOPDEL2I5ARocqVerifyHarness?AgentSubmission8SymExec33SX28sidecond00C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_Kit6SHBASEI5ARocqVerifyHarness?AgentSubmission8SymExec33SX29sym_state00I5ARocqVerifyHarness?AgentSubmission8SymExec33SX27scripts00C5ARocqVerifyHarness?AgentSubmission8SymExec33SX25sr_idI47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK6ADT_D2K5ARocqVerifyHarness?AgentSubmission8SymExec33SX24expr05c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR6br_hdrc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR5RTD2LK4ELinuxProcessSemantics5Riscv5Instr5mulop01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface:AFREE_STUBc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR5RTD3Fc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4ATD3c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4D0T3c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4D1T3c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR9dmid_postc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4RTD4c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR5RTD4FC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK6ADT_D4c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR5RTD5FC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK6ADT_D5c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR5RTD6FC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK6ADT_D6C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK3LD7C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK9tabs_wfd7C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK9winsT_LD7C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK8Dx_step7C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK9tabs_okd7c6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR7ADT_RETc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR4RTDFc6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtR3LTZC6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_DtK6ADT_D7".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition SHF : expr := EAlu ALU_ADD (EAlu ALU_SRL (EVar 49) (ELit 3)) (ELit 2147450880).
Definition SH8 : expr := EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880).
Definition SH320 : expr := EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 320)) (ELit 3)) (ELit 2147450880).

Definition FTD0 : list fent := [(24, 8%nat, EVar 51); (248, 8%nat, EVar 50)].
Definition LT1 : list fent := [(0, 1%nat, ELit 1)].
Definition LTZ : list fent := [(0, 1%nat, ELit 0)].

Definition ATD2 : list fent := [(80, 8%nat, EVar 49); (40, 8%nat, SH320)].
Definition D0T2 : list fent := [(0, 8%nat, ELit 1583784); (8, 8%nat, ELit 1583384)].
Definition D1T2 : list fent := [(112, 8%nat, ELit 1583824)].
Definition FTD2 : list fent :=
  [(24, 8%nat, EVar 51); (248, 8%nat, EVar 50); (0, 8%nat, ELit 1102416563); (8, 8%nat, ELit 123258); (16, 8%nat, ELit 1034672)].
Definition HTD2 : list fent :=
  [(2147450880, 1%nat, ELit 18446744073709551601); (2147450881, 1%nat, ELit 18446744073709551601);
   (2147450882, 1%nat, ELit 18446744073709551601); (2147450883, 1%nat, ELit 18446744073709551601);
   (2147450884, 1%nat, ELit 18446744073709551608); (2147450885, 1%nat, ELit 18446744073709551602);
   (2147450886, 1%nat, ELit 18446744073709551602); (2147450887, 1%nat, ELit 18446744073709551602);
   (2147450892, 1%nat, ELit 18446744073709551608); (2147450893, 1%nat, ELit 18446744073709551602);
   (2147450894, 1%nat, ELit 18446744073709551608); (2147450895, 1%nat, ELit 18446744073709551602);
   (2147450888, 1%nat, ELit 18446744073709551608); (2147450889, 1%nat, ELit 18446744073709551602);
   (2147450890, 1%nat, ELit 18446744073709551602); (2147450891, 1%nat, ELit 18446744073709551602);
   (2147450896, 1%nat, ELit 18446744073709551602); (2147450897, 1%nat, ELit 18446744073709551602);
   (2147450898, 1%nat, ELit 18446744073709551608); (2147450899, 1%nat, ELit 18446744073709551602);
   (2147450900, 1%nat, ELit 18446744073709551602); (2147450901, 1%nat, ELit 18446744073709551602);
   (2147450902, 1%nat, ELit 18446744073709551608); (2147450903, 1%nat, ELit 18446744073709551608);
   (2147450908, 1%nat, ELit 18446744073709551603); (2147450909, 1%nat, ELit 18446744073709551603);
   (2147450910, 1%nat, ELit 18446744073709551603); (2147450911, 1%nat, ELit 18446744073709551603);
   (2147450904, 1%nat, ELit 18446744073709551608); (2147450905, 1%nat, ELit 18446744073709551603);
   (2147450906, 1%nat, ELit 18446744073709551603); (2147450907, 1%nat, ELit 18446744073709551603)].

Definition RTD3 : list (reg * expr) :=
  [(2%bv, EVar 51); (3%bv, EVar 47); (4%bv, EVar 48); (8%bv, EVar 33); (9%bv, EVar 51); (18%bv, EVar 49); (19%bv, EVar 32);
   (20%bv, SHF); (21%bv, ELit 2147450880); (22%bv, ELit 1583840); (23%bv, SH8); (24%bv, EAlu ALU_ADD (EVar 32) (ELit 8));
   (25%bv, EAlu ALU_SRL (EVar 32) (ELit 3)); (26%bv, EAlu ALU_ADD (EVar 32) (ELit 320)); (27%bv, EVar 49)].

Definition RTD2L : list (reg * expr) := (1%bv, ELit 0xfd148) :: (10%bv, EVar 54) :: RTD3.

Definition ATD3 : list fent :=
  [(80, 8%nat, EVar 49); (40, 8%nat, SH320); (-8, 8%nat, ELit 1036668); (-16, 8%nat, EVar 33); (-24, 8%nat, EVar 51);
   (-32, 8%nat, EVar 49); (-40, 8%nat, EVar 32)].
Definition D0T3 : list fent := [(0, 8%nat, ELit 1583784); (8, 8%nat, ELit 1582808)].
Definition D1T3 : list fent := [(112, 8%nat, ELit 1582608)].

Definition RTD4 : list (reg * expr) :=
  [(2%bv, EAlu ALU_ADD (EVar 51) (ELit (-48))); (3%bv, EVar 47); (4%bv, EVar 48); (8%bv, EAlu ALU_ADD (EVar 32) (ELit 112));
   (9%bv, ELit 0); (18%bv, EVar 49); (19%bv, EVar 32); (20%bv, SHF); (21%bv, ELit 2147450880); (22%bv, ELit 1583840); (23%bv, SH8);
   (24%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (25%bv, EAlu ALU_SRL (EVar 32) (ELit 3)); (26%bv, EAlu ALU_ADD (EVar 32) (ELit 320));
   (27%bv, EVar 49)].

Definition RTD3F : list (reg * expr) := (1%bv, ELit 0x1236c4) :: (10%bv, ELit 0) :: RTD4.
Definition RTD4F : list (reg * expr) := (1%bv, ELit 0x1236cc) :: (10%bv, ELit 0) :: RTD4.
Definition RTD5F : list (reg * expr) := (1%bv, ELit 0x1236d4) :: (10%bv, ELit 0) :: RTD4.
Definition RTD6F : list (reg * expr) := (1%bv, ELit 0xfd17c) :: (10%bv, ELit 0) :: RTD3.

Definition RTDF : list (reg * expr) :=
  [(1%bv, EVar 34); (2%bv, EVar 33); (3%bv, EVar 47); (4%bv, EVar 48); (8%bv, EVar 35); (9%bv, EVar 36); (10%bv, EVar 50);
   (18%bv, EVar 37); (19%bv, EVar 38); (20%bv, EVar 39); (21%bv, EVar 40); (22%bv, EVar 41); (23%bv, EVar 42);
   (24%bv, EVar 43); (25%bv, EVar 44); (26%bv, EVar 45); (27%bv, EVar 46)].
Definition ADT_RET : Z := 0xfd2d8.

Section DR.

  Local Notation ADT_D2 := LbB_DtK.ADT_D2 (only parsing).
  Local Notation ADT_D3 := LbB_DtK.ADT_D3 (only parsing).
  Local Notation ADT_D4 := LbB_DtK.ADT_D4 (only parsing).
  Local Notation ADT_D5 := LbB_DtK.ADT_D5 (only parsing).
  Local Notation ADT_D6 := LbB_DtK.ADT_D6 (only parsing).
  Local Notation ADT_D7 := LbB_DtK.ADT_D7 (only parsing).
  Local Notation ADT_VTT := LbB_DtK.ADT_VTT (only parsing).
  Local Notation VT_SBB_A := LbB_DtK.VT_SBB_A (only parsing).
  Local Notation VT_IOB_A := LbB_DtK.VT_IOB_A (only parsing).
  Local Notation wdS := LbB_DtK.wdS (only parsing).
  Local Notation wdA := LbB_DtK.wdA (only parsing).
  Local Notation wdD0 := LbB_DtK.wdD0 (only parsing).
  Local Notation wdD1 := LbB_DtK.wdD1 (only parsing).
  Local Notation wdDS := LbB_DtK.wdDS (only parsing).
  Local Notation wdF := LbB_DtK.wdF (only parsing).
  Local Notation wdH := LbB_DtK.wdH (only parsing).
  Local Notation wdL := LbB_DtK.wdL (only parsing).
  Local Notation WSD := LbB_DtK.WSD (only parsing).
  Local Notation WWD := LbB_DtK.WWD (only parsing).
  Local Notation SHPD := LbB_DtK.SHPD (only parsing).
  Local Notation kdsd := LbB_DtK.kdsd (only parsing).
  Local Notation khdr := LbB_DtK.khdr (only parsing).
  Local Notation kgeod := LbB_DtK.kgeod (only parsing).
  Local Notation kstd := LbB_DtK.kstd (only parsing).
  Local Notation kin := LbB_DtK.kin (only parsing).
  Local Notation TSD := LbB_DtK.TSD (only parsing).
  Local Notation RTD2 := LbB_DtK.RTD2 (only parsing).
  Local Notation rw_cells_of_fld1 := LbB_DtK.rw_cells_of_fld1 (only parsing).
  Local Notation WSD_len := LbB_DtK.WSD_len (only parsing).
  Local Notation WSD_len2 := LbB_DtK.WSD_len2 (only parsing).
  Local Notation DSR_FIELDS := LbB_DtK.DSR_FIELDS (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (ds err lo : Z) (ff fp spa hw dptr : Z).
  Hypothesis G : dg H sp ds err lo ff fp spa hw dptr.

  Local Notation hdrf := (@LbB_DtK.hdrf ds hw dptr) (only parsing).
  Local Notation WD := (@LbB_DtK.WD ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err ff fp spa hw dptr) (only parsing).
  Local Notation d_ranges := (@LbB_DtK.d_ranges HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation d_nums := (@LbB_DtK.d_nums HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation d_dj := (@LbB_DtK.d_dj HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation evWD := (@LbB_DtK.evWD ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err ff fp spa hw dptr) (only parsing).
  Local Notation d_vals := (@LbB_DtK.d_vals HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation wvalsd := (@LbB_DtK.wvalsd HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation shp_vald := (@LbB_DtK.shp_vald HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation kdsd_ok := (@LbB_DtK.kdsd_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation khdr_ok := (@LbB_DtK.khdr_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation kgeod_ok := (@LbB_DtK.kgeod_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation kwrsd_ok := (@LbB_DtK.kwrsd_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation kdisjd_ok := (@LbB_DtK.kdisjd_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation kshpd1_ok := (@LbB_DtK.kshpd1_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation kshpsd_ok := (@LbB_DtK.kshpsd_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation klcd_ok := (@LbB_DtK.klcd_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation kstd_ok := (@LbB_DtK.kstd_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation QWD := (@LbB_DtK.QWD sp ds ff fp spa) (only parsing).
  Local Notation Dx := (@LbB_DtK.Dx sp ds ff fp spa) (only parsing).
  Local Notation Dx_refl := (@LbB_DtK.Dx_refl sp ds ff fp spa) (only parsing).
  Local Notation Dx_trans := (@LbB_DtK.Dx_trans sp ds ff fp spa) (only parsing).
  Local Notation shbd_eq := (@LbB_DtK.shbd_eq ff) (only parsing).
  Local Notation qwd_aconst := (@LbB_DtK.qwd_aconst HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation qwd_out_img := (@LbB_DtK.qwd_out_img HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation hulld_nums := (@LbB_DtK.hulld_nums HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation qwd_ds_sh := (@LbB_DtK.qwd_ds_sh HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation dsr_keep := (@LbB_DtK.dsr_keep ds err) (only parsing).
  Local Notation hdrf_keep := (@LbB_DtK.hdrf_keep ds hw dptr) (only parsing).
  Local Notation hdrf_0 := (@LbB_DtK.hdrf_0 ds hw dptr) (only parsing).
  Local Notation df_0 := (@LbB_DtK.df_0 sp ds err lo ff fp hw dptr) (only parsing).
  Local Notation d_keep := (@LbB_DtK.d_keep HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation Dx_ok := (@LbB_DtK.Dx_ok HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation tS := (@LbB_DtK.tS sp) (only parsing).
  Local Notation tA := (@LbB_DtK.tA spa) (only parsing).
  Local Notation tD0 := (@LbB_DtK.tD0 ds) (only parsing).
  Local Notation tD1 := (@LbB_DtK.tD1 ds) (only parsing).
  Local Notation tF := (@LbB_DtK.tF ff) (only parsing).
  Local Notation tH := (@LbB_DtK.tH ff) (only parsing).
  Local Notation tL := (@LbB_DtK.tL fp) (only parsing).
  Local Notation tabd_vals := (@LbB_DtK.tabd_vals HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation LD6 := (@LbB_DtK.LD6 sp ds ff spa) (only parsing).
  Local Notation LD7 := (@LbB_DtK.LD7 sp ds ff fp spa) (only parsing).
  Local Notation tabs_wfd7 := (@LbB_DtK.tabs_wfd7 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation tabs_wfd6 := (@LbB_DtK.tabs_wfd6 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation tabs_okd7 := (@LbB_DtK.tabs_okd7 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation tabs_okd6 := (@LbB_DtK.tabs_okd6 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation winsT_LD6 := (@LbB_DtK.winsT_LD6 sp ds ff fp spa) (only parsing).
  Local Notation winsT_LD7 := (@LbB_DtK.winsT_LD7 sp ds ff fp spa) (only parsing).
  Local Notation munch6_QWD := (@LbB_DtK.munch6_QWD sp ds ff fp spa) (only parsing).
  Local Notation Dx_step7 := (@LbB_DtK.Dx_step7 sp ds err lo ff fp spa hw dptr) (only parsing).
  Local Notation Dx_step6 := (@LbB_DtK.Dx_step6 sp ds err lo ff fp spa hw dptr) (only parsing).
  Local Notation HHb := (@LbB_DtK.HHb HCEIL H HHbp) (only parsing).
  Local Notation afsd_ok_stack := (@LbB_DtK.afsd_ok_stack HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation afsd_ok_shadow := (@LbB_DtK.afsd_ok_shadow HCEIL H sp ds err lo ff fp spa hw dptr G) (only parsing).
  Local Notation afsd_ok_frame := (@LbB_DtK.afsd_ok_frame H ff fp) (only parsing).
  Local Notation afsd_ok_ds := (@LbB_DtK.afsd_ok_ds H ds) (only parsing).
  Local Notation RFS_stepd := (@LbB_DtK.RFS_stepd HCEIL H HHbp sp ds err lo ff fp spa hw dptr G) (only parsing).

  Notation spz := (bv_unsigned sp) (only parsing).
  Notation df := (df sp ds err lo ff fp hw dptr) (only parsing).
  Notation dsr := (dsr ds err) (only parsing).

  Ltac evwd := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, WD;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Ltac fop tac := first [apply FOP_nil | apply FOP_cons; [repeat (apply Forall_cons; [tac|]); apply Forall_nil | fop tac]].

  Ltac tnormd HX :=
    lazymatch type of HX with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in HX; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in HX; clear E
    end.

  Ltac dkrund7 HRT HXT HAT HD0T HD1T HFT HHT HLT HQP HMI fuel stops dirs :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HXT with ftbl _ _ _ ?XT =>
      lazymatch type of HAT with ftbl _ _ _ ?AT =>
      lazymatch type of HD0T with ftbl _ _ _ ?D0T =>
      lazymatch type of HD1T with ftbl _ _ _ ?D1T =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HLT with ftbl _ _ _ ?LT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
      lazymatch type of HQP with df ?hh ?m0 /\ Dx _ _ =>
        let L0 := constr:(LD7 XT AT D0T D1T FT HT LT [] [] [] [] [] [] []) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (kstd hh ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound WD) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) XT) in
          let ks2 := eval vm_compute in (nkeys (EVar 51) (s_log SSr) AT) in
          let ks3 := eval vm_compute in (kin 0 16 (nkeys (EVar 32) (s_log SSr) D0T)) in
          let ks4 := eval vm_compute in (kin 112 120 (nkeys (EVar 32) (s_log SSr) D1T)) in
          let ks5 := eval vm_compute in (nkeys (EVar 49) (s_log SSr) FT) in
          let ks6 := eval vm_compute in (nkeys (shb 49 0) (s_log SSr) HT) in
          let ks7 := eval vm_compute in (nkeys (EVar 50) (s_log SSr) LT) in
          eapply (dk_runN WD (LD7 XT AT D0T D1T FT HT LT ks1 ks2 ks3 ks4 ks5 ks6 ks7)
                    (tabs_wfd7 XT AT D0T D1T FT HT LT ks1 ks2 ks3 ks4 ks5 ks6 ks7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (fun mx => df hh m0 /\ Dx m0 mx) (Dx_step7 hh m0 XT AT D0T D1T FT HT LT ks1 ks2 ks3 ks4 ks5 ks6 ks7)
                    Q R F pc fc m ro RT [] (kstd hh) fuel stops (SCR dirs [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_okd7 hh m0); [exact HQP | exact HMI | exact HXT | exact HAT | exact HD0T | exact HD1T | exact HFT | exact HHT | exact HLT | vm_compute; reflexivity .. ]
          | exact HQP | exact HMI | apply (kstd_ok hh); [exact (Dx_ok hh m0 _ HQP HMI) | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end end end end end
    end.

  Ltac dkrund6 HRT HXT HAT HD0T HD1T HFT HHT HQP HMI fuel stops dirs :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HXT with ftbl _ _ _ ?XT =>
      lazymatch type of HAT with ftbl _ _ _ ?AT =>
      lazymatch type of HD0T with ftbl _ _ _ ?D0T =>
      lazymatch type of HD1T with ftbl _ _ _ ?D1T =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
      lazymatch type of HQP with df ?hh ?m0 /\ Dx _ _ =>
        let L0 := constr:(LD6 XT AT D0T D1T FT HT [] [] [] [] [] []) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (kstd hh ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound WD) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) XT) in
          let ks2 := eval vm_compute in (nkeys (EVar 51) (s_log SSr) AT) in
          let ks3 := eval vm_compute in (kin 0 16 (nkeys (EVar 32) (s_log SSr) D0T)) in
          let ks4 := eval vm_compute in (kin 112 120 (nkeys (EVar 32) (s_log SSr) D1T)) in
          let ks5 := eval vm_compute in (nkeys (EVar 49) (s_log SSr) FT) in
          let ks6 := eval vm_compute in (nkeys (shb 49 0) (s_log SSr) HT) in
          eapply (dk_runN WD (LD6 XT AT D0T D1T FT HT ks1 ks2 ks3 ks4 ks5 ks6)
                    (tabs_wfd6 XT AT D0T D1T FT HT ks1 ks2 ks3 ks4 ks5 ks6 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity))
                    (fun mx => df hh m0 /\ Dx m0 mx) (Dx_step6 hh m0 XT AT D0T D1T FT HT ks1 ks2 ks3 ks4 ks5 ks6)
                    Q R F pc fc m ro RT [] (kstd hh) fuel stops (SCR dirs [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_okd6 hh m0); [exact HQP | exact HMI | exact HXT | exact HAT | exact HD0T | exact HD1T | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HQP | exact HMI | apply (kstd_ok hh); [exact (Dx_ok hh m0 _ HQP HMI) | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end end end end
    end.

  Ltac tsplit6d HTS H1 H2 H3 H4 H5 H6 :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS; clear E end;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; apply Forall_cons_iff in HTS as [H5 HTS];
    apply Forall_cons_iff in HTS as [H6 HTS]; clear HTS;
    cbn [fst snd] in H1, H2, H3, H4, H5, H6.
  Ltac tsplit7d HTS H1 H2 H3 H4 H5 H6 H7 :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS; clear E end;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; apply Forall_cons_iff in HTS as [H5 HTS];
    apply Forall_cons_iff in HTS as [H6 HTS]; apply Forall_cons_iff in HTS as [H7 HTS]; clear HTS;
    cbn [fst snd] in H1, H2, H3, H4, H5, H6, H7.

  Ltac scsd := split_scs; cbn [sc_denot edenot]; unfold HLib.Eseed, reg_ev, WD;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app]; rewrite ?LbB_PcOvf.w_mul_g, ?LbB_PcOvf.w_add_g.

  Lemma br_err : forall R X,
    branch_taken BC_EQ (edenot (HLib.Eseed R (WD ++ X)) (EExt true 0 4 (EVar 52))) (edenot (HLib.Eseed R (WD ++ X)) (ELit 4)) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_DtR ()) ["DR"] "p'0h06__sat3h16__sat1h24__x1h36__sat5h42Hah57__arithh64__ffh76__sat0h86__sat2h98__varmaph:5__with;1zh<4__p1h=6__sat4h>1Hh?5__p10h@5__p11hA5__p12hB5__p13hC5__p14hD5__p15hE5__p16hF5__p17hG5__p18hH5__p19hI4__p2hJ5__p20hK4__p3hL4__p4hM4__p5hN4__p6hO4__p7hP4__p8hQ4__p9hR7__sat10hS7__sat12hT6__sat8hU1xhV1yhW2H0hX2HehY2NUhZ1Rh[1Xh\7__sat11h]7__sat13h^7__sat14h_6__sat6h`6__sat7ha6__sat9hb1ehc2e0hd5heq_ei001np%0p&0p;1p;2p;<p;3p;4p;6p;5p;Gp;7p;8p10000p4p70R0g000jR1p4p710p8P0p1001Fp4p710p8g001cj10Tg002Hj12Tg002mj1KTg003Kj1zTg003nk20OTg004Zj1pTg005:m<0?Tg0065j2:Tg006_j13Tg007=j2ATg007Zj25Tg0086j28Tg008Vj2ITg0093k104Tg009mj1~Tg00:Jj2?Tg00:fj1TTg00;]j2LTg00<:j2gTg00<Tj2WTg00=Ej2QTg00=mj3PTg00>Qk20NTg00?2k10MTg00?Rk20LTg00@0k10JTg00@Nk10ITg00A9j2_Tg00A\j3fTg00B?k20GTg00Bbk10DTg00CDk20>Tg00Cfk20=Tg00DRj3NTg00Dlk30;Tg00EKk40:Tg00F=S00j27Tg00FXj2eTg00G5k208Tg00GVj1[Tg00H5j2=Tg00H[j4mTg00ITk107Tg00J4k206Tg00JQj1kTg00K1j2aTg00KNj2bTg00Kkj2STg00LRk105Tg00M;j2dTg00Mak303Tg00NDk302Tg00Ngk301Tg00OJj4ZTg00P5k100Tg00PSj3cTg00Q6j4}TP1j6lTg00QWj2qTg00RFj2|Tg00Rej1nTg00S>j5{Tg00TDk109Tg00Tej1yTg00UFj2xTg00VJk30<Tg00W7j3oTg00WfmG0@Tg00X]k30ATg00Y:j2vTg00Z1k10BTg00Zik40CTg00[aj2iTg00\Yj1uTg00]Qj6^Tg00^5j7tTg00^Yj7OTg00_=k80HTg00_aj6sTg00`Ek60KTg00`cR1f0R0'5p=1f2R2f1R3/?0'7p=U%20#2p=`%20#2#2#2p=E%20#0p=F%00#0p=4%00#0#0#0p=]%00#0#0#0#0#0#0#0p=@%00#3p=B1L23/50p=Gg00aAR4?N01p=V1523/70p=9%00#2p=Y%30,L3p=R1730,72p=wf4R5f3R61730,72'7'7p=;AN430p=r1?10p=MP3g00a_R7g00b>R8P8g00b^R9P0E^p=hP4P3g00c>P0CZp=\P3P7P8P8P9P0g00ceFtp=<P4P3g00dEP0CZp=XP2P7P8P8P9P3P0FOp=DP6P7P8P8P9P2P7P8P8P9P3E^P0FOp>0Ff6R:P7P8P8P9f5R;P7P8P8P9P5E^P6P7P8P8P9P2P7P8P8P9P3E^P0FOFOp=CP5P7P8P8P9P6P2P7P8P8P9P3P0FOFOp>0EP6P7P8P8P9P2P3P0L0Hp=Hg00dlR<g00eL7N0p=JAN430#np=6P3P7P8P8P9P0Esp=jP4P5P6P2P3P0J0Kp=>g00elR7#0R=#2R>#K%0=R?#0R@#0RA#0RB#0RC#KRD#zRE+0O%pEp,5HCEILp,1HRFp,2spRGp,2dsRHp,3errRIp,2loRJp,2ffRKp,2fpRLp,3spaRMp,2hwRNp,4dptrROp,1GN<0?1:DGRP#1RQ%3=R=%3CRR'ARS7UPS01%27RT#2#`RU#2#E#E#F#E#E#4#]#@#@#BRV%4CRC#0#4RW#0RX#0RY#BRZ;GPS02%2>R>#`#3R[,A=R\,5PS03%3ARA,8PR]#VS04%3BR^,8MR_#VS05%0TRT#2#4S06#0#B,IP%4TRT#4#B,IP,5M79MS07%27#Y#`#Y#4#]#@#BR`&04FRF'5S08%4>R>#4#F#Y#]#@,RFRa/5JS0915VJS0:AGJZPS0;%F?#@RZ#0#4,RFRJ/5KS0<%3C=GKaS0=18KRRC#VS0>%3X=GFLS0?%37RX=GLJS0@15FHS0A%2TRT#4#B=GHaS0B%3@RJ,8HRV#VS0C%3URb,A=Rc#~1?I179IRd1A=^Re,8IRf1?fe59c%1N?UNS1?O\99`O%47#@#Y#F#F#F#F#4#@#B%TFRF%THR`1RFZ%TKRZ1R`T%TaRa1LZ^1RaW%TPRW%EY#E#E#E#4#]#@#B%3>R>,A=RY=GWP59W3979a393959F393wRFD;D;D;D;D;PfP41g4f1r0fRaePa1WIe%1I%1eRa%1f[[1WPA%1A%1][\Q1Q=^RQ%M=R]%1^RA%Me[RP[Rf%1=RWg00fQRZAP=^3UW4R`Pa\Z^4WRa1Q=[%1[%M\[RT\]AP=[3VZX4W%1\\Z^4W1Q=>%1>%MY[R\\]AP=>3VZX4W%1Y\Z^4W1WKR%1K%1RRY%1C[[1Q=bRC%1b%Mc[R>\]R[AP=b3VZX4WRb%1c\Z^4WRg1Q=RRh%MS\YRY\]RiAP=R3VZX4WRR%1S\Z^4WRW1WHJ%1H%1J%1V[[1WM^%1M%1_\A[P6g00fm20N1='gP]eR]O1PYP:P]O1P>f:RAP]O1P\f=R\P]O1PTf@RTP]O1PPp-0R_g00gSR^$0MRV%p^R^20L43Rj&0J4Rk&0I4RlPl1hl6RmPl1hl5PlPlP;PlPlP:PlPlf7RnPlPlf8RoPlPlf9RpPlPlPAPlPlf;RqPlPlf<RrPlPlP\PlPlf>RsPlPlf?RtPlPlPTPlPlfARuPlPlfBRvPlPlfCRwPlPlfDRxPlPlfE1_4=Ry%KU5f420G47R7'\,<lRU%KBRB9f4yRz,X7,<lR{5DlR|fFR},hl5DlH0FFCFCFCFCFCFCFCFCI0E&0D8R8P|CH20>l9R9P0P2g00h?R~,g<20=02=N<~dB0;413H0:R<b6b9b:X24X<_XI_XK_XL_XM_XN_XO_XP_XQ_X?_X@_XA_XB_XC_XD_XE_XF_XG_XH_WJP3P2P6P5P;P:PnPoPpPAPqPrP\PsPtPTPuPvPw15c0Rw1?0eRv'7RuPxD;D;D;D;D;15c3S0D1?3eRx'7[^24^<_^I_^K_^L_^M_^N_^O_^P_^Q_^?_^@_^A_^B_^C_^D_^E_^F_^G_^H_^J_P0PFPdQ0CQ0BQ0AQ0@Q0?Q0>Q0=Q0<Q0;Q0:Q09Q08Q07Q05Q04Q03Q02Q01P}fGOFb5bSbRbTb3b0b7b1b8b0b=b3b_b`bTbabRb\bSb]b^bdPuQ001e30#J1623R}[16301e23#J[Rd1e62#J\}20830P0n2001000000120000000XV4XU4Pd^V4^U4P0P~g00h_Rd%[d#[#[#[R}1=D2RFCm,:DS00%3?R?,=DRT,:DRtP2%K@&07}+06%kd,aJ,A=,b0%k},aJ,A='8'S,=D,:D/6tX;4PX1b60/8e,SB,=D,:D/6tX;4P2180e,SB,=D,:D/6tX;4P21SB0,=D,:D/6tX;4&05B,I21=D0,:D/6tX;41I2eRJ,dDR@160tX;41dD?Rs1I6eR6,dD/60X;4P41aXSR\,LJRA/8SS0118?SR:,60X;4R;PAP;P?1L6\/60X;4PQPfP`PaPhPiPRPWPCP[PbPgP3P]O1R6P>P5P]O1R5PYPnP]O1R]PPPVP^PjPkPlADlUmS02P8P4B0347z1_4XAf4yDRy60246014Rzg00i>S031_4?RnCZ,<l,jlCHP9P<b6b9b:X24X<_17w3Rw1I3e/L\R\/r?g00ieR;[[^24^<_P01?rePrPqO3b5b3b0b1b7b1b8b0b=b3P:PQPfP`PaPhPiPRPWPCP[PbPgP6P>P5PYP]PPPVP^&004S04Pk1_41R:/\n,<l1Xny,<l5DlP9P<b6b9b:%1??U?SP0b5b3b0b1b7b1b8b0b=b39c?SD>Q01PQPfP`PaPhPiPRPWPCP[PbPgP6P>P5PYP]PPPVP^PjPkPlP|P81\:z,<l1Xzy,<l5DlCHP9P<b6b9b:X24%1\?U\S\u^24P0PrPqO2Rqb5b3b0b1b7b1b8b0b=b39cASD>18JSPJPXPSPQPfP`PaPhPiPRPWPCP[PbPgP6P>P5PYP]PPPVP^Q04PkP4PyQ03P:CZ,<l,jlP9P<b6b9b:%VSP;[P0b5b3b0b1b7b1b8b0b=b3C}El16@sePt1qD?D>1=DJ,:D1qDJD>1SB2PBP2g00jBRJg00j`Rs7NBR@PJPBPJP_P0P;PZn0110000020010000XcJg00k>PsP0ElP;1|;0bWW>%n@ePQPfP`PaPCP[PbPgP6P>P5PPPVP^PjPkPlQ02P8PUCHP9P<b6b9b:X24X<_Q0D\w^24^<_P01?pePpPoO3b5b0b1b7b1b8b0PQPfP`PaPCP[PbPgP6P>P5PPPVP^PjPkPlADlm{P8P{CHP9P<b6b9b:X24X<_173vPx[^24^<_P015cpPpPoO3b5b0b1b7b1b8b0D{D>182ePQPfP`PaPCP[PbPgP6P>P5PPPVP^PjPkPlP|P81\:7,<lR:=Dl{CHP9P<b6b9b:X24%13R{/7x\u^24P0PpPoO2b5b0b1b7b1b8b09c2eD>1b2X&092D>1A=1%y=D>1:DFPQPfP`PaPhPiPRPWPCP[PbPgP6P>P5PYP]PPPVP^PjPkPlP|P81X7y,<l9Dl:CHP9P<b6b9b:X24AU{3S\u^24Pqb5b3b0b1b7b1b8b0b=b3,x2D>Q00/6teO3b>P~PdP}1=D3CmRt>0<DT#Jeg00kZRD?otT#JebXbbp,2raPGp,2gpp,2tpp,2s0p,2s1p,2s2p,2s3p,2s4p,2s5p,2s6p,2s7p,2s8p,2s9p,3s10p,3s11PHPIPKPLPMPNPONG0@>0AE3,v2R2P~PdP}Q06#K$0BH0C'i%u?,i25oD#JebYW[WZo"). Qed.

  Lemma br_hdr : forall R X,
    branch_taken BC_EQ (edenot (HLib.Eseed R (WD ++ X)) (EAlu ALU_AND (EExt false 0 1 (EVar 53)) (ELit 1))) (edenot (HLib.Eseed R (WD ++ X)) (ELit 0)) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_DtR ()) ["DR"] "h02H0h16__sat8h24__x1h34__x2h44__x3h54__p1h61Hh72H1h82H2h92H3h:7__arithh;4__ffh<6__sat7h=8__varmaph>5__with?1qh@1rhA2HahB2_HhC3_H0hD3_H1hE3_H2hF3HWOhG1RhH2V6hI1XhJ3_H3hK3_H4hL1bhM2hwp%0p&0p;1p;2p;<p;Gp;4p;3p;6p;7p;8g001cj12Tg002Hj10Tg002mj1NTg003Kk10>Tg003nk203Tg004Zj1WTg00lLl<pTg0093j1kTg006_j1:Tg00;]j24Tg007Zj26Tg00mEj2KTg00:fj1[Tg0086j2YTg00F=R0j21Tg00WflGvTg00GVj1JTg00Z1j1mTg00Zij4lTg00\Yj1STg00m_j3iTg00nWl<gTg007=j2^Tg00:Jj2>Tg00oRj2cTg00DRj3@Tg00Rej1bTg00KNj2aTg00K1j2ITg0103j2`Tg010Zj2_Tg011Ak20<Tg011gk20;Tg00>Qk20:Tg00<:j2QTg00=Ek207Tg00=mk306Tg012Mj2DTg0136j2FTg013bk102Tg014@k201Tg014aj3LTg00?2j1zTg015Jj3GTg00?Rj2TTg015jj4yTg00@0j1xTg00@Nj1wTg00A9j2PTg00_aj6uTg00Bbj1tTg00B?j2MTg00NDj3sTg00Ngj3OTg00CDj2oTg00Cfj2nTg00Dlj3qTg00EKj4rTg00H5j2HTg00H[j4VTg016Hj3RTg0170j2XTg00OJj4BTg00]Qj6jTg017\j2{Tg018Ej3|Tg00A\j3}Tg018nj3~Tg00`Ek600Tg000jj6fTg00X]k304Tg00Y:k205Tg00[aj2\Tg00W7j3]Tg019lj3eTg00^5j7dTg00_=k808Tg00^Yk709Tf0R1#2#2#2#2p=3%21#2p=E%01#0#0#0p=?%01#0p>0=g00aAR2f1R3;@1p=<f3R4f2R5@0431+05p=5g00dlR6g00kZR71\451\313]g00eLR83@p=7g00`cR9/651>31'1p==1691p=CAe231p=9P2P3g00i>P1CBp=AP3g00a_R:g00b>R;P;g00b^R<P1g00ceFdp=8P4P:P;P;P<P5P3P1L08p=;A]731=@68p=UP5P:P;P;P<P3P1K09p=Z1>31,15p=hg00elR7#2R=#0R>#N%3=R?#2R@#NRA$0>RB+03%WBp,5HCEILRCp,1HRDp,2spREp,2dsRFp,3errRGp,2loRHp,2ffRIp,2fpRJp,3spaRKp,2hwRLp,4dptrRMp,1GRNM<p%kDRO%0>#3#0#E#0#3#3#3#:'4%07R>#0#?#?#?#2#0$0=#3#3#3#:'6%E@RP#2#3#?#?#?#?#2#E#3#3#3#:/6O'KRO%:P,4I/6F%2>RP#E#0RQ#2#E#:,4FRR/6I'KRS%:7RT,4J/6F16RJ'KRR%[IRU%:?R?'4%[FRV'6%:Q,4V/6U'KRU%:=RV,YLRQ/<TRW'1RX'1RY'1RZ'1P0POPZP4PBp,2raPEp,2gpp,2tpp,2s0p,2s1p,2s2p,2s3p,2s4p,2s5p,2s6p,2s7p,2s8p,2s9p,3s10p,3s11PFPGPIPJPKPLPMMGvR[P5C5R\g01:UR]P8g00h_R^%J^R_%0P#2#0#N#mCl%ST3iRPP\%S9R\C7P1P0PSPYf7PBP[f6R`C5RaPPPaP\C7P1P0PRPXf;RaPBP[f:C5RbPPPbP\C7P1P0PUPWf?PBP[f>S00C5RbPPPbP\C7P1PCPDPEPFPGPHPIPJPKPLPMPNM<g%:@R@,^VRN9=FFRFA=IINRIA=JJNRJA=KKNRK1^V?,YGRG?=GNRG%CLS011>LNS02'1R?A=MMNRM'1RH'1RE'1RD'1RC'1Rb'1P0PFPbfDPBP[fCC5RcPPPcP\C7P1P0PIPCfHPBP[fGC5RcPPPcP\C7P1P0PJPDfLPBP[fKC5RcPPPcP\C7P1P0PKPEfPPBP[fOC5RcPPPcP\C7P1P0PGPHfTPBP[fSC5RcPPPcP\C7P1P0P?PMfXPBP[fWC5R0PPP0P\C7P11cLVS03A@2V9R0#b1aLVRc,IVRd/4Q,<L[S041`LVS051>9VReA=QQV[S061_LVS071>V91>VQ16Q9'1[S0820<LVS09A@2c9\0S0:20;LVS0;1<QL\0S0<PcP2PQP2f5Rfg00fm20:9V'QPeeRgO1S0=A=11VS0>207V@S0?%C@1>9N[Rh\eS0@%CVReg00fQRiB06V@3UWAR@%CN\i^AeReP3PgO1RgPhg00gSRi%J_Rj,D2Rk1D2_Rl1D2^Rm'9'9g01;ARn'F&027-012Ro=L2kRpAL2ol/9m'9/Fn%ziRq5Gi3G%WiRrP21T25P31T24CyRs%x2Rt%w2RuPuPuP:P;P;P<1P2VRv1P29Rw'A,8uEuS0A%t;Rx1M2=R=1M27S0B9s2vR71M2>R>5O2'A,8uC;PxPu1P2TRy,A>,8uPxAO27yS0C/A=,8uC;C;1ou<RzP1P5g00h?R{,Q61n15=@6{dAq293CrR{b;b=b>X22X32X42g00ie\0R01IV3R|/44,<5[1<4TR}1IV5/4T/<4[[^22^32^42P1PfPLP`PafUO5b:b1b<b1b0b@b?b9b8b7b0b614dTRd/<LP2PdP8P^P_1HA1CV1HATR~5R]1HA9R9'UXM2PBP~1U19XLB1Q68P8P^P_1HAdCV=R]~Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<PcP2PQP2Q0=Q0>Q0?Q0@P@PePgPhp-0R~%JjRj,D2R]19kl'919ml/Fn'X=GiqPrPsPtPuPuQ0APxAO27=,A>,8uC;R7PxPuP2Pwg00c>RlP>CB,8uPuP:P;P;P<PfEjR<5ZuPxPu1A=y,8uRyPxP2PwPlQ0BCB,8uC;C;C;PzP{b;b=b>X22X32X42W514|5,<4\0R0%C4R|f4R5'1P|\}[[^22^32^42^5~P1Q02PLPfP`PaQ00fVR|O7b:b1b<b1b0b@b?b9b8b7b0b6Q03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<PcP2PQP2Q0=Q0>Q0?Q0@P@PePgPh1{2V=|2m%Jj,D29L2o19]p'9'9/Fn,Xm=GiqPrPsPtPuP7PxPuP2P>g00dER>A}2vARvCB,8u9Zu<PxPuPyPxP2Q0CP>PvCB,8uC;C;C;PzP{b;b=b>X22X32X42X5~Ah54N1IV4/4T/>N\}[\0^22^32^42^5~P1Q01PLPfP`PaQ00P|O7b:b1b<b1b0b@b?b9b8b7b0b65~cJ00PLP1Efb0f[PBP[fZC5R[PPP[P\C7eXKMXH?P3P1O2n2001000000121000000X0HXJGP3P1O2n2001000000121000000X0EXEKP3P1O2n2001000000121000000X0DXDJP3P1O2n2001000000121000000X0CXCIP3P1O2n2001000000121000000X0bXBFP3P1O2n2001000000121000000b0XFWXEUP3P1O2n2001000000121000000X0XXDRP3P1O2n2001000000121000000X0YXCSP3P1O2n2001000000121000000X0ZXBOP3P1O2n2001000000121000000b0WIWGo"). Qed.

  Lemma q_d2s : forall m0 R m, rfull R -> rtbl WD R RTD2 ->
    ftbl WD spz m TSD -> ftbl WD spa m [] -> ftbl WD ds m [] -> ftbl WD ff m FTD0 -> ftbl WD (ff / 8) m [] ->
    (df 1%nat m0 /\ Dx m0 m) -> mem_inv asegs m ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 ADT_D3) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl WD R1 RTD3 /\ ftbl WD spz m1 TSD /\ ftbl WD spa m1 ATD2 /\ ftbl WD ds m1 D0T2 /\ ftbl WD ds m1 D1T2
                  /\ ftbl WD ff m1 FTD2 /\ ftbl WD (ff / 8) m1 HTD2
                  /\ (df 1%nat m0 /\ Dx m0 m1) /\ mem_inv asegs m1 /\ munch (removelast QWD) m m1 /\ wmono asegs m m1)
        (MS R F (Z_to_bv 64 ADT_D2) fc None m (seg_rom asegs)).
Proof.
  intros m0 R m RF HRT HXT HAT HDT HFT HHT HQP MI.
  dkrund6 HRT HXT HAT HDT HDT HFT HHT HQP MI 3000%nat [ADT_D3; AOPDEL2] [false].
  { constructor; [apply br_err | constructor]. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit6d HTS1 HX1 HA1 HD01 HD11 HF1 HH1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HX1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD01); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD11); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HF1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HH1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [rewrite winsT_LD6 in MU1; exact MU1 | exact WM1].
Qed.

  Lemma q_d2l : forall m0 R m, rfull R -> rtbl WD R RTD2 ->
    ftbl WD spz m TSD -> ftbl WD spa m [] -> ftbl WD ds m [] -> ftbl WD ff m FTD0 -> ftbl WD (ff / 8) m [] ->
    (df 2%nat m0 /\ Dx m0 m) -> mem_inv asegs m ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AOPDEL2) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl WD R1 RTD2L /\ ftbl WD spz m1 TSD /\ ftbl WD spa m1 ATD2 /\ ftbl WD ds m1 D0T2 /\ ftbl WD ds m1 D1T2
                  /\ ftbl WD ff m1 FTD2 /\ ftbl WD (ff / 8) m1 HTD2
                  /\ (df 2%nat m0 /\ Dx m0 m1) /\ mem_inv asegs m1 /\ munch (removelast QWD) m m1 /\ wmono asegs m m1)
        (MS R F (Z_to_bv 64 ADT_D2) fc None m (seg_rom asegs)).
Proof.
  intros m0 R m RF HRT HXT HAT HDT HFT HHT HQP MI.
  dkrund6 HRT HXT HAT HDT HDT HFT HHT HQP MI 3000%nat [ADT_D3; AOPDEL2] [false; false].
  { repeat (apply Forall_cons; [first [apply br_err | apply br_hdr] |]); apply Forall_nil. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit6d HTS1 HX1 HA1 HD01 HD11 HF1 HH1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HX1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD01); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD11); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HF1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HH1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [rewrite winsT_LD6 in MU1; exact MU1 | exact WM1].
Qed.

  Lemma q_d3 : forall m0 R m, rfull R -> rtbl WD R RTD3 ->
    ftbl WD spz m TSD -> ftbl WD spa m ATD2 -> ftbl WD ds m D0T2 -> ftbl WD ds m D1T2 -> ftbl WD ff m FTD2 -> ftbl WD (ff / 8) m HTD2 ->
    (df 0%nat m0 /\ Dx m0 m) -> mem_inv asegs m ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AFREE_STUB) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl WD R1 RTD3F /\ ftbl WD spz m1 TSD /\ ftbl WD spa m1 ATD3 /\ ftbl WD ds m1 D0T3 /\ ftbl WD ds m1 D1T3
                  /\ ftbl WD ff m1 FTD2 /\ ftbl WD (ff / 8) m1 HTD2
                  /\ (df 0%nat m0 /\ Dx m0 m1) /\ mem_inv asegs m1 /\ munch (removelast QWD) m m1 /\ wmono asegs m m1)
        (MS R F (Z_to_bv 64 ADT_D3) fc None m (seg_rom asegs)).
Proof.
  intros m0 R m RF HRT HXT HAT HD0T HD1T HFT HHT HQP MI.
  dkrund6 HRT HXT HAT HD0T HD1T HFT HHT HQP MI 3000%nat [AFREE_STUB] (@nil bool).
  { constructor. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit6d HTS1 HX1 HA1 HD01 HD11 HF1 HH1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HX1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD01); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD11); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HF1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HH1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [rewrite winsT_LD6 in MU1; exact MU1 | exact WM1].
Qed.

  Definition dmid_post (RT' : list (reg * expr)) (m0 m : mem) : machine_state -> Prop :=
    fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 AFREE_STUB) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl WD R1 RT' /\ ftbl WD spz m1 TSD /\ ftbl WD spa m1 ATD3 /\ ftbl WD ds m1 D0T3 /\ ftbl WD ds m1 D1T3
                  /\ ftbl WD ff m1 FTD2 /\ ftbl WD (ff / 8) m1 HTD2
                  /\ (df 0%nat m0 /\ Dx m0 m1) /\ mem_inv asegs m1 /\ munch (removelast QWD) m m1 /\ wmono asegs m m1.

  Lemma q_d4 : forall m0 R m, rfull R -> rtbl WD R RTD4 ->
    ftbl WD spz m TSD -> ftbl WD spa m ATD3 -> ftbl WD ds m D0T3 -> ftbl WD ds m D1T3 -> ftbl WD ff m FTD2 -> ftbl WD (ff / 8) m HTD2 ->
    (df 0%nat m0 /\ Dx m0 m) -> mem_inv asegs m ->
    evt asegs (dmid_post RTD4F m0 m) (MS R F (Z_to_bv 64 ADT_D4) fc None m (seg_rom asegs)).
Proof.
  intros m0 R m RF HRT HXT HAT HD0T HD1T HFT HHT HQP MI. unfold dmid_post.
  dkrund6 HRT HXT HAT HD0T HD1T HFT HHT HQP MI 300%nat [AFREE_STUB] (@nil bool).
  { constructor. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit6d HTS1 HX1 HA1 HD01 HD11 HF1 HH1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HX1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD01); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD11); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HF1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HH1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [rewrite winsT_LD6 in MU1; exact MU1 | exact WM1].
Qed.

  Lemma q_d5 : forall m0 R m, rfull R -> rtbl WD R RTD4 ->
    ftbl WD spz m TSD -> ftbl WD spa m ATD3 -> ftbl WD ds m D0T3 -> ftbl WD ds m D1T3 -> ftbl WD ff m FTD2 -> ftbl WD (ff / 8) m HTD2 ->
    (df 0%nat m0 /\ Dx m0 m) -> mem_inv asegs m ->
    evt asegs (dmid_post RTD5F m0 m) (MS R F (Z_to_bv 64 ADT_D5) fc None m (seg_rom asegs)).
Proof.
  intros m0 R m RF HRT HXT HAT HD0T HD1T HFT HHT HQP MI. unfold dmid_post.
  dkrund6 HRT HXT HAT HD0T HD1T HFT HHT HQP MI 300%nat [AFREE_STUB] (@nil bool).
  { constructor. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit6d HTS1 HX1 HA1 HD01 HD11 HF1 HH1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HX1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD01); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD11); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HF1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HH1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [rewrite winsT_LD6 in MU1; exact MU1 | exact WM1].
Qed.

  Lemma q_d6 : forall m0 R m, rfull R -> rtbl WD R RTD4 ->
    ftbl WD spz m TSD -> ftbl WD spa m ATD3 -> ftbl WD ds m D0T3 -> ftbl WD ds m D1T3 -> ftbl WD ff m FTD2 -> ftbl WD (ff / 8) m HTD2 ->
    (df 0%nat m0 /\ Dx m0 m) -> mem_inv asegs m ->
    evt asegs (dmid_post RTD6F m0 m) (MS R F (Z_to_bv 64 ADT_D6) fc None m (seg_rom asegs)).
Proof.
  intros m0 R m RF HRT HXT HAT HD0T HD1T HFT HHT HQP MI. unfold dmid_post.
  dkrund6 HRT HXT HAT HD0T HD1T HFT HHT HQP MI 300%nat [AFREE_STUB] (@nil bool).
  { constructor. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit6d HTS1 HX1 HA1 HD01 HD11 HF1 HH1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HX1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HA1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD01); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HD11); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HF1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HH1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [rewrite winsT_LD6 in MU1; exact MU1 | exact WM1].
Qed.

  Lemma q_d7 : forall m0 R m, rfull R -> rtbl WD R RTD3 ->
    ftbl WD spz m TSD -> ftbl WD spa m [] -> ftbl WD ds m D0T3 -> ftbl WD ds m D1T3 -> ftbl WD ff m FTD2 -> ftbl WD (ff / 8) m HTD2 ->
    ftbl WD fp m [] ->
    (df 0%nat m0 /\ Dx m0 m) -> mem_inv asegs m ->
    evt asegs (fun ms => exists R1 m1, ms = MS R1 F (Z_to_bv 64 ADT_RET) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl WD R1 RTDF /\ ftbl WD fp m1 LTZ
                  /\ (df 0%nat m0 /\ Dx m0 m1) /\ mem_inv asegs m1 /\ munch QWD m m1 /\ wmono asegs m m1)
        (MS R F (Z_to_bv 64 ADT_D7) fc None m (seg_rom asegs)).
Proof.
  intros m0 R m RF HRT HXT HAT HD0T HD1T HFT HHT HLT HQP MI.
  dkrund7 HRT HXT HAT HD0T HD1T HFT HHT HLT HQP MI 3000%nat [ADT_RET] (@nil bool).
  { constructor. }
  intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
  tsplit7d HTS1 HX1 HA1 HD01 HD11 HF1 HH1 HL1.
  cbn [s_pc]. apply evt_done. exists R1, m1. split; [reflexivity|].
  split; [exact RF1|].
  split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
  split; [apply (ftbl_sub _ _ _ _ _ HL1); vm_compute; reflexivity|].
  split; [exact HP1|]. split; [exact HMI1|].
  split; [rewrite winsT_LD7 in MU1; exact MU1 | exact WM1].
Qed.
End DR.
