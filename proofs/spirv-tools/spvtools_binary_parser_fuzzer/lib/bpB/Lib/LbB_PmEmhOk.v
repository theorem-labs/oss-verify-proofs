From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_Own LbB_HEmpStmt LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmEmhW.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmEmh LbB_PmEmhI LbB_PmEmhL1 LbB_PmEmhL2a LbB_PmEmhL2b.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HEmp.

Section EmhOk.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Theorem emh_ext_ok : emh_stmt H EMH_EXT.
  Proof using HHbp.
    apply (emh_ok H HHbp); [exact (emh_to_B H HHbp EMH_EXT ltac:(vm_compute; reflexivity) ltac:(cbn; lia) emh_A_ext emh_B_ext)|].
    exact (emh_from_B H HHbp EMH_EXT (emh_B_to_C H HHbp EMH_EXT ltac:(vm_compute; reflexivity) (LbB_HEmp.emp_ext_okA H HHbp)) (emh_C_to_post H HHbp EMH_EXT ltac:(vm_compute; reflexivity) emh_C_ext emh_ret_ext)).
  Qed.

  Theorem emh_u32_ok : emh_stmt H EMH_U32.
  Proof using HHbp.
    apply (emh_ok H HHbp); [exact (emh_to_B H HHbp EMH_U32 ltac:(vm_compute; reflexivity) ltac:(cbn; lia) emh_A_u32 emh_B_u32)|].
    exact (emh_from_B H HHbp EMH_U32 (emh_B_to_C H HHbp EMH_U32 ltac:(vm_compute; reflexivity) (LbB_HEmp.emp_u32_okA H HHbp)) (emh_C_to_post H HHbp EMH_U32 ltac:(vm_compute; reflexivity) emh_C_u32 emh_ret_u32)).
  Qed.
End EmhOk.
