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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmFin LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmU3XK LbB_PmU5K.

Definition RT_M0_35 : list (reg * expr) := RT_M0 35.
Definition RT_M0_36 : list (reg * expr) := RT_M0 36.
Definition RT_M0_37 : list (reg * expr) := RT_M0 37.
Definition RT_M0_38 : list (reg * expr) := RT_M0 38.
Definition RT_M0_39 : list (reg * expr) := RT_M0 39.
Definition RT_M0_40 : list (reg * expr) := RT_M0 40.
Definition RT_M0_43 : list (reg * expr) := RT_M0 43.
Definition RT_M0_44 : list (reg * expr) := RT_M0 44.
Definition RT_M0_56 : list (reg * expr) := RT_M0 56.
Definition RT_M0_61 : list (reg * expr) := RT_M0 61.
Definition RT_M0_77 : list (reg * expr) := RT_M0 77.
Definition RT_M0_78 : list (reg * expr) := RT_M0 78.
Definition RT_M0_87 : list (reg * expr) := RT_M0 87.
Definition RT_M0_89 : list (reg * expr) := RT_M0 89.
Definition RT_M0_90 : list (reg * expr) := RT_M0 90.
Definition RT_M0_91 : list (reg * expr) := RT_M0 91.
Definition RT_M0_92 : list (reg * expr) := RT_M0 92.
Definition RT_M0_103 : list (reg * expr) := RT_M0 103.
Definition RT_M0_104 : list (reg * expr) := RT_M0 104.

Definition RT_PM_U5M_1_35_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 104); (11%bv, ELit 49); (18%bv, ELit 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_36_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 104); (11%bv, ELit 49); (18%bv, ELit 36); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_37_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 104); (11%bv, ELit 49); (18%bv, ELit 37); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_38_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 104); (11%bv, ELit 49); (18%bv, ELit 38); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_39_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 104); (11%bv, ELit 49); (18%bv, ELit 39); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_40_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 104); (11%bv, ELit 49); (18%bv, ELit 40); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_43_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 35); (11%bv, ELit 989224); (18%bv, ELit 43); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_44_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 40); (11%bv, ELit 988408); (18%bv, ELit 44); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_56_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 35); (11%bv, ELit 989228); (18%bv, ELit 56); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_61_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 35); (11%bv, ELit 989228); (18%bv, ELit 61); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_77_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 35); (11%bv, ELit 989228); (18%bv, ELit 77); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_78_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 77); (11%bv, ELit 989212); (18%bv, ELit 78); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_87_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 86); (11%bv, ELit 989220); (18%bv, ELit 87); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_89_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 35); (11%bv, ELit 989228); (18%bv, ELit 89); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_90_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 35); (11%bv, ELit 989228); (18%bv, ELit 90); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_91_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 35); (11%bv, ELit 989228); (18%bv, ELit 91); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_92_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 91); (11%bv, ELit 989204); (18%bv, ELit 92); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_103_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 104); (11%bv, ELit 49); (18%bv, ELit 103); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_1_104_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 103); (11%bv, ELit 49); (18%bv, ELit 104); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section U5Ma.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTbAPmU5Ma_0 : list (Z * expr) := [(32, EAlu ALU_ADD (EVar 33) (ELit 5472)); (40, EAlu ALU_ADD (EVar 33) (ELit 4496)); (48, EAlu ALU_ADD (EVar 33) (ELit 2048)); (56, EAlu ALU_ADD (EVar 33) (ELit 4032)); (64, EAlu ALU_ADD (EVar 33) (ELit 3056)); (72, EAlu ALU_ADD (EVar 33) (ELit 3008)); (80, EAlu ALU_ADD (EVar 33) (ELit 5008)); (88, EAlu ALU_ADD (EVar 33) (ELit 32)); (96, EAlu ALU_ADD (EVar 33) (ELit 4000)); (104, ELit 65535); (112, EAlu ALU_ADD (EVar 33) (ELit 6000)); (120, EAlu ALU_ADD (EVar 33) (ELit 6464)); (128, EAlu ALU_ADD (EVar 33) (ELit 7952)); (136, EAlu ALU_ADD (EVar 33) (ELit 3024)); (144, EAlu ALU_ADD (EVar 33) (ELit 656)); (152, EAlu ALU_ADD (EVar 33) (ELit 192)); (160, EAlu ALU_ADD (EVar 33) (ELit 1120)); (168, EAlu ALU_ADD (EVar 33) (ELit 3520)); (176, ELit 262140); (184, EAlu ALU_ADD (EVar 32) (ELit 176)); (192, EAlu ALU_ADD (EVar 33) (ELit 5937)); (200, EAlu ALU_ADD (EVar 33) (ELit 4544)); (208, EAlu ALU_ADD (EVar 33) (ELit 2512)); (216, EAlu ALU_ADD (EVar 33) (ELit 1584)); (224, EAlu ALU_ADD (EVar 33) (ELit 3536)); (232, EAlu ALU_ADD (EVar 33) (ELit 8576)); (240, EAlu ALU_ADD (EVar 33) (ELit 7456)); (248, EAlu ALU_ADD (EVar 33) (ELit 4528)); (256, EAlu ALU_ADD (EVar 33) (ELit 7488)); (264, EAlu ALU_ADD (EVar 33) (ELit 10640)); (272, EAlu ALU_ADD (EVar 32) (ELit 96)); (280, EAlu ALU_ADD (EVar 33) (ELit 9056)); (288, EAlu ALU_ADD (EVar 33) (ELit 11104)); (296, EAlu ALU_ADD (EVar 33) (ELit 8544)); (304, EAlu ALU_ADD (EVar 33) (ELit 9060)); (312, EAlu ALU_ADD (EVar 33) (ELit 2976)); (320, EAlu ALU_ADD (EVar 33) (ELit 5936)); (328, EAlu ALU_ADD (EVar 33) (ELit 10176)); (336, EAlu ALU_ADD (EVar 33) (ELit 8512)); (344, EAlu ALU_ADD (EVar 33) (ELit 8016)); (352, EAlu ALU_ADD (EVar 33) (ELit 7424)); (360, EAlu ALU_ADD (EVar 32) (ELit 92)); (368, EAlu ALU_ADD (EVar 32) (ELit 93)); (376, EAlu ALU_ADD (EVar 32) (ELit 40)); (384, EAlu ALU_ADD (EVar 33) (ELit 6928)); (392, EAlu ALU_ADD (EVar 33) (ELit 6960)); (400, EAlu ALU_ADD (EVar 33) (ELit 9616)); (408, EAlu ALU_ADD (EVar 32) (ELit 216)); (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (424, EAlu ALU_ADD (EVar 33) (ELit 96)); (432, EAlu ALU_ADD (EVar 32) (ELit 232)); (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (448, EAlu ALU_ADD (EVar 32) (ELit 224)); (456, EAlu ALU_ADD (EVar 33) (ELit 64)); (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (472, EAlu ALU_ADD (EVar 33) (ELit 176)); (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (488, EAlu ALU_ADD (EVar 33) (ELit 8480)); (496, EAlu ALU_ADD (EVar 33) (ELit 10112)); (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (512, EAlu ALU_ADD (EVar 32) (ELit 88)); (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (528, EAlu ALU_ADD (EVar 32) (ELit 48)); (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (544, ELit 2305843009213693952); (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (560, EAlu ALU_ADD (EVar 32) (ELit 240)); (568, EVar 33); (576, EVar 33); (584, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (592, EAlu ALU_ADD (EVar 32) (ELit 56)); (600, EAlu ALU_ADD (EVar 32) (ELit 272)); (608, EAlu ALU_ADD (EVar 33) (ELit 9050)); (616, ELit 2147450880); (624, EAlu ALU_ADD (EVar 33) (ELit 9040)); (632, EAlu ALU_ADD (EVar 32) (ELit 264)); (640, EAlu ALU_ADD (EVar 33) (ELit 9136)); (648, EVar 32); (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_ADD (EVar 32) (ELit 72)); (680, EVar 33); (688, EAlu ALU_ADD (EVar 33) (ELit 10112)); (696, EAlu ALU_ADD (EVar 33) (ELit 9136)); (704, EVar 32); (712, EAlu ALU_ADD (EVar 33) (ELit 9120)); (720, EAlu ALU_ADD (EVar 33) (ELit 9040))].
  Lemma pm_u5m_1_35 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_35 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 35)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 35)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_35_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_35_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 35)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_36 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_36 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 36)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 36)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_36_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_36_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 36)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_37 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_37 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 37)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 37)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_37_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_37_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 37)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_38 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_38 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 38)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 38)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_38_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_38_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 38)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_39 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_39 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 39)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 39)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_39_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_39_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 39)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_40 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_40 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 40)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 40)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_40_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_40_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 40)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_43 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_43 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 35)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_43_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_43_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EVar 33, 116, 120)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 35)]). { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf1 | reflexivity | cbn [firstn]; apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite EFc; reflexivity | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 116 + i) with (wa_ff w + (116 + i)) by lia; apply FW2; lia | reflexivity | exact Logic.I | reflexivity]. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_44 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_44 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 40)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_44_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_44_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EVar 33, 116, 120)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 40)]). { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf1 | reflexivity | cbn [firstn]; apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite EFc; reflexivity | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 116 + i) with (wa_ff w + (116 + i)) by lia; apply FW2; lia | reflexivity | exact Logic.I | reflexivity]. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_56 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_56 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 56)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 56)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_56_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_56_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 56)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_61 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_61 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 61)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 61)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_61_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_61_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 61)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_77 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_77 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 77)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 77)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_77_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_77_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 77)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_78 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_78 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 77)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_78_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_78_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EVar 33, 116, 120)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 77)]). { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf1 | reflexivity | cbn [firstn]; apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite EFc; reflexivity | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 116 + i) with (wa_ff w + (116 + i)) by lia; apply FW2; lia | reflexivity | exact Logic.I | reflexivity]. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_87 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_87 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 86)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_87_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_87_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EVar 33, 116, 120)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 86)]). { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf1 | reflexivity | cbn [firstn]; apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite EFc; reflexivity | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 116 + i) with (wa_ff w + (116 + i)) by lia; apply FW2; lia | reflexivity | exact Logic.I | reflexivity]. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_89 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_89 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 89)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 89)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_89_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_89_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 89)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_90 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_90 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 90)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 90)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_90_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_90_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 90)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_91 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_91 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 91)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 91)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_91_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_91_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 91)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_92 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_92 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 91)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_92_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_92_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EVar 33, 116, 120)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 91)]). { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf1 | reflexivity | cbn [firstn]; apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite EFc; reflexivity | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 116 + i) with (wa_ff w + (116 + i)) by lia; apply FW2; lia | reflexivity | exact Logic.I | reflexivity]. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_103 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_103 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 103)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 103)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 C116 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_103_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_103_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 103)]). { subst M1. replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity). cbn [mem_denot]. exact C116. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

  Lemma pm_u5m_1_104 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf14cc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_M0_104 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf182c) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ML -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 103)] -> ffkeepX w [(116, 4)] m m1 -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q
           OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ (@nil word))) m [KImg 147280 147480]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ (@nil word))) OK (env_world_seed H w R (@nil word))) as EF.
      apply Forall_cons; [| apply Forall_nil].
      { apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia]. }
    }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KImg 147280 147480] HK1 40%nat [0xf182c] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Ma_0 (@nil (Z * expr)) RT_PM_U5M_1_104_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = (wa_gp w)) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = (wa_tp w)) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U5M_1_104_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc. destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (E32c & E33c & _). pose proof (pmw_bounds H w OK) as BNDc. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2. assert (FK : ffkeepX w [(116, 4)] m M1). { pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m (s_log SSr) [(EVar 33, 116, 120)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc; cbn [num_wins map] in MUc; rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33c ltac:(lia)) in MUc; rewrite ?EFc in MUc; apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)); repeat (apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |]); apply Forall_nil. } assert (CT : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 103)]). { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf1 | reflexivity | cbn [firstn]; apply Forall_nil | unfold estart; cbn [a_base a_off]; rewrite EFc; reflexivity | split; [lia|]; split; [lia|]; intros i Hi; replace (wa_ff w + 116 + i) with (wa_ff w + (116 + i)) by lia; apply FW2; lia | reflexivity | exact Logic.I | reflexivity]. } eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ML HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1); first [ rtf HT1 | exact CT | exact FK | (rewrite (HR1 21%bv); reflexivity) | (intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0]) ].
  Qed.

End U5Ma.
