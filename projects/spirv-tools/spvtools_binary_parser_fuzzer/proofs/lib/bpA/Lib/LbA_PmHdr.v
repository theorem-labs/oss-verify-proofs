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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition SH_P48 : expr := EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 48)) (ELit 3)) (ELit SHBASE).
Definition SH_P56 : expr := EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 56)) (ELit 3)) (ELit SHBASE).
Definition SH_FF : expr := EAlu ALU_ADD (EAlu ALU_SRL (EVar WV_FF) (ELit 3)) (ELit SHBASE).
Definition WADD (n : N) (k : Z) : expr := EAlu ALU_ADD (EVar n) (ELit k).

Definition RT_ED284 : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, EVar WV_FF); (19%bv, EVar WV_P);
   (20%bv, SH_FF); (21%bv, WADD WV_P 48); (22%bv, ELit SHBASE); (26%bv, SH_P48); (27%bv, EVar WV_FF)].
Definition TBL_ED284 : list (Z * expr) := [(1056, EVar WV_FF)].

Definition RT_ED90C : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (10%bv, EVar WV_WORDS); (11%bv, EVar WV_N);
   (18%bv, ELit SHBASE); (19%bv, EVar WV_P); (20%bv, SH_FF); (21%bv, WADD WV_P 48); (22%bv, ELit SHBASE);
   (23%bv, WADD WV_FF 13584); (24%bv, WADD WV_FF 14640); (25%bv, WADD WV_FF 11488); (26%bv, SH_P48); (27%bv, WADD WV_P 56)].
Definition TBL_ED90C : list (Z * expr) := [(1056, EVar WV_FF); (968, EVar WV_FF); (1040, EVar WV_FF); (1048, SH_P56)].

Section Hdr.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

End Hdr.
