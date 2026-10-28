(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_DStat LbB_DiagStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Stmt.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Definition exhausted_stmtA11 : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
           (this pcons nwords widx icount inst_offset opcode type : Z),
      ds_pre H LINV AEXHAUSTED ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc msF m mo s LB [] LF CH (2 ^ 20) lo B shi errv ->

      lo <= bv_unsigned sp - (ADS_STACK + 1024) -> (length LF + S DS_FRAMES <= AFS_MAXLIVE_BP)%nat ->
      lb_small LB + 3 * 64512 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 3 <= RT_CNT_MAX -> nlarge LB + 3 <= RT_LARGE_MAX ->
      pf_ok (as_TR H) DS_EXH_PF (bv_unsigned ra) CH ->
      a0 = Z_to_bv 64 this -> a1 = Z_to_bv 64 inst_offset -> a2 = Z_to_bv 64 opcode -> a3 = Z_to_bv 64 type ->
      0 <= inst_offset < 2 ^ 63 -> 0 <= opcode < 2 ^ 16 -> 0 <= type < 2 ^ 32 ->
      ds_obj H LF m (bv_unsigned sp) this 288 -> obj_inframe LF this 288 ->
      rw_cells asegs m (this + 8) [C8 (Z_to_bv 64 pcons)] -> rw_cells asegs m (this + 56) [C8 (Z_to_bv 64 nwords)] ->
      rw_cells asegs m (this + 72) [C8 (Z_to_bv 64 widx)] -> rw_cells asegs m (this + 80) [C8 (Z_to_bv 64 icount)] ->
      0 <= nwords < 2 ^ 63 -> 0 <= widx < 2 ^ 63 -> 0 <= icount < 2 ^ 63 ->
      ds_obj H LF m (bv_unsigned sp) pcons 48 -> obj_inframe LF pcons 48 -> rw_cells asegs m (pcons + 32) [C8 (Z_to_bv 64 0)] ->
      pcons mod 16 = 0 ->
      as_SR H (ds_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LB LF
                       [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] (2 ^ 20) lo B shi m mo
                       (Some (2 ^ 64 - 4)) (fun LB' m' => Permutation LB' LB))
              (mkCfg msF mo).
End Stmt.
