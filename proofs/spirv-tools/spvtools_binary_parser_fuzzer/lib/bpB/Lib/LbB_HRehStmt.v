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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_Own LbB_ContStmt LbB_HEmpStmt.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition reh_entry (E : emp_inst) : Z := emp_entry E + 0x950.

Definition AREH_STACK : Z := 64 + AOPNEW_STACK.

Section Stmts.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition reh_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : as_St H) (LB0 : list block) (LF : list fframe) (obj n : Z) (ents : list (Z * (Z * Z)))
      (lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' LBm' : list block)
                     (F' : bvmap 5 word) (fc' : bv 32) (bl' : Z) (ents' : list (Z * (Z * Z))),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm_zero fc'
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B

      /\ umapx MI_A 24 (nval24 ASEGS) (lbl LB') m' obj bl' n ents' /\ umap_sh m' 24 (bl', n, ents') /\ Permutation ents' ents
      /\ addressable m' obj 40 /\ wr_at asegs m' obj 40

      /\ as_RHEAP H s' LB' m' /\ Permutation LB' (LB0 ++ LBm') /\ Permutation (lbl LBm') (umap_blocks 24 bl' n ents')
      /\ lb_own LBm' m'
      /\ xpres H LB0 (bv_unsigned sp) [(obj, obj + 40)] m m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - ICM (8 * n).

  Definition reh_stmt (E : emp_inst) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe)
           (obj bl bc : Z) (ents : list (Z * (Z * Z))) (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (reh_entry E)) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 obj -> a1 = Z_to_bv 64 (bseq_next bc) ->

      umapx MI_A 24 (nval24 ASEGS) (lbl LB) m obj bl bc ents -> umap_sh m 24 (bl, bc, ents) ->
      Permutation LB (LB0 ++ LBm) -> Permutation (lbl LBm) (umap_blocks 24 bl bc ents) ->
      addressable m obj 40 -> wr_at asegs m obj 40 -> map_live_frame LF obj -> obj + 40 <= aceil ->
      (forall b, In b LB -> obj + 40 <= blk_addr b \/ blk_addr b + blk_size b <= obj) ->
      bc <> BSEQ_LAST ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
      lb_small LB + nsmall (8 * bseq_next bc) <= RT_SMALL_MAX -> Z.of_nat (length LB) + 1 <= RT_CNT_MAX ->
      nlarge LB + nlg (8 * bseq_next bc) <= RT_LARGE_MAX -> ICM (8 * bseq_next bc) <= as_AL H s ->
      trace_ok (as_TR H) APC0_FREE [emp_del_ra E] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AREH_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
      lb_own LBm m ->
      as_SR H (reh_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LF obj (bseq_next bc) ents lo B shi m mo) (mkCfg msF mo).
End Stmts.
