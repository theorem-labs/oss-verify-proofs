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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_Own LbB_ContStmt.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Record emp_inst : Type := EMPI { emp_entry : Z; emp_del_ra : Z }.
Definition EMP_U32 : emp_inst := EMPI 0xfa354 0xfad2c.
Definition EMP_EXT : emp_inst := EMPI 0xfb648 0xfc020.

Definition AEMP_STACK : Z := 256 + AOPNEW_STACK.

Section Stmts.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition map_live_frame (LF : list fframe) (x : Z) : Prop :=
    exists f, In f LF /\ ff_addr f <= x /\ x + 40 <= ff_addr f + fsz (ff_class f).

  Definition emp_src (LB0 : list block) (spz obj a n : Z) : Prop :=
    aclient_range H LB0 spz a n /\ aclient_range H LB0 spz (sh a) (nsh n) /\ apart a n obj 40.

  Definition emp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z)))
      (lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' LBm' : list block)
                     (F' : bvmap 5 word) (fc' : bv 32) (p v bl' bc' : Z) (ents' : list (Z * (Z * Z))) (inserted rehashed : bool),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (b2z inserted)) a2 a3 a4 a5 a6 a7
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm_zero fc'
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B

      /\ umapx MI_A 24 (nval24 ASEGS) (lbl LB') m' obj bl' bc' ents' /\ umap_sh m' 24 (bl', bc', ents')
      /\ addressable m' obj 40 /\ wr_at asegs m' obj 40
      /\ In (p, (key, v)) ents'
      /\ (inserted = false -> ents' = ents /\ rehashed = false)
      /\ (inserted = true -> v = 0 /\ Permutation ents' ((p, (key, 0)) :: ents))
      /\ (rehashed = false -> bl' = bl /\ bc' = bc)
      /\ (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc)

      /\ as_RHEAP H s' LB' m' /\ Permutation LB' (LB0 ++ LBm') /\ Permutation (lbl LBm') (umap_blocks 24 bl' bc' ents')
      /\ lb_own LBm' m'
      /\ xpres H LB0 (bv_unsigned sp) [(obj, obj + 40)] m m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - (if rehashed then ICM (8 * bc') else 0).

  Definition emp_stmt (E : emp_inst) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe)
           (obj bl bc keyp tupp keyp2 key : Z) (ents : list (Z * (Z * Z))) (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (emp_entry E)) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 obj -> a1 = Z_to_bv 64 keyp -> a3 = Z_to_bv 64 tupp ->

      umapx MI_A 24 (nval24 ASEGS) (lbl LB) m obj bl bc ents -> umap_sh m 24 (bl, bc, ents) ->
      Permutation LB (LB0 ++ LBm) -> Permutation (lbl LBm) (umap_blocks 24 bl bc ents) ->
      addressable m obj 40 -> wr_at asegs m obj 40 -> map_live_frame LF obj -> obj + 40 <= aceil ->
      (forall b, In b LB -> obj + 40 <= blk_addr b \/ blk_addr b + blk_size b <= obj) ->

      fldA m keyp 4 key -> accessible m keyp 4 -> emp_src LB0 (bv_unsigned sp) obj keyp 4 ->
      fldA m tupp 8 keyp2 -> accessible m tupp 8 -> emp_src LB0 (bv_unsigned sp) obj tupp 8 ->
      fldA m keyp2 4 key -> accessible m keyp2 4 -> emp_src LB0 (bv_unsigned sp) obj keyp2 4 ->
      keyp mod 4 = 0 -> tupp mod 8 = 0 -> keyp2 mod 4 = 0 -> 0 <= key < 2 ^ 32 ->

      Zlength ents + 1 < 2 ^ 24 -> bc <> BSEQ_LAST ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
      lb_small LB + 24 + nsmall (8 * bseq_next bc) <= RT_SMALL_MAX -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX ->
      nlarge LB + nlg (8 * bseq_next bc) <= RT_LARGE_MAX ->
      ((bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [emp_del_ra E] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AEMP_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
      lb_own LBm m ->
      as_SR H (emp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LF obj bl bc key ents lo B shi m mo) (mkCfg msF mo).
End Stmts.
