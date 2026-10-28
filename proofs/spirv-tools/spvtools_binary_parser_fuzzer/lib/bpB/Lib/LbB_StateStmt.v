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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_Own.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition AST_MVA : Z := 0xecf54.
Definition AST_DTOR : Z := 0xed5d8.

Definition AST_MVA_STACK : Z := 256 + AFREE_STACK.

Definition AST_DTOR_STACK : Z := 128 + AFREE_STACK.
Definition ST_SIZE : Z := 240.

Section Stmts.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition st_live_frame (LF : list fframe) (x : Z) : Prop :=
    exists f, In f LF /\ ff_addr f <= x /\ x + ST_SIZE <= ff_addr f + fsz (ff_class f).

  Definition st_mva_tr_ok : Prop := Forall (fun r => trace_ok (as_TR H) APC0_FREE [r]) ST_MVA_DEL_RAS.
  Definition st_dtor_tr_ok : Prop := Forall (fun r => trace_ok (as_TR H) APC0_FREE [r]) ST_DTOR_DEL_RAS.

  Definition st_mva_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : as_St H) (LB0 LBs2 : list block) (LF : list fframe) (st1 st2 : Z) (c1 c2 : stateC) (lo B shi : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block)
                     (XS : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 st1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm_zero fc'
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ Permutation LB' (LB0 ++ LBs2)
      /\ state_repA LB' m' st1 (state_moved c1 c2) /\ state_sh m' (state_moved c1 c2)
      /\ state_repA LB' m' st2 (state_emptied c2)
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LB0 (bv_unsigned sp) ((st1, st1 + ST_SIZE) :: (st2, st2 + ST_SIZE) :: XS) m m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s
      /\ lb_own LB' m'.

  Definition st_mva_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBs1 LBs2 : list block) (LF : list fframe) (st1 st2 : Z) (c1 c2 : stateC)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 AST_MVA) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 st1 -> a1 = Z_to_bv 64 st2 ->
      state_repA LB m st1 c1 -> state_sh m c1 -> state_repA LB m st2 c2 -> state_sh m c2 ->
      Permutation LB (LB0 ++ LBs1 ++ LBs2) -> Permutation (lbl LBs1) (state_blocks c1) -> Permutation (lbl LBs2) (state_blocks c2) ->

      (forall p n, In (p, n) (state_blocks c1) -> n <= 2 ^ 40) ->

      addressable m st1 ST_SIZE -> addressable m st2 ST_SIZE -> st1 + ST_SIZE <= st2 \/ st2 + ST_SIZE <= st1 ->
      (forall b, In b LB -> st1 + ST_SIZE <= blk_addr b \/ blk_addr b + blk_size b <= st1) ->
      (forall b, In b LB -> st2 + ST_SIZE <= blk_addr b \/ blk_addr b + blk_size b <= st2) ->

      st_live_frame LF st1 -> st_live_frame LF st2 \/ (bv_unsigned sp <= st2 /\ st2 + ST_SIZE + 64 <= shi) ->
      st1 + ST_SIZE <= aceil ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AST_MVA_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
      lb_own LB m ->
      st_mva_tr_ok ->
      as_SR H (st_mva_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LBs2 LF st1 st2 c1 c2 lo B shi m mo) (mkCfg msF mo).

  Definition st_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : as_St H) (LB0 : list block) (LF : list fframe) (st : Z) (lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block)
                     (XS : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm_zero fc'
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ Permutation LB' LB0
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LB0 (bv_unsigned sp) ((st, st + ST_SIZE) :: XS) m m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s
      /\ lb_own LB' m'

      /\ wr_at asegs m' st ST_SIZE.

  Definition st_dtor_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBs : list block) (LF : list fframe) (st : Z) (c : stateC)
           (lo B shi : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 AST_DTOR) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 st ->
      state_repA LB m st c -> state_sh m c ->
      Permutation LB (LB0 ++ LBs) -> Permutation (lbl LBs) (state_blocks c) ->
      (forall p n, In (p, n) (state_blocks c) -> n <= 2 ^ 40) ->
      addressable m st ST_SIZE ->
      (forall b, In b LB -> st + ST_SIZE <= blk_addr b \/ blk_addr b + blk_size b <= st) ->
      st_live_frame LF st \/ (bv_unsigned sp <= st /\ st + ST_SIZE + 64 <= shi) ->

      (state_blocks c = [] \/ st + ST_SIZE <= aceil) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->
      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AST_DTOR_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
      lb_own LB m ->
      st_dtor_tr_ok ->
      as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) APC0_FREE (bv_unsigned ra :: map snd CH) ->
      (forall fp ra', In (fp, ra') CH -> bv_unsigned sp + 16 <= fp) ->
      as_SR H (st_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LF st lo B shi m mo) (mkCfg msF mo).
End Stmts.
