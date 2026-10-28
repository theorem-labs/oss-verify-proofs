(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt.
Import ListNotations.
Open Scope Z_scope.

Definition BIW32_ENTRY : Z := 0xfc65c.
Definition BIW32_STACK : Z := 64 + V4_STACK.

Section BiW32.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition biw32_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (it v b cap x : Z) (xs : list Z) (pid : bptr) (lo B shi : Z)
      (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (b' cap' : Z),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 it) a1 a2 a3 a4 a5 a6 a7
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ vec32A LB' m' v b' (xs ++ [x]) cap' /\ as_RHEAP H s' LB' m'
      /\ SHAD m' b' (cc_gen (4 * cap') (4 * (Zlen xs + 1)))
      /\ addressable m' v 24 /\ wr_at asegs m' v 24 /\ lb_own LB' m'
      /\ ((Zlen xs < cap /\ b' = b /\ cap' = cap /\ LB' = LB
           /\ xpres H LB (bv_unsigned sp) [(v, v + 24); (b, b + 4 * cap); (sh b, sh b + nsh (4 * cap))] m m'
           /\ as_AL H s' >= as_AL H s)
          \/ (Zlen xs = cap /\ cap' = v4_newcap cap
              /\ (exists pid', LB' = v4_newLB H LB b pid pid' b' (4 * cap') /\ ablock_range H b' (4 * cap'))
              /\ xpres H LB (bv_unsigned sp) ((v, v + 24) :: v4_oldx b (4 * cap)) m m'
              /\ as_AL H s' >= as_AL H s - (as_Cm H (4 * cap') + as_Cf H (4 * cap))))
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

  Definition biw32_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (it v b cap src x : Z) (xs : list Z) (pid : bptr)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 BIW32_ENTRY) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 it -> a1 = Z_to_bv 64 src ->
      fldA m it 8 v -> it mod 8 = 0 -> addressable m it 8 -> aapp it 8 ->
      vec32A LB m v b xs cap -> v mod 8 = 0 ->
      addressable m v 24 -> obj_win H LB LF (bv_unsigned sp) lo v 24 ->
      ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
      wr_at asegs m v 24 -> lb_own LB m ->
      v4_oldblk LB b cap pid -> (0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * Zlen xs))) ->
      4 * cap <= 2 ^ 26 -> (Zlen xs = cap -> 4 * v4_newcap cap <= 2 ^ 26) ->

      src4_keep_x H LB (bv_unsigned sp) (if b =? 0 then [] else [(sh b, sh b + nsh (4 * cap))]) m src x ->
      0 <= x < 2 ^ 32 -> src mod 4 = 0 -> 0 <= src -> src + 4 <= 2 ^ 47 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      (Zlen xs = cap -> as_alloc_ok H s LB (4 * v4_newcap cap)
                        /\ as_Cm H (4 * v4_newcap cap) + as_Cf H (4 * cap) <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [v4_del_ra V32_SLOW_RREF] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIW32_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_SR H (biw32_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF it v b cap x xs pid lo B shi m mo)
        (mkCfg msF mo).

End BiW32.
