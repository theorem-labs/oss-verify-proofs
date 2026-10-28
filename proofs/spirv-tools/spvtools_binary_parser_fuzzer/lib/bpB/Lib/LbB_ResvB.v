(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_Own LbB_ContStmt.

Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Record rv_consts : Type := RVC { rv_entry : Z; rv_del_ra : Z }.
Definition RESV_W32 : rv_consts := RVC 0xec634 0xec748.
Definition RESV_TYP : rv_consts := RVC 0xec788 0xec89c.
Definition RESV_OPND_ENTRY : Z := 0xec4ac.
Definition RESV_OPND_DEL_RA : Z := 0xec5f0.
Definition RESV_STACK : Z := 96 + AOPNEW_STACK.

Section ResvB.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition resv32_post (c : rv_consts) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (fc : bv 32) (s : as_St H) (LB LBo : list block) (LF : list fframe) (v b : Z) (xs : list Z) (cap k : Z) (pid : bptr)
      (lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (pid' : bptr) (b' cap' : Z),
      let LB' := if k <=? cap then LB else v4_newLB H LB b pid pid' b' (4 * k) in
      let LBo' := if k <=? cap then LBo else v4_newLB H LBo b pid pid' b' (4 * k) in
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) ((v, v + 24) :: v4_oldx b (4 * cap)) m m'
      /\ (k <= cap -> b' = b /\ cap' = cap /\ as_AL H s' >= as_AL H s
                      /\ (0 < cap -> SHAD m' b (cc_gen (4 * cap) (4 * Zlen xs))))
      /\ (cap < k -> cap' = k /\ ablock_range H b' (4 * k) /\ SHAD m' b' (cc_gen (4 * k) (4 * Zlen xs))
                     /\ as_AL H s' >= as_AL H s - (as_Cm H (4 * k) + as_Cf H (4 * cap)))
      /\ as_RHEAP H s' LB' m' /\ vec32A LB' m' v b' xs cap'
      /\ addressable m' v 24 /\ wr_at asegs m' v 24 /\ lb_own LBo' m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

  Definition resv32_stmt (c : rv_consts) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LBo : list block) (LF : list fframe) (v b : Z) (xs : list Z) (cap k : Z) (pid : bptr)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (rv_entry c)) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 k ->
      vec32A LB m v b xs cap -> v mod 8 = 0 ->
      addressable m v 24 -> obj_win H LB LF (bv_unsigned sp) lo v 24 ->
      ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
      wr_at asegs m v 24 -> lb_own LBo m -> (forall bb, In bb LBo -> In bb LB) -> List.NoDup (map blk_id LBo) ->
      v4_oldblk LBo b cap pid -> (0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * Zlen xs))) ->
      0 <= k -> 4 * k <= 2 ^ 26 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      (cap < k -> as_alloc_ok H s LB (4 * k) /\ as_Cm H (4 * k) + as_Cf H (4 * cap) <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [rv_del_ra c] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - RESV_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_SR H (resv32_post c ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBo LF v b xs cap k pid lo B shi m mo)
        (mkCfg msF mo).

  Definition resv_opnd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB LBo : list block) (LF : list fframe) (v b n cap k : Z) (pid : bptr) (lo B shi : Z)
      (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (pid' : bptr) (b' cap' : Z),
      let LB' := if k <=? cap then LB else v4_newLB H LB b pid pid' b' (OPND_SZ * k) in
      let LBo' := if k <=? cap then LBo else v4_newLB H LBo b pid pid' b' (OPND_SZ * k) in
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) ((v, v + 24) :: v4_oldx b (OPND_SZ * cap)) m m'
      /\ (k <= cap -> b' = b /\ cap' = cap /\ as_AL H s' >= as_AL H s
                      /\ (0 < cap -> SHAD m' b (cc_gen (OPND_SZ * cap) (OPND_SZ * n))))
      /\ (cap < k -> cap' = k /\ ablock_range H b' (OPND_SZ * k) /\ SHAD m' b' (cc_gen (OPND_SZ * k) (OPND_SZ * n))
                     /\ as_AL H s' >= as_AL H s - (as_Cm H (OPND_SZ * k) + as_Cf H (OPND_SZ * cap)))
      /\ as_RHEAP H s' LB' m' /\ vopndA LB' m' v b' n cap'
      /\ addressable m' v 24 /\ wr_at asegs m' v 24 /\ lb_own LBo' m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

  Definition resv_opnd_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LBo : list block) (LF : list fframe) (v b n cap k : Z) (pid : bptr)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 RESV_OPND_ENTRY) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 k ->
      vopndA LB m v b n cap -> v mod 8 = 0 ->
      addressable m v 24 -> obj_win H LB LF (bv_unsigned sp) lo v 24 ->
      ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
      wr_at asegs m v 24 -> lb_own LBo m -> (forall bb, In bb LBo -> In bb LB) -> List.NoDup (map blk_id LBo) ->
      ((b = 0 /\ cap = 0) \/ (0 < cap /\ In (pid, b, OPND_SZ * cap) LBo)) ->
      (0 < cap -> SHAD m b (cc_gen (OPND_SZ * cap) (OPND_SZ * n))) ->
      0 <= k -> OPND_SZ * k <= 2 ^ 26 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      (cap < k -> as_alloc_ok H s LB (OPND_SZ * k) /\ as_Cm H (OPND_SZ * k) + as_Cf H (OPND_SZ * cap) <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [RESV_OPND_DEL_RA] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - RESV_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_SR H (resv_opnd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBo LF v b n cap k pid lo B shi m mo)
        (mkCfg msF mo).
End ResvB.
