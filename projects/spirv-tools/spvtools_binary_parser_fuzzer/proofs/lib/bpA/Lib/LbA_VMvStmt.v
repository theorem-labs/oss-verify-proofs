(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Own.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition AVMOVE_1 : Z := 0xf46d8.   Definition AVMOVE_DEL_RA_1 : Z := 0xf47b8.
Definition AVMOVE_2 : Z := 0xf48e4.   Definition AVMOVE_DEL_RA_2 : Z := 0xf49c4.
Definition AVMOVE_3 : Z := 0xf4af0.   Definition AVMOVE_DEL_RA_3 : Z := 0xf4bd0.

Definition AVMOVE_STACK : Z := 80 + AFREE_STACK.

Section VMv.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition vmove_LB (LB : list block) (pid : bptr) (b1 : Z) : list block :=
    if b1 =? 0 then LB else as_lb_remove H pid LB.

  Definition vmove_X (v w b1 c1 : Z) : list (Z * Z) :=
    [(v, v + 24); (w, w + 24)] ++ (if b1 =? 0 then [] else [(b1, c1); (sh b1, sh b1 + nsh (c1 - b1))]).

  Definition vmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (pid : bptr) (v w b1 c1 b2 e2 c2 lo B shi : Z) (errv : word)
      (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                       t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
      /\ xpres H (vmove_LB LB pid b1) (bv_unsigned sp) (vmove_X v w b1 c1) m m'
      /\ as_RHEAP H s' (vmove_LB LB pid b1) m' /\ lb_own (vmove_LB LB pid b1) m'
      /\ rw_cells asegs m' v [C8 (wz b2); C8 (wz e2); C8 (wz c2)] /\ rw_cells asegs m' w [C8 (wz 0); C8 (wz 0); C8 (wz 0)]
      /\ SHAD m' v (repeat (b8 0) 3) /\ SHAD m' w (repeat (b8 0) 3)
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - as_Cf H (c1 - b1).

  Definition vhdr_ok (LF : list fframe) (x : Z) (m : mem) : Prop :=
    x mod 8 = 0 /\ SHAD m x (repeat (b8 0) 3)
    /\ exists f, In f LF /\ ff_addr f <= x /\ x + 24 <= ff_addr f + fsz (ff_class f).

  Definition vhdr_w_ok (LF : list fframe) (SP shi x : Z) (m : mem) : Prop :=
    x mod 8 = 0 /\ SHAD m x (repeat (b8 0) 3)
    /\ ((exists f, In f LF /\ ff_addr f <= x /\ x + 24 <= ff_addr f + fsz (ff_class f)) \/ (SP <= x /\ x + 24 + 64 <= shi)).

  Definition vmove_stmt_at (entry del_ra : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (pid : bptr) (v w b1 e1 c1 b2 e2 c2 lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 v -> a1 = Z_to_bv 64 w ->

      rw_cells asegs m v [C8 (wz b1); C8 (wz e1); C8 (wz c1)] -> vhdr_ok LF v m ->
      rw_cells asegs m w [C8 (wz b2); C8 (wz e2); C8 (wz c2)] -> vhdr_w_ok LF (bv_unsigned sp) shi w m ->
      (v + 24 <= w \/ w + 24 <= v) ->

      (b1 = 0 -> e1 = 0 /\ c1 = 0) ->
      (b1 <> 0 -> In (pid, b1, c1 - b1) LB /\ b1 <= e1 <= c1 /\ c1 - b1 <= 2 ^ 40 /\ SHAD m b1 (cc_gen (c1 - b1) (e1 - b1))
                  /\ (b1 + (c1 - b1) <= v \/ v + 24 <= b1) /\ (b1 + (c1 - b1) <= w \/ w + 24 <= b1)) ->
      lb_own LB m ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_Cf H (c1 - b1) <= as_AL H s ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AVMOVE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      ACONST m -> as_RFS H LF m -> stack0 m lo shi -> bv_unsigned sp <= shi ->

      (b1 <> 0 -> trace_ok (as_TR H) APC0_FREE [del_ra]) ->
      as_SR H (vmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF pid v w b1 c1 b2 e2 c2 lo B shi errv m mo)
        (mkCfg msF mo).

  Definition vmove_stmtA : Prop :=
    vmove_stmt_at AVMOVE_1 AVMOVE_DEL_RA_1 /\ vmove_stmt_at AVMOVE_2 AVMOVE_DEL_RA_2 /\ vmove_stmt_at AVMOVE_3 AVMOVE_DEL_RA_3.
End VMv.
