(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from P/SO_fprintf.v (module SO_iface): so_fprintf_diag_stmt, so_exit_stmt, so_diag_str_stmt and so_diag_usage_stmt restated over BudgetWit.Rzb.rzb. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_fmt_fp_lib F_pad Exit Printf_model F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Definition so_fprintf_diag_stmt_b : Prop :=
  forall (d : diag_msg)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (canary : word) (K : TSet),
    MOK mo -> chan_ok mo 2 ->
    stderr_wfile m ->
    a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) -> diag_small d ->
    stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) ->
    ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
    K [] ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
        munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' -> wmono psegs m m' -> mem_inv psegs m' ->
        frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
        stk psegs m' lo (bv_unsigned sp) -> stderr_wfile m' -> ssp_cells m' canary ->
        rzb psegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                             Ft (ret_pc ra) fc' None m' (seg_rom psegs)) mo) K) ->
    rzb psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x174f0) fc None m (seg_rom psegs)) mo)
        (t_emit (W 2 (fdiag_bytes d)) K).

Definition so_exit_stmt_b : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (so : stdout_st)
         (code t : Z) (td0 td1 td2 td3 guard : word) (cdt thr sec : byte) (tm1 : word) (ph : bool),
    MOK mo -> chan_ok mo 1 ->
    stk psegs m lo (bv_unsigned sp) ->
    rw_cells psegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
    rw_cells psegs m 0x53af0 [C4 (Z_to_bv 64 0)] ->
    rw_cells psegs m 0x224f0 [C8 (Z_to_bv 64 0x223f8); C8 (Z_to_bv 64 0x223f0)] ->
    rw_cells psegs m 0x223f0 [C8 (Z_to_bv 64 0x120bc)] ->
    rw_cells psegs m 0x23778 [C1 (Z_to_bv 8 0)] ->
    rw_cells psegs m 0x22498 [C8 (Z_to_bv 64 0x14e98); C8 (Z_to_bv 64 0)] ->
    rw_cells psegs m 0x23500 [C8 (Z_to_bv 64 0x23500)] ->
    rw_cells psegs m 0x33784 [C1 (Z_to_bv 8 0)] ->
    ATEX ph m ->
    rw_cells psegs m 0x53b18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells psegs m 0x53f48 [C8 (Z_to_bv 64 0)] ->
    rw_cells psegs m 0x53f38 [C8 (Z_to_bv 64 0)] ->
    rw_cells psegs m 0x23718 [C8 (Z_to_bv 64 RSTDOUT)] ->
    rw_cells psegs m 0x23628 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m so -> zlength (so_buf so) <= 2^25 -> stderr_file m ->
    rw_cells psegs m 0x224e8 [C8 (Z_to_bv 64 0x53af8)] -> rw_cells psegs m 0x53af8 [C8 guard] ->
    mem_inv psegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code -> 0 <= code < 256 ->
    (0 < t < 4194304) -> (lo <= bv_unsigned sp - EXIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
    rzb psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x14fb4) fc None m (seg_rom psegs)) mo)
        (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (Z_to_bv 64 code) (m_fs mo))).

Definition so_diag_str_stmt_b (fmt : Z) (msg : list byte -> list byte) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (lo : Z) (canary : word) (s slack : list byte) (K : TSet),
    MOK mo -> chan_ok mo 2 ->
    stderr_wfile m ->
    a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 fmt ->
    bytes_at psegs m (bv_unsigned a2) (s ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) s ->
    ((- (bv_unsigned a2 + zlength s + 1)) mod 8 <= zlength slack) -> (zlength s <= 2^20) ->
    (bv_unsigned a2 + zlength s + 1 + zlength slack <= lo \/ bv_unsigned sp <= bv_unsigned a2) ->
    (GLOBALS_TOP <= bv_unsigned a2) ->
    stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) ->
    ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
    K [] ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
        munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' -> wmono psegs m m' -> mem_inv psegs m' ->
        frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
        stk psegs m' lo (bv_unsigned sp) -> stderr_wfile m' -> ssp_cells m' canary ->
        rzb psegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                             Ft (ret_pc ra) fc' None m' (seg_rom psegs)) mo) K) ->
    rzb psegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x174f0) fc None m (seg_rom psegs)) mo)
        (t_emit (W 2 (msg s)) K).

Definition so_diag_usage_stmt_b : Prop := so_diag_str_stmt_b A_FMT_usage msg_usage.
