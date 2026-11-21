(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from simdjson/fuzz_minifyimpl's proofs/lib/Plain/PExitU_defs.v: module paths and target names, 12 image addresses for simdjson/fuzz_utf8's plain binary. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg F_syscalls StdioFiles.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition RSTDIN : Z := 0xd10a8.
Definition stdin_cells : list cell :=
  [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0xb87f4); C8 z64; C8 z64; C8 z64; C8 z64;
   C8 (Z_to_bv 64 0xb8540); C8 z64; C8 (Z_to_bv 64 0xb87e8); C8 (Z_to_bv 64 0x103db0); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
   C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)].
Definition PNEED_LOCKS : Z := 0x10385b.   (* [comment removed for export] *)

Section StdioExitStatement2.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Definition stdio_exit_spec_stmt2 : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word),
      stk psegs m lo (bv_unsigned sp) ->
      rw_cells psegs m 0x10385b [C1 (Z_to_bv 8 0)] ->                                  (* [comment removed for export] *)
      rw_cells psegs m 0x103d98 [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells psegs m 0xd1190 [C8 (Z_to_bv 64 RSTDIN)] ->                           (* [comment removed for export] *)
      rw_cells psegs m RSTDIN stdin_cells ->                                           (* [comment removed for export] *)
      rw_cells psegs m 0xd1280 [C8 (Z_to_bv 64 RSTDOUT)] ->                          (* [comment removed for export] *)
      rw_cells psegs m 0xd10a0 [C8 (Z_to_bv 64 RSTDERR)] ->                          (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells psegs m ssp_guard [C8 guard] ->   (* [comment removed for export] *)
      mem_inv psegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (GLOBALS_TOP <= lo)%Z ->
      (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
      implM psegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xb8af8) fc None m (seg_rom psegs)).
End StdioExitStatement2.
