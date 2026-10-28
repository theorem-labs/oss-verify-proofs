(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_syscalls.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation RTP := 0x2ef30%Z (only parsing).
Definition GLOBALS_TOP : Z := 0x50000.
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
[C4 flags; C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x1750c);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x176c8); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 z64;
CB 80 tail].
Notation RSTDOUT := 0x1ece0%Z (only parsing).
Notation RSTDOUT_BUF := 0x4f608%Z (only parsing).
Notation RSTDERR := 0x1ebf0%Z (only parsing).
Notation RSTDERR_BUF := 0x4f600%Z (only parsing).
Notation F_STDOUT_WRITE := 0x176d0%Z (only parsing).
Notation F_STDIO_WRITE := 0x17538%Z (only parsing).
Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
exists (flags mode : word) (tail bufbytes : list byte),
rw_cells usegs m RSTDOUT
(file_cells flags
(if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
(if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
(if so_active so then RSTDOUT_BUF else 0)%Z
(if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
RSTDOUT_BUF 1024 1 mode
(if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
/\ Z.land (bv_unsigned flags) 72 = 0%Z
/\ rw_cells usegs m RSTDOUT_BUF [CB 1024 bufbytes]
/\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
/\ (zlength (so_buf so) <= 1024)%Z
/\ (so_active so = false -> so_buf so = []).
Definition stderr_file (m : word -> option byte) : Prop :=
exists (flags mode : word) (e wend : Z) (tail : list byte),
rw_cells usegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE RSTDERR_BUF 0 2 mode 0xffffffff tail).
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
Section StdioExitStatement.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x1edc8); (RSTDOUT_BUF, 0x4fa08)]%Z m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ s' = set_so so' s
/\ stdout_file m' so' /\ so_buf so' = []
/\ stderr_file m'
/\ rw_cells usegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m' ssp_guard [C8 guard].
Definition stdio_exit_spec_stmt : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
(cdt thr sec : byte) (tm1 : word),
stk usegs m lo (bv_unsigned sp) ->
rw_cells usegs m 0x4f1c0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
rw_cells usegs m 0x4f5f0 [C8 z64] ->
rw_cells usegs m 0x4f5e0 [C8 z64] ->
rw_cells usegs m 0x1edc8 [C8 (Z_to_bv 64 RSTDOUT)] ->
rw_cells usegs m 0x1ecd8 [C8 (Z_to_bv 64 RSTDERR)] ->
stdout_file m (get_so s) -> stderr_file m ->
rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells usegs m ssp_guard [C8 guard] ->
mem_inv usegs m ->
tp = Z_to_bv 64 RTP ->
(lo <= bv_unsigned sp - 160)%Z -> (GLOBALS_TOP <= lo)%Z ->
(bv_unsigned sp < 2^47)%Z ->
implM usegs (stdout_exit_flush get_so set_so) s
(stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x17328) fc None m (seg_rom usegs)).
End StdioExitStatement.
