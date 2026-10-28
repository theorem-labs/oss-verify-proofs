(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qp X0pv X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fr X1h7 X1kd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Notation rsegs := X1gj.rsegs.

Definition RTARGET_ALLOC_INIT : Z := 0x1bf4c.
Definition RTARGET_ALLOC_COUNT : Z := 0x1bf50.
Definition RTARGET_RUN : Z := 0x1bf58.
Definition REMIT_PRINTF : Z := 0x1c0e0.

Definition RTARGET_RUN_STACK : Z := 80 + RFUZZ_STACK.

Definition rdrv_X : list (Z * Z) :=
[(RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024); (RSTDERR, RSTDERR + 232); (RINITIALIZED, RINITIALIZED + 1);
(RAEF_INCB, RAEF_INCB + 1); (RATEXIT, RATEXIT + 40); (RATEXIT_A0, RATEXIT_A0 + 8)].

Definition rdrv_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
pres_except rsegs (rclient_addr LB SP) rdrv_X m m'.

Definition rtarget_run_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : PState) (LB : list block) (AB lo : Z) (m : mem)
(r : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) fc' m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ 0 <= r <= 2
/\ frm0 fc'
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' AB
/\ rdrv_pres LB (bv_unsigned sp) m m'
/\ RHEAP s' LB m'
/\ stdout_file m' (ps_so s')
/\ stderr_wfile m'
/\ AXSTAT true m'.

Definition rtarget_run_stmt {RCEIL : RunCeiling} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (AB lo : Z) (errv : word),
RHEAP s LB m -> In (p, A, cap) LB ->
bytes_at rsegs m A (zbytes content) -> Forall (fun c => 0 <= c < 256) content ->
zlength content <= cap -> cap <= 2^26 -> 0 <= L -> 6 + L <= zlength content ->
rauxv_ok m AB -> bv_unsigned sp <= AB -> AB < 2^62 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RTARGET_RUN_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m -> frm0 fc ->
stdout_file m (ps_so s) -> stderr_wfile m ->
rw_cells rsegs m RINITIALIZED [C1 (Z_to_bv 8 0)] -> rtables_pristine m -> AXSTAT false m ->
tp = Z_to_bv 64 RATP -> bv_unsigned sp mod 16 = 0 ->
a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 (A + 6 + L) -> a3 = Z_to_bv 64 (zlength content - 6 - L) ->
implM rsegs (run (if 0 <? L then znth content 2 else 0) (skipn (Z.to_nat (6 + L)) content)) s
(rtarget_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RTARGET_RUN) fc None m (seg_rom rsegs)).

Goal rsegs = X1ea.rsegs. Proof. reflexivity. Qed.
