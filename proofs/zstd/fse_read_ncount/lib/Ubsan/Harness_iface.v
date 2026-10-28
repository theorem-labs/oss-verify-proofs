(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Malloc Monad Stdio Harness Prog.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Section CANSEC1. Context {rc : runConstT}.
Definition PFUZZ_ENTRY : Z := 0x13528.
Definition PEMPTY : Z := 0x2ee40.
Definition PGOT_STDERR : Z := 0x1db70.
Definition PSTDERR_PTR : Z := 0x1db20.
Definition HARNESS_STACK : Z := 16384.
Definition harness_cells (m : mem) : Prop :=
rw_cells usegs m PGOT_STDERR [C8 (wz PSTDERR_PTR)]
/\ rw_cells usegs m PSTDERR_PTR [C8 (wz RSTDERR)].
Definition stderr_file0 (m : mem) : Prop :=
rw_cells usegs m RSTDERR (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE RSTDERR_BUF 0 2 (wz 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)).
#[using="Type"] Lemma stderr_file0_file : forall m, stderr_file0 m -> stderr_file m.
Proof. intros m H. exists (Z_to_bv 64 5), (wz 0), 0, 0, (repeat (Z_to_bv 8 0) 80). exact H. Qed.
Section FuzzOne.
Definition fuzz_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : PState) (LB : list block) (AB lo : Z) (m : mem)
(r : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom usegs)
/\ -2^31 <= r < 2^31
/\ mem_inv usegs m' /\ frm0 fc'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' AB
/\ rheap_pres LB (bv_unsigned sp) m m'
/\ RHEAP s' LB m'
/\ ps_so s' = ps_so s.
Definition fuzz_one_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z) (errv : word),
RHEAP s LB m ->
bytes_at usegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
rclient_range LB (bv_unsigned sp) D (zlength payload) ->
D mod 16 = 0 -> 0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
harness_cells m -> stderr_file0 m ->
rauxv_ok m AB -> bv_unsigned sp <= AB ->
stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - HARNESS_STACK ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
mem_inv usegs m -> frm0 fc ->
tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
a0 = wz D -> a1 = wz (zlength payload) ->
implM usegs (Prog.fuzz_one payload) s
(fuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz PFUZZ_ENTRY) fc None m (seg_rom usegs)).
End FuzzOne.
End CANSEC1.
