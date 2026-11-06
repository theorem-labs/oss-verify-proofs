(* Modified by Theorem Labs, 2026-10: relocated from fuzz_preset (commit d0fcb396eeeb); module paths changed and every image numeral moved by symbol + offset to fuzz_reply's asan image A (unstripped fuzz_reply.asan sha256 d751b179ea49, pin 42c58610e125). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fuzz_reply.asan image A, realloc(NULL, n)'s prefix (segment S5, RGtop's seg_npre): the symbolic states of the walk
   from __wrap_realloc 0x53df0 to Allocator::Allocate's entry 0x31bd8 through asan_realloc's NULL-input arm
   (`beqz a0` 0x32570 taken, `jal Allocate` 0x325d4), seeded with a0 = 0 (A/RGcfS5_u.v SS0). The run helpers and the
   regions R_SCRR / R_OBJR are A/FSRealloc_S1_r.v's; the internal allocator's map word that the PointerIsMine probe
   reads (0x54244 `ld a3, 8(a2)`, a2 = internal_allocator + 8 * (p >> 32) = 0xa72c0 at p = 0) is the literal region
   R_IMN at 0xa72c8. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFeq FSRealloc_S1_tbl RGcfS5_u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require FSRealloc_S1_r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition R_IMN : YP09.region := YP09.mkRegion None 0xa72c8 0xa72d0 0 0 [YP09.mkChunk 0xa72c8 (CZero 8)].
Definition SS_L1N : sstate := Eval vm_compute in (FSRealloc_S1_r.xrun_to 0x5f704 RGcfS5_u.SS0).
Definition SS_AN : sstate := Eval vm_compute in
(FSRealloc_S1_r.xrun_to 0x5bb88 (FSRealloc_S1_r.xpin 10 (SLit TFIB_IAL_LO)
  (FSRealloc_S1_r.xadd R_IMN (FSRealloc_S1_r.xadd FSRealloc_S1_r.R_SCRR (FSRealloc_S1_r.xafter 54 (-2144) 0x54230 SS_L1N))))).
Definition SS_EN : sstate := Eval vm_compute in
(FSRealloc_S1_r.xrun_to 0x31bd8 (FSRealloc_S1_r.xadd FSRealloc_S1_r.R_OBJR
  (FSRealloc_S1_r.xadd FSRealloc_S1_r.R_SCRR (FSRealloc_S1_r.xafterU 70 0x54384 SS_AN)))).
Goal ss_pc SS_L1N = 0x5f704 /\ ss_pc SS_AN = 0x5bb88 /\ ss_pc SS_EN = 0x31bd8. Proof. repeat split; reflexivity. Qed.
