(* Modified by Theorem Labs, 2026-10: relocated from fuzz_preset (commit d0fcb396eeeb); module paths changed and every image numeral moved by symbol + offset to fuzz_reply's asan image A (unstripped fuzz_reply.asan sha256 d751b179ea49, pin 42c58610e125). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RGcfS5_r.v at commit 6ea216c338f as lib/B/RGcfS5_r.v, with its module paths changed (lib.A to lib.B, except the image-free ADIfaceImgA and the one params file CfParamsReply; the image twins A<r> to Y<r>, CfImgA / CfImg_A to CfImgB / CfImg_B, WrapAKit / WrapFreeA<x> to WrapBKit / WrapFreeB<x>, AFf0cfR to YFf0cfR, RGcfWalkA to RGcfWalkB with its three exported names wrap_realloc_walk_cf_A, wrap_realloc_null_walk_cf_A, wrap_realloc_walk_cf_rh_A to _B), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan by alreloc 6e5d1356c317 (18 numerals; per-numeral report). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a): every address in the next comment is image B's; an image it names is the image its text came from. *)
(* fuzz_reply.asan image A, realloc(NULL, n)'s prefix (segment S5, RGtop's seg_npre): the symbolic states of the walk
   from __wrap_realloc 0x53e48 to Allocator::Allocate's entry 0x31c30 through asan_realloc's NULL-input arm
   (`beqz a0` 0x325c8 taken, `jal Allocate` 0x3262c), seeded with a0 = 0 (A/RGcfS5_u.v SS0). The run helpers and the
   regions R_SCRR / R_OBJR are A/FSRealloc_S1_r.v's; the internal allocator's map word that the PointerIsMine probe
   reads (0x5429c `ld a3, 8(a2)`, a2 = internal_allocator + 8 * (p >> 32) = 0xa7840 at p = 0) is the literal region
   R_IMN at 0xa7848. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFeq FSRealloc_S1_tbl RGcfS5_u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require FSRealloc_S1_r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition R_IMN : YP09.region := YP09.mkRegion None 0xa7848 0xa7850 0 0 [YP09.mkChunk 0xa7848 (CZero 8)].
Definition SS_L1N : sstate := Eval vm_compute in (FSRealloc_S1_r.xrun_to 0x5f75c RGcfS5_u.SS0).
Definition SS_AN : sstate := Eval vm_compute in
(FSRealloc_S1_r.xrun_to 0x5bbe0 (FSRealloc_S1_r.xpin 10 (SLit TFIB_IAL_LO)
  (FSRealloc_S1_r.xadd R_IMN (FSRealloc_S1_r.xadd FSRealloc_S1_r.R_SCRR (FSRealloc_S1_r.xafter 54 (-2144) 0x54288 SS_L1N))))).
Definition SS_EN : sstate := Eval vm_compute in
(FSRealloc_S1_r.xrun_to 0x31c30 (FSRealloc_S1_r.xadd FSRealloc_S1_r.R_OBJR
  (FSRealloc_S1_r.xadd FSRealloc_S1_r.R_SCRR (FSRealloc_S1_r.xafterU 70 0x543dc SS_AN)))).
Goal ss_pc SS_L1N = 0x5f75c /\ ss_pc SS_AN = 0x5bbe0 /\ ss_pc SS_EN = 0x31c30. Proof. repeat split; reflexivity. Qed.
