(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan). The tables of
   __asan_stack_malloc_8 at 0x3f40c: EVERY scene address and class constant the class-8 segment cuts name, and
   nothing image-free. The cuts themselves are in lib/A/Rt/StackMalloc8Cuts.v and hold no literal address; they
   use the names below. Same split as a Theorem Labs lane's lib/A/Rt/StackMalloc4Tbl.v + StackMalloc4.v (libreac/fuzz_grant
   at 798447a1772) and a Theorem Labs lane's class 3 (StackMalloc3Tbl.v + StackMalloc3.v).
   The asan-ubsan side is a twin of THIS file only (lib/AU/Rt/StackMalloc8Tbl.v); the cuts serve both images.

   Addresses, MEASURED from the pinned image's unstripped twin (.symtab) and its disassembly
   (internal path). The asan-ubsan column is
   for the twin file; it is NOT used here:
     __asan_stack_malloc_8 = 0x3f40c, 380 B, 95 instructions                              [asan-ubsan 0x3f438]
       +0x9c  = 0x3f4a8  the head of the 64-flag search loop                              [asan-ubsan 0x3f4d4]
       +0xe8  = 0x3f4f4  the free-flag exit of that loop ("found")                        [asan-ubsan 0x3f520]
       +0x12c = 0x3f538  the jal into __asan::MemToShadow (result discarded)              [asan-ubsan 0x3f564]
       +0x13c = 0x3f548  the jal into __asan::PoisonShadow                                [asan-ubsan 0x3f574]
       +0x140 = 0x3f54c  the pc PoisonShadow returns to                                   [asan-ubsan 0x3f578]
     __asan_stack_free_8 = 0x3f588 (not walked here; its tail `j` into PoisonShadow is at 0x3f5d4)
                                                                                          [asan-ubsan 0x3f5b4]
     __asan::PoisonShadow(unsigned long, unsigned long, unsigned char) = 0x55bb8, 1276 B  [asan-ubsan 0x55be4]
     __asan::MemToShadow (static; the image holds five copies, this one is pinned by the two jals above)
                                                                       = 0x3f5d8, 316 B   [asan-ubsan 0x3f604]
   The summaries those last two entries carry are the image-free statements of lib/Reusable/AsStackLeaf.v
   (`poison_shadow_realizes`, `mem_to_shadow_realizes`), which this file Requires and re-exports, so a segment
   lane needs no second Require for them.
   A relocated file that disagrees with any of these values is a FINDING, not something to patch quietly
   (REF-12.md, "the 460-byte trap": a Theorem Labs lane's dry run wrote 0x3f5d8 where 0x3f40c was meant).

   No symbolic table here (no `tbl_fs`, no `fs_phase`, no `ssX`): the cuts are concrete-state predicates, so the
   symbolic machinery belongs to each segment lane's own file, over A/AF0r.v's `tbl_icpt` base, the way
   a Theorem Labs lane's StackMalloc4Tbl.v builds on A/Rt/AF0r.v. The reason for the concrete form, and what it costs, is in
   (internal path) section 3.1. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Export AsStackLeaf.
Import ListNotations.
Open Scope Z_scope.

Definition CID8 : Z := 8.
Definition PC_STACK_MALLOC_8 : Z := 0x3df90.
Definition PC_SM8_LOOP : Z := 0x3e02c.
Definition PC_SM8_FOUND : Z := 0x3e078.
Definition PC_SM8_MSRET : Z := 0x3e0d0.
(* The function's own frame: `addi sp,sp,-0x30` at 0x3df90, released by `addi sp,sp,0x30` at 0x3e0e8. *)
Definition SM8_FRAME : Z := 48.
(* The stack window the walk reserves below the caller's sp, callees included: the deepest stack use is Seg A's TLS
   chain, 48 B (this frame) + 32 B (__interceptor___tls_get_addr) + 144 B (DTLS_on_tls_get_addr) = 224 B (a Theorem Labs lane,
   23:43Z; Seg A's writes lie in [sp0 - 208, sp0)). PoisonShadow's 64 B and musl memset fit inside it. The value is
   the same as cgif_rgb_fuzzer's FS_WIN (lib/YF9a.v:35). ESTACK = 4096 of ecall_pre covers it. *)
Definition SM8_WIN : Z := 224.
(* __asan::PoisonShadow(unsigned long, unsigned long, unsigned char), asan. *)
Definition PC_POISON_SHADOW : Z := 0x551a8.
(* __asan::MemToShadow, the copy __asan_stack_malloc_8 +0x12c and __asan_stack_free_8 +0x2c call, asan. *)
Definition PC_MEM_TO_SHADOW : Z := 0x3e324.

(* Seg A: the TLS chain of __asan_stack_malloc_8 +0x28 (`jal 0x50ec` into __wrap___tls_get_addr 0x430a4, whose
   `j 0x4f04` lands on __interceptor___tls_get_addr), and the cells that chain and the prologue read. MEASURED by
   M8SegA, asan build, with pyelftools + capstone 5.0.7 over the pinned image (decode) and its unstripped twin
   (.symtab names), with the scripts link-a/tools/rvdis.py (internal record, sha256 b2bc766bc091) and link-a/tools/syms.py (internal record, sha256 e98d90e68f66).
   0x430a4 and TryAsanInitFromRtl 0x5b214 (called at 0x47fc0) are already in A/AE34.v's tbl_icpt, so they get no name here.
   The asan-ubsan values go in the lib/AU/Rt twin. The VALUES of the bss / TLS cells below are start-up facts;
   the Seg A walk takes them as named Section hypotheses (lib/A/Rt/StackMalloc8SegA.v), not from this file. *)
(* __interceptor___tls_get_addr, 124 B = 31 instructions (.symtab). *)
Definition SM8_ICPT_TGA : Z := 0x47fa8.
(* musl __tls_get_addr, 36 B = 9 instructions; reached by `jalr a1` at 0x47fd4 through SM8_REAL_TGA. *)
Definition SM8_TGA : Z := 0x9b7f8.
(* __asan::GetCurrentThread(), 32 B = 8 instructions; `jal 0x15a34` at 0x47fe0. *)
Definition SM8_GET_THREAD : Z := 0x5da14.
(* __asan::AsanTSDGet(), 6 instructions walked (0x56310-0x56324, ending in `j 0x46588`); `jal -0x770c` at 0x5da1c. *)
Definition SM8_TSD_GET : Z := 0x56310.
(* musl pthread_getspecific, 28 B = 7 instructions; the tail `j` at 0x56324. *)
Definition SM8_GETSPECIFIC : Z := 0x9c8ac.
(* __sanitizer::DTLS_on_tls_get_addr(void*, void*, unsigned long, unsigned long), 140 instructions walked
   (0x6b23c-0x6b468); `jal 0x23238` at 0x48004. *)
Definition SM8_DTLS_ON_TGA : Z := 0x6b23c.
(* The main thread's tp: builtin_tls (0x631b48, .symtab) + 0xc8 (REF-12 section 5). *)
Definition SM8_TP : Z := 0x631c10.
(* __pthread_tsd_main (.symtab), the value of [tp - 88] that pthread_getspecific loads at 0x9c8b0. *)
Definition SM8_TSD : Z := 0x652fb8.
(* The main thread's dtv (inside builtin_tls), the value of [tp - 8] that __tls_get_addr loads at 0x9b800;
   it reads dtv[1] = [SM8_DTV + 8] at 0x9b810. *)
Definition SM8_DTV : Z := 0x631c30.
(* The TLS-GD .got pair malloc_8 passes to __tls_get_addr (auipc+addi at entry +0x20/+0x24); image words
   (1, SM8_TLS_GOT_OFF): module 1, offset -0x800. *)
Definition SM8_TLS_GOT : Z := 0xa26b0.
Definition SM8_TLS_GOT_OFF : Z := 0xfffffffffffff800.
(* __interception::real___tls_get_addr (.symtab), image word 0x9b7f8 = SM8_TGA; loaded at 0x47fc4-0x47fc8. *)
Definition SM8_REAL_TGA : Z := 0xa3778.
(* __asan::asan_inited (.symtab, 1 B); `lb` at 0x5b228. *)
Definition SM8_ASAN_INITED : Z := 0xab118.
(* __asan::tsd_key_inited (.symtab, 1 B); AsanTSDGet reads it at 0x56318 and the u32 tsd_key at +4 (0x56320). *)
Definition SM8_TSD_KEY_INITED : Z := 0xa9ca0.
(* The .got slot DTLS_on_tls_get_addr loads at 0x6b278-0x6b27c; image word 0x13bf68 = SM8_CFLAGS. *)
Definition SM8_GOT_CFLAGS : Z := 0xa19c0.
(* __sanitizer::common_flags_dont_use (.symtab, 288 B). *)
Definition SM8_CFLAGS : Z := 0x13bf68.
(* The flag byte DTLS_on_tls_get_addr tests at 0x6b280 (`lbu a1, 0x89(a1)`): SM8_CFLAGS + 0x89. *)
Definition SM8_CFLAG_TGA : Z := 0x13bff1.
(* The .got slot DTLS_on_tls_get_addr loads at 0x6b28c-0x6b290; image word 0x139ed8 = SM8_VERB. *)
Definition SM8_GOT_VERB : Z := 0xa1a20.
(* __sanitizer::current_verbosity (.symtab, 4 B); `lw` at 0x6b29c. *)
Definition SM8_VERB : Z := 0x139ed8.
(* The .got slot of DTLS's tp-relative offset, loaded at 0x6b298-0x6b2a0 (then `add s5,s5,tp`); image word 8. *)
Definition SM8_GOT_DTLS : Z := 0xa26c0.
Definition SM8_DTLS_TPOFF : Z := 8.
(* [T + 48] and [T + 56], the main thread's static-TLS bounds that __interceptor___tls_get_addr loads at
   0x47fe8 / 0x47fec and passes to DTLS_on_tls_get_addr. The values are those of the staged start-up table
   (A/AF0m.v:24, z8 (AT 48) / z8 (AT 56)), taken by the walk as a Section hypothesis. *)
Definition SM8_T_TLS_BEG : Z := 0x632348.
Definition SM8_T_TLS_END : Z := 0x632424.
(* The image's extent: the first PT_LOAD's start and the last PT_LOAD's page end (A/AF0x.v:25/:37). *)
Definition SM8_IMG_LO : Z := 0x10000.
Definition SM8_IMG_END : Z := 0x654000.
