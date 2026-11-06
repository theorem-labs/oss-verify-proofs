(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (ASAN-UBSAN). This is the asan-ubsan TWIN
   of lib/A/Rt/StackMalloc8Tbl.v: the same Definitions, with the same names, in the same order, each value
   MEASURED on the asan-ubsan image. The cuts (lib/AU/Rt/StackMalloc8Cuts.v) hold no literal address and use the
   names below; they are the asan cuts with the module paths changed. *)

(*   HOW MEASURED. Host nm/objdump cannot read these RISC-V ELFs, so every value below comes from pyelftools
   (.symtab of the unstripped twin, and the PT_LOAD bytes of the pinned image) plus capstone 5.0.7 (decode):
     pinned image     pau-pipeline/libreac/bin/fuzz_scene/fuzz_scene.asan-ubsan
     unstripped twin  pau-pipeline/libreac/unstripped/fuzz_scene/fuzz_scene.asan-ubsan
     scripts          syms-au.py (sha256 181743b87947; internal record) and rvdis-au.py (sha256 0c53dbedd902; internal record)
                      (the asan syms.py / rvdis.py of a Theorem Labs lane with the image path changed; syms-au.py also takes a symbol name)
     disassembly      dis-__asan_stack_malloc_8-asan-ubsan.txt (sha256 5d435d28723f; internal record)
     table            AU-TWIN.md (sha256 0c6a1a3b6c6c; internal record) (asan value / asan-ubsan value /
                      how measured, for every name in this file)

   __asan_stack_malloc_8 and the whole Seg A chain decode INSTRUCTION FOR INSTRUCTION the same as in the asan
   image: 95 instructions, same mnemonics and same operands, except three pc-relative operands whose targets are
   named below (the TLS-GD pair at entry +0x20/+0x24, the .got load at entry +0xc0/+0xc4 on the branch the
   premises refute, and the real___tls_get_addr load inside __interceptor___tls_get_addr). So every NON-ADDRESS
   constant of the asan table is unchanged here; each one was re-decoded, not copied:
     CID8 = 8, SM8_FRAME = 48 (`addi sp,sp,-0x30` at 0x3f438, released at 0x3f590), SM8_WIN = 224
     (48 + 32 + 144: the same three prologues, `addi sp,sp,-0x20` at __interceptor___tls_get_addr 0x48ca0 and
     `addi sp,sp,-0x90` at DTLS_on_tls_get_addr 0x6b914), SM8_TLS_GOT_OFF = -0x800 (image word), SM8_DTLS_TPOFF
     = 8 (image word), SM8_CFLAG_TGA = SM8_CFLAGS + 0x89 (`lbu a1,0x89(a1)` at 0x6b958), SM8_IMG_LO = 0x10000 and
     SM8_IMG_END = 0x5f9000 (PT_LOAD extent, the same pages as asan). NO non-address constant differs between the
     two images.

   Addresses, MEASURED (symbol by .symtab name; the offsets inside the function by decode):
     __asan_stack_malloc_8 = 0x3f438, 380 B, 95 instructions                                      [asan 0x3f40c]
       +0x9c  = 0x3f4d4  the head of the 64-flag search loop (`and a7,a2,a5`)                     [asan 0x3f4a8]
       +0xe8  = 0x3f520  the free-flag exit of that loop ("found", target of `beqz t0` at +0xa8)  [asan 0x3f4f4]
       +0x12c = 0x3f564  the jal into __asan::MemToShadow (result discarded)                      [asan 0x3f538]
       +0x13c = 0x3f574  the jal into __asan::PoisonShadow                                        [asan 0x3f548]
       +0x140 = 0x3f578  the pc PoisonShadow returns to                                           [asan 0x3f54c]
     __asan_stack_free_8 = 0x3f5b4 (not walked here; its tail `j` into PoisonShadow is at 0x3f600)
                                                                                                  [asan 0x3f588]
     __asan::PoisonShadow(unsigned long, unsigned long, unsigned char) = 0x55be4, 1276 B          [asan 0x55bb8]
       (the target of `jal 0x16670` at 0x3f574)
     __asan::MemToShadow (static; the image holds five copies, this one is pinned by the `jal 0xa0` at 0x3f564
       and the `jal 0x24` at __asan_stack_free_8 +0x2c = 0x3f5e0)      = 0x3f604, 316 B           [asan 0x3f5d8]
   The summaries those last two entries carry are the image-free statements of lib/Reusable/AsStackLeaf.v
   (`poison_shadow_realizes`, `mem_to_shadow_realizes`), which this file Requires and re-exports, so a segment
   lane needs no second Require for them.
   A relocated file that disagrees with any of these values is a FINDING, not something to patch quietly
   (REF-12.md, "the 460-byte trap": a Theorem Labs lane's dry run wrote 0x3f5d8 where 0x3f40c was meant).

   No symbolic table here (no `tbl_fs`, no `fs_phase`, no `ssX`): the cuts are concrete-state predicates, so the
   symbolic machinery belongs to each segment lane's own file, over AU/YF0r.v's `tbl_icpt` base. The reason for
   the concrete form, and what it costs, is in
   STATED.md (sha256 c026bca459f5; internal record) section 3.1. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Export AsStackLeaf.
Import ListNotations.
Open Scope Z_scope.

Definition CID8 : Z := 8.
Definition PC_STACK_MALLOC_8 : Z := 0x3f438.
Definition PC_SM8_LOOP : Z := 0x3f4d4.
Definition PC_SM8_FOUND : Z := 0x3f520.
Definition PC_SM8_MSRET : Z := 0x3f578.
(* The function's own frame: `addi sp,sp,-0x30` at 0x3f438, released by `addi sp,sp,0x30` at 0x3f590. *)
Definition SM8_FRAME : Z := 48.
(* The stack window the walk reserves below the caller's sp, callees included: the deepest stack use is Seg A's TLS
   chain, 48 B (this frame) + 32 B (__interceptor___tls_get_addr) + 144 B (DTLS_on_tls_get_addr) = 224 B; the three
   prologues are byte-identical to the asan ones. PoisonShadow's 64 B and musl memset fit inside it. ESTACK = 4096
   of ecall_pre covers it. *)
Definition SM8_WIN : Z := 224.
(* __asan::PoisonShadow(unsigned long, unsigned long, unsigned char), asan-ubsan. *)
Definition PC_POISON_SHADOW : Z := 0x55be4.
(* __asan::MemToShadow, the copy __asan_stack_malloc_8 +0x12c and __asan_stack_free_8 +0x2c call, asan-ubsan. *)
Definition PC_MEM_TO_SHADOW : Z := 0x3f604.

(* Seg A: the TLS chain of __asan_stack_malloc_8 +0x28 (`jal 0x4f20` into __wrap___tls_get_addr 0x44380, whose
   `j 0x4920` lands on __interceptor___tls_get_addr), and the cells that chain and the prologue read. MEASURED on
   the asan-ubsan build with pyelftools + capstone 5.0.7 over the pinned image (decode) and its unstripped twin
   (.symtab names). 0x44380 and TryAsanInitFromRtl 0x5ba00 (called at 0x48cb8) are already in AU/YE34.v's
   tbl_icpt, so they get no name here. The VALUES of the bss / TLS cells below are start-up facts; the Seg A walk
   takes them as named Section hypotheses (lib/AU/Rt/StackMalloc8SegA.v), not from this file. *)
(* __interceptor___tls_get_addr, 124 B = 31 instructions (.symtab). *)
Definition SM8_ICPT_TGA : Z := 0x48ca0.
(* musl __tls_get_addr, 36 B = 9 instructions; reached by `jalr a1` at 0x48ccc through SM8_REAL_TGA. *)
Definition SM8_TGA : Z := 0x95964.
(* __asan::GetCurrentThread(), 32 B = 8 instructions; `jal 0x15528` at 0x48cd8. *)
Definition SM8_GET_THREAD : Z := 0x5e200.
(* __asan::AsanTSDGet(), 6 instructions walked (0x56d4c-0x56d60, ending in `j 0x3fcb8`); `jal -0x74bc` at 0x5e208. *)
Definition SM8_TSD_GET : Z := 0x56d4c.
(* musl pthread_getspecific, 28 B = 7 instructions; the tail `j` at 0x56d60. *)
Definition SM8_GETSPECIFIC : Z := 0x96a18.
(* __sanitizer::DTLS_on_tls_get_addr(void*, void*, unsigned long, unsigned long), 140 instructions walked
   (0x6b914-0x6bb40); `jal 0x22c18` at 0x48cfc. *)
Definition SM8_DTLS_ON_TGA : Z := 0x6b914.
(* The main thread's tp: builtin_tls (0x5d69d0, .symtab, 131280 B, the same size as asan's, over the same
   PT_TLS memsz 0x14 / align 8) + 0xc8 (REF-12 section 5); it is AU/YF0r.v:39's TP. *)
Definition SM8_TP : Z := 0x5d6a98.
(* __pthread_tsd_main (.symtab), the value of [tp - 88] that pthread_getspecific loads at 0x96a1c;
   it is AU/YF0r.v:40's TSD. *)
Definition SM8_TSD : Z := 0x5f7e40.
(* The main thread's dtv (inside builtin_tls), the value of [tp - 8] that __tls_get_addr loads at 0x9596c;
   it reads dtv[1] = [SM8_DTV + 8] at 0x9597c. The value is the staged start-up table's (AU/YF0m.v:26,
   z8 (ATp (-8))), and it is builtin_tls + 0xe8 = SM8_TP + 0x20, the same offsets as asan. *)
Definition SM8_DTV : Z := 0x5d6ab8.
(* The TLS-GD .got pair malloc_8 passes to __tls_get_addr (`auipc a0,0x5d` + `addi a0,a0,0x2d0` at entry
   +0x20/+0x24); image words (1, SM8_TLS_GOT_OFF): module 1, offset -0x800. *)
Definition SM8_TLS_GOT : Z := 0x9c728.
Definition SM8_TLS_GOT_OFF : Z := 0xfffffffffffff800.
(* __interception::real___tls_get_addr (.symtab), image word 0x95964 = SM8_TGA; loaded at 0x48cbc-0x48cc0. *)
Definition SM8_REAL_TGA : Z := 0x9d7e8.
(* __asan::asan_inited (.symtab, 1 B); `lb` at 0x5ba14. *)
Definition SM8_ASAN_INITED : Z := 0xa47d8.
(* __asan::tsd_key_inited (.symtab, 1 B); AsanTSDGet reads it at 0x56d54 and the u32 tsd_key at +4 (0x56d5c). *)
Definition SM8_TSD_KEY_INITED : Z := 0xa3360.
(* The .got slot DTLS_on_tls_get_addr loads at 0x6b950-0x6b954; image word 0x135628 = SM8_CFLAGS. *)
Definition SM8_GOT_CFLAGS : Z := 0x9ba30.
(* __sanitizer::common_flags_dont_use (.symtab, 288 B). *)
Definition SM8_CFLAGS : Z := 0x135628.
(* The flag byte DTLS_on_tls_get_addr tests at 0x6b958 (`lbu a1, 0x89(a1)`): SM8_CFLAGS + 0x89. *)
Definition SM8_CFLAG_TGA : Z := 0x1356b1.
(* The .got slot DTLS_on_tls_get_addr loads at 0x6b964-0x6b968; image word 0x133598 = SM8_VERB. *)
Definition SM8_GOT_VERB : Z := 0x9ba90.
(* __sanitizer::current_verbosity (.symtab, 4 B); `lw` at 0x6b974. *)
Definition SM8_VERB : Z := 0x133598.
(* The .got slot of DTLS's tp-relative offset, loaded at 0x6b970-0x6b978 (then `add s5,s5,tp`); image word 8. *)
Definition SM8_GOT_DTLS : Z := 0x9c738.
Definition SM8_DTLS_TPOFF : Z := 8.
(* [T + 48] and [T + 56], the main thread's static-TLS bounds that __interceptor___tls_get_addr loads at
   0x48ce0 / 0x48ce4 and passes to DTLS_on_tls_get_addr. The values are those of the staged start-up table
   (AU/YF0m.v:24, z8 (AT 48) / z8 (AT 56)), taken by the walk as a Section hypothesis. *)
Definition SM8_T_TLS_BEG : Z := 0x5d71d0.
Definition SM8_T_TLS_END : Z := 0x5d72ac.
(* The image's extent: the first PT_LOAD's start and the last PT_LOAD's page end (AU/YF0x.v:35/:23). *)
Definition SM8_IMG_LO : Z := 0x10000.
Definition SM8_IMG_END : Z := 0x5f9000.
