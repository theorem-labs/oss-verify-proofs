(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec Hoare.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import MallocLayout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition reloc_layout (RL : Reloc) : MallocLayout := {|
  ml_segs := rl_segs;
  IMG_LO := rl_img_lo; RW_LO := rl_rw_lo; IMG_HI := rl_img_hi;

  A_LOCK           := rl dA_2f848 0x2f8d8;
  A_CTX            := rl dA_2f848 0x2f8e0;
  A_INIT_DONE      := rl dA_2f848 0x2f8e8;
  A_MMAP_CTR       := rl dA_2f848 0x2f8ec;
  A_FREE_META_HEAD := rl dA_2f848 0x2f8f0;
  A_AVAIL_META     := rl dA_2f848 0x2f8f8;
  A_AVAIL_META_CNT := rl dA_2f848 0x2f900;
  A_AVAIL_AREA_CNT := rl dA_2f848 0x2f908;
  A_META_SHIFT     := rl dA_2f848 0x2f910;
  A_AREA_HEAD      := rl dA_2f848 0x2f918;
  A_AREA_TAIL      := rl dA_2f848 0x2f920;
  A_AVAIL_AREAS    := rl dA_2f848 0x2f928;
  Z_UNMAP_SEQ      := 0x2fc30 + dA_2f848;
  Z_BOUNCES        := 0x2fc50 + dA_2f848;
  A_SEQ            := rl dA_2f848 0x2fc70;
  A_BRK            := rl dA_2f848 0x2fc78;
  A_MALLOC_REPLACED := rl dA_2f848 0x2fc80;

  A_LIBC       := rl dA_2f848 0x2f868;
  A_NEED_LOCKS := rl dA_2f848 0x2f86b;
  A_PAGE_SIZE  := rl dA_2f848 0x2f898;
  A_TP         := rl dA_2f6b0 0x2f7b8;
  A_ERRNO      := rl dA_2f6b0 0x2f714;
  A_GOT_SSP    := rl dA_1e3b8 0x1e3e0;
  A_SSP        := rl dA_2f848 0x2f848;

  A_SIZE_CLASSES  := rl dA_113d4 0x113d4;
  A_SMALL_CNT_TAB := rl dA_113d4 0x11434;
  A_MED_CNT_TAB   := rl dA_1144f 0x1144f;
  A_DEBRUIJN      := rl dA_113b4 0x113b4;

  PC_MALLOC      := rl dF_15b3c 0x15b3c;
  PC_FREE        := rl dF_15b38 0x15b38;
  PC_CALLOC      := rl dF_15a00 0x15a00;
  PC_LIBC_FREE   := rl dF_15b40 0x15b40;
  PC_MALLOC_IMPL := rl dF_164cc 0x164cc;
  PC_GET_META    := rl dF_15d0c 0x15d0c;
  PC_NTFREE      := rl dF_15e1c 0x15e1c;
  PC_ALLOC_META  := rl dF_161f4 0x161f4;
  PC_ALLOC_SLOT  := rl dF_1683c 0x1683c;
  PC_ENFRAME     := rl dF_170e0 0x170e0;
  PC_ALLZEROP    := rl dF_17230 0x17230;
  PC_MMAP        := rl dF_17444 0x17444;
  PC_MPROTECT    := rl dF_17530 0x17530;
  PC_MUNMAP      := rl dF_17578 0x17578;
  PC_VM_WAIT     := rl dF_17440 0x17440;
  PC_SYSCALL_RET := rl dF_159c0 0x159c0;
  PC_ERRNO_LOC   := rl dF_1574c 0x1574c;
  PC_LOCK        := rl dF_1cf84 0x1cf84;
  PC_UNLOCK      := rl dF_1d20c 0x1d20c;
  PC_MEMCPY      := rl dF_1c9b4 0x1c9b4;
  PC_MEMSET      := rl dF_1cdb8 0x1cdb8
|}.

(* [comment removed for export] *)
Ltac rl_layout_unfold :=
  cbv beta iota delta [reloc_layout ml_segs IMG_LO RW_LO IMG_HI
    A_LOCK A_CTX A_INIT_DONE A_MMAP_CTR A_FREE_META_HEAD A_AVAIL_META A_AVAIL_META_CNT A_AVAIL_AREA_CNT
    A_META_SHIFT A_AREA_HEAD A_AREA_TAIL A_AVAIL_AREAS Z_UNMAP_SEQ Z_BOUNCES A_SEQ A_BRK A_MALLOC_REPLACED
    A_LIBC A_NEED_LOCKS A_PAGE_SIZE A_TP A_ERRNO A_GOT_SSP A_SSP
    A_SIZE_CLASSES A_SMALL_CNT_TAB A_MED_CNT_TAB A_DEBRUIJN
    PC_MALLOC PC_FREE PC_CALLOC PC_LIBC_FREE PC_MALLOC_IMPL PC_GET_META PC_NTFREE PC_ALLOC_META PC_ALLOC_SLOT
    PC_ENFRAME PC_ALLZEROP PC_MMAP PC_MPROTECT PC_MUNMAP PC_VM_WAIT PC_SYSCALL_RET PC_ERRNO_LOC PC_LOCK
    PC_UNLOCK PC_MEMCPY PC_MEMSET].
