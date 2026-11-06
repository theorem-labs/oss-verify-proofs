(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: box_code is proofs/libreac/fuzz_grant/lib/A/AF0l.v's Tfib_code
   (a working branch ac3f475adac) for fuzz_boxreg.asan (image eacfa205..., ET_EXEC, no PT_DYNAMIC). Each entry is
   the same runtime symbol, at the same offset into it, as in fuzz_grant.asan; the entries were read from the
   symbol table of the unstripped fuzz_boxreg.asan, and the bytes at each address are the same in the stripped image.
   Each function that holds an entry has the same size and the same instruction sequence (opcodes and destination
   registers) in both builds. The two return addresses come right after a `jal ra` (malloc+0xc8, free+0x138). Each
   spin entry is the only `j .` in its function. fuzz_boxreg.asan has one side-stack entry, __asan_stack_malloc_3
   (0x3c520), so pc_stack_malloc maps frame class 3 to it and every other class to 0.
   The file does not define the unit's asyms record (fuzz_grant's GrantB, lib/A/AD2l.v). That record also needs
   fuzz_grant's lib/A/AF0m.v (the TFIB_* cells, the constant cells, the owned and zero-shadow ranges, the trace
   hashes), lib/A/ACej.v (the allocation-trace universe) and lib/Reusable/YF0p.v (the trace hash), measured again
   for fuzz_boxreg.asan. None of them is on this branch. box_PALib and box_PALibF therefore take as hypotheses the
   fields of B that PALib (BoxPaLib.v) and PALibF (BoxFrame.v) read: as_code B = box_code, the two GOT slots
   (objects 1 and 0 of BoxAddr.v, .got 0x98eb8 and 0x98f10, which hold 0xa0f78 and 0xa0f80 in the image), the two
   cells (objects 12 and 13, .bss 0xa0f78 and 0xa0f80) and api_env. When the record is defined, each hypothesis
   except api_env holds by reflexivity. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05 YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun BoxSyms BoxList BoxAddr BoxPa BoxImg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxPaLib BoxFrame BoxFrameImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition box_code : acode := {|
pc_malloc := 0x525c0;        pc_wrap_malloc := 0x523ec;   pc_malloc_ra0 := 0x52688;
pc_free := 0x523f0;          pc_wrap_free := 0x523e8;     pc_free_ra0 := 0x52528;
pc_stack_malloc := fun cid => if cid =? 3 then 0x3c520 else 0;
pc_asan_memcpy := 0x51098;   pc_asan_memset := 0x51534;
pc_wrap_memcpy := 0x51094;   pc_wrap_memset := 0x51090;   pc_wrap_memcmp := 0x41400;  pc_wrap_bcmp := 0x41404;
pc_wrap_read := 0x41410;     pc_wrap_fwrite := 0x41414;   pc_wrap_vprintf := 0x41420; pc_wrap_vfprintf := 0x41424;
pc_wrap_fprintf := 0x4142c;  pc_wrap_memchr := 0x41408;   pc_wrap_strnlen := 0x413f0;
pc_region_is_poisoned := 0x53c14;
pc_spin_mmapdie := 0x5f4a0;  pc_spin_batch := 0x355dc;    pc_spin_freearray := 0x33fb8; pc_spin_shadow := 0x6d9a8
|}.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma box_code_wrap_malloc :
@pa_sigma _ box_listing PI_box BS___interceptor_trampoline_malloc = pc_wrap_malloc box_code.
Proof. vm_compute. reflexivity. Qed.
Lemma box_code_wrap_free :
@pa_sigma _ box_listing PI_box BS___interceptor_trampoline_free = pc_wrap_free box_code.
Proof. vm_compute. reflexivity. Qed.
Lemma box_code_sm3 : pc_stack_malloc box_code 3 = 0x3c520.
Proof. reflexivity. Qed.
Lemma box_code_rt_below :
pc_free_ra0 box_code < @pa_val _ box_listing PI_box A_TEXT /\ pc_malloc_ra0 box_code < @pa_val _ box_listing PI_box A_TEXT.
Proof. split; vm_compute; reflexivity. Qed.
Lemma box_PALib : forall B : asyms,
as_code B = box_code -> as_got_shadow B = 0x98eb8 -> as_shadow_cell B = 0xa0f78 ->
api_env (@pa_segs _ box_listing PI_box) B ->
PALib (PI := PI_box) B.
Proof.
intros B Hc Hg Hs He. split.
- rewrite Hg. exact (eq_sym box_val_obj1).
- rewrite Hs. exact (eq_sym box_val_obj12).
- pose proof box_val_obj1 as E1. pose proof box_val_obj12 as E12. lia.
- exact He.
- rewrite Hc. exact box_code_wrap_free.
- rewrite Hc. exact box_code_wrap_malloc.
- rewrite Hc. exact box_code_rt_below.
Qed.
Lemma box_PALibF : forall B : asyms,
as_code B = box_code -> as_got_uar B = 0x98f10 -> as_uar_cell B = 0xa0f80 ->
PALibF (PI := PI_box) B.
Proof.
intros B Hc Hg Hu. apply box_palf; [exact Hg | exact Hu |]. rewrite Hc. exact box_code_sm3.
Qed.
End c.
