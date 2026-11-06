(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the build-B (asan-ubsan) copy of lib/A/Prog/BoxB.v, which has no
   BoxBFrameImg.v to build on, so the image part of PALibF (lib/A/Prog/BoxFrameImg.v's box_palf) is proved here too.
   boxb_code is proofs/libreac/fuzz_grant/lib/A/AF0l.v's Tfib_code (a working branch ac3f475adac) for
   fuzz_boxreg.asan-ubsan (image 7620eb05..., ET_EXEC, no PT_DYNAMIC). Each entry is the same runtime symbol, at the
   same offset into it, as in fuzz_grant.asan; the entries were read from the symbol table of the unstripped
   fuzz_boxreg.asan-ubsan, and the bytes at each address are the same in the stripped image. Each function that
   holds an entry has the same size and the same instruction sequence (opcodes and destination registers) in both
   builds. The two return addresses come right after a `jal ra` (malloc+0xc8, free+0x138). Each spin entry is the
   only `j .` in its function. The one side-stack entry is __asan_stack_malloc_3 (0x3c580).
   The side-stack flag's GOT slot is object 0 of BoxBAddr.v (.got 0x99330, which holds 0xa13c0 in the image), the
   shadow GOT slot object 1 (.got 0x992d8, which holds 0xa13b8), the shadow-base cell
   __asan_shadow_memory_dynamic_address object 12 (.bss 0xa13b8) and the flag
   __asan_option_detect_stack_use_after_return object 13 (.bss 0xa13c0, 4 bytes).
   The file does not define the unit's asyms record, for the reason lib/A/Prog/BoxB.v gives (fuzz_grant's lib/A/AF0m.v,
   lib/A/ACej.v and lib/Reusable/YF0p.v have no fuzz_boxreg copy on this branch). boxb_PALib and boxb_PALibF take as
   hypotheses the fields of B that PALib (BoxBPaLib.v) and PALibF (BoxBFrame.v) read. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05 YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBAddr BoxBPa BoxBImg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib BoxBFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition boxb_code : acode := {|
pc_malloc := 0x52620;        pc_wrap_malloc := 0x5244c;   pc_malloc_ra0 := 0x526e8;
pc_free := 0x52450;          pc_wrap_free := 0x52448;     pc_free_ra0 := 0x52588;
pc_stack_malloc := fun cid => if cid =? 3 then 0x3c580 else 0;
pc_asan_memcpy := 0x510f8;   pc_asan_memset := 0x51594;
pc_wrap_memcpy := 0x510f4;   pc_wrap_memset := 0x510f0;   pc_wrap_memcmp := 0x41460;  pc_wrap_bcmp := 0x41464;
pc_wrap_read := 0x41470;     pc_wrap_fwrite := 0x41474;   pc_wrap_vprintf := 0x41480; pc_wrap_vfprintf := 0x41484;
pc_wrap_fprintf := 0x4148c;  pc_wrap_memchr := 0x41468;   pc_wrap_strnlen := 0x41450;
pc_region_is_poisoned := 0x53c74;
pc_spin_mmapdie := 0x5f500;  pc_spin_batch := 0x3563c;    pc_spin_freearray := 0x34018; pc_spin_shadow := 0x6da08
|}.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma boxb_val_obj0 : @pa_val _ boxb_listing PI_boxb (A_OBJ 0) = 0x99330.
Proof. vm_compute. reflexivity. Qed.
Lemma boxb_val_obj1 : @pa_val _ boxb_listing PI_boxb (A_OBJ 1) = 0x992d8.
Proof. vm_compute. reflexivity. Qed.
Lemma boxb_val_obj12 : @pa_val _ boxb_listing PI_boxb (A_OBJ 12) = 0xa13b8.
Proof. vm_compute. reflexivity. Qed.
Lemma boxb_val_obj13 : @pa_val _ boxb_listing PI_boxb (A_OBJ 13) = 0xa13c0.
Proof. vm_compute. reflexivity. Qed.
Lemma boxb_palf : forall B : asyms,
as_got_uar B = 0x99330 -> as_uar_cell B = 0xa13c0 ->
pc_stack_malloc (as_code B) 3 = 0x3c580 ->
PALibF (PI := PI_boxb) B.
Proof.
intros B Hgot Hcell H3. split.
- rewrite Hgot. exact (eq_sym boxb_val_obj0).
- rewrite Hcell. lia.
- rewrite Hcell. reflexivity.
- rewrite H3. vm_compute. reflexivity.
- rewrite Hcell. pose proof boxb_val_obj0 as E0. pose proof boxb_val_obj1 as E1. pose proof boxb_val_obj12 as E12.
  cbn [zseps zseps_from fst snd]. lia.
Qed.
Lemma boxb_code_wrap_malloc :
@pa_sigma _ boxb_listing PI_boxb BB___interceptor_trampoline_malloc = pc_wrap_malloc boxb_code.
Proof. vm_compute. reflexivity. Qed.
Lemma boxb_code_wrap_free :
@pa_sigma _ boxb_listing PI_boxb BB___interceptor_trampoline_free = pc_wrap_free boxb_code.
Proof. vm_compute. reflexivity. Qed.
Lemma boxb_code_sm3 : pc_stack_malloc boxb_code 3 = 0x3c580.
Proof. reflexivity. Qed.
Lemma boxb_code_rt_below :
pc_free_ra0 boxb_code < @pa_val _ boxb_listing PI_boxb A_TEXT /\ pc_malloc_ra0 boxb_code < @pa_val _ boxb_listing PI_boxb A_TEXT.
Proof. split; vm_compute; reflexivity. Qed.
Lemma boxb_PALib : forall B : asyms,
as_code B = boxb_code -> as_got_shadow B = 0x992d8 -> as_shadow_cell B = 0xa13b8 ->
api_env (@pa_segs _ boxb_listing PI_boxb) B ->
PALib (PI := PI_boxb) B.
Proof.
intros B Hc Hg Hs He. split.
- rewrite Hg. exact (eq_sym boxb_val_obj1).
- rewrite Hs. exact (eq_sym boxb_val_obj12).
- pose proof boxb_val_obj1 as E1. pose proof boxb_val_obj12 as E12. lia.
- exact He.
- rewrite Hc. exact boxb_code_wrap_free.
- rewrite Hc. exact boxb_code_wrap_malloc.
- rewrite Hc. exact boxb_code_rt_below.
Qed.
Lemma boxb_PALibF : forall B : asyms,
as_code B = boxb_code -> as_got_uar B = 0x99330 -> as_uar_cell B = 0xa13c0 ->
PALibF (PI := PI_boxb) B.
Proof.
intros B Hc Hg Hu. apply boxb_palf; [exact Hg | exact Hu |]. rewrite Hc. exact boxb_code_sm3.
Qed.
End c.
