(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A (ASan build, #102 A' pin 1be0f53d96cb, unstripped twin bff8519bbe3e; donor pin d83eb25d; tfibsegs = A/AB1v.v Asan.M.loaded_segments; TfibSyms = A/AF0m.v): the two memcpy runtime rows of h-mani-a8's API record
   (lib/A/CfApiPreset.v po_asan_memcpy_cf, po_memcpy_icpt_cf) in the target text of c-omx-alloc's engine,
   YGcallMxmn.aintrin_realizes_xm (op OCpy) over the generic allocator relation ARx with its laws AR_laws_x:
   __asan_memcpy at pc_asan_memcpy (as_code B) = 0x523e4 and the memcpy interceptor's __wrap_memcpy trampoline at pc_wrap_memcpy (as_code B) = 0x523e0 (A/AF0l.v Tfib_code).
   rule 24: proves function __asan_memcpy (fuzz_preset, image A) po_asan_memcpy_cf (kind: restatement over ARx + memnorm
   keep of preset's AE2q walk, in the released file lib/A/AE2q.v, deleted in this series; CONFIRM the internal file bcmpcpy-CONFIRM.md).
   rule 24: proves function memcpy interceptor (fuzz_preset, image A) po_memcpy_icpt_cf (kind: restatement over ARx +
   memnorm keep of preset's AE31 walk; CONFIRM the internal file bcmpcpy-CONFIRM.md).
   The walks are lib/A/PRowCpyA.v asan_memcpy_realizes_xm (preset's lib/A/AE2q.v walk) and lib/A/PRowCpyI.v memcpy_icpt_realizes_xm (lib/A/AE31.v); each takes the four AR_laws_x fields it reads, which the record gives here.
   The record's fields at the s1b tree still have the OLD cf text (YG0d2cf.aintrin_realizes_cf); h-mani-a8 restates
   each as the _xm row at ARx := ARcf. No bridge to the old text is made here.
   #102 A' (c-libc-stdio rows102): origin/cold/c-libc-stdio-rows-cpy 532cf8bd849e's lib/A/PRowCpy.v (blob caaf029fde78)
   relocated by the frozen alreloc c4338d099cfb8025 (2 comment numerals moved by symbol + offset: __asan_memcpy -> 0x523e4,
   __wrap_memcpy -> 0x523e0); theorem names and statements unchanged. The pcs come from the tree's #102 image record
   A/AB1v.v 5c16133beeff, A/AF0l.v dfca6bb1a8d7, A/AF0m.v 97f423adf6eb, A/AE34.v 5cbf1e87dd38, A/AE2y.v 5c090820312f: Tfib_code's pc_asan_memcpy / pc_wrap_memcpy are the A' symbols __asan_memcpy / __wrap_memcpy
   (pyelftools on twin bff8519bbe3e). lib/A/PRowKitA.v and lib/Reusable/PRowKit.v are the donor's, unchanged (no image numeral). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YCbqG YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0l AF0m PRowCpyI PRowCpyA.
Open Scope Z_scope.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem prow_asan_memcpy_xm_A : forall B ARx HL, AR_laws_x tfibsegs B ARx HL -> TfibSyms B ->
aintrin_realizes_xm tfibsegs B ARx OCpy (pc_asan_memcpy (as_code B)).
Proof.
intros B ARx HL LAWS TB. rewrite (ts_code B TB).
intros ly S hps W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL HX.
exact (asan_memcpy_realizes_xm B ARx (alx_frame _ _ _ LAWS) (alx_stack _ _ _ LAWS) (alx_layout_ok _ _ _ LAWS)
(alx_const_cells _ _ _ LAWS) TB ly S hps W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL HX).
Qed.

Theorem prow_memcpy_icpt_xm_A : forall B ARx HL, AR_laws_x tfibsegs B ARx HL -> TfibSyms B ->
aintrin_realizes_xm tfibsegs B ARx OCpy (pc_wrap_memcpy (as_code B)).
Proof.
intros B ARx HL LAWS TB. rewrite (ts_code B TB).
intros ly S hps W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL HX.
exact (memcpy_icpt_realizes_xm B ARx (alx_frame _ _ _ LAWS) (alx_stack _ _ _ LAWS) (alx_layout_ok _ _ _ LAWS)
(alx_const_cells _ _ _ LAWS) TB ly S hps W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL HX).
Qed.

End r.
