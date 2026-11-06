(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (ASan+UBSan build, #102 B' pin d663f82d7f48, unstripped twin c90d4fa54d43; donor pin f8f98a95; tfibsegs = Reusable/YB1v.v AsanUbsan.M.loaded_segments; TfibSyms = Reusable/YF0m.v): the two memcpy runtime rows of h-mani-a8's API record
   (lib/A/CfApiPreset.v po_asan_memcpy_cf, po_memcpy_icpt_cf) in the target text of c-omx-alloc's engine,
   YGcallMxmn.aintrin_realizes_xm (op OCpy) over the generic allocator relation ARx with its laws AR_laws_x:
   __asan_memcpy at pc_asan_memcpy (as_code B) = B_ASAN_MEMCPY_PC = 0x524d0 and the memcpy interceptor's __wrap_memcpy trampoline at pc_wrap_memcpy (as_code B) = B_WRAP_MEMCPY_PC = 0x524cc (Reusable/YF0l.v Tfib_code, Reusable/YImgCellsB.v).
   rule 24: proves function __asan_memcpy (fuzz_preset, image B) po_asan_memcpy_cf (kind: restatement over ARx + memnorm
   keep of preset's YE2q walk (in the released file lib/Reusable/YE2q.v, deleted in this series); CONFIRM the internal file bcmpcpy-CONFIRM.md).
   rule 24: proves function memcpy interceptor (fuzz_preset, image B) po_memcpy_icpt_cf (kind: restatement over ARx +
   memnorm keep of preset's YE31 walk; CONFIRM the internal file bcmpcpy-CONFIRM.md).
   The walks are lib/AU/PRowCpyA.v asan_memcpy_realizes_xm (preset's lib/Reusable/YE2q.v walk) and lib/AU/PRowCpyI.v memcpy_icpt_realizes_xm (lib/Reusable/YE31.v); each takes the four AR_laws_x fields it reads, which the record gives here.
   The record's fields at the s1b tree still have the OLD cf text (YG0d2cf.aintrin_realizes_cf); h-mani-a8 restates
   each as the _xm row at ARx := ARcf. No bridge to the old text is made here.
   #102 B' (c-libc-stdio rows102): origin/cold/c-libc-stdio-rows-cpy 532cf8bd849e's lib/AU/PRowCpy.v (blob 48de77417f81) relocated by the
   frozen alreloc c4338d099cfb8025 (2 comment numerals moved by symbol + offset, both as the internal file b-to-bprime.tsv 5a684bb2: __asan_memcpy
   -> 0x524d0, __wrap_memcpy -> 0x524cc); theorem names and statements unchanged. The pcs come from the tree's #102 record
   Reusable/YB1v.v b8d05529c744, Reusable/YF0l.v 4a405a3dba65, Reusable/YF0m.v f82202ebccdf, Reusable/YE34.v cc3d7182c344, Reusable/YImgCellsB.v f1cc7493a79d, Reusable/YImgTop.v d2a97d3111ce (IMG_TOP_B 0x601000): Tfib_code's pc_asan_memcpy / pc_wrap_memcpy are
   B_ASAN_MEMCPY_PC / B_WRAP_MEMCPY_PC = the B' symbols __asan_memcpy / __wrap_memcpy (pyelftools on twin c90d4fa54d43).
   lib/AU/PRowKitA.v is the donor's, unchanged (no image numeral). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YCbqG YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PRowCpyI PRowCpyA.
Open Scope Z_scope.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem prow_asan_memcpy_xm_B : forall B ARx HL, AR_laws_x tfibsegs B ARx HL -> TfibSyms B ->
aintrin_realizes_xm tfibsegs B ARx OCpy (pc_asan_memcpy (as_code B)).
Proof.
intros B ARx HL LAWS TB. rewrite (ts_code B TB).
intros ly S hps W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL HX.
exact (asan_memcpy_realizes_xm B ARx (alx_frame _ _ _ LAWS) (alx_stack _ _ _ LAWS) (alx_layout_ok _ _ _ LAWS)
(alx_const_cells _ _ _ LAWS) TB ly S hps W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL HX).
Qed.

Theorem prow_memcpy_icpt_xm_B : forall B ARx HL, AR_laws_x tfibsegs B ARx HL -> TfibSyms B ->
aintrin_realizes_xm tfibsegs B ARx OCpy (pc_wrap_memcpy (as_code B)).
Proof.
intros B ARx HL LAWS TB. rewrite (ts_code B TB).
intros ly S hps W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL HX.
exact (memcpy_icpt_realizes_xm B ARx (alx_frame _ _ _ LAWS) (alx_stack _ _ _ LAWS) (alx_layout_ok _ _ _ LAWS)
(alx_const_cells _ _ _ LAWS) TB ly S hps W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL HX).
Qed.

End r.
