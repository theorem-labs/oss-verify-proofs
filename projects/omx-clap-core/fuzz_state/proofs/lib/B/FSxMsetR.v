(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/Rt/StrcmpU.v, with its module paths and module names changed; 28 of its 54 lines of code are new or changed and 518 lines of the source are left out. *)
(* fuzz_state image B (fuzz_state.asan-ubsan): the __asan_memset walk under the ARU invariant (lib/A/FSupoison.v), any U
   (the statement is lib/A/FSupoisonU.v aintrin_realizesU OSet at B's PC_memset 0x5222c, proved in lib/B/FSxMset.v):
   the walk's REGION CONDITION as one named lemma, asan_memset_regions_off_ush.
   RULE 24 LINE: proves function __asan_memset (fs image B, 0x5222c). Reuse search: `proof-index __asan_memset
   0x5222c` unpiped, last line: `proof-index: end; __asan_memset: 0 named, 1339 by address, 25 related, 0 released
   lemma(s), ...; 0x5222c: 0 named, 0 by address, 0 related, 0 released lemma(s), 0 by file name, ...`. Second-agent
   checker a Theorem Labs lane (2026-10-29 14:27Z): CONFIRM over 13535 working-branch heads, 16713 distinct fuzz_state .v
   blobs: 0 image-B ARU-OSet theorems at __asan_memset (7 hits, all image A, interceptor, or premise uses).

   Port-from: lib/A/FSxMsetR.v (image A, the same walk at 0x521bc), text unchanged except the image modules. The
   image-free helpers (icpt_ro_byte, shadow_span, low_off_ush, high_off_ush, ro_byte_low, span_off_ush) are IMPORTED
   from S0's lib/B/FSupoisonAsanR.v (a Theorem Labs lane's image-B __asan_memcpy helpers, over B's tfibsegs / icpt_rodata),
   not copied; this file states only asan_memset_fixed and asan_memset_regions_off_ush. No image-A module is imported.

   The walk is S0's lib/B/YE6t.v + YE6u + YE6v + YE2r.v (U = [] form: YE2r.v:564 asan_memset_realizes), ported over
   FSupoison.ecall_preU in lib/B/FSxMset.v. B's __asan_memset (0x5222c) is A's (0x521bc) instruction for instruction
   (0x240 bytes, 144 instructions) except four pc-relative GOT loads through B's own GOT cells; the walk's texts differ
   only in those addresses. The machine runs on mem, where U's shadow bytes read 0xf7; the AR that ecall_preU carries
   holds of FSupoison.unpoison U mem, where they read 0.

   - asan_memset_regions_off_ush: every byte that a region of this walk fixes (the stack window [sp - MS_SCR, sp) below
     sp (MS_SCR = 2200, YE6t.v:340; stk reaches sp - MS_STK = sp - 2192), the image's read-only cells icpt_rodata
     (YE2y.v:65), the shadow bytes of the granules of the destination range: YE6t.v:30-35 shreg1 / shregs2 and the
     mem_is_zero range inside them) and every byte that REAL(memset) writes (the destination [d, d + n): YE6t.v ms_tail,
     musl memset MS_REAL 0x99340 = YB1w tfib_A_memset) is outside U's shadow bytes: FSupoison.in_ush U is false there.
     Its premises are premises of aintrin_realizesU itself (ecall_preU, 0 <= d, amem_range d n, range_addressable d n),
     so any real __asan_memset call state witnesses them; no new bound is introduced.
   - Which part the walk consumes: the stack and shadow regions are built from the contract's premises, which are
     already stated on aview mem (the real memory), so they need no transfer; only the read-only cells come from AR
     (FSxMset.v ent_ro, through FSupoisonAsanR.ro_regions_off). The write to [d, d + n) is application memory
     (amem_range), never shadow; FSupoison.ARU_frame takes it in FSxMset.v ms_tailU.
   - Bytes the walk READS outside any region: the QuickCheckForUnpoisonedRegion fast path (n <= 64) loads the two 8-byte
     aligned shadow words around shadow(d) and shadow(d + n - 1); YE6t resumes after them at 0x522b0 / 0x522b4
     (p1_t_s3, YE6t.v:86 ff.), and the r_p1_t_2 runs stop at SR_addr there. Such a word can contain a shadow byte of U
     (a neighbouring granule's poisoned head). The walk takes those two words as FRESH atoms q1 / q2 read from aview mem
     and proves both branches of the zero test, so it holds for whatever the real memory has there; no premise about
     those bytes is needed, and none is added. The n > 64 path's __asan_region_is_poisoned / mem_is_zero reads (return
     0x54dc8) lie in the shadow span of the range, which this lemma covers. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE3d YE20 YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YE6t FSupoisonAsanR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14 YI16.
Import ListNotations.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSuR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAsanR.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The bytes the __asan_memset walk's regions fix, and the bytes REAL(memset) writes: its stack window
   [sp - MS_SCR, sp), the read-only cells, the destination shadow span, the destination [d, d + n). *)
Definition asan_memset_fixed (sp d n a : Z) : Prop :=
  (sp - YE6t.MS_SCR <= a < sp) \/ FSuR.icpt_ro_byte a \/ FSuR.shadow_span d n a \/ (d <= a < d + n).
Section r.
Variable B : asyms.
(* a Theorem Labs lane's region condition for the __asan_memset walk (lib/B/YE6t.v + YE6u + YE6v + YE2r.v). *)
Lemma asan_memset_regions_off_ush : forall ly S U W regs mem md d n,
  FSP.ecall_preU tfibsegs B ly S U W regs mem md -> 0 <= d -> amem_range d n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n ->
  forall a, asan_memset_fixed (spZ regs) d n a -> FSP.in_ush U a = false.
Proof.
intros ly S U W regs mem md d n HPRE Hd HAM HRA a Ha.
pose proof HPRE as ((HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & HOK & HPO).
assert (HARU : FSP.ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; [exact HOK | exact HPO]]).
destruct Ha as [Hs | [Hro | [Hsd | Hdst]]].
- pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & _ & _ & _ & Lbeg).
  apply (FSuR.high_off_ush B ly S U W mem md a HARU). unfold YE6t.MS_SCR, ESTACK in *. lia.
- apply (FSuR.low_off_ush B ly S U W mem md a HARU). pose proof (FSuR.ro_byte_low a Hro). unfold SHADOW_OFF, kLowMemEnd in *. lia.
- exact (FSuR.span_off_ush U W mem d n a HPO HRA Hd Hsd).
- destruct HAM as [HL | [HH _]].
  + apply (FSuR.low_off_ush B ly S U W mem md a HARU). unfold SHADOW_OFF, kLowMemEnd in *. lia.
  + apply (FSuR.high_off_ush B ly S U W mem md a HARU). lia.
Qed.
End r.
End f.
