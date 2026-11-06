(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: __interceptor_vfprintf of fm.asan (0x457ec, frame 0x30, entered from musl vsnprintf
   through __wrap_vfprintf) ported from A/AE35.v's walk: the entry state with the read-only image cells in vpA_rodata's
   form, TryAsanInitFromRtl and the common_flags ()->check_printf test run through, REAL (vfprintf) read from 0x9b740,
   the epilogue and ret as in tfib_vprintf_icpt_E; the inline printf_common run is replaced by a kcall of the
   printf_common contract (apcommon_realizesU), musl vfprintf by a kcall of avfp_realizes; the vprintf entry part
   (tfib_vprintf_icpt_A) is not used; stated as FMsnprintfGI's avfpi_realizes over FMsnprintfI's snk_frame. *)
(* Modified by Theorem Labs, 2026-10: the image-bearing half of origin/cold/port-fm-rtprintf-param 7e395de08f5
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGvfi.v for the snprintf chain restated over ARx (route (a),
   c-omx-hpreset 10:51Z), re-pinned at preset image A (fuzz_preset.asan d83eb25d; symbols from its unstripped twin
   f0d2e8d4): only vfi_rodata / vfi_rodata_chk (:36-39), the items of the four roots' closure that carry image
   numerals; the image-free ones are lib/Reusable/PSnpGvfikit.v. icpt_rodata is preset A's (A/AE2y.v). Relocation BY
   SYMBOL + OFFSET from fm.asan 0ba7e169 (unstripped fc92e86b) by the internal file reloc.py:
     cell                                              fm.asan    preset A
     .got slot of __sanitizer::common_flags_dont_use   0x999a0    0xa1ac0  (no symbol: the auipc / ld pair at
         ___interceptor_vfprintf + 0x30 in both images; the slot holds common_flags_dont_use + 0 in both)
     __sanitizer::common_flags_dont_use + 0 (value)    0x1338a8   0x13c3e8
     __sanitizer::common_flags_dont_use + 0x54         0x1338fc   0x13c43c (check_printf; .bss, value 1 at run time)
     __interception::real_vfprintf + 0                 0x9b740    0xa3848
     vfprintf + 0 (value)                              0x8ede0    0x950a0 *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpGvfi.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpGkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PSnpGk.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the read-only image cells of the walk: icpt_rodata (TryAsanInitFromRtl's asan_inited) and the common_flags
   pointer, check_printf and REAL (vfprintf) ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition vfi_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0xa2000, 8, [(0, 8%N, 0x13c9e8)]); (0x13ca3c, 1, [(0, 1%N, 1)]); (0xa3d88, 8, [(0, 8%N, 0x955dc)])].
Lemma vfi_rodata_chk : forall ly, rodata_chk ly vfi_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
End r.
