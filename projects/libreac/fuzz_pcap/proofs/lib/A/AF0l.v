From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := (symaddr Symbols.Asan.s___interceptor_malloc);        pc_wrap_malloc := (symaddr Symbols.Asan.s___wrap_malloc);   pc_malloc_ra0 := (symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z);
pc_free := (symaddr Symbols.Asan.s___interceptor_free);          pc_wrap_free := (symaddr Symbols.Asan.s___wrap_free);     pc_free_ra0 := (symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z);
pc_stack_malloc := fun cid => if cid =? 0 then (symaddr Symbols.Asan.s___asan_stack_malloc_0) else if cid =? 1 then (symaddr Symbols.Asan.s___asan_stack_malloc_1) else 0;
pc_asan_memcpy := (symaddr Symbols.Asan.s___asan_memcpy);   pc_asan_memset := (symaddr Symbols.Asan.s___asan_memset);
pc_wrap_memcpy := (symaddr Symbols.Asan.s___wrap_memcpy);   pc_wrap_memset := (symaddr Symbols.Asan.s___wrap_memset);   pc_wrap_memcmp := (symaddr Symbols.Asan.s___wrap_memcmp);  pc_wrap_bcmp := (symaddr Symbols.Asan.s___wrap_bcmp);
pc_wrap_read := (symaddr Symbols.Asan.s___wrap_read);     pc_wrap_fwrite := (symaddr Symbols.Asan.s___wrap_fwrite);   pc_wrap_vprintf := (symaddr Symbols.Asan.s___wrap_vprintf); pc_wrap_vfprintf := (symaddr Symbols.Asan.s___wrap_vfprintf);
pc_wrap_fprintf := (symaddr Symbols.Asan.s___wrap_fprintf);  pc_wrap_memchr := (symaddr Symbols.Asan.s___wrap_memchr);   pc_wrap_strnlen := (symaddr Symbols.Asan.s___wrap_strnlen);
pc_region_is_poisoned := (symaddr Symbols.Asan.s___asan_region_is_poisoned);
pc_spin_mmapdie := (symaddr (Symbols.Asan.s__ZN11__sanitizer23ReportMmapFailureAndDieEmPKcS1_ib + 0x30)%Z);  pc_spin_batch := (symaddr (Symbols.Asan.s__ZN11__sanitizer15QuarantineCacheIN6__asan18QuarantineCallbackEE7EnqueueES2_Pvm + 0x190)%Z);    pc_spin_freearray := (symaddr (Symbols.Asan.s__ZN11__sanitizer29SealedHangOnAllocationFailureEv + 0x24)%Z); pc_spin_shadow := (symaddr (Symbols.Asan.s__ZN11__sanitizer18MmapFixedNoReserveEmmPKc + 0xc4)%Z)
|}.
