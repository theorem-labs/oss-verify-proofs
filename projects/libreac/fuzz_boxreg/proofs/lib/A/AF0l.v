(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
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
