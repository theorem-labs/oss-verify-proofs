(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
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
