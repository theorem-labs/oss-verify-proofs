(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed, its addresses moved to libreac/fuzz_grant's ASan build and the side-stack entries of classes 0 and 4, which fuzz_grant's program calls, added. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AF0l.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x5213c;        pc_wrap_malloc := 0x51f64;   pc_malloc_ra0 := 0x52204;
pc_free := 0x51f6c;          pc_wrap_free := 0x51f60;     pc_free_ra0 := 0x520a4;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3c6b0 else 0;
pc_asan_memcpy := 0x50c10;   pc_asan_memset := 0x510ac;
pc_wrap_memcpy := 0x50c0c;   pc_wrap_memset := 0x50c08;   pc_wrap_memcmp := 0x41554;  pc_wrap_bcmp := 0x41558;
pc_wrap_read := 0x41564;     pc_wrap_fwrite := 0x41568;   pc_wrap_vprintf := 0x41574; pc_wrap_vfprintf := 0x41578;
pc_wrap_fprintf := 0x41580;  pc_wrap_memchr := 0x4155c;   pc_wrap_strnlen := 0x41548;
pc_region_is_poisoned := 0x539c8;
pc_spin_mmapdie := 0x5f5b8;  pc_spin_batch := 0x3576c;    pc_spin_freearray := 0x34148; pc_spin_shadow := 0x6dac0
|}.
