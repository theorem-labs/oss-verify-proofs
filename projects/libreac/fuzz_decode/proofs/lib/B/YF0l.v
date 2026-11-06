(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YF0l.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52188;        pc_wrap_malloc := 0x51fb0;   pc_malloc_ra0 := 0x52250;
pc_free := 0x51fb8;          pc_wrap_free := 0x51fac;     pc_free_ra0 := 0x520f0;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3c6fc else 0;
pc_asan_memcpy := 0x50c5c;   pc_asan_memset := 0x510f8;
pc_wrap_memcpy := 0x50c58;   pc_wrap_memset := 0x50c54;   pc_wrap_memcmp := 0x415a0;  pc_wrap_bcmp := 0x415a4;
pc_wrap_read := 0x415b0;     pc_wrap_fwrite := 0x415b4;   pc_wrap_vprintf := 0x415c0; pc_wrap_vfprintf := 0x415c4;
pc_wrap_fprintf := 0x415cc;  pc_wrap_memchr := 0x415a8;   pc_wrap_strnlen := 0x41594;
pc_region_is_poisoned := 0x53a14;
pc_spin_mmapdie := 0x5f604;  pc_spin_batch := 0x357b8;    pc_spin_freearray := 0x34194; pc_spin_shadow := 0x6db0c
|}.
