(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YF0l.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x54f18;        pc_wrap_malloc := 0x54d44;   pc_malloc_ra0 := 0x54fe0;
pc_free := 0x54d48;          pc_wrap_free := 0x54d40;     pc_free_ra0 := 0x54e80;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3f10c else if cid =? 2 then 0x3f29c else 0;
pc_asan_memcpy := 0x539f0;   pc_asan_memset := 0x53e8c;
pc_wrap_memcpy := 0x539ec;   pc_wrap_memset := 0x539e8;   pc_wrap_memcmp := 0x44334;  pc_wrap_bcmp := 0x44338;
pc_wrap_read := 0x44344;     pc_wrap_fwrite := 0x44348;   pc_wrap_vprintf := 0x44354; pc_wrap_vfprintf := 0x44358;
pc_wrap_fprintf := 0x44360;  pc_wrap_memchr := 0x4433c;   pc_wrap_strnlen := 0x44328;
pc_region_is_poisoned := 0x5656c;
pc_spin_mmapdie := 0x61df8;  pc_spin_batch := 0x381c8;    pc_spin_freearray := 0x36ba4; pc_spin_shadow := 0x70300
|}.
