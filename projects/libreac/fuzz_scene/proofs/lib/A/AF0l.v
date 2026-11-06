(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x54eec;        pc_wrap_malloc := 0x54d18;   pc_malloc_ra0 := 0x54fb4;
pc_free := 0x54d1c;          pc_wrap_free := 0x54d14;     pc_free_ra0 := 0x54e54;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3f0e0 else if cid =? 2 then 0x3f270 else 0;
pc_asan_memcpy := 0x539c4;   pc_asan_memset := 0x53e60;
pc_wrap_memcpy := 0x539c0;   pc_wrap_memset := 0x539bc;   pc_wrap_memcmp := 0x44308;  pc_wrap_bcmp := 0x4430c;
pc_wrap_read := 0x44318;     pc_wrap_fwrite := 0x4431c;   pc_wrap_vprintf := 0x44328; pc_wrap_vfprintf := 0x4432c;
pc_wrap_fprintf := 0x44334;  pc_wrap_memchr := 0x44310;   pc_wrap_strnlen := 0x442fc;
pc_region_is_poisoned := 0x56540;
pc_spin_mmapdie := 0x61dcc;  pc_spin_batch := 0x3819c;    pc_spin_freearray := 0x36b78; pc_spin_shadow := 0x702d4
|}.
