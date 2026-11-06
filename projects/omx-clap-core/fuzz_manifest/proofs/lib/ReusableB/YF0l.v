(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YF0l.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to omx-clap-core/fuzz_manifest's ASan build. *)
(* Modified by Theorem Labs, 2026-10: a Theorem Labs lane's changes to lib/A/AF0l.v (a30c06078e9..5d8d8a15571) carried onto the image-B file by merge3.py. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52ff0;        pc_wrap_malloc := 0x52e1c;   pc_malloc_ra0 := 0x530b8;
pc_free := 0x52e20;          pc_wrap_free := 0x52e18;     pc_free_ra0 := 0x52f58;
pc_stack_malloc := fun _ => 0;
pc_asan_memcpy := 0x51ac8;   pc_asan_memset := 0x51f64;
pc_wrap_memcpy := 0x51ac4;   pc_wrap_memset := 0x51ac0;   pc_wrap_memcmp := 0x41344;  pc_wrap_bcmp := 0x41348;
pc_wrap_read := 0x41354;     pc_wrap_fwrite := 0x41358;   pc_wrap_vprintf := 0x41364; pc_wrap_vfprintf := 0x41368;
pc_wrap_fprintf := 0x41370;  pc_wrap_memchr := 0x4134c;   pc_wrap_strnlen := 0x4132c;
pc_region_is_poisoned := 0x54644;
pc_spin_mmapdie := 0x5fed0;  pc_spin_batch := 0x35ae8;    pc_spin_freearray := 0x344c4; pc_spin_shadow := 0x6e3d8
|}.
