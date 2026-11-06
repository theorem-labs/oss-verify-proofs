(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AF0l.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_rate's ASan build. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/AF0l.v at 4e3a0a9ad299, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/AF0l.v was made and quote that file's image-A values; the code below carries image B's values. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52de0;        pc_wrap_malloc := 0x52c0c;   pc_malloc_ra0 := 0x52ea8;
pc_free := 0x52c10;          pc_wrap_free := 0x52c08;     pc_free_ra0 := 0x52d48;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3cfd4 else if cid =? 2 then 0x3d164 else if cid =? 4 then 0x3d300 else 0;
pc_asan_memcpy := 0x518b8;   pc_asan_memset := 0x51d54;
pc_wrap_memcpy := 0x518b4;   pc_wrap_memset := 0x518b0;   pc_wrap_memcmp := 0x421fc;  pc_wrap_bcmp := 0x42200;
pc_wrap_read := 0x4220c;     pc_wrap_fwrite := 0x42210;   pc_wrap_vprintf := 0x4221c; pc_wrap_vfprintf := 0x42220;
pc_wrap_fprintf := 0x42228;  pc_wrap_memchr := 0x42204;   pc_wrap_strnlen := 0x421f0;
pc_region_is_poisoned := 0x54434;
pc_spin_mmapdie := 0x5fcc0;  pc_spin_batch := 0x36090;    pc_spin_freearray := 0x34a6c; pc_spin_shadow := 0x6e1c8
|}.
