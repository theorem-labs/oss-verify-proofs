(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AF0l.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AF0l.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_role's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AF0l.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52694;        pc_wrap_malloc := 0x524c0;   pc_malloc_ra0 := 0x5275c;
pc_free := 0x524c4;          pc_wrap_free := 0x524bc;     pc_free_ra0 := 0x525fc;
pc_stack_malloc := fun cid => if cid =? 4 then 0x3cc74 else 0;
pc_asan_memcpy := 0x5116c;   pc_asan_memset := 0x51608;
pc_wrap_memcpy := 0x51168;   pc_wrap_memset := 0x51164;   pc_wrap_memcmp := 0x41b70;  pc_wrap_bcmp := 0;
pc_wrap_read := 0x41b7c;     pc_wrap_fwrite := 0x41b80;   pc_wrap_vprintf := 0x41b8c; pc_wrap_vfprintf := 0x41b90;
pc_wrap_fprintf := 0x41b98;  pc_wrap_memchr := 0x41b74;   pc_wrap_strnlen := 0x41b64;
pc_region_is_poisoned := 0x53ce8;
pc_spin_mmapdie := 0x5f574;  pc_spin_batch := 0x35d30;    pc_spin_freearray := 0x3470c; pc_spin_shadow := 0x6da7c
|}.
