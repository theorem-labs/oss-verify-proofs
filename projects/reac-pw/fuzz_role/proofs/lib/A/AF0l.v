(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AF0l.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x525fc;        pc_wrap_malloc := 0x52428;   pc_malloc_ra0 := 0x526c4;
pc_free := 0x5242c;          pc_wrap_free := 0x52424;     pc_free_ra0 := 0x52564;
pc_stack_malloc := fun cid => if cid =? 3 then 0x3cbfc else 0;
pc_asan_memcpy := 0x510d4;   pc_asan_memset := 0x51570;
pc_wrap_memcpy := 0x510d0;   pc_wrap_memset := 0x510cc;   pc_wrap_memcmp := 0x41ad8;  pc_wrap_bcmp := 0;
pc_wrap_read := 0x41ae4;     pc_wrap_fwrite := 0x41ae8;   pc_wrap_vprintf := 0x41af4; pc_wrap_vfprintf := 0x41af8;
pc_wrap_fprintf := 0x41b00;  pc_wrap_memchr := 0x41adc;   pc_wrap_strnlen := 0x41acc;
pc_region_is_poisoned := 0x53c50;
pc_spin_mmapdie := 0x5f4dc;  pc_spin_batch := 0x35cb8;    pc_spin_freearray := 0x34694; pc_spin_shadow := 0x6d9e4
|}.
