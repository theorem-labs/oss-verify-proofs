(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AF0l.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AF0l.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x53234;        pc_wrap_malloc := 0x53060;   pc_malloc_ra0 := 0x532fc;
pc_free := 0x53064;          pc_wrap_free := 0x5305c;     pc_free_ra0 := 0x5319c;
pc_stack_malloc := fun cid => if cid =? 4 then 0x3ccac else 0;
pc_asan_memcpy := 0x51d0c;   pc_asan_memset := 0x521a8;
pc_wrap_memcpy := 0x51d08;   pc_wrap_memset := 0x51d04;   pc_wrap_memcmp := 0x41bac;  pc_wrap_bcmp := 0;
pc_wrap_read := 0x41bb8;     pc_wrap_fwrite := 0x41bbc;   pc_wrap_vprintf := 0x41bc8; pc_wrap_vfprintf := 0x41bcc;
pc_wrap_fprintf := 0x41bd4;  pc_wrap_memchr := 0x41bb0;   pc_wrap_strnlen := 0x41b9c;
pc_region_is_poisoned := 0x54888;
pc_spin_mmapdie := 0x60114;  pc_spin_batch := 0x35d68;    pc_spin_freearray := 0x34744; pc_spin_shadow := 0x6e61c
|}.
