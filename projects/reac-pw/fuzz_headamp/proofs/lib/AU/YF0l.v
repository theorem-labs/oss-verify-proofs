(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AF0l.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AF0l.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_headamp/lib/A/AF0l.v at b0cad0df5623 (image sha256 f3e0669d2819), with its module names changed (A.Axyz -> AU.Yxyz) and its addresses moved to reac-pw/fuzz_headamp's ASan+UBSan build (image sha256 53edda9bdeeb) by derive_y.py b7b132fb12a7; the Modified-by lines above describe how lib/A/AF0l.v was made and quote its ASan-build values. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x532b4;        pc_wrap_malloc := 0x530e0;   pc_malloc_ra0 := 0x5337c;
pc_free := 0x530e4;          pc_wrap_free := 0x530dc;     pc_free_ra0 := 0x5321c;
pc_stack_malloc := fun cid => if cid =? 4 then 0x3cd2c else 0;
pc_asan_memcpy := 0x51d8c;   pc_asan_memset := 0x52228;
pc_wrap_memcpy := 0x51d88;   pc_wrap_memset := 0x51d84;   pc_wrap_memcmp := 0x41c2c;  pc_wrap_bcmp := 0;
pc_wrap_read := 0x41c38;     pc_wrap_fwrite := 0x41c3c;   pc_wrap_vprintf := 0x41c48; pc_wrap_vfprintf := 0x41c4c;
pc_wrap_fprintf := 0x41c54;  pc_wrap_memchr := 0x41c30;   pc_wrap_strnlen := 0x41c1c;
pc_region_is_poisoned := 0x54908;
pc_spin_mmapdie := 0x60194;  pc_spin_batch := 0x35de8;    pc_spin_freearray := 0x347c4; pc_spin_shadow := 0x6e69c
|}.
