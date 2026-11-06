(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed, its addresses moved to plugin-hostd/fuzz_command's ASan build, and pc_stack_malloc keyed by fuzz_command's side-stack classes 0, 1, 3, 4, 5, 7 (cgif's class 2 has no counterpart). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AF0l.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AF0l.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x56e98;        pc_wrap_malloc := 0x56cc0;   pc_malloc_ra0 := 0x56f60;
pc_free := 0x56cc8;          pc_wrap_free := 0x56cbc;     pc_free_ra0 := 0x56e00;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3e608 else if cid =? 1 then 0x3e77c else if cid =? 3 then 0x3e90c
else if cid =? 5 then 0x3eab8 else 0;
pc_asan_memcpy := 0x5596c;   pc_asan_memset := 0x55e08;
pc_wrap_memcpy := 0x55968;   pc_wrap_memset := 0x55964;   pc_wrap_memcmp := 0x43ac0;  pc_wrap_bcmp := 0x43ac4;
pc_wrap_read := 0x43ad0;     pc_wrap_fwrite := 0x43ad4;   pc_wrap_vprintf := 0x43ae0; pc_wrap_vfprintf := 0x43ae4;
pc_wrap_fprintf := 0x43aec;  pc_wrap_memchr := 0x43ac8;   pc_wrap_strnlen := 0x43a9c;
pc_region_is_poisoned := 0x58724;
pc_spin_mmapdie := 0x64314;  pc_spin_batch := 0x376c4;    pc_spin_freearray := 0x360a0; pc_spin_shadow := 0x7281c
|}.
