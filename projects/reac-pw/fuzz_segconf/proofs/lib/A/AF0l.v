(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed, its addresses moved to plugin-hostd/fuzz_command's ASan build, and pc_stack_malloc keyed by fuzz_command's side-stack classes 0, 1, 3, 4, 5, 7 (cgif's class 2 has no counterpart). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AF0l.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x56e0c;        pc_wrap_malloc := 0x56c34;   pc_malloc_ra0 := 0x56ed4;
pc_free := 0x56c3c;          pc_wrap_free := 0x56c30;     pc_free_ra0 := 0x56d74;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3e57c else if cid =? 1 then 0x3e6f0 else if cid =? 3 then 0x3e880
else if cid =? 5 then 0x3ea2c else 0;
pc_asan_memcpy := 0x558e0;   pc_asan_memset := 0x55d7c;
pc_wrap_memcpy := 0x558dc;   pc_wrap_memset := 0x558d8;   pc_wrap_memcmp := 0x43a34;  pc_wrap_bcmp := 0x43a38;
pc_wrap_read := 0x43a44;     pc_wrap_fwrite := 0x43a48;   pc_wrap_vprintf := 0x43a54; pc_wrap_vfprintf := 0x43a58;
pc_wrap_fprintf := 0x43a60;  pc_wrap_memchr := 0x43a3c;   pc_wrap_strnlen := 0x43a10;
pc_region_is_poisoned := 0x58698;
pc_spin_mmapdie := 0x64288;  pc_spin_batch := 0x37638;    pc_spin_freearray := 0x36014; pc_spin_shadow := 0x72790
|}.
