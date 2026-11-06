(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x542a4;        pc_wrap_malloc := 0x540cc;   pc_malloc_ra0 := 0x5436c;
pc_free := 0x540d4;          pc_wrap_free := 0x540c8;     pc_free_ra0 := 0x5420c;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d914 else if cid =? 1 then 0x3da88 else if cid =? 3 then 0x3dc18 else if cid =? 4 then 0x3ddc4 else 0;
pc_asan_memcpy := 0x52d78;   pc_asan_memset := 0x53214;
pc_wrap_memcpy := 0x52d74;   pc_wrap_memset := 0x52d70;   pc_wrap_memcmp := 0x43058;  pc_wrap_bcmp := 0x4305c;
pc_wrap_read := 0x43068;     pc_wrap_fwrite := 0x4306c;   pc_wrap_vprintf := 0x43078; pc_wrap_vfprintf := 0x4307c;
pc_wrap_fprintf := 0x43084;  pc_wrap_memchr := 0x43060;   pc_wrap_strnlen := 0x43048;
pc_region_is_poisoned := 0x55b30;
pc_spin_mmapdie := 0x61720;  pc_spin_batch := 0x369d0;    pc_spin_freearray := 0x353ac; pc_spin_shadow := 0x6fc28
|}.
