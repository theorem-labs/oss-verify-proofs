(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed; its address literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv maps them; the literals it does not map are still cgif_file_fuzzer.asan's (listed in the commit that moved them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x53910;        pc_wrap_malloc := 0x53738;   pc_malloc_ra0 := 0x539d8;
pc_free := 0x53740;          pc_wrap_free := 0x53734;     pc_free_ra0 := 0x53878;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3db48 else if cid =? 1 then 0x3dcbc else if cid =? 3 then 0x3de4c else 0;
pc_asan_memcpy := 0x523e4;   pc_asan_memset := 0x52880;
pc_wrap_memcpy := 0x523e0;   pc_wrap_memset := 0x523dc;   pc_wrap_memcmp := 0x42d28;  pc_wrap_bcmp := 0x42d2c;
pc_wrap_read := 0x42d38;     pc_wrap_fwrite := 0x42d3c;   pc_wrap_vprintf := 0x42d48; pc_wrap_vfprintf := 0x42d4c;
pc_wrap_fprintf := 0x42d54;  pc_wrap_memchr := 0x42d30;   pc_wrap_strnlen := 0x42d1c;
pc_region_is_poisoned := 0x552a8;
pc_spin_mmapdie := 0x60b34;  pc_spin_batch := 0x36c04;    pc_spin_freearray := 0x355e0; pc_spin_shadow := 0x6f03c
|}.
