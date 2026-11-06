(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
(* Modified by Theorem Labs, 2026-10: pc_stack_malloc holds omx-clap-core/fuzz_state.asan's __asan_stack_malloc_0 / _1 / _3 (0x3d484, 0x3d5f8, 0x3d788); fuzz_state has no _2. The other fields are relocated by the RELOC lane. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x5324c;        pc_wrap_malloc := 0x53074;   pc_malloc_ra0 := 0x53314;
pc_free := 0x5307c;          pc_wrap_free := 0x53070;     pc_free_ra0 := 0x531b4;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d484 else if cid =? 1 then 0x3d5f8 else if cid =? 3 then 0x3d788 else 0;
pc_asan_memcpy := 0x51d20;   pc_asan_memset := 0x521bc;
pc_wrap_memcpy := 0x51d1c;   pc_wrap_memset := 0x51d18;   pc_wrap_memcmp := 0x42664;  pc_wrap_bcmp := 0x42668;
pc_wrap_read := 0x42674;     pc_wrap_fwrite := 0x42678;   pc_wrap_vprintf := 0x42684; pc_wrap_vfprintf := 0x42688;
pc_wrap_fprintf := 0x42690;  pc_wrap_memchr := 0x4266c;   pc_wrap_strnlen := 0x42658;
pc_region_is_poisoned := 0x54be4;
pc_spin_mmapdie := 0x60470;  pc_spin_batch := 0x36540;    pc_spin_freearray := 0x34f1c; pc_spin_shadow := 0x6e978
|}.
