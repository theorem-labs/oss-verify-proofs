(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YF0l.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan+UBSan build (fuzz_state.asan-ubsan). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x532bc;        pc_wrap_malloc := 0x530e4;   pc_malloc_ra0 := 0x53384;
pc_free := 0x530ec;          pc_wrap_free := 0x530e0;     pc_free_ra0 := 0x53224;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d4f4 else if cid =? 1 then 0x3d668 else if cid =? 3 then 0x3d7f8 else 0;
pc_asan_memcpy := 0x51d90;   pc_asan_memset := 0x5222c;
pc_wrap_memcpy := 0x51d8c;   pc_wrap_memset := 0x51d88;   pc_wrap_memcmp := 0x426d4;  pc_wrap_bcmp := 0x426d8;
pc_wrap_read := 0x426e4;     pc_wrap_fwrite := 0x426e8;   pc_wrap_vprintf := 0x426f4; pc_wrap_vfprintf := 0x426f8;
pc_wrap_fprintf := 0x42700;  pc_wrap_memchr := 0x426dc;   pc_wrap_strnlen := 0x426c8;
pc_region_is_poisoned := 0x54c54;
pc_spin_mmapdie := 0x604e0;  pc_spin_batch := 0x365b0;    pc_spin_freearray := 0x34f8c; pc_spin_shadow := 0x6e9e8
|}.
