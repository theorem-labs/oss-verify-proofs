(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YF0l.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
(* Relocated from proofs/libreac/fuzz_decode/lib/YF0l.v at 88154566652a by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan-ubsan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x53914;        pc_wrap_malloc := 0x53740;   pc_malloc_ra0 := 0x539dc;
pc_free := 0x53744;          pc_wrap_free := 0x5373c;     pc_free_ra0 := 0x5387c;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d6f4 else if cid =? 1 then 0x3d868 else if cid =? 2 then 0x3d9f8 else if cid =? 3 then 0x3db94 else if cid =? 5 then 0x3dd40 else 0;
pc_asan_memcpy := 0x523ec;   pc_asan_memset := 0x52888;
pc_wrap_memcpy := 0x523e8;   pc_wrap_memset := 0x523e4;   pc_wrap_memcmp := 0x42d30;  pc_wrap_bcmp := 0x42d34;
pc_wrap_read := 0x42d40;     pc_wrap_fwrite := 0x42d44;   pc_wrap_vprintf := 0x42d50; pc_wrap_vfprintf := 0x42d54;
pc_wrap_fprintf := 0x42d5c;  pc_wrap_memchr := 0x42d38;   pc_wrap_strnlen := 0x42d24;
pc_region_is_poisoned := 0x54f68;
pc_spin_mmapdie := 0x607f4;  pc_spin_batch := 0x367b0;    pc_spin_freearray := 0x3518c; pc_spin_shadow := 0x6ecfc
|}.
