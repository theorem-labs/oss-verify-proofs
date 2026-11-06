(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed, its addresses moved to libreac/fuzz_grant's ASan build and the side-stack entries of classes 0 and 4, which fuzz_grant's program calls, added. *)
(* Relocated from proofs/libreac/fuzz_grant/lib/A/AF0l.v at 25e3d17bdb50 by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x538d8;        pc_wrap_malloc := 0x53704;   pc_malloc_ra0 := 0x539a0;
pc_free := 0x53708;          pc_wrap_free := 0x53700;     pc_free_ra0 := 0x53840;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d698 else if cid =? 1 then 0x3d80c else if cid =? 2 then 0x3d99c else if cid =? 4 then 0x3db38 else if cid =? 5 then 0x3dd04 else 0;
pc_asan_memcpy := 0x523b0;   pc_asan_memset := 0x5284c;
pc_wrap_memcpy := 0x523ac;   pc_wrap_memset := 0x523a8;   pc_wrap_memcmp := 0x42cf4;  pc_wrap_bcmp := 0x42cf8;
pc_wrap_read := 0x42d04;     pc_wrap_fwrite := 0x42d08;   pc_wrap_vprintf := 0x42d14; pc_wrap_vfprintf := 0x42d18;
pc_wrap_fprintf := 0x42d20;  pc_wrap_memchr := 0x42cfc;   pc_wrap_strnlen := 0x42ce8;
pc_region_is_poisoned := 0x54f2c;
pc_spin_mmapdie := 0x607b8;  pc_spin_batch := 0x36754;    pc_spin_freearray := 0x35130; pc_spin_shadow := 0x6ecc0
|}.
