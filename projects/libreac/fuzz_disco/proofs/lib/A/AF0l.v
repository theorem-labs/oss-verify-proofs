(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build; pc_stack_malloc lists fuzz_disco's fake-stack classes 0, 1, 2, 3 and 6, read from its symbol table. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x535b8;        pc_wrap_malloc := 0x533e4;   pc_malloc_ra0 := 0x53680;
pc_free := 0x533e8;          pc_wrap_free := 0x533e0;     pc_free_ra0 := 0x53520;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d474 else if cid =? 1 then 0x3d5e8 else if cid =? 2 then 0x3d778 else if cid =? 3 then 0x3d914 else if cid =? 6 then 0x3dac0 else 0;
pc_asan_memcpy := 0x52090;   pc_asan_memset := 0x5252c;
pc_wrap_memcpy := 0x5208c;   pc_wrap_memset := 0x52088;   pc_wrap_memcmp := 0x429d4;  pc_wrap_bcmp := 0x429d8;
pc_wrap_read := 0x429e4;     pc_wrap_fwrite := 0x429e8;   pc_wrap_vprintf := 0x429f4; pc_wrap_vfprintf := 0x429f8;
pc_wrap_fprintf := 0x42a00;  pc_wrap_memchr := 0x429dc;   pc_wrap_strnlen := 0x429c8;
pc_region_is_poisoned := 0x54c0c;
pc_spin_mmapdie := 0x60498;  pc_spin_batch := 0x36530;    pc_spin_freearray := 0x34f0c; pc_spin_shadow := 0x6e9a0
|}.
