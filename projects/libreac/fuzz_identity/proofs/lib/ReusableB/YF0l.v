(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/YF0l.v, with its module paths and addresses changed; 1 of its 15 lines of code is new or changed and 1 line of the source is left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52de8;        pc_wrap_malloc := 0x52c14;   pc_malloc_ra0 := 0x52eb0;
pc_free := 0x52c18;          pc_wrap_free := 0x52c10;     pc_free_ra0 := 0x52d50;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3cfe8 else if cid =? 3 then 0x3d15c else if cid =? 4 then 0x3d308 else 0;
pc_asan_memcpy := 0x518c0;   pc_asan_memset := 0x51d5c;
pc_wrap_memcpy := 0x518bc;   pc_wrap_memset := 0x518b8;   pc_wrap_memcmp := 0x42204;  pc_wrap_bcmp := 0x42208;
pc_wrap_read := 0x42214;     pc_wrap_fwrite := 0x42218;   pc_wrap_vprintf := 0x42224; pc_wrap_vfprintf := 0x42228;
pc_wrap_fprintf := 0x42230;  pc_wrap_memchr := 0x4220c;   pc_wrap_strnlen := 0x421f8;
pc_region_is_poisoned := 0x5443c;
pc_spin_mmapdie := 0x5fcc8;  pc_spin_batch := 0x360a4;    pc_spin_freearray := 0x34a80; pc_spin_shadow := 0x6e1d0
|}.
