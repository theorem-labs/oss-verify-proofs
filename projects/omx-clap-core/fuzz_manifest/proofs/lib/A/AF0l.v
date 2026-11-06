(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 26 address literal(s) rewritten, module paths changed; pc_stack_malloc is fun _ => 0 because fuzz_manifest.asan has no __asan_stack_malloc_* code. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52f90;        pc_wrap_malloc := 0x52dbc;   pc_malloc_ra0 := 0x53058;
pc_free := 0x52dc0;          pc_wrap_free := 0x52db8;     pc_free_ra0 := 0x52ef8;
pc_stack_malloc := fun _ => 0;
pc_asan_memcpy := 0x51a68;   pc_asan_memset := 0x51f04;
pc_wrap_memcpy := 0x51a64;   pc_wrap_memset := 0x51a60;   pc_wrap_memcmp := 0x412e4;  pc_wrap_bcmp := 0x412e8;
pc_wrap_read := 0x412f4;     pc_wrap_fwrite := 0x412f8;   pc_wrap_vprintf := 0x41304; pc_wrap_vfprintf := 0x41308;
pc_wrap_fprintf := 0x41310;  pc_wrap_memchr := 0x412ec;   pc_wrap_strnlen := 0x412cc;
pc_region_is_poisoned := 0x545e4;
pc_spin_mmapdie := 0x5fe70;  pc_spin_batch := 0x35a88;    pc_spin_freearray := 0x34464; pc_spin_shadow := 0x6e378
|}.
