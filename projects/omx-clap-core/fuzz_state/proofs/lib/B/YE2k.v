(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE2k.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan+UBSan build (fuzz_state.asan-ubsan). *)
(* Modified by Theorem Labs, 2026-10: cgif's output-file strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen / fclose wrapper, real and GOT cells are dropped: fuzz_state.asan-ubsan has none of those strings and links no fopen or fclose (its __wrap_ table runs 0x426c4 .. 0x42750 with no fopen or fclose slot). tfib_K and tfib_icells follow. FF_mask stays 0x103c0: fuzz_state.asan-ubsan stores the word 0xafffff00000fffff only there. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x426d0.
Definition FF_pc_wrap_fwrite : Z := 0x426e8.
Definition FF_pc_wrap_fflush : Z := 0x42724.
Definition FF_real_strchr : Z := 0x99438.
Definition FF_real_fwrite : Z := 0x92fdc.
Definition FF_real_fflush : Z := 0x92a70.
Definition FF_got_strchr : Z := 0xa1938.
Definition FF_got_fwrite : Z := 0xa1968.
Definition FF_got_fflush : Z := 0xa19d0.
Definition FF_meta_ptr : Z := 0xa7c80.
Definition FF_meta_mem : Z := 0xa7c88.
Definition FF_got_cflags : Z := 0x9fc00.
Definition FF_cflags : Z := 0x139f68.
Definition FF_got_shadow : Z := 0x9fc10.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5fbb20.
Definition A_ofl_head : Z := 0x5fbb28.
Definition A_threaded : Z := 0x5fb6c1.
Definition A_need_locks : Z := 0x5fb6c3.
Definition A_stdio_read : Z := 0x92600.
Definition A_stdio_write : Z := 0x92720.
Definition A_stdio_seek : Z := 0x92718.
Definition A_stdio_close : Z := 0x925d4.
Definition FF_got_canary : Z := 0xa0898.
Definition FF_canary : Z := 0x5fb470.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103c0.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard (B values, fuzz_state.asan-ubsan .symtab; the same shape as lib/A/AE2k.v, a Theorem Labs lane's ak_owned sink taken by S0 400b2a240b3). ofl_lock is 8 bytes; the ofl head A_ofl_head = A_ofl_lock + 8 is the second disjunct of aenv_addr, so ak_owned holds the lock's 8 bytes only. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 8); (FF_canary, 8)].
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
