(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
(* Modified by Theorem Labs, 2026-10: cgif's output-file strings (A_PATH, A_WB, A_RWA, A_TRAILER) dropped (fuzz_state.asan has none of them and links no fopen or fclose), so tfib_K's four string fields are 0 and asink_strs is never stated for it. FF_mask stays 0x103c0: that is where fuzz_state.asan stores its copy of the 0xafffff00000fffff constant (file offset 0x3c0, the only copy in the image). tfib_owned is the sink's own static cells (ak_owned), the cells fuzz_state's aenv_addr named before the sink kit took the shared parameter form. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x42660.
Definition FF_pc_wrap_fwrite : Z := 0x42678.
Definition FF_pc_wrap_fflush : Z := 0x426b4.
Definition FF_real_strchr : Z := 0x98f1c.
Definition FF_real_fwrite : Z := 0x92ac0.
Definition FF_real_fflush : Z := 0x92554.
Definition FF_got_strchr : Z := 0xa1418.
Definition FF_got_fwrite : Z := 0xa1448.
Definition FF_got_fflush : Z := 0xa14b0.
Definition FF_meta_ptr : Z := 0xa7780.
Definition FF_meta_mem : Z := 0xa7788.
Definition FF_got_cflags : Z := 0x9f6e0.
Definition FF_cflags : Z := 0x139a68.
Definition FF_got_shadow : Z := 0x9f6f0.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5fb620.
Definition A_ofl_head : Z := 0x5fb628.
Definition A_threaded : Z := 0x5fb1c1.
Definition A_need_locks : Z := 0x5fb1c3.
Definition A_stdio_read : Z := 0x920e4.
Definition A_stdio_write : Z := 0x92204.
Definition A_stdio_seek : Z := 0x921fc.
Definition A_stdio_close : Z := 0x920b8.
Definition FF_got_canary : Z := 0xa0378.
Definition FF_canary : Z := 0x5faf70.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103c0.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. The old fixed disjunction gave ofl_lock 16 bytes, A_ofl_lock .. A_ofl_lock + 16; those are the 8 bytes of the lock and the 8 bytes of the ofl head (A_ofl_head = A_ofl_lock + 8), and the head is the second disjunct of aenv_addr, so ak_owned holds the lock's 8 bytes only. YE01's ail_env_static asks for exactly that: ak_owned misses the head. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 8); (FF_canary, 8)].
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
