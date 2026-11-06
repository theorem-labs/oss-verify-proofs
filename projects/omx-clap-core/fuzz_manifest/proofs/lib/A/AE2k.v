(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 24 address literal(s) rewritten, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: cgif's output-file strings (A_PATH, A_WB, A_RWA, A_TRAILER) and the fopen/fclose wrapper, real-function and GOT names dropped (fuzz_manifest.asan has none of them); tfib_K and tfib_icells without them; FF_mask moved to fuzz_manifest.asan's copy of the constant at 0x10398. *)
(* Modified by Theorem Labs, 2026-10: the sink kit is a Theorem Labs lane's shared parameter form (a working branch 4d244de18f0) instantiated for fuzz_manifest: tfib_owned is the sink's own static cells (ak_owned) and tfib_K's four string fields are 0 (fuzz_manifest writes no file). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x412e0.
Definition FF_pc_wrap_fwrite : Z := 0x412f8.
Definition FF_pc_wrap_fflush : Z := 0x41334.
Definition FF_real_strchr : Z := 0x92ab4.
Definition FF_real_fwrite : Z := 0x8eb58.
Definition FF_real_fflush : Z := 0x8e5ec.
Definition FF_got_strchr : Z := 0x9b6f0.
Definition FF_got_fwrite : Z := 0x9b720.
Definition FF_got_fflush : Z := 0x9b788.
Definition FF_meta_ptr : Z := 0xa15c0.
Definition FF_meta_mem : Z := 0xa15c8.
Definition FF_got_cflags : Z := 0x999a0.
Definition FF_cflags : Z := 0x1338a8.
Definition FF_got_shadow : Z := 0x999b0.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f5460.
Definition A_ofl_head : Z := 0x5f5468.
Definition A_threaded : Z := 0x5f5001.
Definition A_need_locks : Z := 0x5f5003.
Definition A_stdio_read : Z := 0x8e17c.
Definition A_stdio_write : Z := 0x8e29c.
Definition A_stdio_seek : Z := 0x8e294.
Definition A_stdio_close : Z := 0x8e150.
Definition FF_got_canary : Z := 0x9a638.
Definition FF_canary : Z := 0x5f4db0.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x10398.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite); (FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. The old fixed disjunction gave ofl_lock 16 bytes, A_ofl_lock .. A_ofl_lock + 16: the 4 bytes of the lock (fuzz_manifest.asan's ofl_lock has size 4), 4 bytes of padding, and the 8 bytes of the ofl head (A_ofl_head = A_ofl_lock + 8); the head is the second disjunct of aenv_addr, so ak_owned holds A_ofl_lock .. A_ofl_lock + 8 only. YE01's ail_env_static asks for exactly that: ak_owned misses the head. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 8); (FF_canary, 8)].
(* fuzz_manifest writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
