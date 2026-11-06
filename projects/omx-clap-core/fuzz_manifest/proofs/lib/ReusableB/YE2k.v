(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE2k.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to omx-clap-core/fuzz_manifest's ASan build. *)
(* Modified by Theorem Labs, 2026-10: a Theorem Labs lane's changes to lib/A/AE2k.v (a30c06078e9..5d8d8a15571) carried onto the image-B file by merge3.py. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x41340.
Definition FF_pc_wrap_fwrite : Z := 0x41358.
Definition FF_pc_wrap_fflush : Z := 0x41394.
Definition FF_real_strchr : Z := 0x92d9c.
Definition FF_real_fwrite : Z := 0x8ee40.
Definition FF_real_fflush : Z := 0x8e8d4.
Definition FF_got_strchr : Z := 0x9b9d0.
Definition FF_got_fwrite : Z := 0x9ba00.
Definition FF_got_fflush : Z := 0x9ba68.
Definition FF_meta_ptr : Z := 0xa18c0.
Definition FF_meta_mem : Z := 0xa18c8.
Definition FF_got_cflags : Z := 0x99c88.
Definition FF_cflags : Z := 0x133ba8.
Definition FF_got_shadow : Z := 0x99c98.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5f5760.
Definition A_ofl_head : Z := 0x5f5768.
Definition A_threaded : Z := 0x5f5301.
Definition A_need_locks : Z := 0x5f5303.
Definition A_stdio_read : Z := 0x8e464.
Definition A_stdio_write : Z := 0x8e584.
Definition A_stdio_seek : Z := 0x8e57c.
Definition A_stdio_close : Z := 0x8e438.
Definition FF_got_canary : Z := 0x9a920.
Definition FF_canary : Z := 0x5f50b0.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x10398.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite); (FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. The old fixed disjunction gave ofl_lock 16 bytes, A_ofl_lock .. A_ofl_lock + 16: the 4 bytes of the lock (fuzz_manifest.asan-ubsan's ofl_lock has size 4), 4 bytes of padding, and the 8 bytes of the ofl head (A_ofl_head = A_ofl_lock + 8); the head is the second disjunct of aenv_addr, so ak_owned holds A_ofl_lock .. A_ofl_lock + 8 only. YE01's ail_env_static asks for exactly that: ak_owned misses the head. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 8); (FF_canary, 8)].
(* fuzz_manifest writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
