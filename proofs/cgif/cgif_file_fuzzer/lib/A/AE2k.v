(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x418fc.
Definition FF_pc_wrap_fwrite : Z := 0x41914.
Definition FF_pc_wrap_fopen : Z := 0x41950.
Definition FF_pc_wrap_fflush : Z := 0x41954.
Definition FF_pc_wrap_fclose : Z := 0x41958.
Definition FF_real_strchr : Z := 0x97790.
Definition FF_real_fwrite : Z := 0x93808.
Definition FF_real_fopen : Z := 0x93540.
Definition FF_real_fflush : Z := 0x9310c.
Definition FF_real_fclose : Z := 0x92ee4.
Definition FF_got_strchr : Z := 0x9fcc0.
Definition FF_got_fwrite : Z := 0x9fcf0.
Definition FF_got_fopen : Z := 0x9fd58.
Definition FF_got_fflush : Z := 0x9fd60.
Definition FF_got_fclose : Z := 0x9fd68.
Definition FF_meta_ptr : Z := 0xa5840.
Definition FF_meta_mem : Z := 0xa5848.
Definition FF_got_cflags : Z := 0x9df88.
Definition FF_cflags : Z := 0x137b28.
Definition FF_got_shadow : Z := 0x9df98.
Definition FF_SB : Z := 0x7fff8000.
Definition A_RWA : Z := 0x20124.
Definition A_WB : Z := 0x20e60.
Definition A_TRAILER : Z := 0x20ea0.
Definition A_PATH : Z := 0x20e00.
Definition A_ofl_lock : Z := 0x5f9680.
Definition A_ofl_head : Z := 0x5f9688.
Definition A_threaded : Z := 0x5f9221.
Definition A_need_locks : Z := 0x5f9223.
Definition A_stdio_read : Z := 0x92bcc.
Definition A_stdio_write : Z := 0x92cec.
Definition A_stdio_seek : Z := 0x92ce4.
Definition A_stdio_close : Z := 0x92ba0.
Definition FF_got_canary : Z := 0x9ec38.
Definition FF_canary : Z := 0x5f8fd0.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a0.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fclose, FF_real_fclose); (FF_got_fopen, FF_real_fopen); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close A_PATH A_WB A_RWA A_TRAILER A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
