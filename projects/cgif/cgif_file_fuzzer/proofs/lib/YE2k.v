(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x4192c.
Definition FF_pc_wrap_fwrite : Z := 0x41944.
Definition FF_pc_wrap_fopen : Z := 0x41980.
Definition FF_pc_wrap_fflush : Z := 0x41984.
Definition FF_pc_wrap_fclose : Z := 0x41988.
Definition FF_real_strchr : Z := 0x97a04.
Definition FF_real_fwrite : Z := 0x93a7c.
Definition FF_real_fopen : Z := 0x937b4.
Definition FF_real_fflush : Z := 0x93380.
Definition FF_real_fclose : Z := 0x93158.
Definition FF_got_strchr : Z := 0x9ff30.
Definition FF_got_fwrite : Z := 0x9ff60.
Definition FF_got_fopen : Z := 0x9ffc8.
Definition FF_got_fflush : Z := 0x9ffd0.
Definition FF_got_fclose : Z := 0x9ffd8.
Definition FF_meta_ptr : Z := 0xa5ac0.
Definition FF_meta_mem : Z := 0xa5ac8.
Definition FF_got_cflags : Z := 0x9e1f8.
Definition FF_cflags : Z := 0x137da8.
Definition FF_got_shadow : Z := 0x9e208.
Definition FF_SB : Z := 0x7fff8000.
Definition A_RWA : Z := 0x200e6.
Definition A_WB : Z := 0x20e20.
Definition A_TRAILER : Z := 0x20e60.
Definition A_PATH : Z := 0x20dc0.
Definition A_ofl_lock : Z := 0x5f9900.
Definition A_ofl_head : Z := 0x5f9908.
Definition A_threaded : Z := 0x5f94a1.
Definition A_need_locks : Z := 0x5f94a3.
Definition A_stdio_read : Z := 0x92e40.
Definition A_stdio_write : Z := 0x92f60.
Definition A_stdio_seek : Z := 0x92f58.
Definition A_stdio_close : Z := 0x92e14.
Definition FF_got_canary : Z := 0x9eea8.
Definition FF_canary : Z := 0x5f9250.
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
