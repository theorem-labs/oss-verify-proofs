(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Restated for fuzz_disco's asan-ubsan image, in the form of a Theorem Labs lane's A/AE2k.v: every address is disco's, read
   from its symbol table, its GOT contents or (FF_mask) its rodata by value; fopen / fclose and their cells are dropped,
   since disco links neither. cgif's harness strings A_PATH / A_WB / A_RWA / A_TRAILER are removed, as
   fuzz_disco.asan-ubsan holds none of them, so tfib_K's four string fields are 0; tfib_owned is the sink's own static
   cells (ak_owned), as in a Theorem Labs lane's release form of the sink (lib/Reusable/YE00.v). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x42a48.
Definition FF_pc_wrap_fwrite : Z := 0x42a60.
Definition FF_pc_wrap_fflush : Z := 0x42a9c.
Definition FF_real_strchr : Z := 0x9a00c.
Definition FF_real_fwrite : Z := 0x960c4.
Definition FF_real_fflush : Z := 0x95b58.
Definition FF_got_strchr : Z := 0xa25c0.
Definition FF_got_fwrite : Z := 0xa25f0.
Definition FF_got_fflush : Z := 0xa2658.
Definition FF_meta_ptr : Z := 0xa8cc0.
Definition FF_meta_mem : Z := 0xa8cc8.
Definition FF_got_cflags : Z := 0xa08a0.
Definition FF_cflags : Z := 0x13afa8.
Definition FF_got_shadow : Z := 0xa08b0.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5fcb00.
Definition A_ofl_head : Z := 0x5fcb08.
Definition A_threaded : Z := 0x5fc6a1.
Definition A_need_locks : Z := 0x5fc6a3.
Definition A_stdio_read : Z := 0x956e8.
Definition A_stdio_write : Z := 0x95808.
Definition A_stdio_seek : Z := 0x95800.
Definition A_stdio_close : Z := 0x956bc.
Definition FF_got_canary : Z := 0xa1538.
Definition FF_canary : Z := 0x5fc450.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103b8.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite); (FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
(* fuzz_disco writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
