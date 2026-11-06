(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE2k.v, with its module paths changed, and its fuzz_reply.asan-ubsan addresses relocated from cgif_file_fuzzer.asan-ubsan (28 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: fopen/fclose and cgif's sink strings cut (fuzz_reply links neither; Reusable/YE00.v mkASink without the four strings), as lib/A/AE2k.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x421f8.
Definition FF_pc_wrap_fwrite : Z := 0x42218.
(* cut: FF_pc_wrap_fopen (OLD 0x41980, no NEW twin) *)
Definition FF_pc_wrap_fflush : Z := 0x42254.
(* cut: FF_pc_wrap_fclose (OLD 0x41988, no NEW twin) *)
Definition FF_real_strchr : Z := 0x96f78.
Definition FF_real_fwrite : Z := 0x93000.
(* cut: FF_real_fopen (OLD musl fopen, not linked in fuzz_reply) *)
Definition FF_real_fflush : Z := 0x92a94.
(* cut: FF_real_fclose (OLD musl fclose 0x93158, not linked in fuzz_reply) *)
Definition FF_got_strchr : Z := 0x9fc88.
Definition FF_got_fwrite : Z := 0x9fcc8.
(* cut: FF_got_fopen (OLD .data 0x9ffc8, __interception::real_fopen) *)
Definition FF_got_fflush : Z := 0x9fd30.
(* cut: FF_got_fclose (OLD .data 0x9ffd8, __interception::real_fclose) *)
Definition FF_meta_ptr : Z := 0xa5e80.
Definition FF_meta_mem : Z := 0xa5e88.
Definition FF_got_cflags : Z := 0x9df40.
Definition FF_cflags : Z := 0x138168.
Definition FF_got_shadow : Z := 0x9df50.
Definition FF_SB : Z := 0x7fff8000.
(* cut: A_RWA, A_WB, A_TRAILER, A_PATH (cgif's sink strings "rwa", "wb", ";", "/tmp/out.gif"; absent in fuzz_reply.asan-ubsan) *)
Definition A_ofl_lock : Z := 0x5fa0e0.
Definition A_ofl_head : Z := 0x5fa0e8.
Definition A_threaded : Z := 0x5f9c81.
Definition A_need_locks : Z := 0x5f9c83.
Definition A_stdio_read : Z := 0x92624.
Definition A_stdio_write : Z := 0x92744.
Definition A_stdio_seek : Z := 0x9273c.
Definition A_stdio_close : Z := 0x925f8.
Definition FF_got_canary : Z := 0x9ebd8.
Definition FF_canary : Z := 0x5f9a30.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a0.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
