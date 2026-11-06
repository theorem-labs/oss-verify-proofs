(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed; its image addresses relocated to omx-clap-core/fuzz_preset's ASan build through code-verified pairs; entries with no preset counterpart are listed in the commit that relocated them. tfib_K's four string fields are 0 and tfib_owned is the sink's own static cells (ak_owned): the text of libreac/fuzz_grant's lib/A/AE2k.v at port-grant's release commit 4d244de18f0. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x42d24.
Definition FF_pc_wrap_fwrite : Z := 0x42d3c.
Definition FF_pc_wrap_fflush : Z := 0x42d78.
Definition FF_real_strchr : Z := 0x9b7b0.
Definition FF_real_fwrite : Z := 0x95354.
Definition FF_real_fflush : Z := 0x94de8.
Definition FF_got_strchr : Z := 0xa3d38.
Definition FF_got_fwrite : Z := 0xa3d68.
Definition FF_got_fflush : Z := 0xa3dd0.
Definition FF_meta_ptr : Z := 0xaa700.
Definition FF_meta_mem : Z := 0xaa708.
Definition FF_got_cflags : Z := 0xa2000.
Definition FF_cflags : Z := 0x13c9e8.
Definition FF_got_shadow : Z := 0xa2010.
Definition FF_SB : Z := 0x7fff8000.
Definition A_ofl_lock : Z := 0x5fe5e0.
Definition A_ofl_head : Z := 0x5fe5e8.
Definition A_threaded : Z := 0x5fe181.
Definition A_need_locks : Z := 0x5fe183.
Definition A_stdio_read : Z := 0x94978.
Definition A_stdio_write : Z := 0x94a98.
Definition A_stdio_seek : Z := 0x94a90.
Definition A_stdio_close : Z := 0x9494c.
Definition FF_got_canary : Z := 0xa2c98.
Definition FF_canary : Z := 0x5fdf30.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103b8.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
(* The sink's own static cells, as (address, size): __libc.threaded, __libc.need_locks, ofl_lock and __stack_chk_guard. *)
Definition tfib_owned : list (Z * Z) := [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 4); (FF_canary, 8)].
(* fuzz_preset writes no file: ak_path, ak_mode, ak_rwa and ak_trailer are 0, and asink_strs is never stated for it. *)
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close 0 0 0 0 A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells tfib_owned.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
