(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build; the fopen/fclose wrapper, REAL and GOT definitions and their two tfib_icells cells are dropped (fuzz_command's image has neither function); A_RWA, A_WB, A_TRAILER and A_PATH, cgif's sink-file strings, are 0, since fuzz_command's image holds none of them and nothing fuzz_command reaches reads them. *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/AE2k.v (the twin of cgif_file_fuzzer's lib/YE2k.v), with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x45190.
Definition FF_pc_wrap_fwrite : Z := 0x451b0.
Definition FF_pc_wrap_fflush : Z := 0x451f0.
Definition FF_real_strchr : Z := 0x9ebd4.
Definition FF_real_fwrite : Z := 0x9ac38.
Definition FF_real_fflush : Z := 0x9a6cc.
Definition FF_got_strchr : Z := 0xa7c90.
Definition FF_got_fwrite : Z := 0xa7cd0.
Definition FF_got_fflush : Z := 0xa7d40.
Definition FF_meta_ptr : Z := 0xb0480.
Definition FF_meta_mem : Z := 0xb0488.
Definition FF_got_cflags : Z := 0xa5f40.
Definition FF_cflags : Z := 0x142768.
Definition FF_got_shadow : Z := 0xa5f50.
Definition FF_SB : Z := 0x7fff8000.
(* cgif's sink-file strings; fuzz_command's harness opens no file *)
Definition A_RWA : Z := 0.
Definition A_WB : Z := 0.
Definition A_TRAILER : Z := 0.
Definition A_PATH : Z := 0.
Definition A_ofl_lock : Z := 0x604808.
Definition A_ofl_head : Z := 0x604810.
Definition A_threaded : Z := 0x6043a9.
Definition A_need_locks : Z := 0x6043ab.
Definition A_stdio_read : Z := 0x9a25c.
Definition A_stdio_write : Z := 0x9a37c.
Definition A_stdio_seek : Z := 0x9a374.
Definition A_stdio_close : Z := 0x9a230.
Definition FF_got_canary : Z := 0xa6bf8.
Definition FF_canary : Z := 0x604158.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a8.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close A_PATH A_WB A_RWA A_TRAILER A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
