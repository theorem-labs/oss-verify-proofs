(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2k.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build; the fopen/fclose wrapper, REAL and GOT definitions and their two tfib_icells cells are dropped (fuzz_command's image has neither function); A_RWA, A_WB, A_TRAILER and A_PATH, cgif's sink-file strings, are 0, since fuzz_command's image holds none of them and nothing fuzz_command reaches reads them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AE2k.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AE2k.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YE00.
Import ListNotations.
Open Scope Z_scope.
Definition FF_pc_wrap_strchr : Z := 0x43ab4.
Definition FF_pc_wrap_fwrite : Z := 0x43ad4.
Definition FF_pc_wrap_fflush : Z := 0x43b10.
Definition FF_real_strchr : Z := 0x9b180.
Definition FF_real_fwrite : Z := 0x97154.
Definition FF_real_fflush : Z := 0x96be8.
Definition FF_got_strchr : Z := 0xa4f40.
Definition FF_got_fwrite : Z := 0xa4f80.
Definition FF_got_fflush : Z := 0xa4fe8.
Definition FF_meta_ptr : Z := 0xac000.
Definition FF_meta_mem : Z := 0xac008.
Definition FF_got_cflags : Z := 0xa3200.
Definition FF_cflags : Z := 0x13e2e8.
Definition FF_got_shadow : Z := 0xa3210.
Definition FF_SB : Z := 0x7fff8000.
(* cgif's sink-file strings; fuzz_command's harness opens no file *)
Definition A_RWA : Z := 0.
Definition A_WB : Z := 0.
Definition A_TRAILER : Z := 0.
Definition A_PATH : Z := 0.
Definition A_ofl_lock : Z := 0x5ffee8.
Definition A_ofl_head : Z := 0x5ffef0.
Definition A_threaded : Z := 0x5ffa89.
Definition A_need_locks : Z := 0x5ffa8b.
Definition A_stdio_read : Z := 0x96778.
Definition A_stdio_write : Z := 0x96898.
Definition A_stdio_seek : Z := 0x96890.
Definition A_stdio_close : Z := 0x9674c.
Definition FF_got_canary : Z := 0xa3e98.
Definition FF_canary : Z := 0x5ff838.
#[export] Instance tfib_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_ofl_head |}.
Definition FF_mask : Z := 0x103a0.
Definition FF_mask_val : Z := 0xafffff00000fffff.
Definition tfib_icells : list (Z * Z) :=
[(FF_got_fflush, FF_real_fflush); (FF_got_fwrite, FF_real_fwrite);
(FF_got_strchr, FF_real_strchr); (FF_mask, FF_mask_val)].
Definition tfib_K : asink_syms :=
mkASink A_stdio_read A_stdio_write A_stdio_seek A_stdio_close A_PATH A_WB A_RWA A_TRAILER A_threaded A_need_locks A_ofl_lock FF_meta_ptr FF_meta_mem FF_got_canary FF_canary
tfib_icells.
Lemma tfib_K_head : ak_ofl_head tfib_K = A_ofl_head.
Proof. reflexivity. Qed.
