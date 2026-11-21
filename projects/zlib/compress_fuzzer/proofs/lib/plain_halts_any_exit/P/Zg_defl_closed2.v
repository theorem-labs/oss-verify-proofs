(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_trees_iface Z_defl_iface
     Zg_adler32_iface Zg_defl_iface Zg_defl_iface2 Zg_defl_closed Zg_fast Zg_defl2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem deflate_fast_g : deflate_fast_stmtg.
Proof. exact (deflate_fast_specg fill_window_g tr_flush_block_g tr_flush_bits_g). Qed.

Theorem deflate_in_g2 : deflate_in_stmtg2.
Proof. exact (deflate_in_specg2 deflate_stored_g deflate_fast_g deflate_slow_g tr_flush_bits_g). Qed.
