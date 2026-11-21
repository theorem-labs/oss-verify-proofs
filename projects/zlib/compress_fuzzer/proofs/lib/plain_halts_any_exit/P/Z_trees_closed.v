(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_trees_iface Z_tr_bt_iface Z_tr_bits Z_tr_init Z_tr_fb11 Z_tr_bt19.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition tr_init_closed : tr_init_stmt := tr_init_spec.
Definition tr_flush_bits_closed : tr_flush_bits_stmt := tr_flush_bits_spec.
Definition tr_flush_block_closed : build_tree_stmt -> tr_flush_block_stmt := tr_flush_block_spec.

Theorem trees_closed : build_tree_stmt -> tr_init_stmt /\ tr_flush_bits_stmt /\ tr_flush_block_stmt.
Proof. intros BT. split; [exact tr_init_spec|]. split; [exact tr_flush_bits_spec| exact (tr_flush_block_spec BT)]. Qed.

Definition build_tree_closed : build_tree_stmt := build_tree_spec.
Definition tr_flush_block_final : tr_flush_block_stmt := tr_flush_block_closed build_tree_spec.
Theorem trees_closed_final : tr_init_stmt /\ tr_flush_bits_stmt /\ tr_flush_block_stmt.
Proof. exact (trees_closed build_tree_closed). Qed.
