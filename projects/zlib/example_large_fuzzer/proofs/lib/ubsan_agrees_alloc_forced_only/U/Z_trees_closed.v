(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_drep Z_trees_iface Z_tr_bt_iface Z_tr_bits Z_tr_init Z_tr_fb11 Z_tr_bt19.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Definition tr_init_closed : tr_init_stmt := tr_init_spec.
Definition tr_flush_bits_closed : tr_flush_bits_stmt := tr_flush_bits_spec.
Definition tr_flush_block_closedU : build_tree_stmt -> tr_flush_block_stmtU := tr_flush_block_specU.

Definition tr_flush_block_closed :
  (forall s buf len last, fb_safe s buf len last -> BINV DS_PEND s -> fb_ubsan s buf len last) ->
  build_tree_stmt -> tr_flush_block_stmt :=
  fun H BT => tr_flush_block_of_ubsan H (tr_flush_block_specU BT).

(* [comment removed for export] *)
Definition build_tree_closed : build_tree_stmt := build_tree_spec.
Definition tr_flush_block_finalU : tr_flush_block_stmtU := tr_flush_block_closedU build_tree_spec.

