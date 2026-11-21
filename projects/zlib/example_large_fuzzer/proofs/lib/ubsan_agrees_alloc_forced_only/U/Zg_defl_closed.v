(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_trees_iface Z_defl_iface Z_tr_stored Z_tr_fbubsan Z_trees_closed
     Zg_adler32_iface Zg_adler32 Zg_defl_iface Zg_sto Zg_fw Zg_slow Zg_defl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma tr_stored_block_g : tr_stored_block_stmt.
Proof. exact tr_stored_block_spec. Qed.

Lemma tr_flush_bits_g : tr_flush_bits_stmt.
Proof. exact tr_flush_bits_closed. Qed.

(* [comment removed for export] *)
Lemma tr_flush_block_gE : tr_flush_block_stmtE.
Proof.
  unfold tr_flush_block_stmtE. intros until m. intros DR MI RC STK LO AL BEL BI FBS FE.
  apply (tr_flush_block_finalU L s buf len last lo); try assumption. exact (flush_ubsan_facts s last FE buf len).
Qed.

Theorem fill_window_g : fill_window_stmtg.
Proof. exact (fill_window_specg adler32_g). Qed.

Theorem deflate_stored_g : deflate_stored_stmt.
Proof. exact (deflate_stored_spec tr_stored_block_g tr_flush_bits_g adler32_g). Qed.

Theorem deflate_slow_g : deflate_slow_stmtg.
Proof. exact (deflate_slow_specg fill_window_g tr_flush_block_gE tr_flush_bits_g). Qed.

Theorem deflate_in_g : deflate_in_stmtg.
Proof. exact (deflate_in_specg deflate_stored_g deflate_slow_g tr_flush_bits_g). Qed.
