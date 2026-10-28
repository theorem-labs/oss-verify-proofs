(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_disp
  RF_huf_dx4 RF_huf_y4s_iface RF_huf_dec4x2 RF_huf_y4sf.

Theorem huf_dec_4x_closed {rc : runConstT} : huf_dec_stmt huf_dt_ok PHUF_DEC_4X.
Proof.
  exact (huf_dec_4x_disp dec_4x1_proof (dec_4x2_proof_slow y4_slow_proof)). Qed.
