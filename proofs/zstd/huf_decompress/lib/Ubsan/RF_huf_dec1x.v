(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_disp RF_huf_dx1e RF_huf_dx2e.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_dec1x () := "C5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_dx1e=dec_1x1_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_dx2e=dec_1x2_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_disp?huf_dec_1x_dispI5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00".

Theorem huf_dec_1x_closed {rc : runConstT} : huf_dec_stmt huf_dt_ok PHUF_DEC_1X.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_dec1x ()) [] "h02rcp;1p;2g0000j12Tg0014j11Tg0028j20Tg003>R0f0R1#2%11'0X00P1O1W0o"). Qed.
