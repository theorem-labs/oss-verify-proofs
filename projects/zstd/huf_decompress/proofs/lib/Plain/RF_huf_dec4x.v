(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_disp
  RF_huf_dx4 RF_huf_y4s_iface RF_huf_dec4x2 RF_huf_y4sf.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_dec4x () := "C59OSSVerify5KrLib5Plain:RF_huf_dx4=dec_4x1_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RF_huf_y4sf=y4_slow_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RF_huf_dec4x2Bdec_4x2_proof_slowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RF_huf_disp?huf_dec_4x_dispC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~".

Theorem huf_dec_4x_closed {rc : runConstT} : huf_dec_stmt huf_dt_ok PHUF_DEC_4X.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_dec4x ()) [] "h02rcp;1p;2g0000j13Tg0013j12Tg0027j20Tg003Bj21Tg004HR0f0R1#3%21,01'1X00P1O1W0o"). Qed.
