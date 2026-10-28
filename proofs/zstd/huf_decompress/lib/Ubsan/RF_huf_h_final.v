(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg Harness_iface RF_huf_iface RF_huf_h_iface RF_huf_h_asm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RF_huf_x1t RF_huf_x2t RF_huf_dec1x RF_huf_dec4x.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.

Section CANSEC1. Context {rc : runConstT}.
Theorem fuzz_one_final : fuzz_one_stmt.
Proof.
  exact (fuzz_one_closed huf_dt_ok huf_rdt_x1_proof huf_rdt_x2_proof huf_dec_1x_closed huf_dec_4x_closed).
Qed.
End CANSEC1.
