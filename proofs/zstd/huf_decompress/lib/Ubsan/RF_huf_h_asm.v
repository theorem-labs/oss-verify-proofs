(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RMalloc_iface Harness_iface RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RF_huf_h_iface RF_huf_iface_m RF_huf_prod RF_huf_h_malloc RF_huf_h.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_h_asm () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_rdt_stmtC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_stmtC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_malloc_spec<rmalloc_specC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_h_mallocAfuzz_malloc_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_h_mallocAprod_create_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_free_spec@rfree_spec_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_h_malloc?prod_free_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod?prod_i32r_proofC5ARocqVerifyHarness?AgentSubmission5Ubsan8RF_huf_h>fuzz_one_proofK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface;PHUF_RDT_X1C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface;PHUF_RDT_X2C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface;PHUF_DEC_1XC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface;PHUF_DEC_4XC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_prod?prod_u32r_proof".

Section CANSEC1. Context {rc : runConstT}.
Theorem fuzz_one_closed : forall dt_ok : (word -> option byte) -> Z -> Z -> Prop,
  huf_rdt_stmt dt_ok PHUF_RDT_X1 -> huf_rdt_stmt dt_ok PHUF_RDT_X2 ->
  huf_dec_stmt dt_ok PHUF_DEC_1X -> huf_dec_stmt dt_ok PHUF_DEC_4X ->
  fuzz_one_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_asm ()) ["CANSEC1"] "h04DEC1h14DEC4h24RDT1h34RDT2h45dt_okp;1p;2p;<g0000j10Tg000Uj11Tg0013j12Tg001Vj15Tg0028j24Tg003>j23Tg004Dj1<Tg005Jj2;Tg006Vj2:Tg007bj16Tg008jj27Tg00:4j18Tg00;:l<9Tg00<<#0#0#0R0#0#0#0#1#2%10#2#5[g00<aR0p-0\0[[f0R0g00=?'4f1R1g00>D'4f2R2g00?I'3f3R3g00@N'3p,2rcR4f4%<4,;4R5,:4P5%64R51745g00ASR5%85P3P2P1P0M<9W1W0W3W2W4o"). Qed.
End CANSEC1.
