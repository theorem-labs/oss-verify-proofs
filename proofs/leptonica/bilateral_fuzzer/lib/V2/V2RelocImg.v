(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec StreamSim.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocImg CanonImg RelocSpan CanonSpans.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2RelocImg () := "K47Corelib4Init5Logic2eq01C6ARocqVerifyHarness?AgentSubmission6Common5Reloc8RelocImg;cells_checkI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC6ARocqVerifyHarness?AgentSubmission6Common5Reloc8CanonImg;canon_cellsC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsK47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc9rl_img_hiC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission6Common9StreamSim7wseg_okK47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission6Common5Reloc9RelocSpan8hull_okbc5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg7v2_dataC6ARocqVerifyHarness?AgentSubmission6Common5Reloc9RelocSpan;spans_checkC6ARocqVerifyHarness?AgentSubmission6Common5Reloc:CanonSpans;canon_spansC6ARocqVerifyHarness?AgentSubmission6Common5Reloc9RelocSpan<orders_checkC6ARocqVerifyHarness?AgentSubmission6Common5Reloc:CanonSpans;canon_order".
Local Open Scope Z_scope.

Lemma v2_cells_ok : @cells_check v2_reloc canon_cells = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocImg ()) [] "p;2p;3g0000j22Tg000Jj21Tg001Pj30Tg001jR0g002JR1'2g002jg003b'1=001do"). Qed.

Definition v2_img : RelocImg v2_reloc := {| rl_cells_ok := v2_cells_ok |}.

Lemma v2_data_wseg : wseg_ok (@rl_segs v2_reloc) (Z_to_bv 64 0x45000) (Z.to_nat (@rl_img_hi v2_reloc - 0x45000)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocImg ()) [] "p;2p;1p;3g0000j2<Tg004hj1;Tg005gj13Tg006Ej11Tg006jj12Tg007Oj1:Tg007mj24Tg008Sj15Tg009Tj26Tg00:1j17Tg00:Qj38Tg001Pj39Tf0#1#1p=0g001jR0g002JR1'<g002jR2#;g00;NR3#0#0#0#3%13#0#2#1#2#0#0#0#0#0#0#:R3'4%52/63#738=901do"). Qed.

Lemma v2_data_ok : (0 <=? 0x45000) && (0x45000 <=? @rl_img_hi v2_reloc) && (@rl_img_hi v2_reloc <=? 2^32) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocImg ()) [] "p;2g0000j20Tg001jg002J'0o"). Qed.

Definition v2_data : RelocData v2_reloc := {| rl_data_lo := 0x45000; rl_data_ok := v2_data_ok; rl_data_wseg := v2_data_wseg |}.

Lemma v2_hull_ok : @hull_okb v2_reloc v2_data = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocImg ()) [] "p;2p;3g0000j22Tg00<3j21Tg001Pj30Tg001jR0g002JR1'2g002jg00=7'1=001do"). Qed.
Lemma v2_spans_ok : @spans_check v2_reloc v2_data canon_spans = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocImg ()) [] "p;2p;3g0000j22Tg00>1j31Tg001Pj30Tg001jR0g002JR1'2g002jg00=7g00?831=001do"). Qed.
Lemma v2_orders_ok : @orders_check v2_reloc canon_spans canon_order = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocImg ()) [] "p;2p;3g0000j22Tg00@@j31Tg001Pj30Tg001jR0g002JR1'2g002jg00?8g00AH31=001do"). Qed.
Definition v2_spans : RelocSpans v2_reloc v2_data := {| rl_hull_ok := v2_hull_ok; rl_spans_ok := v2_spans_ok; rl_orders_ok := v2_orders_ok |}.
