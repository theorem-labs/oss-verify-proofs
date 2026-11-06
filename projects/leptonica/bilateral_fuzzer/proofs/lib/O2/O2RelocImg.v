(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec StreamSim.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocImg CanonImg RelocSpan CanonSpans.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2RelocImg () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common5Reloc8RelocImg;cells_checkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg;canon_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib6Common9StreamSim7wseg_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib6Common5Reloc9RelocSpan8hull_okbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9RelocSpan;spans_checkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc:CanonSpans;canon_spansC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9RelocSpan<orders_checkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc:CanonSpans;canon_orderC1?~~~~~~~~~~~~~~~".
Local Open Scope Z_scope.

Lemma o2_cells_ok : @cells_check o2_reloc canon_cells = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2RelocImg ()) [] "p;2p;3g0000j22Tg000Jj21Tg001Pj30Tg001jR0g002JR1'2g002jg003b'1=001do"). Qed.

Definition o2_img : RelocImg o2_reloc := {| rl_cells_ok := o2_cells_ok |}.

Lemma o2_data_wseg : wseg_ok (@rl_segs o2_reloc) (Z_to_bv 64 0x39000) (Z.to_nat (@rl_img_hi o2_reloc - 0x39000)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2RelocImg ()) [] "p;2p;1p;3g0000j2<Tg004hj1;Tg005gj13Tg006Ej11Tg006jj1:Tg007Hj29Tg007nj14Tg008oj25Tg009Lj16Tg009lj37Tg001Pj38Tg00:ij12Tf0#2#2p=0g001jR0g002JR1'<g002jR2#;g00;NR3#0#0#0#3%13#1#0#1#0#0#0#0#0#0#:R3'9%42/53#637=801do"). Qed.

Lemma o2_data_ok : (0 <=? 0x39000) && (0x39000 <=? @rl_img_hi o2_reloc) && (@rl_img_hi o2_reloc <=? 2^32) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2RelocImg ()) [] "p;2g0000j20Tg001jg002J'0o"). Qed.

Definition o2_data : RelocData o2_reloc := {| rl_data_lo := 0x39000; rl_data_ok := o2_data_ok; rl_data_wseg := o2_data_wseg |}.

Lemma o2_hull_ok : @hull_okb o2_reloc o2_data = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2RelocImg ()) [] "p;2p;3g0000j22Tg00<3j21Tg001Pj30Tg001jR0g002JR1'2g002jg00=7'1=001do"). Qed.
Lemma o2_spans_ok : @spans_check o2_reloc o2_data canon_spans = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2RelocImg ()) [] "p;2p;3g0000j22Tg00>1j31Tg001Pj30Tg001jR0g002JR1'2g002jg00=7g00?831=001do"). Qed.
Lemma o2_orders_ok : @orders_check o2_reloc canon_spans canon_order = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2RelocImg ()) [] "p;2p;3g0000j22Tg00@@j31Tg001Pj30Tg001jR0g002JR1'2g002jg00?8g00AH31=001do"). Qed.
Definition o2_spans : RelocSpans o2_reloc o2_data := {| rl_hull_ok := o2_hull_ok; rl_spans_ok := o2_spans_ok; rl_orders_ok := o2_orders_ok |}.
