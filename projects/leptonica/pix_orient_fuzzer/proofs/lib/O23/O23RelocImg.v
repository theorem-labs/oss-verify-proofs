(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec StreamSim.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocImg CanonImg RelocSpan CanonSpans.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23RelocImg () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common5Reloc8RelocImg;cells_checkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8CanonImg;canon_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib6Common9StreamSim7wseg_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib6Common5Reloc9RelocSpan8hull_okbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9RelocSpan;spans_checkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc:CanonSpans;canon_spansC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9RelocSpan<orders_checkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc:CanonSpans;canon_orderC1?~~~~~~~~~~~~~~~".
Local Open Scope Z_scope.

Lemma o23_cells_ok : @cells_check o23_reloc canon_cells = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocImg ()) [] "p;2p;3g0000j22Tg000Jj21Tg001Pj30Tg001jR0g002JR1'2g002jg003e'1=001do"). Qed.

Definition o23_img : RelocImg o23_reloc := {| rl_cells_ok := o23_cells_ok |}.

Lemma o23_data_wseg : wseg_ok (@rl_segs o23_reloc) (Z_to_bv 64 0x113000) (Z.to_nat (@rl_img_hi o23_reloc - 0x113000)) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocImg ()) [] "p;2p;1p;3g0000j2<Tg004kj1;Tg005jj11Tg006Oj1:Tg006mj12Tg007Rj17Tg0080j24Tg008Vj15Tg009Wj26Tg00:4j13Tg00:Tj38Tg001Pj39Tf0#1#1p=0g001jR0g002JR1'<g002jR2#;g00;Q#1#0R3#1#0#:%23#0#2#2#0#0#0#0#0#0#7R3'4%52/63#338=901do"). Qed.

Lemma o23_data_ok : (0 <=? 0x113000) && (0x113000 <=? @rl_img_hi o23_reloc) && (@rl_img_hi o23_reloc <=? 2^32) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocImg ()) [] "p;2g0000j20Tg001jg002J'0o"). Qed.

Definition o23_data : RelocData o23_reloc := {| rl_data_lo := 0x113000; rl_data_ok := o23_data_ok; rl_data_wseg := o23_data_wseg |}.

Lemma o23_hull_ok : @hull_okb o23_reloc o23_data = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocImg ()) [] "p;2p;3g0000j22Tg00<6j21Tg001Pj30Tg001jR0g002JR1'2g002jg00=:'1=001do"). Qed.
Lemma o23_spans_ok : @spans_check o23_reloc o23_data canon_spans = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocImg ()) [] "p;2p;3g0000j22Tg00>7j31Tg001Pj30Tg001jR0g002JR1'2g002jg00=:g00?>31=001do"). Qed.
Lemma o23_orders_ok : @orders_check o23_reloc canon_spans canon_order = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocImg ()) [] "p;2p;3g0000j22Tg00@Fj31Tg001Pj30Tg001jR0g002JR1'2g002jg00?>g00AN31=001do"). Qed.
Definition o23_spans : RelocSpans o23_reloc o23_data := {| rl_hull_ok := o23_hull_ok; rl_spans_ok := o23_spans_ok; rl_orders_ok := o23_orders_ok |}.
