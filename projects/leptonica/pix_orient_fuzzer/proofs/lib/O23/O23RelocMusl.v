(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg RelocSpan CanonSpans.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc O23RelocImg.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23RelocMusl () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common4Musl7RelocRW?dwin_bounds_chkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5PFLib7segs_loC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5PFLib7segs_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl7RelocPF=pf_bounds_chkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common4Musl7RelocPF<pf_prefix_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03".
Local Open Scope Z_scope.

Lemma o23_dwin_bounds : @dwin_bounds_chk o23_reloc o23_data = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocMusl ()) [] "p;2p;3g0000j22Tg000Jj21Tg001Rj30Tg001lR0g002LR1'2g002lg003g'1=001do"). Qed.
Definition o23_rw : RelocRW o23_reloc o23_data := {| rl_dwin_bounds := o23_dwin_bounds; rl_rw_hull := o23_hull_ok; rl_rw_spans := o23_spans_ok; rl_rw_orders := o23_orders_ok |}.

Lemma o23_segs_lo : segs_lo (@rl_segs o23_reloc) = @rl_img_lo o23_reloc.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocMusl ()) [] "p;1p;2p;3g004dj14Tg0000j23Tg005ej10Tg006dj11Tg001Rj32Tg007gR0g002lR1#4R2'3%01#1=202do"). Qed.
Lemma o23_segs_hi : segs_hi (@rl_segs o23_reloc) = @rl_img_hi o23_reloc.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocMusl ()) [] "p;1p;2p;3g008Ej14Tg0000j23Tg005ej10Tg009Fj11Tg001Rj32Tg007gR0g002lR1#4R2'3%01#1=202do"). Qed.
Lemma o23_pf_bounds : @pf_bounds_chk o23_reloc = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocMusl ()) [] "p;2p;1p;3g0000j22Tg00:Ij11Tg001Rj30Tg001lR0g002LR1'2g002l#1=001do"). Qed.
Lemma o23_pf_prefix : pf_prefix_ok (@rl_segs o23_reloc) (0x102e7 + @rl_delta o23_reloc B_S_102e7) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23RelocMusl ()) [] "p;2p;1p;3g0000j29Tg005ej18Tg00;Oj10Tg00<4j12Tg00<Yj17Tg00=7j24Tg00>7j23Tg00>Tj25Tg001Rj36Tf0#2#2p=1g001lR0g002LR1'9g002lR2#8g00?YR3#1#1#1#0#2#0#0#0#1#0#0#0#7%03#0#0#0#2#0#2#1#1,42'3'5=601do"). Qed.
Definition o23_pf : RelocPF o23_reloc :=
  {| rl_segs_lo_val := o23_segs_lo; rl_segs_hi_val := o23_segs_hi; rl_pf_bounds := o23_pf_bounds; rl_pf_prefix := o23_pf_prefix |}.
