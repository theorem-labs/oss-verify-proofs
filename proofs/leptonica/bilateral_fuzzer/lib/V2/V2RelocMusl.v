(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg RelocSpan CanonSpans.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocImg.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2RelocMusl () := "K47Corelib4Init5Logic2eq01C6ARocqVerifyHarness?AgentSubmission6Common4Musl7RelocRW?dwin_bounds_chkI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg7v2_dataC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc9rl_img_loC6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc7rl_segsC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica5PFLib7segs_loI47Corelib7Numbers7BinNums1Z00C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc9rl_img_hiC6ARocqVerifyHarness?AgentSubmission6Common9Leptonica5PFLib7segs_hiC6ARocqVerifyHarness?AgentSubmission6Common4Musl7RelocPF=pf_bounds_chkK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission6Common4Musl7RelocPF<pf_prefix_okK47Corelib7Numbers7BinNums8positive03".
Local Open Scope Z_scope.

Lemma v2_dwin_bounds : @dwin_bounds_chk v2_reloc v2_data = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocMusl ()) [] "p;2p;3g0000j22Tg000Jj21Tg001Rj30Tg001lR0g002LR1'2g002lg003d'1=001do"). Qed.
Definition v2_rw : RelocRW v2_reloc v2_data := {| rl_dwin_bounds := v2_dwin_bounds; rl_rw_hull := v2_hull_ok; rl_rw_spans := v2_spans_ok; rl_rw_orders := v2_orders_ok |}.

Lemma v2_segs_lo : segs_lo (@rl_segs v2_reloc) = @rl_img_lo v2_reloc.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocMusl ()) [] "p;1p;2p;3g004^j14Tg0000j23Tg005_j10Tg006^j11Tg001Rj32Tg007aR0g002lR1#4R2'3%01#1=202do"). Qed.
Lemma v2_segs_hi : segs_hi (@rl_segs v2_reloc) = @rl_img_hi v2_reloc.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocMusl ()) [] "p;1p;2p;3g008?j14Tg0000j23Tg005_j10Tg009@j11Tg001Rj32Tg007aR0g002lR1#4R2'3%01#1=202do"). Qed.
Lemma v2_pf_bounds : @pf_bounds_chk v2_reloc = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocMusl ()) [] "p;2p;1p;3g0000j22Tg00:Cj11Tg001Rj30Tg001lR0g002LR1'2g002l#1=001do"). Qed.
Lemma v2_pf_prefix : pf_prefix_ok (@rl_segs v2_reloc) (0x102e7 + @rl_delta v2_reloc B_S_102e7) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocMusl ()) [] "p;2p;1p;3g0000j29Tg005_j18Tg00;Ij10Tg00;nj12Tg00<Sj17Tg00=1j24Tg00>1j23Tg00>Nj25Tg001Rj36Tf0#2#2p=1g001lR0g002LR1'9g002lR2#8g00?SR3#1#1#1#0#2#0#0#0#1#0#0#0#7%03#0#0#0#2#0#2#1#1,42'3'5=601do"). Qed.
Definition v2_pf : RelocPF v2_reloc :=
  {| rl_segs_lo_val := v2_segs_lo; rl_segs_hi_val := v2_segs_hi; rl_pf_bounds := v2_pf_bounds; rl_pf_prefix := v2_pf_prefix |}.
