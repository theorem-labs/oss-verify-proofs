(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import RelocStart.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocImg.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2RelocStart () := "K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC6ARocqVerifyHarness?AgentSubmission6Common5Reloc8RelocImg:rl_data_loC6ARocqVerifyHarness?AgentSubmission6Common4Musl:RelocStart8start_okI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg7v2_data".
Local Open Scope Z_scope.

Lemma v2_start_ok : start_ok (@rl_delta v2_reloc 8%positive) (@rl_data_lo v2_reloc v2_data) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocStart ()) [] "p;2p;1p;3g0000j25Tg000Jj10Tg000oj22Tg001oj21Tg0034j24Tg0048j33Tg004RR0g0052R1'5g005RR2g006J#0#0#0'2g006o,12'4=301do"). Qed.
Definition v2_start : RelocStart v2_reloc v2_data := {| rl_start_ok := v2_start_ok |}.
