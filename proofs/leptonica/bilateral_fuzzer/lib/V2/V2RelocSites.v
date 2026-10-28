(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites CanonSites.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2RelocSites () := "K47Corelib4Init5Logic2eq01C6ARocqVerifyHarness?AgentSubmission6Common5Reloc:RelocSites;sites_checkI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC6ARocqVerifyHarness?AgentSubmission6Common5Reloc:CanonSites;canon_sites".

Lemma v2_sites_ok : @sites_check v2_reloc canon_sites = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2RelocSites ()) [] "p;2p;3g0000j22Tg000Jj21Tg001Rj30Tg001lR0g002LR1'2g002lg003d'1=001do"). Qed.

Definition v2_sites : RelocSites v2_reloc := {| rl_sites_ok := v2_sites_ok |}.
