(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites CanonSites.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2RelocSites () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common5Reloc:RelocSites;sites_checkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc:CanonSites;canon_sitesC1?~~~~~~~~~~~~~~~".

Lemma o2_sites_ok : @sites_check o2_reloc canon_sites = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2RelocSites ()) [] "p;2p;3g0000j22Tg000Jj21Tg001Rj30Tg001lR0g002LR1'2g002lg003d'1=001do"). Qed.

Definition o2_sites : RelocSites o2_reloc := {| rl_sites_ok := o2_sites_ok |}.
