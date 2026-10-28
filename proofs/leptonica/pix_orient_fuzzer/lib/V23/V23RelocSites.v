(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites CanonSites.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc.

Lemma v23_sites_ok : @sites_check v23_reloc canon_sites = true.
Proof.
vm_cast_no_check (@eq_refl bool true). Qed.

Definition v23_sites : RelocSites v23_reloc := {| rl_sites_ok := v23_sites_ok |}.
