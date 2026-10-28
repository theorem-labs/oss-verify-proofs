(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require PFSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.VL Require Import LeptStderr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc.

Lemma v23_lenv_ok1 : @PFSpec.ls_ok1 v23_reloc (@LG v23_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v23_lenv_ok2 : @PFSpec.ls_ok2 v23_reloc (@LG v23_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v23_lenv_vl : RelocLeptEnvVL v23_reloc := {| rl_lenv_ok1 := v23_lenv_ok1; rl_lenv_ok2 := v23_lenv_ok2 |}.
