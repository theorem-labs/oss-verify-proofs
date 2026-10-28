(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require PFSpec.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.VL Require Import LeptStderr.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc.

Lemma v2_lenv_ok1 : @PFSpec.ls_ok1 v2_reloc (@LG v2_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v2_lenv_ok2 : @PFSpec.ls_ok2 v2_reloc (@LG v2_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v2_lenv_vl : RelocLeptEnvVL v2_reloc := {| rl_lenv_ok1 := v2_lenv_ok1; rl_lenv_ok2 := v2_lenv_ok2 |}.
