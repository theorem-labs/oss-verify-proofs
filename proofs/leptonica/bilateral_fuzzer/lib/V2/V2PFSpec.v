(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites RelocImg.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require RelocRW RelocPF PFSpec.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocMusl V2PFBase.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2PFSpec () := "C6ARocqVerifyHarness?AgentSubmission6Common4Musl6PFSpecGlept_stderr_s1_contractC5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocCode7v2_codeC5ARocqVerifyHarness?AgentSubmission2V2<V2RelocSites8v2_sitesC5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg7v2_dataC5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg6v2_imgC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocMusl5v2_rwC5ARocqVerifyHarness?AgentSubmission2V2;V2RelocMusl5v2_pfC6ARocqVerifyHarness?AgentSubmission6Common4Musl6PFSpecGlept_stderr_s2_contract".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ls_ok (nS : nat) (fmts : list Z) (L : SSP.ls_addrs) : bool :=
  PFSpec.ls_ok (RL := v2_reloc) nS fmts L.
Definition ls_ok1 (L : SSP.ls_addrs) : bool := ls_ok 1 (SSP.ls_fmts1 L) L.
Definition ls_ok2 (L : SSP.ls_addrs) : bool := ls_ok 2 (SSP.ls_fmts2 L) L.

Section Contracts.
#[local] Existing Instances v2_reloc v2_data.
#[local] Existing Instances v2_code v2_sites v2_img v2_rw v2_pf.
Context {fx : FPState}.

Theorem lept_stderr_s1_contract : forall L, ls_ok1 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L).
Proof.
  intros addrs s1_fmts_checked.
  refine (PFSpec.lept_stderr_s1_contract addrs _).
  exact s1_fmts_checked.
Qed.

Theorem lept_stderr_s2_contract : forall L, ls_ok2 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L).
Proof.
  intros addrs s2_fmt_checked.
  refine (PFSpec.lept_stderr_s2_contract addrs _).
  exact s2_fmt_checked.
Qed.
End Contracts.
