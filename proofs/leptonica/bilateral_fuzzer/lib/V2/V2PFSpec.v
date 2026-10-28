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
Definition ls_ok (nS : nat) (fmts : list Z) (L : SSP.ls_addrs) : bool := @PFSpec.ls_ok v2_reloc nS fmts L.
Definition ls_ok1 (L : SSP.ls_addrs) : bool := ls_ok 1 (SSP.ls_fmts1 L) L.
Definition ls_ok2 (L : SSP.ls_addrs) : bool := ls_ok 2 (SSP.ls_fmts2 L) L.

Section Contracts.
Context {fx : FPState}.
#[local] Existing Instance v2_reloc.
#[local] Existing Instance v2_code.
#[local] Existing Instance v2_sites.
#[local] Existing Instance v2_data.
#[local] Existing Instance v2_img.
#[local] Existing Instance v2_rw.
#[local] Existing Instance v2_pf.

(* [comment removed for export] *)
Theorem lept_stderr_s1_contract : forall L, ls_ok1 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L).
Proof.
ltac2:(KReplay.run1 (kr_t_V2PFSpec ()) ["Contracts"] "p;8g0000j80Tf0g001?g0027g0032g003og004ig005bg006[G0p=1p,2fx#1o"). Qed.

(* [comment removed for export] *)
Theorem lept_stderr_s2_contract : forall L, ls_ok2 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L).
Proof.
ltac2:(KReplay.run1 (kr_t_V2PFSpec ()) ["Contracts"] "p;8g007Tj80Tf0g001?g0027g0032g003og004ig005bg006[G0p=1p,2fx#1o"). Qed.
End Contracts.
