(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode RelocSites RelocImg.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require RelocRW RelocPF PFSpec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc O23RelocCode O23RelocSites O23RelocImg O23RelocMusl O23PFBase.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23PFSpec () := "C69OSSVerify5KrLib6Common4Musl6PFSpecGlept_stderr_s1_contractC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23RelocCode8o23_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23=O23RelocSites9o23_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg7o23_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23RelocMusl6o23_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23RelocMusl6o23_pfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl6PFSpecGlept_stderr_s2_contractC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ls_ok (nS : nat) (fmts : list Z) (L : SSP.ls_addrs) : bool := @PFSpec.ls_ok o23_reloc nS fmts L.
Definition ls_ok1 (L : SSP.ls_addrs) : bool := ls_ok 1 (SSP.ls_fmts1 L) L.
Definition ls_ok2 (L : SSP.ls_addrs) : bool := ls_ok 2 (SSP.ls_fmts2 L) L.

Section Contracts.
Context {fx : FPState}.
#[local] Existing Instance o23_reloc.
#[local] Existing Instance o23_code.
#[local] Existing Instance o23_sites.
#[local] Existing Instance o23_data.
#[local] Existing Instance o23_img.
#[local] Existing Instance o23_rw.
#[local] Existing Instance o23_pf.

(* [comment removed for export] *)
Theorem lept_stderr_s1_contract : forall L, ls_ok1 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L).
Proof.
ltac2:(KReplay.run1 (kr_t_O23PFSpec ()) ["Contracts"] "p;8g0000j80Tf0g001?g002:g0038g0048g0055g0061g006mG0p=1p,2fx#1o"). Qed.

(* [comment removed for export] *)
Theorem lept_stderr_s2_contract : forall L, ls_ok2 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L).
Proof.
ltac2:(KReplay.run1 (kr_t_O23PFSpec ()) ["Contracts"] "p;8g007ij80Tf0g001?g002:g0038g0048g0055g0061g006mG0p=1p,2fx#1o"). Qed.
End Contracts.
