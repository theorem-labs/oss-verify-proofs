From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import CType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import __intscan_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import __intscan_c __shlim_c __errno_location_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import __intscan_ro_c __intscan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import RoAdapt.
Import ListNotations.
Open Scope Z_scope.

Lemma __intscan_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem __intscan_ro_of : __intscan_contract -> __intscan_ro_contract.
Proof. ro_adapt rsegs __intscan_wx. Qed.

Theorem __intscan_ro_holds : __errno_location_contract -> __shlim_contract -> __intscan_ro_contract.
Proof. intros H0 H1. exact (__intscan_ro_of (__intscan_holds H0 H1)). Qed.
