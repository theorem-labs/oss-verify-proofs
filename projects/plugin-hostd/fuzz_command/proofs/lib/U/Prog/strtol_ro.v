From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import CType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strtol_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import __intscan_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import __shlim_c __intscan_c strtol_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strtol_ro_c strtol.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import RoAdapt.
Import ListNotations.
Open Scope Z_scope.

Lemma strtol_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem strtol_ro_of : strtol_contract -> strtol_ro_contract.
Proof. ro_adapt rsegs strtol_wx. Qed.

Theorem strtol_ro_holds : __shlim_contract -> __intscan_contract -> strtol_ro_contract.
Proof. intros H0 H1. exact (strtol_ro_of (strtol_holds H0 H1)). Qed.
