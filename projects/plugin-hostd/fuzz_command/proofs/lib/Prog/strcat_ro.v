From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strcat_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strlen_c strcpy_c strcat_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strcat_ro_c strcat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import RoAdapt.
Import ListNotations.
Open Scope bv_scope.

Lemma strcat_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem strcat_ro_of : strcat_contract -> strcat_ro_contract.
Proof. ro_adapt rsegs strcat_wx. Qed.

Theorem strcat_ro_holds : strlen_contract -> strcpy_contract -> strcat_ro_contract.
Proof. intros H0 H1. exact (strcat_ro_of (strcat_holds H0 H1)). Qed.
