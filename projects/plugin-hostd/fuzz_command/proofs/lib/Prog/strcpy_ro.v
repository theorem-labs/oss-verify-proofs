From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strcpy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import stpcpy_c strcpy_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strcpy_ro_c strcpy.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import RoAdapt.
Import ListNotations.
Open Scope bv_scope.

Lemma strcpy_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem strcpy_ro_of : strcpy_contract -> strcpy_ro_contract.
Proof. ro_adapt rsegs strcpy_wx. Qed.

Theorem strcpy_ro_holds : stpcpy_contract -> strcpy_ro_contract.
Proof. intros H0. exact (strcpy_ro_of (strcpy_holds H0)). Qed.
