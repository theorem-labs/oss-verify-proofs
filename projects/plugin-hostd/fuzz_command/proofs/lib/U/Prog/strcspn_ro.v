From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import memset_c strchrnul_c strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strcspn_ro_c strcspn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import RoAdapt.
Import ListNotations.
Open Scope bv_scope.

Lemma strcspn_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem strcspn_ro_of : strcspn_contract -> strcspn_ro_contract.
Proof. ro_adapt rsegs strcspn_wx. Qed.

Theorem strcspn_ro_holds : memset_contract -> strchrnul_contract -> strcspn_ro_contract.
Proof. intros H0 H1. exact (strcspn_ro_of (strcspn_holds H0 H1)). Qed.
