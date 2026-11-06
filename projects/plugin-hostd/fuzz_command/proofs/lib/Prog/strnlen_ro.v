From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strnlen_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import memchr_c strnlen_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strnlen_ro_c strnlen.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import RoAdapt.
Import ListNotations.
Open Scope Z_scope.

Lemma strnlen_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem strnlen_ro_of : strnlen_contract -> strnlen_ro_contract.
Proof. ro_adapt rsegs strnlen_wx. Qed.

Theorem strnlen_ro_holds : memchr_contract -> strnlen_ro_contract.
Proof. intros H0. exact (strnlen_ro_of (strnlen_holds H0)). Qed.
