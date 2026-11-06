From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strrchr_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memrchr_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strlen_c memrchr_c strrchr_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strrchr_ro_c strrchr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import RoAdapt.
Import ListNotations.
Open Scope Z_scope.

Lemma strrchr_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem strrchr_ro_of : strrchr_contract -> strrchr_ro_contract.
Proof. ro_adapt rsegs strrchr_wx. Qed.

Theorem strrchr_ro_holds : strlen_contract -> memrchr_contract -> strrchr_ro_contract.
Proof. intros H0 H1. exact (strrchr_ro_of (strrchr_holds H0 H1)). Qed.
