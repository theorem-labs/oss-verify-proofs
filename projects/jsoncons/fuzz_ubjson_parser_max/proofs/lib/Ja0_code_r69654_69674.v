(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require CTabKA.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_82f8c : bv 32 := 0xff010113.
Lemma F_82f8c : CTabKA.F 0x82f8c W_82f8c.
Proof. vm_refl. Qed.
Lemma D_82f8c : CTabKA.D W_82f8c (OpImm ALU_ADD 2 2 4080).
Proof. vm_refl. Qed.
Definition W_82f90 : bv 32 := 0x00113423.
Lemma F_82f90 : CTabKA.F 0x82f90 W_82f90.
Proof. vm_refl. Qed.
Lemma D_82f90 : CTabKA.D W_82f90 (Store SZ8 2 1 8).
Proof. vm_refl. Qed.
Definition W_82f94 : bv 32 := 0xe78f80ef.
Lemma F_82f94 : CTabKA.F 0x82f94 W_82f94.
Proof. vm_refl. Qed.
Lemma D_82f94 : CTabKA.D W_82f94 (Jal 1 2066040).
Proof. vm_refl. Qed.
Definition W_82f98 : bv 32 := 0x00050463.
Lemma F_82f98 : CTabKA.F 0x82f98 W_82f98.
Proof. vm_refl. Qed.
Lemma D_82f98 : CTabKA.D W_82f98 (Branch BC_EQ 10 0 8).
Proof. vm_refl. Qed.
Definition W_82f9c : bv 32 := 0x09853503.
Lemma F_82f9c : CTabKA.F 0x82f9c W_82f9c.
Proof. vm_refl. Qed.
Lemma D_82f9c : CTabKA.D W_82f9c (Load SZ8 true 10 10 152).
Proof. vm_refl. Qed.
Definition W_82fa0 : bv 32 := 0x00813083.
Lemma F_82fa0 : CTabKA.F 0x82fa0 W_82fa0.
Proof. vm_refl. Qed.
Lemma D_82fa0 : CTabKA.D W_82fa0 (Load SZ8 true 1 2 8).
Proof. vm_refl. Qed.
Definition W_82fa4 : bv 32 := 0x01010113.
Lemma F_82fa4 : CTabKA.F 0x82fa4 W_82fa4.
Proof. vm_refl. Qed.
Lemma D_82fa4 : CTabKA.D W_82fa4 (OpImm ALU_ADD 2 2 16).
Proof. vm_refl. Qed.
Definition W_82fa8 : bv 32 := 0x00008067.
Lemma F_82fa8 : CTabKA.F 0x82fa8 W_82fa8.
Proof. vm_refl. Qed.
Lemma D_82fa8 : CTabKA.D W_82fa8 (Jalr 0 1 0).
Proof. vm_refl. Qed.
