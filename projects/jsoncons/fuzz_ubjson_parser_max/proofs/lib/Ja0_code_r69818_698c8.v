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
Definition W_83150 : bv 32 := 0x02850583.
Lemma F_83150 : CTabKA.F 0x83150 W_83150.
Proof. vm_refl. Qed.
Lemma D_83150 : CTabKA.D W_83150 (Load SZ1 true 11 10 40).
Proof. vm_refl. Qed.
Definition W_83154 : bv 32 := 0x0230000f.
Lemma F_83154 : CTabKA.F 0x83154 W_83154.
Proof. vm_refl. Qed.
Lemma D_83154 : CTabKA.D W_83154 (Fence 0 2 3 0 0).
Proof. vm_refl. Qed.
Definition W_83158 : bv 32 := 0x02058c63.
Lemma F_83158 : CTabKA.F 0x83158 W_83158.
Proof. vm_refl. Qed.
Lemma D_83158 : CTabKA.D W_83158 (Branch BC_EQ 11 0 56).
Proof. vm_refl. Qed.
Definition W_83190 : bv 32 := 0x00853583.
Lemma F_83190 : CTabKA.F 0x83190 W_83190.
Proof. vm_refl. Qed.
Lemma D_83190 : CTabKA.D W_83190 (Load SZ8 true 11 10 8).
Proof. vm_refl. Qed.
Definition W_83194 : bv 32 := 0x01053503.
Lemma F_83194 : CTabKA.F 0x83194 W_83194.
Proof. vm_refl. Qed.
Lemma D_83194 : CTabKA.D W_83194 (Load SZ8 true 10 10 16).
Proof. vm_refl. Qed.
Definition W_83198 : bv 32 := 0x00b53533.
Lemma F_83198 : CTabKA.F 0x83198 W_83198.
Proof. vm_refl. Qed.
Lemma D_83198 : CTabKA.D W_83198 (Op ALU_SLTU 10 10 11).
Proof. vm_refl. Qed.
Definition W_8319c : bv 32 := 0x40a00533.
Lemma F_8319c : CTabKA.F 0x8319c W_8319c.
Proof. vm_refl. Qed.
Lemma D_8319c : CTabKA.D W_8319c (Op ALU_SUB 10 0 10).
Proof. vm_refl. Qed.
Definition W_831a0 : bv 32 := 0x00b57533.
Lemma F_831a0 : CTabKA.F 0x831a0 W_831a0.
Proof. vm_refl. Qed.
Lemma D_831a0 : CTabKA.D W_831a0 (Op ALU_AND 10 10 11).
Proof. vm_refl. Qed.
Definition W_831a4 : bv 32 := 0x00008067.
Lemma F_831a4 : CTabKA.F 0x831a4 W_831a4.
Proof. vm_refl. Qed.
Lemma D_831a4 : CTabKA.D W_831a4 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_831a8 : bv 32 := 0x02850583.
Lemma F_831a8 : CTabKA.F 0x831a8 W_831a8.
Proof. vm_refl. Qed.
Lemma D_831a8 : CTabKA.D W_831a8 (Load SZ1 true 11 10 40).
Proof. vm_refl. Qed.
Definition W_831ac : bv 32 := 0x0230000f.
Lemma F_831ac : CTabKA.F 0x831ac W_831ac.
Proof. vm_refl. Qed.
Lemma D_831ac : CTabKA.D W_831ac (Fence 0 2 3 0 0).
Proof. vm_refl. Qed.
Definition W_831b0 : bv 32 := 0x02058c63.
Lemma F_831b0 : CTabKA.F 0x831b0 W_831b0.
Proof. vm_refl. Qed.
Lemma D_831b0 : CTabKA.D W_831b0 (Branch BC_EQ 11 0 56).
Proof. vm_refl. Qed.
Definition W_831e8 : bv 32 := 0x00853583.
Lemma F_831e8 : CTabKA.F 0x831e8 W_831e8.
Proof. vm_refl. Qed.
Lemma D_831e8 : CTabKA.D W_831e8 (Load SZ8 true 11 10 8).
Proof. vm_refl. Qed.
Definition W_831ec : bv 32 := 0x01053503.
Lemma F_831ec : CTabKA.F 0x831ec W_831ec.
Proof. vm_refl. Qed.
Lemma D_831ec : CTabKA.D W_831ec (Load SZ8 true 10 10 16).
Proof. vm_refl. Qed.
Definition W_831f0 : bv 32 := 0x00b535b3.
Lemma F_831f0 : CTabKA.F 0x831f0 W_831f0.
Proof. vm_refl. Qed.
Lemma D_831f0 : CTabKA.D W_831f0 (Op ALU_SLTU 11 10 11).
Proof. vm_refl. Qed.
Definition W_831f4 : bv 32 := 0x40b005b3.
Lemma F_831f4 : CTabKA.F 0x831f4 W_831f4.
Proof. vm_refl. Qed.
Lemma D_831f4 : CTabKA.D W_831f4 (Op ALU_SUB 11 0 11).
Proof. vm_refl. Qed.
Definition W_831f8 : bv 32 := 0x00a5f533.
Lemma F_831f8 : CTabKA.F 0x831f8 W_831f8.
Proof. vm_refl. Qed.
Lemma D_831f8 : CTabKA.D W_831f8 (Op ALU_AND 10 11 10).
Proof. vm_refl. Qed.
Definition W_831fc : bv 32 := 0x00008067.
Lemma F_831fc : CTabKA.F 0x831fc W_831fc.
Proof. vm_refl. Qed.
Lemma D_831fc : CTabKA.D W_831fc (Jalr 0 1 0).
Proof. vm_refl. Qed.
