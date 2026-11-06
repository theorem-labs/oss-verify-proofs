(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require CTabKB.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_83420 : bv 32 := 0x02850583.
Lemma F_83420 : CTabKB.F 0x83420 W_83420.
Proof. vm_refl. Qed.
Lemma D_83420 : CTabKB.D W_83420 (Load SZ1 true 11 10 40).
Proof. vm_refl. Qed.
Definition W_83424 : bv 32 := 0x0230000f.
Lemma F_83424 : CTabKB.F 0x83424 W_83424.
Proof. vm_refl. Qed.
Lemma D_83424 : CTabKB.D W_83424 (Fence 0 2 3 0 0).
Proof. vm_refl. Qed.
Definition W_83428 : bv 32 := 0x02058c63.
Lemma F_83428 : CTabKB.F 0x83428 W_83428.
Proof. vm_refl. Qed.
Lemma D_83428 : CTabKB.D W_83428 (Branch BC_EQ 11 0 56).
Proof. vm_refl. Qed.
Definition W_83460 : bv 32 := 0x00853583.
Lemma F_83460 : CTabKB.F 0x83460 W_83460.
Proof. vm_refl. Qed.
Lemma D_83460 : CTabKB.D W_83460 (Load SZ8 true 11 10 8).
Proof. vm_refl. Qed.
Definition W_83464 : bv 32 := 0x01053503.
Lemma F_83464 : CTabKB.F 0x83464 W_83464.
Proof. vm_refl. Qed.
Lemma D_83464 : CTabKB.D W_83464 (Load SZ8 true 10 10 16).
Proof. vm_refl. Qed.
Definition W_83468 : bv 32 := 0x00b53533.
Lemma F_83468 : CTabKB.F 0x83468 W_83468.
Proof. vm_refl. Qed.
Lemma D_83468 : CTabKB.D W_83468 (Op ALU_SLTU 10 10 11).
Proof. vm_refl. Qed.
Definition W_8346c : bv 32 := 0x40a00533.
Lemma F_8346c : CTabKB.F 0x8346c W_8346c.
Proof. vm_refl. Qed.
Lemma D_8346c : CTabKB.D W_8346c (Op ALU_SUB 10 0 10).
Proof. vm_refl. Qed.
Definition W_83470 : bv 32 := 0x00b57533.
Lemma F_83470 : CTabKB.F 0x83470 W_83470.
Proof. vm_refl. Qed.
Lemma D_83470 : CTabKB.D W_83470 (Op ALU_AND 10 10 11).
Proof. vm_refl. Qed.
Definition W_83474 : bv 32 := 0x00008067.
Lemma F_83474 : CTabKB.F 0x83474 W_83474.
Proof. vm_refl. Qed.
Lemma D_83474 : CTabKB.D W_83474 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_83478 : bv 32 := 0x02850583.
Lemma F_83478 : CTabKB.F 0x83478 W_83478.
Proof. vm_refl. Qed.
Lemma D_83478 : CTabKB.D W_83478 (Load SZ1 true 11 10 40).
Proof. vm_refl. Qed.
Definition W_8347c : bv 32 := 0x0230000f.
Lemma F_8347c : CTabKB.F 0x8347c W_8347c.
Proof. vm_refl. Qed.
Lemma D_8347c : CTabKB.D W_8347c (Fence 0 2 3 0 0).
Proof. vm_refl. Qed.
Definition W_83480 : bv 32 := 0x02058c63.
Lemma F_83480 : CTabKB.F 0x83480 W_83480.
Proof. vm_refl. Qed.
Lemma D_83480 : CTabKB.D W_83480 (Branch BC_EQ 11 0 56).
Proof. vm_refl. Qed.
Definition W_834b8 : bv 32 := 0x00853583.
Lemma F_834b8 : CTabKB.F 0x834b8 W_834b8.
Proof. vm_refl. Qed.
Lemma D_834b8 : CTabKB.D W_834b8 (Load SZ8 true 11 10 8).
Proof. vm_refl. Qed.
Definition W_834bc : bv 32 := 0x01053503.
Lemma F_834bc : CTabKB.F 0x834bc W_834bc.
Proof. vm_refl. Qed.
Lemma D_834bc : CTabKB.D W_834bc (Load SZ8 true 10 10 16).
Proof. vm_refl. Qed.
Definition W_834c0 : bv 32 := 0x00b535b3.
Lemma F_834c0 : CTabKB.F 0x834c0 W_834c0.
Proof. vm_refl. Qed.
Lemma D_834c0 : CTabKB.D W_834c0 (Op ALU_SLTU 11 10 11).
Proof. vm_refl. Qed.
Definition W_834c4 : bv 32 := 0x40b005b3.
Lemma F_834c4 : CTabKB.F 0x834c4 W_834c4.
Proof. vm_refl. Qed.
Lemma D_834c4 : CTabKB.D W_834c4 (Op ALU_SUB 11 0 11).
Proof. vm_refl. Qed.
Definition W_834c8 : bv 32 := 0x00a5f533.
Lemma F_834c8 : CTabKB.F 0x834c8 W_834c8.
Proof. vm_refl. Qed.
Lemma D_834c8 : CTabKB.D W_834c8 (Op ALU_AND 10 11 10).
Proof. vm_refl. Qed.
Definition W_834cc : bv 32 := 0x00008067.
Lemma F_834cc : CTabKB.F 0x834cc W_834cc.
Proof. vm_refl. Qed.
Lemma D_834cc : CTabKB.D W_834cc (Jalr 0 1 0).
Proof. vm_refl. Qed.
