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
Definition W_8325c : bv 32 := 0xff010113.
Lemma F_8325c : CTabKB.F 0x8325c W_8325c.
Proof. vm_refl. Qed.
Lemma D_8325c : CTabKB.D W_8325c (OpImm ALU_ADD 2 2 4080).
Proof. vm_refl. Qed.
Definition W_83260 : bv 32 := 0x00113423.
Lemma F_83260 : CTabKB.F 0x83260 W_83260.
Proof. vm_refl. Qed.
Lemma D_83260 : CTabKB.D W_83260 (Store SZ8 2 1 8).
Proof. vm_refl. Qed.
Definition W_83264 : bv 32 := 0xe78f80ef.
Lemma F_83264 : CTabKB.F 0x83264 W_83264.
Proof. vm_refl. Qed.
Lemma D_83264 : CTabKB.D W_83264 (Jal 1 2066040).
Proof. vm_refl. Qed.
Definition W_83268 : bv 32 := 0x00050463.
Lemma F_83268 : CTabKB.F 0x83268 W_83268.
Proof. vm_refl. Qed.
Lemma D_83268 : CTabKB.D W_83268 (Branch BC_EQ 10 0 8).
Proof. vm_refl. Qed.
Definition W_8326c : bv 32 := 0x09853503.
Lemma F_8326c : CTabKB.F 0x8326c W_8326c.
Proof. vm_refl. Qed.
Lemma D_8326c : CTabKB.D W_8326c (Load SZ8 true 10 10 152).
Proof. vm_refl. Qed.
Definition W_83270 : bv 32 := 0x00813083.
Lemma F_83270 : CTabKB.F 0x83270 W_83270.
Proof. vm_refl. Qed.
Lemma D_83270 : CTabKB.D W_83270 (Load SZ8 true 1 2 8).
Proof. vm_refl. Qed.
Definition W_83274 : bv 32 := 0x01010113.
Lemma F_83274 : CTabKB.F 0x83274 W_83274.
Proof. vm_refl. Qed.
Lemma D_83274 : CTabKB.D W_83274 (OpImm ALU_ADD 2 2 16).
Proof. vm_refl. Qed.
Definition W_83278 : bv 32 := 0x00008067.
Lemma F_83278 : CTabKB.F 0x83278 W_83278.
Proof. vm_refl. Qed.
Lemma D_83278 : CTabKB.D W_83278 (Jalr 0 1 0).
Proof. vm_refl. Qed.
