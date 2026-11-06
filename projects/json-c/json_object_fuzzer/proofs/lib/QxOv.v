(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_ceb90 : bv 32 := 0x00050593.
Lemma F_ceb90 : fetch_word asegs (0xceb44 : word) = Some W_ceb90.
Proof. vm_refl. Qed.
Lemma D_ceb90 : decode_any W_ceb90 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ceb94 : bv 32 := 0x05e00893.
Lemma F_ceb94 : fetch_word asegs (0xceb48 : word) = Some W_ceb94.
Proof. vm_refl. Qed.
Lemma D_ceb94 : decode_any W_ceb94 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_ceb98 : bv 32 := 0x00000073.
Lemma F_ceb98 : fetch_word asegs (0xceb4c : word) = Some W_ceb98.
Proof. vm_refl. Qed.

Lemma E_ceb98 : is_ecall W_ceb98 = true.
Proof. reflexivity. Qed.

Definition W_cee2c : bv 32 := 0x00040513.
Lemma F_cee2c : fetch_word asegs (0xcede0 : word) = Some W_cee2c.
Proof. vm_refl. Qed.
Lemma D_cee2c : decode_any W_cee2c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cee30 : bv 32 := 0xd61ff0ef.
Lemma F_cee30 : fetch_word asegs (0xcede4 : word) = Some W_cee30.
Proof. vm_refl. Qed.
Lemma D_cee30 : decode_any W_cee30 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf118 : bv 32 := 0xfffff5b7.
Lemma F_cf118 : fetch_word asegs (0xcf0cc : word) = Some W_cf118.
Proof. vm_refl. Qed.
Lemma D_cf118 : decode_any W_cf118 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf11c : bv 32 := 0x0015859b.
Lemma F_cf11c : fetch_word asegs (0xcf0d0 : word) = Some W_cf11c.
Proof. vm_refl. Qed.
Lemma D_cf11c : decode_any W_cf11c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf120 : bv 32 := 0x02b56663.
Lemma F_cf120 : fetch_word asegs (0xcf0d4 : word) = Some W_cf120.
Proof. vm_refl. Qed.
Lemma D_cf120 : decode_any W_cf120 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf14c : bv 32 := 0x00008067.
Lemma F_cf14c : fetch_word asegs (0xcf100 : word) = Some W_cf14c.
Proof. vm_refl. Qed.
Lemma D_cf14c : decode_any W_cf14c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
