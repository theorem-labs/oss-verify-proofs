(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_cc4a4 : bv 32 := 0x00050593.
Lemma F_cc4a4 : fetch_word asegs (0xcc480 : word) = Some W_cc4a4.
Proof. vm_refl. Qed.
Lemma D_cc4a4 : decode_any W_cc4a4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc4a8 : bv 32 := 0x05e00893.
Lemma F_cc4a8 : fetch_word asegs (0xcc484 : word) = Some W_cc4a8.
Proof. vm_refl. Qed.
Lemma D_cc4a8 : decode_any W_cc4a8 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc4ac : bv 32 := 0x00000073.
Lemma F_cc4ac : fetch_word asegs (0xcc488 : word) = Some W_cc4ac.
Proof. vm_refl. Qed.

Lemma E_cc4ac : is_ecall W_cc4ac = true.
Proof. reflexivity. Qed.

Definition W_cc740 : bv 32 := 0x00040513.
Lemma F_cc740 : fetch_word asegs (0xcc71c : word) = Some W_cc740.
Proof. vm_refl. Qed.
Lemma D_cc740 : decode_any W_cc740 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc744 : bv 32 := 0xd61ff0ef.
Lemma F_cc744 : fetch_word asegs (0xcc720 : word) = Some W_cc744.
Proof. vm_refl. Qed.
Lemma D_cc744 : decode_any W_cc744 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

Definition W_cca2c : bv 32 := 0xfffff5b7.
Lemma F_cca2c : fetch_word asegs (0xcca08 : word) = Some W_cca2c.
Proof. vm_refl. Qed.
Lemma D_cca2c : decode_any W_cca2c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_cca30 : bv 32 := 0x0015859b.
Lemma F_cca30 : fetch_word asegs (0xcca0c : word) = Some W_cca30.
Proof. vm_refl. Qed.
Lemma D_cca30 : decode_any W_cca30 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cca34 : bv 32 := 0x02b56663.
Lemma F_cca34 : fetch_word asegs (0xcca10 : word) = Some W_cca34.
Proof. vm_refl. Qed.
Lemma D_cca34 : decode_any W_cca34 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_cca60 : bv 32 := 0x00008067.
Lemma F_cca60 : fetch_word asegs (0xcca3c : word) = Some W_cca60.
Proof. vm_refl. Qed.
Lemma D_cca60 : decode_any W_cca60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
