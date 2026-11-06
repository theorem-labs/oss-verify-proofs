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

Definition W_d29f4 : bv 32 := 0xf9010113.
Lemma F_d29f4 : fetch_word asegs (0xd29d0 : word) = Some W_d29f4.
Proof. vm_refl. Qed.
Lemma D_d29f4 : decode_any W_d29f4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_d29f8 : bv 32 := 0x06113423.
Lemma F_d29f8 : fetch_word asegs (0xd29d4 : word) = Some W_d29f8.
Proof. vm_refl. Qed.
Lemma D_d29f8 : decode_any W_d29f8 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_d29fc : bv 32 := 0x06813023.
Lemma F_d29fc : fetch_word asegs (0xd29d8 : word) = Some W_d29fc.
Proof. vm_refl. Qed.
Lemma D_d29fc : decode_any W_d29fc = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a00 : bv 32 := 0x04913c23.
Lemma F_d2a00 : fetch_word asegs (0xd29dc : word) = Some W_d2a00.
Proof. vm_refl. Qed.
Lemma D_d2a00 : decode_any W_d2a00 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a04 : bv 32 := 0x05213823.
Lemma F_d2a04 : fetch_word asegs (0xd29e0 : word) = Some W_d2a04.
Proof. vm_refl. Qed.
Lemma D_d2a04 : decode_any W_d2a04 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a08 : bv 32 := 0x05313423.
Lemma F_d2a08 : fetch_word asegs (0xd29e4 : word) = Some W_d2a08.
Proof. vm_refl. Qed.
Lemma D_d2a08 : decode_any W_d2a08 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a0c : bv 32 := 0x05413023.
Lemma F_d2a0c : fetch_word asegs (0xd29e8 : word) = Some W_d2a0c.
Proof. vm_refl. Qed.
Lemma D_d2a0c : decode_any W_d2a0c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a10 : bv 32 := 0x03513c23.
Lemma F_d2a10 : fetch_word asegs (0xd29ec : word) = Some W_d2a10.
Proof. vm_refl. Qed.
Lemma D_d2a10 : decode_any W_d2a10 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a14 : bv 32 := 0x03613823.
Lemma F_d2a14 : fetch_word asegs (0xd29f0 : word) = Some W_d2a14.
Proof. vm_refl. Qed.
Lemma D_d2a14 : decode_any W_d2a14 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a18 : bv 32 := 0x00060413.
Lemma F_d2a18 : fetch_word asegs (0xd29f4 : word) = Some W_d2a18.
Proof. vm_refl. Qed.
Lemma D_d2a18 : decode_any W_d2a18 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a1c : bv 32 := 0x00050493.
Lemma F_d2a1c : fetch_word asegs (0xd29f8 : word) = Some W_d2a1c.
Proof. vm_refl. Qed.
Lemma D_d2a1c : decode_any W_d2a1c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a20 : bv 32 := 0x00014517.
Lemma F_d2a20 : fetch_word asegs (0xd29fc : word) = Some W_d2a20.
Proof. vm_refl. Qed.
Lemma D_d2a20 : decode_any W_d2a20 = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a24 : bv 32 := 0x18453a83.
Lemma F_d2a24 : fetch_word asegs (0xd2a00 : word) = Some W_d2a24.
Proof. vm_refl. Qed.
Lemma D_d2a24 : decode_any W_d2a24 = Some (Load SZ8 true 21 10 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a28 : bv 32 := 0x000ab503.
Lemma F_d2a28 : fetch_word asegs (0xd2a04 : word) = Some W_d2a28.
Proof. vm_refl. Qed.
Lemma D_d2a28 : decode_any W_d2a28 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a2c : bv 32 := 0x02a13423.
Lemma F_d2a2c : fetch_word asegs (0xd2a08 : word) = Some W_d2a2c.
Proof. vm_refl. Qed.
Lemma D_d2a2c : decode_any W_d2a2c = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a30 : bv 32 := 0x0284b503.
Lemma F_d2a30 : fetch_word asegs (0xd2a0c : word) = Some W_d2a30.
Proof. vm_refl. Qed.
Lemma D_d2a30 : decode_any W_d2a30 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a34 : bv 32 := 0x0384b603.
Lemma F_d2a34 : fetch_word asegs (0xd2a10 : word) = Some W_d2a34.
Proof. vm_refl. Qed.
Lemma D_d2a34 : decode_any W_d2a34 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a38 : bv 32 := 0x40c50b33.
Lemma F_d2a38 : fetch_word asegs (0xd2a14 : word) = Some W_d2a38.
Proof. vm_refl. Qed.
Lemma D_d2a38 : decode_any W_d2a38 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a3c : bv 32 := 0x00c546b3.
Lemma F_d2a3c : fetch_word asegs (0xd2a18 : word) = Some W_d2a3c.
Proof. vm_refl. Qed.
Lemma D_d2a3c : decode_any W_d2a3c = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a40 : bv 32 := 0x00c13423.
Lemma F_d2a40 : fetch_word asegs (0xd2a1c : word) = Some W_d2a40.
Proof. vm_refl. Qed.
Lemma D_d2a40 : decode_any W_d2a40 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a44 : bv 32 := 0x01613823.
Lemma F_d2a44 : fetch_word asegs (0xd2a20 : word) = Some W_d2a44.
Proof. vm_refl. Qed.
Lemma D_d2a44 : decode_any W_d2a44 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a48 : bv 32 := 0x00b13c23.
Lemma F_d2a48 : fetch_word asegs (0xd2a24 : word) = Some W_d2a48.
Proof. vm_refl. Qed.
Lemma D_d2a48 : decode_any W_d2a48 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a4c : bv 32 := 0x02813023.
Lemma F_d2a4c : fetch_word asegs (0xd2a28 : word) = Some W_d2a4c.
Proof. vm_refl. Qed.
Lemma D_d2a4c : decode_any W_d2a4c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a50 : bv 32 := 0x008b0b33.
Lemma F_d2a50 : fetch_word asegs (0xd2a2c : word) = Some W_d2a50.
Proof. vm_refl. Qed.
Lemma D_d2a50 : decode_any W_d2a50 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a54 : bv 32 := 0x00d03933.
Lemma F_d2a54 : fetch_word asegs (0xd2a30 : word) = Some W_d2a54.
Proof. vm_refl. Qed.
Lemma D_d2a54 : decode_any W_d2a54 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a58 : bv 32 := 0x00c50663.
Lemma F_d2a58 : fetch_word asegs (0xd2a34 : word) = Some W_d2a58.
Proof. vm_refl. Qed.
Lemma D_d2a58 : decode_any W_d2a58 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a5c : bv 32 := 0x00810993.
Lemma F_d2a5c : fetch_word asegs (0xd2a38 : word) = Some W_d2a5c.
Proof. vm_refl. Qed.
Lemma D_d2a5c : decode_any W_d2a5c = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a60 : bv 32 := 0x0080006f.
Lemma F_d2a60 : fetch_word asegs (0xd2a3c : word) = Some W_d2a60.
Proof. vm_refl. Qed.
Lemma D_d2a60 : decode_any W_d2a60 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a64 : bv 32 := 0x01810993.
Lemma F_d2a64 : fetch_word asegs (0xd2a40 : word) = Some W_d2a64.
Proof. vm_refl. Qed.
Lemma D_d2a64 : decode_any W_d2a64 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a68 : bv 32 := 0x0784a503.
Lemma F_d2a68 : fetch_word asegs (0xd2a44 : word) = Some W_d2a68.
Proof. vm_refl. Qed.
Lemma D_d2a68 : decode_any W_d2a68 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a6c : bv 32 := 0x00190913.
Lemma F_d2a6c : fetch_word asegs (0xd2a48 : word) = Some W_d2a6c.
Proof. vm_refl. Qed.
Lemma D_d2a6c : decode_any W_d2a6c = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a70 : bv 32 := 0x04200893.
Lemma F_d2a70 : fetch_word asegs (0xd2a4c : word) = Some W_d2a70.
Proof. vm_refl. Qed.
Lemma D_d2a70 : decode_any W_d2a70 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a74 : bv 32 := 0x00098593.
Lemma F_d2a74 : fetch_word asegs (0xd2a50 : word) = Some W_d2a74.
Proof. vm_refl. Qed.
Lemma D_d2a74 : decode_any W_d2a74 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a78 : bv 32 := 0x00090613.
Lemma F_d2a78 : fetch_word asegs (0xd2a54 : word) = Some W_d2a78.
Proof. vm_refl. Qed.
Lemma D_d2a78 : decode_any W_d2a78 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a7c : bv 32 := 0x00000073.
Lemma F_d2a7c : fetch_word asegs (0xd2a58 : word) = Some W_d2a7c.
Proof. vm_refl. Qed.

Lemma E_d2a7c : is_ecall W_d2a7c = true.
Proof. reflexivity. Qed.

Definition W_d2a80 : bv 32 := 0xfadf90ef.
Lemma F_d2a80 : fetch_word asegs (0xd2a5c : word) = Some W_d2a80.
Proof. vm_refl. Qed.
Lemma D_d2a80 : decode_any W_d2a80 = Some (Jal 1 2072492, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a84 : bv 32 := 0x09651863.
Lemma F_d2a84 : fetch_word asegs (0xd2a60 : word) = Some W_d2a84.
Proof. vm_refl. Qed.
Lemma D_d2a84 : decode_any W_d2a84 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a88 : bv 32 := 0x0584b503.
Lemma F_d2a88 : fetch_word asegs (0xd2a64 : word) = Some W_d2a88.
Proof. vm_refl. Qed.
Lemma D_d2a88 : decode_any W_d2a88 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a8c : bv 32 := 0x0604b583.
Lemma F_d2a8c : fetch_word asegs (0xd2a68 : word) = Some W_d2a8c.
Proof. vm_refl. Qed.
Lemma D_d2a8c : decode_any W_d2a8c = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a90 : bv 32 := 0x00b505b3.
Lemma F_d2a90 : fetch_word asegs (0xd2a6c : word) = Some W_d2a90.
Proof. vm_refl. Qed.
Lemma D_d2a90 : decode_any W_d2a90 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a94 : bv 32 := 0x02b4b023.
Lemma F_d2a94 : fetch_word asegs (0xd2a70 : word) = Some W_d2a94.
Proof. vm_refl. Qed.
Lemma D_d2a94 : decode_any W_d2a94 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a98 : bv 32 := 0x02a4b423.
Lemma F_d2a98 : fetch_word asegs (0xd2a74 : word) = Some W_d2a98.
Proof. vm_refl. Qed.
Lemma D_d2a98 : decode_any W_d2a98 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2a9c : bv 32 := 0x02a4bc23.
Lemma F_d2a9c : fetch_word asegs (0xd2a78 : word) = Some W_d2a9c.
Proof. vm_refl. Qed.
Lemma D_d2a9c : decode_any W_d2a9c = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2aa0 : bv 32 := 0x00040513.
Lemma F_d2aa0 : fetch_word asegs (0xd2a7c : word) = Some W_d2aa0.
Proof. vm_refl. Qed.
Lemma D_d2aa0 : decode_any W_d2aa0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2aa4 : bv 32 := 0x000ab583.
Lemma F_d2aa4 : fetch_word asegs (0xd2a80 : word) = Some W_d2aa4.
Proof. vm_refl. Qed.
Lemma D_d2aa4 : decode_any W_d2aa4 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2aa8 : bv 32 := 0x02813603.
Lemma F_d2aa8 : fetch_word asegs (0xd2a84 : word) = Some W_d2aa8.
Proof. vm_refl. Qed.
Lemma D_d2aa8 : decode_any W_d2aa8 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2aac : bv 32 := 0x0cc59a63.
Lemma F_d2aac : fetch_word asegs (0xd2a88 : word) = Some W_d2aac.
Proof. vm_refl. Qed.
Lemma D_d2aac : decode_any W_d2aac = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ab0 : bv 32 := 0x06813083.
Lemma F_d2ab0 : fetch_word asegs (0xd2a8c : word) = Some W_d2ab0.
Proof. vm_refl. Qed.
Lemma D_d2ab0 : decode_any W_d2ab0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ab4 : bv 32 := 0x06013403.
Lemma F_d2ab4 : fetch_word asegs (0xd2a90 : word) = Some W_d2ab4.
Proof. vm_refl. Qed.
Lemma D_d2ab4 : decode_any W_d2ab4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ab8 : bv 32 := 0x05813483.
Lemma F_d2ab8 : fetch_word asegs (0xd2a94 : word) = Some W_d2ab8.
Proof. vm_refl. Qed.
Lemma D_d2ab8 : decode_any W_d2ab8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2abc : bv 32 := 0x05013903.
Lemma F_d2abc : fetch_word asegs (0xd2a98 : word) = Some W_d2abc.
Proof. vm_refl. Qed.
Lemma D_d2abc : decode_any W_d2abc = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ac0 : bv 32 := 0x04813983.
Lemma F_d2ac0 : fetch_word asegs (0xd2a9c : word) = Some W_d2ac0.
Proof. vm_refl. Qed.
Lemma D_d2ac0 : decode_any W_d2ac0 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ac4 : bv 32 := 0x04013a03.
Lemma F_d2ac4 : fetch_word asegs (0xd2aa0 : word) = Some W_d2ac4.
Proof. vm_refl. Qed.
Lemma D_d2ac4 : decode_any W_d2ac4 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ac8 : bv 32 := 0x03813a83.
Lemma F_d2ac8 : fetch_word asegs (0xd2aa4 : word) = Some W_d2ac8.
Proof. vm_refl. Qed.
Lemma D_d2ac8 : decode_any W_d2ac8 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2acc : bv 32 := 0x03013b03.
Lemma F_d2acc : fetch_word asegs (0xd2aa8 : word) = Some W_d2acc.
Proof. vm_refl. Qed.
Lemma D_d2acc : decode_any W_d2acc = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ad0 : bv 32 := 0x07010113.
Lemma F_d2ad0 : fetch_word asegs (0xd2aac : word) = Some W_d2ad0.
Proof. vm_refl. Qed.
Lemma D_d2ad0 : decode_any W_d2ad0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ad4 : bv 32 := 0x00008067.
Lemma F_d2ad4 : fetch_word asegs (0xd2ab0 : word) = Some W_d2ad4.
Proof. vm_refl. Qed.
Lemma D_d2ad4 : decode_any W_d2ad4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ad8 : bv 32 := 0x00800713.
Lemma F_d2ad8 : fetch_word asegs (0xd2ab4 : word) = Some W_d2ad8.
Proof. vm_refl. Qed.
Lemma D_d2ad8 : decode_any W_d2ad8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2adc : bv 32 := 0x000a0593.
Lemma F_d2adc : fetch_word asegs (0xd2ab8 : word) = Some W_d2adc.
Proof. vm_refl. Qed.
Lemma D_d2adc : decode_any W_d2adc = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ae0 : bv 32 := 0x00e98733.
Lemma F_d2ae0 : fetch_word asegs (0xd2abc : word) = Some W_d2ae0.
Proof. vm_refl. Qed.
Lemma D_d2ae0 : decode_any W_d2ae0 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ae4 : bv 32 := 0x00073783.
Lemma F_d2ae4 : fetch_word asegs (0xd2ac0 : word) = Some W_d2ae4.
Proof. vm_refl. Qed.
Lemma D_d2ae4 : decode_any W_d2ae4 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ae8 : bv 32 := 0x40ab0b33.
Lemma F_d2ae8 : fetch_word asegs (0xd2ac4 : word) = Some W_d2ae8.
Proof. vm_refl. Qed.
Lemma D_d2ae8 : decode_any W_d2ae8 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2aec : bv 32 := 0x0784a503.
Lemma F_d2aec : fetch_word asegs (0xd2ac8 : word) = Some W_d2aec.
Proof. vm_refl. Qed.
Lemma D_d2aec : decode_any W_d2aec = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2af0 : bv 32 := 0x40c9093b.
Lemma F_d2af0 : fetch_word asegs (0xd2acc : word) = Some W_d2af0.
Proof. vm_refl. Qed.
Lemma D_d2af0 : decode_any W_d2af0 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2af4 : bv 32 := 0x40d787b3.
Lemma F_d2af4 : fetch_word asegs (0xd2ad0 : word) = Some W_d2af4.
Proof. vm_refl. Qed.
Lemma D_d2af4 : decode_any W_d2af4 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2af8 : bv 32 := 0x00f73023.
Lemma F_d2af8 : fetch_word asegs (0xd2ad4 : word) = Some W_d2af8.
Proof. vm_refl. Qed.
Lemma D_d2af8 : decode_any W_d2af8 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2afc : bv 32 := 0x04200893.
Lemma F_d2afc : fetch_word asegs (0xd2ad8 : word) = Some W_d2afc.
Proof. vm_refl. Qed.
Lemma D_d2afc : decode_any W_d2afc = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b00 : bv 32 := 0x00090613.
Lemma F_d2b00 : fetch_word asegs (0xd2adc : word) = Some W_d2b00.
Proof. vm_refl. Qed.
Lemma D_d2b00 : decode_any W_d2b00 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b04 : bv 32 := 0x00000073.
Lemma F_d2b04 : fetch_word asegs (0xd2ae0 : word) = Some W_d2b04.
Proof. vm_refl. Qed.

Lemma E_d2b04 : is_ecall W_d2b04 = true.
Proof. reflexivity. Qed.

Definition W_d2b08 : bv 32 := 0xf25f90ef.
Lemma F_d2b08 : fetch_word asegs (0xd2ae4 : word) = Some W_d2b08.
Proof. vm_refl. Qed.
Lemma D_d2b08 : decode_any W_d2b08 = Some (Jal 1 2072356, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b0c : bv 32 := 0x000a0993.
Lemma F_d2b0c : fetch_word asegs (0xd2ae8 : word) = Some W_d2b0c.
Proof. vm_refl. Qed.
Lemma D_d2b0c : decode_any W_d2b0c = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b10 : bv 32 := 0xf7650ce3.
Lemma F_d2b10 : fetch_word asegs (0xd2aec : word) = Some W_d2b10.
Proof. vm_refl. Qed.
Lemma D_d2b10 : decode_any W_d2b10 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b14 : bv 32 := 0x02054c63.
Lemma F_d2b14 : fetch_word asegs (0xd2af0 : word) = Some W_d2b14.
Proof. vm_refl. Qed.
Lemma D_d2b14 : decode_any W_d2b14 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b18 : bv 32 := 0x0089b583.
Lemma F_d2b18 : fetch_word asegs (0xd2af4 : word) = Some W_d2b18.
Proof. vm_refl. Qed.
Lemma D_d2b18 : decode_any W_d2b18 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b1c : bv 32 := 0x00a5b633.
Lemma F_d2b1c : fetch_word asegs (0xd2af8 : word) = Some W_d2b1c.
Proof. vm_refl. Qed.
Lemma D_d2b1c : decode_any W_d2b1c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b20 : bv 32 := 0x00461a13.
Lemma F_d2b20 : fetch_word asegs (0xd2afc : word) = Some W_d2b20.
Proof. vm_refl. Qed.
Lemma D_d2b20 : decode_any W_d2b20 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b24 : bv 32 := 0x01498a33.
Lemma F_d2b24 : fetch_word asegs (0xd2b00 : word) = Some W_d2b24.
Proof. vm_refl. Qed.
Lemma D_d2b24 : decode_any W_d2b24 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b28 : bv 32 := 0x000a3703.
Lemma F_d2b28 : fetch_word asegs (0xd2b04 : word) = Some W_d2b28.
Proof. vm_refl. Qed.
Lemma D_d2b28 : decode_any W_d2b28 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b2c : bv 32 := 0x40c006b3.
Lemma F_d2b2c : fetch_word asegs (0xd2b08 : word) = Some W_d2b2c.
Proof. vm_refl. Qed.
Lemma D_d2b2c : decode_any W_d2b2c = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b30 : bv 32 := 0x00b6f6b3.
Lemma F_d2b30 : fetch_word asegs (0xd2b0c : word) = Some W_d2b30.
Proof. vm_refl. Qed.
Lemma D_d2b30 : decode_any W_d2b30 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b34 : bv 32 := 0x40d506b3.
Lemma F_d2b34 : fetch_word asegs (0xd2b10 : word) = Some W_d2b34.
Proof. vm_refl. Qed.
Lemma D_d2b34 : decode_any W_d2b34 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b38 : bv 32 := 0x00d70733.
Lemma F_d2b38 : fetch_word asegs (0xd2b14 : word) = Some W_d2b38.
Proof. vm_refl. Qed.
Lemma D_d2b38 : decode_any W_d2b38 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b3c : bv 32 := 0x00ea3023.
Lemma F_d2b3c : fetch_word asegs (0xd2b18 : word) = Some W_d2b3c.
Proof. vm_refl. Qed.
Lemma D_d2b3c : decode_any W_d2b3c = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b40 : bv 32 := 0xf8a5fce3.
Lemma F_d2b40 : fetch_word asegs (0xd2b1c : word) = Some W_d2b40.
Proof. vm_refl. Qed.
Lemma D_d2b40 : decode_any W_d2b40 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b44 : bv 32 := 0x01800713.
Lemma F_d2b44 : fetch_word asegs (0xd2b20 : word) = Some W_d2b44.
Proof. vm_refl. Qed.
Lemma D_d2b44 : decode_any W_d2b44 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2b48 : bv 32 := 0xf95ff06f.
Lemma F_d2b48 : fetch_word asegs (0xd2b24 : word) = Some W_d2b48.
Proof. vm_refl. Qed.
Lemma D_d2b48 : decode_any W_d2b48 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2fd4 : bv 32 := 0xff010113.
Lemma F_d2fd4 : fetch_word asegs (0xd2fb0 : word) = Some W_d2fd4.
Proof. vm_refl. Qed.
Lemma D_d2fd4 : decode_any W_d2fd4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2fd8 : bv 32 := 0x00113423.
Lemma F_d2fd8 : fetch_word asegs (0xd2fb4 : word) = Some W_d2fd8.
Proof. vm_refl. Qed.
Lemma D_d2fd8 : decode_any W_d2fd8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2fdc : bv 32 := 0x00813023.
Lemma F_d2fdc : fetch_word asegs (0xd2fb8 : word) = Some W_d2fdc.
Proof. vm_refl. Qed.
Lemma D_d2fdc : decode_any W_d2fdc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2fe0 : bv 32 := 0x5fc000ef.
Lemma F_d2fe0 : fetch_word asegs (0xd2fbc : word) = Some W_d2fe0.
Proof. vm_refl. Qed.
Lemma D_d2fe0 : decode_any W_d2fe0 = Some (Jal 1 1532, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2fe4 : bv 32 := 0x00053403.
Lemma F_d2fe4 : fetch_word asegs (0xd2fc0 : word) = Some W_d2fe4.
Proof. vm_refl. Qed.
Lemma D_d2fe4 : decode_any W_d2fe4 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2fe8 : bv 32 := 0x12041663.
Lemma F_d2fe8 : fetch_word asegs (0xd2fc4 : word) = Some W_d2fe8.
Proof. vm_refl. Qed.
Lemma D_d2fe8 : decode_any W_d2fe8 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2fec : bv 32 := 0x00018517.
Lemma F_d2fec : fetch_word asegs (0xd2fc8 : word) = Some W_d2fec.
Proof. vm_refl. Qed.
Lemma D_d2fec : decode_any W_d2fec = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ff0 : bv 32 := 0x96053403.
Lemma F_d2ff0 : fetch_word asegs (0xd2fcc : word) = Some W_d2ff0.
Proof. vm_refl. Qed.
Lemma D_d2ff0 : decode_any W_d2ff0 = Some (Load SZ8 true 8 10 2400, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ff4 : bv 32 := 0x04040a63.
Lemma F_d2ff4 : fetch_word asegs (0xd2fd0 : word) = Some W_d2ff4.
Proof. vm_refl. Qed.
Lemma D_d2ff4 : decode_any W_d2ff4 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ff8 : bv 32 := 0x08c42503.
Lemma F_d2ff8 : fetch_word asegs (0xd2fd4 : word) = Some W_d2ff8.
Proof. vm_refl. Qed.
Lemma D_d2ff8 : decode_any W_d2ff8 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2ffc : bv 32 := 0x00054663.
Lemma F_d2ffc : fetch_word asegs (0xd2fd8 : word) = Some W_d2ffc.
Proof. vm_refl. Qed.
Lemma D_d2ffc : decode_any W_d2ffc = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3008 : bv 32 := 0x02843503.
Lemma F_d3008 : fetch_word asegs (0xd2fe4 : word) = Some W_d3008.
Proof. vm_refl. Qed.
Lemma D_d3008 : decode_any W_d3008 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d300c : bv 32 := 0x03843583.
Lemma F_d300c : fetch_word asegs (0xd2fe8 : word) = Some W_d300c.
Proof. vm_refl. Qed.
Lemma D_d300c : decode_any W_d300c = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3010 : bv 32 := 0x00b50c63.
Lemma F_d3010 : fetch_word asegs (0xd2fec : word) = Some W_d3010.
Proof. vm_refl. Qed.
Lemma D_d3010 : decode_any W_d3010 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3028 : bv 32 := 0x00843503.
Lemma F_d3028 : fetch_word asegs (0xd3004 : word) = Some W_d3028.
Proof. vm_refl. Qed.
Lemma D_d3028 : decode_any W_d3028 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d302c : bv 32 := 0x01043583.
Lemma F_d302c : fetch_word asegs (0xd3008 : word) = Some W_d302c.
Proof. vm_refl. Qed.
Lemma D_d302c : decode_any W_d302c = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3030 : bv 32 := 0x00b50c63.
Lemma F_d3030 : fetch_word asegs (0xd300c : word) = Some W_d3030.
Proof. vm_refl. Qed.
Lemma D_d3030 : decode_any W_d3030 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3048 : bv 32 := 0x00018517.
Lemma F_d3048 : fetch_word asegs (0xd3024 : word) = Some W_d3048.
Proof. vm_refl. Qed.
Lemma D_d3048 : decode_any W_d3048 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d304c : bv 32 := 0x81453403.
Lemma F_d304c : fetch_word asegs (0xd3028 : word) = Some W_d304c.
Proof. vm_refl. Qed.
Lemma D_d304c : decode_any W_d304c = Some (Load SZ8 true 8 10 2068, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3050 : bv 32 := 0x04040a63.
Lemma F_d3050 : fetch_word asegs (0xd302c : word) = Some W_d3050.
Proof. vm_refl. Qed.
Lemma D_d3050 : decode_any W_d3050 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3054 : bv 32 := 0x08c42503.
Lemma F_d3054 : fetch_word asegs (0xd3030 : word) = Some W_d3054.
Proof. vm_refl. Qed.
Lemma D_d3054 : decode_any W_d3054 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3058 : bv 32 := 0x00054663.
Lemma F_d3058 : fetch_word asegs (0xd3034 : word) = Some W_d3058.
Proof. vm_refl. Qed.
Lemma D_d3058 : decode_any W_d3058 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3064 : bv 32 := 0x02843503.
Lemma F_d3064 : fetch_word asegs (0xd3040 : word) = Some W_d3064.
Proof. vm_refl. Qed.
Lemma D_d3064 : decode_any W_d3064 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3068 : bv 32 := 0x03843583.
Lemma F_d3068 : fetch_word asegs (0xd3044 : word) = Some W_d3068.
Proof. vm_refl. Qed.
Lemma D_d3068 : decode_any W_d3068 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d306c : bv 32 := 0x00b50c63.
Lemma F_d306c : fetch_word asegs (0xd3048 : word) = Some W_d306c.
Proof. vm_refl. Qed.
Lemma D_d306c : decode_any W_d306c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3070 : bv 32 := 0x04843683.
Lemma F_d3070 : fetch_word asegs (0xd304c : word) = Some W_d3070.
Proof. vm_refl. Qed.
Lemma D_d3070 : decode_any W_d3070 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3074 : bv 32 := 0x00040513.
Lemma F_d3074 : fetch_word asegs (0xd3050 : word) = Some W_d3074.
Proof. vm_refl. Qed.
Lemma D_d3074 : decode_any W_d3074 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3078 : bv 32 := 0x00000593.
Lemma F_d3078 : fetch_word asegs (0xd3054 : word) = Some W_d3078.
Proof. vm_refl. Qed.
Lemma D_d3078 : decode_any W_d3078 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d307c : bv 32 := 0x00000613.
Lemma F_d307c : fetch_word asegs (0xd3058 : word) = Some W_d307c.
Proof. vm_refl. Qed.
Lemma D_d307c : decode_any W_d307c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3080 : bv 32 := 0x000680e7.
Lemma F_d3080 : fetch_word asegs (0xd305c : word) = Some W_d3080.
Proof. vm_refl. Qed.
Lemma D_d3080 : decode_any W_d3080 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3084 : bv 32 := 0x00843503.
Lemma F_d3084 : fetch_word asegs (0xd3060 : word) = Some W_d3084.
Proof. vm_refl. Qed.
Lemma D_d3084 : decode_any W_d3084 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3088 : bv 32 := 0x01043583.
Lemma F_d3088 : fetch_word asegs (0xd3064 : word) = Some W_d3088.
Proof. vm_refl. Qed.
Lemma D_d3088 : decode_any W_d3088 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d308c : bv 32 := 0x00b50c63.
Lemma F_d308c : fetch_word asegs (0xd3068 : word) = Some W_d308c.
Proof. vm_refl. Qed.
Lemma D_d308c : decode_any W_d308c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30a4 : bv 32 := 0x00017517.
Lemma F_d30a4 : fetch_word asegs (0xd3080 : word) = Some W_d30a4.
Proof. vm_refl. Qed.
Lemma D_d30a4 : decode_any W_d30a4 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30a8 : bv 32 := 0x6c853403.
Lemma F_d30a8 : fetch_word asegs (0xd3084 : word) = Some W_d30a8.
Proof. vm_refl. Qed.
Lemma D_d30a8 : decode_any W_d30a8 = Some (Load SZ8 true 8 10 1736, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30ac : bv 32 := 0x0a040e63.
Lemma F_d30ac : fetch_word asegs (0xd3088 : word) = Some W_d30ac.
Proof. vm_refl. Qed.
Lemma D_d30ac : decode_any W_d30ac = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30b0 : bv 32 := 0x08c42503.
Lemma F_d30b0 : fetch_word asegs (0xd308c : word) = Some W_d30b0.
Proof. vm_refl. Qed.
Lemma D_d30b0 : decode_any W_d30b0 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30b4 : bv 32 := 0x00054663.
Lemma F_d30b4 : fetch_word asegs (0xd3090 : word) = Some W_d30b4.
Proof. vm_refl. Qed.
Lemma D_d30b4 : decode_any W_d30b4 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30c0 : bv 32 := 0x02843503.
Lemma F_d30c0 : fetch_word asegs (0xd309c : word) = Some W_d30c0.
Proof. vm_refl. Qed.
Lemma D_d30c0 : decode_any W_d30c0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30c4 : bv 32 := 0x03843583.
Lemma F_d30c4 : fetch_word asegs (0xd30a0 : word) = Some W_d30c4.
Proof. vm_refl. Qed.
Lemma D_d30c4 : decode_any W_d30c4 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30c8 : bv 32 := 0x00b50c63.
Lemma F_d30c8 : fetch_word asegs (0xd30a4 : word) = Some W_d30c8.
Proof. vm_refl. Qed.
Lemma D_d30c8 : decode_any W_d30c8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30e0 : bv 32 := 0x00843503.
Lemma F_d30e0 : fetch_word asegs (0xd30bc : word) = Some W_d30e0.
Proof. vm_refl. Qed.
Lemma D_d30e0 : decode_any W_d30e0 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30e4 : bv 32 := 0x01043583.
Lemma F_d30e4 : fetch_word asegs (0xd30c0 : word) = Some W_d30e4.
Proof. vm_refl. Qed.
Lemma D_d30e4 : decode_any W_d30e4 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d30e8 : bv 32 := 0x08b50063.
Lemma F_d30e8 : fetch_word asegs (0xd30c4 : word) = Some W_d30e8.
Proof. vm_refl. Qed.
Lemma D_d30e8 : decode_any W_d30e8 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3168 : bv 32 := 0x00813083.
Lemma F_d3168 : fetch_word asegs (0xd3144 : word) = Some W_d3168.
Proof. vm_refl. Qed.
Lemma D_d3168 : decode_any W_d3168 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d316c : bv 32 := 0x00013403.
Lemma F_d316c : fetch_word asegs (0xd3148 : word) = Some W_d316c.
Proof. vm_refl. Qed.
Lemma D_d316c : decode_any W_d316c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3170 : bv 32 := 0x01010113.
Lemma F_d3170 : fetch_word asegs (0xd314c : word) = Some W_d3170.
Proof. vm_refl. Qed.
Lemma D_d3170 : decode_any W_d3170 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3174 : bv 32 := 0x00008067.
Lemma F_d3174 : fetch_word asegs (0xd3150 : word) = Some W_d3174.
Proof. vm_refl. Qed.
Lemma D_d3174 : decode_any W_d3174 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d35dc : bv 32 := 0xff010113.
Lemma F_d35dc : fetch_word asegs (0xd35b8 : word) = Some W_d35dc.
Proof. vm_refl. Qed.
Lemma D_d35dc : decode_any W_d35dc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d35e0 : bv 32 := 0x00113423.
Lemma F_d35e0 : fetch_word asegs (0xd35bc : word) = Some W_d35e0.
Proof. vm_refl. Qed.
Lemma D_d35e0 : decode_any W_d35e0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d35e4 : bv 32 := 0x00813023.
Lemma F_d35e4 : fetch_word asegs (0xd35c0 : word) = Some W_d35e4.
Proof. vm_refl. Qed.
Lemma D_d35e4 : decode_any W_d35e4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d35e8 : bv 32 := 0x00570517.
Lemma F_d35e8 : fetch_word asegs (0xd35c4 : word) = Some W_d35e8.
Proof. vm_refl. Qed.
Lemma D_d35e8 : decode_any W_d35e8 = Some (Auipc 10 1392, 4%Z).
Proof. vm_refl. Qed.

Definition W_d35ec : bv 32 := 0x00450413.
Lemma F_d35ec : fetch_word asegs (0xd35c8 : word) = Some W_d35ec.
Proof. vm_refl. Qed.
Lemma D_d35ec : decode_any W_d35ec = Some (OpImm ALU_ADD 8 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_d35f0 : bv 32 := 0x00040513.
Lemma F_d35f0 : fetch_word asegs (0xd35cc : word) = Some W_d35f0.
Proof. vm_refl. Qed.
Lemma D_d35f0 : decode_any W_d35f0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d35f4 : bv 32 := 0x66d080ef.
Lemma F_d35f4 : fetch_word asegs (0xd35d0 : word) = Some W_d35f4.
Proof. vm_refl. Qed.
Lemma D_d35f4 : decode_any W_d35f4 = Some (Jal 1 36460, 4%Z).
Proof. vm_refl. Qed.

Definition W_d35f8 : bv 32 := 0x00840513.
Lemma F_d35f8 : fetch_word asegs (0xd35d4 : word) = Some W_d35f8.
Proof. vm_refl. Qed.
Lemma D_d35f8 : decode_any W_d35f8 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d35fc : bv 32 := 0x00813083.
Lemma F_d35fc : fetch_word asegs (0xd35d8 : word) = Some W_d35fc.
Proof. vm_refl. Qed.
Lemma D_d35fc : decode_any W_d35fc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3600 : bv 32 := 0x00013403.
Lemma F_d3600 : fetch_word asegs (0xd35dc : word) = Some W_d3600.
Proof. vm_refl. Qed.
Lemma D_d3600 : decode_any W_d3600 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3604 : bv 32 := 0x01010113.
Lemma F_d3604 : fetch_word asegs (0xd35e0 : word) = Some W_d3604.
Proof. vm_refl. Qed.
Lemma D_d3604 : decode_any W_d3604 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d3608 : bv 32 := 0x00008067.
Lemma F_d3608 : fetch_word asegs (0xd35e4 : word) = Some W_d3608.
Proof. vm_refl. Qed.
Lemma D_d3608 : decode_any W_d3608 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
