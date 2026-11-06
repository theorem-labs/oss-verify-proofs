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

Definition W_d50e0 : bv 32 := 0xf9010113.
Lemma F_d50e0 : fetch_word asegs (0xd5094 : word) = Some W_d50e0.
Proof. vm_refl. Qed.
Lemma D_d50e0 : decode_any W_d50e0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_d50e4 : bv 32 := 0x06113423.
Lemma F_d50e4 : fetch_word asegs (0xd5098 : word) = Some W_d50e4.
Proof. vm_refl. Qed.
Lemma D_d50e4 : decode_any W_d50e4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_d50e8 : bv 32 := 0x06813023.
Lemma F_d50e8 : fetch_word asegs (0xd509c : word) = Some W_d50e8.
Proof. vm_refl. Qed.
Lemma D_d50e8 : decode_any W_d50e8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d50ec : bv 32 := 0x04913c23.
Lemma F_d50ec : fetch_word asegs (0xd50a0 : word) = Some W_d50ec.
Proof. vm_refl. Qed.
Lemma D_d50ec : decode_any W_d50ec = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d50f0 : bv 32 := 0x05213823.
Lemma F_d50f0 : fetch_word asegs (0xd50a4 : word) = Some W_d50f0.
Proof. vm_refl. Qed.
Lemma D_d50f0 : decode_any W_d50f0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_d50f4 : bv 32 := 0x05313423.
Lemma F_d50f4 : fetch_word asegs (0xd50a8 : word) = Some W_d50f4.
Proof. vm_refl. Qed.
Lemma D_d50f4 : decode_any W_d50f4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d50f8 : bv 32 := 0x05413023.
Lemma F_d50f8 : fetch_word asegs (0xd50ac : word) = Some W_d50f8.
Proof. vm_refl. Qed.
Lemma D_d50f8 : decode_any W_d50f8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_d50fc : bv 32 := 0x03513c23.
Lemma F_d50fc : fetch_word asegs (0xd50b0 : word) = Some W_d50fc.
Proof. vm_refl. Qed.
Lemma D_d50fc : decode_any W_d50fc = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5100 : bv 32 := 0x03613823.
Lemma F_d5100 : fetch_word asegs (0xd50b4 : word) = Some W_d5100.
Proof. vm_refl. Qed.
Lemma D_d5100 : decode_any W_d5100 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5104 : bv 32 := 0x00060413.
Lemma F_d5104 : fetch_word asegs (0xd50b8 : word) = Some W_d5104.
Proof. vm_refl. Qed.
Lemma D_d5104 : decode_any W_d5104 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5108 : bv 32 := 0x00050493.
Lemma F_d5108 : fetch_word asegs (0xd50bc : word) = Some W_d5108.
Proof. vm_refl. Qed.
Lemma D_d5108 : decode_any W_d5108 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d510c : bv 32 := 0x00014517.
Lemma F_d510c : fetch_word asegs (0xd50c0 : word) = Some W_d510c.
Proof. vm_refl. Qed.
Lemma D_d510c : decode_any W_d510c = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5110 : bv 32 := 0xed053a83.
Lemma F_d5110 : fetch_word asegs (0xd50c4 : word) = Some W_d5110.
Proof. vm_refl. Qed.
Lemma D_d5110 : decode_any W_d5110 = Some (Load SZ8 true 21 10 3792, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5114 : bv 32 := 0x000ab503.
Lemma F_d5114 : fetch_word asegs (0xd50c8 : word) = Some W_d5114.
Proof. vm_refl. Qed.
Lemma D_d5114 : decode_any W_d5114 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5118 : bv 32 := 0x02a13423.
Lemma F_d5118 : fetch_word asegs (0xd50cc : word) = Some W_d5118.
Proof. vm_refl. Qed.
Lemma D_d5118 : decode_any W_d5118 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d511c : bv 32 := 0x0284b503.
Lemma F_d511c : fetch_word asegs (0xd50d0 : word) = Some W_d511c.
Proof. vm_refl. Qed.
Lemma D_d511c : decode_any W_d511c = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5120 : bv 32 := 0x0384b603.
Lemma F_d5120 : fetch_word asegs (0xd50d4 : word) = Some W_d5120.
Proof. vm_refl. Qed.
Lemma D_d5120 : decode_any W_d5120 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5124 : bv 32 := 0x40c50b33.
Lemma F_d5124 : fetch_word asegs (0xd50d8 : word) = Some W_d5124.
Proof. vm_refl. Qed.
Lemma D_d5124 : decode_any W_d5124 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5128 : bv 32 := 0x00c546b3.
Lemma F_d5128 : fetch_word asegs (0xd50dc : word) = Some W_d5128.
Proof. vm_refl. Qed.
Lemma D_d5128 : decode_any W_d5128 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d512c : bv 32 := 0x00c13423.
Lemma F_d512c : fetch_word asegs (0xd50e0 : word) = Some W_d512c.
Proof. vm_refl. Qed.
Lemma D_d512c : decode_any W_d512c = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5130 : bv 32 := 0x01613823.
Lemma F_d5130 : fetch_word asegs (0xd50e4 : word) = Some W_d5130.
Proof. vm_refl. Qed.
Lemma D_d5130 : decode_any W_d5130 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5134 : bv 32 := 0x00b13c23.
Lemma F_d5134 : fetch_word asegs (0xd50e8 : word) = Some W_d5134.
Proof. vm_refl. Qed.
Lemma D_d5134 : decode_any W_d5134 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5138 : bv 32 := 0x02813023.
Lemma F_d5138 : fetch_word asegs (0xd50ec : word) = Some W_d5138.
Proof. vm_refl. Qed.
Lemma D_d5138 : decode_any W_d5138 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d513c : bv 32 := 0x008b0b33.
Lemma F_d513c : fetch_word asegs (0xd50f0 : word) = Some W_d513c.
Proof. vm_refl. Qed.
Lemma D_d513c : decode_any W_d513c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5140 : bv 32 := 0x00d03933.
Lemma F_d5140 : fetch_word asegs (0xd50f4 : word) = Some W_d5140.
Proof. vm_refl. Qed.
Lemma D_d5140 : decode_any W_d5140 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5144 : bv 32 := 0x00c50663.
Lemma F_d5144 : fetch_word asegs (0xd50f8 : word) = Some W_d5144.
Proof. vm_refl. Qed.
Lemma D_d5144 : decode_any W_d5144 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5148 : bv 32 := 0x00810993.
Lemma F_d5148 : fetch_word asegs (0xd50fc : word) = Some W_d5148.
Proof. vm_refl. Qed.
Lemma D_d5148 : decode_any W_d5148 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d514c : bv 32 := 0x0080006f.
Lemma F_d514c : fetch_word asegs (0xd5100 : word) = Some W_d514c.
Proof. vm_refl. Qed.
Lemma D_d514c : decode_any W_d514c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5150 : bv 32 := 0x01810993.
Lemma F_d5150 : fetch_word asegs (0xd5104 : word) = Some W_d5150.
Proof. vm_refl. Qed.
Lemma D_d5150 : decode_any W_d5150 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5154 : bv 32 := 0x0784a503.
Lemma F_d5154 : fetch_word asegs (0xd5108 : word) = Some W_d5154.
Proof. vm_refl. Qed.
Lemma D_d5154 : decode_any W_d5154 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5158 : bv 32 := 0x00190913.
Lemma F_d5158 : fetch_word asegs (0xd510c : word) = Some W_d5158.
Proof. vm_refl. Qed.
Lemma D_d5158 : decode_any W_d5158 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d515c : bv 32 := 0x04200893.
Lemma F_d515c : fetch_word asegs (0xd5110 : word) = Some W_d515c.
Proof. vm_refl. Qed.
Lemma D_d515c : decode_any W_d515c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5160 : bv 32 := 0x00098593.
Lemma F_d5160 : fetch_word asegs (0xd5114 : word) = Some W_d5160.
Proof. vm_refl. Qed.
Lemma D_d5160 : decode_any W_d5160 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5164 : bv 32 := 0x00090613.
Lemma F_d5164 : fetch_word asegs (0xd5118 : word) = Some W_d5164.
Proof. vm_refl. Qed.
Lemma D_d5164 : decode_any W_d5164 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5168 : bv 32 := 0x00000073.
Lemma F_d5168 : fetch_word asegs (0xd511c : word) = Some W_d5168.
Proof. vm_refl. Qed.

Lemma E_d5168 : is_ecall W_d5168 = true.
Proof. reflexivity. Qed.

Definition W_d516c : bv 32 := 0xfadf90ef.
Lemma F_d516c : fetch_word asegs (0xd5120 : word) = Some W_d516c.
Proof. vm_refl. Qed.
Lemma D_d516c : decode_any W_d516c = Some (Jal 1 2072492, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5170 : bv 32 := 0x09651863.
Lemma F_d5170 : fetch_word asegs (0xd5124 : word) = Some W_d5170.
Proof. vm_refl. Qed.
Lemma D_d5170 : decode_any W_d5170 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5174 : bv 32 := 0x0584b503.
Lemma F_d5174 : fetch_word asegs (0xd5128 : word) = Some W_d5174.
Proof. vm_refl. Qed.
Lemma D_d5174 : decode_any W_d5174 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5178 : bv 32 := 0x0604b583.
Lemma F_d5178 : fetch_word asegs (0xd512c : word) = Some W_d5178.
Proof. vm_refl. Qed.
Lemma D_d5178 : decode_any W_d5178 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d517c : bv 32 := 0x00b505b3.
Lemma F_d517c : fetch_word asegs (0xd5130 : word) = Some W_d517c.
Proof. vm_refl. Qed.
Lemma D_d517c : decode_any W_d517c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5180 : bv 32 := 0x02b4b023.
Lemma F_d5180 : fetch_word asegs (0xd5134 : word) = Some W_d5180.
Proof. vm_refl. Qed.
Lemma D_d5180 : decode_any W_d5180 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5184 : bv 32 := 0x02a4b423.
Lemma F_d5184 : fetch_word asegs (0xd5138 : word) = Some W_d5184.
Proof. vm_refl. Qed.
Lemma D_d5184 : decode_any W_d5184 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5188 : bv 32 := 0x02a4bc23.
Lemma F_d5188 : fetch_word asegs (0xd513c : word) = Some W_d5188.
Proof. vm_refl. Qed.
Lemma D_d5188 : decode_any W_d5188 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d518c : bv 32 := 0x00040513.
Lemma F_d518c : fetch_word asegs (0xd5140 : word) = Some W_d518c.
Proof. vm_refl. Qed.
Lemma D_d518c : decode_any W_d518c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5190 : bv 32 := 0x000ab583.
Lemma F_d5190 : fetch_word asegs (0xd5144 : word) = Some W_d5190.
Proof. vm_refl. Qed.
Lemma D_d5190 : decode_any W_d5190 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5194 : bv 32 := 0x02813603.
Lemma F_d5194 : fetch_word asegs (0xd5148 : word) = Some W_d5194.
Proof. vm_refl. Qed.
Lemma D_d5194 : decode_any W_d5194 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5198 : bv 32 := 0x0cc59a63.
Lemma F_d5198 : fetch_word asegs (0xd514c : word) = Some W_d5198.
Proof. vm_refl. Qed.
Lemma D_d5198 : decode_any W_d5198 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_d519c : bv 32 := 0x06813083.
Lemma F_d519c : fetch_word asegs (0xd5150 : word) = Some W_d519c.
Proof. vm_refl. Qed.
Lemma D_d519c : decode_any W_d519c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51a0 : bv 32 := 0x06013403.
Lemma F_d51a0 : fetch_word asegs (0xd5154 : word) = Some W_d51a0.
Proof. vm_refl. Qed.
Lemma D_d51a0 : decode_any W_d51a0 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51a4 : bv 32 := 0x05813483.
Lemma F_d51a4 : fetch_word asegs (0xd5158 : word) = Some W_d51a4.
Proof. vm_refl. Qed.
Lemma D_d51a4 : decode_any W_d51a4 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51a8 : bv 32 := 0x05013903.
Lemma F_d51a8 : fetch_word asegs (0xd515c : word) = Some W_d51a8.
Proof. vm_refl. Qed.
Lemma D_d51a8 : decode_any W_d51a8 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51ac : bv 32 := 0x04813983.
Lemma F_d51ac : fetch_word asegs (0xd5160 : word) = Some W_d51ac.
Proof. vm_refl. Qed.
Lemma D_d51ac : decode_any W_d51ac = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51b0 : bv 32 := 0x04013a03.
Lemma F_d51b0 : fetch_word asegs (0xd5164 : word) = Some W_d51b0.
Proof. vm_refl. Qed.
Lemma D_d51b0 : decode_any W_d51b0 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51b4 : bv 32 := 0x03813a83.
Lemma F_d51b4 : fetch_word asegs (0xd5168 : word) = Some W_d51b4.
Proof. vm_refl. Qed.
Lemma D_d51b4 : decode_any W_d51b4 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51b8 : bv 32 := 0x03013b03.
Lemma F_d51b8 : fetch_word asegs (0xd516c : word) = Some W_d51b8.
Proof. vm_refl. Qed.
Lemma D_d51b8 : decode_any W_d51b8 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51bc : bv 32 := 0x07010113.
Lemma F_d51bc : fetch_word asegs (0xd5170 : word) = Some W_d51bc.
Proof. vm_refl. Qed.
Lemma D_d51bc : decode_any W_d51bc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51c0 : bv 32 := 0x00008067.
Lemma F_d51c0 : fetch_word asegs (0xd5174 : word) = Some W_d51c0.
Proof. vm_refl. Qed.
Lemma D_d51c0 : decode_any W_d51c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51c4 : bv 32 := 0x00800713.
Lemma F_d51c4 : fetch_word asegs (0xd5178 : word) = Some W_d51c4.
Proof. vm_refl. Qed.
Lemma D_d51c4 : decode_any W_d51c4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51c8 : bv 32 := 0x000a0593.
Lemma F_d51c8 : fetch_word asegs (0xd517c : word) = Some W_d51c8.
Proof. vm_refl. Qed.
Lemma D_d51c8 : decode_any W_d51c8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51cc : bv 32 := 0x00e98733.
Lemma F_d51cc : fetch_word asegs (0xd5180 : word) = Some W_d51cc.
Proof. vm_refl. Qed.
Lemma D_d51cc : decode_any W_d51cc = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51d0 : bv 32 := 0x00073783.
Lemma F_d51d0 : fetch_word asegs (0xd5184 : word) = Some W_d51d0.
Proof. vm_refl. Qed.
Lemma D_d51d0 : decode_any W_d51d0 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51d4 : bv 32 := 0x40ab0b33.
Lemma F_d51d4 : fetch_word asegs (0xd5188 : word) = Some W_d51d4.
Proof. vm_refl. Qed.
Lemma D_d51d4 : decode_any W_d51d4 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51d8 : bv 32 := 0x0784a503.
Lemma F_d51d8 : fetch_word asegs (0xd518c : word) = Some W_d51d8.
Proof. vm_refl. Qed.
Lemma D_d51d8 : decode_any W_d51d8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51dc : bv 32 := 0x40c9093b.
Lemma F_d51dc : fetch_word asegs (0xd5190 : word) = Some W_d51dc.
Proof. vm_refl. Qed.
Lemma D_d51dc : decode_any W_d51dc = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51e0 : bv 32 := 0x40d787b3.
Lemma F_d51e0 : fetch_word asegs (0xd5194 : word) = Some W_d51e0.
Proof. vm_refl. Qed.
Lemma D_d51e0 : decode_any W_d51e0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51e4 : bv 32 := 0x00f73023.
Lemma F_d51e4 : fetch_word asegs (0xd5198 : word) = Some W_d51e4.
Proof. vm_refl. Qed.
Lemma D_d51e4 : decode_any W_d51e4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51e8 : bv 32 := 0x04200893.
Lemma F_d51e8 : fetch_word asegs (0xd519c : word) = Some W_d51e8.
Proof. vm_refl. Qed.
Lemma D_d51e8 : decode_any W_d51e8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51ec : bv 32 := 0x00090613.
Lemma F_d51ec : fetch_word asegs (0xd51a0 : word) = Some W_d51ec.
Proof. vm_refl. Qed.
Lemma D_d51ec : decode_any W_d51ec = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51f0 : bv 32 := 0x00000073.
Lemma F_d51f0 : fetch_word asegs (0xd51a4 : word) = Some W_d51f0.
Proof. vm_refl. Qed.

Lemma E_d51f0 : is_ecall W_d51f0 = true.
Proof. reflexivity. Qed.

Definition W_d51f4 : bv 32 := 0xf25f90ef.
Lemma F_d51f4 : fetch_word asegs (0xd51a8 : word) = Some W_d51f4.
Proof. vm_refl. Qed.
Lemma D_d51f4 : decode_any W_d51f4 = Some (Jal 1 2072356, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51f8 : bv 32 := 0x000a0993.
Lemma F_d51f8 : fetch_word asegs (0xd51ac : word) = Some W_d51f8.
Proof. vm_refl. Qed.
Lemma D_d51f8 : decode_any W_d51f8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d51fc : bv 32 := 0xf7650ce3.
Lemma F_d51fc : fetch_word asegs (0xd51b0 : word) = Some W_d51fc.
Proof. vm_refl. Qed.
Lemma D_d51fc : decode_any W_d51fc = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5200 : bv 32 := 0x02054c63.
Lemma F_d5200 : fetch_word asegs (0xd51b4 : word) = Some W_d5200.
Proof. vm_refl. Qed.
Lemma D_d5200 : decode_any W_d5200 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5204 : bv 32 := 0x0089b583.
Lemma F_d5204 : fetch_word asegs (0xd51b8 : word) = Some W_d5204.
Proof. vm_refl. Qed.
Lemma D_d5204 : decode_any W_d5204 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5208 : bv 32 := 0x00a5b633.
Lemma F_d5208 : fetch_word asegs (0xd51bc : word) = Some W_d5208.
Proof. vm_refl. Qed.
Lemma D_d5208 : decode_any W_d5208 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d520c : bv 32 := 0x00461a13.
Lemma F_d520c : fetch_word asegs (0xd51c0 : word) = Some W_d520c.
Proof. vm_refl. Qed.
Lemma D_d520c : decode_any W_d520c = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5210 : bv 32 := 0x01498a33.
Lemma F_d5210 : fetch_word asegs (0xd51c4 : word) = Some W_d5210.
Proof. vm_refl. Qed.
Lemma D_d5210 : decode_any W_d5210 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5214 : bv 32 := 0x000a3703.
Lemma F_d5214 : fetch_word asegs (0xd51c8 : word) = Some W_d5214.
Proof. vm_refl. Qed.
Lemma D_d5214 : decode_any W_d5214 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5218 : bv 32 := 0x40c006b3.
Lemma F_d5218 : fetch_word asegs (0xd51cc : word) = Some W_d5218.
Proof. vm_refl. Qed.
Lemma D_d5218 : decode_any W_d5218 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d521c : bv 32 := 0x00b6f6b3.
Lemma F_d521c : fetch_word asegs (0xd51d0 : word) = Some W_d521c.
Proof. vm_refl. Qed.
Lemma D_d521c : decode_any W_d521c = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5220 : bv 32 := 0x40d506b3.
Lemma F_d5220 : fetch_word asegs (0xd51d4 : word) = Some W_d5220.
Proof. vm_refl. Qed.
Lemma D_d5220 : decode_any W_d5220 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5224 : bv 32 := 0x00d70733.
Lemma F_d5224 : fetch_word asegs (0xd51d8 : word) = Some W_d5224.
Proof. vm_refl. Qed.
Lemma D_d5224 : decode_any W_d5224 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5228 : bv 32 := 0x00ea3023.
Lemma F_d5228 : fetch_word asegs (0xd51dc : word) = Some W_d5228.
Proof. vm_refl. Qed.
Lemma D_d5228 : decode_any W_d5228 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d522c : bv 32 := 0xf8a5fce3.
Lemma F_d522c : fetch_word asegs (0xd51e0 : word) = Some W_d522c.
Proof. vm_refl. Qed.
Lemma D_d522c : decode_any W_d522c = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5230 : bv 32 := 0x01800713.
Lemma F_d5230 : fetch_word asegs (0xd51e4 : word) = Some W_d5230.
Proof. vm_refl. Qed.
Lemma D_d5230 : decode_any W_d5230 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5234 : bv 32 := 0xf95ff06f.
Lemma F_d5234 : fetch_word asegs (0xd51e8 : word) = Some W_d5234.
Proof. vm_refl. Qed.
Lemma D_d5234 : decode_any W_d5234 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56c0 : bv 32 := 0xff010113.
Lemma F_d56c0 : fetch_word asegs (0xd5674 : word) = Some W_d56c0.
Proof. vm_refl. Qed.
Lemma D_d56c0 : decode_any W_d56c0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56c4 : bv 32 := 0x00113423.
Lemma F_d56c4 : fetch_word asegs (0xd5678 : word) = Some W_d56c4.
Proof. vm_refl. Qed.
Lemma D_d56c4 : decode_any W_d56c4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56c8 : bv 32 := 0x00813023.
Lemma F_d56c8 : fetch_word asegs (0xd567c : word) = Some W_d56c8.
Proof. vm_refl. Qed.
Lemma D_d56c8 : decode_any W_d56c8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56cc : bv 32 := 0x5fc000ef.
Lemma F_d56cc : fetch_word asegs (0xd5680 : word) = Some W_d56cc.
Proof. vm_refl. Qed.
Lemma D_d56cc : decode_any W_d56cc = Some (Jal 1 1532, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56d0 : bv 32 := 0x00053403.
Lemma F_d56d0 : fetch_word asegs (0xd5684 : word) = Some W_d56d0.
Proof. vm_refl. Qed.
Lemma D_d56d0 : decode_any W_d56d0 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56d4 : bv 32 := 0x12041663.
Lemma F_d56d4 : fetch_word asegs (0xd5688 : word) = Some W_d56d4.
Proof. vm_refl. Qed.
Lemma D_d56d4 : decode_any W_d56d4 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56d8 : bv 32 := 0x00018517.
Lemma F_d56d8 : fetch_word asegs (0xd568c : word) = Some W_d56d8.
Proof. vm_refl. Qed.
Lemma D_d56d8 : decode_any W_d56d8 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56dc : bv 32 := 0x97c53403.
Lemma F_d56dc : fetch_word asegs (0xd5690 : word) = Some W_d56dc.
Proof. vm_refl. Qed.
Lemma D_d56dc : decode_any W_d56dc = Some (Load SZ8 true 8 10 2428, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56e0 : bv 32 := 0x04040a63.
Lemma F_d56e0 : fetch_word asegs (0xd5694 : word) = Some W_d56e0.
Proof. vm_refl. Qed.
Lemma D_d56e0 : decode_any W_d56e0 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56e4 : bv 32 := 0x08c42503.
Lemma F_d56e4 : fetch_word asegs (0xd5698 : word) = Some W_d56e4.
Proof. vm_refl. Qed.
Lemma D_d56e4 : decode_any W_d56e4 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56e8 : bv 32 := 0x00054663.
Lemma F_d56e8 : fetch_word asegs (0xd569c : word) = Some W_d56e8.
Proof. vm_refl. Qed.
Lemma D_d56e8 : decode_any W_d56e8 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56f4 : bv 32 := 0x02843503.
Lemma F_d56f4 : fetch_word asegs (0xd56a8 : word) = Some W_d56f4.
Proof. vm_refl. Qed.
Lemma D_d56f4 : decode_any W_d56f4 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56f8 : bv 32 := 0x03843583.
Lemma F_d56f8 : fetch_word asegs (0xd56ac : word) = Some W_d56f8.
Proof. vm_refl. Qed.
Lemma D_d56f8 : decode_any W_d56f8 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d56fc : bv 32 := 0x00b50c63.
Lemma F_d56fc : fetch_word asegs (0xd56b0 : word) = Some W_d56fc.
Proof. vm_refl. Qed.
Lemma D_d56fc : decode_any W_d56fc = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5714 : bv 32 := 0x00843503.
Lemma F_d5714 : fetch_word asegs (0xd56c8 : word) = Some W_d5714.
Proof. vm_refl. Qed.
Lemma D_d5714 : decode_any W_d5714 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5718 : bv 32 := 0x01043583.
Lemma F_d5718 : fetch_word asegs (0xd56cc : word) = Some W_d5718.
Proof. vm_refl. Qed.
Lemma D_d5718 : decode_any W_d5718 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d571c : bv 32 := 0x00b50c63.
Lemma F_d571c : fetch_word asegs (0xd56d0 : word) = Some W_d571c.
Proof. vm_refl. Qed.
Lemma D_d571c : decode_any W_d571c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5734 : bv 32 := 0x00018517.
Lemma F_d5734 : fetch_word asegs (0xd56e8 : word) = Some W_d5734.
Proof. vm_refl. Qed.
Lemma D_d5734 : decode_any W_d5734 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5738 : bv 32 := 0x83053403.
Lemma F_d5738 : fetch_word asegs (0xd56ec : word) = Some W_d5738.
Proof. vm_refl. Qed.
Lemma D_d5738 : decode_any W_d5738 = Some (Load SZ8 true 8 10 2096, 4%Z).
Proof. vm_refl. Qed.

Definition W_d573c : bv 32 := 0x04040a63.
Lemma F_d573c : fetch_word asegs (0xd56f0 : word) = Some W_d573c.
Proof. vm_refl. Qed.
Lemma D_d573c : decode_any W_d573c = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5740 : bv 32 := 0x08c42503.
Lemma F_d5740 : fetch_word asegs (0xd56f4 : word) = Some W_d5740.
Proof. vm_refl. Qed.
Lemma D_d5740 : decode_any W_d5740 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5744 : bv 32 := 0x00054663.
Lemma F_d5744 : fetch_word asegs (0xd56f8 : word) = Some W_d5744.
Proof. vm_refl. Qed.
Lemma D_d5744 : decode_any W_d5744 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5750 : bv 32 := 0x02843503.
Lemma F_d5750 : fetch_word asegs (0xd5704 : word) = Some W_d5750.
Proof. vm_refl. Qed.
Lemma D_d5750 : decode_any W_d5750 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5754 : bv 32 := 0x03843583.
Lemma F_d5754 : fetch_word asegs (0xd5708 : word) = Some W_d5754.
Proof. vm_refl. Qed.
Lemma D_d5754 : decode_any W_d5754 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5758 : bv 32 := 0x00b50c63.
Lemma F_d5758 : fetch_word asegs (0xd570c : word) = Some W_d5758.
Proof. vm_refl. Qed.
Lemma D_d5758 : decode_any W_d5758 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d575c : bv 32 := 0x04843683.
Lemma F_d575c : fetch_word asegs (0xd5710 : word) = Some W_d575c.
Proof. vm_refl. Qed.
Lemma D_d575c : decode_any W_d575c = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5760 : bv 32 := 0x00040513.
Lemma F_d5760 : fetch_word asegs (0xd5714 : word) = Some W_d5760.
Proof. vm_refl. Qed.
Lemma D_d5760 : decode_any W_d5760 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5764 : bv 32 := 0x00000593.
Lemma F_d5764 : fetch_word asegs (0xd5718 : word) = Some W_d5764.
Proof. vm_refl. Qed.
Lemma D_d5764 : decode_any W_d5764 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5768 : bv 32 := 0x00000613.
Lemma F_d5768 : fetch_word asegs (0xd571c : word) = Some W_d5768.
Proof. vm_refl. Qed.
Lemma D_d5768 : decode_any W_d5768 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d576c : bv 32 := 0x000680e7.
Lemma F_d576c : fetch_word asegs (0xd5720 : word) = Some W_d576c.
Proof. vm_refl. Qed.
Lemma D_d576c : decode_any W_d576c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5770 : bv 32 := 0x00843503.
Lemma F_d5770 : fetch_word asegs (0xd5724 : word) = Some W_d5770.
Proof. vm_refl. Qed.
Lemma D_d5770 : decode_any W_d5770 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5774 : bv 32 := 0x01043583.
Lemma F_d5774 : fetch_word asegs (0xd5728 : word) = Some W_d5774.
Proof. vm_refl. Qed.
Lemma D_d5774 : decode_any W_d5774 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5778 : bv 32 := 0x00b50c63.
Lemma F_d5778 : fetch_word asegs (0xd572c : word) = Some W_d5778.
Proof. vm_refl. Qed.
Lemma D_d5778 : decode_any W_d5778 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5790 : bv 32 := 0x00017517.
Lemma F_d5790 : fetch_word asegs (0xd5744 : word) = Some W_d5790.
Proof. vm_refl. Qed.
Lemma D_d5790 : decode_any W_d5790 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5794 : bv 32 := 0x6e453403.
Lemma F_d5794 : fetch_word asegs (0xd5748 : word) = Some W_d5794.
Proof. vm_refl. Qed.
Lemma D_d5794 : decode_any W_d5794 = Some (Load SZ8 true 8 10 1764, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5798 : bv 32 := 0x0a040e63.
Lemma F_d5798 : fetch_word asegs (0xd574c : word) = Some W_d5798.
Proof. vm_refl. Qed.
Lemma D_d5798 : decode_any W_d5798 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_d579c : bv 32 := 0x08c42503.
Lemma F_d579c : fetch_word asegs (0xd5750 : word) = Some W_d579c.
Proof. vm_refl. Qed.
Lemma D_d579c : decode_any W_d579c = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_d57a0 : bv 32 := 0x00054663.
Lemma F_d57a0 : fetch_word asegs (0xd5754 : word) = Some W_d57a0.
Proof. vm_refl. Qed.
Lemma D_d57a0 : decode_any W_d57a0 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d57ac : bv 32 := 0x02843503.
Lemma F_d57ac : fetch_word asegs (0xd5760 : word) = Some W_d57ac.
Proof. vm_refl. Qed.
Lemma D_d57ac : decode_any W_d57ac = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d57b0 : bv 32 := 0x03843583.
Lemma F_d57b0 : fetch_word asegs (0xd5764 : word) = Some W_d57b0.
Proof. vm_refl. Qed.
Lemma D_d57b0 : decode_any W_d57b0 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d57b4 : bv 32 := 0x00b50c63.
Lemma F_d57b4 : fetch_word asegs (0xd5768 : word) = Some W_d57b4.
Proof. vm_refl. Qed.
Lemma D_d57b4 : decode_any W_d57b4 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d57cc : bv 32 := 0x00843503.
Lemma F_d57cc : fetch_word asegs (0xd5780 : word) = Some W_d57cc.
Proof. vm_refl. Qed.
Lemma D_d57cc : decode_any W_d57cc = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d57d0 : bv 32 := 0x01043583.
Lemma F_d57d0 : fetch_word asegs (0xd5784 : word) = Some W_d57d0.
Proof. vm_refl. Qed.
Lemma D_d57d0 : decode_any W_d57d0 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d57d4 : bv 32 := 0x08b50063.
Lemma F_d57d4 : fetch_word asegs (0xd5788 : word) = Some W_d57d4.
Proof. vm_refl. Qed.
Lemma D_d57d4 : decode_any W_d57d4 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5854 : bv 32 := 0x00813083.
Lemma F_d5854 : fetch_word asegs (0xd5808 : word) = Some W_d5854.
Proof. vm_refl. Qed.
Lemma D_d5854 : decode_any W_d5854 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5858 : bv 32 := 0x00013403.
Lemma F_d5858 : fetch_word asegs (0xd580c : word) = Some W_d5858.
Proof. vm_refl. Qed.
Lemma D_d5858 : decode_any W_d5858 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d585c : bv 32 := 0x01010113.
Lemma F_d585c : fetch_word asegs (0xd5810 : word) = Some W_d585c.
Proof. vm_refl. Qed.
Lemma D_d585c : decode_any W_d585c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5860 : bv 32 := 0x00008067.
Lemma F_d5860 : fetch_word asegs (0xd5814 : word) = Some W_d5860.
Proof. vm_refl. Qed.
Lemma D_d5860 : decode_any W_d5860 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5cc8 : bv 32 := 0xff010113.
Lemma F_d5cc8 : fetch_word asegs (0xd5c7c : word) = Some W_d5cc8.
Proof. vm_refl. Qed.
Lemma D_d5cc8 : decode_any W_d5cc8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5ccc : bv 32 := 0x00113423.
Lemma F_d5ccc : fetch_word asegs (0xd5c80 : word) = Some W_d5ccc.
Proof. vm_refl. Qed.
Lemma D_d5ccc : decode_any W_d5ccc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5cd0 : bv 32 := 0x00813023.
Lemma F_d5cd0 : fetch_word asegs (0xd5c84 : word) = Some W_d5cd0.
Proof. vm_refl. Qed.
Lemma D_d5cd0 : decode_any W_d5cd0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5cd4 : bv 32 := 0x00570517.
Lemma F_d5cd4 : fetch_word asegs (0xd5c88 : word) = Some W_d5cd4.
Proof. vm_refl. Qed.
Lemma D_d5cd4 : decode_any W_d5cd4 = Some (Auipc 10 1392, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5cd8 : bv 32 := 0x00050413.
Lemma F_d5cd8 : fetch_word asegs (0xd5c8c : word) = Some W_d5cd8.
Proof. vm_refl. Qed.
Lemma D_d5cd8 : decode_any W_d5cd8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5cdc : bv 32 := 0x00040513.
Lemma F_d5cdc : fetch_word asegs (0xd5c90 : word) = Some W_d5cdc.
Proof. vm_refl. Qed.
Lemma D_d5cdc : decode_any W_d5cdc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5ce0 : bv 32 := 0x66d080ef.
Lemma F_d5ce0 : fetch_word asegs (0xd5c94 : word) = Some W_d5ce0.
Proof. vm_refl. Qed.
Lemma D_d5ce0 : decode_any W_d5ce0 = Some (Jal 1 36460, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5ce4 : bv 32 := 0x00840513.
Lemma F_d5ce4 : fetch_word asegs (0xd5c98 : word) = Some W_d5ce4.
Proof. vm_refl. Qed.
Lemma D_d5ce4 : decode_any W_d5ce4 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5ce8 : bv 32 := 0x00813083.
Lemma F_d5ce8 : fetch_word asegs (0xd5c9c : word) = Some W_d5ce8.
Proof. vm_refl. Qed.
Lemma D_d5ce8 : decode_any W_d5ce8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5cec : bv 32 := 0x00013403.
Lemma F_d5cec : fetch_word asegs (0xd5ca0 : word) = Some W_d5cec.
Proof. vm_refl. Qed.
Lemma D_d5cec : decode_any W_d5cec = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5cf0 : bv 32 := 0x01010113.
Lemma F_d5cf0 : fetch_word asegs (0xd5ca4 : word) = Some W_d5cf0.
Proof. vm_refl. Qed.
Lemma D_d5cf0 : decode_any W_d5cf0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5cf4 : bv 32 := 0x00008067.
Lemma F_d5cf4 : fetch_word asegs (0xd5ca8 : word) = Some W_d5cf4.
Proof. vm_refl. Qed.
Lemma D_d5cf4 : decode_any W_d5cf4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
