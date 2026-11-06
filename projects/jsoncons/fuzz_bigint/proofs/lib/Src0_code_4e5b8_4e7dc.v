(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_4e5b8 : bv 32 := 0xff010113.
Lemma F_4e5b8 : fetch_word Plain.M.loaded_segments (0x4e5b8 : word) = Some W_4e5b8.
Proof. vm_refl. Qed.
Lemma D_4e5b8 : decode_any W_4e5b8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5bc : bv 32 := 0x00113423.
Lemma F_4e5bc : fetch_word Plain.M.loaded_segments (0x4e5bc : word) = Some W_4e5bc.
Proof. vm_refl. Qed.
Lemma D_4e5bc : decode_any W_4e5bc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5c0 : bv 32 := 0x00813023.
Lemma F_4e5c0 : fetch_word Plain.M.loaded_segments (0x4e5c0 : word) = Some W_4e5c0.
Proof. vm_refl. Qed.
Lemma D_4e5c0 : decode_any W_4e5c0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5c4 : bv 32 := 0x00042517.
Lemma F_4e5c4 : fetch_word Plain.M.loaded_segments (0x4e5c4 : word) = Some W_4e5c4.
Proof. vm_refl. Qed.
Lemma D_4e5c4 : decode_any W_4e5c4 = Some (Auipc 10 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5c8 : bv 32 := 0x52c50413.
Lemma F_4e5c8 : fetch_word Plain.M.loaded_segments (0x4e5c8 : word) = Some W_4e5c8.
Proof. vm_refl. Qed.
Lemma D_4e5c8 : decode_any W_4e5c8 = Some (OpImm ALU_ADD 8 10 1324, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5cc : bv 32 := 0x00040513.
Lemma F_4e5cc : fetch_word Plain.M.loaded_segments (0x4e5cc : word) = Some W_4e5cc.
Proof. vm_refl. Qed.
Lemma D_4e5cc : decode_any W_4e5cc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5d0 : bv 32 := 0x4590a0ef.
Lemma F_4e5d0 : fetch_word Plain.M.loaded_segments (0x4e5d0 : word) = Some W_4e5d0.
Proof. vm_refl. Qed.
Lemma D_4e5d0 : decode_any W_4e5d0 = Some (Jal 1 44120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5d4 : bv 32 := 0x00840513.
Lemma F_4e5d4 : fetch_word Plain.M.loaded_segments (0x4e5d4 : word) = Some W_4e5d4.
Proof. vm_refl. Qed.
Lemma D_4e5d4 : decode_any W_4e5d4 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5d8 : bv 32 := 0x00813083.
Lemma F_4e5d8 : fetch_word Plain.M.loaded_segments (0x4e5d8 : word) = Some W_4e5d8.
Proof. vm_refl. Qed.
Lemma D_4e5d8 : decode_any W_4e5d8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5dc : bv 32 := 0x00013403.
Lemma F_4e5dc : fetch_word Plain.M.loaded_segments (0x4e5dc : word) = Some W_4e5dc.
Proof. vm_refl. Qed.
Lemma D_4e5dc : decode_any W_4e5dc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5e0 : bv 32 := 0x01010113.
Lemma F_4e5e0 : fetch_word Plain.M.loaded_segments (0x4e5e0 : word) = Some W_4e5e0.
Proof. vm_refl. Qed.
Lemma D_4e5e0 : decode_any W_4e5e0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e5e4 : bv 32 := 0x00008067.
Lemma F_4e5e4 : fetch_word Plain.M.loaded_segments (0x4e5e4 : word) = Some W_4e5e4.
Proof. vm_refl. Qed.
Lemma D_4e5e4 : decode_any W_4e5e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e654 : bv 32 := 0x00008067.
Lemma F_4e654 : fetch_word Plain.M.loaded_segments (0x4e654 : word) = Some W_4e654.
Proof. vm_refl. Qed.
Lemma D_4e654 : decode_any W_4e654 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e684 : bv 32 := 0xf9010113.
Lemma F_4e684 : fetch_word Plain.M.loaded_segments (0x4e684 : word) = Some W_4e684.
Proof. vm_refl. Qed.
Lemma D_4e684 : decode_any W_4e684 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e688 : bv 32 := 0x06113423.
Lemma F_4e688 : fetch_word Plain.M.loaded_segments (0x4e688 : word) = Some W_4e688.
Proof. vm_refl. Qed.
Lemma D_4e688 : decode_any W_4e688 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e68c : bv 32 := 0x06813023.
Lemma F_4e68c : fetch_word Plain.M.loaded_segments (0x4e68c : word) = Some W_4e68c.
Proof. vm_refl. Qed.
Lemma D_4e68c : decode_any W_4e68c = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e690 : bv 32 := 0x04913c23.
Lemma F_4e690 : fetch_word Plain.M.loaded_segments (0x4e690 : word) = Some W_4e690.
Proof. vm_refl. Qed.
Lemma D_4e690 : decode_any W_4e690 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e694 : bv 32 := 0x05213823.
Lemma F_4e694 : fetch_word Plain.M.loaded_segments (0x4e694 : word) = Some W_4e694.
Proof. vm_refl. Qed.
Lemma D_4e694 : decode_any W_4e694 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e698 : bv 32 := 0x05313423.
Lemma F_4e698 : fetch_word Plain.M.loaded_segments (0x4e698 : word) = Some W_4e698.
Proof. vm_refl. Qed.
Lemma D_4e698 : decode_any W_4e698 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e69c : bv 32 := 0x05413023.
Lemma F_4e69c : fetch_word Plain.M.loaded_segments (0x4e69c : word) = Some W_4e69c.
Proof. vm_refl. Qed.
Lemma D_4e69c : decode_any W_4e69c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6a0 : bv 32 := 0x03513c23.
Lemma F_4e6a0 : fetch_word Plain.M.loaded_segments (0x4e6a0 : word) = Some W_4e6a0.
Proof. vm_refl. Qed.
Lemma D_4e6a0 : decode_any W_4e6a0 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6a4 : bv 32 := 0x03613823.
Lemma F_4e6a4 : fetch_word Plain.M.loaded_segments (0x4e6a4 : word) = Some W_4e6a4.
Proof. vm_refl. Qed.
Lemma D_4e6a4 : decode_any W_4e6a4 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6a8 : bv 32 := 0x00060413.
Lemma F_4e6a8 : fetch_word Plain.M.loaded_segments (0x4e6a8 : word) = Some W_4e6a8.
Proof. vm_refl. Qed.
Lemma D_4e6a8 : decode_any W_4e6a8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6ac : bv 32 := 0x00050493.
Lemma F_4e6ac : fetch_word Plain.M.loaded_segments (0x4e6ac : word) = Some W_4e6ac.
Proof. vm_refl. Qed.
Lemma D_4e6ac : decode_any W_4e6ac = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6b0 : bv 32 := 0x00010517.
Lemma F_4e6b0 : fetch_word Plain.M.loaded_segments (0x4e6b0 : word) = Some W_4e6b0.
Proof. vm_refl. Qed.
Lemma D_4e6b0 : decode_any W_4e6b0 = Some (Auipc 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6b4 : bv 32 := 0xf4053a83.
Lemma F_4e6b4 : fetch_word Plain.M.loaded_segments (0x4e6b4 : word) = Some W_4e6b4.
Proof. vm_refl. Qed.
Lemma D_4e6b4 : decode_any W_4e6b4 = Some (Load SZ8 true 21 10 3904, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6b8 : bv 32 := 0x000ab503.
Lemma F_4e6b8 : fetch_word Plain.M.loaded_segments (0x4e6b8 : word) = Some W_4e6b8.
Proof. vm_refl. Qed.
Lemma D_4e6b8 : decode_any W_4e6b8 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6bc : bv 32 := 0x02a13423.
Lemma F_4e6bc : fetch_word Plain.M.loaded_segments (0x4e6bc : word) = Some W_4e6bc.
Proof. vm_refl. Qed.
Lemma D_4e6bc : decode_any W_4e6bc = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6c0 : bv 32 := 0x0284b503.
Lemma F_4e6c0 : fetch_word Plain.M.loaded_segments (0x4e6c0 : word) = Some W_4e6c0.
Proof. vm_refl. Qed.
Lemma D_4e6c0 : decode_any W_4e6c0 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6c4 : bv 32 := 0x0384b603.
Lemma F_4e6c4 : fetch_word Plain.M.loaded_segments (0x4e6c4 : word) = Some W_4e6c4.
Proof. vm_refl. Qed.
Lemma D_4e6c4 : decode_any W_4e6c4 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6c8 : bv 32 := 0x40c50b33.
Lemma F_4e6c8 : fetch_word Plain.M.loaded_segments (0x4e6c8 : word) = Some W_4e6c8.
Proof. vm_refl. Qed.
Lemma D_4e6c8 : decode_any W_4e6c8 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6cc : bv 32 := 0x00c546b3.
Lemma F_4e6cc : fetch_word Plain.M.loaded_segments (0x4e6cc : word) = Some W_4e6cc.
Proof. vm_refl. Qed.
Lemma D_4e6cc : decode_any W_4e6cc = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6d0 : bv 32 := 0x00c13423.
Lemma F_4e6d0 : fetch_word Plain.M.loaded_segments (0x4e6d0 : word) = Some W_4e6d0.
Proof. vm_refl. Qed.
Lemma D_4e6d0 : decode_any W_4e6d0 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6d4 : bv 32 := 0x01613823.
Lemma F_4e6d4 : fetch_word Plain.M.loaded_segments (0x4e6d4 : word) = Some W_4e6d4.
Proof. vm_refl. Qed.
Lemma D_4e6d4 : decode_any W_4e6d4 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6d8 : bv 32 := 0x00b13c23.
Lemma F_4e6d8 : fetch_word Plain.M.loaded_segments (0x4e6d8 : word) = Some W_4e6d8.
Proof. vm_refl. Qed.
Lemma D_4e6d8 : decode_any W_4e6d8 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6dc : bv 32 := 0x02813023.
Lemma F_4e6dc : fetch_word Plain.M.loaded_segments (0x4e6dc : word) = Some W_4e6dc.
Proof. vm_refl. Qed.
Lemma D_4e6dc : decode_any W_4e6dc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6e0 : bv 32 := 0x008b0b33.
Lemma F_4e6e0 : fetch_word Plain.M.loaded_segments (0x4e6e0 : word) = Some W_4e6e0.
Proof. vm_refl. Qed.
Lemma D_4e6e0 : decode_any W_4e6e0 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6e4 : bv 32 := 0x00d03933.
Lemma F_4e6e4 : fetch_word Plain.M.loaded_segments (0x4e6e4 : word) = Some W_4e6e4.
Proof. vm_refl. Qed.
Lemma D_4e6e4 : decode_any W_4e6e4 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6e8 : bv 32 := 0x00c50663.
Lemma F_4e6e8 : fetch_word Plain.M.loaded_segments (0x4e6e8 : word) = Some W_4e6e8.
Proof. vm_refl. Qed.
Lemma D_4e6e8 : decode_any W_4e6e8 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6ec : bv 32 := 0x00810993.
Lemma F_4e6ec : fetch_word Plain.M.loaded_segments (0x4e6ec : word) = Some W_4e6ec.
Proof. vm_refl. Qed.
Lemma D_4e6ec : decode_any W_4e6ec = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6f0 : bv 32 := 0x0080006f.
Lemma F_4e6f0 : fetch_word Plain.M.loaded_segments (0x4e6f0 : word) = Some W_4e6f0.
Proof. vm_refl. Qed.
Lemma D_4e6f0 : decode_any W_4e6f0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6f4 : bv 32 := 0x01810993.
Lemma F_4e6f4 : fetch_word Plain.M.loaded_segments (0x4e6f4 : word) = Some W_4e6f4.
Proof. vm_refl. Qed.
Lemma D_4e6f4 : decode_any W_4e6f4 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6f8 : bv 32 := 0x0784a503.
Lemma F_4e6f8 : fetch_word Plain.M.loaded_segments (0x4e6f8 : word) = Some W_4e6f8.
Proof. vm_refl. Qed.
Lemma D_4e6f8 : decode_any W_4e6f8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e6fc : bv 32 := 0x00190913.
Lemma F_4e6fc : fetch_word Plain.M.loaded_segments (0x4e6fc : word) = Some W_4e6fc.
Proof. vm_refl. Qed.
Lemma D_4e6fc : decode_any W_4e6fc = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e700 : bv 32 := 0x04200893.
Lemma F_4e700 : fetch_word Plain.M.loaded_segments (0x4e700 : word) = Some W_4e700.
Proof. vm_refl. Qed.
Lemma D_4e700 : decode_any W_4e700 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e704 : bv 32 := 0x00098593.
Lemma F_4e704 : fetch_word Plain.M.loaded_segments (0x4e704 : word) = Some W_4e704.
Proof. vm_refl. Qed.
Lemma D_4e704 : decode_any W_4e704 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e708 : bv 32 := 0x00090613.
Lemma F_4e708 : fetch_word Plain.M.loaded_segments (0x4e708 : word) = Some W_4e708.
Proof. vm_refl. Qed.
Lemma D_4e708 : decode_any W_4e708 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e70c : bv 32 := 0x00000073.
Lemma F_4e70c : fetch_word Plain.M.loaded_segments (0x4e70c : word) = Some W_4e70c.
Proof. vm_refl. Qed.
Lemma D_4e70c : decode_any W_4e70c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_4e70c : is_ecall W_4e70c = true.
Proof. reflexivity. Qed.

Definition W_4e710 : bv 32 := 0xf0dfc0ef.
Lemma F_4e710 : fetch_word Plain.M.loaded_segments (0x4e710 : word) = Some W_4e710.
Proof. vm_refl. Qed.
Lemma D_4e710 : decode_any W_4e710 = Some (Jal 1 2084620, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e714 : bv 32 := 0x09651863.
Lemma F_4e714 : fetch_word Plain.M.loaded_segments (0x4e714 : word) = Some W_4e714.
Proof. vm_refl. Qed.
Lemma D_4e714 : decode_any W_4e714 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e718 : bv 32 := 0x0584b503.
Lemma F_4e718 : fetch_word Plain.M.loaded_segments (0x4e718 : word) = Some W_4e718.
Proof. vm_refl. Qed.
Lemma D_4e718 : decode_any W_4e718 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e71c : bv 32 := 0x0604b583.
Lemma F_4e71c : fetch_word Plain.M.loaded_segments (0x4e71c : word) = Some W_4e71c.
Proof. vm_refl. Qed.
Lemma D_4e71c : decode_any W_4e71c = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e720 : bv 32 := 0x00b505b3.
Lemma F_4e720 : fetch_word Plain.M.loaded_segments (0x4e720 : word) = Some W_4e720.
Proof. vm_refl. Qed.
Lemma D_4e720 : decode_any W_4e720 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e724 : bv 32 := 0x02b4b023.
Lemma F_4e724 : fetch_word Plain.M.loaded_segments (0x4e724 : word) = Some W_4e724.
Proof. vm_refl. Qed.
Lemma D_4e724 : decode_any W_4e724 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e728 : bv 32 := 0x02a4b423.
Lemma F_4e728 : fetch_word Plain.M.loaded_segments (0x4e728 : word) = Some W_4e728.
Proof. vm_refl. Qed.
Lemma D_4e728 : decode_any W_4e728 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e72c : bv 32 := 0x02a4bc23.
Lemma F_4e72c : fetch_word Plain.M.loaded_segments (0x4e72c : word) = Some W_4e72c.
Proof. vm_refl. Qed.
Lemma D_4e72c : decode_any W_4e72c = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e730 : bv 32 := 0x00040513.
Lemma F_4e730 : fetch_word Plain.M.loaded_segments (0x4e730 : word) = Some W_4e730.
Proof. vm_refl. Qed.
Lemma D_4e730 : decode_any W_4e730 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e734 : bv 32 := 0x000ab583.
Lemma F_4e734 : fetch_word Plain.M.loaded_segments (0x4e734 : word) = Some W_4e734.
Proof. vm_refl. Qed.
Lemma D_4e734 : decode_any W_4e734 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e738 : bv 32 := 0x02813603.
Lemma F_4e738 : fetch_word Plain.M.loaded_segments (0x4e738 : word) = Some W_4e738.
Proof. vm_refl. Qed.
Lemma D_4e738 : decode_any W_4e738 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e73c : bv 32 := 0x0cc59a63.
Lemma F_4e73c : fetch_word Plain.M.loaded_segments (0x4e73c : word) = Some W_4e73c.
Proof. vm_refl. Qed.
Lemma D_4e73c : decode_any W_4e73c = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e740 : bv 32 := 0x06813083.
Lemma F_4e740 : fetch_word Plain.M.loaded_segments (0x4e740 : word) = Some W_4e740.
Proof. vm_refl. Qed.
Lemma D_4e740 : decode_any W_4e740 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e744 : bv 32 := 0x06013403.
Lemma F_4e744 : fetch_word Plain.M.loaded_segments (0x4e744 : word) = Some W_4e744.
Proof. vm_refl. Qed.
Lemma D_4e744 : decode_any W_4e744 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e748 : bv 32 := 0x05813483.
Lemma F_4e748 : fetch_word Plain.M.loaded_segments (0x4e748 : word) = Some W_4e748.
Proof. vm_refl. Qed.
Lemma D_4e748 : decode_any W_4e748 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e74c : bv 32 := 0x05013903.
Lemma F_4e74c : fetch_word Plain.M.loaded_segments (0x4e74c : word) = Some W_4e74c.
Proof. vm_refl. Qed.
Lemma D_4e74c : decode_any W_4e74c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e750 : bv 32 := 0x04813983.
Lemma F_4e750 : fetch_word Plain.M.loaded_segments (0x4e750 : word) = Some W_4e750.
Proof. vm_refl. Qed.
Lemma D_4e750 : decode_any W_4e750 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e754 : bv 32 := 0x04013a03.
Lemma F_4e754 : fetch_word Plain.M.loaded_segments (0x4e754 : word) = Some W_4e754.
Proof. vm_refl. Qed.
Lemma D_4e754 : decode_any W_4e754 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e758 : bv 32 := 0x03813a83.
Lemma F_4e758 : fetch_word Plain.M.loaded_segments (0x4e758 : word) = Some W_4e758.
Proof. vm_refl. Qed.
Lemma D_4e758 : decode_any W_4e758 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e75c : bv 32 := 0x03013b03.
Lemma F_4e75c : fetch_word Plain.M.loaded_segments (0x4e75c : word) = Some W_4e75c.
Proof. vm_refl. Qed.
Lemma D_4e75c : decode_any W_4e75c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e760 : bv 32 := 0x07010113.
Lemma F_4e760 : fetch_word Plain.M.loaded_segments (0x4e760 : word) = Some W_4e760.
Proof. vm_refl. Qed.
Lemma D_4e760 : decode_any W_4e760 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e764 : bv 32 := 0x00008067.
Lemma F_4e764 : fetch_word Plain.M.loaded_segments (0x4e764 : word) = Some W_4e764.
Proof. vm_refl. Qed.
Lemma D_4e764 : decode_any W_4e764 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e768 : bv 32 := 0x00800713.
Lemma F_4e768 : fetch_word Plain.M.loaded_segments (0x4e768 : word) = Some W_4e768.
Proof. vm_refl. Qed.
Lemma D_4e768 : decode_any W_4e768 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e76c : bv 32 := 0x000a0593.
Lemma F_4e76c : fetch_word Plain.M.loaded_segments (0x4e76c : word) = Some W_4e76c.
Proof. vm_refl. Qed.
Lemma D_4e76c : decode_any W_4e76c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e770 : bv 32 := 0x00e98733.
Lemma F_4e770 : fetch_word Plain.M.loaded_segments (0x4e770 : word) = Some W_4e770.
Proof. vm_refl. Qed.
Lemma D_4e770 : decode_any W_4e770 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e774 : bv 32 := 0x00073783.
Lemma F_4e774 : fetch_word Plain.M.loaded_segments (0x4e774 : word) = Some W_4e774.
Proof. vm_refl. Qed.
Lemma D_4e774 : decode_any W_4e774 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e778 : bv 32 := 0x40ab0b33.
Lemma F_4e778 : fetch_word Plain.M.loaded_segments (0x4e778 : word) = Some W_4e778.
Proof. vm_refl. Qed.
Lemma D_4e778 : decode_any W_4e778 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e77c : bv 32 := 0x0784a503.
Lemma F_4e77c : fetch_word Plain.M.loaded_segments (0x4e77c : word) = Some W_4e77c.
Proof. vm_refl. Qed.
Lemma D_4e77c : decode_any W_4e77c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e780 : bv 32 := 0x40c9093b.
Lemma F_4e780 : fetch_word Plain.M.loaded_segments (0x4e780 : word) = Some W_4e780.
Proof. vm_refl. Qed.
Lemma D_4e780 : decode_any W_4e780 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e784 : bv 32 := 0x40d787b3.
Lemma F_4e784 : fetch_word Plain.M.loaded_segments (0x4e784 : word) = Some W_4e784.
Proof. vm_refl. Qed.
Lemma D_4e784 : decode_any W_4e784 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e788 : bv 32 := 0x00f73023.
Lemma F_4e788 : fetch_word Plain.M.loaded_segments (0x4e788 : word) = Some W_4e788.
Proof. vm_refl. Qed.
Lemma D_4e788 : decode_any W_4e788 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e78c : bv 32 := 0x04200893.
Lemma F_4e78c : fetch_word Plain.M.loaded_segments (0x4e78c : word) = Some W_4e78c.
Proof. vm_refl. Qed.
Lemma D_4e78c : decode_any W_4e78c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e790 : bv 32 := 0x00090613.
Lemma F_4e790 : fetch_word Plain.M.loaded_segments (0x4e790 : word) = Some W_4e790.
Proof. vm_refl. Qed.
Lemma D_4e790 : decode_any W_4e790 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e794 : bv 32 := 0x00000073.
Lemma F_4e794 : fetch_word Plain.M.loaded_segments (0x4e794 : word) = Some W_4e794.
Proof. vm_refl. Qed.
Lemma D_4e794 : decode_any W_4e794 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_4e794 : is_ecall W_4e794 = true.
Proof. reflexivity. Qed.

Definition W_4e798 : bv 32 := 0xe85fc0ef.
Lemma F_4e798 : fetch_word Plain.M.loaded_segments (0x4e798 : word) = Some W_4e798.
Proof. vm_refl. Qed.
Lemma D_4e798 : decode_any W_4e798 = Some (Jal 1 2084484, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e79c : bv 32 := 0x000a0993.
Lemma F_4e79c : fetch_word Plain.M.loaded_segments (0x4e79c : word) = Some W_4e79c.
Proof. vm_refl. Qed.
Lemma D_4e79c : decode_any W_4e79c = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7a0 : bv 32 := 0xf7650ce3.
Lemma F_4e7a0 : fetch_word Plain.M.loaded_segments (0x4e7a0 : word) = Some W_4e7a0.
Proof. vm_refl. Qed.
Lemma D_4e7a0 : decode_any W_4e7a0 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7a4 : bv 32 := 0x02054c63.
Lemma F_4e7a4 : fetch_word Plain.M.loaded_segments (0x4e7a4 : word) = Some W_4e7a4.
Proof. vm_refl. Qed.
Lemma D_4e7a4 : decode_any W_4e7a4 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7a8 : bv 32 := 0x0089b583.
Lemma F_4e7a8 : fetch_word Plain.M.loaded_segments (0x4e7a8 : word) = Some W_4e7a8.
Proof. vm_refl. Qed.
Lemma D_4e7a8 : decode_any W_4e7a8 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7ac : bv 32 := 0x00a5b633.
Lemma F_4e7ac : fetch_word Plain.M.loaded_segments (0x4e7ac : word) = Some W_4e7ac.
Proof. vm_refl. Qed.
Lemma D_4e7ac : decode_any W_4e7ac = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7b0 : bv 32 := 0x00461a13.
Lemma F_4e7b0 : fetch_word Plain.M.loaded_segments (0x4e7b0 : word) = Some W_4e7b0.
Proof. vm_refl. Qed.
Lemma D_4e7b0 : decode_any W_4e7b0 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7b4 : bv 32 := 0x01498a33.
Lemma F_4e7b4 : fetch_word Plain.M.loaded_segments (0x4e7b4 : word) = Some W_4e7b4.
Proof. vm_refl. Qed.
Lemma D_4e7b4 : decode_any W_4e7b4 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7b8 : bv 32 := 0x000a3703.
Lemma F_4e7b8 : fetch_word Plain.M.loaded_segments (0x4e7b8 : word) = Some W_4e7b8.
Proof. vm_refl. Qed.
Lemma D_4e7b8 : decode_any W_4e7b8 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7bc : bv 32 := 0x40c006b3.
Lemma F_4e7bc : fetch_word Plain.M.loaded_segments (0x4e7bc : word) = Some W_4e7bc.
Proof. vm_refl. Qed.
Lemma D_4e7bc : decode_any W_4e7bc = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7c0 : bv 32 := 0x00b6f6b3.
Lemma F_4e7c0 : fetch_word Plain.M.loaded_segments (0x4e7c0 : word) = Some W_4e7c0.
Proof. vm_refl. Qed.
Lemma D_4e7c0 : decode_any W_4e7c0 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7c4 : bv 32 := 0x40d506b3.
Lemma F_4e7c4 : fetch_word Plain.M.loaded_segments (0x4e7c4 : word) = Some W_4e7c4.
Proof. vm_refl. Qed.
Lemma D_4e7c4 : decode_any W_4e7c4 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7c8 : bv 32 := 0x00d70733.
Lemma F_4e7c8 : fetch_word Plain.M.loaded_segments (0x4e7c8 : word) = Some W_4e7c8.
Proof. vm_refl. Qed.
Lemma D_4e7c8 : decode_any W_4e7c8 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7cc : bv 32 := 0x00ea3023.
Lemma F_4e7cc : fetch_word Plain.M.loaded_segments (0x4e7cc : word) = Some W_4e7cc.
Proof. vm_refl. Qed.
Lemma D_4e7cc : decode_any W_4e7cc = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7d0 : bv 32 := 0xf8a5fce3.
Lemma F_4e7d0 : fetch_word Plain.M.loaded_segments (0x4e7d0 : word) = Some W_4e7d0.
Proof. vm_refl. Qed.
Lemma D_4e7d0 : decode_any W_4e7d0 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7d4 : bv 32 := 0x01800713.
Lemma F_4e7d4 : fetch_word Plain.M.loaded_segments (0x4e7d4 : word) = Some W_4e7d4.
Proof. vm_refl. Qed.
Lemma D_4e7d4 : decode_any W_4e7d4 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7d8 : bv 32 := 0xf95ff06f.
Lemma F_4e7d8 : fetch_word Plain.M.loaded_segments (0x4e7d8 : word) = Some W_4e7d8.
Proof. vm_refl. Qed.
Lemma D_4e7d8 : decode_any W_4e7d8 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
