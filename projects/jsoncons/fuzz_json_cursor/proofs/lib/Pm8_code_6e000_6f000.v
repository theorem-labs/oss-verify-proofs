(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6e640 : bv 32 := 0x104240ef.
Lemma F_6e640 : fetch_word Asan.M.loaded_segments (0x6e690 : word) = Some W_6e640.
Proof. vm_refl. Qed.
Lemma D_6e640 : decode_any W_6e640 = Some (Jal 1 147716, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e644 : bv 32 := 0x00150b93.
Lemma F_6e644 : fetch_word Asan.M.loaded_segments (0x6e694 : word) = Some W_6e644.
Proof. vm_refl. Qed.
Lemma D_6e644 : decode_any W_6e644 = Some (OpImm ALU_ADD 23 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e648 : bv 32 := 0xfffb4513.
Lemma F_6e648 : fetch_word Asan.M.loaded_segments (0x6e698 : word) = Some W_6e648.
Proof. vm_refl. Qed.
Lemma D_6e648 : decode_any W_6e648 = Some (OpImm ALU_XOR 10 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e64c : bv 32 := 0x25756e63.
Lemma F_6e64c : fetch_word Asan.M.loaded_segments (0x6e69c : word) = Some W_6e64c.
Proof. vm_refl. Qed.
Lemma D_6e64c : decode_any W_6e64c = Some (Branch BC_LTU 10 23 604, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e650 : bv 32 := 0xfbfb8513.
Lemma F_6e650 : fetch_word Asan.M.loaded_segments (0x6e6a0 : word) = Some W_6e650.
Proof. vm_refl. Qed.
Lemma D_6e650 : decode_any W_6e650 = Some (OpImm ALU_ADD 10 23 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e654 : bv 32 := 0xfbf00593.
Lemma F_6e654 : fetch_word Asan.M.loaded_segments (0x6e6a4 : word) = Some W_6e654.
Proof. vm_refl. Qed.
Lemma D_6e654 : decode_any W_6e654 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e658 : bv 32 := 0x2ca5f063.
Lemma F_6e658 : fetch_word Asan.M.loaded_segments (0x6e6a8 : word) = Some W_6e658.
Proof. vm_refl. Qed.
Lemma D_6e658 : decode_any W_6e658 = Some (Branch BC_GEU 11 10 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e65c : bv 32 := 0x000e5517.
Lemma F_6e65c : fetch_word Asan.M.loaded_segments (0x6e6ac : word) = Some W_6e65c.
Proof. vm_refl. Qed.
Lemma D_6e65c : decode_any W_6e65c = Some (Auipc 10 229, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e660 : bv 32 := 0xa8c53503.
Lemma F_6e660 : fetch_word Asan.M.loaded_segments (0x6e6b0 : word) = Some W_6e660.
Proof. vm_refl. Qed.
Lemma D_6e660 : decode_any W_6e660 = Some (Load SZ8 true 10 10 2700, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e664 : bv 32 := 0x017b0633.
Lemma F_6e664 : fetch_word Asan.M.loaded_segments (0x6e6b4 : word) = Some W_6e664.
Proof. vm_refl. Qed.
Lemma D_6e664 : decode_any W_6e664 = Some (Op ALU_ADD 12 22 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e668 : bv 32 := 0x00053583.
Lemma F_6e668 : fetch_word Asan.M.loaded_segments (0x6e6b8 : word) = Some W_6e668.
Proof. vm_refl. Qed.
Lemma D_6e668 : decode_any W_6e668 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e66c : bv 32 := 0x003b5513.
Lemma F_6e66c : fetch_word Asan.M.loaded_segments (0x6e6bc : word) = Some W_6e66c.
Proof. vm_refl. Qed.
Lemma D_6e66c : decode_any W_6e66c = Some (ShiftImm ALU_SRL 10 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e670 : bv 32 := 0xfff60613.
Lemma F_6e670 : fetch_word Asan.M.loaded_segments (0x6e6c0 : word) = Some W_6e670.
Proof. vm_refl. Qed.
Lemma D_6e670 : decode_any W_6e670 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e674 : bv 32 := 0x00365693.
Lemma F_6e674 : fetch_word Asan.M.loaded_segments (0x6e6c4 : word) = Some W_6e674.
Proof. vm_refl. Qed.
Lemma D_6e674 : decode_any W_6e674 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e678 : bv 32 := 0x00a58533.
Lemma F_6e678 : fetch_word Asan.M.loaded_segments (0x6e6c8 : word) = Some W_6e678.
Proof. vm_refl. Qed.
Lemma D_6e678 : decode_any W_6e678 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e67c : bv 32 := 0x00d585b3.
Lemma F_6e67c : fetch_word Asan.M.loaded_segments (0x6e6cc : word) = Some W_6e67c.
Proof. vm_refl. Qed.
Lemma D_6e67c : decode_any W_6e67c = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e680 : bv 32 := 0xff857693.
Lemma F_6e680 : fetch_word Asan.M.loaded_segments (0x6e6d0 : word) = Some W_6e680.
Proof. vm_refl. Qed.
Lemma D_6e680 : decode_any W_6e680 = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e684 : bv 32 := 0xff85f713.
Lemma F_6e684 : fetch_word Asan.M.loaded_segments (0x6e6d4 : word) = Some W_6e684.
Proof. vm_refl. Qed.
Lemma D_6e684 : decode_any W_6e684 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e688 : bv 32 := 0x0006b683.
Lemma F_6e688 : fetch_word Asan.M.loaded_segments (0x6e6d8 : word) = Some W_6e688.
Proof. vm_refl. Qed.
Lemma D_6e688 : decode_any W_6e688 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e68c : bv 32 := 0x00073703.
Lemma F_6e68c : fetch_word Asan.M.loaded_segments (0x6e6dc : word) = Some W_6e68c.
Proof. vm_refl. Qed.
Lemma D_6e68c : decode_any W_6e68c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e690 : bv 32 := 0x00d766b3.
Lemma F_6e690 : fetch_word Asan.M.loaded_segments (0x6e6e0 : word) = Some W_6e690.
Proof. vm_refl. Qed.
Lemma D_6e690 : decode_any W_6e690 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e694 : bv 32 := 0xf00688e3.
Lemma F_6e694 : fetch_word Asan.M.loaded_segments (0x6e6e4 : word) = Some W_6e694.
Proof. vm_refl. Qed.
Lemma D_6e694 : decode_any W_6e694 = Some (Branch BC_EQ 13 0 7952, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e6cc : bv 32 := 0x000b0513.
Lemma F_6e6cc : fetch_word Asan.M.loaded_segments (0x6e71c : word) = Some W_6e6cc.
Proof. vm_refl. Qed.
Lemma D_6e6cc : decode_any W_6e6cc = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e6d0 : bv 32 := 0x000b8593.
Lemma F_6e6d0 : fetch_word Asan.M.loaded_segments (0x6e720 : word) = Some W_6e6d0.
Proof. vm_refl. Qed.
Lemma D_6e6d0 : decode_any W_6e6d0 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e6d4 : bv 32 := 0x77d130ef.
Lemma F_6e6d4 : fetch_word Asan.M.loaded_segments (0x6e724 : word) = Some W_6e6d4.
Proof. vm_refl. Qed.
Lemma D_6e6d4 : decode_any W_6e6d4 = Some (Jal 1 81788, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e6d8 : bv 32 := 0xec0506e3.
Lemma F_6e6d8 : fetch_word Asan.M.loaded_segments (0x6e728 : word) = Some W_6e6d8.
Proof. vm_refl. Qed.
Lemma D_6e6d8 : decode_any W_6e6d8 = Some (Branch BC_EQ 10 0 7884, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e918 : bv 32 := 0xda0b9ae3.
Lemma F_6e918 : fetch_word Asan.M.loaded_segments (0x6e968 : word) = Some W_6e918.
Proof. vm_refl. Qed.
Lemma D_6e918 : decode_any W_6e918 = Some (Branch BC_NE 23 0 7604, 4%Z).
Proof. vm_refl. Qed.

