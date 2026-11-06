(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_50a78 : bv 32 := 0x23d200ef.
Lemma F_50a78 : fetch_word Asan.M.loaded_segments (0x50a78 : word) = Some W_50a78.
Proof. vm_refl. Qed.
Lemma D_50a78 : decode_any W_50a78 = Some (Jal 1 133692, 4%Z).
Proof. vm_refl. Qed.

Definition W_50a7c : bv 32 := 0x00150b93.
Lemma F_50a7c : fetch_word Asan.M.loaded_segments (0x50a7c : word) = Some W_50a7c.
Proof. vm_refl. Qed.
Lemma D_50a7c : decode_any W_50a7c = Some (OpImm ALU_ADD 23 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_50a80 : bv 32 := 0xfffb4513.
Lemma F_50a80 : fetch_word Asan.M.loaded_segments (0x50a80 : word) = Some W_50a80.
Proof. vm_refl. Qed.
Lemma D_50a80 : decode_any W_50a80 = Some (OpImm ALU_XOR 10 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_50a84 : bv 32 := 0x25756e63.
Lemma F_50a84 : fetch_word Asan.M.loaded_segments (0x50a84 : word) = Some W_50a84.
Proof. vm_refl. Qed.
Lemma D_50a84 : decode_any W_50a84 = Some (Branch BC_LTU 10 23 604, 4%Z).
Proof. vm_refl. Qed.

Definition W_50a88 : bv 32 := 0xfbfb8513.
Lemma F_50a88 : fetch_word Asan.M.loaded_segments (0x50a88 : word) = Some W_50a88.
Proof. vm_refl. Qed.
Lemma D_50a88 : decode_any W_50a88 = Some (OpImm ALU_ADD 10 23 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_50a8c : bv 32 := 0xfbf00593.
Lemma F_50a8c : fetch_word Asan.M.loaded_segments (0x50a8c : word) = Some W_50a8c.
Proof. vm_refl. Qed.
Lemma D_50a8c : decode_any W_50a8c = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_50a90 : bv 32 := 0x2ca5f063.
Lemma F_50a90 : fetch_word Asan.M.loaded_segments (0x50a90 : word) = Some W_50a90.
Proof. vm_refl. Qed.
Lemma D_50a90 : decode_any W_50a90 = Some (Branch BC_GEU 11 10 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_50a94 : bv 32 := 0x00085517.
Lemma F_50a94 : fetch_word Asan.M.loaded_segments (0x50a94 : word) = Some W_50a94.
Proof. vm_refl. Qed.
Lemma D_50a94 : decode_any W_50a94 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_50a98 : bv 32 := 0xe2453503.
Lemma F_50a98 : fetch_word Asan.M.loaded_segments (0x50a98 : word) = Some W_50a98.
Proof. vm_refl. Qed.
Lemma D_50a98 : decode_any W_50a98 = Some (Load SZ8 true 10 10 3620, 4%Z).
Proof. vm_refl. Qed.

Definition W_50a9c : bv 32 := 0x017b0633.
Lemma F_50a9c : fetch_word Asan.M.loaded_segments (0x50a9c : word) = Some W_50a9c.
Proof. vm_refl. Qed.
Lemma D_50a9c : decode_any W_50a9c = Some (Op ALU_ADD 12 22 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_50aa0 : bv 32 := 0x00053583.
Lemma F_50aa0 : fetch_word Asan.M.loaded_segments (0x50aa0 : word) = Some W_50aa0.
Proof. vm_refl. Qed.
Lemma D_50aa0 : decode_any W_50aa0 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50aa4 : bv 32 := 0x003b5513.
Lemma F_50aa4 : fetch_word Asan.M.loaded_segments (0x50aa4 : word) = Some W_50aa4.
Proof. vm_refl. Qed.
Lemma D_50aa4 : decode_any W_50aa4 = Some (ShiftImm ALU_SRL 10 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_50aa8 : bv 32 := 0xfff60613.
Lemma F_50aa8 : fetch_word Asan.M.loaded_segments (0x50aa8 : word) = Some W_50aa8.
Proof. vm_refl. Qed.
Lemma D_50aa8 : decode_any W_50aa8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_50aac : bv 32 := 0x00365693.
Lemma F_50aac : fetch_word Asan.M.loaded_segments (0x50aac : word) = Some W_50aac.
Proof. vm_refl. Qed.
Lemma D_50aac : decode_any W_50aac = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ab0 : bv 32 := 0x00a58533.
Lemma F_50ab0 : fetch_word Asan.M.loaded_segments (0x50ab0 : word) = Some W_50ab0.
Proof. vm_refl. Qed.
Lemma D_50ab0 : decode_any W_50ab0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ab4 : bv 32 := 0x00d585b3.
Lemma F_50ab4 : fetch_word Asan.M.loaded_segments (0x50ab4 : word) = Some W_50ab4.
Proof. vm_refl. Qed.
Lemma D_50ab4 : decode_any W_50ab4 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ab8 : bv 32 := 0xff857693.
Lemma F_50ab8 : fetch_word Asan.M.loaded_segments (0x50ab8 : word) = Some W_50ab8.
Proof. vm_refl. Qed.
Lemma D_50ab8 : decode_any W_50ab8 = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_50abc : bv 32 := 0xff85f713.
Lemma F_50abc : fetch_word Asan.M.loaded_segments (0x50abc : word) = Some W_50abc.
Proof. vm_refl. Qed.
Lemma D_50abc : decode_any W_50abc = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ac0 : bv 32 := 0x0006b683.
Lemma F_50ac0 : fetch_word Asan.M.loaded_segments (0x50ac0 : word) = Some W_50ac0.
Proof. vm_refl. Qed.
Lemma D_50ac0 : decode_any W_50ac0 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ac4 : bv 32 := 0x00073703.
Lemma F_50ac4 : fetch_word Asan.M.loaded_segments (0x50ac4 : word) = Some W_50ac4.
Proof. vm_refl. Qed.
Lemma D_50ac4 : decode_any W_50ac4 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ac8 : bv 32 := 0x00d766b3.
Lemma F_50ac8 : fetch_word Asan.M.loaded_segments (0x50ac8 : word) = Some W_50ac8.
Proof. vm_refl. Qed.
Lemma D_50ac8 : decode_any W_50ac8 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_50acc : bv 32 := 0xf00688e3.
Lemma F_50acc : fetch_word Asan.M.loaded_segments (0x50acc : word) = Some W_50acc.
Proof. vm_refl. Qed.
Lemma D_50acc : decode_any W_50acc = Some (Branch BC_EQ 13 0 7952, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ad0 : bv 32 := 0x00058683.
Lemma F_50ad0 : fetch_word Asan.M.loaded_segments (0x50ad0 : word) = Some W_50ad0.
Proof. vm_refl. Qed.
Lemma D_50ad0 : decode_any W_50ad0 = Some (Load SZ1 true 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ad4 : bv 32 := 0x00767613.
Lemma F_50ad4 : fetch_word Asan.M.loaded_segments (0x50ad4 : word) = Some W_50ad4.
Proof. vm_refl. Qed.
Lemma D_50ad4 : decode_any W_50ad4 = Some (OpImm ALU_AND 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ad8 : bv 32 := 0x00d03733.
Lemma F_50ad8 : fetch_word Asan.M.loaded_segments (0x50ad8 : word) = Some W_50ad8.
Proof. vm_refl. Qed.
Lemma D_50ad8 : decode_any W_50ad8 = Some (Op ALU_SLTU 14 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_50adc : bv 32 := 0x00d62633.
Lemma F_50adc : fetch_word Asan.M.loaded_segments (0x50adc : word) = Some W_50adc.
Proof. vm_refl. Qed.
Lemma D_50adc : decode_any W_50adc = Some (Op ALU_SLT 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ae0 : bv 32 := 0x00164613.
Lemma F_50ae0 : fetch_word Asan.M.loaded_segments (0x50ae0 : word) = Some W_50ae0.
Proof. vm_refl. Qed.
Lemma D_50ae0 : decode_any W_50ae0 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ae4 : bv 32 := 0x00c77633.
Lemma F_50ae4 : fetch_word Asan.M.loaded_segments (0x50ae4 : word) = Some W_50ae4.
Proof. vm_refl. Qed.
Lemma D_50ae4 : decode_any W_50ae4 = Some (Op ALU_AND 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_50ae8 : bv 32 := 0x00b57a63.
Lemma F_50ae8 : fetch_word Asan.M.loaded_segments (0x50ae8 : word) = Some W_50ae8.
Proof. vm_refl. Qed.
Lemma D_50ae8 : decode_any W_50ae8 = Some (Branch BC_GEU 10 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_50aec : bv 32 := 0x00054683.
Lemma F_50aec : fetch_word Asan.M.loaded_segments (0x50aec : word) = Some W_50aec.
Proof. vm_refl. Qed.
Lemma D_50aec : decode_any W_50aec = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50af0 : bv 32 := 0x00150513.
Lemma F_50af0 : fetch_word Asan.M.loaded_segments (0x50af0 : word) = Some W_50af0.
Proof. vm_refl. Qed.
Lemma D_50af0 : decode_any W_50af0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_50af4 : bv 32 := 0x00c6e633.
Lemma F_50af4 : fetch_word Asan.M.loaded_segments (0x50af4 : word) = Some W_50af4.
Proof. vm_refl. Qed.
Lemma D_50af4 : decode_any W_50af4 = Some (Op ALU_OR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_50af8 : bv 32 := 0xfeb51ae3.
Lemma F_50af8 : fetch_word Asan.M.loaded_segments (0x50af8 : word) = Some W_50af8.
Proof. vm_refl. Qed.
Lemma D_50af8 : decode_any W_50af8 = Some (Branch BC_NE 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_50afc : bv 32 := 0x0ff67513.
Lemma F_50afc : fetch_word Asan.M.loaded_segments (0x50afc : word) = Some W_50afc.
Proof. vm_refl. Qed.
Lemma D_50afc : decode_any W_50afc = Some (OpImm ALU_AND 10 12 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_50b00 : bv 32 := 0xec050ee3.
Lemma F_50b00 : fetch_word Asan.M.loaded_segments (0x50b00 : word) = Some W_50b00.
Proof. vm_refl. Qed.
Lemma D_50b00 : decode_any W_50b00 = Some (Branch BC_EQ 10 0 7900, 4%Z).
Proof. vm_refl. Qed.

Definition W_50b04 : bv 32 := 0x000b0513.
Lemma F_50b04 : fetch_word Asan.M.loaded_segments (0x50b04 : word) = Some W_50b04.
Proof. vm_refl. Qed.
Lemma D_50b04 : decode_any W_50b04 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50b08 : bv 32 := 0x000b8593.
Lemma F_50b08 : fetch_word Asan.M.loaded_segments (0x50b08 : word) = Some W_50b08.
Proof. vm_refl. Qed.
Lemma D_50b08 : decode_any W_50b08 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50b0c : bv 32 := 0x5f5100ef.
Lemma F_50b0c : fetch_word Asan.M.loaded_segments (0x50b0c : word) = Some W_50b0c.
Proof. vm_refl. Qed.
Lemma D_50b0c : decode_any W_50b0c = Some (Jal 1 69108, 4%Z).
Proof. vm_refl. Qed.

Definition W_50b10 : bv 32 := 0xec0506e3.
Lemma F_50b10 : fetch_word Asan.M.loaded_segments (0x50b10 : word) = Some W_50b10.
Proof. vm_refl. Qed.
Lemma D_50b10 : decode_any W_50b10 = Some (Branch BC_EQ 10 0 7884, 4%Z).
Proof. vm_refl. Qed.
