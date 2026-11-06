(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_67de4 : bv 32 := 0x104240ef.
Lemma F_67de4 : fetch_word Asan.M.loaded_segments (0x67e34 : word) = Some W_67de4.
Proof. vm_refl. Qed.
Lemma D_67de4 : decode_any W_67de4 = Some (Jal 1 147716, 4%Z).
Proof. vm_refl. Qed.

Definition W_67de8 : bv 32 := 0x00150b93.
Lemma F_67de8 : fetch_word Asan.M.loaded_segments (0x67e38 : word) = Some W_67de8.
Proof. vm_refl. Qed.
Lemma D_67de8 : decode_any W_67de8 = Some (OpImm ALU_ADD 23 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dec : bv 32 := 0xfffb4513.
Lemma F_67dec : fetch_word Asan.M.loaded_segments (0x67e3c : word) = Some W_67dec.
Proof. vm_refl. Qed.
Lemma D_67dec : decode_any W_67dec = Some (OpImm ALU_XOR 10 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_67df0 : bv 32 := 0x25756e63.
Lemma F_67df0 : fetch_word Asan.M.loaded_segments (0x67e40 : word) = Some W_67df0.
Proof. vm_refl. Qed.
Lemma D_67df0 : decode_any W_67df0 = Some (Branch BC_LTU 10 23 604, 4%Z).
Proof. vm_refl. Qed.

Definition W_67df4 : bv 32 := 0xfbfb8513.
Lemma F_67df4 : fetch_word Asan.M.loaded_segments (0x67e44 : word) = Some W_67df4.
Proof. vm_refl. Qed.
Lemma D_67df4 : decode_any W_67df4 = Some (OpImm ALU_ADD 10 23 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_67df8 : bv 32 := 0xfbf00593.
Lemma F_67df8 : fetch_word Asan.M.loaded_segments (0x67e48 : word) = Some W_67df8.
Proof. vm_refl. Qed.
Lemma D_67df8 : decode_any W_67df8 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dfc : bv 32 := 0x2ca5f063.
Lemma F_67dfc : fetch_word Asan.M.loaded_segments (0x67e4c : word) = Some W_67dfc.
Proof. vm_refl. Qed.
Lemma D_67dfc : decode_any W_67dfc = Some (Branch BC_GEU 11 10 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e00 : bv 32 := 0x000d1517.
Lemma F_67e00 : fetch_word Asan.M.loaded_segments (0x67e50 : word) = Some W_67e00.
Proof. vm_refl. Qed.
Lemma D_67e00 : decode_any W_67e00 = Some (Auipc 10 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e04 : bv 32 := 0x36853503.
Lemma F_67e04 : fetch_word Asan.M.loaded_segments (0x67e54 : word) = Some W_67e04.
Proof. vm_refl. Qed.
Lemma D_67e04 : decode_any W_67e04 = Some (Load SZ8 true 10 10 872, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e08 : bv 32 := 0x017b0633.
Lemma F_67e08 : fetch_word Asan.M.loaded_segments (0x67e58 : word) = Some W_67e08.
Proof. vm_refl. Qed.
Lemma D_67e08 : decode_any W_67e08 = Some (Op ALU_ADD 12 22 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e0c : bv 32 := 0x00053583.
Lemma F_67e0c : fetch_word Asan.M.loaded_segments (0x67e5c : word) = Some W_67e0c.
Proof. vm_refl. Qed.
Lemma D_67e0c : decode_any W_67e0c = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e10 : bv 32 := 0x003b5513.
Lemma F_67e10 : fetch_word Asan.M.loaded_segments (0x67e60 : word) = Some W_67e10.
Proof. vm_refl. Qed.
Lemma D_67e10 : decode_any W_67e10 = Some (ShiftImm ALU_SRL 10 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e14 : bv 32 := 0xfff60613.
Lemma F_67e14 : fetch_word Asan.M.loaded_segments (0x67e64 : word) = Some W_67e14.
Proof. vm_refl. Qed.
Lemma D_67e14 : decode_any W_67e14 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e18 : bv 32 := 0x00365693.
Lemma F_67e18 : fetch_word Asan.M.loaded_segments (0x67e68 : word) = Some W_67e18.
Proof. vm_refl. Qed.
Lemma D_67e18 : decode_any W_67e18 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e1c : bv 32 := 0x00a58533.
Lemma F_67e1c : fetch_word Asan.M.loaded_segments (0x67e6c : word) = Some W_67e1c.
Proof. vm_refl. Qed.
Lemma D_67e1c : decode_any W_67e1c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e20 : bv 32 := 0x00d585b3.
Lemma F_67e20 : fetch_word Asan.M.loaded_segments (0x67e70 : word) = Some W_67e20.
Proof. vm_refl. Qed.
Lemma D_67e20 : decode_any W_67e20 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e24 : bv 32 := 0xff857693.
Lemma F_67e24 : fetch_word Asan.M.loaded_segments (0x67e74 : word) = Some W_67e24.
Proof. vm_refl. Qed.
Lemma D_67e24 : decode_any W_67e24 = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e28 : bv 32 := 0xff85f713.
Lemma F_67e28 : fetch_word Asan.M.loaded_segments (0x67e78 : word) = Some W_67e28.
Proof. vm_refl. Qed.
Lemma D_67e28 : decode_any W_67e28 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e2c : bv 32 := 0x0006b683.
Lemma F_67e2c : fetch_word Asan.M.loaded_segments (0x67e7c : word) = Some W_67e2c.
Proof. vm_refl. Qed.
Lemma D_67e2c : decode_any W_67e2c = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e30 : bv 32 := 0x00073703.
Lemma F_67e30 : fetch_word Asan.M.loaded_segments (0x67e80 : word) = Some W_67e30.
Proof. vm_refl. Qed.
Lemma D_67e30 : decode_any W_67e30 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e34 : bv 32 := 0x00d766b3.
Lemma F_67e34 : fetch_word Asan.M.loaded_segments (0x67e84 : word) = Some W_67e34.
Proof. vm_refl. Qed.
Lemma D_67e34 : decode_any W_67e34 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e38 : bv 32 := 0xf00688e3.
Lemma F_67e38 : fetch_word Asan.M.loaded_segments (0x67e88 : word) = Some W_67e38.
Proof. vm_refl. Qed.
Lemma D_67e38 : decode_any W_67e38 = Some (Branch BC_EQ 13 0 7952, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e70 : bv 32 := 0x000b0513.
Lemma F_67e70 : fetch_word Asan.M.loaded_segments (0x67ec0 : word) = Some W_67e70.
Proof. vm_refl. Qed.
Lemma D_67e70 : decode_any W_67e70 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e74 : bv 32 := 0x000b8593.
Lemma F_67e74 : fetch_word Asan.M.loaded_segments (0x67ec4 : word) = Some W_67e74.
Proof. vm_refl. Qed.
Lemma D_67e74 : decode_any W_67e74 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e78 : bv 32 := 0x77d130ef.
Lemma F_67e78 : fetch_word Asan.M.loaded_segments (0x67ec8 : word) = Some W_67e78.
Proof. vm_refl. Qed.
Lemma D_67e78 : decode_any W_67e78 = Some (Jal 1 81788, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e7c : bv 32 := 0xec0506e3.
Lemma F_67e7c : fetch_word Asan.M.loaded_segments (0x67ecc : word) = Some W_67e7c.
Proof. vm_refl. Qed.
Lemma D_67e7c : decode_any W_67e7c = Some (Branch BC_EQ 10 0 7884, 4%Z).
Proof. vm_refl. Qed.
