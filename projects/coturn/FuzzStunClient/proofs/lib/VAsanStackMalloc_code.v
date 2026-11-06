(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_3ecf8 : bv 32 := 0xfe010113.
Lemma F_3ecf8 : fetch_word Asan.M.loaded_segments (0x3ecf8 : word) = Some W_3ecf8.
Proof. vm_refl. Qed.
Lemma D_3ecf8 : decode_any W_3ecf8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ecfc : bv 32 := 0x00113c23.
Lemma F_3ecfc : fetch_word Asan.M.loaded_segments (0x3ecfc : word) = Some W_3ecfc.
Proof. vm_refl. Qed.
Lemma D_3ecfc : decode_any W_3ecfc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed00 : bv 32 := 0x00813823.
Lemma F_3ed00 : fetch_word Asan.M.loaded_segments (0x3ed00 : word) = Some W_3ed00.
Proof. vm_refl. Qed.
Lemma D_3ed00 : decode_any W_3ed00 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed04 : bv 32 := 0x00913423.
Lemma F_3ed04 : fetch_word Asan.M.loaded_segments (0x3ed04 : word) = Some W_3ed04.
Proof. vm_refl. Qed.
Lemma D_3ed04 : decode_any W_3ed04 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed08 : bv 32 := 0x01213023.
Lemma F_3ed08 : fetch_word Asan.M.loaded_segments (0x3ed08 : word) = Some W_3ed08.
Proof. vm_refl. Qed.
Lemma D_3ed08 : decode_any W_3ed08 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed0c : bv 32 := 0x02010413.
Lemma F_3ed0c : fetch_word Asan.M.loaded_segments (0x3ed0c : word) = Some W_3ed0c.
Proof. vm_refl. Qed.
Lemma D_3ed0c : decode_any W_3ed0c = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed10 : bv 32 := 0x0006d517.
Lemma F_3ed10 : fetch_word Asan.M.loaded_segments (0x3ed10 : word) = Some W_3ed10.
Proof. vm_refl. Qed.
Lemma D_3ed10 : decode_any W_3ed10 = Some (Auipc 10 109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed14 : bv 32 := 0xe5050513.
Lemma F_3ed14 : fetch_word Asan.M.loaded_segments (0x3ed14 : word) = Some W_3ed14.
Proof. vm_refl. Qed.
Lemma D_3ed14 : decode_any W_3ed14 = Some (OpImm ALU_ADD 10 10 3664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed18 : bv 32 := 0x574050ef.
Lemma F_3ed18 : fetch_word Asan.M.loaded_segments (0x3ed18 : word) = Some W_3ed18.
Proof. vm_refl. Qed.
Lemma D_3ed18 : decode_any W_3ed18 = Some (Jal 1 21876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed1c : bv 32 := 0x00053483.
Lemma F_3ed1c : fetch_word Asan.M.loaded_segments (0x3ed1c : word) = Some W_3ed1c.
Proof. vm_refl. Qed.
Lemma D_3ed1c : decode_any W_3ed1c = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed20 : bv 32 := 0x08048063.
Lemma F_3ed20 : fetch_word Asan.M.loaded_segments (0x3ed20 : word) = Some W_3ed20.
Proof. vm_refl. Qed.
Lemma D_3ed20 : decode_any W_3ed20 = Some (Branch BC_EQ 9 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed24 : bv 32 := 0x0604c503.
Lemma F_3ed24 : fetch_word Asan.M.loaded_segments (0x3ed24 : word) = Some W_3ed24.
Proof. vm_refl. Qed.
Lemma D_3ed24 : decode_any W_3ed24 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed28 : bv 32 := 0x0584b903.
Lemma F_3ed28 : fetch_word Asan.M.loaded_segments (0x3ed28 : word) = Some W_3ed28.
Proof. vm_refl. Qed.
Lemma D_3ed28 : decode_any W_3ed28 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed2c : bv 32 := 0x00050863.
Lemma F_3ed2c : fetch_word Asan.M.loaded_segments (0x3ed2c : word) = Some W_3ed2c.
Proof. vm_refl. Qed.
Lemma D_3ed2c : decode_any W_3ed2c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed30 : bv 32 := 0x00048513.
Lemma F_3ed30 : fetch_word Asan.M.loaded_segments (0x3ed30 : word) = Some W_3ed30.
Proof. vm_refl. Qed.
Lemma D_3ed30 : decode_any W_3ed30 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed34 : bv 32 := 0x00040593.
Lemma F_3ed34 : fetch_word Asan.M.loaded_segments (0x3ed34 : word) = Some W_3ed34.
Proof. vm_refl. Qed.
Lemma D_3ed34 : decode_any W_3ed34 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed38 : bv 32 := 0xb75ff0ef.
Lemma F_3ed38 : fetch_word Asan.M.loaded_segments (0x3ed38 : word) = Some W_3ed38.
Proof. vm_refl. Qed.
Lemma D_3ed38 : decode_any W_3ed38 = Some (Jal 1 2095988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed3c : bv 32 := 0xffa90593.
Lemma F_3ed3c : fetch_word Asan.M.loaded_segments (0x3ed3c : word) = Some W_3ed3c.
Proof. vm_refl. Qed.
Lemma D_3ed3c : decode_any W_3ed3c = Some (OpImm ALU_ADD 11 18 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed40 : bv 32 := 0x00100513.
Lemma F_3ed40 : fetch_word Asan.M.loaded_segments (0x3ed40 : word) = Some W_3ed40.
Proof. vm_refl. Qed.
Lemma D_3ed40 : decode_any W_3ed40 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed44 : bv 32 := 0x00b51533.
Lemma F_3ed44 : fetch_word Asan.M.loaded_segments (0x3ed44 : word) = Some W_3ed44.
Proof. vm_refl. Qed.
Lemma D_3ed44 : decode_any W_3ed44 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed48 : bv 32 := 0x0005061b.
Lemma F_3ed48 : fetch_word Asan.M.loaded_segments (0x3ed48 : word) = Some W_3ed48.
Proof. vm_refl. Qed.
Lemma D_3ed48 : decode_any W_3ed48 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed4c : bv 32 := 0x06c05a63.
Lemma F_3ed4c : fetch_word Asan.M.loaded_segments (0x3ed4c : word) = Some W_3ed4c.
Proof. vm_refl. Qed.
Lemma D_3ed4c : decode_any W_3ed4c = Some (Branch BC_GE 0 12 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed50 : bv 32 := 0x000016b7.
Lemma F_3ed50 : fetch_word Asan.M.loaded_segments (0x3ed50 : word) = Some W_3ed50.
Proof. vm_refl. Qed.
Lemma D_3ed50 : decode_any W_3ed50 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed54 : bv 32 := 0xfff00713.
Lemma F_3ed54 : fetch_word Asan.M.loaded_segments (0x3ed54 : word) = Some W_3ed54.
Proof. vm_refl. Qed.
Lemma D_3ed54 : decode_any W_3ed54 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed58 : bv 32 := 0x0004b603.
Lemma F_3ed58 : fetch_word Asan.M.loaded_segments (0x3ed58 : word) = Some W_3ed58.
Proof. vm_refl. Qed.
Lemma D_3ed58 : decode_any W_3ed58 = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed5c : bv 32 := 0x00b71733.
Lemma F_3ed5c : fetch_word Asan.M.loaded_segments (0x3ed5c : word) = Some W_3ed5c.
Proof. vm_refl. Qed.
Lemma D_3ed5c : decode_any W_3ed5c = Some (Op ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed60 : bv 32 := 0xfff50793.
Lemma F_3ed60 : fetch_word Asan.M.loaded_segments (0x3ed60 : word) = Some W_3ed60.
Proof. vm_refl. Qed.
Lemma D_3ed60 : decode_any W_3ed60 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed64 : bv 32 := 0x00d485b3.
Lemma F_3ed64 : fetch_word Asan.M.loaded_segments (0x3ed64 : word) = Some W_3ed64.
Proof. vm_refl. Qed.
Lemma D_3ed64 : decode_any W_3ed64 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed68 : bv 32 := 0xfff74693.
Lemma F_3ed68 : fetch_word Asan.M.loaded_segments (0x3ed68 : word) = Some W_3ed68.
Proof. vm_refl. Qed.
Lemma D_3ed68 : decode_any W_3ed68 = Some (OpImm ALU_XOR 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed6c : bv 32 := 0x02079793.
Lemma F_3ed6c : fetch_word Asan.M.loaded_segments (0x3ed6c : word) = Some W_3ed6c.
Proof. vm_refl. Qed.
Lemma D_3ed6c : decode_any W_3ed6c = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed70 : bv 32 := 0x0207d793.
Lemma F_3ed70 : fetch_word Asan.M.loaded_segments (0x3ed70 : word) = Some W_3ed70.
Proof. vm_refl. Qed.
Lemma D_3ed70 : decode_any W_3ed70 = Some (ShiftImm ALU_SRL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed74 : bv 32 := 0x00f60733.
Lemma F_3ed74 : fetch_word Asan.M.loaded_segments (0x3ed74 : word) = Some W_3ed74.
Proof. vm_refl. Qed.
Lemma D_3ed74 : decode_any W_3ed74 = Some (Op ALU_ADD 14 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed78 : bv 32 := 0x00170713.
Lemma F_3ed78 : fetch_word Asan.M.loaded_segments (0x3ed78 : word) = Some W_3ed78.
Proof. vm_refl. Qed.
Lemma D_3ed78 : decode_any W_3ed78 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed7c : bv 32 := 0x00d67833.
Lemma F_3ed7c : fetch_word Asan.M.loaded_segments (0x3ed7c : word) = Some W_3ed7c.
Proof. vm_refl. Qed.
Lemma D_3ed7c : decode_any W_3ed7c = Some (Op ALU_AND 16 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed80 : bv 32 := 0x010587b3.
Lemma F_3ed80 : fetch_word Asan.M.loaded_segments (0x3ed80 : word) = Some W_3ed80.
Proof. vm_refl. Qed.
Lemma D_3ed80 : decode_any W_3ed80 = Some (Op ALU_ADD 15 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed84 : bv 32 := 0x0007c883.
Lemma F_3ed84 : fetch_word Asan.M.loaded_segments (0x3ed84 : word) = Some W_3ed84.
Proof. vm_refl. Qed.
Lemma D_3ed84 : decode_any W_3ed84 = Some (Load SZ1 false 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed88 : bv 32 := 0x06088663.
Lemma F_3ed88 : fetch_word Asan.M.loaded_segments (0x3ed88 : word) = Some W_3ed88.
Proof. vm_refl. Qed.
Lemma D_3ed88 : decode_any W_3ed88 = Some (Branch BC_EQ 17 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed8c : bv 32 := 0xfff5051b.
Lemma F_3ed8c : fetch_word Asan.M.loaded_segments (0x3ed8c : word) = Some W_3ed8c.
Proof. vm_refl. Qed.
Lemma D_3ed8c : decode_any W_3ed8c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed90 : bv 32 := 0x00160613.
Lemma F_3ed90 : fetch_word Asan.M.loaded_segments (0x3ed90 : word) = Some W_3ed90.
Proof. vm_refl. Qed.
Lemma D_3ed90 : decode_any W_3ed90 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed94 : bv 32 := 0xfe0514e3.
Lemma F_3ed94 : fetch_word Asan.M.loaded_segments (0x3ed94 : word) = Some W_3ed94.
Proof. vm_refl. Qed.
Lemma D_3ed94 : decode_any W_3ed94 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed98 : bv 32 := 0x00e4b023.
Lemma F_3ed98 : fetch_word Asan.M.loaded_segments (0x3ed98 : word) = Some W_3ed98.
Proof. vm_refl. Qed.
Lemma D_3ed98 : decode_any W_3ed98 = Some (Store SZ8 9 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ed9c : bv 32 := 0x0400006f.
Lemma F_3ed9c : fetch_word Asan.M.loaded_segments (0x3ed9c : word) = Some W_3ed9c.
Proof. vm_refl. Qed.
Lemma D_3ed9c : decode_any W_3ed9c = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eda0 : bv 32 := 0x0006c517.
Lemma F_3eda0 : fetch_word Asan.M.loaded_segments (0x3eda0 : word) = Some W_3eda0.
Proof. vm_refl. Qed.
Lemma D_3eda0 : decode_any W_3eda0 = Some (Auipc 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eda4 : bv 32 := 0x13853503.
Lemma F_3eda4 : fetch_word Asan.M.loaded_segments (0x3eda4 : word) = Some W_3eda4.
Proof. vm_refl. Qed.
Lemma D_3eda4 : decode_any W_3eda4 = Some (Load SZ8 true 10 10 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eda8 : bv 32 := 0x00052503.
Lemma F_3eda8 : fetch_word Asan.M.loaded_segments (0x3eda8 : word) = Some W_3eda8.
Proof. vm_refl. Qed.
Lemma D_3eda8 : decode_any W_3eda8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edac : bv 32 := 0x02050863.
Lemma F_3edac : fetch_word Asan.M.loaded_segments (0x3edac : word) = Some W_3edac.
Proof. vm_refl. Qed.
Lemma D_3edac : decode_any W_3edac = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edb0 : bv 32 := 0x0911f0ef.
Lemma F_3edb0 : fetch_word Asan.M.loaded_segments (0x3edb0 : word) = Some W_3edb0.
Proof. vm_refl. Qed.
Lemma D_3edb0 : decode_any W_3edb0 = Some (Jal 1 129168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edb4 : bv 32 := 0x02050463.
Lemma F_3edb4 : fetch_word Asan.M.loaded_segments (0x3edb4 : word) = Some W_3edb4.
Proof. vm_refl. Qed.
Lemma D_3edb4 : decode_any W_3edb4 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edb8 : bv 32 := 0x02850583.
Lemma F_3edb8 : fetch_word Asan.M.loaded_segments (0x3edb8 : word) = Some W_3edb8.
Proof. vm_refl. Qed.
Lemma D_3edb8 : decode_any W_3edb8 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edbc : bv 32 := 0x08058a63.
Lemma F_3edbc : fetch_word Asan.M.loaded_segments (0x3edbc : word) = Some W_3edbc.
Proof. vm_refl. Qed.
Lemma D_3edbc : decode_any W_3edbc = Some (Branch BC_EQ 11 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edc0 : bv 32 := 0x00000513.
Lemma F_3edc0 : fetch_word Asan.M.loaded_segments (0x3edc0 : word) = Some W_3edc0.
Proof. vm_refl. Qed.
Lemma D_3edc0 : decode_any W_3edc0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edc4 : bv 32 := 0x01813083.
Lemma F_3edc4 : fetch_word Asan.M.loaded_segments (0x3edc4 : word) = Some W_3edc4.
Proof. vm_refl. Qed.
Lemma D_3edc4 : decode_any W_3edc4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edc8 : bv 32 := 0x01013403.
Lemma F_3edc8 : fetch_word Asan.M.loaded_segments (0x3edc8 : word) = Some W_3edc8.
Proof. vm_refl. Qed.
Lemma D_3edc8 : decode_any W_3edc8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edcc : bv 32 := 0x00813483.
Lemma F_3edcc : fetch_word Asan.M.loaded_segments (0x3edcc : word) = Some W_3edcc.
Proof. vm_refl. Qed.
Lemma D_3edcc : decode_any W_3edcc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edd0 : bv 32 := 0x00013903.
Lemma F_3edd0 : fetch_word Asan.M.loaded_segments (0x3edd0 : word) = Some W_3edd0.
Proof. vm_refl. Qed.
Lemma D_3edd0 : decode_any W_3edd0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edd4 : bv 32 := 0x02010113.
Lemma F_3edd4 : fetch_word Asan.M.loaded_segments (0x3edd4 : word) = Some W_3edd4.
Proof. vm_refl. Qed.
Lemma D_3edd4 : decode_any W_3edd4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edd8 : bv 32 := 0x00008067.
Lemma F_3edd8 : fetch_word Asan.M.loaded_segments (0x3edd8 : word) = Some W_3edd8.
Proof. vm_refl. Qed.
Lemma D_3edd8 : decode_any W_3edd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eddc : bv 32 := 0x01813083.
Lemma F_3eddc : fetch_word Asan.M.loaded_segments (0x3eddc : word) = Some W_3eddc.
Proof. vm_refl. Qed.
Lemma D_3eddc : decode_any W_3eddc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ede0 : bv 32 := 0x01013403.
Lemma F_3ede0 : fetch_word Asan.M.loaded_segments (0x3ede0 : word) = Some W_3ede0.
Proof. vm_refl. Qed.
Lemma D_3ede0 : decode_any W_3ede0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ede4 : bv 32 := 0x00813483.
Lemma F_3ede4 : fetch_word Asan.M.loaded_segments (0x3ede4 : word) = Some W_3ede4.
Proof. vm_refl. Qed.
Lemma D_3ede4 : decode_any W_3ede4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ede8 : bv 32 := 0x00013903.
Lemma F_3ede8 : fetch_word Asan.M.loaded_segments (0x3ede8 : word) = Some W_3ede8.
Proof. vm_refl. Qed.
Lemma D_3ede8 : decode_any W_3ede8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edec : bv 32 := 0x02010113.
Lemma F_3edec : fetch_word Asan.M.loaded_segments (0x3edec : word) = Some W_3edec.
Proof. vm_refl. Qed.
Lemma D_3edec : decode_any W_3edec = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edf0 : bv 32 := 0x00008067.
Lemma F_3edf0 : fetch_word Asan.M.loaded_segments (0x3edf0 : word) = Some W_3edf0.
Proof. vm_refl. Qed.
Lemma D_3edf0 : decode_any W_3edf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edf4 : bv 32 := 0x00160613.
Lemma F_3edf4 : fetch_word Asan.M.loaded_segments (0x3edf4 : word) = Some W_3edf4.
Proof. vm_refl. Qed.
Lemma D_3edf4 : decode_any W_3edf4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edf8 : bv 32 := 0x00100513.
Lemma F_3edf8 : fetch_word Asan.M.loaded_segments (0x3edf8 : word) = Some W_3edf8.
Proof. vm_refl. Qed.
Lemma D_3edf8 : decode_any W_3edf8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3edfc : bv 32 := 0xffb90913.
Lemma F_3edfc : fetch_word Asan.M.loaded_segments (0x3edfc : word) = Some W_3edfc.
Proof. vm_refl. Qed.
Lemma D_3edfc : decode_any W_3edfc = Some (OpImm ALU_ADD 18 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee00 : bv 32 := 0x00681813.
Lemma F_3ee00 : fetch_word Asan.M.loaded_segments (0x3ee00 : word) = Some W_3ee00.
Proof. vm_refl. Qed.
Lemma D_3ee00 : decode_any W_3ee00 = Some (ShiftImm ALU_SLL 16 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee04 : bv 32 := 0x00c4b023.
Lemma F_3ee04 : fetch_word Asan.M.loaded_segments (0x3ee04 : word) = Some W_3ee04.
Proof. vm_refl. Qed.
Lemma D_3ee04 : decode_any W_3ee04 = Some (Store SZ8 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee08 : bv 32 := 0x00a78023.
Lemma F_3ee08 : fetch_word Asan.M.loaded_segments (0x3ee08 : word) = Some W_3ee08.
Proof. vm_refl. Qed.
Lemma D_3ee08 : decode_any W_3ee08 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee0c : bv 32 := 0x01251533.
Lemma F_3ee0c : fetch_word Asan.M.loaded_segments (0x3ee0c : word) = Some W_3ee0c.
Proof. vm_refl. Qed.
Lemma D_3ee0c : decode_any W_3ee0c = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee10 : bv 32 := 0x00a58533.
Lemma F_3ee10 : fetch_word Asan.M.loaded_segments (0x3ee10 : word) = Some W_3ee10.
Proof. vm_refl. Qed.
Lemma D_3ee10 : decode_any W_3ee10 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee14 : bv 32 := 0x010504b3.
Lemma F_3ee14 : fetch_word Asan.M.loaded_segments (0x3ee14 : word) = Some W_3ee14.
Proof. vm_refl. Qed.
Lemma D_3ee14 : decode_any W_3ee14 = Some (Op ALU_ADD 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee18 : bv 32 := 0x0084bc23.
Lemma F_3ee18 : fetch_word Asan.M.loaded_segments (0x3ee18 : word) = Some W_3ee18.
Proof. vm_refl. Qed.
Lemma D_3ee18 : decode_any W_3ee18 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee1c : bv 32 := 0x02f4bc23.
Lemma F_3ee1c : fetch_word Asan.M.loaded_segments (0x3ee1c : word) = Some W_3ee1c.
Proof. vm_refl. Qed.
Lemma D_3ee1c : decode_any W_3ee1c = Some (Store SZ8 9 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee20 : bv 32 := 0x00048513.
Lemma F_3ee20 : fetch_word Asan.M.loaded_segments (0x3ee20 : word) = Some W_3ee20.
Proof. vm_refl. Qed.
Lemma D_3ee20 : decode_any W_3ee20 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee24 : bv 32 := 0x6ec000ef.
Lemma F_3ee24 : fetch_word Asan.M.loaded_segments (0x3ee24 : word) = Some W_3ee24.
Proof. vm_refl. Qed.
Lemma D_3ee24 : decode_any W_3ee24 = Some (Jal 1 1772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee28 : bv 32 := 0x00050593.
Lemma F_3ee28 : fetch_word Asan.M.loaded_segments (0x3ee28 : word) = Some W_3ee28.
Proof. vm_refl. Qed.
Lemma D_3ee28 : decode_any W_3ee28 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee2c : bv 32 := 0x00048513.
Lemma F_3ee2c : fetch_word Asan.M.loaded_segments (0x3ee2c : word) = Some W_3ee2c.
Proof. vm_refl. Qed.
Lemma D_3ee2c : decode_any W_3ee2c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee30 : bv 32 := 0x00000613.
Lemma F_3ee30 : fetch_word Asan.M.loaded_segments (0x3ee30 : word) = Some W_3ee30.
Proof. vm_refl. Qed.
Lemma D_3ee30 : decode_any W_3ee30 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee34 : bv 32 := 0x0005b023.
Lemma F_3ee34 : fetch_word Asan.M.loaded_segments (0x3ee34 : word) = Some W_3ee34.
Proof. vm_refl. Qed.
Lemma D_3ee34 : decode_any W_3ee34 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee38 : bv 32 := 0x01813083.
Lemma F_3ee38 : fetch_word Asan.M.loaded_segments (0x3ee38 : word) = Some W_3ee38.
Proof. vm_refl. Qed.
Lemma D_3ee38 : decode_any W_3ee38 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee3c : bv 32 := 0x01013403.
Lemma F_3ee3c : fetch_word Asan.M.loaded_segments (0x3ee3c : word) = Some W_3ee3c.
Proof. vm_refl. Qed.
Lemma D_3ee3c : decode_any W_3ee3c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee40 : bv 32 := 0x00813483.
Lemma F_3ee40 : fetch_word Asan.M.loaded_segments (0x3ee40 : word) = Some W_3ee40.
Proof. vm_refl. Qed.
Lemma D_3ee40 : decode_any W_3ee40 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee44 : bv 32 := 0x00013903.
Lemma F_3ee44 : fetch_word Asan.M.loaded_segments (0x3ee44 : word) = Some W_3ee44.
Proof. vm_refl. Qed.
Lemma D_3ee44 : decode_any W_3ee44 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee48 : bv 32 := 0x02010113.
Lemma F_3ee48 : fetch_word Asan.M.loaded_segments (0x3ee48 : word) = Some W_3ee48.
Proof. vm_refl. Qed.
Lemma D_3ee48 : decode_any W_3ee48 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee4c : bv 32 := 0x00008067.
Lemma F_3ee4c : fetch_word Asan.M.loaded_segments (0x3ee4c : word) = Some W_3ee4c.
Proof. vm_refl. Qed.
Lemma D_3ee4c : decode_any W_3ee4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_3ee6c : bv 32 := 0xfe010113.
Lemma F_3ee6c : fetch_word Asan.M.loaded_segments (0x3ee6c : word) = Some W_3ee6c.
Proof. vm_refl. Qed.
Lemma D_3ee6c : decode_any W_3ee6c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee70 : bv 32 := 0x00113c23.
Lemma F_3ee70 : fetch_word Asan.M.loaded_segments (0x3ee70 : word) = Some W_3ee70.
Proof. vm_refl. Qed.
Lemma D_3ee70 : decode_any W_3ee70 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee74 : bv 32 := 0x00813823.
Lemma F_3ee74 : fetch_word Asan.M.loaded_segments (0x3ee74 : word) = Some W_3ee74.
Proof. vm_refl. Qed.
Lemma D_3ee74 : decode_any W_3ee74 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee78 : bv 32 := 0x00913423.
Lemma F_3ee78 : fetch_word Asan.M.loaded_segments (0x3ee78 : word) = Some W_3ee78.
Proof. vm_refl. Qed.
Lemma D_3ee78 : decode_any W_3ee78 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee7c : bv 32 := 0x01213023.
Lemma F_3ee7c : fetch_word Asan.M.loaded_segments (0x3ee7c : word) = Some W_3ee7c.
Proof. vm_refl. Qed.
Lemma D_3ee7c : decode_any W_3ee7c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee80 : bv 32 := 0x02010413.
Lemma F_3ee80 : fetch_word Asan.M.loaded_segments (0x3ee80 : word) = Some W_3ee80.
Proof. vm_refl. Qed.
Lemma D_3ee80 : decode_any W_3ee80 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee84 : bv 32 := 0x0006d517.
Lemma F_3ee84 : fetch_word Asan.M.loaded_segments (0x3ee84 : word) = Some W_3ee84.
Proof. vm_refl. Qed.
Lemma D_3ee84 : decode_any W_3ee84 = Some (Auipc 10 109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee88 : bv 32 := 0xcdc50513.
Lemma F_3ee88 : fetch_word Asan.M.loaded_segments (0x3ee88 : word) = Some W_3ee88.
Proof. vm_refl. Qed.
Lemma D_3ee88 : decode_any W_3ee88 = Some (OpImm ALU_ADD 10 10 3292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee8c : bv 32 := 0x400050ef.
Lemma F_3ee8c : fetch_word Asan.M.loaded_segments (0x3ee8c : word) = Some W_3ee8c.
Proof. vm_refl. Qed.
Lemma D_3ee8c : decode_any W_3ee8c = Some (Jal 1 21504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee90 : bv 32 := 0x00053483.
Lemma F_3ee90 : fetch_word Asan.M.loaded_segments (0x3ee90 : word) = Some W_3ee90.
Proof. vm_refl. Qed.
Lemma D_3ee90 : decode_any W_3ee90 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee94 : bv 32 := 0x08048863.
Lemma F_3ee94 : fetch_word Asan.M.loaded_segments (0x3ee94 : word) = Some W_3ee94.
Proof. vm_refl. Qed.
Lemma D_3ee94 : decode_any W_3ee94 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee98 : bv 32 := 0x0604c503.
Lemma F_3ee98 : fetch_word Asan.M.loaded_segments (0x3ee98 : word) = Some W_3ee98.
Proof. vm_refl. Qed.
Lemma D_3ee98 : decode_any W_3ee98 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ee9c : bv 32 := 0x0584b903.
Lemma F_3ee9c : fetch_word Asan.M.loaded_segments (0x3ee9c : word) = Some W_3ee9c.
Proof. vm_refl. Qed.
Lemma D_3ee9c : decode_any W_3ee9c = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eea0 : bv 32 := 0x00050863.
Lemma F_3eea0 : fetch_word Asan.M.loaded_segments (0x3eea0 : word) = Some W_3eea0.
Proof. vm_refl. Qed.
Lemma D_3eea0 : decode_any W_3eea0 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eea4 : bv 32 := 0x00048513.
Lemma F_3eea4 : fetch_word Asan.M.loaded_segments (0x3eea4 : word) = Some W_3eea4.
Proof. vm_refl. Qed.
Lemma D_3eea4 : decode_any W_3eea4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eea8 : bv 32 := 0x00040593.
Lemma F_3eea8 : fetch_word Asan.M.loaded_segments (0x3eea8 : word) = Some W_3eea8.
Proof. vm_refl. Qed.
Lemma D_3eea8 : decode_any W_3eea8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eeac : bv 32 := 0xa01ff0ef.
Lemma F_3eeac : fetch_word Asan.M.loaded_segments (0x3eeac : word) = Some W_3eeac.
Proof. vm_refl. Qed.
Lemma D_3eeac : decode_any W_3eeac = Some (Jal 1 2095616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eeb0 : bv 32 := 0xff990593.
Lemma F_3eeb0 : fetch_word Asan.M.loaded_segments (0x3eeb0 : word) = Some W_3eeb0.
Proof. vm_refl. Qed.
Lemma D_3eeb0 : decode_any W_3eeb0 = Some (OpImm ALU_ADD 11 18 4089, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eeb4 : bv 32 := 0x00100513.
Lemma F_3eeb4 : fetch_word Asan.M.loaded_segments (0x3eeb4 : word) = Some W_3eeb4.
Proof. vm_refl. Qed.
Lemma D_3eeb4 : decode_any W_3eeb4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eeb8 : bv 32 := 0x00b51533.
Lemma F_3eeb8 : fetch_word Asan.M.loaded_segments (0x3eeb8 : word) = Some W_3eeb8.
Proof. vm_refl. Qed.
Lemma D_3eeb8 : decode_any W_3eeb8 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eebc : bv 32 := 0x0005061b.
Lemma F_3eebc : fetch_word Asan.M.loaded_segments (0x3eebc : word) = Some W_3eebc.
Proof. vm_refl. Qed.
Lemma D_3eebc : decode_any W_3eebc = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eec0 : bv 32 := 0x08c05263.
Lemma F_3eec0 : fetch_word Asan.M.loaded_segments (0x3eec0 : word) = Some W_3eec0.
Proof. vm_refl. Qed.
Lemma D_3eec0 : decode_any W_3eec0 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eec4 : bv 32 := 0x000016b7.
Lemma F_3eec4 : fetch_word Asan.M.loaded_segments (0x3eec4 : word) = Some W_3eec4.
Proof. vm_refl. Qed.
Lemma D_3eec4 : decode_any W_3eec4 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eec8 : bv 32 := 0xff190613.
Lemma F_3eec8 : fetch_word Asan.M.loaded_segments (0x3eec8 : word) = Some W_3eec8.
Proof. vm_refl. Qed.
Lemma D_3eec8 : decode_any W_3eec8 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eecc : bv 32 := 0x20000713.
Lemma F_3eecc : fetch_word Asan.M.loaded_segments (0x3eecc : word) = Some W_3eecc.
Proof. vm_refl. Qed.
Lemma D_3eecc : decode_any W_3eecc = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eed0 : bv 32 := 0xfff00793.
Lemma F_3eed0 : fetch_word Asan.M.loaded_segments (0x3eed0 : word) = Some W_3eed0.
Proof. vm_refl. Qed.
Lemma D_3eed0 : decode_any W_3eed0 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eed4 : bv 32 := 0x00c71733.
Lemma F_3eed4 : fetch_word Asan.M.loaded_segments (0x3eed4 : word) = Some W_3eed4.
Proof. vm_refl. Qed.
Lemma D_3eed4 : decode_any W_3eed4 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eed8 : bv 32 := 0x0084b603.
Lemma F_3eed8 : fetch_word Asan.M.loaded_segments (0x3eed8 : word) = Some W_3eed8.
Proof. vm_refl. Qed.
Lemma D_3eed8 : decode_any W_3eed8 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eedc : bv 32 := 0x00b797b3.
Lemma F_3eedc : fetch_word Asan.M.loaded_segments (0x3eedc : word) = Some W_3eedc.
Proof. vm_refl. Qed.
Lemma D_3eedc : decode_any W_3eedc = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eee0 : bv 32 := 0xfff50813.
Lemma F_3eee0 : fetch_word Asan.M.loaded_segments (0x3eee0 : word) = Some W_3eee0.
Proof. vm_refl. Qed.
Lemma D_3eee0 : decode_any W_3eee0 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eee4 : bv 32 := 0x00d485b3.
Lemma F_3eee4 : fetch_word Asan.M.loaded_segments (0x3eee4 : word) = Some W_3eee4.
Proof. vm_refl. Qed.
Lemma D_3eee4 : decode_any W_3eee4 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eee8 : bv 32 := 0x00e586b3.
Lemma F_3eee8 : fetch_word Asan.M.loaded_segments (0x3eee8 : word) = Some W_3eee8.
Proof. vm_refl. Qed.
Lemma D_3eee8 : decode_any W_3eee8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eeec : bv 32 := 0xfff7c713.
Lemma F_3eeec : fetch_word Asan.M.loaded_segments (0x3eeec : word) = Some W_3eeec.
Proof. vm_refl. Qed.
Lemma D_3eeec : decode_any W_3eeec = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eef0 : bv 32 := 0x02081813.
Lemma F_3eef0 : fetch_word Asan.M.loaded_segments (0x3eef0 : word) = Some W_3eef0.
Proof. vm_refl. Qed.
Lemma D_3eef0 : decode_any W_3eef0 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eef4 : bv 32 := 0x02085793.
Lemma F_3eef4 : fetch_word Asan.M.loaded_segments (0x3eef4 : word) = Some W_3eef4.
Proof. vm_refl. Qed.
Lemma D_3eef4 : decode_any W_3eef4 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eef8 : bv 32 := 0x00f607b3.
Lemma F_3eef8 : fetch_word Asan.M.loaded_segments (0x3eef8 : word) = Some W_3eef8.
Proof. vm_refl. Qed.
Lemma D_3eef8 : decode_any W_3eef8 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3eefc : bv 32 := 0x00178813.
Lemma F_3eefc : fetch_word Asan.M.loaded_segments (0x3eefc : word) = Some W_3eefc.
Proof. vm_refl. Qed.
Lemma D_3eefc : decode_any W_3eefc = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef00 : bv 32 := 0x00e678b3.
Lemma F_3ef00 : fetch_word Asan.M.loaded_segments (0x3ef00 : word) = Some W_3ef00.
Proof. vm_refl. Qed.
Lemma D_3ef00 : decode_any W_3ef00 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef04 : bv 32 := 0x011687b3.
Lemma F_3ef04 : fetch_word Asan.M.loaded_segments (0x3ef04 : word) = Some W_3ef04.
Proof. vm_refl. Qed.
Lemma D_3ef04 : decode_any W_3ef04 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef08 : bv 32 := 0x0007c283.
Lemma F_3ef08 : fetch_word Asan.M.loaded_segments (0x3ef08 : word) = Some W_3ef08.
Proof. vm_refl. Qed.
Lemma D_3ef08 : decode_any W_3ef08 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef0c : bv 32 := 0x06028663.
Lemma F_3ef0c : fetch_word Asan.M.loaded_segments (0x3ef0c : word) = Some W_3ef0c.
Proof. vm_refl. Qed.
Lemma D_3ef0c : decode_any W_3ef0c = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef10 : bv 32 := 0xfff5051b.
Lemma F_3ef10 : fetch_word Asan.M.loaded_segments (0x3ef10 : word) = Some W_3ef10.
Proof. vm_refl. Qed.
Lemma D_3ef10 : decode_any W_3ef10 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef14 : bv 32 := 0x00160613.
Lemma F_3ef14 : fetch_word Asan.M.loaded_segments (0x3ef14 : word) = Some W_3ef14.
Proof. vm_refl. Qed.
Lemma D_3ef14 : decode_any W_3ef14 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef18 : bv 32 := 0xfe0514e3.
Lemma F_3ef18 : fetch_word Asan.M.loaded_segments (0x3ef18 : word) = Some W_3ef18.
Proof. vm_refl. Qed.
Lemma D_3ef18 : decode_any W_3ef18 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef1c : bv 32 := 0x0104b423.
Lemma F_3ef1c : fetch_word Asan.M.loaded_segments (0x3ef1c : word) = Some W_3ef1c.
Proof. vm_refl. Qed.
Lemma D_3ef1c : decode_any W_3ef1c = Some (Store SZ8 9 16 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef20 : bv 32 := 0x0400006f.
Lemma F_3ef20 : fetch_word Asan.M.loaded_segments (0x3ef20 : word) = Some W_3ef20.
Proof. vm_refl. Qed.
Lemma D_3ef20 : decode_any W_3ef20 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef24 : bv 32 := 0x0006c517.
Lemma F_3ef24 : fetch_word Asan.M.loaded_segments (0x3ef24 : word) = Some W_3ef24.
Proof. vm_refl. Qed.
Lemma D_3ef24 : decode_any W_3ef24 = Some (Auipc 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef28 : bv 32 := 0xfb453503.
Lemma F_3ef28 : fetch_word Asan.M.loaded_segments (0x3ef28 : word) = Some W_3ef28.
Proof. vm_refl. Qed.
Lemma D_3ef28 : decode_any W_3ef28 = Some (Load SZ8 true 10 10 4020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef2c : bv 32 := 0x00052503.
Lemma F_3ef2c : fetch_word Asan.M.loaded_segments (0x3ef2c : word) = Some W_3ef2c.
Proof. vm_refl. Qed.
Lemma D_3ef2c : decode_any W_3ef2c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef30 : bv 32 := 0x02050863.
Lemma F_3ef30 : fetch_word Asan.M.loaded_segments (0x3ef30 : word) = Some W_3ef30.
Proof. vm_refl. Qed.
Lemma D_3ef30 : decode_any W_3ef30 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef34 : bv 32 := 0x70c1f0ef.
Lemma F_3ef34 : fetch_word Asan.M.loaded_segments (0x3ef34 : word) = Some W_3ef34.
Proof. vm_refl. Qed.
Lemma D_3ef34 : decode_any W_3ef34 = Some (Jal 1 128780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef38 : bv 32 := 0x02050463.
Lemma F_3ef38 : fetch_word Asan.M.loaded_segments (0x3ef38 : word) = Some W_3ef38.
Proof. vm_refl. Qed.
Lemma D_3ef38 : decode_any W_3ef38 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef3c : bv 32 := 0x02850583.
Lemma F_3ef3c : fetch_word Asan.M.loaded_segments (0x3ef3c : word) = Some W_3ef3c.
Proof. vm_refl. Qed.
Lemma D_3ef3c : decode_any W_3ef3c = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef40 : bv 32 := 0x0a058063.
Lemma F_3ef40 : fetch_word Asan.M.loaded_segments (0x3ef40 : word) = Some W_3ef40.
Proof. vm_refl. Qed.
Lemma D_3ef40 : decode_any W_3ef40 = Some (Branch BC_EQ 11 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef44 : bv 32 := 0x00000513.
Lemma F_3ef44 : fetch_word Asan.M.loaded_segments (0x3ef44 : word) = Some W_3ef44.
Proof. vm_refl. Qed.
Lemma D_3ef44 : decode_any W_3ef44 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef48 : bv 32 := 0x01813083.
Lemma F_3ef48 : fetch_word Asan.M.loaded_segments (0x3ef48 : word) = Some W_3ef48.
Proof. vm_refl. Qed.
Lemma D_3ef48 : decode_any W_3ef48 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef4c : bv 32 := 0x01013403.
Lemma F_3ef4c : fetch_word Asan.M.loaded_segments (0x3ef4c : word) = Some W_3ef4c.
Proof. vm_refl. Qed.
Lemma D_3ef4c : decode_any W_3ef4c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef50 : bv 32 := 0x00813483.
Lemma F_3ef50 : fetch_word Asan.M.loaded_segments (0x3ef50 : word) = Some W_3ef50.
Proof. vm_refl. Qed.
Lemma D_3ef50 : decode_any W_3ef50 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef54 : bv 32 := 0x00013903.
Lemma F_3ef54 : fetch_word Asan.M.loaded_segments (0x3ef54 : word) = Some W_3ef54.
Proof. vm_refl. Qed.
Lemma D_3ef54 : decode_any W_3ef54 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef58 : bv 32 := 0x02010113.
Lemma F_3ef58 : fetch_word Asan.M.loaded_segments (0x3ef58 : word) = Some W_3ef58.
Proof. vm_refl. Qed.
Lemma D_3ef58 : decode_any W_3ef58 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef5c : bv 32 := 0x00008067.
Lemma F_3ef5c : fetch_word Asan.M.loaded_segments (0x3ef5c : word) = Some W_3ef5c.
Proof. vm_refl. Qed.
Lemma D_3ef5c : decode_any W_3ef5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef60 : bv 32 := 0x01813083.
Lemma F_3ef60 : fetch_word Asan.M.loaded_segments (0x3ef60 : word) = Some W_3ef60.
Proof. vm_refl. Qed.
Lemma D_3ef60 : decode_any W_3ef60 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef64 : bv 32 := 0x01013403.
Lemma F_3ef64 : fetch_word Asan.M.loaded_segments (0x3ef64 : word) = Some W_3ef64.
Proof. vm_refl. Qed.
Lemma D_3ef64 : decode_any W_3ef64 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef68 : bv 32 := 0x00813483.
Lemma F_3ef68 : fetch_word Asan.M.loaded_segments (0x3ef68 : word) = Some W_3ef68.
Proof. vm_refl. Qed.
Lemma D_3ef68 : decode_any W_3ef68 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef6c : bv 32 := 0x00013903.
Lemma F_3ef6c : fetch_word Asan.M.loaded_segments (0x3ef6c : word) = Some W_3ef6c.
Proof. vm_refl. Qed.
Lemma D_3ef6c : decode_any W_3ef6c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef70 : bv 32 := 0x02010113.
Lemma F_3ef70 : fetch_word Asan.M.loaded_segments (0x3ef70 : word) = Some W_3ef70.
Proof. vm_refl. Qed.
Lemma D_3ef70 : decode_any W_3ef70 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef74 : bv 32 := 0x00008067.
Lemma F_3ef74 : fetch_word Asan.M.loaded_segments (0x3ef74 : word) = Some W_3ef74.
Proof. vm_refl. Qed.
Lemma D_3ef74 : decode_any W_3ef74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef78 : bv 32 := 0x00160613.
Lemma F_3ef78 : fetch_word Asan.M.loaded_segments (0x3ef78 : word) = Some W_3ef78.
Proof. vm_refl. Qed.
Lemma D_3ef78 : decode_any W_3ef78 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef7c : bv 32 := 0x00100513.
Lemma F_3ef7c : fetch_word Asan.M.loaded_segments (0x3ef7c : word) = Some W_3ef7c.
Proof. vm_refl. Qed.
Lemma D_3ef7c : decode_any W_3ef7c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef80 : bv 32 := 0xffb90693.
Lemma F_3ef80 : fetch_word Asan.M.loaded_segments (0x3ef80 : word) = Some W_3ef80.
Proof. vm_refl. Qed.
Lemma D_3ef80 : decode_any W_3ef80 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef84 : bv 32 := 0x00789893.
Lemma F_3ef84 : fetch_word Asan.M.loaded_segments (0x3ef84 : word) = Some W_3ef84.
Proof. vm_refl. Qed.
Lemma D_3ef84 : decode_any W_3ef84 = Some (ShiftImm ALU_SLL 17 17 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef88 : bv 32 := 0x00c4b423.
Lemma F_3ef88 : fetch_word Asan.M.loaded_segments (0x3ef88 : word) = Some W_3ef88.
Proof. vm_refl. Qed.
Lemma D_3ef88 : decode_any W_3ef88 = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef8c : bv 32 := 0x00a78023.
Lemma F_3ef8c : fetch_word Asan.M.loaded_segments (0x3ef8c : word) = Some W_3ef8c.
Proof. vm_refl. Qed.
Lemma D_3ef8c : decode_any W_3ef8c = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef90 : bv 32 := 0x00d51633.
Lemma F_3ef90 : fetch_word Asan.M.loaded_segments (0x3ef90 : word) = Some W_3ef90.
Proof. vm_refl. Qed.
Lemma D_3ef90 : decode_any W_3ef90 = Some (Op ALU_SLL 12 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef94 : bv 32 := 0x01251533.
Lemma F_3ef94 : fetch_word Asan.M.loaded_segments (0x3ef94 : word) = Some W_3ef94.
Proof. vm_refl. Qed.
Lemma D_3ef94 : decode_any W_3ef94 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef98 : bv 32 := 0x00c585b3.
Lemma F_3ef98 : fetch_word Asan.M.loaded_segments (0x3ef98 : word) = Some W_3ef98.
Proof. vm_refl. Qed.
Lemma D_3ef98 : decode_any W_3ef98 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ef9c : bv 32 := 0x01150533.
Lemma F_3ef9c : fetch_word Asan.M.loaded_segments (0x3ef9c : word) = Some W_3ef9c.
Proof. vm_refl. Qed.
Lemma D_3ef9c : decode_any W_3ef9c = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efa0 : bv 32 := 0x00a584b3.
Lemma F_3efa0 : fetch_word Asan.M.loaded_segments (0x3efa0 : word) = Some W_3efa0.
Proof. vm_refl. Qed.
Lemma D_3efa0 : decode_any W_3efa0 = Some (Op ALU_ADD 9 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efa4 : bv 32 := 0x0084bc23.
Lemma F_3efa4 : fetch_word Asan.M.loaded_segments (0x3efa4 : word) = Some W_3efa4.
Proof. vm_refl. Qed.
Lemma D_3efa4 : decode_any W_3efa4 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efa8 : bv 32 := 0x06f4bc23.
Lemma F_3efa8 : fetch_word Asan.M.loaded_segments (0x3efa8 : word) = Some W_3efa8.
Proof. vm_refl. Qed.
Lemma D_3efa8 : decode_any W_3efa8 = Some (Store SZ8 9 15 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efac : bv 32 := 0x00048513.
Lemma F_3efac : fetch_word Asan.M.loaded_segments (0x3efac : word) = Some W_3efac.
Proof. vm_refl. Qed.
Lemma D_3efac : decode_any W_3efac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efb0 : bv 32 := 0x560000ef.
Lemma F_3efb0 : fetch_word Asan.M.loaded_segments (0x3efb0 : word) = Some W_3efb0.
Proof. vm_refl. Qed.
Lemma D_3efb0 : decode_any W_3efb0 = Some (Jal 1 1376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efb4 : bv 32 := 0x00050593.
Lemma F_3efb4 : fetch_word Asan.M.loaded_segments (0x3efb4 : word) = Some W_3efb4.
Proof. vm_refl. Qed.
Lemma D_3efb4 : decode_any W_3efb4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efb8 : bv 32 := 0x00048513.
Lemma F_3efb8 : fetch_word Asan.M.loaded_segments (0x3efb8 : word) = Some W_3efb8.
Proof. vm_refl. Qed.
Lemma D_3efb8 : decode_any W_3efb8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efbc : bv 32 := 0x00000613.
Lemma F_3efbc : fetch_word Asan.M.loaded_segments (0x3efbc : word) = Some W_3efbc.
Proof. vm_refl. Qed.
Lemma D_3efbc : decode_any W_3efbc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efc0 : bv 32 := 0x0005b023.
Lemma F_3efc0 : fetch_word Asan.M.loaded_segments (0x3efc0 : word) = Some W_3efc0.
Proof. vm_refl. Qed.
Lemma D_3efc0 : decode_any W_3efc0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efc4 : bv 32 := 0x0005b423.
Lemma F_3efc4 : fetch_word Asan.M.loaded_segments (0x3efc4 : word) = Some W_3efc4.
Proof. vm_refl. Qed.
Lemma D_3efc4 : decode_any W_3efc4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efc8 : bv 32 := 0x01813083.
Lemma F_3efc8 : fetch_word Asan.M.loaded_segments (0x3efc8 : word) = Some W_3efc8.
Proof. vm_refl. Qed.
Lemma D_3efc8 : decode_any W_3efc8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efcc : bv 32 := 0x01013403.
Lemma F_3efcc : fetch_word Asan.M.loaded_segments (0x3efcc : word) = Some W_3efcc.
Proof. vm_refl. Qed.
Lemma D_3efcc : decode_any W_3efcc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efd0 : bv 32 := 0x00813483.
Lemma F_3efd0 : fetch_word Asan.M.loaded_segments (0x3efd0 : word) = Some W_3efd0.
Proof. vm_refl. Qed.
Lemma D_3efd0 : decode_any W_3efd0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efd4 : bv 32 := 0x00013903.
Lemma F_3efd4 : fetch_word Asan.M.loaded_segments (0x3efd4 : word) = Some W_3efd4.
Proof. vm_refl. Qed.
Lemma D_3efd4 : decode_any W_3efd4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efd8 : bv 32 := 0x02010113.
Lemma F_3efd8 : fetch_word Asan.M.loaded_segments (0x3efd8 : word) = Some W_3efd8.
Proof. vm_refl. Qed.
Lemma D_3efd8 : decode_any W_3efd8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3efdc : bv 32 := 0x00008067.
Lemma F_3efdc : fetch_word Asan.M.loaded_segments (0x3efdc : word) = Some W_3efdc.
Proof. vm_refl. Qed.
Lemma D_3efdc : decode_any W_3efdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_3effc : bv 32 := 0xfe010113.
Lemma F_3effc : fetch_word Asan.M.loaded_segments (0x3effc : word) = Some W_3effc.
Proof. vm_refl. Qed.
Lemma D_3effc : decode_any W_3effc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f000 : bv 32 := 0x00113c23.
Lemma F_3f000 : fetch_word Asan.M.loaded_segments (0x3f000 : word) = Some W_3f000.
Proof. vm_refl. Qed.
Lemma D_3f000 : decode_any W_3f000 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f004 : bv 32 := 0x00813823.
Lemma F_3f004 : fetch_word Asan.M.loaded_segments (0x3f004 : word) = Some W_3f004.
Proof. vm_refl. Qed.
Lemma D_3f004 : decode_any W_3f004 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f008 : bv 32 := 0x00913423.
Lemma F_3f008 : fetch_word Asan.M.loaded_segments (0x3f008 : word) = Some W_3f008.
Proof. vm_refl. Qed.
Lemma D_3f008 : decode_any W_3f008 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f00c : bv 32 := 0x01213023.
Lemma F_3f00c : fetch_word Asan.M.loaded_segments (0x3f00c : word) = Some W_3f00c.
Proof. vm_refl. Qed.
Lemma D_3f00c : decode_any W_3f00c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f010 : bv 32 := 0x02010413.
Lemma F_3f010 : fetch_word Asan.M.loaded_segments (0x3f010 : word) = Some W_3f010.
Proof. vm_refl. Qed.
Lemma D_3f010 : decode_any W_3f010 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f014 : bv 32 := 0x0006d517.
Lemma F_3f014 : fetch_word Asan.M.loaded_segments (0x3f014 : word) = Some W_3f014.
Proof. vm_refl. Qed.
Lemma D_3f014 : decode_any W_3f014 = Some (Auipc 10 109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f018 : bv 32 := 0xb4c50513.
Lemma F_3f018 : fetch_word Asan.M.loaded_segments (0x3f018 : word) = Some W_3f018.
Proof. vm_refl. Qed.
Lemma D_3f018 : decode_any W_3f018 = Some (OpImm ALU_ADD 10 10 2892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f01c : bv 32 := 0x270050ef.
Lemma F_3f01c : fetch_word Asan.M.loaded_segments (0x3f01c : word) = Some W_3f01c.
Proof. vm_refl. Qed.
Lemma D_3f01c : decode_any W_3f01c = Some (Jal 1 21104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f020 : bv 32 := 0x00053483.
Lemma F_3f020 : fetch_word Asan.M.loaded_segments (0x3f020 : word) = Some W_3f020.
Proof. vm_refl. Qed.
Lemma D_3f020 : decode_any W_3f020 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f024 : bv 32 := 0x08048863.
Lemma F_3f024 : fetch_word Asan.M.loaded_segments (0x3f024 : word) = Some W_3f024.
Proof. vm_refl. Qed.
Lemma D_3f024 : decode_any W_3f024 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f028 : bv 32 := 0x0604c503.
Lemma F_3f028 : fetch_word Asan.M.loaded_segments (0x3f028 : word) = Some W_3f028.
Proof. vm_refl. Qed.
Lemma D_3f028 : decode_any W_3f028 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f02c : bv 32 := 0x0584b903.
Lemma F_3f02c : fetch_word Asan.M.loaded_segments (0x3f02c : word) = Some W_3f02c.
Proof. vm_refl. Qed.
Lemma D_3f02c : decode_any W_3f02c = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f030 : bv 32 := 0x00050863.
Lemma F_3f030 : fetch_word Asan.M.loaded_segments (0x3f030 : word) = Some W_3f030.
Proof. vm_refl. Qed.
Lemma D_3f030 : decode_any W_3f030 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f034 : bv 32 := 0x00048513.
Lemma F_3f034 : fetch_word Asan.M.loaded_segments (0x3f034 : word) = Some W_3f034.
Proof. vm_refl. Qed.
Lemma D_3f034 : decode_any W_3f034 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f038 : bv 32 := 0x00040593.
Lemma F_3f038 : fetch_word Asan.M.loaded_segments (0x3f038 : word) = Some W_3f038.
Proof. vm_refl. Qed.
Lemma D_3f038 : decode_any W_3f038 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f03c : bv 32 := 0x871ff0ef.
Lemma F_3f03c : fetch_word Asan.M.loaded_segments (0x3f03c : word) = Some W_3f03c.
Proof. vm_refl. Qed.
Lemma D_3f03c : decode_any W_3f03c = Some (Jal 1 2095216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f040 : bv 32 := 0xff890593.
Lemma F_3f040 : fetch_word Asan.M.loaded_segments (0x3f040 : word) = Some W_3f040.
Proof. vm_refl. Qed.
Lemma D_3f040 : decode_any W_3f040 = Some (OpImm ALU_ADD 11 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f044 : bv 32 := 0x00100513.
Lemma F_3f044 : fetch_word Asan.M.loaded_segments (0x3f044 : word) = Some W_3f044.
Proof. vm_refl. Qed.
Lemma D_3f044 : decode_any W_3f044 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f048 : bv 32 := 0x00b51533.
Lemma F_3f048 : fetch_word Asan.M.loaded_segments (0x3f048 : word) = Some W_3f048.
Proof. vm_refl. Qed.
Lemma D_3f048 : decode_any W_3f048 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f04c : bv 32 := 0x0005061b.
Lemma F_3f04c : fetch_word Asan.M.loaded_segments (0x3f04c : word) = Some W_3f04c.
Proof. vm_refl. Qed.
Lemma D_3f04c : decode_any W_3f04c = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f050 : bv 32 := 0x08c05263.
Lemma F_3f050 : fetch_word Asan.M.loaded_segments (0x3f050 : word) = Some W_3f050.
Proof. vm_refl. Qed.
Lemma D_3f050 : decode_any W_3f050 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f054 : bv 32 := 0x000016b7.
Lemma F_3f054 : fetch_word Asan.M.loaded_segments (0x3f054 : word) = Some W_3f054.
Proof. vm_refl. Qed.
Lemma D_3f054 : decode_any W_3f054 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f058 : bv 32 := 0xff190613.
Lemma F_3f058 : fetch_word Asan.M.loaded_segments (0x3f058 : word) = Some W_3f058.
Proof. vm_refl. Qed.
Lemma D_3f058 : decode_any W_3f058 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f05c : bv 32 := 0x30000713.
Lemma F_3f05c : fetch_word Asan.M.loaded_segments (0x3f05c : word) = Some W_3f05c.
Proof. vm_refl. Qed.
Lemma D_3f05c : decode_any W_3f05c = Some (OpImm ALU_ADD 14 0 768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f060 : bv 32 := 0xfff00793.
Lemma F_3f060 : fetch_word Asan.M.loaded_segments (0x3f060 : word) = Some W_3f060.
Proof. vm_refl. Qed.
Lemma D_3f060 : decode_any W_3f060 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f064 : bv 32 := 0x00c71733.
Lemma F_3f064 : fetch_word Asan.M.loaded_segments (0x3f064 : word) = Some W_3f064.
Proof. vm_refl. Qed.
Lemma D_3f064 : decode_any W_3f064 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f068 : bv 32 := 0x0104b603.
Lemma F_3f068 : fetch_word Asan.M.loaded_segments (0x3f068 : word) = Some W_3f068.
Proof. vm_refl. Qed.
Lemma D_3f068 : decode_any W_3f068 = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f06c : bv 32 := 0x00b797b3.
Lemma F_3f06c : fetch_word Asan.M.loaded_segments (0x3f06c : word) = Some W_3f06c.
Proof. vm_refl. Qed.
Lemma D_3f06c : decode_any W_3f06c = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f070 : bv 32 := 0xfff50813.
Lemma F_3f070 : fetch_word Asan.M.loaded_segments (0x3f070 : word) = Some W_3f070.
Proof. vm_refl. Qed.
Lemma D_3f070 : decode_any W_3f070 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f074 : bv 32 := 0x00d485b3.
Lemma F_3f074 : fetch_word Asan.M.loaded_segments (0x3f074 : word) = Some W_3f074.
Proof. vm_refl. Qed.
Lemma D_3f074 : decode_any W_3f074 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f078 : bv 32 := 0x00e586b3.
Lemma F_3f078 : fetch_word Asan.M.loaded_segments (0x3f078 : word) = Some W_3f078.
Proof. vm_refl. Qed.
Lemma D_3f078 : decode_any W_3f078 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f07c : bv 32 := 0xfff7c713.
Lemma F_3f07c : fetch_word Asan.M.loaded_segments (0x3f07c : word) = Some W_3f07c.
Proof. vm_refl. Qed.
Lemma D_3f07c : decode_any W_3f07c = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f080 : bv 32 := 0x02081813.
Lemma F_3f080 : fetch_word Asan.M.loaded_segments (0x3f080 : word) = Some W_3f080.
Proof. vm_refl. Qed.
Lemma D_3f080 : decode_any W_3f080 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f084 : bv 32 := 0x02085793.
Lemma F_3f084 : fetch_word Asan.M.loaded_segments (0x3f084 : word) = Some W_3f084.
Proof. vm_refl. Qed.
Lemma D_3f084 : decode_any W_3f084 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f088 : bv 32 := 0x00f607b3.
Lemma F_3f088 : fetch_word Asan.M.loaded_segments (0x3f088 : word) = Some W_3f088.
Proof. vm_refl. Qed.
Lemma D_3f088 : decode_any W_3f088 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f08c : bv 32 := 0x00178813.
Lemma F_3f08c : fetch_word Asan.M.loaded_segments (0x3f08c : word) = Some W_3f08c.
Proof. vm_refl. Qed.
Lemma D_3f08c : decode_any W_3f08c = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f090 : bv 32 := 0x00e678b3.
Lemma F_3f090 : fetch_word Asan.M.loaded_segments (0x3f090 : word) = Some W_3f090.
Proof. vm_refl. Qed.
Lemma D_3f090 : decode_any W_3f090 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f094 : bv 32 := 0x011687b3.
Lemma F_3f094 : fetch_word Asan.M.loaded_segments (0x3f094 : word) = Some W_3f094.
Proof. vm_refl. Qed.
Lemma D_3f094 : decode_any W_3f094 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f098 : bv 32 := 0x0007c283.
Lemma F_3f098 : fetch_word Asan.M.loaded_segments (0x3f098 : word) = Some W_3f098.
Proof. vm_refl. Qed.
Lemma D_3f098 : decode_any W_3f098 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f09c : bv 32 := 0x06028663.
Lemma F_3f09c : fetch_word Asan.M.loaded_segments (0x3f09c : word) = Some W_3f09c.
Proof. vm_refl. Qed.
Lemma D_3f09c : decode_any W_3f09c = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0a0 : bv 32 := 0xfff5051b.
Lemma F_3f0a0 : fetch_word Asan.M.loaded_segments (0x3f0a0 : word) = Some W_3f0a0.
Proof. vm_refl. Qed.
Lemma D_3f0a0 : decode_any W_3f0a0 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0a4 : bv 32 := 0x00160613.
Lemma F_3f0a4 : fetch_word Asan.M.loaded_segments (0x3f0a4 : word) = Some W_3f0a4.
Proof. vm_refl. Qed.
Lemma D_3f0a4 : decode_any W_3f0a4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0a8 : bv 32 := 0xfe0514e3.
Lemma F_3f0a8 : fetch_word Asan.M.loaded_segments (0x3f0a8 : word) = Some W_3f0a8.
Proof. vm_refl. Qed.
Lemma D_3f0a8 : decode_any W_3f0a8 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0ac : bv 32 := 0x0104b823.
Lemma F_3f0ac : fetch_word Asan.M.loaded_segments (0x3f0ac : word) = Some W_3f0ac.
Proof. vm_refl. Qed.
Lemma D_3f0ac : decode_any W_3f0ac = Some (Store SZ8 9 16 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0b0 : bv 32 := 0x0400006f.
Lemma F_3f0b0 : fetch_word Asan.M.loaded_segments (0x3f0b0 : word) = Some W_3f0b0.
Proof. vm_refl. Qed.
Lemma D_3f0b0 : decode_any W_3f0b0 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0b4 : bv 32 := 0x0006c517.
Lemma F_3f0b4 : fetch_word Asan.M.loaded_segments (0x3f0b4 : word) = Some W_3f0b4.
Proof. vm_refl. Qed.
Lemma D_3f0b4 : decode_any W_3f0b4 = Some (Auipc 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0b8 : bv 32 := 0xe2453503.
Lemma F_3f0b8 : fetch_word Asan.M.loaded_segments (0x3f0b8 : word) = Some W_3f0b8.
Proof. vm_refl. Qed.
Lemma D_3f0b8 : decode_any W_3f0b8 = Some (Load SZ8 true 10 10 3620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0bc : bv 32 := 0x00052503.
Lemma F_3f0bc : fetch_word Asan.M.loaded_segments (0x3f0bc : word) = Some W_3f0bc.
Proof. vm_refl. Qed.
Lemma D_3f0bc : decode_any W_3f0bc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0c0 : bv 32 := 0x02050863.
Lemma F_3f0c0 : fetch_word Asan.M.loaded_segments (0x3f0c0 : word) = Some W_3f0c0.
Proof. vm_refl. Qed.
Lemma D_3f0c0 : decode_any W_3f0c0 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0c4 : bv 32 := 0x57c1f0ef.
Lemma F_3f0c4 : fetch_word Asan.M.loaded_segments (0x3f0c4 : word) = Some W_3f0c4.
Proof. vm_refl. Qed.
Lemma D_3f0c4 : decode_any W_3f0c4 = Some (Jal 1 128380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0c8 : bv 32 := 0x02050463.
Lemma F_3f0c8 : fetch_word Asan.M.loaded_segments (0x3f0c8 : word) = Some W_3f0c8.
Proof. vm_refl. Qed.
Lemma D_3f0c8 : decode_any W_3f0c8 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0cc : bv 32 := 0x02850583.
Lemma F_3f0cc : fetch_word Asan.M.loaded_segments (0x3f0cc : word) = Some W_3f0cc.
Proof. vm_refl. Qed.
Lemma D_3f0cc : decode_any W_3f0cc = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0d0 : bv 32 := 0x0a058663.
Lemma F_3f0d0 : fetch_word Asan.M.loaded_segments (0x3f0d0 : word) = Some W_3f0d0.
Proof. vm_refl. Qed.
Lemma D_3f0d0 : decode_any W_3f0d0 = Some (Branch BC_EQ 11 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0d4 : bv 32 := 0x00000513.
Lemma F_3f0d4 : fetch_word Asan.M.loaded_segments (0x3f0d4 : word) = Some W_3f0d4.
Proof. vm_refl. Qed.
Lemma D_3f0d4 : decode_any W_3f0d4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0d8 : bv 32 := 0x01813083.
Lemma F_3f0d8 : fetch_word Asan.M.loaded_segments (0x3f0d8 : word) = Some W_3f0d8.
Proof. vm_refl. Qed.
Lemma D_3f0d8 : decode_any W_3f0d8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0dc : bv 32 := 0x01013403.
Lemma F_3f0dc : fetch_word Asan.M.loaded_segments (0x3f0dc : word) = Some W_3f0dc.
Proof. vm_refl. Qed.
Lemma D_3f0dc : decode_any W_3f0dc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0e0 : bv 32 := 0x00813483.
Lemma F_3f0e0 : fetch_word Asan.M.loaded_segments (0x3f0e0 : word) = Some W_3f0e0.
Proof. vm_refl. Qed.
Lemma D_3f0e0 : decode_any W_3f0e0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0e4 : bv 32 := 0x00013903.
Lemma F_3f0e4 : fetch_word Asan.M.loaded_segments (0x3f0e4 : word) = Some W_3f0e4.
Proof. vm_refl. Qed.
Lemma D_3f0e4 : decode_any W_3f0e4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0e8 : bv 32 := 0x02010113.
Lemma F_3f0e8 : fetch_word Asan.M.loaded_segments (0x3f0e8 : word) = Some W_3f0e8.
Proof. vm_refl. Qed.
Lemma D_3f0e8 : decode_any W_3f0e8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0ec : bv 32 := 0x00008067.
Lemma F_3f0ec : fetch_word Asan.M.loaded_segments (0x3f0ec : word) = Some W_3f0ec.
Proof. vm_refl. Qed.
Lemma D_3f0ec : decode_any W_3f0ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0f0 : bv 32 := 0x01813083.
Lemma F_3f0f0 : fetch_word Asan.M.loaded_segments (0x3f0f0 : word) = Some W_3f0f0.
Proof. vm_refl. Qed.
Lemma D_3f0f0 : decode_any W_3f0f0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0f4 : bv 32 := 0x01013403.
Lemma F_3f0f4 : fetch_word Asan.M.loaded_segments (0x3f0f4 : word) = Some W_3f0f4.
Proof. vm_refl. Qed.
Lemma D_3f0f4 : decode_any W_3f0f4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0f8 : bv 32 := 0x00813483.
Lemma F_3f0f8 : fetch_word Asan.M.loaded_segments (0x3f0f8 : word) = Some W_3f0f8.
Proof. vm_refl. Qed.
Lemma D_3f0f8 : decode_any W_3f0f8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f0fc : bv 32 := 0x00013903.
Lemma F_3f0fc : fetch_word Asan.M.loaded_segments (0x3f0fc : word) = Some W_3f0fc.
Proof. vm_refl. Qed.
Lemma D_3f0fc : decode_any W_3f0fc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f100 : bv 32 := 0x02010113.
Lemma F_3f100 : fetch_word Asan.M.loaded_segments (0x3f100 : word) = Some W_3f100.
Proof. vm_refl. Qed.
Lemma D_3f100 : decode_any W_3f100 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f104 : bv 32 := 0x00008067.
Lemma F_3f104 : fetch_word Asan.M.loaded_segments (0x3f104 : word) = Some W_3f104.
Proof. vm_refl. Qed.
Lemma D_3f104 : decode_any W_3f104 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f108 : bv 32 := 0x00160613.
Lemma F_3f108 : fetch_word Asan.M.loaded_segments (0x3f108 : word) = Some W_3f108.
Proof. vm_refl. Qed.
Lemma D_3f108 : decode_any W_3f108 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f10c : bv 32 := 0x00100513.
Lemma F_3f10c : fetch_word Asan.M.loaded_segments (0x3f10c : word) = Some W_3f10c.
Proof. vm_refl. Qed.
Lemma D_3f10c : decode_any W_3f10c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f110 : bv 32 := 0xffb90693.
Lemma F_3f110 : fetch_word Asan.M.loaded_segments (0x3f110 : word) = Some W_3f110.
Proof. vm_refl. Qed.
Lemma D_3f110 : decode_any W_3f110 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f114 : bv 32 := 0x00c4b823.
Lemma F_3f114 : fetch_word Asan.M.loaded_segments (0x3f114 : word) = Some W_3f114.
Proof. vm_refl. Qed.
Lemma D_3f114 : decode_any W_3f114 = Some (Store SZ8 9 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f118 : bv 32 := 0x00a78023.
Lemma F_3f118 : fetch_word Asan.M.loaded_segments (0x3f118 : word) = Some W_3f118.
Proof. vm_refl. Qed.
Lemma D_3f118 : decode_any W_3f118 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f11c : bv 32 := 0x00d51533.
Lemma F_3f11c : fetch_word Asan.M.loaded_segments (0x3f11c : word) = Some W_3f11c.
Proof. vm_refl. Qed.
Lemma D_3f11c : decode_any W_3f11c = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f120 : bv 32 := 0x00200613.
Lemma F_3f120 : fetch_word Asan.M.loaded_segments (0x3f120 : word) = Some W_3f120.
Proof. vm_refl. Qed.
Lemma D_3f120 : decode_any W_3f120 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f124 : bv 32 := 0x00889893.
Lemma F_3f124 : fetch_word Asan.M.loaded_segments (0x3f124 : word) = Some W_3f124.
Proof. vm_refl. Qed.
Lemma D_3f124 : decode_any W_3f124 = Some (ShiftImm ALU_SLL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f128 : bv 32 := 0x01261633.
Lemma F_3f128 : fetch_word Asan.M.loaded_segments (0x3f128 : word) = Some W_3f128.
Proof. vm_refl. Qed.
Lemma D_3f128 : decode_any W_3f128 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f12c : bv 32 := 0x00a58533.
Lemma F_3f12c : fetch_word Asan.M.loaded_segments (0x3f12c : word) = Some W_3f12c.
Proof. vm_refl. Qed.
Lemma D_3f12c : decode_any W_3f12c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f130 : bv 32 := 0x01160633.
Lemma F_3f130 : fetch_word Asan.M.loaded_segments (0x3f130 : word) = Some W_3f130.
Proof. vm_refl. Qed.
Lemma D_3f130 : decode_any W_3f130 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f134 : bv 32 := 0x00c504b3.
Lemma F_3f134 : fetch_word Asan.M.loaded_segments (0x3f134 : word) = Some W_3f134.
Proof. vm_refl. Qed.
Lemma D_3f134 : decode_any W_3f134 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f138 : bv 32 := 0x0084bc23.
Lemma F_3f138 : fetch_word Asan.M.loaded_segments (0x3f138 : word) = Some W_3f138.
Proof. vm_refl. Qed.
Lemma D_3f138 : decode_any W_3f138 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f13c : bv 32 := 0x0ef4bc23.
Lemma F_3f13c : fetch_word Asan.M.loaded_segments (0x3f13c : word) = Some W_3f13c.
Proof. vm_refl. Qed.
Lemma D_3f13c : decode_any W_3f13c = Some (Store SZ8 9 15 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f140 : bv 32 := 0x00048513.
Lemma F_3f140 : fetch_word Asan.M.loaded_segments (0x3f140 : word) = Some W_3f140.
Proof. vm_refl. Qed.
Lemma D_3f140 : decode_any W_3f140 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f144 : bv 32 := 0x3cc000ef.
Lemma F_3f144 : fetch_word Asan.M.loaded_segments (0x3f144 : word) = Some W_3f144.
Proof. vm_refl. Qed.
Lemma D_3f144 : decode_any W_3f144 = Some (Jal 1 972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f148 : bv 32 := 0x00050593.
Lemma F_3f148 : fetch_word Asan.M.loaded_segments (0x3f148 : word) = Some W_3f148.
Proof. vm_refl. Qed.
Lemma D_3f148 : decode_any W_3f148 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f14c : bv 32 := 0x00048513.
Lemma F_3f14c : fetch_word Asan.M.loaded_segments (0x3f14c : word) = Some W_3f14c.
Proof. vm_refl. Qed.
Lemma D_3f14c : decode_any W_3f14c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f150 : bv 32 := 0x00000613.
Lemma F_3f150 : fetch_word Asan.M.loaded_segments (0x3f150 : word) = Some W_3f150.
Proof. vm_refl. Qed.
Lemma D_3f150 : decode_any W_3f150 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f154 : bv 32 := 0x0005b023.
Lemma F_3f154 : fetch_word Asan.M.loaded_segments (0x3f154 : word) = Some W_3f154.
Proof. vm_refl. Qed.
Lemma D_3f154 : decode_any W_3f154 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f158 : bv 32 := 0x0005b423.
Lemma F_3f158 : fetch_word Asan.M.loaded_segments (0x3f158 : word) = Some W_3f158.
Proof. vm_refl. Qed.
Lemma D_3f158 : decode_any W_3f158 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f15c : bv 32 := 0x0005b823.
Lemma F_3f15c : fetch_word Asan.M.loaded_segments (0x3f15c : word) = Some W_3f15c.
Proof. vm_refl. Qed.
Lemma D_3f15c : decode_any W_3f15c = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f160 : bv 32 := 0x0005bc23.
Lemma F_3f160 : fetch_word Asan.M.loaded_segments (0x3f160 : word) = Some W_3f160.
Proof. vm_refl. Qed.
Lemma D_3f160 : decode_any W_3f160 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f164 : bv 32 := 0x01813083.
Lemma F_3f164 : fetch_word Asan.M.loaded_segments (0x3f164 : word) = Some W_3f164.
Proof. vm_refl. Qed.
Lemma D_3f164 : decode_any W_3f164 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f168 : bv 32 := 0x01013403.
Lemma F_3f168 : fetch_word Asan.M.loaded_segments (0x3f168 : word) = Some W_3f168.
Proof. vm_refl. Qed.
Lemma D_3f168 : decode_any W_3f168 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f16c : bv 32 := 0x00813483.
Lemma F_3f16c : fetch_word Asan.M.loaded_segments (0x3f16c : word) = Some W_3f16c.
Proof. vm_refl. Qed.
Lemma D_3f16c : decode_any W_3f16c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f170 : bv 32 := 0x00013903.
Lemma F_3f170 : fetch_word Asan.M.loaded_segments (0x3f170 : word) = Some W_3f170.
Proof. vm_refl. Qed.
Lemma D_3f170 : decode_any W_3f170 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f174 : bv 32 := 0x02010113.
Lemma F_3f174 : fetch_word Asan.M.loaded_segments (0x3f174 : word) = Some W_3f174.
Proof. vm_refl. Qed.
Lemma D_3f174 : decode_any W_3f174 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f178 : bv 32 := 0x00008067.
Lemma F_3f178 : fetch_word Asan.M.loaded_segments (0x3f178 : word) = Some W_3f178.
Proof. vm_refl. Qed.
Lemma D_3f178 : decode_any W_3f178 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_3f198 : bv 32 := 0xfe010113.
Lemma F_3f198 : fetch_word Asan.M.loaded_segments (0x3f198 : word) = Some W_3f198.
Proof. vm_refl. Qed.
Lemma D_3f198 : decode_any W_3f198 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f19c : bv 32 := 0x00113c23.
Lemma F_3f19c : fetch_word Asan.M.loaded_segments (0x3f19c : word) = Some W_3f19c.
Proof. vm_refl. Qed.
Lemma D_3f19c : decode_any W_3f19c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1a0 : bv 32 := 0x00813823.
Lemma F_3f1a0 : fetch_word Asan.M.loaded_segments (0x3f1a0 : word) = Some W_3f1a0.
Proof. vm_refl. Qed.
Lemma D_3f1a0 : decode_any W_3f1a0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1a4 : bv 32 := 0x00913423.
Lemma F_3f1a4 : fetch_word Asan.M.loaded_segments (0x3f1a4 : word) = Some W_3f1a4.
Proof. vm_refl. Qed.
Lemma D_3f1a4 : decode_any W_3f1a4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1a8 : bv 32 := 0x01213023.
Lemma F_3f1a8 : fetch_word Asan.M.loaded_segments (0x3f1a8 : word) = Some W_3f1a8.
Proof. vm_refl. Qed.
Lemma D_3f1a8 : decode_any W_3f1a8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1ac : bv 32 := 0x02010413.
Lemma F_3f1ac : fetch_word Asan.M.loaded_segments (0x3f1ac : word) = Some W_3f1ac.
Proof. vm_refl. Qed.
Lemma D_3f1ac : decode_any W_3f1ac = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1b0 : bv 32 := 0x0006d517.
Lemma F_3f1b0 : fetch_word Asan.M.loaded_segments (0x3f1b0 : word) = Some W_3f1b0.
Proof. vm_refl. Qed.
Lemma D_3f1b0 : decode_any W_3f1b0 = Some (Auipc 10 109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1b4 : bv 32 := 0x9b050513.
Lemma F_3f1b4 : fetch_word Asan.M.loaded_segments (0x3f1b4 : word) = Some W_3f1b4.
Proof. vm_refl. Qed.
Lemma D_3f1b4 : decode_any W_3f1b4 = Some (OpImm ALU_ADD 10 10 2480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1b8 : bv 32 := 0x0d4050ef.
Lemma F_3f1b8 : fetch_word Asan.M.loaded_segments (0x3f1b8 : word) = Some W_3f1b8.
Proof. vm_refl. Qed.
Lemma D_3f1b8 : decode_any W_3f1b8 = Some (Jal 1 20692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1bc : bv 32 := 0x00053483.
Lemma F_3f1bc : fetch_word Asan.M.loaded_segments (0x3f1bc : word) = Some W_3f1bc.
Proof. vm_refl. Qed.
Lemma D_3f1bc : decode_any W_3f1bc = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1c0 : bv 32 := 0x08048863.
Lemma F_3f1c0 : fetch_word Asan.M.loaded_segments (0x3f1c0 : word) = Some W_3f1c0.
Proof. vm_refl. Qed.
Lemma D_3f1c0 : decode_any W_3f1c0 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1c4 : bv 32 := 0x0604c503.
Lemma F_3f1c4 : fetch_word Asan.M.loaded_segments (0x3f1c4 : word) = Some W_3f1c4.
Proof. vm_refl. Qed.
Lemma D_3f1c4 : decode_any W_3f1c4 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1c8 : bv 32 := 0x0584b903.
Lemma F_3f1c8 : fetch_word Asan.M.loaded_segments (0x3f1c8 : word) = Some W_3f1c8.
Proof. vm_refl. Qed.
Lemma D_3f1c8 : decode_any W_3f1c8 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1cc : bv 32 := 0x00050863.
Lemma F_3f1cc : fetch_word Asan.M.loaded_segments (0x3f1cc : word) = Some W_3f1cc.
Proof. vm_refl. Qed.
Lemma D_3f1cc : decode_any W_3f1cc = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1d0 : bv 32 := 0x00048513.
Lemma F_3f1d0 : fetch_word Asan.M.loaded_segments (0x3f1d0 : word) = Some W_3f1d0.
Proof. vm_refl. Qed.
Lemma D_3f1d0 : decode_any W_3f1d0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1d4 : bv 32 := 0x00040593.
Lemma F_3f1d4 : fetch_word Asan.M.loaded_segments (0x3f1d4 : word) = Some W_3f1d4.
Proof. vm_refl. Qed.
Lemma D_3f1d4 : decode_any W_3f1d4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1d8 : bv 32 := 0xed4ff0ef.
Lemma F_3f1d8 : fetch_word Asan.M.loaded_segments (0x3f1d8 : word) = Some W_3f1d8.
Proof. vm_refl. Qed.
Lemma D_3f1d8 : decode_any W_3f1d8 = Some (Jal 1 2094804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1dc : bv 32 := 0xff790593.
Lemma F_3f1dc : fetch_word Asan.M.loaded_segments (0x3f1dc : word) = Some W_3f1dc.
Proof. vm_refl. Qed.
Lemma D_3f1dc : decode_any W_3f1dc = Some (OpImm ALU_ADD 11 18 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1e0 : bv 32 := 0x00100513.
Lemma F_3f1e0 : fetch_word Asan.M.loaded_segments (0x3f1e0 : word) = Some W_3f1e0.
Proof. vm_refl. Qed.
Lemma D_3f1e0 : decode_any W_3f1e0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1e4 : bv 32 := 0x00b51533.
Lemma F_3f1e4 : fetch_word Asan.M.loaded_segments (0x3f1e4 : word) = Some W_3f1e4.
Proof. vm_refl. Qed.
Lemma D_3f1e4 : decode_any W_3f1e4 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1e8 : bv 32 := 0x0005061b.
Lemma F_3f1e8 : fetch_word Asan.M.loaded_segments (0x3f1e8 : word) = Some W_3f1e8.
Proof. vm_refl. Qed.
Lemma D_3f1e8 : decode_any W_3f1e8 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1ec : bv 32 := 0x08c05263.
Lemma F_3f1ec : fetch_word Asan.M.loaded_segments (0x3f1ec : word) = Some W_3f1ec.
Proof. vm_refl. Qed.
Lemma D_3f1ec : decode_any W_3f1ec = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1f0 : bv 32 := 0x000016b7.
Lemma F_3f1f0 : fetch_word Asan.M.loaded_segments (0x3f1f0 : word) = Some W_3f1f0.
Proof. vm_refl. Qed.
Lemma D_3f1f0 : decode_any W_3f1f0 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1f4 : bv 32 := 0xff190613.
Lemma F_3f1f4 : fetch_word Asan.M.loaded_segments (0x3f1f4 : word) = Some W_3f1f4.
Proof. vm_refl. Qed.
Lemma D_3f1f4 : decode_any W_3f1f4 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1f8 : bv 32 := 0x38000713.
Lemma F_3f1f8 : fetch_word Asan.M.loaded_segments (0x3f1f8 : word) = Some W_3f1f8.
Proof. vm_refl. Qed.
Lemma D_3f1f8 : decode_any W_3f1f8 = Some (OpImm ALU_ADD 14 0 896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f1fc : bv 32 := 0xfff00793.
Lemma F_3f1fc : fetch_word Asan.M.loaded_segments (0x3f1fc : word) = Some W_3f1fc.
Proof. vm_refl. Qed.
Lemma D_3f1fc : decode_any W_3f1fc = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f200 : bv 32 := 0x00c71733.
Lemma F_3f200 : fetch_word Asan.M.loaded_segments (0x3f200 : word) = Some W_3f200.
Proof. vm_refl. Qed.
Lemma D_3f200 : decode_any W_3f200 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f204 : bv 32 := 0x0184b603.
Lemma F_3f204 : fetch_word Asan.M.loaded_segments (0x3f204 : word) = Some W_3f204.
Proof. vm_refl. Qed.
Lemma D_3f204 : decode_any W_3f204 = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f208 : bv 32 := 0x00b797b3.
Lemma F_3f208 : fetch_word Asan.M.loaded_segments (0x3f208 : word) = Some W_3f208.
Proof. vm_refl. Qed.
Lemma D_3f208 : decode_any W_3f208 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f20c : bv 32 := 0xfff50813.
Lemma F_3f20c : fetch_word Asan.M.loaded_segments (0x3f20c : word) = Some W_3f20c.
Proof. vm_refl. Qed.
Lemma D_3f20c : decode_any W_3f20c = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f210 : bv 32 := 0x00d485b3.
Lemma F_3f210 : fetch_word Asan.M.loaded_segments (0x3f210 : word) = Some W_3f210.
Proof. vm_refl. Qed.
Lemma D_3f210 : decode_any W_3f210 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f214 : bv 32 := 0x00e586b3.
Lemma F_3f214 : fetch_word Asan.M.loaded_segments (0x3f214 : word) = Some W_3f214.
Proof. vm_refl. Qed.
Lemma D_3f214 : decode_any W_3f214 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f218 : bv 32 := 0xfff7c713.
Lemma F_3f218 : fetch_word Asan.M.loaded_segments (0x3f218 : word) = Some W_3f218.
Proof. vm_refl. Qed.
Lemma D_3f218 : decode_any W_3f218 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f21c : bv 32 := 0x02081813.
Lemma F_3f21c : fetch_word Asan.M.loaded_segments (0x3f21c : word) = Some W_3f21c.
Proof. vm_refl. Qed.
Lemma D_3f21c : decode_any W_3f21c = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f220 : bv 32 := 0x02085793.
Lemma F_3f220 : fetch_word Asan.M.loaded_segments (0x3f220 : word) = Some W_3f220.
Proof. vm_refl. Qed.
Lemma D_3f220 : decode_any W_3f220 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f224 : bv 32 := 0x00f607b3.
Lemma F_3f224 : fetch_word Asan.M.loaded_segments (0x3f224 : word) = Some W_3f224.
Proof. vm_refl. Qed.
Lemma D_3f224 : decode_any W_3f224 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f228 : bv 32 := 0x00178813.
Lemma F_3f228 : fetch_word Asan.M.loaded_segments (0x3f228 : word) = Some W_3f228.
Proof. vm_refl. Qed.
Lemma D_3f228 : decode_any W_3f228 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f22c : bv 32 := 0x00e678b3.
Lemma F_3f22c : fetch_word Asan.M.loaded_segments (0x3f22c : word) = Some W_3f22c.
Proof. vm_refl. Qed.
Lemma D_3f22c : decode_any W_3f22c = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f230 : bv 32 := 0x011687b3.
Lemma F_3f230 : fetch_word Asan.M.loaded_segments (0x3f230 : word) = Some W_3f230.
Proof. vm_refl. Qed.
Lemma D_3f230 : decode_any W_3f230 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f234 : bv 32 := 0x0007c283.
Lemma F_3f234 : fetch_word Asan.M.loaded_segments (0x3f234 : word) = Some W_3f234.
Proof. vm_refl. Qed.
Lemma D_3f234 : decode_any W_3f234 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f238 : bv 32 := 0x06028663.
Lemma F_3f238 : fetch_word Asan.M.loaded_segments (0x3f238 : word) = Some W_3f238.
Proof. vm_refl. Qed.
Lemma D_3f238 : decode_any W_3f238 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f23c : bv 32 := 0xfff5051b.
Lemma F_3f23c : fetch_word Asan.M.loaded_segments (0x3f23c : word) = Some W_3f23c.
Proof. vm_refl. Qed.
Lemma D_3f23c : decode_any W_3f23c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f240 : bv 32 := 0x00160613.
Lemma F_3f240 : fetch_word Asan.M.loaded_segments (0x3f240 : word) = Some W_3f240.
Proof. vm_refl. Qed.
Lemma D_3f240 : decode_any W_3f240 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f244 : bv 32 := 0xfe0514e3.
Lemma F_3f244 : fetch_word Asan.M.loaded_segments (0x3f244 : word) = Some W_3f244.
Proof. vm_refl. Qed.
Lemma D_3f244 : decode_any W_3f244 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f248 : bv 32 := 0x0104bc23.
Lemma F_3f248 : fetch_word Asan.M.loaded_segments (0x3f248 : word) = Some W_3f248.
Proof. vm_refl. Qed.
Lemma D_3f248 : decode_any W_3f248 = Some (Store SZ8 9 16 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f24c : bv 32 := 0x0400006f.
Lemma F_3f24c : fetch_word Asan.M.loaded_segments (0x3f24c : word) = Some W_3f24c.
Proof. vm_refl. Qed.
Lemma D_3f24c : decode_any W_3f24c = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f250 : bv 32 := 0x0006c517.
Lemma F_3f250 : fetch_word Asan.M.loaded_segments (0x3f250 : word) = Some W_3f250.
Proof. vm_refl. Qed.
Lemma D_3f250 : decode_any W_3f250 = Some (Auipc 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f254 : bv 32 := 0xc8853503.
Lemma F_3f254 : fetch_word Asan.M.loaded_segments (0x3f254 : word) = Some W_3f254.
Proof. vm_refl. Qed.
Lemma D_3f254 : decode_any W_3f254 = Some (Load SZ8 true 10 10 3208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f258 : bv 32 := 0x00052503.
Lemma F_3f258 : fetch_word Asan.M.loaded_segments (0x3f258 : word) = Some W_3f258.
Proof. vm_refl. Qed.
Lemma D_3f258 : decode_any W_3f258 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f25c : bv 32 := 0x02050863.
Lemma F_3f25c : fetch_word Asan.M.loaded_segments (0x3f25c : word) = Some W_3f25c.
Proof. vm_refl. Qed.
Lemma D_3f25c : decode_any W_3f25c = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f260 : bv 32 := 0x3e01f0ef.
Lemma F_3f260 : fetch_word Asan.M.loaded_segments (0x3f260 : word) = Some W_3f260.
Proof. vm_refl. Qed.
Lemma D_3f260 : decode_any W_3f260 = Some (Jal 1 127968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f264 : bv 32 := 0x02050463.
Lemma F_3f264 : fetch_word Asan.M.loaded_segments (0x3f264 : word) = Some W_3f264.
Proof. vm_refl. Qed.
Lemma D_3f264 : decode_any W_3f264 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f268 : bv 32 := 0x02850583.
Lemma F_3f268 : fetch_word Asan.M.loaded_segments (0x3f268 : word) = Some W_3f268.
Proof. vm_refl. Qed.
Lemma D_3f268 : decode_any W_3f268 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f26c : bv 32 := 0x0a058e63.
Lemma F_3f26c : fetch_word Asan.M.loaded_segments (0x3f26c : word) = Some W_3f26c.
Proof. vm_refl. Qed.
Lemma D_3f26c : decode_any W_3f26c = Some (Branch BC_EQ 11 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f270 : bv 32 := 0x00000513.
Lemma F_3f270 : fetch_word Asan.M.loaded_segments (0x3f270 : word) = Some W_3f270.
Proof. vm_refl. Qed.
Lemma D_3f270 : decode_any W_3f270 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f274 : bv 32 := 0x01813083.
Lemma F_3f274 : fetch_word Asan.M.loaded_segments (0x3f274 : word) = Some W_3f274.
Proof. vm_refl. Qed.
Lemma D_3f274 : decode_any W_3f274 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f278 : bv 32 := 0x01013403.
Lemma F_3f278 : fetch_word Asan.M.loaded_segments (0x3f278 : word) = Some W_3f278.
Proof. vm_refl. Qed.
Lemma D_3f278 : decode_any W_3f278 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f27c : bv 32 := 0x00813483.
Lemma F_3f27c : fetch_word Asan.M.loaded_segments (0x3f27c : word) = Some W_3f27c.
Proof. vm_refl. Qed.
Lemma D_3f27c : decode_any W_3f27c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f280 : bv 32 := 0x00013903.
Lemma F_3f280 : fetch_word Asan.M.loaded_segments (0x3f280 : word) = Some W_3f280.
Proof. vm_refl. Qed.
Lemma D_3f280 : decode_any W_3f280 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f284 : bv 32 := 0x02010113.
Lemma F_3f284 : fetch_word Asan.M.loaded_segments (0x3f284 : word) = Some W_3f284.
Proof. vm_refl. Qed.
Lemma D_3f284 : decode_any W_3f284 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f288 : bv 32 := 0x00008067.
Lemma F_3f288 : fetch_word Asan.M.loaded_segments (0x3f288 : word) = Some W_3f288.
Proof. vm_refl. Qed.
Lemma D_3f288 : decode_any W_3f288 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f28c : bv 32 := 0x01813083.
Lemma F_3f28c : fetch_word Asan.M.loaded_segments (0x3f28c : word) = Some W_3f28c.
Proof. vm_refl. Qed.
Lemma D_3f28c : decode_any W_3f28c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f290 : bv 32 := 0x01013403.
Lemma F_3f290 : fetch_word Asan.M.loaded_segments (0x3f290 : word) = Some W_3f290.
Proof. vm_refl. Qed.
Lemma D_3f290 : decode_any W_3f290 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f294 : bv 32 := 0x00813483.
Lemma F_3f294 : fetch_word Asan.M.loaded_segments (0x3f294 : word) = Some W_3f294.
Proof. vm_refl. Qed.
Lemma D_3f294 : decode_any W_3f294 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f298 : bv 32 := 0x00013903.
Lemma F_3f298 : fetch_word Asan.M.loaded_segments (0x3f298 : word) = Some W_3f298.
Proof. vm_refl. Qed.
Lemma D_3f298 : decode_any W_3f298 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f29c : bv 32 := 0x02010113.
Lemma F_3f29c : fetch_word Asan.M.loaded_segments (0x3f29c : word) = Some W_3f29c.
Proof. vm_refl. Qed.
Lemma D_3f29c : decode_any W_3f29c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2a0 : bv 32 := 0x00008067.
Lemma F_3f2a0 : fetch_word Asan.M.loaded_segments (0x3f2a0 : word) = Some W_3f2a0.
Proof. vm_refl. Qed.
Lemma D_3f2a0 : decode_any W_3f2a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2a4 : bv 32 := 0x00160613.
Lemma F_3f2a4 : fetch_word Asan.M.loaded_segments (0x3f2a4 : word) = Some W_3f2a4.
Proof. vm_refl. Qed.
Lemma D_3f2a4 : decode_any W_3f2a4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2a8 : bv 32 := 0x00100513.
Lemma F_3f2a8 : fetch_word Asan.M.loaded_segments (0x3f2a8 : word) = Some W_3f2a8.
Proof. vm_refl. Qed.
Lemma D_3f2a8 : decode_any W_3f2a8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2ac : bv 32 := 0xffb90693.
Lemma F_3f2ac : fetch_word Asan.M.loaded_segments (0x3f2ac : word) = Some W_3f2ac.
Proof. vm_refl. Qed.
Lemma D_3f2ac : decode_any W_3f2ac = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2b0 : bv 32 := 0x00c4bc23.
Lemma F_3f2b0 : fetch_word Asan.M.loaded_segments (0x3f2b0 : word) = Some W_3f2b0.
Proof. vm_refl. Qed.
Lemma D_3f2b0 : decode_any W_3f2b0 = Some (Store SZ8 9 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2b4 : bv 32 := 0x00a78023.
Lemma F_3f2b4 : fetch_word Asan.M.loaded_segments (0x3f2b4 : word) = Some W_3f2b4.
Proof. vm_refl. Qed.
Lemma D_3f2b4 : decode_any W_3f2b4 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2b8 : bv 32 := 0x00d51533.
Lemma F_3f2b8 : fetch_word Asan.M.loaded_segments (0x3f2b8 : word) = Some W_3f2b8.
Proof. vm_refl. Qed.
Lemma D_3f2b8 : decode_any W_3f2b8 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2bc : bv 32 := 0x00300613.
Lemma F_3f2bc : fetch_word Asan.M.loaded_segments (0x3f2bc : word) = Some W_3f2bc.
Proof. vm_refl. Qed.
Lemma D_3f2bc : decode_any W_3f2bc = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2c0 : bv 32 := 0x00989893.
Lemma F_3f2c0 : fetch_word Asan.M.loaded_segments (0x3f2c0 : word) = Some W_3f2c0.
Proof. vm_refl. Qed.
Lemma D_3f2c0 : decode_any W_3f2c0 = Some (ShiftImm ALU_SLL 17 17 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2c4 : bv 32 := 0x01261633.
Lemma F_3f2c4 : fetch_word Asan.M.loaded_segments (0x3f2c4 : word) = Some W_3f2c4.
Proof. vm_refl. Qed.
Lemma D_3f2c4 : decode_any W_3f2c4 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2c8 : bv 32 := 0x00a58533.
Lemma F_3f2c8 : fetch_word Asan.M.loaded_segments (0x3f2c8 : word) = Some W_3f2c8.
Proof. vm_refl. Qed.
Lemma D_3f2c8 : decode_any W_3f2c8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2cc : bv 32 := 0x01160633.
Lemma F_3f2cc : fetch_word Asan.M.loaded_segments (0x3f2cc : word) = Some W_3f2cc.
Proof. vm_refl. Qed.
Lemma D_3f2cc : decode_any W_3f2cc = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2d0 : bv 32 := 0x00c504b3.
Lemma F_3f2d0 : fetch_word Asan.M.loaded_segments (0x3f2d0 : word) = Some W_3f2d0.
Proof. vm_refl. Qed.
Lemma D_3f2d0 : decode_any W_3f2d0 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2d4 : bv 32 := 0x0084bc23.
Lemma F_3f2d4 : fetch_word Asan.M.loaded_segments (0x3f2d4 : word) = Some W_3f2d4.
Proof. vm_refl. Qed.
Lemma D_3f2d4 : decode_any W_3f2d4 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2d8 : bv 32 := 0x1ef4bc23.
Lemma F_3f2d8 : fetch_word Asan.M.loaded_segments (0x3f2d8 : word) = Some W_3f2d8.
Proof. vm_refl. Qed.
Lemma D_3f2d8 : decode_any W_3f2d8 = Some (Store SZ8 9 15 504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2dc : bv 32 := 0x00048513.
Lemma F_3f2dc : fetch_word Asan.M.loaded_segments (0x3f2dc : word) = Some W_3f2dc.
Proof. vm_refl. Qed.
Lemma D_3f2dc : decode_any W_3f2dc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2e0 : bv 32 := 0x230000ef.
Lemma F_3f2e0 : fetch_word Asan.M.loaded_segments (0x3f2e0 : word) = Some W_3f2e0.
Proof. vm_refl. Qed.
Lemma D_3f2e0 : decode_any W_3f2e0 = Some (Jal 1 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2e4 : bv 32 := 0x00050593.
Lemma F_3f2e4 : fetch_word Asan.M.loaded_segments (0x3f2e4 : word) = Some W_3f2e4.
Proof. vm_refl. Qed.
Lemma D_3f2e4 : decode_any W_3f2e4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2e8 : bv 32 := 0x00048513.
Lemma F_3f2e8 : fetch_word Asan.M.loaded_segments (0x3f2e8 : word) = Some W_3f2e8.
Proof. vm_refl. Qed.
Lemma D_3f2e8 : decode_any W_3f2e8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2ec : bv 32 := 0x00000613.
Lemma F_3f2ec : fetch_word Asan.M.loaded_segments (0x3f2ec : word) = Some W_3f2ec.
Proof. vm_refl. Qed.
Lemma D_3f2ec : decode_any W_3f2ec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2f0 : bv 32 := 0x0005b023.
Lemma F_3f2f0 : fetch_word Asan.M.loaded_segments (0x3f2f0 : word) = Some W_3f2f0.
Proof. vm_refl. Qed.
Lemma D_3f2f0 : decode_any W_3f2f0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2f4 : bv 32 := 0x0005b423.
Lemma F_3f2f4 : fetch_word Asan.M.loaded_segments (0x3f2f4 : word) = Some W_3f2f4.
Proof. vm_refl. Qed.
Lemma D_3f2f4 : decode_any W_3f2f4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2f8 : bv 32 := 0x0005b823.
Lemma F_3f2f8 : fetch_word Asan.M.loaded_segments (0x3f2f8 : word) = Some W_3f2f8.
Proof. vm_refl. Qed.
Lemma D_3f2f8 : decode_any W_3f2f8 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f2fc : bv 32 := 0x0005bc23.
Lemma F_3f2fc : fetch_word Asan.M.loaded_segments (0x3f2fc : word) = Some W_3f2fc.
Proof. vm_refl. Qed.
Lemma D_3f2fc : decode_any W_3f2fc = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f300 : bv 32 := 0x0205b023.
Lemma F_3f300 : fetch_word Asan.M.loaded_segments (0x3f300 : word) = Some W_3f300.
Proof. vm_refl. Qed.
Lemma D_3f300 : decode_any W_3f300 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f304 : bv 32 := 0x0205b423.
Lemma F_3f304 : fetch_word Asan.M.loaded_segments (0x3f304 : word) = Some W_3f304.
Proof. vm_refl. Qed.
Lemma D_3f304 : decode_any W_3f304 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f308 : bv 32 := 0x0205b823.
Lemma F_3f308 : fetch_word Asan.M.loaded_segments (0x3f308 : word) = Some W_3f308.
Proof. vm_refl. Qed.
Lemma D_3f308 : decode_any W_3f308 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f30c : bv 32 := 0x0205bc23.
Lemma F_3f30c : fetch_word Asan.M.loaded_segments (0x3f30c : word) = Some W_3f30c.
Proof. vm_refl. Qed.
Lemma D_3f30c : decode_any W_3f30c = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f310 : bv 32 := 0x01813083.
Lemma F_3f310 : fetch_word Asan.M.loaded_segments (0x3f310 : word) = Some W_3f310.
Proof. vm_refl. Qed.
Lemma D_3f310 : decode_any W_3f310 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f314 : bv 32 := 0x01013403.
Lemma F_3f314 : fetch_word Asan.M.loaded_segments (0x3f314 : word) = Some W_3f314.
Proof. vm_refl. Qed.
Lemma D_3f314 : decode_any W_3f314 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f318 : bv 32 := 0x00813483.
Lemma F_3f318 : fetch_word Asan.M.loaded_segments (0x3f318 : word) = Some W_3f318.
Proof. vm_refl. Qed.
Lemma D_3f318 : decode_any W_3f318 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f31c : bv 32 := 0x00013903.
Lemma F_3f31c : fetch_word Asan.M.loaded_segments (0x3f31c : word) = Some W_3f31c.
Proof. vm_refl. Qed.
Lemma D_3f31c : decode_any W_3f31c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f320 : bv 32 := 0x02010113.
Lemma F_3f320 : fetch_word Asan.M.loaded_segments (0x3f320 : word) = Some W_3f320.
Proof. vm_refl. Qed.
Lemma D_3f320 : decode_any W_3f320 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f324 : bv 32 := 0x00008067.
Lemma F_3f324 : fetch_word Asan.M.loaded_segments (0x3f324 : word) = Some W_3f324.
Proof. vm_refl. Qed.
Lemma D_3f324 : decode_any W_3f324 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_3f344 : bv 32 := 0xfe010113.
Lemma F_3f344 : fetch_word Asan.M.loaded_segments (0x3f344 : word) = Some W_3f344.
Proof. vm_refl. Qed.
Lemma D_3f344 : decode_any W_3f344 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f348 : bv 32 := 0x00113c23.
Lemma F_3f348 : fetch_word Asan.M.loaded_segments (0x3f348 : word) = Some W_3f348.
Proof. vm_refl. Qed.
Lemma D_3f348 : decode_any W_3f348 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f34c : bv 32 := 0x00813823.
Lemma F_3f34c : fetch_word Asan.M.loaded_segments (0x3f34c : word) = Some W_3f34c.
Proof. vm_refl. Qed.
Lemma D_3f34c : decode_any W_3f34c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f350 : bv 32 := 0x00913423.
Lemma F_3f350 : fetch_word Asan.M.loaded_segments (0x3f350 : word) = Some W_3f350.
Proof. vm_refl. Qed.
Lemma D_3f350 : decode_any W_3f350 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f354 : bv 32 := 0x01213023.
Lemma F_3f354 : fetch_word Asan.M.loaded_segments (0x3f354 : word) = Some W_3f354.
Proof. vm_refl. Qed.
Lemma D_3f354 : decode_any W_3f354 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f358 : bv 32 := 0x02010413.
Lemma F_3f358 : fetch_word Asan.M.loaded_segments (0x3f358 : word) = Some W_3f358.
Proof. vm_refl. Qed.
Lemma D_3f358 : decode_any W_3f358 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f35c : bv 32 := 0x0006d517.
Lemma F_3f35c : fetch_word Asan.M.loaded_segments (0x3f35c : word) = Some W_3f35c.
Proof. vm_refl. Qed.
Lemma D_3f35c : decode_any W_3f35c = Some (Auipc 10 109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f360 : bv 32 := 0x80450513.
Lemma F_3f360 : fetch_word Asan.M.loaded_segments (0x3f360 : word) = Some W_3f360.
Proof. vm_refl. Qed.
Lemma D_3f360 : decode_any W_3f360 = Some (OpImm ALU_ADD 10 10 2052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f364 : bv 32 := 0x729040ef.
Lemma F_3f364 : fetch_word Asan.M.loaded_segments (0x3f364 : word) = Some W_3f364.
Proof. vm_refl. Qed.
Lemma D_3f364 : decode_any W_3f364 = Some (Jal 1 20264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f368 : bv 32 := 0x00053483.
Lemma F_3f368 : fetch_word Asan.M.loaded_segments (0x3f368 : word) = Some W_3f368.
Proof. vm_refl. Qed.
Lemma D_3f368 : decode_any W_3f368 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f36c : bv 32 := 0x08048863.
Lemma F_3f36c : fetch_word Asan.M.loaded_segments (0x3f36c : word) = Some W_3f36c.
Proof. vm_refl. Qed.
Lemma D_3f36c : decode_any W_3f36c = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f370 : bv 32 := 0x0604c503.
Lemma F_3f370 : fetch_word Asan.M.loaded_segments (0x3f370 : word) = Some W_3f370.
Proof. vm_refl. Qed.
Lemma D_3f370 : decode_any W_3f370 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f374 : bv 32 := 0x0584b903.
Lemma F_3f374 : fetch_word Asan.M.loaded_segments (0x3f374 : word) = Some W_3f374.
Proof. vm_refl. Qed.
Lemma D_3f374 : decode_any W_3f374 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f378 : bv 32 := 0x00050863.
Lemma F_3f378 : fetch_word Asan.M.loaded_segments (0x3f378 : word) = Some W_3f378.
Proof. vm_refl. Qed.
Lemma D_3f378 : decode_any W_3f378 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f37c : bv 32 := 0x00048513.
Lemma F_3f37c : fetch_word Asan.M.loaded_segments (0x3f37c : word) = Some W_3f37c.
Proof. vm_refl. Qed.
Lemma D_3f37c : decode_any W_3f37c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f380 : bv 32 := 0x00040593.
Lemma F_3f380 : fetch_word Asan.M.loaded_segments (0x3f380 : word) = Some W_3f380.
Proof. vm_refl. Qed.
Lemma D_3f380 : decode_any W_3f380 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f384 : bv 32 := 0xd28ff0ef.
Lemma F_3f384 : fetch_word Asan.M.loaded_segments (0x3f384 : word) = Some W_3f384.
Proof. vm_refl. Qed.
Lemma D_3f384 : decode_any W_3f384 = Some (Jal 1 2094376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f388 : bv 32 := 0xff690593.
Lemma F_3f388 : fetch_word Asan.M.loaded_segments (0x3f388 : word) = Some W_3f388.
Proof. vm_refl. Qed.
Lemma D_3f388 : decode_any W_3f388 = Some (OpImm ALU_ADD 11 18 4086, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f38c : bv 32 := 0x00100513.
Lemma F_3f38c : fetch_word Asan.M.loaded_segments (0x3f38c : word) = Some W_3f38c.
Proof. vm_refl. Qed.
Lemma D_3f38c : decode_any W_3f38c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f390 : bv 32 := 0x00b51533.
Lemma F_3f390 : fetch_word Asan.M.loaded_segments (0x3f390 : word) = Some W_3f390.
Proof. vm_refl. Qed.
Lemma D_3f390 : decode_any W_3f390 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f394 : bv 32 := 0x0005061b.
Lemma F_3f394 : fetch_word Asan.M.loaded_segments (0x3f394 : word) = Some W_3f394.
Proof. vm_refl. Qed.
Lemma D_3f394 : decode_any W_3f394 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f398 : bv 32 := 0x08c05263.
Lemma F_3f398 : fetch_word Asan.M.loaded_segments (0x3f398 : word) = Some W_3f398.
Proof. vm_refl. Qed.
Lemma D_3f398 : decode_any W_3f398 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f39c : bv 32 := 0x000016b7.
Lemma F_3f39c : fetch_word Asan.M.loaded_segments (0x3f39c : word) = Some W_3f39c.
Proof. vm_refl. Qed.
Lemma D_3f39c : decode_any W_3f39c = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3a0 : bv 32 := 0xff190613.
Lemma F_3f3a0 : fetch_word Asan.M.loaded_segments (0x3f3a0 : word) = Some W_3f3a0.
Proof. vm_refl. Qed.
Lemma D_3f3a0 : decode_any W_3f3a0 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3a4 : bv 32 := 0x3c000713.
Lemma F_3f3a4 : fetch_word Asan.M.loaded_segments (0x3f3a4 : word) = Some W_3f3a4.
Proof. vm_refl. Qed.
Lemma D_3f3a4 : decode_any W_3f3a4 = Some (OpImm ALU_ADD 14 0 960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3a8 : bv 32 := 0xfff00793.
Lemma F_3f3a8 : fetch_word Asan.M.loaded_segments (0x3f3a8 : word) = Some W_3f3a8.
Proof. vm_refl. Qed.
Lemma D_3f3a8 : decode_any W_3f3a8 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3ac : bv 32 := 0x00c71733.
Lemma F_3f3ac : fetch_word Asan.M.loaded_segments (0x3f3ac : word) = Some W_3f3ac.
Proof. vm_refl. Qed.
Lemma D_3f3ac : decode_any W_3f3ac = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3b0 : bv 32 := 0x0204b603.
Lemma F_3f3b0 : fetch_word Asan.M.loaded_segments (0x3f3b0 : word) = Some W_3f3b0.
Proof. vm_refl. Qed.
Lemma D_3f3b0 : decode_any W_3f3b0 = Some (Load SZ8 true 12 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3b4 : bv 32 := 0x00b797b3.
Lemma F_3f3b4 : fetch_word Asan.M.loaded_segments (0x3f3b4 : word) = Some W_3f3b4.
Proof. vm_refl. Qed.
Lemma D_3f3b4 : decode_any W_3f3b4 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3b8 : bv 32 := 0xfff50813.
Lemma F_3f3b8 : fetch_word Asan.M.loaded_segments (0x3f3b8 : word) = Some W_3f3b8.
Proof. vm_refl. Qed.
Lemma D_3f3b8 : decode_any W_3f3b8 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3bc : bv 32 := 0x00d485b3.
Lemma F_3f3bc : fetch_word Asan.M.loaded_segments (0x3f3bc : word) = Some W_3f3bc.
Proof. vm_refl. Qed.
Lemma D_3f3bc : decode_any W_3f3bc = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3c0 : bv 32 := 0x00e586b3.
Lemma F_3f3c0 : fetch_word Asan.M.loaded_segments (0x3f3c0 : word) = Some W_3f3c0.
Proof. vm_refl. Qed.
Lemma D_3f3c0 : decode_any W_3f3c0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3c4 : bv 32 := 0xfff7c713.
Lemma F_3f3c4 : fetch_word Asan.M.loaded_segments (0x3f3c4 : word) = Some W_3f3c4.
Proof. vm_refl. Qed.
Lemma D_3f3c4 : decode_any W_3f3c4 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3c8 : bv 32 := 0x02081813.
Lemma F_3f3c8 : fetch_word Asan.M.loaded_segments (0x3f3c8 : word) = Some W_3f3c8.
Proof. vm_refl. Qed.
Lemma D_3f3c8 : decode_any W_3f3c8 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3cc : bv 32 := 0x02085793.
Lemma F_3f3cc : fetch_word Asan.M.loaded_segments (0x3f3cc : word) = Some W_3f3cc.
Proof. vm_refl. Qed.
Lemma D_3f3cc : decode_any W_3f3cc = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3d0 : bv 32 := 0x00f607b3.
Lemma F_3f3d0 : fetch_word Asan.M.loaded_segments (0x3f3d0 : word) = Some W_3f3d0.
Proof. vm_refl. Qed.
Lemma D_3f3d0 : decode_any W_3f3d0 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3d4 : bv 32 := 0x00178813.
Lemma F_3f3d4 : fetch_word Asan.M.loaded_segments (0x3f3d4 : word) = Some W_3f3d4.
Proof. vm_refl. Qed.
Lemma D_3f3d4 : decode_any W_3f3d4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3d8 : bv 32 := 0x00e678b3.
Lemma F_3f3d8 : fetch_word Asan.M.loaded_segments (0x3f3d8 : word) = Some W_3f3d8.
Proof. vm_refl. Qed.
Lemma D_3f3d8 : decode_any W_3f3d8 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3dc : bv 32 := 0x011687b3.
Lemma F_3f3dc : fetch_word Asan.M.loaded_segments (0x3f3dc : word) = Some W_3f3dc.
Proof. vm_refl. Qed.
Lemma D_3f3dc : decode_any W_3f3dc = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3e0 : bv 32 := 0x0007c283.
Lemma F_3f3e0 : fetch_word Asan.M.loaded_segments (0x3f3e0 : word) = Some W_3f3e0.
Proof. vm_refl. Qed.
Lemma D_3f3e0 : decode_any W_3f3e0 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3e4 : bv 32 := 0x06028663.
Lemma F_3f3e4 : fetch_word Asan.M.loaded_segments (0x3f3e4 : word) = Some W_3f3e4.
Proof. vm_refl. Qed.
Lemma D_3f3e4 : decode_any W_3f3e4 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3e8 : bv 32 := 0xfff5051b.
Lemma F_3f3e8 : fetch_word Asan.M.loaded_segments (0x3f3e8 : word) = Some W_3f3e8.
Proof. vm_refl. Qed.
Lemma D_3f3e8 : decode_any W_3f3e8 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3ec : bv 32 := 0x00160613.
Lemma F_3f3ec : fetch_word Asan.M.loaded_segments (0x3f3ec : word) = Some W_3f3ec.
Proof. vm_refl. Qed.
Lemma D_3f3ec : decode_any W_3f3ec = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3f0 : bv 32 := 0xfe0514e3.
Lemma F_3f3f0 : fetch_word Asan.M.loaded_segments (0x3f3f0 : word) = Some W_3f3f0.
Proof. vm_refl. Qed.
Lemma D_3f3f0 : decode_any W_3f3f0 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3f4 : bv 32 := 0x0304b023.
Lemma F_3f3f4 : fetch_word Asan.M.loaded_segments (0x3f3f4 : word) = Some W_3f3f4.
Proof. vm_refl. Qed.
Lemma D_3f3f4 : decode_any W_3f3f4 = Some (Store SZ8 9 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3f8 : bv 32 := 0x0400006f.
Lemma F_3f3f8 : fetch_word Asan.M.loaded_segments (0x3f3f8 : word) = Some W_3f3f8.
Proof. vm_refl. Qed.
Lemma D_3f3f8 : decode_any W_3f3f8 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f3fc : bv 32 := 0x0006c517.
Lemma F_3f3fc : fetch_word Asan.M.loaded_segments (0x3f3fc : word) = Some W_3f3fc.
Proof. vm_refl. Qed.
Lemma D_3f3fc : decode_any W_3f3fc = Some (Auipc 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f400 : bv 32 := 0xadc53503.
Lemma F_3f400 : fetch_word Asan.M.loaded_segments (0x3f400 : word) = Some W_3f400.
Proof. vm_refl. Qed.
Lemma D_3f400 : decode_any W_3f400 = Some (Load SZ8 true 10 10 2780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f404 : bv 32 := 0x00052503.
Lemma F_3f404 : fetch_word Asan.M.loaded_segments (0x3f404 : word) = Some W_3f404.
Proof. vm_refl. Qed.
Lemma D_3f404 : decode_any W_3f404 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f408 : bv 32 := 0x02050863.
Lemma F_3f408 : fetch_word Asan.M.loaded_segments (0x3f408 : word) = Some W_3f408.
Proof. vm_refl. Qed.
Lemma D_3f408 : decode_any W_3f408 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f40c : bv 32 := 0x2341f0ef.
Lemma F_3f40c : fetch_word Asan.M.loaded_segments (0x3f40c : word) = Some W_3f40c.
Proof. vm_refl. Qed.
Lemma D_3f40c : decode_any W_3f40c = Some (Jal 1 127540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f410 : bv 32 := 0x02050463.
Lemma F_3f410 : fetch_word Asan.M.loaded_segments (0x3f410 : word) = Some W_3f410.
Proof. vm_refl. Qed.
Lemma D_3f410 : decode_any W_3f410 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f414 : bv 32 := 0x02850583.
Lemma F_3f414 : fetch_word Asan.M.loaded_segments (0x3f414 : word) = Some W_3f414.
Proof. vm_refl. Qed.
Lemma D_3f414 : decode_any W_3f414 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f418 : bv 32 := 0x0c058e63.
Lemma F_3f418 : fetch_word Asan.M.loaded_segments (0x3f418 : word) = Some W_3f418.
Proof. vm_refl. Qed.
Lemma D_3f418 : decode_any W_3f418 = Some (Branch BC_EQ 11 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f41c : bv 32 := 0x00000513.
Lemma F_3f41c : fetch_word Asan.M.loaded_segments (0x3f41c : word) = Some W_3f41c.
Proof. vm_refl. Qed.
Lemma D_3f41c : decode_any W_3f41c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f420 : bv 32 := 0x01813083.
Lemma F_3f420 : fetch_word Asan.M.loaded_segments (0x3f420 : word) = Some W_3f420.
Proof. vm_refl. Qed.
Lemma D_3f420 : decode_any W_3f420 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f424 : bv 32 := 0x01013403.
Lemma F_3f424 : fetch_word Asan.M.loaded_segments (0x3f424 : word) = Some W_3f424.
Proof. vm_refl. Qed.
Lemma D_3f424 : decode_any W_3f424 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f428 : bv 32 := 0x00813483.
Lemma F_3f428 : fetch_word Asan.M.loaded_segments (0x3f428 : word) = Some W_3f428.
Proof. vm_refl. Qed.
Lemma D_3f428 : decode_any W_3f428 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f42c : bv 32 := 0x00013903.
Lemma F_3f42c : fetch_word Asan.M.loaded_segments (0x3f42c : word) = Some W_3f42c.
Proof. vm_refl. Qed.
Lemma D_3f42c : decode_any W_3f42c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f430 : bv 32 := 0x02010113.
Lemma F_3f430 : fetch_word Asan.M.loaded_segments (0x3f430 : word) = Some W_3f430.
Proof. vm_refl. Qed.
Lemma D_3f430 : decode_any W_3f430 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f434 : bv 32 := 0x00008067.
Lemma F_3f434 : fetch_word Asan.M.loaded_segments (0x3f434 : word) = Some W_3f434.
Proof. vm_refl. Qed.
Lemma D_3f434 : decode_any W_3f434 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f438 : bv 32 := 0x01813083.
Lemma F_3f438 : fetch_word Asan.M.loaded_segments (0x3f438 : word) = Some W_3f438.
Proof. vm_refl. Qed.
Lemma D_3f438 : decode_any W_3f438 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f43c : bv 32 := 0x01013403.
Lemma F_3f43c : fetch_word Asan.M.loaded_segments (0x3f43c : word) = Some W_3f43c.
Proof. vm_refl. Qed.
Lemma D_3f43c : decode_any W_3f43c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f440 : bv 32 := 0x00813483.
Lemma F_3f440 : fetch_word Asan.M.loaded_segments (0x3f440 : word) = Some W_3f440.
Proof. vm_refl. Qed.
Lemma D_3f440 : decode_any W_3f440 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f444 : bv 32 := 0x00013903.
Lemma F_3f444 : fetch_word Asan.M.loaded_segments (0x3f444 : word) = Some W_3f444.
Proof. vm_refl. Qed.
Lemma D_3f444 : decode_any W_3f444 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f448 : bv 32 := 0x02010113.
Lemma F_3f448 : fetch_word Asan.M.loaded_segments (0x3f448 : word) = Some W_3f448.
Proof. vm_refl. Qed.
Lemma D_3f448 : decode_any W_3f448 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f44c : bv 32 := 0x00008067.
Lemma F_3f44c : fetch_word Asan.M.loaded_segments (0x3f44c : word) = Some W_3f44c.
Proof. vm_refl. Qed.
Lemma D_3f44c : decode_any W_3f44c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f450 : bv 32 := 0x00160613.
Lemma F_3f450 : fetch_word Asan.M.loaded_segments (0x3f450 : word) = Some W_3f450.
Proof. vm_refl. Qed.
Lemma D_3f450 : decode_any W_3f450 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f454 : bv 32 := 0x00100513.
Lemma F_3f454 : fetch_word Asan.M.loaded_segments (0x3f454 : word) = Some W_3f454.
Proof. vm_refl. Qed.
Lemma D_3f454 : decode_any W_3f454 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f458 : bv 32 := 0xffb90693.
Lemma F_3f458 : fetch_word Asan.M.loaded_segments (0x3f458 : word) = Some W_3f458.
Proof. vm_refl. Qed.
Lemma D_3f458 : decode_any W_3f458 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f45c : bv 32 := 0x02c4b023.
Lemma F_3f45c : fetch_word Asan.M.loaded_segments (0x3f45c : word) = Some W_3f45c.
Proof. vm_refl. Qed.
Lemma D_3f45c : decode_any W_3f45c = Some (Store SZ8 9 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f460 : bv 32 := 0x00a78023.
Lemma F_3f460 : fetch_word Asan.M.loaded_segments (0x3f460 : word) = Some W_3f460.
Proof. vm_refl. Qed.
Lemma D_3f460 : decode_any W_3f460 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f464 : bv 32 := 0x00d51533.
Lemma F_3f464 : fetch_word Asan.M.loaded_segments (0x3f464 : word) = Some W_3f464.
Proof. vm_refl. Qed.
Lemma D_3f464 : decode_any W_3f464 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f468 : bv 32 := 0x00400613.
Lemma F_3f468 : fetch_word Asan.M.loaded_segments (0x3f468 : word) = Some W_3f468.
Proof. vm_refl. Qed.
Lemma D_3f468 : decode_any W_3f468 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f46c : bv 32 := 0x00a89893.
Lemma F_3f46c : fetch_word Asan.M.loaded_segments (0x3f46c : word) = Some W_3f46c.
Proof. vm_refl. Qed.
Lemma D_3f46c : decode_any W_3f46c = Some (ShiftImm ALU_SLL 17 17 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f470 : bv 32 := 0x01261633.
Lemma F_3f470 : fetch_word Asan.M.loaded_segments (0x3f470 : word) = Some W_3f470.
Proof. vm_refl. Qed.
Lemma D_3f470 : decode_any W_3f470 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f474 : bv 32 := 0x00a58533.
Lemma F_3f474 : fetch_word Asan.M.loaded_segments (0x3f474 : word) = Some W_3f474.
Proof. vm_refl. Qed.
Lemma D_3f474 : decode_any W_3f474 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f478 : bv 32 := 0x01160633.
Lemma F_3f478 : fetch_word Asan.M.loaded_segments (0x3f478 : word) = Some W_3f478.
Proof. vm_refl. Qed.
Lemma D_3f478 : decode_any W_3f478 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f47c : bv 32 := 0x00c504b3.
Lemma F_3f47c : fetch_word Asan.M.loaded_segments (0x3f47c : word) = Some W_3f47c.
Proof. vm_refl. Qed.
Lemma D_3f47c : decode_any W_3f47c = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f480 : bv 32 := 0x0084bc23.
Lemma F_3f480 : fetch_word Asan.M.loaded_segments (0x3f480 : word) = Some W_3f480.
Proof. vm_refl. Qed.
Lemma D_3f480 : decode_any W_3f480 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f484 : bv 32 := 0x3ef4bc23.
Lemma F_3f484 : fetch_word Asan.M.loaded_segments (0x3f484 : word) = Some W_3f484.
Proof. vm_refl. Qed.
Lemma D_3f484 : decode_any W_3f484 = Some (Store SZ8 9 15 1016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f488 : bv 32 := 0x00048513.
Lemma F_3f488 : fetch_word Asan.M.loaded_segments (0x3f488 : word) = Some W_3f488.
Proof. vm_refl. Qed.
Lemma D_3f488 : decode_any W_3f488 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f48c : bv 32 := 0x084000ef.
Lemma F_3f48c : fetch_word Asan.M.loaded_segments (0x3f48c : word) = Some W_3f48c.
Proof. vm_refl. Qed.
Lemma D_3f48c : decode_any W_3f48c = Some (Jal 1 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f490 : bv 32 := 0x00050593.
Lemma F_3f490 : fetch_word Asan.M.loaded_segments (0x3f490 : word) = Some W_3f490.
Proof. vm_refl. Qed.
Lemma D_3f490 : decode_any W_3f490 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f494 : bv 32 := 0x00048513.
Lemma F_3f494 : fetch_word Asan.M.loaded_segments (0x3f494 : word) = Some W_3f494.
Proof. vm_refl. Qed.
Lemma D_3f494 : decode_any W_3f494 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f498 : bv 32 := 0x00000613.
Lemma F_3f498 : fetch_word Asan.M.loaded_segments (0x3f498 : word) = Some W_3f498.
Proof. vm_refl. Qed.
Lemma D_3f498 : decode_any W_3f498 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f49c : bv 32 := 0x0005b023.
Lemma F_3f49c : fetch_word Asan.M.loaded_segments (0x3f49c : word) = Some W_3f49c.
Proof. vm_refl. Qed.
Lemma D_3f49c : decode_any W_3f49c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4a0 : bv 32 := 0x0005b423.
Lemma F_3f4a0 : fetch_word Asan.M.loaded_segments (0x3f4a0 : word) = Some W_3f4a0.
Proof. vm_refl. Qed.
Lemma D_3f4a0 : decode_any W_3f4a0 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4a4 : bv 32 := 0x0005b823.
Lemma F_3f4a4 : fetch_word Asan.M.loaded_segments (0x3f4a4 : word) = Some W_3f4a4.
Proof. vm_refl. Qed.
Lemma D_3f4a4 : decode_any W_3f4a4 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4a8 : bv 32 := 0x0005bc23.
Lemma F_3f4a8 : fetch_word Asan.M.loaded_segments (0x3f4a8 : word) = Some W_3f4a8.
Proof. vm_refl. Qed.
Lemma D_3f4a8 : decode_any W_3f4a8 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4ac : bv 32 := 0x0205b023.
Lemma F_3f4ac : fetch_word Asan.M.loaded_segments (0x3f4ac : word) = Some W_3f4ac.
Proof. vm_refl. Qed.
Lemma D_3f4ac : decode_any W_3f4ac = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4b0 : bv 32 := 0x0205b423.
Lemma F_3f4b0 : fetch_word Asan.M.loaded_segments (0x3f4b0 : word) = Some W_3f4b0.
Proof. vm_refl. Qed.
Lemma D_3f4b0 : decode_any W_3f4b0 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4b4 : bv 32 := 0x0205b823.
Lemma F_3f4b4 : fetch_word Asan.M.loaded_segments (0x3f4b4 : word) = Some W_3f4b4.
Proof. vm_refl. Qed.
Lemma D_3f4b4 : decode_any W_3f4b4 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4b8 : bv 32 := 0x0205bc23.
Lemma F_3f4b8 : fetch_word Asan.M.loaded_segments (0x3f4b8 : word) = Some W_3f4b8.
Proof. vm_refl. Qed.
Lemma D_3f4b8 : decode_any W_3f4b8 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4bc : bv 32 := 0x0405b023.
Lemma F_3f4bc : fetch_word Asan.M.loaded_segments (0x3f4bc : word) = Some W_3f4bc.
Proof. vm_refl. Qed.
Lemma D_3f4bc : decode_any W_3f4bc = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4c0 : bv 32 := 0x0405b423.
Lemma F_3f4c0 : fetch_word Asan.M.loaded_segments (0x3f4c0 : word) = Some W_3f4c0.
Proof. vm_refl. Qed.
Lemma D_3f4c0 : decode_any W_3f4c0 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4c4 : bv 32 := 0x0405b823.
Lemma F_3f4c4 : fetch_word Asan.M.loaded_segments (0x3f4c4 : word) = Some W_3f4c4.
Proof. vm_refl. Qed.
Lemma D_3f4c4 : decode_any W_3f4c4 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4c8 : bv 32 := 0x0405bc23.
Lemma F_3f4c8 : fetch_word Asan.M.loaded_segments (0x3f4c8 : word) = Some W_3f4c8.
Proof. vm_refl. Qed.
Lemma D_3f4c8 : decode_any W_3f4c8 = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4cc : bv 32 := 0x0605b023.
Lemma F_3f4cc : fetch_word Asan.M.loaded_segments (0x3f4cc : word) = Some W_3f4cc.
Proof. vm_refl. Qed.
Lemma D_3f4cc : decode_any W_3f4cc = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4d0 : bv 32 := 0x0605b423.
Lemma F_3f4d0 : fetch_word Asan.M.loaded_segments (0x3f4d0 : word) = Some W_3f4d0.
Proof. vm_refl. Qed.
Lemma D_3f4d0 : decode_any W_3f4d0 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4d4 : bv 32 := 0x0605b823.
Lemma F_3f4d4 : fetch_word Asan.M.loaded_segments (0x3f4d4 : word) = Some W_3f4d4.
Proof. vm_refl. Qed.
Lemma D_3f4d4 : decode_any W_3f4d4 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4d8 : bv 32 := 0x0605bc23.
Lemma F_3f4d8 : fetch_word Asan.M.loaded_segments (0x3f4d8 : word) = Some W_3f4d8.
Proof. vm_refl. Qed.
Lemma D_3f4d8 : decode_any W_3f4d8 = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4dc : bv 32 := 0x01813083.
Lemma F_3f4dc : fetch_word Asan.M.loaded_segments (0x3f4dc : word) = Some W_3f4dc.
Proof. vm_refl. Qed.
Lemma D_3f4dc : decode_any W_3f4dc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4e0 : bv 32 := 0x01013403.
Lemma F_3f4e0 : fetch_word Asan.M.loaded_segments (0x3f4e0 : word) = Some W_3f4e0.
Proof. vm_refl. Qed.
Lemma D_3f4e0 : decode_any W_3f4e0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4e4 : bv 32 := 0x00813483.
Lemma F_3f4e4 : fetch_word Asan.M.loaded_segments (0x3f4e4 : word) = Some W_3f4e4.
Proof. vm_refl. Qed.
Lemma D_3f4e4 : decode_any W_3f4e4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4e8 : bv 32 := 0x00013903.
Lemma F_3f4e8 : fetch_word Asan.M.loaded_segments (0x3f4e8 : word) = Some W_3f4e8.
Proof. vm_refl. Qed.
Lemma D_3f4e8 : decode_any W_3f4e8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4ec : bv 32 := 0x02010113.
Lemma F_3f4ec : fetch_word Asan.M.loaded_segments (0x3f4ec : word) = Some W_3f4ec.
Proof. vm_refl. Qed.
Lemma D_3f4ec : decode_any W_3f4ec = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f4f0 : bv 32 := 0x00008067.
Lemma F_3f4f0 : fetch_word Asan.M.loaded_segments (0x3f4f0 : word) = Some W_3f4f0.
Proof. vm_refl. Qed.
Lemma D_3f4f0 : decode_any W_3f4f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_3f510 : bv 32 := 0x0006c597.
Lemma F_3f510 : fetch_word Asan.M.loaded_segments (0x3f510 : word) = Some W_3f510.
Proof. vm_refl. Qed.
Lemma D_3f510 : decode_any W_3f510 = Some (Auipc 11 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f514 : bv 32 := 0x9705b583.
Lemma F_3f514 : fetch_word Asan.M.loaded_segments (0x3f514 : word) = Some W_3f514.
Proof. vm_refl. Qed.
Lemma D_3f514 : decode_any W_3f514 = Some (Load SZ8 true 11 11 2416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f518 : bv 32 := 0x0005b583.
Lemma F_3f518 : fetch_word Asan.M.loaded_segments (0x3f518 : word) = Some W_3f518.
Proof. vm_refl. Qed.
Lemma D_3f518 : decode_any W_3f518 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f51c : bv 32 := 0xfff58613.
Lemma F_3f51c : fetch_word Asan.M.loaded_segments (0x3f51c : word) = Some W_3f51c.
Proof. vm_refl. Qed.
Lemma D_3f51c : decode_any W_3f51c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f520 : bv 32 := 0x00c5b6b3.
Lemma F_3f520 : fetch_word Asan.M.loaded_segments (0x3f520 : word) = Some W_3f520.
Proof. vm_refl. Qed.
Lemma D_3f520 : decode_any W_3f520 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f524 : bv 32 := 0xfff68693.
Lemma F_3f524 : fetch_word Asan.M.loaded_segments (0x3f524 : word) = Some W_3f524.
Proof. vm_refl. Qed.
Lemma D_3f524 : decode_any W_3f524 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f528 : bv 32 := 0x00c6f6b3.
Lemma F_3f528 : fetch_word Asan.M.loaded_segments (0x3f528 : word) = Some W_3f528.
Proof. vm_refl. Qed.
Lemma D_3f528 : decode_any W_3f528 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f52c : bv 32 := 0x04a6f263.
Lemma F_3f52c : fetch_word Asan.M.loaded_segments (0x3f52c : word) = Some W_3f52c.
Proof. vm_refl. Qed.
Lemma D_3f52c : decode_any W_3f52c = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f530 : bv 32 := 0x0006c697.
Lemma F_3f530 : fetch_word Asan.M.loaded_segments (0x3f530 : word) = Some W_3f530.
Proof. vm_refl. Qed.
Lemma D_3f530 : decode_any W_3f530 = Some (Auipc 13 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f534 : bv 32 := 0x9586b683.
Lemma F_3f534 : fetch_word Asan.M.loaded_segments (0x3f534 : word) = Some W_3f534.
Proof. vm_refl. Qed.
Lemma D_3f534 : decode_any W_3f534 = Some (Load SZ8 true 13 13 2392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f538 : bv 32 := 0x0006c717.
Lemma F_3f538 : fetch_word Asan.M.loaded_segments (0x3f538 : word) = Some W_3f538.
Proof. vm_refl. Qed.
Lemma D_3f538 : decode_any W_3f538 = Some (Auipc 14 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f53c : bv 32 := 0x95873703.
Lemma F_3f53c : fetch_word Asan.M.loaded_segments (0x3f53c : word) = Some W_3f53c.
Proof. vm_refl. Qed.
Lemma D_3f53c : decode_any W_3f53c = Some (Load SZ8 true 14 14 2392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f540 : bv 32 := 0x0006b803.
Lemma F_3f540 : fetch_word Asan.M.loaded_segments (0x3f540 : word) = Some W_3f540.
Proof. vm_refl. Qed.
Lemma D_3f540 : decode_any W_3f540 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f544 : bv 32 := 0x00073683.
Lemma F_3f544 : fetch_word Asan.M.loaded_segments (0x3f544 : word) = Some W_3f544.
Proof. vm_refl. Qed.
Lemma D_3f544 : decode_any W_3f544 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f548 : bv 32 := 0xfff80793.
Lemma F_3f548 : fetch_word Asan.M.loaded_segments (0x3f548 : word) = Some W_3f548.
Proof. vm_refl. Qed.
Lemma D_3f548 : decode_any W_3f548 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f54c : bv 32 := 0x00a7f463.
Lemma F_3f54c : fetch_word Asan.M.loaded_segments (0x3f54c : word) = Some W_3f54c.
Proof. vm_refl. Qed.
Lemma D_3f54c : decode_any W_3f54c = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f550 : bv 32 := 0x02a6f063.
Lemma F_3f550 : fetch_word Asan.M.loaded_segments (0x3f550 : word) = Some W_3f550.
Proof. vm_refl. Qed.
Lemma D_3f550 : decode_any W_3f550 = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f554 : bv 32 := 0x0006c717.
Lemma F_3f554 : fetch_word Asan.M.loaded_segments (0x3f554 : word) = Some W_3f554.
Proof. vm_refl. Qed.
Lemma D_3f554 : decode_any W_3f554 = Some (Auipc 14 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f558 : bv 32 := 0x94473703.
Lemma F_3f558 : fetch_word Asan.M.loaded_segments (0x3f558 : word) = Some W_3f558.
Proof. vm_refl. Qed.
Lemma D_3f558 : decode_any W_3f558 = Some (Load SZ8 true 14 14 2372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f55c : bv 32 := 0x00073283.
Lemma F_3f55c : fetch_word Asan.M.loaded_segments (0x3f55c : word) = Some W_3f55c.
Proof. vm_refl. Qed.
Lemma D_3f55c : decode_any W_3f55c = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f560 : bv 32 := 0x0032d713.
Lemma F_3f560 : fetch_word Asan.M.loaded_segments (0x3f560 : word) = Some W_3f560.
Proof. vm_refl. Qed.
Lemma D_3f560 : decode_any W_3f560 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f564 : bv 32 := 0x00b708b3.
Lemma F_3f564 : fetch_word Asan.M.loaded_segments (0x3f564 : word) = Some W_3f564.
Proof. vm_refl. Qed.
Lemma D_3f564 : decode_any W_3f564 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f568 : bv 32 := 0x00a2ea63.
Lemma F_3f568 : fetch_word Asan.M.loaded_segments (0x3f568 : word) = Some W_3f568.
Proof. vm_refl. Qed.
Lemma D_3f568 : decode_any W_3f568 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f56c : bv 32 := 0x00a8f863.
Lemma F_3f56c : fetch_word Asan.M.loaded_segments (0x3f56c : word) = Some W_3f56c.
Proof. vm_refl. Qed.
Lemma D_3f56c : decode_any W_3f56c = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f570 : bv 32 := 0x00355513.
Lemma F_3f570 : fetch_word Asan.M.loaded_segments (0x3f570 : word) = Some W_3f570.
Proof. vm_refl. Qed.
Lemma D_3f570 : decode_any W_3f570 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f574 : bv 32 := 0x00a58533.
Lemma F_3f574 : fetch_word Asan.M.loaded_segments (0x3f574 : word) = Some W_3f574.
Proof. vm_refl. Qed.
Lemma D_3f574 : decode_any W_3f574 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3f578 : bv 32 := 0x00008067.
Lemma F_3f578 : fetch_word Asan.M.loaded_segments (0x3f578 : word) = Some W_3f578.
Proof. vm_refl. Qed.
Lemma D_3f578 : decode_any W_3f578 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
