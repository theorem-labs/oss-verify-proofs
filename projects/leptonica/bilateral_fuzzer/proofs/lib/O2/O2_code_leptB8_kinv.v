(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2ce3c : bv 32 := 0xfc010113.
Lemma F_2ce3c : fetch_word Plain.M.loaded_segments (0x2ce94 : word) = Some W_2ce3c.
Proof. vm_refl. Qed.
Lemma D_2ce3c : decode_any W_2ce3c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce40 : bv 32 := 0x02113c23.
Lemma F_2ce40 : fetch_word Plain.M.loaded_segments (0x2ce98 : word) = Some W_2ce40.
Proof. vm_refl. Qed.
Lemma D_2ce40 : decode_any W_2ce40 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce44 : bv 32 := 0x02813823.
Lemma F_2ce44 : fetch_word Plain.M.loaded_segments (0x2ce9c : word) = Some W_2ce44.
Proof. vm_refl. Qed.
Lemma D_2ce44 : decode_any W_2ce44 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce48 : bv 32 := 0x02913423.
Lemma F_2ce48 : fetch_word Plain.M.loaded_segments (0x2cea0 : word) = Some W_2ce48.
Proof. vm_refl. Qed.
Lemma D_2ce48 : decode_any W_2ce48 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce4c : bv 32 := 0x03213023.
Lemma F_2ce4c : fetch_word Plain.M.loaded_segments (0x2cea4 : word) = Some W_2ce4c.
Proof. vm_refl. Qed.
Lemma D_2ce4c : decode_any W_2ce4c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce50 : bv 32 := 0x01313c23.
Lemma F_2ce50 : fetch_word Plain.M.loaded_segments (0x2cea8 : word) = Some W_2ce50.
Proof. vm_refl. Qed.
Lemma D_2ce50 : decode_any W_2ce50 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce54 : bv 32 := 0x01413823.
Lemma F_2ce54 : fetch_word Plain.M.loaded_segments (0x2ceac : word) = Some W_2ce54.
Proof. vm_refl. Qed.
Lemma D_2ce54 : decode_any W_2ce54 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce58 : bv 32 := 0x01513423.
Lemma F_2ce58 : fetch_word Plain.M.loaded_segments (0x2ceb0 : word) = Some W_2ce58.
Proof. vm_refl. Qed.
Lemma D_2ce58 : decode_any W_2ce58 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce5c : bv 32 := 0x0a050c63.
Lemma F_2ce5c : fetch_word Plain.M.loaded_segments (0x2ceb4 : word) = Some W_2ce5c.
Proof. vm_refl. Qed.
Lemma D_2ce5c : decode_any W_2ce5c = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce60 : bv 32 := 0x00050413.
Lemma F_2ce60 : fetch_word Plain.M.loaded_segments (0x2ceb8 : word) = Some W_2ce60.
Proof. vm_refl. Qed.
Lemma D_2ce60 : decode_any W_2ce60 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce64 : bv 32 := 0x00052483.
Lemma F_2ce64 : fetch_word Plain.M.loaded_segments (0x2cebc : word) = Some W_2ce64.
Proof. vm_refl. Qed.
Lemma D_2ce64 : decode_any W_2ce64 = Some (Load SZ4 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce68 : bv 32 := 0x00456983.
Lemma F_2ce68 : fetch_word Plain.M.loaded_segments (0x2cec0 : word) = Some W_2ce68.
Proof. vm_refl. Qed.
Lemma D_2ce68 : decode_any W_2ce68 = Some (Load SZ4 false 19 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce6c : bv 32 := 0x00852a83.
Lemma F_2ce6c : fetch_word Plain.M.loaded_segments (0x2cec4 : word) = Some W_2ce6c.
Proof. vm_refl. Qed.
Lemma D_2ce6c : decode_any W_2ce6c = Some (Load SZ4 true 21 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce70 : bv 32 := 0x00c52a03.
Lemma F_2ce70 : fetch_word Plain.M.loaded_segments (0x2cec8 : word) = Some W_2ce70.
Proof. vm_refl. Qed.
Lemma D_2ce70 : decode_any W_2ce70 = Some (Load SZ4 true 20 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce74 : bv 32 := 0x0009891b.
Lemma F_2ce74 : fetch_word Plain.M.loaded_segments (0x2cecc : word) = Some W_2ce74.
Proof. vm_refl. Qed.
Lemma D_2ce74 : decode_any W_2ce74 = Some (OpImm32 18 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce78 : bv 32 := 0x00048513.
Lemma F_2ce78 : fetch_word Plain.M.loaded_segments (0x2ced0 : word) = Some W_2ce78.
Proof. vm_refl. Qed.
Lemma D_2ce78 : decode_any W_2ce78 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce7c : bv 32 := 0x00090593.
Lemma F_2ce7c : fetch_word Plain.M.loaded_segments (0x2ced4 : word) = Some W_2ce7c.
Proof. vm_refl. Qed.
Lemma D_2ce7c : decode_any W_2ce7c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce80 : bv 32 := 0xf24ff0ef.
Lemma F_2ce80 : fetch_word Plain.M.loaded_segments (0x2ced8 : word) = Some W_2ce80.
Proof. vm_refl. Qed.
Lemma D_2ce80 : decode_any W_2ce80 = Some (Jal 1 2094884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce84 : bv 32 := 0x0a050863.
Lemma F_2ce84 : fetch_word Plain.M.loaded_segments (0x2cedc : word) = Some W_2ce84.
Proof. vm_refl. Qed.
Lemma D_2ce84 : decode_any W_2ce84 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce88 : bv 32 := 0xfffac593.
Lemma F_2ce88 : fetch_word Plain.M.loaded_segments (0x2cee0 : word) = Some W_2ce88.
Proof. vm_refl. Qed.
Lemma D_2ce88 : decode_any W_2ce88 = Some (OpImm ALU_XOR 11 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce8c : bv 32 := 0xfffa4613.
Lemma F_2ce8c : fetch_word Plain.M.loaded_segments (0x2cee4 : word) = Some W_2ce8c.
Proof. vm_refl. Qed.
Lemma D_2ce8c : decode_any W_2ce8c = Some (OpImm ALU_XOR 12 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce90 : bv 32 := 0x00b485b3.
Lemma F_2ce90 : fetch_word Plain.M.loaded_segments (0x2cee8 : word) = Some W_2ce90.
Proof. vm_refl. Qed.
Lemma D_2ce90 : decode_any W_2ce90 = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce94 : bv 32 := 0x00c90633.
Lemma F_2ce94 : fetch_word Plain.M.loaded_segments (0x2ceec : word) = Some W_2ce94.
Proof. vm_refl. Qed.
Lemma D_2ce94 : decode_any W_2ce94 = Some (Op ALU_ADD 12 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce98 : bv 32 := 0x00b52423.
Lemma F_2ce98 : fetch_word Plain.M.loaded_segments (0x2cef0 : word) = Some W_2ce98.
Proof. vm_refl. Qed.
Lemma D_2ce98 : decode_any W_2ce98 = Some (Store SZ4 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ce9c : bv 32 := 0x00c52623.
Lemma F_2ce9c : fetch_word Plain.M.loaded_segments (0x2cef4 : word) = Some W_2ce9c.
Proof. vm_refl. Qed.
Lemma D_2ce9c : decode_any W_2ce9c = Some (Store SZ4 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cea0 : bv 32 := 0x0e905263.
Lemma F_2cea0 : fetch_word Plain.M.loaded_segments (0x2cef8 : word) = Some W_2cea0.
Proof. vm_refl. Qed.
Lemma D_2cea0 : decode_any W_2cea0 = Some (Branch BC_GE 0 9 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cea4 : bv 32 := 0x00000593.
Lemma F_2cea4 : fetch_word Plain.M.loaded_segments (0x2cefc : word) = Some W_2cea4.
Proof. vm_refl. Qed.
Lemma D_2cea4 : decode_any W_2cea4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cea8 : bv 32 := 0x00291613.
Lemma F_2cea8 : fetch_word Plain.M.loaded_segments (0x2cf00 : word) = Some W_2cea8.
Proof. vm_refl. Qed.
Lemma D_2cea8 : decode_any W_2cea8 = Some (ShiftImm ALU_SLL 12 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ceac : bv 32 := 0x00299993.
Lemma F_2ceac : fetch_word Plain.M.loaded_segments (0x2cf04 : word) = Some W_2ceac.
Proof. vm_refl. Qed.
Lemma D_2ceac : decode_any W_2ceac = Some (ShiftImm ALU_SLL 19 19 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ceb0 : bv 32 := 0xffc60613.
Lemma F_2ceb0 : fetch_word Plain.M.loaded_segments (0x2cf08 : word) = Some W_2ceb0.
Proof. vm_refl. Qed.
Lemma D_2ceb0 : decode_any W_2ceb0 = Some (OpImm ALU_ADD 12 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ceb4 : bv 32 := 0x413606b3.
Lemma F_2ceb4 : fetch_word Plain.M.loaded_segments (0x2cf0c : word) = Some W_2ceb4.
Proof. vm_refl. Qed.
Lemma D_2ceb4 : decode_any W_2ceb4 = Some (Op ALU_SUB 13 12 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ceb8 : bv 32 := 0x00349713.
Lemma F_2ceb8 : fetch_word Plain.M.loaded_segments (0x2cf10 : word) = Some W_2ceb8.
Proof. vm_refl. Qed.
Lemma D_2ceb8 : decode_any W_2ceb8 = Some (ShiftImm ALU_SLL 14 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cebc : bv 32 := 0x00c0006f.
Lemma F_2cebc : fetch_word Plain.M.loaded_segments (0x2cf14 : word) = Some W_2cebc.
Proof. vm_refl. Qed.
Lemma D_2cebc : decode_any W_2cebc = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cec0 : bv 32 := 0x00158593.
Lemma F_2cec0 : fetch_word Plain.M.loaded_segments (0x2cf18 : word) = Some W_2cec0.
Proof. vm_refl. Qed.
Lemma D_2cec0 : decode_any W_2cec0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cec4 : bv 32 := 0x0c958063.
Lemma F_2cec4 : fetch_word Plain.M.loaded_segments (0x2cf1c : word) = Some W_2cec4.
Proof. vm_refl. Qed.
Lemma D_2cec4 : decode_any W_2cec4 = Some (Branch BC_EQ 11 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cec8 : bv 32 := 0xff205ce3.
Lemma F_2cec8 : fetch_word Plain.M.loaded_segments (0x2cf20 : word) = Some W_2cec8.
Proof. vm_refl. Qed.
Lemma D_2cec8 : decode_any W_2cec8 = Some (Branch BC_GE 0 18 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cecc : bv 32 := 0x01043783.
Lemma F_2cecc : fetch_word Plain.M.loaded_segments (0x2cf24 : word) = Some W_2cecc.
Proof. vm_refl. Qed.
Lemma D_2cecc : decode_any W_2cecc = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ced0 : bv 32 := 0xfff5c813.
Lemma F_2ced0 : fetch_word Plain.M.loaded_segments (0x2cf28 : word) = Some W_2ced0.
Proof. vm_refl. Qed.
Lemma D_2ced0 : decode_any W_2ced0 = Some (OpImm ALU_XOR 16 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ced4 : bv 32 := 0x01053883.
Lemma F_2ced4 : fetch_word Plain.M.loaded_segments (0x2cf2c : word) = Some W_2ced4.
Proof. vm_refl. Qed.
Lemma D_2ced4 : decode_any W_2ced4 = Some (Load SZ8 true 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ced8 : bv 32 := 0x00381813.
Lemma F_2ced8 : fetch_word Plain.M.loaded_segments (0x2cf30 : word) = Some W_2ced8.
Proof. vm_refl. Qed.
Lemma D_2ced8 : decode_any W_2ced8 = Some (ShiftImm ALU_SLL 16 16 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cedc : bv 32 := 0x01070833.
Lemma F_2cedc : fetch_word Plain.M.loaded_segments (0x2cf34 : word) = Some W_2cedc.
Proof. vm_refl. Qed.
Lemma D_2cedc : decode_any W_2cedc = Some (Op ALU_ADD 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cee0 : bv 32 := 0x010787b3.
Lemma F_2cee0 : fetch_word Plain.M.loaded_segments (0x2cf38 : word) = Some W_2cee0.
Proof. vm_refl. Qed.
Lemma D_2cee0 : decode_any W_2cee0 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cee4 : bv 32 := 0x00359813.
Lemma F_2cee4 : fetch_word Plain.M.loaded_segments (0x2cf3c : word) = Some W_2cee4.
Proof. vm_refl. Qed.
Lemma D_2cee4 : decode_any W_2cee4 = Some (ShiftImm ALU_SLL 16 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cee8 : bv 32 := 0x0007b283.
Lemma F_2cee8 : fetch_word Plain.M.loaded_segments (0x2cf40 : word) = Some W_2cee8.
Proof. vm_refl. Qed.
Lemma D_2cee8 : decode_any W_2cee8 = Some (Load SZ8 true 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ceec : bv 32 := 0x01088833.
Lemma F_2ceec : fetch_word Plain.M.loaded_segments (0x2cf44 : word) = Some W_2ceec.
Proof. vm_refl. Qed.
Lemma D_2ceec : decode_any W_2ceec = Some (Op ALU_ADD 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cef0 : bv 32 := 0x00083783.
Lemma F_2cef0 : fetch_word Plain.M.loaded_segments (0x2cf48 : word) = Some W_2cef0.
Proof. vm_refl. Qed.
Lemma D_2cef0 : decode_any W_2cef0 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cef4 : bv 32 := 0x00c28833.
Lemma F_2cef4 : fetch_word Plain.M.loaded_segments (0x2cf4c : word) = Some W_2cef4.
Proof. vm_refl. Qed.
Lemma D_2cef4 : decode_any W_2cef4 = Some (Op ALU_ADD 16 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cef8 : bv 32 := 0x00d288b3.
Lemma F_2cef8 : fetch_word Plain.M.loaded_segments (0x2cf50 : word) = Some W_2cef8.
Proof. vm_refl. Qed.
Lemma D_2cef8 : decode_any W_2cef8 = Some (Op ALU_ADD 17 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cefc : bv 32 := 0x00082787.
Lemma F_2cefc : fetch_word Plain.M.loaded_segments (0x2cf54 : word) = Some W_2cefc.
Proof. vm_refl. Qed.
Lemma D_2cefc : decode_any W_2cefc = Some (FLoad FMT_S 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf00 : bv 32 := 0xffc80813.
Lemma F_2cf00 : fetch_word Plain.M.loaded_segments (0x2cf58 : word) = Some W_2cf00.
Proof. vm_refl. Qed.
Lemma D_2cf00 : decode_any W_2cf00 = Some (OpImm ALU_ADD 16 16 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf04 : bv 32 := 0x00f7a027.
Lemma F_2cf04 : fetch_word Plain.M.loaded_segments (0x2cf5c : word) = Some W_2cf04.
Proof. vm_refl. Qed.
Lemma D_2cf04 : decode_any W_2cf04 = Some (FStore FMT_S 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf08 : bv 32 := 0x00478793.
Lemma F_2cf08 : fetch_word Plain.M.loaded_segments (0x2cf60 : word) = Some W_2cf08.
Proof. vm_refl. Qed.
Lemma D_2cf08 : decode_any W_2cf08 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf0c : bv 32 := 0xff1818e3.
Lemma F_2cf0c : fetch_word Plain.M.loaded_segments (0x2cf64 : word) = Some W_2cf0c.
Proof. vm_refl. Qed.
Lemma D_2cf0c : decode_any W_2cf0c = Some (Branch BC_NE 16 17 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf10 : bv 32 := 0xfb1ff06f.
Lemma F_2cf10 : fetch_word Plain.M.loaded_segments (0x2cf68 : word) = Some W_2cf10.
Proof. vm_refl. Qed.
Lemma D_2cf10 : decode_any W_2cf10 = Some (Jal 0 2097072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf84 : bv 32 := 0x03813083.
Lemma F_2cf84 : fetch_word Plain.M.loaded_segments (0x2cfdc : word) = Some W_2cf84.
Proof. vm_refl. Qed.
Lemma D_2cf84 : decode_any W_2cf84 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf88 : bv 32 := 0x03013403.
Lemma F_2cf88 : fetch_word Plain.M.loaded_segments (0x2cfe0 : word) = Some W_2cf88.
Proof. vm_refl. Qed.
Lemma D_2cf88 : decode_any W_2cf88 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf8c : bv 32 := 0x02813483.
Lemma F_2cf8c : fetch_word Plain.M.loaded_segments (0x2cfe4 : word) = Some W_2cf8c.
Proof. vm_refl. Qed.
Lemma D_2cf8c : decode_any W_2cf8c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf90 : bv 32 := 0x02013903.
Lemma F_2cf90 : fetch_word Plain.M.loaded_segments (0x2cfe8 : word) = Some W_2cf90.
Proof. vm_refl. Qed.
Lemma D_2cf90 : decode_any W_2cf90 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf94 : bv 32 := 0x01813983.
Lemma F_2cf94 : fetch_word Plain.M.loaded_segments (0x2cfec : word) = Some W_2cf94.
Proof. vm_refl. Qed.
Lemma D_2cf94 : decode_any W_2cf94 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf98 : bv 32 := 0x01013a03.
Lemma F_2cf98 : fetch_word Plain.M.loaded_segments (0x2cff0 : word) = Some W_2cf98.
Proof. vm_refl. Qed.
Lemma D_2cf98 : decode_any W_2cf98 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cf9c : bv 32 := 0x00813a83.
Lemma F_2cf9c : fetch_word Plain.M.loaded_segments (0x2cff4 : word) = Some W_2cf9c.
Proof. vm_refl. Qed.
Lemma D_2cf9c : decode_any W_2cf9c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfa0 : bv 32 := 0x04010113.
Lemma F_2cfa0 : fetch_word Plain.M.loaded_segments (0x2cff8 : word) = Some W_2cfa0.
Proof. vm_refl. Qed.
Lemma D_2cfa0 : decode_any W_2cfa0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfa4 : bv 32 := 0x00008067.
Lemma F_2cfa4 : fetch_word Plain.M.loaded_segments (0x2cffc : word) = Some W_2cfa4.
Proof. vm_refl. Qed.
Lemma D_2cfa4 : decode_any W_2cfa4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
