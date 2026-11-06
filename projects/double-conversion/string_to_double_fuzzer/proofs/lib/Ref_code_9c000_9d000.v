(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation PSEGS := ImgP.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9c258 : bv 32 := 0x02a00693.
Lemma F_9c258 : fetch_word PSEGS (0x9c258 : word) = Some W_9c258.
Proof. vm_refl. Qed.
Lemma D_9c258 : decode_any W_9c258 = Some (OpImm ALU_ADD 13 0 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c25c : bv 32 := 0x04d59e63.
Lemma F_9c25c : fetch_word PSEGS (0x9c25c : word) = Some W_9c25c.
Proof. vm_refl. Qed.
Lemma D_9c25c : decode_any W_9c25c = Some (Branch BC_NE 11 13 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c260 : bv 32 := 0x00264583.
Lemma F_9c260 : fetch_word PSEGS (0x9c260 : word) = Some W_9c260.
Proof. vm_refl. Qed.
Lemma D_9c260 : decode_any W_9c260 = Some (Load SZ1 false 11 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c264 : bv 32 := 0xfd058593.
Lemma F_9c264 : fetch_word PSEGS (0x9c264 : word) = Some W_9c264.
Proof. vm_refl. Qed.
Lemma D_9c264 : decode_any W_9c264 = Some (OpImm ALU_ADD 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c268 : bv 32 := 0x00900693.
Lemma F_9c268 : fetch_word PSEGS (0x9c268 : word) = Some W_9c268.
Proof. vm_refl. Qed.
Lemma D_9c268 : decode_any W_9c268 = Some (OpImm ALU_ADD 13 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c26c : bv 32 := 0xfc600793.
Lemma F_9c26c : fetch_word PSEGS (0x9c26c : word) = Some W_9c26c.
Proof. vm_refl. Qed.
Lemma D_9c26c : decode_any W_9c26c = Some (OpImm ALU_ADD 15 0 4038, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c270 : bv 32 := 0x03a00813.
Lemma F_9c270 : fetch_word PSEGS (0x9c270 : word) = Some W_9c270.
Proof. vm_refl. Qed.
Lemma D_9c270 : decode_any W_9c270 = Some (OpImm ALU_ADD 16 0 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c274 : bv 32 := 0x00800893.
Lemma F_9c274 : fetch_word PSEGS (0x9c274 : word) = Some W_9c274.
Proof. vm_refl. Qed.
Lemma D_9c274 : decode_any W_9c274 = Some (OpImm ALU_ADD 17 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c278 : bv 32 := 0x0ab6e263.
Lemma F_9c278 : fetch_word PSEGS (0x9c278 : word) = Some W_9c278.
Proof. vm_refl. Qed.
Lemma D_9c278 : decode_any W_9c278 = Some (Branch BC_LTU 13 11 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c27c : bv 32 := 0x00364683.
Lemma F_9c27c : fetch_word PSEGS (0x9c27c : word) = Some W_9c27c.
Proof. vm_refl. Qed.
Lemma D_9c27c : decode_any W_9c27c = Some (Load SZ1 false 13 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c280 : bv 32 := 0x02400713.
Lemma F_9c280 : fetch_word PSEGS (0x9c280 : word) = Some W_9c280.
Proof. vm_refl. Qed.
Lemma D_9c280 : decode_any W_9c280 = Some (OpImm ALU_ADD 14 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c284 : bv 32 := 0x08e69c63.
Lemma F_9c284 : fetch_word PSEGS (0x9c284 : word) = Some W_9c284.
Proof. vm_refl. Qed.
Lemma D_9c284 : decode_any W_9c284 = Some (Branch BC_NE 13 14 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c288 : bv 32 := 0x0c0a0a63.
Lemma F_9c288 : fetch_word PSEGS (0x9c288 : word) = Some W_9c288.
Proof. vm_refl. Qed.
Lemma D_9c288 : decode_any W_9c288 = Some (Branch BC_EQ 20 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c28c : bv 32 := 0x00459593.
Lemma F_9c28c : fetch_word PSEGS (0x9c28c : word) = Some W_9c28c.
Proof. vm_refl. Qed.
Lemma D_9c28c : decode_any W_9c28c = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c290 : bv 32 := 0x03813683.
Lemma F_9c290 : fetch_word PSEGS (0x9c290 : word) = Some W_9c290.
Proof. vm_refl. Qed.
Lemma D_9c290 : decode_any W_9c290 = Some (Load SZ8 true 13 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c294 : bv 32 := 0x00b685b3.
Lemma F_9c294 : fetch_word PSEGS (0x9c294 : word) = Some W_9c294.
Proof. vm_refl. Qed.
Lemma D_9c294 : decode_any W_9c294 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c298 : bv 32 := 0x0005ac83.
Lemma F_9c298 : fetch_word PSEGS (0x9c298 : word) = Some W_9c298.
Proof. vm_refl. Qed.
Lemma D_9c298 : decode_any W_9c298 = Some (Load SZ4 true 25 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c29c : bv 32 := 0x0d80006f.
Lemma F_9c29c : fetch_word PSEGS (0x9c29c : word) = Some W_9c29c.
Proof. vm_refl. Qed.
Lemma D_9c29c : decode_any W_9c29c = Some (Jal 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2a0 : bv 32 := 0x00000293.
Lemma F_9c2a0 : fetch_word PSEGS (0x9c2a0 : word) = Some W_9c2a0.
Proof. vm_refl. Qed.
Lemma D_9c2a0 : decode_any W_9c2a0 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2a4 : bv 32 := 0xfff00c93.
Lemma F_9c2a4 : fetch_word PSEGS (0x9c2a4 : word) = Some W_9c2a4.
Proof. vm_refl. Qed.
Lemma D_9c2a4 : decode_any W_9c2a4 = Some (OpImm ALU_ADD 25 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2a8 : bv 32 := 0xfc600793.
Lemma F_9c2a8 : fetch_word PSEGS (0x9c2a8 : word) = Some W_9c2a8.
Proof. vm_refl. Qed.
Lemma D_9c2a8 : decode_any W_9c2a8 = Some (OpImm ALU_ADD 15 0 4038, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2ac : bv 32 := 0x03a00813.
Lemma F_9c2ac : fetch_word PSEGS (0x9c2ac : word) = Some W_9c2ac.
Proof. vm_refl. Qed.
Lemma D_9c2ac : decode_any W_9c2ac = Some (OpImm ALU_ADD 16 0 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2b0 : bv 32 := 0x00800893.
Lemma F_9c2b0 : fetch_word PSEGS (0x9c2b0 : word) = Some W_9c2b0.
Proof. vm_refl. Qed.
Lemma D_9c2b0 : decode_any W_9c2b0 = Some (OpImm ALU_ADD 17 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2b4 : bv 32 := 0x0cc0006f.
Lemma F_9c2b4 : fetch_word PSEGS (0x9c2b4 : word) = Some W_9c2b4.
Proof. vm_refl. Qed.
Lemma D_9c2b4 : decode_any W_9c2b4 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2b8 : bv 32 := 0x00160613.
Lemma F_9c2b8 : fetch_word PSEGS (0x9c2b8 : word) = Some W_9c2b8.
Proof. vm_refl. Qed.
Lemma D_9c2b8 : decode_any W_9c2b8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2bc : bv 32 := 0xfd058593.
Lemma F_9c2bc : fetch_word PSEGS (0x9c2bc : word) = Some W_9c2bc.
Proof. vm_refl. Qed.
Lemma D_9c2bc : decode_any W_9c2bc = Some (OpImm ALU_ADD 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2c0 : bv 32 := 0x00100293.
Lemma F_9c2c0 : fetch_word PSEGS (0x9c2c0 : word) = Some W_9c2c0.
Proof. vm_refl. Qed.
Lemma D_9c2c0 : decode_any W_9c2c0 = Some (OpImm ALU_ADD 5 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2c4 : bv 32 := 0x00900693.
Lemma F_9c2c4 : fetch_word PSEGS (0x9c2c4 : word) = Some W_9c2c4.
Proof. vm_refl. Qed.
Lemma D_9c2c4 : decode_any W_9c2c4 = Some (OpImm ALU_ADD 13 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2c8 : bv 32 := 0x00800893.
Lemma F_9c2c8 : fetch_word PSEGS (0x9c2c8 : word) = Some W_9c2c8.
Proof. vm_refl. Qed.
Lemma D_9c2c8 : decode_any W_9c2c8 = Some (OpImm ALU_ADD 17 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2cc : bv 32 := 0x00000c93.
Lemma F_9c2cc : fetch_word PSEGS (0x9c2cc : word) = Some W_9c2cc.
Proof. vm_refl. Qed.
Lemma D_9c2cc : decode_any W_9c2cc = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2d0 : bv 32 := 0x06b6ec63.
Lemma F_9c2d0 : fetch_word PSEGS (0x9c2d0 : word) = Some W_9c2d0.
Proof. vm_refl. Qed.
Lemma D_9c2d0 : decode_any W_9c2d0 = Some (Branch BC_LTU 13 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2d4 : bv 32 := 0x00a00813.
Lemma F_9c2d4 : fetch_word PSEGS (0x9c2d4 : word) = Some W_9c2d4.
Proof. vm_refl. Qed.
Lemma D_9c2d4 : decode_any W_9c2d4 = Some (OpImm ALU_ADD 16 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2d8 : bv 32 := 0x0340006f.
Lemma F_9c2d8 : fetch_word PSEGS (0x9c2d8 : word) = Some W_9c2d8.
Proof. vm_refl. Qed.
Lemma D_9c2d8 : decode_any W_9c2d8 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2dc : bv 32 := 0x030c86bb.
Lemma F_9c2dc : fetch_word PSEGS (0x9c2dc : word) = Some W_9c2dc.
Proof. vm_refl. Qed.
Lemma D_9c2dc : decode_any W_9c2dc = Some (Mul32 M_MUL 13 25 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2e0 : bv 32 := 0x0005871b.
Lemma F_9c2e0 : fetch_word PSEGS (0x9c2e0 : word) = Some W_9c2e0.
Proof. vm_refl. Qed.
Lemma D_9c2e0 : decode_any W_9c2e0 = Some (OpImm32 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2e4 : bv 32 := 0x0096c7b3.
Lemma F_9c2e4 : fetch_word PSEGS (0x9c2e4 : word) = Some W_9c2e4.
Proof. vm_refl. Qed.
Lemma D_9c2e4 : decode_any W_9c2e4 = Some (Op ALU_XOR 15 13 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2e8 : bv 32 := 0x00e7b733.
Lemma F_9c2e8 : fetch_word PSEGS (0x9c2e8 : word) = Some W_9c2e8.
Proof. vm_refl. Qed.
Lemma D_9c2e8 : decode_any W_9c2e8 = Some (Op ALU_SLTU 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2ec : bv 32 := 0x00b685bb.
Lemma F_9c2ec : fetch_word PSEGS (0x9c2ec : word) = Some W_9c2ec.
Proof. vm_refl. Qed.
Lemma D_9c2ec : decode_any W_9c2ec = Some (Op32 ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2f0 : bv 32 := 0x40e006bb.
Lemma F_9c2f0 : fetch_word PSEGS (0x9c2f0 : word) = Some W_9c2f0.
Proof. vm_refl. Qed.
Lemma D_9c2f0 : decode_any W_9c2f0 = Some (Op32 ALU_SUB 13 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2f4 : bv 32 := 0x00b6ecb3.
Lemma F_9c2f4 : fetch_word PSEGS (0x9c2f4 : word) = Some W_9c2f4.
Proof. vm_refl. Qed.
Lemma D_9c2f4 : decode_any W_9c2f4 = Some (Op ALU_OR 25 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2f8 : bv 32 := 0x00164583.
Lemma F_9c2f8 : fetch_word PSEGS (0x9c2f8 : word) = Some W_9c2f8.
Proof. vm_refl. Qed.
Lemma D_9c2f8 : decode_any W_9c2f8 = Some (Load SZ1 false 11 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c2fc : bv 32 := 0x00160693.
Lemma F_9c2fc : fetch_word PSEGS (0x9c2fc : word) = Some W_9c2fc.
Proof. vm_refl. Qed.
Lemma D_9c2fc : decode_any W_9c2fc = Some (OpImm ALU_ADD 13 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c300 : bv 32 := 0xfd058593.
Lemma F_9c300 : fetch_word PSEGS (0x9c300 : word) = Some W_9c300.
Proof. vm_refl. Qed.
Lemma D_9c300 : decode_any W_9c300 = Some (OpImm ALU_ADD 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c304 : bv 32 := 0x00068613.
Lemma F_9c304 : fetch_word PSEGS (0x9c304 : word) = Some W_9c304.
Proof. vm_refl. Qed.
Lemma D_9c304 : decode_any W_9c304 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c308 : bv 32 := 0x0305fe63.
Lemma F_9c308 : fetch_word PSEGS (0x9c308 : word) = Some W_9c308.
Proof. vm_refl. Qed.
Lemma D_9c308 : decode_any W_9c308 = Some (Branch BC_GEU 11 16 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c30c : bv 32 := 0x06813683.
Lemma F_9c30c : fetch_word PSEGS (0x9c30c : word) = Some W_9c30c.
Proof. vm_refl. Qed.
Lemma D_9c30c : decode_any W_9c30c = Some (Load SZ8 true 13 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c310 : bv 32 := 0xfd96f6e3.
Lemma F_9c310 : fetch_word PSEGS (0x9c310 : word) = Some W_9c310.
Proof. vm_refl. Qed.
Lemma D_9c310 : decode_any W_9c310 = Some (Branch BC_GEU 13 25 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c314 : bv 32 := 0xfff00c93.
Lemma F_9c314 : fetch_word PSEGS (0x9c314 : word) = Some W_9c314.
Proof. vm_refl. Qed.
Lemma D_9c314 : decode_any W_9c314 = Some (OpImm ALU_ADD 25 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c318 : bv 32 := 0xfe1ff06f.
Lemma F_9c318 : fetch_word PSEGS (0x9c318 : word) = Some W_9c318.
Proof. vm_refl. Qed.
Lemma D_9c318 : decode_any W_9c318 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c31c : bv 32 := 0x05813583.
Lemma F_9c31c : fetch_word PSEGS (0x9c31c : word) = Some W_9c31c.
Proof. vm_refl. Qed.
Lemma D_9c31c : decode_any W_9c31c = Some (Load SZ8 true 11 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c320 : bv 32 := 0x1e0592e3.
Lemma F_9c320 : fetch_word PSEGS (0x9c320 : word) = Some W_9c320.
Proof. vm_refl. Qed.
Lemma D_9c320 : decode_any W_9c320 = Some (Branch BC_NE 11 0 2532, 4%Z).
Proof. vm_refl. Qed.

