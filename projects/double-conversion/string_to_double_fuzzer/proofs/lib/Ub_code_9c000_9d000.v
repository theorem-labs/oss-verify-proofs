(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation USEGS := ImgU.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9c1b8 : bv 32 := 0xf94fa0ef.
Lemma F_9c1b8 : fetch_word USEGS (0x9c1b8 : word) = Some W_9c1b8.
Proof. vm_refl. Qed.
Lemma D_9c1b8 : decode_any W_9c1b8 = Some (Jal 1 2074516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1bc : bv 32 := 0x09651863.
Lemma F_9c1bc : fetch_word USEGS (0x9c1bc : word) = Some W_9c1bc.
Proof. vm_refl. Qed.
Lemma D_9c1bc : decode_any W_9c1bc = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1c0 : bv 32 := 0x0584b503.
Lemma F_9c1c0 : fetch_word USEGS (0x9c1c0 : word) = Some W_9c1c0.
Proof. vm_refl. Qed.
Lemma D_9c1c0 : decode_any W_9c1c0 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1c4 : bv 32 := 0x0604b583.
Lemma F_9c1c4 : fetch_word USEGS (0x9c1c4 : word) = Some W_9c1c4.
Proof. vm_refl. Qed.
Lemma D_9c1c4 : decode_any W_9c1c4 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1c8 : bv 32 := 0x00b505b3.
Lemma F_9c1c8 : fetch_word USEGS (0x9c1c8 : word) = Some W_9c1c8.
Proof. vm_refl. Qed.
Lemma D_9c1c8 : decode_any W_9c1c8 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1cc : bv 32 := 0x02b4b023.
Lemma F_9c1cc : fetch_word USEGS (0x9c1cc : word) = Some W_9c1cc.
Proof. vm_refl. Qed.
Lemma D_9c1cc : decode_any W_9c1cc = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1d0 : bv 32 := 0x02a4b423.
Lemma F_9c1d0 : fetch_word USEGS (0x9c1d0 : word) = Some W_9c1d0.
Proof. vm_refl. Qed.
Lemma D_9c1d0 : decode_any W_9c1d0 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1d4 : bv 32 := 0x02a4bc23.
Lemma F_9c1d4 : fetch_word USEGS (0x9c1d4 : word) = Some W_9c1d4.
Proof. vm_refl. Qed.
Lemma D_9c1d4 : decode_any W_9c1d4 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1d8 : bv 32 := 0x00040513.
Lemma F_9c1d8 : fetch_word USEGS (0x9c1d8 : word) = Some W_9c1d8.
Proof. vm_refl. Qed.
Lemma D_9c1d8 : decode_any W_9c1d8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1dc : bv 32 := 0x000ab583.
Lemma F_9c1dc : fetch_word USEGS (0x9c1dc : word) = Some W_9c1dc.
Proof. vm_refl. Qed.
Lemma D_9c1dc : decode_any W_9c1dc = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1e0 : bv 32 := 0x02813603.
Lemma F_9c1e0 : fetch_word USEGS (0x9c1e0 : word) = Some W_9c1e0.
Proof. vm_refl. Qed.
Lemma D_9c1e0 : decode_any W_9c1e0 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1e4 : bv 32 := 0x0cc59a63.
Lemma F_9c1e4 : fetch_word USEGS (0x9c1e4 : word) = Some W_9c1e4.
Proof. vm_refl. Qed.
Lemma D_9c1e4 : decode_any W_9c1e4 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1e8 : bv 32 := 0x06813083.
Lemma F_9c1e8 : fetch_word USEGS (0x9c1e8 : word) = Some W_9c1e8.
Proof. vm_refl. Qed.
Lemma D_9c1e8 : decode_any W_9c1e8 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1ec : bv 32 := 0x06013403.
Lemma F_9c1ec : fetch_word USEGS (0x9c1ec : word) = Some W_9c1ec.
Proof. vm_refl. Qed.
Lemma D_9c1ec : decode_any W_9c1ec = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1f0 : bv 32 := 0x05813483.
Lemma F_9c1f0 : fetch_word USEGS (0x9c1f0 : word) = Some W_9c1f0.
Proof. vm_refl. Qed.
Lemma D_9c1f0 : decode_any W_9c1f0 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1f4 : bv 32 := 0x05013903.
Lemma F_9c1f4 : fetch_word USEGS (0x9c1f4 : word) = Some W_9c1f4.
Proof. vm_refl. Qed.
Lemma D_9c1f4 : decode_any W_9c1f4 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1f8 : bv 32 := 0x04813983.
Lemma F_9c1f8 : fetch_word USEGS (0x9c1f8 : word) = Some W_9c1f8.
Proof. vm_refl. Qed.
Lemma D_9c1f8 : decode_any W_9c1f8 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1fc : bv 32 := 0x04013a03.
Lemma F_9c1fc : fetch_word USEGS (0x9c1fc : word) = Some W_9c1fc.
Proof. vm_refl. Qed.
Lemma D_9c1fc : decode_any W_9c1fc = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c200 : bv 32 := 0x03813a83.
Lemma F_9c200 : fetch_word USEGS (0x9c200 : word) = Some W_9c200.
Proof. vm_refl. Qed.
Lemma D_9c200 : decode_any W_9c200 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c204 : bv 32 := 0x03013b03.
Lemma F_9c204 : fetch_word USEGS (0x9c204 : word) = Some W_9c204.
Proof. vm_refl. Qed.
Lemma D_9c204 : decode_any W_9c204 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c208 : bv 32 := 0x07010113.
Lemma F_9c208 : fetch_word USEGS (0x9c208 : word) = Some W_9c208.
Proof. vm_refl. Qed.
Lemma D_9c208 : decode_any W_9c208 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c20c : bv 32 := 0x00008067.
Lemma F_9c20c : fetch_word USEGS (0x9c20c : word) = Some W_9c20c.
Proof. vm_refl. Qed.
Lemma D_9c20c : decode_any W_9c20c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c210 : bv 32 := 0x00800713.
Lemma F_9c210 : fetch_word USEGS (0x9c210 : word) = Some W_9c210.
Proof. vm_refl. Qed.
Lemma D_9c210 : decode_any W_9c210 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c214 : bv 32 := 0x000a0593.
Lemma F_9c214 : fetch_word USEGS (0x9c214 : word) = Some W_9c214.
Proof. vm_refl. Qed.
Lemma D_9c214 : decode_any W_9c214 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c218 : bv 32 := 0x00e98733.
Lemma F_9c218 : fetch_word USEGS (0x9c218 : word) = Some W_9c218.
Proof. vm_refl. Qed.
Lemma D_9c218 : decode_any W_9c218 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c21c : bv 32 := 0x00073783.
Lemma F_9c21c : fetch_word USEGS (0x9c21c : word) = Some W_9c21c.
Proof. vm_refl. Qed.
Lemma D_9c21c : decode_any W_9c21c = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c220 : bv 32 := 0x40ab0b33.
Lemma F_9c220 : fetch_word USEGS (0x9c220 : word) = Some W_9c220.
Proof. vm_refl. Qed.
Lemma D_9c220 : decode_any W_9c220 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c224 : bv 32 := 0x0784a503.
Lemma F_9c224 : fetch_word USEGS (0x9c224 : word) = Some W_9c224.
Proof. vm_refl. Qed.
Lemma D_9c224 : decode_any W_9c224 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c228 : bv 32 := 0x40c9093b.
Lemma F_9c228 : fetch_word USEGS (0x9c228 : word) = Some W_9c228.
Proof. vm_refl. Qed.
Lemma D_9c228 : decode_any W_9c228 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c22c : bv 32 := 0x40d787b3.
Lemma F_9c22c : fetch_word USEGS (0x9c22c : word) = Some W_9c22c.
Proof. vm_refl. Qed.
Lemma D_9c22c : decode_any W_9c22c = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c230 : bv 32 := 0x00f73023.
Lemma F_9c230 : fetch_word USEGS (0x9c230 : word) = Some W_9c230.
Proof. vm_refl. Qed.
Lemma D_9c230 : decode_any W_9c230 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c234 : bv 32 := 0x04200893.
Lemma F_9c234 : fetch_word USEGS (0x9c234 : word) = Some W_9c234.
Proof. vm_refl. Qed.
Lemma D_9c234 : decode_any W_9c234 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c238 : bv 32 := 0x00090613.
Lemma F_9c238 : fetch_word USEGS (0x9c238 : word) = Some W_9c238.
Proof. vm_refl. Qed.
Lemma D_9c238 : decode_any W_9c238 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c23c : bv 32 := 0x00000073.
Lemma F_9c23c : fetch_word USEGS (0x9c23c : word) = Some W_9c23c.
Proof. vm_refl. Qed.
Lemma D_9c23c : decode_any W_9c23c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9c23c : is_ecall W_9c23c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9c240 : bv 32 := 0xf0cfa0ef.
Lemma F_9c240 : fetch_word USEGS (0x9c240 : word) = Some W_9c240.
Proof. vm_refl. Qed.
Lemma D_9c240 : decode_any W_9c240 = Some (Jal 1 2074380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c244 : bv 32 := 0x000a0993.
Lemma F_9c244 : fetch_word USEGS (0x9c244 : word) = Some W_9c244.
Proof. vm_refl. Qed.
Lemma D_9c244 : decode_any W_9c244 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c248 : bv 32 := 0xf7650ce3.
Lemma F_9c248 : fetch_word USEGS (0x9c248 : word) = Some W_9c248.
Proof. vm_refl. Qed.
Lemma D_9c248 : decode_any W_9c248 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c24c : bv 32 := 0x02054c63.
Lemma F_9c24c : fetch_word USEGS (0x9c24c : word) = Some W_9c24c.
Proof. vm_refl. Qed.
Lemma D_9c24c : decode_any W_9c24c = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c250 : bv 32 := 0x0089b583.
Lemma F_9c250 : fetch_word USEGS (0x9c250 : word) = Some W_9c250.
Proof. vm_refl. Qed.
Lemma D_9c250 : decode_any W_9c250 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c254 : bv 32 := 0x00a5b633.
Lemma F_9c254 : fetch_word USEGS (0x9c254 : word) = Some W_9c254.
Proof. vm_refl. Qed.
Lemma D_9c254 : decode_any W_9c254 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c258 : bv 32 := 0x00461a13.
Lemma F_9c258 : fetch_word USEGS (0x9c258 : word) = Some W_9c258.
Proof. vm_refl. Qed.
Lemma D_9c258 : decode_any W_9c258 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c25c : bv 32 := 0x01498a33.
Lemma F_9c25c : fetch_word USEGS (0x9c25c : word) = Some W_9c25c.
Proof. vm_refl. Qed.
Lemma D_9c25c : decode_any W_9c25c = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c260 : bv 32 := 0x000a3703.
Lemma F_9c260 : fetch_word USEGS (0x9c260 : word) = Some W_9c260.
Proof. vm_refl. Qed.
Lemma D_9c260 : decode_any W_9c260 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c264 : bv 32 := 0x40c006b3.
Lemma F_9c264 : fetch_word USEGS (0x9c264 : word) = Some W_9c264.
Proof. vm_refl. Qed.
Lemma D_9c264 : decode_any W_9c264 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c268 : bv 32 := 0x00b6f6b3.
Lemma F_9c268 : fetch_word USEGS (0x9c268 : word) = Some W_9c268.
Proof. vm_refl. Qed.
Lemma D_9c268 : decode_any W_9c268 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c26c : bv 32 := 0x40d506b3.
Lemma F_9c26c : fetch_word USEGS (0x9c26c : word) = Some W_9c26c.
Proof. vm_refl. Qed.
Lemma D_9c26c : decode_any W_9c26c = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c270 : bv 32 := 0x00d70733.
Lemma F_9c270 : fetch_word USEGS (0x9c270 : word) = Some W_9c270.
Proof. vm_refl. Qed.
Lemma D_9c270 : decode_any W_9c270 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c274 : bv 32 := 0x00ea3023.
Lemma F_9c274 : fetch_word USEGS (0x9c274 : word) = Some W_9c274.
Proof. vm_refl. Qed.
Lemma D_9c274 : decode_any W_9c274 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c278 : bv 32 := 0xf8a5fce3.
Lemma F_9c278 : fetch_word USEGS (0x9c278 : word) = Some W_9c278.
Proof. vm_refl. Qed.
Lemma D_9c278 : decode_any W_9c278 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c27c : bv 32 := 0x01800713.
Lemma F_9c27c : fetch_word USEGS (0x9c27c : word) = Some W_9c27c.
Proof. vm_refl. Qed.
Lemma D_9c27c : decode_any W_9c27c = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c280 : bv 32 := 0xf95ff06f.
Lemma F_9c280 : fetch_word USEGS (0x9c280 : word) = Some W_9c280.
Proof. vm_refl. Qed.
Lemma D_9c280 : decode_any W_9c280 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

