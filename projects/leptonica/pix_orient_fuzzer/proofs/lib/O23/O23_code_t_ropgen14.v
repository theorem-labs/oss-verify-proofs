(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7a0a4 : bv 32 := 0x09813683.
Lemma F_7a0a4 : fetch_word Plain.M.loaded_segments (0x7a0fc : word) = Some W_7a0a4.
Proof. vm_refl. Qed.
Lemma D_7a0a4 : decode_any W_7a0a4 = Some (Load SZ8 true 13 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0a8 : bv 32 := 0x07813583.
Lemma F_7a0a8 : fetch_word Plain.M.loaded_segments (0x7a100 : word) = Some W_7a0a8.
Proof. vm_refl. Qed.
Lemma D_7a0a8 : decode_any W_7a0a8 = Some (Load SZ8 true 11 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0ac : bv 32 := 0x08013b03.
Lemma F_7a0ac : fetch_word Plain.M.loaded_segments (0x7a104 : word) = Some W_7a0ac.
Proof. vm_refl. Qed.
Lemma D_7a0ac : decode_any W_7a0ac = Some (Load SZ8 true 22 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b0 : bv 32 := 0x01a9e7b3.
Lemma F_7a0b0 : fetch_word Plain.M.loaded_segments (0x7a108 : word) = Some W_7a0b0.
Proof. vm_refl. Qed.
Lemma D_7a0b0 : decode_any W_7a0b0 = Some (Op ALU_OR 15 19 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b4 : bv 32 := 0x01f7f793.
Lemma F_7a0b4 : fetch_word Plain.M.loaded_segments (0x7a10c : word) = Some W_7a0b4.
Proof. vm_refl. Qed.
Lemma D_7a0b4 : decode_any W_7a0b4 = Some (OpImm ALU_AND 15 15 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b8 : bv 32 := 0xfff58a93.
Lemma F_7a0b8 : fetch_word Plain.M.loaded_segments (0x7a110 : word) = Some W_7a0b8.
Proof. vm_refl. Qed.
Lemma D_7a0b8 : decode_any W_7a0b8 = Some (OpImm ALU_ADD 21 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0bc : bv 32 := 0x0a078463.
Lemma F_7a0bc : fetch_word Plain.M.loaded_segments (0x7a114 : word) = Some W_7a0bc.
Proof. vm_refl. Qed.
Lemma D_7a0bc : decode_any W_7a0bc = Some (Branch BC_EQ 15 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0c0 : bv 32 := 0x01f9fa13.
Lemma F_7a0c0 : fetch_word Plain.M.loaded_segments (0x7a118 : word) = Some W_7a0c0.
Proof. vm_refl. Qed.
Lemma D_7a0c0 : decode_any W_7a0c0 = Some (OpImm ALU_AND 20 19 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0c4 : bv 32 := 0x01fd7f13.
Lemma F_7a0c4 : fetch_word Plain.M.loaded_segments (0x7a11c : word) = Some W_7a0c4.
Proof. vm_refl. Qed.
Lemma D_7a0c4 : decode_any W_7a0c4 = Some (OpImm ALU_AND 30 26 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0c8 : bv 32 := 0xfff98517.
Lemma F_7a0c8 : fetch_word Plain.M.loaded_segments (0x7a120 : word) = Some W_7a0c8.
Proof. vm_refl. Qed.
Lemma D_7a0c8 : decode_any W_7a0c8 = Some (Auipc 10 1048472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0cc : bv 32 := 0x68b50513.
Lemma F_7a0cc : fetch_word Plain.M.loaded_segments (0x7a124 : word) = Some W_7a0cc.
Proof. vm_refl. Qed.
Lemma D_7a0cc : decode_any W_7a0cc = Some (OpImm ALU_ADD 10 10 1675, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0d0 : bv 32 := 0x0bea1a63.
Lemma F_7a0d0 : fetch_word Plain.M.loaded_segments (0x7a128 : word) = Some W_7a0d0.
Proof. vm_refl. Qed.
Lemma D_7a0d0 : decode_any W_7a0d0 = Some (Branch BC_NE 20 30 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a228 : bv 32 := 0x25d37463.
Lemma F_7a228 : fetch_word Plain.M.loaded_segments (0x7a280 : word) = Some W_7a228.
Proof. vm_refl. Qed.
Lemma D_7a228 : decode_any W_7a228 = Some (Branch BC_GEU 6 29 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a22c : bv 32 := 0x00000493.
Lemma F_7a22c : fetch_word Plain.M.loaded_segments (0x7a284 : word) = Some W_7a22c.
Proof. vm_refl. Qed.
Lemma D_7a22c : decode_any W_7a22c = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a230 : bv 32 := 0x00000e93.
Lemma F_7a230 : fetch_word Plain.M.loaded_segments (0x7a288 : word) = Some W_7a230.
Proof. vm_refl. Qed.
Lemma D_7a230 : decode_any W_7a230 = Some (OpImm ALU_ADD 29 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a234 : bv 32 := 0x00000e13.
Lemma F_7a234 : fetch_word Plain.M.loaded_segments (0x7a28c : word) = Some W_7a234.
Proof. vm_refl. Qed.
Lemma D_7a234 : decode_any W_7a234 = Some (OpImm ALU_ADD 28 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a238 : bv 32 := 0x00000293.
Lemma F_7a238 : fetch_word Plain.M.loaded_segments (0x7a290 : word) = Some W_7a238.
Proof. vm_refl. Qed.
Lemma D_7a238 : decode_any W_7a238 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a23c : bv 32 := 0x00000d13.
Lemma F_7a23c : fetch_word Plain.M.loaded_segments (0x7a294 : word) = Some W_7a23c.
Proof. vm_refl. Qed.
Lemma D_7a23c : decode_any W_7a23c = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a240 : bv 32 := 0x0143033b.
Lemma F_7a240 : fetch_word Plain.M.loaded_segments (0x7a298 : word) = Some W_7a240.
Proof. vm_refl. Qed.
Lemma D_7a240 : decode_any W_7a240 = Some (Op32 ALU_ADD 6 6 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a244 : bv 32 := 0xfffa5397.
Lemma F_7a244 : fetch_word Plain.M.loaded_segments (0x7a29c : word) = Some W_7a244.
Proof. vm_refl. Qed.
Lemma D_7a244 : decode_any W_7a244 = Some (Auipc 7 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a248 : bv 32 := 0x00231313.
Lemma F_7a248 : fetch_word Plain.M.loaded_segments (0x7a2a0 : word) = Some W_7a248.
Proof. vm_refl. Qed.
Lemma D_7a248 : decode_any W_7a248 = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a24c : bv 32 := 0x18838393.
Lemma F_7a24c : fetch_word Plain.M.loaded_segments (0x7a2a4 : word) = Some W_7a24c.
Proof. vm_refl. Qed.
Lemma D_7a24c : decode_any W_7a24c = Some (OpImm ALU_ADD 7 7 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a250 : bv 32 := 0x00638333.
Lemma F_7a250 : fetch_word Plain.M.loaded_segments (0x7a2a8 : word) = Some W_7a250.
Proof. vm_refl. Qed.
Lemma D_7a250 : decode_any W_7a250 = Some (Op ALU_ADD 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a254 : bv 32 := 0x00032303.
Lemma F_7a254 : fetch_word Plain.M.loaded_segments (0x7a2ac : word) = Some W_7a254.
Proof. vm_refl. Qed.
Lemma D_7a254 : decode_any W_7a254 = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a258 : bv 32 := 0x00100393.
Lemma F_7a258 : fetch_word Plain.M.loaded_segments (0x7a2b0 : word) = Some W_7a258.
Proof. vm_refl. Qed.
Lemma D_7a258 : decode_any W_7a258 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a25c : bv 32 := 0x00713023.
Lemma F_7a25c : fetch_word Plain.M.loaded_segments (0x7a2b4 : word) = Some W_7a25c.
Proof. vm_refl. Qed.
Lemma D_7a25c : decode_any W_7a25c = Some (Store SZ8 2 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a260 : bv 32 := 0x01237933.
Lemma F_7a260 : fetch_word Plain.M.loaded_segments (0x7a2b8 : word) = Some W_7a260.
Proof. vm_refl. Qed.
Lemma D_7a260 : decode_any W_7a260 = Some (Op ALU_AND 18 6 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a264 : bv 32 := 0x00100993.
Lemma F_7a264 : fetch_word Plain.M.loaded_segments (0x7a2bc : word) = Some W_7a264.
Proof. vm_refl. Qed.
Lemma D_7a264 : decode_any W_7a264 = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a268 : bv 32 := 0x2e40006f.
Lemma F_7a268 : fetch_word Plain.M.loaded_segments (0x7a2c0 : word) = Some W_7a268.
Proof. vm_refl. Qed.
Lemma D_7a268 : decode_any W_7a268 = Some (Jal 0 740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4c4 : bv 32 := 0x01330333.
Lemma F_7a4c4 : fetch_word Plain.M.loaded_segments (0x7a51c : word) = Some W_7a4c4.
Proof. vm_refl. Qed.
Lemma D_7a4c4 : decode_any W_7a4c4 = Some (Op ALU_ADD 6 6 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4c8 : bv 32 := 0x01f37393.
Lemma F_7a4c8 : fetch_word Plain.M.loaded_segments (0x7a520 : word) = Some W_7a4c8.
Proof. vm_refl. Qed.
Lemma D_7a4c8 : decode_any W_7a4c8 = Some (OpImm ALU_AND 7 6 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4cc : bv 32 := 0x020fb993.
Lemma F_7a4cc : fetch_word Plain.M.loaded_segments (0x7a524 : word) = Some W_7a4cc.
Proof. vm_refl. Qed.
Lemma D_7a4cc : decode_any W_7a4cc = Some (OpImm ALU_SLTU 19 31 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4d0 : bv 32 := 0x06038663.
Lemma F_7a4d0 : fetch_word Plain.M.loaded_segments (0x7a528 : word) = Some W_7a4d0.
Proof. vm_refl. Qed.
Lemma D_7a4d0 : decode_any W_7a4d0 = Some (Branch BC_EQ 7 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4d4 : bv 32 := 0x00013023.
Lemma F_7a4d4 : fetch_word Plain.M.loaded_segments (0x7a52c : word) = Some W_7a4d4.
Proof. vm_refl. Qed.
Lemma D_7a4d4 : decode_any W_7a4d4 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4d8 : bv 32 := 0x00239313.
Lemma F_7a4d8 : fetch_word Plain.M.loaded_segments (0x7a530 : word) = Some W_7a4d8.
Proof. vm_refl. Qed.
Lemma D_7a4d8 : decode_any W_7a4d8 = Some (ShiftImm ALU_SLL 6 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4dc : bv 32 := 0xfffa5f97.
Lemma F_7a4dc : fetch_word Plain.M.loaded_segments (0x7a534 : word) = Some W_7a4dc.
Proof. vm_refl. Qed.
Lemma D_7a4dc : decode_any W_7a4dc = Some (Auipc 31 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4e0 : bv 32 := 0xef0f8f93.
Lemma F_7a4e0 : fetch_word Plain.M.loaded_segments (0x7a538 : word) = Some W_7a4e0.
Proof. vm_refl. Qed.
Lemma D_7a4e0 : decode_any W_7a4e0 = Some (OpImm ALU_ADD 31 31 3824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4e4 : bv 32 := 0x006f8333.
Lemma F_7a4e4 : fetch_word Plain.M.loaded_segments (0x7a53c : word) = Some W_7a4e4.
Proof. vm_refl. Qed.
Lemma D_7a4e4 : decode_any W_7a4e4 = Some (Op ALU_ADD 6 31 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4e8 : bv 32 := 0x02ed8fb3.
Lemma F_7a4e8 : fetch_word Plain.M.loaded_segments (0x7a540 : word) = Some W_7a4e8.
Proof. vm_refl. Qed.
Lemma D_7a4e8 : decode_any W_7a4e8 = Some (Mul M_MUL 31 27 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4ec : bv 32 := 0x005f5f1b.
Lemma F_7a4ec : fetch_word Plain.M.loaded_segments (0x7a544 : word) = Some W_7a4ec.
Proof. vm_refl. Qed.
Lemma D_7a4ec : decode_any W_7a4ec = Some (ShiftImm32 ALU_SRL 30 30 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f0 : bv 32 := 0x002f9f93.
Lemma F_7a4f0 : fetch_word Plain.M.loaded_segments (0x7a548 : word) = Some W_7a4f0.
Proof. vm_refl. Qed.
Lemma D_7a4f0 : decode_any W_7a4f0 = Some (ShiftImm ALU_SLL 31 31 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f4 : bv 32 := 0x01f282b3.
Lemma F_7a4f4 : fetch_word Plain.M.loaded_segments (0x7a54c : word) = Some W_7a4f4.
Proof. vm_refl. Qed.
Lemma D_7a4f4 : decode_any W_7a4f4 = Some (Op ALU_ADD 5 5 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f8 : bv 32 := 0x002e1f93.
Lemma F_7a4f8 : fetch_word Plain.M.loaded_segments (0x7a550 : word) = Some W_7a4f8.
Proof. vm_refl. Qed.
Lemma D_7a4f8 : decode_any W_7a4f8 = Some (ShiftImm ALU_SLL 31 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4fc : bv 32 := 0x02db8bb3.
Lemma F_7a4fc : fetch_word Plain.M.loaded_segments (0x7a554 : word) = Some W_7a4fc.
Proof. vm_refl. Qed.
Lemma D_7a4fc : decode_any W_7a4fc = Some (Mul M_MUL 23 23 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a500 : bv 32 := 0x005d5d1b.
Lemma F_7a500 : fetch_word Plain.M.loaded_segments (0x7a558 : word) = Some W_7a500.
Proof. vm_refl. Qed.
Lemma D_7a500 : decode_any W_7a500 = Some (ShiftImm32 ALU_SRL 26 26 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a504 : bv 32 := 0x002f1f13.
Lemma F_7a504 : fetch_word Plain.M.loaded_segments (0x7a55c : word) = Some W_7a504.
Proof. vm_refl. Qed.
Lemma D_7a504 : decode_any W_7a504 = Some (ShiftImm ALU_SLL 30 30 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a508 : bv 32 := 0x002b9b93.
Lemma F_7a508 : fetch_word Plain.M.loaded_segments (0x7a560 : word) = Some W_7a508.
Proof. vm_refl. Qed.
Lemma D_7a508 : decode_any W_7a508 = Some (ShiftImm ALU_SLL 23 23 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a50c : bv 32 := 0x002d1d13.
Lemma F_7a50c : fetch_word Plain.M.loaded_segments (0x7a564 : word) = Some W_7a50c.
Proof. vm_refl. Qed.
Lemma D_7a50c : decode_any W_7a50c = Some (ShiftImm ALU_SLL 26 26 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a510 : bv 32 := 0x017b0b33.
Lemma F_7a510 : fetch_word Plain.M.loaded_segments (0x7a568 : word) = Some W_7a510.
Proof. vm_refl. Qed.
Lemma D_7a510 : decode_any W_7a510 = Some (Op ALU_ADD 22 22 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a514 : bv 32 := 0x00032303.
Lemma F_7a514 : fetch_word Plain.M.loaded_segments (0x7a56c : word) = Some W_7a514.
Proof. vm_refl. Qed.
Lemma D_7a514 : decode_any W_7a514 = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a518 : bv 32 := 0x01e282b3.
Lemma F_7a518 : fetch_word Plain.M.loaded_segments (0x7a570 : word) = Some W_7a518.
Proof. vm_refl. Qed.
Lemma D_7a518 : decode_any W_7a518 = Some (Op ALU_ADD 5 5 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a51c : bv 32 := 0x01ab0b33.
Lemma F_7a51c : fetch_word Plain.M.loaded_segments (0x7a574 : word) = Some W_7a51c.
Proof. vm_refl. Qed.
Lemma D_7a51c : decode_any W_7a51c = Some (Op ALU_ADD 22 22 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a520 : bv 32 := 0x01f282b3.
Lemma F_7a520 : fetch_word Plain.M.loaded_segments (0x7a578 : word) = Some W_7a520.
Proof. vm_refl. Qed.
Lemma D_7a520 : decode_any W_7a520 = Some (Op ALU_ADD 5 5 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a524 : bv 32 := 0x01fb0d33.
Lemma F_7a524 : fetch_word Plain.M.loaded_segments (0x7a57c : word) = Some W_7a524.
Proof. vm_refl. Qed.
Lemma D_7a524 : decode_any W_7a524 = Some (Op ALU_ADD 26 22 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a528 : bv 32 := 0x007823b3.
Lemma F_7a528 : fetch_word Plain.M.loaded_segments (0x7a580 : word) = Some W_7a528.
Proof. vm_refl. Qed.
Lemma D_7a528 : decode_any W_7a528 = Some (Op ALU_SLT 7 16 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a52c : bv 32 := 0x0013cf13.
Lemma F_7a52c : fetch_word Plain.M.loaded_segments (0x7a584 : word) = Some W_7a52c.
Proof. vm_refl. Qed.
Lemma D_7a52c : decode_any W_7a52c = Some (OpImm ALU_XOR 30 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a530 : bv 32 := 0x00d00393.
Lemma F_7a530 : fetch_word Plain.M.loaded_segments (0x7a588 : word) = Some W_7a530.
Proof. vm_refl. Qed.
Lemma D_7a530 : decode_any W_7a530 = Some (OpImm ALU_ADD 7 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a534 : bv 32 := 0x0353f063.
Lemma F_7a534 : fetch_word Plain.M.loaded_segments (0x7a58c : word) = Some W_7a534.
Proof. vm_refl. Qed.
Lemma D_7a534 : decode_any W_7a534 = Some (Branch BC_GEU 7 21 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a53c : bv 32 := 0x00000293.
Lemma F_7a53c : fetch_word Plain.M.loaded_segments (0x7a594 : word) = Some W_7a53c.
Proof. vm_refl. Qed.
Lemma D_7a53c : decode_any W_7a53c = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a540 : bv 32 := 0x00000d13.
Lemma F_7a540 : fetch_word Plain.M.loaded_segments (0x7a598 : word) = Some W_7a540.
Proof. vm_refl. Qed.
Lemma D_7a540 : decode_any W_7a540 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a544 : bv 32 := 0x00100313.
Lemma F_7a544 : fetch_word Plain.M.loaded_segments (0x7a59c : word) = Some W_7a544.
Proof. vm_refl. Qed.
Lemma D_7a544 : decode_any W_7a544 = Some (OpImm ALU_ADD 6 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a548 : bv 32 := 0x00613023.
Lemma F_7a548 : fetch_word Plain.M.loaded_segments (0x7a5a0 : word) = Some W_7a548.
Proof. vm_refl. Qed.
Lemma D_7a548 : decode_any W_7a548 = Some (Store SZ8 2 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a54c : bv 32 := 0x00d00393.
Lemma F_7a54c : fetch_word Plain.M.loaded_segments (0x7a5a4 : word) = Some W_7a54c.
Proof. vm_refl. Qed.
Lemma D_7a54c : decode_any W_7a54c = Some (OpImm ALU_ADD 7 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a550 : bv 32 := 0x1953ea63.
Lemma F_7a550 : fetch_word Plain.M.loaded_segments (0x7a5a8 : word) = Some W_7a550.
Proof. vm_refl. Qed.
Lemma D_7a550 : decode_any W_7a550 = Some (Branch BC_LTU 7 21 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a554 : bv 32 := 0x002a9a93.
Lemma F_7a554 : fetch_word Plain.M.loaded_segments (0x7a5ac : word) = Some W_7a554.
Proof. vm_refl. Qed.
Lemma D_7a554 : decode_any W_7a554 = Some (ShiftImm ALU_SLL 21 21 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a558 : bv 32 := 0xfffa5397.
Lemma F_7a558 : fetch_word Plain.M.loaded_segments (0x7a5b0 : word) = Some W_7a558.
Proof. vm_refl. Qed.
Lemma D_7a558 : decode_any W_7a558 = Some (Auipc 7 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a55c : bv 32 := 0xd4838393.
Lemma F_7a55c : fetch_word Plain.M.loaded_segments (0x7a5b4 : word) = Some W_7a55c.
Proof. vm_refl. Qed.
Lemma D_7a55c : decode_any W_7a55c = Some (OpImm ALU_ADD 7 7 3400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a560 : bv 32 := 0x007a8ab3.
Lemma F_7a560 : fetch_word Plain.M.loaded_segments (0x7a5b8 : word) = Some W_7a560.
Proof. vm_refl. Qed.
Lemma D_7a560 : decode_any W_7a560 = Some (Op ALU_ADD 21 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a564 : bv 32 := 0x000aaf83.
Lemma F_7a564 : fetch_word Plain.M.loaded_segments (0x7a5bc : word) = Some W_7a564.
Proof. vm_refl. Qed.
Lemma D_7a564 : decode_any W_7a564 = Some (Load SZ4 true 31 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a568 : bv 32 := 0x007f83b3.
Lemma F_7a568 : fetch_word Plain.M.loaded_segments (0x7a5c0 : word) = Some W_7a568.
Proof. vm_refl. Qed.
Lemma D_7a568 : decode_any W_7a568 = Some (Op ALU_ADD 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a56c : bv 32 := 0x00038067.
Lemma F_7a56c : fetch_word Plain.M.loaded_segments (0x7a5c4 : word) = Some W_7a56c.
Proof. vm_refl. Qed.
Lemma D_7a56c : decode_any W_7a56c = Some (Jalr 0 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b368 : bv 32 := 0xfff8c513.
Lemma F_7b368 : fetch_word Plain.M.loaded_segments (0x7b3c0 : word) = Some W_7b368.
Proof. vm_refl. Qed.
Lemma D_7b368 : decode_any W_7b368 = Some (OpImm ALU_XOR 10 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b36c : bv 32 := 0x00271713.
Lemma F_7b36c : fetch_word Plain.M.loaded_segments (0x7b3c4 : word) = Some W_7b36c.
Proof. vm_refl. Qed.
Lemma D_7b36c : decode_any W_7b36c = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b370 : bv 32 := 0x00269693.
Lemma F_7b370 : fetch_word Plain.M.loaded_segments (0x7b3c8 : word) = Some W_7b370.
Proof. vm_refl. Qed.
Lemma D_7b370 : decode_any W_7b370 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b374 : bv 32 := 0x0e0a0a63.
Lemma F_7b374 : fetch_word Plain.M.loaded_segments (0x7b3cc : word) = Some W_7b374.
Proof. vm_refl. Qed.
Lemma D_7b374 : decode_any W_7b374 = Some (Branch BC_EQ 20 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b378 : bv 32 := 0xfff94593.
Lemma F_7b378 : fetch_word Plain.M.loaded_segments (0x7b3d0 : word) = Some W_7b378.
Proof. vm_refl. Qed.
Lemma D_7b378 : decode_any W_7b378 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b37c : bv 32 := 0x00408093.
Lemma F_7b37c : fetch_word Plain.M.loaded_segments (0x7b3d4 : word) = Some W_7b37c.
Proof. vm_refl. Qed.
Lemma D_7b37c : decode_any W_7b37c = Some (OpImm ALU_ADD 1 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b380 : bv 32 := 0x001cfa13.
Lemma F_7b380 : fetch_word Plain.M.loaded_segments (0x7b3d8 : word) = Some W_7b380.
Proof. vm_refl. Qed.
Lemma D_7b380 : decode_any W_7b380 = Some (OpImm ALU_AND 20 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b384 : bv 32 := 0x001c7a93.
Lemma F_7b384 : fetch_word Plain.M.loaded_segments (0x7b3dc : word) = Some W_7b384.
Proof. vm_refl. Qed.
Lemma D_7b384 : decode_any W_7b384 = Some (OpImm ALU_AND 21 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b388 : bv 32 := 0x00060b13.
Lemma F_7b388 : fetch_word Plain.M.loaded_segments (0x7b3e0 : word) = Some W_7b388.
Proof. vm_refl. Qed.
Lemma D_7b388 : decode_any W_7b388 = Some (OpImm ALU_ADD 22 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b38c : bv 32 := 0x0300006f.
Lemma F_7b38c : fetch_word Plain.M.loaded_segments (0x7b3e4 : word) = Some W_7b38c.
Proof. vm_refl. Qed.
Lemma D_7b38c : decode_any W_7b38c = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b390 : bv 32 := 0x0103d3bb.
Lemma F_7b390 : fetch_word Plain.M.loaded_segments (0x7b3e8 : word) = Some W_7b390.
Proof. vm_refl. Qed.
Lemma D_7b390 : decode_any W_7b390 = Some (Op32 ALU_SRL 7 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b394 : bv 32 := 0x00042f83.
Lemma F_7b394 : fetch_word Plain.M.loaded_segments (0x7b3ec : word) = Some W_7b394.
Proof. vm_refl. Qed.
Lemma D_7b394 : decode_any W_7b394 = Some (Load SZ4 true 31 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b398 : bv 32 := 0xfffb0b1b.
Lemma F_7b398 : fetch_word Plain.M.loaded_segments (0x7b3f0 : word) = Some W_7b398.
Proof. vm_refl. Qed.
Lemma D_7b398 : decode_any W_7b398 = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b39c : bv 32 := 0x00d080b3.
Lemma F_7b39c : fetch_word Plain.M.loaded_segments (0x7b3f4 : word) = Some W_7b39c.
Proof. vm_refl. Qed.
Lemma D_7b39c : decode_any W_7b39c = Some (Op ALU_ADD 1 1 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3a0 : bv 32 := 0x00bffbb3.
Lemma F_7b3a0 : fetch_word Plain.M.loaded_segments (0x7b3f8 : word) = Some W_7b3a0.
Proof. vm_refl. Qed.
Lemma D_7b3a0 : decode_any W_7b3a0 = Some (Op ALU_AND 23 31 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3a4 : bv 32 := 0x007fe3b3.
Lemma F_7b3a4 : fetch_word Plain.M.loaded_segments (0x7b3fc : word) = Some W_7b3a4.
Proof. vm_refl. Qed.
Lemma D_7b3a4 : decode_any W_7b3a4 = Some (Op ALU_OR 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3a8 : bv 32 := 0x0123f3b3.
Lemma F_7b3a8 : fetch_word Plain.M.loaded_segments (0x7b400 : word) = Some W_7b3a8.
Proof. vm_refl. Qed.
Lemma D_7b3a8 : decode_any W_7b3a8 = Some (Op ALU_AND 7 7 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3ac : bv 32 := 0x0173e3b3.
Lemma F_7b3ac : fetch_word Plain.M.loaded_segments (0x7b404 : word) = Some W_7b3ac.
Proof. vm_refl. Qed.
Lemma D_7b3ac : decode_any W_7b3ac = Some (Op ALU_OR 7 7 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3b0 : bv 32 := 0x00742023.
Lemma F_7b3b0 : fetch_word Plain.M.loaded_segments (0x7b408 : word) = Some W_7b3b0.
Proof. vm_refl. Qed.
Lemma D_7b3b0 : decode_any W_7b3b0 = Some (Store SZ4 8 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3b4 : bv 32 := 0x00e40433.
Lemma F_7b3b4 : fetch_word Plain.M.loaded_segments (0x7b40c : word) = Some W_7b3b4.
Proof. vm_refl. Qed.
Lemma D_7b3b4 : decode_any W_7b3b4 = Some (Op ALU_ADD 8 8 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3b8 : bv 32 := 0x0a0b0863.
Lemma F_7b3b8 : fetch_word Plain.M.loaded_segments (0x7b410 : word) = Some W_7b3b8.
Proof. vm_refl. Qed.
Lemma D_7b3b8 : decode_any W_7b3b8 = Some (Branch BC_EQ 22 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3bc : bv 32 := 0xffc0a383.
Lemma F_7b3bc : fetch_word Plain.M.loaded_segments (0x7b414 : word) = Some W_7b3bc.
Proof. vm_refl. Qed.
Lemma D_7b3bc : decode_any W_7b3bc = Some (Load SZ4 true 7 1 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3c0 : bv 32 := 0xfc0a08e3.
Lemma F_7b3c0 : fetch_word Plain.M.loaded_segments (0x7b418 : word) = Some W_7b3c0.
Proof. vm_refl. Qed.
Lemma D_7b3c0 : decode_any W_7b3c0 = Some (Branch BC_EQ 20 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3c4 : bv 32 := 0x00f393bb.
Lemma F_7b3c4 : fetch_word Plain.M.loaded_segments (0x7b41c : word) = Some W_7b3c4.
Proof. vm_refl. Qed.
Lemma D_7b3c4 : decode_any W_7b3c4 = Some (Op32 ALU_SLL 7 7 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3c8 : bv 32 := 0xfc0a96e3.
Lemma F_7b3c8 : fetch_word Plain.M.loaded_segments (0x7b420 : word) = Some W_7b3c8.
Proof. vm_refl. Qed.
Lemma D_7b3c8 : decode_any W_7b3c8 = Some (Branch BC_NE 21 0 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3cc : bv 32 := 0x0000af83.
Lemma F_7b3cc : fetch_word Plain.M.loaded_segments (0x7b424 : word) = Some W_7b3cc.
Proof. vm_refl. Qed.
Lemma D_7b3cc : decode_any W_7b3cc = Some (Load SZ4 true 31 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3d0 : bv 32 := 0x00a3f3b3.
Lemma F_7b3d0 : fetch_word Plain.M.loaded_segments (0x7b428 : word) = Some W_7b3d0.
Proof. vm_refl. Qed.
Lemma D_7b3d0 : decode_any W_7b3d0 = Some (Op ALU_AND 7 7 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3d4 : bv 32 := 0x010fdfbb.
Lemma F_7b3d4 : fetch_word Plain.M.loaded_segments (0x7b42c : word) = Some W_7b3d4.
Proof. vm_refl. Qed.
Lemma D_7b3d4 : decode_any W_7b3d4 = Some (Op32 ALU_SRL 31 31 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3d8 : bv 32 := 0x011fffb3.
Lemma F_7b3d8 : fetch_word Plain.M.loaded_segments (0x7b430 : word) = Some W_7b3d8.
Proof. vm_refl. Qed.
Lemma D_7b3d8 : decode_any W_7b3d8 = Some (Op ALU_AND 31 31 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3dc : bv 32 := 0x007fe3b3.
Lemma F_7b3dc : fetch_word Plain.M.loaded_segments (0x7b434 : word) = Some W_7b3dc.
Proof. vm_refl. Qed.
Lemma D_7b3dc : decode_any W_7b3dc = Some (Op ALU_OR 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b3e0 : bv 32 := 0xfb5ff06f.
Lemma F_7b3e0 : fetch_word Plain.M.loaded_segments (0x7b438 : word) = Some W_7b3e0.
Proof. vm_refl. Qed.
Lemma D_7b3e0 : decode_any W_7b3e0 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b468 : bv 32 := 0x600982e3.
Lemma F_7b468 : fetch_word Plain.M.loaded_segments (0x7b4c0 : word) = Some W_7b468.
Proof. vm_refl. Qed.
Lemma D_7b468 : decode_any W_7b468 = Some (Branch BC_EQ 19 0 3588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b46c : bv 32 := 0x00013583.
Lemma F_7b46c : fetch_word Plain.M.loaded_segments (0x7b4c4 : word) = Some W_7b46c.
Proof. vm_refl. Qed.
Lemma D_7b46c : decode_any W_7b46c = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b470 : bv 32 := 0x280590e3.
Lemma F_7b470 : fetch_word Plain.M.loaded_segments (0x7b4c8 : word) = Some W_7b470.
Proof. vm_refl. Qed.
Lemma D_7b470 : decode_any W_7b470 = Some (Branch BC_NE 11 0 2688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b474 : bv 32 := 0xfff34593.
Lemma F_7b474 : fetch_word Plain.M.loaded_segments (0x7b4cc : word) = Some W_7b474.
Proof. vm_refl. Qed.
Lemma D_7b474 : decode_any W_7b474 = Some (OpImm ALU_XOR 11 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b478 : bv 32 := 0x004d0393.
Lemma F_7b478 : fetch_word Plain.M.loaded_segments (0x7b4d0 : word) = Some W_7b478.
Proof. vm_refl. Qed.
Lemma D_7b478 : decode_any W_7b478 = Some (OpImm ALU_ADD 7 26 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b47c : bv 32 := 0x001f7e13.
Lemma F_7b47c : fetch_word Plain.M.loaded_segments (0x7b4d4 : word) = Some W_7b47c.
Proof. vm_refl. Qed.
Lemma D_7b47c : decode_any W_7b47c = Some (OpImm ALU_AND 28 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b480 : bv 32 := 0x02c0006f.
Lemma F_7b480 : fetch_word Plain.M.loaded_segments (0x7b4d8 : word) = Some W_7b480.
Proof. vm_refl. Qed.
Lemma D_7b480 : decode_any W_7b480 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b484 : bv 32 := 0x0002af03.
Lemma F_7b484 : fetch_word Plain.M.loaded_segments (0x7b4dc : word) = Some W_7b484.
Proof. vm_refl. Qed.
Lemma D_7b484 : decode_any W_7b484 = Some (Load SZ4 true 30 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b488 : bv 32 := 0xfff6061b.
Lemma F_7b488 : fetch_word Plain.M.loaded_segments (0x7b4e0 : word) = Some W_7b488.
Proof. vm_refl. Qed.
Lemma D_7b488 : decode_any W_7b488 = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b48c : bv 32 := 0x00d383b3.
Lemma F_7b48c : fetch_word Plain.M.loaded_segments (0x7b4e4 : word) = Some W_7b48c.
Proof. vm_refl. Qed.
Lemma D_7b48c : decode_any W_7b48c = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b490 : bv 32 := 0x00bf7fb3.
Lemma F_7b490 : fetch_word Plain.M.loaded_segments (0x7b4e8 : word) = Some W_7b490.
Proof. vm_refl. Qed.
Lemma D_7b490 : decode_any W_7b490 = Some (Op ALU_AND 31 30 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b494 : bv 32 := 0x01df6eb3.
Lemma F_7b494 : fetch_word Plain.M.loaded_segments (0x7b4ec : word) = Some W_7b494.
Proof. vm_refl. Qed.
Lemma D_7b494 : decode_any W_7b494 = Some (Op ALU_OR 29 30 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b498 : bv 32 := 0x006efeb3.
Lemma F_7b498 : fetch_word Plain.M.loaded_segments (0x7b4f0 : word) = Some W_7b498.
Proof. vm_refl. Qed.
Lemma D_7b498 : decode_any W_7b498 = Some (Op ALU_AND 29 29 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b49c : bv 32 := 0x01feeeb3.
Lemma F_7b49c : fetch_word Plain.M.loaded_segments (0x7b4f4 : word) = Some W_7b49c.
Proof. vm_refl. Qed.
Lemma D_7b49c : decode_any W_7b49c = Some (Op ALU_OR 29 29 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4a0 : bv 32 := 0x01d2a023.
Lemma F_7b4a0 : fetch_word Plain.M.loaded_segments (0x7b4f8 : word) = Some W_7b4a0.
Proof. vm_refl. Qed.
Lemma D_7b4a0 : decode_any W_7b4a0 = Some (Store SZ4 5 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4a4 : bv 32 := 0x00e282b3.
Lemma F_7b4a4 : fetch_word Plain.M.loaded_segments (0x7b4fc : word) = Some W_7b4a4.
Proof. vm_refl. Qed.
Lemma D_7b4a4 : decode_any W_7b4a4 = Some (Op ALU_ADD 5 5 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4a8 : bv 32 := 0x240604e3.
Lemma F_7b4a8 : fetch_word Plain.M.loaded_segments (0x7b500 : word) = Some W_7b4a8.
Proof. vm_refl. Qed.
Lemma D_7b4a8 : decode_any W_7b4a8 = Some (Branch BC_EQ 12 0 2632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4ac : bv 32 := 0xffc3ae83.
Lemma F_7b4ac : fetch_word Plain.M.loaded_segments (0x7b504 : word) = Some W_7b4ac.
Proof. vm_refl. Qed.
Lemma D_7b4ac : decode_any W_7b4ac = Some (Load SZ4 true 29 7 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4b0 : bv 32 := 0x00fe9ebb.
Lemma F_7b4b0 : fetch_word Plain.M.loaded_segments (0x7b508 : word) = Some W_7b4b0.
Proof. vm_refl. Qed.
Lemma D_7b4b0 : decode_any W_7b4b0 = Some (Op32 ALU_SLL 29 29 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4b4 : bv 32 := 0xfc0e18e3.
Lemma F_7b4b4 : fetch_word Plain.M.loaded_segments (0x7b50c : word) = Some W_7b4b4.
Proof. vm_refl. Qed.
Lemma D_7b4b4 : decode_any W_7b4b4 = Some (Branch BC_NE 28 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4b8 : bv 32 := 0x0003af03.
Lemma F_7b4b8 : fetch_word Plain.M.loaded_segments (0x7b510 : word) = Some W_7b4b8.
Proof. vm_refl. Qed.
Lemma D_7b4b8 : decode_any W_7b4b8 = Some (Load SZ4 true 30 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4bc : bv 32 := 0x00aefeb3.
Lemma F_7b4bc : fetch_word Plain.M.loaded_segments (0x7b514 : word) = Some W_7b4bc.
Proof. vm_refl. Qed.
Lemma D_7b4bc : decode_any W_7b4bc = Some (Op ALU_AND 29 29 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4c0 : bv 32 := 0x010f5f3b.
Lemma F_7b4c0 : fetch_word Plain.M.loaded_segments (0x7b518 : word) = Some W_7b4c0.
Proof. vm_refl. Qed.
Lemma D_7b4c0 : decode_any W_7b4c0 = Some (Op32 ALU_SRL 30 30 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4c4 : bv 32 := 0x011f7f33.
Lemma F_7b4c4 : fetch_word Plain.M.loaded_segments (0x7b51c : word) = Some W_7b4c4.
Proof. vm_refl. Qed.
Lemma D_7b4c4 : decode_any W_7b4c4 = Some (Op ALU_AND 30 30 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4c8 : bv 32 := 0x01df6eb3.
Lemma F_7b4c8 : fetch_word Plain.M.loaded_segments (0x7b520 : word) = Some W_7b4c8.
Proof. vm_refl. Qed.
Lemma D_7b4c8 : decode_any W_7b4c8 = Some (Op ALU_OR 29 30 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4cc : bv 32 := 0xfb9ff06f.
Lemma F_7b4cc : fetch_word Plain.M.loaded_segments (0x7b524 : word) = Some W_7b4cc.
Proof. vm_refl. Qed.
Lemma D_7b4cc : decode_any W_7b4cc = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c26c : bv 32 := 0x00000593.
Lemma F_7c26c : fetch_word Plain.M.loaded_segments (0x7c2c4 : word) = Some W_7c26c.
Proof. vm_refl. Qed.
Lemma D_7c26c : decode_any W_7c26c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c270 : bv 32 := 0x00000413.
Lemma F_7c270 : fetch_word Plain.M.loaded_segments (0x7c2c8 : word) = Some W_7c270.
Proof. vm_refl. Qed.
Lemma D_7c270 : decode_any W_7c270 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c274 : bv 32 := 0x00448493.
Lemma F_7c274 : fetch_word Plain.M.loaded_segments (0x7c2cc : word) = Some W_7c274.
Proof. vm_refl. Qed.
Lemma D_7c274 : decode_any W_7c274 = Some (OpImm ALU_ADD 9 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c278 : bv 32 := 0x002e1913.
Lemma F_7c278 : fetch_word Plain.M.loaded_segments (0x7c2d0 : word) = Some W_7c278.
Proof. vm_refl. Qed.
Lemma D_7c278 : decode_any W_7c278 = Some (ShiftImm ALU_SLL 18 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c27c : bv 32 := 0x000e8993.
Lemma F_7c27c : fetch_word Plain.M.loaded_segments (0x7c2d4 : word) = Some W_7c27c.
Proof. vm_refl. Qed.
Lemma D_7c27c : decode_any W_7c27c = Some (OpImm ALU_ADD 19 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c280 : bv 32 := 0x0180006f.
Lemma F_7c280 : fetch_word Plain.M.loaded_segments (0x7c2d8 : word) = Some W_7c280.
Proof. vm_refl. Qed.
Lemma D_7c280 : decode_any W_7c280 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c284 : bv 32 := 0x0014041b.
Lemma F_7c284 : fetch_word Plain.M.loaded_segments (0x7c2dc : word) = Some W_7c284.
Proof. vm_refl. Qed.
Lemma D_7c284 : decode_any W_7c284 = Some (OpImm32 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c288 : bv 32 := 0x00e989b3.
Lemma F_7c288 : fetch_word Plain.M.loaded_segments (0x7c2e0 : word) = Some W_7c288.
Proof. vm_refl. Qed.
Lemma D_7c288 : decode_any W_7c288 = Some (Op ALU_ADD 19 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c28c : bv 32 := 0x00d484b3.
Lemma F_7c28c : fetch_word Plain.M.loaded_segments (0x7c2e4 : word) = Some W_7c28c.
Proof. vm_refl. Qed.
Lemma D_7c28c : decode_any W_7c28c = Some (Op ALU_ADD 9 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c290 : bv 32 := 0x00158593.
Lemma F_7c290 : fetch_word Plain.M.loaded_segments (0x7c2e8 : word) = Some W_7c290.
Proof. vm_refl. Qed.
Lemma D_7c290 : decode_any W_7c290 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c294 : bv 32 := 0x9cc40c63.
Lemma F_7c294 : fetch_word Plain.M.loaded_segments (0x7c2ec : word) = Some W_7c294.
Proof. vm_refl. Qed.
Lemma D_7c294 : decode_any W_7c294 = Some (Branch BC_EQ 8 12 4568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c298 : bv 32 := 0xfe0e06e3.
Lemma F_7c298 : fetch_word Plain.M.loaded_segments (0x7c2f0 : word) = Some W_7c298.
Proof. vm_refl. Qed.
Lemma D_7c298 : decode_any W_7c298 = Some (Branch BC_EQ 28 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c29c : bv 32 := 0x02b703b3.
Lemma F_7c29c : fetch_word Plain.M.loaded_segments (0x7c2f4 : word) = Some W_7c29c.
Proof. vm_refl. Qed.
Lemma D_7c29c : decode_any W_7c29c = Some (Mul M_MUL 7 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2a0 : bv 32 := 0x007903b3.
Lemma F_7c2a0 : fetch_word Plain.M.loaded_segments (0x7c2f8 : word) = Some W_7c2a0.
Proof. vm_refl. Qed.
Lemma D_7c2a0 : decode_any W_7c2a0 = Some (Op ALU_ADD 7 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2a4 : bv 32 := 0x007e83b3.
Lemma F_7c2a4 : fetch_word Plain.M.loaded_segments (0x7c2fc : word) = Some W_7c2a4.
Proof. vm_refl. Qed.
Lemma D_7c2a4 : decode_any W_7c2a4 = Some (Op ALU_ADD 7 29 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2a8 : bv 32 := 0x00048a13.
Lemma F_7c2a8 : fetch_word Plain.M.loaded_segments (0x7c300 : word) = Some W_7c2a8.
Proof. vm_refl. Qed.
Lemma D_7c2a8 : decode_any W_7c2a8 = Some (OpImm ALU_ADD 20 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2ac : bv 32 := 0x00098a93.
Lemma F_7c2ac : fetch_word Plain.M.loaded_segments (0x7c304 : word) = Some W_7c2ac.
Proof. vm_refl. Qed.
Lemma D_7c2ac : decode_any W_7c2ac = Some (OpImm ALU_ADD 21 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2b0 : bv 32 := 0xffca2f83.
Lemma F_7c2b0 : fetch_word Plain.M.loaded_segments (0x7c308 : word) = Some W_7c2b0.
Proof. vm_refl. Qed.
Lemma D_7c2b0 : decode_any W_7c2b0 = Some (Load SZ4 true 31 20 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2b4 : bv 32 := 0x000a2b03.
Lemma F_7c2b4 : fetch_word Plain.M.loaded_segments (0x7c30c : word) = Some W_7c2b4.
Proof. vm_refl. Qed.
Lemma D_7c2b4 : decode_any W_7c2b4 = Some (Load SZ4 true 22 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2b8 : bv 32 := 0x000aab83.
Lemma F_7c2b8 : fetch_word Plain.M.loaded_segments (0x7c310 : word) = Some W_7c2b8.
Proof. vm_refl. Qed.
Lemma D_7c2b8 : decode_any W_7c2b8 = Some (Load SZ4 true 23 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2bc : bv 32 := 0x00ff9fbb.
Lemma F_7c2bc : fetch_word Plain.M.loaded_segments (0x7c314 : word) = Some W_7c2bc.
Proof. vm_refl. Qed.
Lemma D_7c2bc : decode_any W_7c2bc = Some (Op32 ALU_SLL 31 31 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2c0 : bv 32 := 0x010b5b3b.
Lemma F_7c2c0 : fetch_word Plain.M.loaded_segments (0x7c318 : word) = Some W_7c2c0.
Proof. vm_refl. Qed.
Lemma D_7c2c0 : decode_any W_7c2c0 = Some (Op32 ALU_SRL 22 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2c4 : bv 32 := 0x00afffb3.
Lemma F_7c2c4 : fetch_word Plain.M.loaded_segments (0x7c31c : word) = Some W_7c2c4.
Proof. vm_refl. Qed.
Lemma D_7c2c4 : decode_any W_7c2c4 = Some (Op ALU_AND 31 31 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2c8 : bv 32 := 0x011b7b33.
Lemma F_7c2c8 : fetch_word Plain.M.loaded_segments (0x7c320 : word) = Some W_7c2c8.
Proof. vm_refl. Qed.
Lemma D_7c2c8 : decode_any W_7c2c8 = Some (Op ALU_AND 22 22 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2cc : bv 32 := 0x01fbefb3.
Lemma F_7c2cc : fetch_word Plain.M.loaded_segments (0x7c324 : word) = Some W_7c2cc.
Proof. vm_refl. Qed.
Lemma D_7c2cc : decode_any W_7c2cc = Some (Op ALU_OR 31 23 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2d0 : bv 32 := 0x016fefb3.
Lemma F_7c2d0 : fetch_word Plain.M.loaded_segments (0x7c328 : word) = Some W_7c2d0.
Proof. vm_refl. Qed.
Lemma D_7c2d0 : decode_any W_7c2d0 = Some (Op ALU_OR 31 31 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2d4 : bv 32 := 0x01faa023.
Lemma F_7c2d4 : fetch_word Plain.M.loaded_segments (0x7c32c : word) = Some W_7c2d4.
Proof. vm_refl. Qed.
Lemma D_7c2d4 : decode_any W_7c2d4 = Some (Store SZ4 21 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2d8 : bv 32 := 0x004a8a93.
Lemma F_7c2d8 : fetch_word Plain.M.loaded_segments (0x7c330 : word) = Some W_7c2d8.
Proof. vm_refl. Qed.
Lemma D_7c2d8 : decode_any W_7c2d8 = Some (OpImm ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2dc : bv 32 := 0x004a0a13.
Lemma F_7c2dc : fetch_word Plain.M.loaded_segments (0x7c334 : word) = Some W_7c2dc.
Proof. vm_refl. Qed.
Lemma D_7c2dc : decode_any W_7c2dc = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2e0 : bv 32 := 0xfc7a98e3.
Lemma F_7c2e0 : fetch_word Plain.M.loaded_segments (0x7c338 : word) = Some W_7c2e0.
Proof. vm_refl. Qed.
Lemma D_7c2e0 : decode_any W_7c2e0 = Some (Branch BC_NE 21 7 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c2e4 : bv 32 := 0xfa1ff06f.
Lemma F_7c2e4 : fetch_word Plain.M.loaded_segments (0x7c33c : word) = Some W_7c2e4.
Proof. vm_refl. Qed.
Lemma D_7c2e4 : decode_any W_7c2e4 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

