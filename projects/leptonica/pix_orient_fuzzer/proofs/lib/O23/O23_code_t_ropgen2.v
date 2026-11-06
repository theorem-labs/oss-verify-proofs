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
Definition W_7b548 : bv 32 := 0x0e0a0463.
Lemma F_7b548 : fetch_word Plain.M.loaded_segments (0x7b5a0 : word) = Some W_7b548.
Proof. vm_refl. Qed.
Lemma D_7b548 : decode_any W_7b548 = Some (Branch BC_EQ 20 0 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b54c : bv 32 := 0xfff8c513.
Lemma F_7b54c : fetch_word Plain.M.loaded_segments (0x7b5a4 : word) = Some W_7b54c.
Proof. vm_refl. Qed.
Lemma D_7b54c : decode_any W_7b54c = Some (OpImm ALU_XOR 10 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b550 : bv 32 := 0x00408093.
Lemma F_7b550 : fetch_word Plain.M.loaded_segments (0x7b5a8 : word) = Some W_7b550.
Proof. vm_refl. Qed.
Lemma D_7b550 : decode_any W_7b550 = Some (OpImm ALU_ADD 1 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b554 : bv 32 := 0x00269593.
Lemma F_7b554 : fetch_word Plain.M.loaded_segments (0x7b5ac : word) = Some W_7b554.
Proof. vm_refl. Qed.
Lemma D_7b554 : decode_any W_7b554 = Some (ShiftImm ALU_SLL 11 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b558 : bv 32 := 0x00271a13.
Lemma F_7b558 : fetch_word Plain.M.loaded_segments (0x7b5b0 : word) = Some W_7b558.
Proof. vm_refl. Qed.
Lemma D_7b558 : decode_any W_7b558 = Some (ShiftImm ALU_SLL 20 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b55c : bv 32 := 0x001cfa93.
Lemma F_7b55c : fetch_word Plain.M.loaded_segments (0x7b5b4 : word) = Some W_7b55c.
Proof. vm_refl. Qed.
Lemma D_7b55c : decode_any W_7b55c = Some (OpImm ALU_AND 21 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b560 : bv 32 := 0x001c7b13.
Lemma F_7b560 : fetch_word Plain.M.loaded_segments (0x7b5b8 : word) = Some W_7b560.
Proof. vm_refl. Qed.
Lemma D_7b560 : decode_any W_7b560 = Some (OpImm ALU_AND 22 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b564 : bv 32 := 0x00060b93.
Lemma F_7b564 : fetch_word Plain.M.loaded_segments (0x7b5bc : word) = Some W_7b564.
Proof. vm_refl. Qed.
Lemma D_7b564 : decode_any W_7b564 = Some (OpImm ALU_ADD 23 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b568 : bv 32 := 0x02c0006f.
Lemma F_7b568 : fetch_word Plain.M.loaded_segments (0x7b5c0 : word) = Some W_7b568.
Proof. vm_refl. Qed.
Lemma D_7b568 : decode_any W_7b568 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b56c : bv 32 := 0x0103d3bb.
Lemma F_7b56c : fetch_word Plain.M.loaded_segments (0x7b5c4 : word) = Some W_7b56c.
Proof. vm_refl. Qed.
Lemma D_7b56c : decode_any W_7b56c = Some (Op32 ALU_SRL 7 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b570 : bv 32 := 0x00042f83.
Lemma F_7b570 : fetch_word Plain.M.loaded_segments (0x7b5c8 : word) = Some W_7b570.
Proof. vm_refl. Qed.
Lemma D_7b570 : decode_any W_7b570 = Some (Load SZ4 true 31 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b574 : bv 32 := 0x0123f3b3.
Lemma F_7b574 : fetch_word Plain.M.loaded_segments (0x7b5cc : word) = Some W_7b574.
Proof. vm_refl. Qed.
Lemma D_7b574 : decode_any W_7b574 = Some (Op ALU_AND 7 7 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b578 : bv 32 := 0xfffb8b9b.
Lemma F_7b578 : fetch_word Plain.M.loaded_segments (0x7b5d0 : word) = Some W_7b578.
Proof. vm_refl. Qed.
Lemma D_7b578 : decode_any W_7b578 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b57c : bv 32 := 0x00b080b3.
Lemma F_7b57c : fetch_word Plain.M.loaded_segments (0x7b5d4 : word) = Some W_7b57c.
Proof. vm_refl. Qed.
Lemma D_7b57c : decode_any W_7b57c = Some (Op ALU_ADD 1 1 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b580 : bv 32 := 0xfff3c393.
Lemma F_7b580 : fetch_word Plain.M.loaded_segments (0x7b5d8 : word) = Some W_7b580.
Proof. vm_refl. Qed.
Lemma D_7b580 : decode_any W_7b580 = Some (OpImm ALU_XOR 7 7 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b584 : bv 32 := 0x007ff3b3.
Lemma F_7b584 : fetch_word Plain.M.loaded_segments (0x7b5dc : word) = Some W_7b584.
Proof. vm_refl. Qed.
Lemma D_7b584 : decode_any W_7b584 = Some (Op ALU_AND 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b588 : bv 32 := 0x00742023.
Lemma F_7b588 : fetch_word Plain.M.loaded_segments (0x7b5e0 : word) = Some W_7b588.
Proof. vm_refl. Qed.
Lemma D_7b588 : decode_any W_7b588 = Some (Store SZ4 8 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b58c : bv 32 := 0x01440433.
Lemma F_7b58c : fetch_word Plain.M.loaded_segments (0x7b5e4 : word) = Some W_7b58c.
Proof. vm_refl. Qed.
Lemma D_7b58c : decode_any W_7b58c = Some (Op ALU_ADD 8 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b590 : bv 32 := 0x0a0b8063.
Lemma F_7b590 : fetch_word Plain.M.loaded_segments (0x7b5e8 : word) = Some W_7b590.
Proof. vm_refl. Qed.
Lemma D_7b590 : decode_any W_7b590 = Some (Branch BC_EQ 23 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b594 : bv 32 := 0xffc0a383.
Lemma F_7b594 : fetch_word Plain.M.loaded_segments (0x7b5ec : word) = Some W_7b594.
Proof. vm_refl. Qed.
Lemma D_7b594 : decode_any W_7b594 = Some (Load SZ4 true 7 1 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b598 : bv 32 := 0xfc0a8ae3.
Lemma F_7b598 : fetch_word Plain.M.loaded_segments (0x7b5f0 : word) = Some W_7b598.
Proof. vm_refl. Qed.
Lemma D_7b598 : decode_any W_7b598 = Some (Branch BC_EQ 21 0 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b59c : bv 32 := 0x00f393bb.
Lemma F_7b59c : fetch_word Plain.M.loaded_segments (0x7b5f4 : word) = Some W_7b59c.
Proof. vm_refl. Qed.
Lemma D_7b59c : decode_any W_7b59c = Some (Op32 ALU_SLL 7 7 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5a0 : bv 32 := 0xfc0b18e3.
Lemma F_7b5a0 : fetch_word Plain.M.loaded_segments (0x7b5f8 : word) = Some W_7b5a0.
Proof. vm_refl. Qed.
Lemma D_7b5a0 : decode_any W_7b5a0 = Some (Branch BC_NE 22 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5a4 : bv 32 := 0x0000af83.
Lemma F_7b5a4 : fetch_word Plain.M.loaded_segments (0x7b5fc : word) = Some W_7b5a4.
Proof. vm_refl. Qed.
Lemma D_7b5a4 : decode_any W_7b5a4 = Some (Load SZ4 true 31 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5a8 : bv 32 := 0x00a3f3b3.
Lemma F_7b5a8 : fetch_word Plain.M.loaded_segments (0x7b600 : word) = Some W_7b5a8.
Proof. vm_refl. Qed.
Lemma D_7b5a8 : decode_any W_7b5a8 = Some (Op ALU_AND 7 7 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5ac : bv 32 := 0x010fdfbb.
Lemma F_7b5ac : fetch_word Plain.M.loaded_segments (0x7b604 : word) = Some W_7b5ac.
Proof. vm_refl. Qed.
Lemma D_7b5ac : decode_any W_7b5ac = Some (Op32 ALU_SRL 31 31 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5b0 : bv 32 := 0x011fffb3.
Lemma F_7b5b0 : fetch_word Plain.M.loaded_segments (0x7b608 : word) = Some W_7b5b0.
Proof. vm_refl. Qed.
Lemma D_7b5b0 : decode_any W_7b5b0 = Some (Op ALU_AND 31 31 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5b4 : bv 32 := 0x007fe3b3.
Lemma F_7b5b4 : fetch_word Plain.M.loaded_segments (0x7b60c : word) = Some W_7b5b4.
Proof. vm_refl. Qed.
Lemma D_7b5b4 : decode_any W_7b5b4 = Some (Op ALU_OR 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5b8 : bv 32 := 0xfb9ff06f.
Lemma F_7b5b8 : fetch_word Plain.M.loaded_segments (0x7b610 : word) = Some W_7b5b8.
Proof. vm_refl. Qed.
Lemma D_7b5b8 : decode_any W_7b5b8 = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b630 : bv 32 := 0x620980e3.
Lemma F_7b630 : fetch_word Plain.M.loaded_segments (0x7b688 : word) = Some W_7b630.
Proof. vm_refl. Qed.
Lemma D_7b630 : decode_any W_7b630 = Some (Branch BC_EQ 19 0 3616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b634 : bv 32 := 0x00013503.
Lemma F_7b634 : fetch_word Plain.M.loaded_segments (0x7b68c : word) = Some W_7b634.
Proof. vm_refl. Qed.
Lemma D_7b634 : decode_any W_7b634 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b638 : bv 32 := 0x0a051ce3.
Lemma F_7b638 : fetch_word Plain.M.loaded_segments (0x7b690 : word) = Some W_7b638.
Proof. vm_refl. Qed.
Lemma D_7b638 : decode_any W_7b638 = Some (Branch BC_NE 10 0 2232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b63c : bv 32 := 0xfff8c513.
Lemma F_7b63c : fetch_word Plain.M.loaded_segments (0x7b694 : word) = Some W_7b63c.
Proof. vm_refl. Qed.
Lemma D_7b63c : decode_any W_7b63c = Some (OpImm ALU_XOR 10 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b640 : bv 32 := 0x004d0393.
Lemma F_7b640 : fetch_word Plain.M.loaded_segments (0x7b698 : word) = Some W_7b640.
Proof. vm_refl. Qed.
Lemma D_7b640 : decode_any W_7b640 = Some (OpImm ALU_ADD 7 26 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b644 : bv 32 := 0x00269693.
Lemma F_7b644 : fetch_word Plain.M.loaded_segments (0x7b69c : word) = Some W_7b644.
Proof. vm_refl. Qed.
Lemma D_7b644 : decode_any W_7b644 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b648 : bv 32 := 0x00271713.
Lemma F_7b648 : fetch_word Plain.M.loaded_segments (0x7b6a0 : word) = Some W_7b648.
Proof. vm_refl. Qed.
Lemma D_7b648 : decode_any W_7b648 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b64c : bv 32 := 0x001f7593.
Lemma F_7b64c : fetch_word Plain.M.loaded_segments (0x7b6a4 : word) = Some W_7b64c.
Proof. vm_refl. Qed.
Lemma D_7b64c : decode_any W_7b64c = Some (OpImm ALU_AND 11 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b650 : bv 32 := 0x0280006f.
Lemma F_7b650 : fetch_word Plain.M.loaded_segments (0x7b6a8 : word) = Some W_7b650.
Proof. vm_refl. Qed.
Lemma D_7b650 : decode_any W_7b650 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b654 : bv 32 := 0x0002ae83.
Lemma F_7b654 : fetch_word Plain.M.loaded_segments (0x7b6ac : word) = Some W_7b654.
Proof. vm_refl. Qed.
Lemma D_7b654 : decode_any W_7b654 = Some (Load SZ4 true 29 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b658 : bv 32 := 0x006e7e33.
Lemma F_7b658 : fetch_word Plain.M.loaded_segments (0x7b6b0 : word) = Some W_7b658.
Proof. vm_refl. Qed.
Lemma D_7b658 : decode_any W_7b658 = Some (Op ALU_AND 28 28 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b65c : bv 32 := 0xfff6061b.
Lemma F_7b65c : fetch_word Plain.M.loaded_segments (0x7b6b4 : word) = Some W_7b65c.
Proof. vm_refl. Qed.
Lemma D_7b65c : decode_any W_7b65c = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b660 : bv 32 := 0x00d383b3.
Lemma F_7b660 : fetch_word Plain.M.loaded_segments (0x7b6b8 : word) = Some W_7b660.
Proof. vm_refl. Qed.
Lemma D_7b660 : decode_any W_7b660 = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b664 : bv 32 := 0xfffe4e13.
Lemma F_7b664 : fetch_word Plain.M.loaded_segments (0x7b6bc : word) = Some W_7b664.
Proof. vm_refl. Qed.
Lemma D_7b664 : decode_any W_7b664 = Some (OpImm ALU_XOR 28 28 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b668 : bv 32 := 0x01cefe33.
Lemma F_7b668 : fetch_word Plain.M.loaded_segments (0x7b6c0 : word) = Some W_7b668.
Proof. vm_refl. Qed.
Lemma D_7b668 : decode_any W_7b668 = Some (Op ALU_AND 28 29 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b66c : bv 32 := 0x01c2a023.
Lemma F_7b66c : fetch_word Plain.M.loaded_segments (0x7b6c4 : word) = Some W_7b66c.
Proof. vm_refl. Qed.
Lemma D_7b66c : decode_any W_7b66c = Some (Store SZ4 5 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b670 : bv 32 := 0x00e282b3.
Lemma F_7b670 : fetch_word Plain.M.loaded_segments (0x7b6c8 : word) = Some W_7b670.
Proof. vm_refl. Qed.
Lemma D_7b670 : decode_any W_7b670 = Some (Op ALU_ADD 5 5 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b674 : bv 32 := 0x06060ee3.
Lemma F_7b674 : fetch_word Plain.M.loaded_segments (0x7b6cc : word) = Some W_7b674.
Proof. vm_refl. Qed.
Lemma D_7b674 : decode_any W_7b674 = Some (Branch BC_EQ 12 0 2172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b678 : bv 32 := 0xffc3ae03.
Lemma F_7b678 : fetch_word Plain.M.loaded_segments (0x7b6d0 : word) = Some W_7b678.
Proof. vm_refl. Qed.
Lemma D_7b678 : decode_any W_7b678 = Some (Load SZ4 true 28 7 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b67c : bv 32 := 0x00fe1e3b.
Lemma F_7b67c : fetch_word Plain.M.loaded_segments (0x7b6d4 : word) = Some W_7b67c.
Proof. vm_refl. Qed.
Lemma D_7b67c : decode_any W_7b67c = Some (Op32 ALU_SLL 28 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b680 : bv 32 := 0xfc059ae3.
Lemma F_7b680 : fetch_word Plain.M.loaded_segments (0x7b6d8 : word) = Some W_7b680.
Proof. vm_refl. Qed.
Lemma D_7b680 : decode_any W_7b680 = Some (Branch BC_NE 11 0 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b684 : bv 32 := 0x0003ae83.
Lemma F_7b684 : fetch_word Plain.M.loaded_segments (0x7b6dc : word) = Some W_7b684.
Proof. vm_refl. Qed.
Lemma D_7b684 : decode_any W_7b684 = Some (Load SZ4 true 29 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b688 : bv 32 := 0x00ae7e33.
Lemma F_7b688 : fetch_word Plain.M.loaded_segments (0x7b6e0 : word) = Some W_7b688.
Proof. vm_refl. Qed.
Lemma D_7b688 : decode_any W_7b688 = Some (Op ALU_AND 28 28 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b68c : bv 32 := 0x010edebb.
Lemma F_7b68c : fetch_word Plain.M.loaded_segments (0x7b6e4 : word) = Some W_7b68c.
Proof. vm_refl. Qed.
Lemma D_7b68c : decode_any W_7b68c = Some (Op32 ALU_SRL 29 29 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b690 : bv 32 := 0x011efeb3.
Lemma F_7b690 : fetch_word Plain.M.loaded_segments (0x7b6e8 : word) = Some W_7b690.
Proof. vm_refl. Qed.
Lemma D_7b690 : decode_any W_7b690 = Some (Op ALU_AND 29 29 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b694 : bv 32 := 0x01ceee33.
Lemma F_7b694 : fetch_word Plain.M.loaded_segments (0x7b6ec : word) = Some W_7b694.
Proof. vm_refl. Qed.
Lemma D_7b694 : decode_any W_7b694 = Some (Op ALU_OR 28 29 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b698 : bv 32 := 0xfbdff06f.
Lemma F_7b698 : fetch_word Plain.M.loaded_segments (0x7b6f0 : word) = Some W_7b698.
Proof. vm_refl. Qed.
Lemma D_7b698 : decode_any W_7b698 = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c450 : bv 32 := 0x00000513.
Lemma F_7c450 : fetch_word Plain.M.loaded_segments (0x7c4a8 : word) = Some W_7c450.
Proof. vm_refl. Qed.
Lemma D_7c450 : decode_any W_7c450 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c454 : bv 32 := 0x00000593.
Lemma F_7c454 : fetch_word Plain.M.loaded_segments (0x7c4ac : word) = Some W_7c454.
Proof. vm_refl. Qed.
Lemma D_7c454 : decode_any W_7c454 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c458 : bv 32 := 0xfff8c413.
Lemma F_7c458 : fetch_word Plain.M.loaded_segments (0x7c4b0 : word) = Some W_7c458.
Proof. vm_refl. Qed.
Lemma D_7c458 : decode_any W_7c458 = Some (OpImm ALU_XOR 8 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c45c : bv 32 := 0x00271913.
Lemma F_7c45c : fetch_word Plain.M.loaded_segments (0x7c4b4 : word) = Some W_7c45c.
Proof. vm_refl. Qed.
Lemma D_7c45c : decode_any W_7c45c = Some (ShiftImm ALU_SLL 18 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c460 : bv 32 := 0x00448493.
Lemma F_7c460 : fetch_word Plain.M.loaded_segments (0x7c4b8 : word) = Some W_7c460.
Proof. vm_refl. Qed.
Lemma D_7c460 : decode_any W_7c460 = Some (OpImm ALU_ADD 9 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c464 : bv 32 := 0x00269993.
Lemma F_7c464 : fetch_word Plain.M.loaded_segments (0x7c4bc : word) = Some W_7c464.
Proof. vm_refl. Qed.
Lemma D_7c464 : decode_any W_7c464 = Some (ShiftImm ALU_SLL 19 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c468 : bv 32 := 0x002e1a13.
Lemma F_7c468 : fetch_word Plain.M.loaded_segments (0x7c4c0 : word) = Some W_7c468.
Proof. vm_refl. Qed.
Lemma D_7c468 : decode_any W_7c468 = Some (ShiftImm ALU_SLL 20 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c46c : bv 32 := 0x000e8a93.
Lemma F_7c46c : fetch_word Plain.M.loaded_segments (0x7c4c4 : word) = Some W_7c46c.
Proof. vm_refl. Qed.
Lemma D_7c46c : decode_any W_7c46c = Some (OpImm ALU_ADD 21 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c470 : bv 32 := 0x0180006f.
Lemma F_7c470 : fetch_word Plain.M.loaded_segments (0x7c4c8 : word) = Some W_7c470.
Proof. vm_refl. Qed.
Lemma D_7c470 : decode_any W_7c470 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c474 : bv 32 := 0x0015859b.
Lemma F_7c474 : fetch_word Plain.M.loaded_segments (0x7c4cc : word) = Some W_7c474.
Proof. vm_refl. Qed.
Lemma D_7c474 : decode_any W_7c474 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c478 : bv 32 := 0x012a8ab3.
Lemma F_7c478 : fetch_word Plain.M.loaded_segments (0x7c4d0 : word) = Some W_7c478.
Proof. vm_refl. Qed.
Lemma D_7c478 : decode_any W_7c478 = Some (Op ALU_ADD 21 21 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c47c : bv 32 := 0x013484b3.
Lemma F_7c47c : fetch_word Plain.M.loaded_segments (0x7c4d4 : word) = Some W_7c47c.
Proof. vm_refl. Qed.
Lemma D_7c47c : decode_any W_7c47c = Some (Op ALU_ADD 9 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c480 : bv 32 := 0x00150513.
Lemma F_7c480 : fetch_word Plain.M.loaded_segments (0x7c4d8 : word) = Some W_7c480.
Proof. vm_refl. Qed.
Lemma D_7c480 : decode_any W_7c480 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c484 : bv 32 := 0x9ac58863.
Lemma F_7c484 : fetch_word Plain.M.loaded_segments (0x7c4dc : word) = Some W_7c484.
Proof. vm_refl. Qed.
Lemma D_7c484 : decode_any W_7c484 = Some (Branch BC_EQ 11 12 4528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c488 : bv 32 := 0xfe0e06e3.
Lemma F_7c488 : fetch_word Plain.M.loaded_segments (0x7c4e0 : word) = Some W_7c488.
Proof. vm_refl. Qed.
Lemma D_7c488 : decode_any W_7c488 = Some (Branch BC_EQ 28 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c48c : bv 32 := 0x02a903b3.
Lemma F_7c48c : fetch_word Plain.M.loaded_segments (0x7c4e4 : word) = Some W_7c48c.
Proof. vm_refl. Qed.
Lemma D_7c48c : decode_any W_7c48c = Some (Mul M_MUL 7 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c490 : bv 32 := 0x007a03b3.
Lemma F_7c490 : fetch_word Plain.M.loaded_segments (0x7c4e8 : word) = Some W_7c490.
Proof. vm_refl. Qed.
Lemma D_7c490 : decode_any W_7c490 = Some (Op ALU_ADD 7 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c494 : bv 32 := 0x007e83b3.
Lemma F_7c494 : fetch_word Plain.M.loaded_segments (0x7c4ec : word) = Some W_7c494.
Proof. vm_refl. Qed.
Lemma D_7c494 : decode_any W_7c494 = Some (Op ALU_ADD 7 29 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c498 : bv 32 := 0x00048b13.
Lemma F_7c498 : fetch_word Plain.M.loaded_segments (0x7c4f0 : word) = Some W_7c498.
Proof. vm_refl. Qed.
Lemma D_7c498 : decode_any W_7c498 = Some (OpImm ALU_ADD 22 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c49c : bv 32 := 0x000a8b93.
Lemma F_7c49c : fetch_word Plain.M.loaded_segments (0x7c4f4 : word) = Some W_7c49c.
Proof. vm_refl. Qed.
Lemma D_7c49c : decode_any W_7c49c = Some (OpImm ALU_ADD 23 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4a0 : bv 32 := 0xffcb2f83.
Lemma F_7c4a0 : fetch_word Plain.M.loaded_segments (0x7c4f8 : word) = Some W_7c4a0.
Proof. vm_refl. Qed.
Lemma D_7c4a0 : decode_any W_7c4a0 = Some (Load SZ4 true 31 22 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4a4 : bv 32 := 0x000b2c03.
Lemma F_7c4a4 : fetch_word Plain.M.loaded_segments (0x7c4fc : word) = Some W_7c4a4.
Proof. vm_refl. Qed.
Lemma D_7c4a4 : decode_any W_7c4a4 = Some (Load SZ4 true 24 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4a8 : bv 32 := 0x000bac83.
Lemma F_7c4a8 : fetch_word Plain.M.loaded_segments (0x7c500 : word) = Some W_7c4a8.
Proof. vm_refl. Qed.
Lemma D_7c4a8 : decode_any W_7c4a8 = Some (Load SZ4 true 25 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4ac : bv 32 := 0x00ff9fbb.
Lemma F_7c4ac : fetch_word Plain.M.loaded_segments (0x7c504 : word) = Some W_7c4ac.
Proof. vm_refl. Qed.
Lemma D_7c4ac : decode_any W_7c4ac = Some (Op32 ALU_SLL 31 31 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4b0 : bv 32 := 0x010c5c3b.
Lemma F_7c4b0 : fetch_word Plain.M.loaded_segments (0x7c508 : word) = Some W_7c4b0.
Proof. vm_refl. Qed.
Lemma D_7c4b0 : decode_any W_7c4b0 = Some (Op32 ALU_SRL 24 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4b4 : bv 32 := 0x008fffb3.
Lemma F_7c4b4 : fetch_word Plain.M.loaded_segments (0x7c50c : word) = Some W_7c4b4.
Proof. vm_refl. Qed.
Lemma D_7c4b4 : decode_any W_7c4b4 = Some (Op ALU_AND 31 31 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4b8 : bv 32 := 0x011c7c33.
Lemma F_7c4b8 : fetch_word Plain.M.loaded_segments (0x7c510 : word) = Some W_7c4b8.
Proof. vm_refl. Qed.
Lemma D_7c4b8 : decode_any W_7c4b8 = Some (Op ALU_AND 24 24 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4bc : bv 32 := 0x01fc6fb3.
Lemma F_7c4bc : fetch_word Plain.M.loaded_segments (0x7c514 : word) = Some W_7c4bc.
Proof. vm_refl. Qed.
Lemma D_7c4bc : decode_any W_7c4bc = Some (Op ALU_OR 31 24 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4c0 : bv 32 := 0xffffcf93.
Lemma F_7c4c0 : fetch_word Plain.M.loaded_segments (0x7c518 : word) = Some W_7c4c0.
Proof. vm_refl. Qed.
Lemma D_7c4c0 : decode_any W_7c4c0 = Some (OpImm ALU_XOR 31 31 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4c4 : bv 32 := 0x01fcffb3.
Lemma F_7c4c4 : fetch_word Plain.M.loaded_segments (0x7c51c : word) = Some W_7c4c4.
Proof. vm_refl. Qed.
Lemma D_7c4c4 : decode_any W_7c4c4 = Some (Op ALU_AND 31 25 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4c8 : bv 32 := 0x01fba023.
Lemma F_7c4c8 : fetch_word Plain.M.loaded_segments (0x7c520 : word) = Some W_7c4c8.
Proof. vm_refl. Qed.
Lemma D_7c4c8 : decode_any W_7c4c8 = Some (Store SZ4 23 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4cc : bv 32 := 0x004b8b93.
Lemma F_7c4cc : fetch_word Plain.M.loaded_segments (0x7c524 : word) = Some W_7c4cc.
Proof. vm_refl. Qed.
Lemma D_7c4cc : decode_any W_7c4cc = Some (OpImm ALU_ADD 23 23 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4d0 : bv 32 := 0x004b0b13.
Lemma F_7c4d0 : fetch_word Plain.M.loaded_segments (0x7c528 : word) = Some W_7c4d0.
Proof. vm_refl. Qed.
Lemma D_7c4d0 : decode_any W_7c4d0 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4d4 : bv 32 := 0xfc7b96e3.
Lemma F_7c4d4 : fetch_word Plain.M.loaded_segments (0x7c52c : word) = Some W_7c4d4.
Proof. vm_refl. Qed.
Lemma D_7c4d4 : decode_any W_7c4d4 = Some (Branch BC_NE 23 7 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c4d8 : bv 32 := 0xf9dff06f.
Lemma F_7c4d8 : fetch_word Plain.M.loaded_segments (0x7c530 : word) = Some W_7c4d8.
Proof. vm_refl. Qed.
Lemma D_7c4d8 : decode_any W_7c4d8 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

