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
Definition W_7b070 : bv 32 := 0x100a0063.
Lemma F_7b070 : fetch_word Plain.M.loaded_segments (0x7b0c8 : word) = Some W_7b070.
Proof. vm_refl. Qed.
Lemma D_7b070 : decode_any W_7b070 = Some (Branch BC_EQ 20 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b074 : bv 32 := 0xfff94513.
Lemma F_7b074 : fetch_word Plain.M.loaded_segments (0x7b0cc : word) = Some W_7b074.
Proof. vm_refl. Qed.
Lemma D_7b074 : decode_any W_7b074 = Some (OpImm ALU_XOR 10 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b078 : bv 32 := 0xfff8c593.
Lemma F_7b078 : fetch_word Plain.M.loaded_segments (0x7b0d0 : word) = Some W_7b078.
Proof. vm_refl. Qed.
Lemma D_7b078 : decode_any W_7b078 = Some (OpImm ALU_XOR 11 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b07c : bv 32 := 0x00408093.
Lemma F_7b07c : fetch_word Plain.M.loaded_segments (0x7b0d4 : word) = Some W_7b07c.
Proof. vm_refl. Qed.
Lemma D_7b07c : decode_any W_7b07c = Some (OpImm ALU_ADD 1 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b080 : bv 32 := 0x00269a13.
Lemma F_7b080 : fetch_word Plain.M.loaded_segments (0x7b0d8 : word) = Some W_7b080.
Proof. vm_refl. Qed.
Lemma D_7b080 : decode_any W_7b080 = Some (ShiftImm ALU_SLL 20 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b084 : bv 32 := 0x00271a93.
Lemma F_7b084 : fetch_word Plain.M.loaded_segments (0x7b0dc : word) = Some W_7b084.
Proof. vm_refl. Qed.
Lemma D_7b084 : decode_any W_7b084 = Some (ShiftImm ALU_SLL 21 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b088 : bv 32 := 0x001cfb13.
Lemma F_7b088 : fetch_word Plain.M.loaded_segments (0x7b0e0 : word) = Some W_7b088.
Proof. vm_refl. Qed.
Lemma D_7b088 : decode_any W_7b088 = Some (OpImm ALU_AND 22 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b08c : bv 32 := 0x001c7b93.
Lemma F_7b08c : fetch_word Plain.M.loaded_segments (0x7b0e4 : word) = Some W_7b08c.
Proof. vm_refl. Qed.
Lemma D_7b08c : decode_any W_7b08c = Some (OpImm ALU_AND 23 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b090 : bv 32 := 0x00060c13.
Lemma F_7b090 : fetch_word Plain.M.loaded_segments (0x7b0e8 : word) = Some W_7b090.
Proof. vm_refl. Qed.
Lemma D_7b090 : decode_any W_7b090 = Some (OpImm ALU_ADD 24 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b094 : bv 32 := 0x0300006f.
Lemma F_7b094 : fetch_word Plain.M.loaded_segments (0x7b0ec : word) = Some W_7b094.
Proof. vm_refl. Qed.
Lemma D_7b094 : decode_any W_7b094 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b098 : bv 32 := 0x0103d3bb.
Lemma F_7b098 : fetch_word Plain.M.loaded_segments (0x7b0f0 : word) = Some W_7b098.
Proof. vm_refl. Qed.
Lemma D_7b098 : decode_any W_7b098 = Some (Op32 ALU_SRL 7 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b09c : bv 32 := 0x00042f83.
Lemma F_7b09c : fetch_word Plain.M.loaded_segments (0x7b0f4 : word) = Some W_7b09c.
Proof. vm_refl. Qed.
Lemma D_7b09c : decode_any W_7b09c = Some (Load SZ4 true 31 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0a0 : bv 32 := 0xfff3c393.
Lemma F_7b0a0 : fetch_word Plain.M.loaded_segments (0x7b0f8 : word) = Some W_7b0a0.
Proof. vm_refl. Qed.
Lemma D_7b0a0 : decode_any W_7b0a0 = Some (OpImm ALU_XOR 7 7 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0a4 : bv 32 := 0xfffc0c1b.
Lemma F_7b0a4 : fetch_word Plain.M.loaded_segments (0x7b0fc : word) = Some W_7b0a4.
Proof. vm_refl. Qed.
Lemma D_7b0a4 : decode_any W_7b0a4 = Some (OpImm32 24 24 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0a8 : bv 32 := 0x014080b3.
Lemma F_7b0a8 : fetch_word Plain.M.loaded_segments (0x7b100 : word) = Some W_7b0a8.
Proof. vm_refl. Qed.
Lemma D_7b0a8 : decode_any W_7b0a8 = Some (Op ALU_ADD 1 1 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0ac : bv 32 := 0x007973b3.
Lemma F_7b0ac : fetch_word Plain.M.loaded_segments (0x7b104 : word) = Some W_7b0ac.
Proof. vm_refl. Qed.
Lemma D_7b0ac : decode_any W_7b0ac = Some (Op ALU_AND 7 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0b0 : bv 32 := 0x00afffb3.
Lemma F_7b0b0 : fetch_word Plain.M.loaded_segments (0x7b108 : word) = Some W_7b0b0.
Proof. vm_refl. Qed.
Lemma D_7b0b0 : decode_any W_7b0b0 = Some (Op ALU_AND 31 31 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0b4 : bv 32 := 0x007fe3b3.
Lemma F_7b0b4 : fetch_word Plain.M.loaded_segments (0x7b10c : word) = Some W_7b0b4.
Proof. vm_refl. Qed.
Lemma D_7b0b4 : decode_any W_7b0b4 = Some (Op ALU_OR 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0b8 : bv 32 := 0x00742023.
Lemma F_7b0b8 : fetch_word Plain.M.loaded_segments (0x7b110 : word) = Some W_7b0b8.
Proof. vm_refl. Qed.
Lemma D_7b0b8 : decode_any W_7b0b8 = Some (Store SZ4 8 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0bc : bv 32 := 0x01540433.
Lemma F_7b0bc : fetch_word Plain.M.loaded_segments (0x7b114 : word) = Some W_7b0bc.
Proof. vm_refl. Qed.
Lemma D_7b0bc : decode_any W_7b0bc = Some (Op ALU_ADD 8 8 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0c0 : bv 32 := 0x0a0c0863.
Lemma F_7b0c0 : fetch_word Plain.M.loaded_segments (0x7b118 : word) = Some W_7b0c0.
Proof. vm_refl. Qed.
Lemma D_7b0c0 : decode_any W_7b0c0 = Some (Branch BC_EQ 24 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0c4 : bv 32 := 0xffc0a383.
Lemma F_7b0c4 : fetch_word Plain.M.loaded_segments (0x7b11c : word) = Some W_7b0c4.
Proof. vm_refl. Qed.
Lemma D_7b0c4 : decode_any W_7b0c4 = Some (Load SZ4 true 7 1 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0c8 : bv 32 := 0xfc0b08e3.
Lemma F_7b0c8 : fetch_word Plain.M.loaded_segments (0x7b120 : word) = Some W_7b0c8.
Proof. vm_refl. Qed.
Lemma D_7b0c8 : decode_any W_7b0c8 = Some (Branch BC_EQ 22 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0cc : bv 32 := 0x00f393bb.
Lemma F_7b0cc : fetch_word Plain.M.loaded_segments (0x7b124 : word) = Some W_7b0cc.
Proof. vm_refl. Qed.
Lemma D_7b0cc : decode_any W_7b0cc = Some (Op32 ALU_SLL 7 7 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0d0 : bv 32 := 0xfc0b96e3.
Lemma F_7b0d0 : fetch_word Plain.M.loaded_segments (0x7b128 : word) = Some W_7b0d0.
Proof. vm_refl. Qed.
Lemma D_7b0d0 : decode_any W_7b0d0 = Some (Branch BC_NE 23 0 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0d4 : bv 32 := 0x0000af83.
Lemma F_7b0d4 : fetch_word Plain.M.loaded_segments (0x7b12c : word) = Some W_7b0d4.
Proof. vm_refl. Qed.
Lemma D_7b0d4 : decode_any W_7b0d4 = Some (Load SZ4 true 31 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0d8 : bv 32 := 0x00b3f3b3.
Lemma F_7b0d8 : fetch_word Plain.M.loaded_segments (0x7b130 : word) = Some W_7b0d8.
Proof. vm_refl. Qed.
Lemma D_7b0d8 : decode_any W_7b0d8 = Some (Op ALU_AND 7 7 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0dc : bv 32 := 0x010fdfbb.
Lemma F_7b0dc : fetch_word Plain.M.loaded_segments (0x7b134 : word) = Some W_7b0dc.
Proof. vm_refl. Qed.
Lemma D_7b0dc : decode_any W_7b0dc = Some (Op32 ALU_SRL 31 31 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0e0 : bv 32 := 0x011fffb3.
Lemma F_7b0e0 : fetch_word Plain.M.loaded_segments (0x7b138 : word) = Some W_7b0e0.
Proof. vm_refl. Qed.
Lemma D_7b0e0 : decode_any W_7b0e0 = Some (Op ALU_AND 31 31 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0e4 : bv 32 := 0x007fe3b3.
Lemma F_7b0e4 : fetch_word Plain.M.loaded_segments (0x7b13c : word) = Some W_7b0e4.
Proof. vm_refl. Qed.
Lemma D_7b0e4 : decode_any W_7b0e4 = Some (Op ALU_OR 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b0e8 : bv 32 := 0xfb5ff06f.
Lemma F_7b0e8 : fetch_word Plain.M.loaded_segments (0x7b140 : word) = Some W_7b0e8.
Proof. vm_refl. Qed.
Lemma D_7b0e8 : decode_any W_7b0e8 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b170 : bv 32 := 0x70098ce3.
Lemma F_7b170 : fetch_word Plain.M.loaded_segments (0x7b1c8 : word) = Some W_7b170.
Proof. vm_refl. Qed.
Lemma D_7b170 : decode_any W_7b170 = Some (Branch BC_EQ 19 0 3864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b174 : bv 32 := 0x00013503.
Lemma F_7b174 : fetch_word Plain.M.loaded_segments (0x7b1cc : word) = Some W_7b174.
Proof. vm_refl. Qed.
Lemma D_7b174 : decode_any W_7b174 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b178 : bv 32 := 0x56051ce3.
Lemma F_7b178 : fetch_word Plain.M.loaded_segments (0x7b1d0 : word) = Some W_7b178.
Proof. vm_refl. Qed.
Lemma D_7b178 : decode_any W_7b178 = Some (Branch BC_NE 10 0 3448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b17c : bv 32 := 0xfff34513.
Lemma F_7b17c : fetch_word Plain.M.loaded_segments (0x7b1d4 : word) = Some W_7b17c.
Proof. vm_refl. Qed.
Lemma D_7b17c : decode_any W_7b17c = Some (OpImm ALU_XOR 10 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b180 : bv 32 := 0xfff8c593.
Lemma F_7b180 : fetch_word Plain.M.loaded_segments (0x7b1d8 : word) = Some W_7b180.
Proof. vm_refl. Qed.
Lemma D_7b180 : decode_any W_7b180 = Some (OpImm ALU_XOR 11 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b184 : bv 32 := 0x004d0393.
Lemma F_7b184 : fetch_word Plain.M.loaded_segments (0x7b1dc : word) = Some W_7b184.
Proof. vm_refl. Qed.
Lemma D_7b184 : decode_any W_7b184 = Some (OpImm ALU_ADD 7 26 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b188 : bv 32 := 0x00269693.
Lemma F_7b188 : fetch_word Plain.M.loaded_segments (0x7b1e0 : word) = Some W_7b188.
Proof. vm_refl. Qed.
Lemma D_7b188 : decode_any W_7b188 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b18c : bv 32 := 0x00271713.
Lemma F_7b18c : fetch_word Plain.M.loaded_segments (0x7b1e4 : word) = Some W_7b18c.
Proof. vm_refl. Qed.
Lemma D_7b18c : decode_any W_7b18c = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b190 : bv 32 := 0x001f7e13.
Lemma F_7b190 : fetch_word Plain.M.loaded_segments (0x7b1e8 : word) = Some W_7b190.
Proof. vm_refl. Qed.
Lemma D_7b190 : decode_any W_7b190 = Some (OpImm ALU_AND 28 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b194 : bv 32 := 0x02c0006f.
Lemma F_7b194 : fetch_word Plain.M.loaded_segments (0x7b1ec : word) = Some W_7b194.
Proof. vm_refl. Qed.
Lemma D_7b194 : decode_any W_7b194 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b198 : bv 32 := 0x0002af03.
Lemma F_7b198 : fetch_word Plain.M.loaded_segments (0x7b1f0 : word) = Some W_7b198.
Proof. vm_refl. Qed.
Lemma D_7b198 : decode_any W_7b198 = Some (Load SZ4 true 30 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b19c : bv 32 := 0xfffece93.
Lemma F_7b19c : fetch_word Plain.M.loaded_segments (0x7b1f4 : word) = Some W_7b19c.
Proof. vm_refl. Qed.
Lemma D_7b19c : decode_any W_7b19c = Some (OpImm ALU_XOR 29 29 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1a0 : bv 32 := 0xfff6061b.
Lemma F_7b1a0 : fetch_word Plain.M.loaded_segments (0x7b1f8 : word) = Some W_7b1a0.
Proof. vm_refl. Qed.
Lemma D_7b1a0 : decode_any W_7b1a0 = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1a4 : bv 32 := 0x00d383b3.
Lemma F_7b1a4 : fetch_word Plain.M.loaded_segments (0x7b1fc : word) = Some W_7b1a4.
Proof. vm_refl. Qed.
Lemma D_7b1a4 : decode_any W_7b1a4 = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1a8 : bv 32 := 0x01d37eb3.
Lemma F_7b1a8 : fetch_word Plain.M.loaded_segments (0x7b200 : word) = Some W_7b1a8.
Proof. vm_refl. Qed.
Lemma D_7b1a8 : decode_any W_7b1a8 = Some (Op ALU_AND 29 6 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1ac : bv 32 := 0x00af7f33.
Lemma F_7b1ac : fetch_word Plain.M.loaded_segments (0x7b204 : word) = Some W_7b1ac.
Proof. vm_refl. Qed.
Lemma D_7b1ac : decode_any W_7b1ac = Some (Op ALU_AND 30 30 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1b0 : bv 32 := 0x01df6eb3.
Lemma F_7b1b0 : fetch_word Plain.M.loaded_segments (0x7b208 : word) = Some W_7b1b0.
Proof. vm_refl. Qed.
Lemma D_7b1b0 : decode_any W_7b1b0 = Some (Op ALU_OR 29 30 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1b4 : bv 32 := 0x01d2a023.
Lemma F_7b1b4 : fetch_word Plain.M.loaded_segments (0x7b20c : word) = Some W_7b1b4.
Proof. vm_refl. Qed.
Lemma D_7b1b4 : decode_any W_7b1b4 = Some (Store SZ4 5 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1b8 : bv 32 := 0x00e282b3.
Lemma F_7b1b8 : fetch_word Plain.M.loaded_segments (0x7b210 : word) = Some W_7b1b8.
Proof. vm_refl. Qed.
Lemma D_7b1b8 : decode_any W_7b1b8 = Some (Op ALU_ADD 5 5 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1bc : bv 32 := 0x52060ae3.
Lemma F_7b1bc : fetch_word Plain.M.loaded_segments (0x7b214 : word) = Some W_7b1bc.
Proof. vm_refl. Qed.
Lemma D_7b1bc : decode_any W_7b1bc = Some (Branch BC_EQ 12 0 3380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1c0 : bv 32 := 0xffc3ae83.
Lemma F_7b1c0 : fetch_word Plain.M.loaded_segments (0x7b218 : word) = Some W_7b1c0.
Proof. vm_refl. Qed.
Lemma D_7b1c0 : decode_any W_7b1c0 = Some (Load SZ4 true 29 7 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1c4 : bv 32 := 0x00fe9ebb.
Lemma F_7b1c4 : fetch_word Plain.M.loaded_segments (0x7b21c : word) = Some W_7b1c4.
Proof. vm_refl. Qed.
Lemma D_7b1c4 : decode_any W_7b1c4 = Some (Op32 ALU_SLL 29 29 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1c8 : bv 32 := 0xfc0e18e3.
Lemma F_7b1c8 : fetch_word Plain.M.loaded_segments (0x7b220 : word) = Some W_7b1c8.
Proof. vm_refl. Qed.
Lemma D_7b1c8 : decode_any W_7b1c8 = Some (Branch BC_NE 28 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1cc : bv 32 := 0x0003af03.
Lemma F_7b1cc : fetch_word Plain.M.loaded_segments (0x7b224 : word) = Some W_7b1cc.
Proof. vm_refl. Qed.
Lemma D_7b1cc : decode_any W_7b1cc = Some (Load SZ4 true 30 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1d0 : bv 32 := 0x00befeb3.
Lemma F_7b1d0 : fetch_word Plain.M.loaded_segments (0x7b228 : word) = Some W_7b1d0.
Proof. vm_refl. Qed.
Lemma D_7b1d0 : decode_any W_7b1d0 = Some (Op ALU_AND 29 29 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1d4 : bv 32 := 0x010f5f3b.
Lemma F_7b1d4 : fetch_word Plain.M.loaded_segments (0x7b22c : word) = Some W_7b1d4.
Proof. vm_refl. Qed.
Lemma D_7b1d4 : decode_any W_7b1d4 = Some (Op32 ALU_SRL 30 30 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1d8 : bv 32 := 0x011f7f33.
Lemma F_7b1d8 : fetch_word Plain.M.loaded_segments (0x7b230 : word) = Some W_7b1d8.
Proof. vm_refl. Qed.
Lemma D_7b1d8 : decode_any W_7b1d8 = Some (Op ALU_AND 30 30 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1dc : bv 32 := 0x01df6eb3.
Lemma F_7b1dc : fetch_word Plain.M.loaded_segments (0x7b234 : word) = Some W_7b1dc.
Proof. vm_refl. Qed.
Lemma D_7b1dc : decode_any W_7b1dc = Some (Op ALU_OR 29 30 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b1e0 : bv 32 := 0xfb9ff06f.
Lemma F_7b1e0 : fetch_word Plain.M.loaded_segments (0x7b238 : word) = Some W_7b1e0.
Proof. vm_refl. Qed.
Lemma D_7b1e0 : decode_any W_7b1e0 = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c088 : bv 32 := 0x00000513.
Lemma F_7c088 : fetch_word Plain.M.loaded_segments (0x7c0e0 : word) = Some W_7c088.
Proof. vm_refl. Qed.
Lemma D_7c088 : decode_any W_7c088 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c08c : bv 32 := 0x00000593.
Lemma F_7c08c : fetch_word Plain.M.loaded_segments (0x7c0e4 : word) = Some W_7c08c.
Proof. vm_refl. Qed.
Lemma D_7c08c : decode_any W_7c08c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c090 : bv 32 := 0xfff8c413.
Lemma F_7c090 : fetch_word Plain.M.loaded_segments (0x7c0e8 : word) = Some W_7c090.
Proof. vm_refl. Qed.
Lemma D_7c090 : decode_any W_7c090 = Some (OpImm ALU_XOR 8 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c094 : bv 32 := 0x00271913.
Lemma F_7c094 : fetch_word Plain.M.loaded_segments (0x7c0ec : word) = Some W_7c094.
Proof. vm_refl. Qed.
Lemma D_7c094 : decode_any W_7c094 = Some (ShiftImm ALU_SLL 18 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c098 : bv 32 := 0x00448493.
Lemma F_7c098 : fetch_word Plain.M.loaded_segments (0x7c0f0 : word) = Some W_7c098.
Proof. vm_refl. Qed.
Lemma D_7c098 : decode_any W_7c098 = Some (OpImm ALU_ADD 9 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c09c : bv 32 := 0x00269993.
Lemma F_7c09c : fetch_word Plain.M.loaded_segments (0x7c0f4 : word) = Some W_7c09c.
Proof. vm_refl. Qed.
Lemma D_7c09c : decode_any W_7c09c = Some (ShiftImm ALU_SLL 19 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0a0 : bv 32 := 0x002e1a13.
Lemma F_7c0a0 : fetch_word Plain.M.loaded_segments (0x7c0f8 : word) = Some W_7c0a0.
Proof. vm_refl. Qed.
Lemma D_7c0a0 : decode_any W_7c0a0 = Some (ShiftImm ALU_SLL 20 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0a4 : bv 32 := 0x000e8a93.
Lemma F_7c0a4 : fetch_word Plain.M.loaded_segments (0x7c0fc : word) = Some W_7c0a4.
Proof. vm_refl. Qed.
Lemma D_7c0a4 : decode_any W_7c0a4 = Some (OpImm ALU_ADD 21 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0a8 : bv 32 := 0x0180006f.
Lemma F_7c0a8 : fetch_word Plain.M.loaded_segments (0x7c100 : word) = Some W_7c0a8.
Proof. vm_refl. Qed.
Lemma D_7c0a8 : decode_any W_7c0a8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0ac : bv 32 := 0x0015859b.
Lemma F_7c0ac : fetch_word Plain.M.loaded_segments (0x7c104 : word) = Some W_7c0ac.
Proof. vm_refl. Qed.
Lemma D_7c0ac : decode_any W_7c0ac = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0b0 : bv 32 := 0x012a8ab3.
Lemma F_7c0b0 : fetch_word Plain.M.loaded_segments (0x7c108 : word) = Some W_7c0b0.
Proof. vm_refl. Qed.
Lemma D_7c0b0 : decode_any W_7c0b0 = Some (Op ALU_ADD 21 21 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0b4 : bv 32 := 0x013484b3.
Lemma F_7c0b4 : fetch_word Plain.M.loaded_segments (0x7c10c : word) = Some W_7c0b4.
Proof. vm_refl. Qed.
Lemma D_7c0b4 : decode_any W_7c0b4 = Some (Op ALU_ADD 9 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0b8 : bv 32 := 0x00150513.
Lemma F_7c0b8 : fetch_word Plain.M.loaded_segments (0x7c110 : word) = Some W_7c0b8.
Proof. vm_refl. Qed.
Lemma D_7c0b8 : decode_any W_7c0b8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0bc : bv 32 := 0x8ac58c63.
Lemma F_7c0bc : fetch_word Plain.M.loaded_segments (0x7c114 : word) = Some W_7c0bc.
Proof. vm_refl. Qed.
Lemma D_7c0bc : decode_any W_7c0bc = Some (Branch BC_EQ 11 12 4280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0c0 : bv 32 := 0xfe0e06e3.
Lemma F_7c0c0 : fetch_word Plain.M.loaded_segments (0x7c118 : word) = Some W_7c0c0.
Proof. vm_refl. Qed.
Lemma D_7c0c0 : decode_any W_7c0c0 = Some (Branch BC_EQ 28 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0c4 : bv 32 := 0x02a903b3.
Lemma F_7c0c4 : fetch_word Plain.M.loaded_segments (0x7c11c : word) = Some W_7c0c4.
Proof. vm_refl. Qed.
Lemma D_7c0c4 : decode_any W_7c0c4 = Some (Mul M_MUL 7 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0c8 : bv 32 := 0x007a03b3.
Lemma F_7c0c8 : fetch_word Plain.M.loaded_segments (0x7c120 : word) = Some W_7c0c8.
Proof. vm_refl. Qed.
Lemma D_7c0c8 : decode_any W_7c0c8 = Some (Op ALU_ADD 7 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0cc : bv 32 := 0x007e83b3.
Lemma F_7c0cc : fetch_word Plain.M.loaded_segments (0x7c124 : word) = Some W_7c0cc.
Proof. vm_refl. Qed.
Lemma D_7c0cc : decode_any W_7c0cc = Some (Op ALU_ADD 7 29 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0d0 : bv 32 := 0x00048b13.
Lemma F_7c0d0 : fetch_word Plain.M.loaded_segments (0x7c128 : word) = Some W_7c0d0.
Proof. vm_refl. Qed.
Lemma D_7c0d0 : decode_any W_7c0d0 = Some (OpImm ALU_ADD 22 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0d4 : bv 32 := 0x000a8b93.
Lemma F_7c0d4 : fetch_word Plain.M.loaded_segments (0x7c12c : word) = Some W_7c0d4.
Proof. vm_refl. Qed.
Lemma D_7c0d4 : decode_any W_7c0d4 = Some (OpImm ALU_ADD 23 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0d8 : bv 32 := 0xffcb2f83.
Lemma F_7c0d8 : fetch_word Plain.M.loaded_segments (0x7c130 : word) = Some W_7c0d8.
Proof. vm_refl. Qed.
Lemma D_7c0d8 : decode_any W_7c0d8 = Some (Load SZ4 true 31 22 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0dc : bv 32 := 0x000b2c03.
Lemma F_7c0dc : fetch_word Plain.M.loaded_segments (0x7c134 : word) = Some W_7c0dc.
Proof. vm_refl. Qed.
Lemma D_7c0dc : decode_any W_7c0dc = Some (Load SZ4 true 24 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0e0 : bv 32 := 0x00ff9fbb.
Lemma F_7c0e0 : fetch_word Plain.M.loaded_segments (0x7c138 : word) = Some W_7c0e0.
Proof. vm_refl. Qed.
Lemma D_7c0e0 : decode_any W_7c0e0 = Some (Op32 ALU_SLL 31 31 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0e4 : bv 32 := 0x010c5c3b.
Lemma F_7c0e4 : fetch_word Plain.M.loaded_segments (0x7c13c : word) = Some W_7c0e4.
Proof. vm_refl. Qed.
Lemma D_7c0e4 : decode_any W_7c0e4 = Some (Op32 ALU_SRL 24 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0e8 : bv 32 := 0x008fffb3.
Lemma F_7c0e8 : fetch_word Plain.M.loaded_segments (0x7c140 : word) = Some W_7c0e8.
Proof. vm_refl. Qed.
Lemma D_7c0e8 : decode_any W_7c0e8 = Some (Op ALU_AND 31 31 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0ec : bv 32 := 0x011c7c33.
Lemma F_7c0ec : fetch_word Plain.M.loaded_segments (0x7c144 : word) = Some W_7c0ec.
Proof. vm_refl. Qed.
Lemma D_7c0ec : decode_any W_7c0ec = Some (Op ALU_AND 24 24 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0f0 : bv 32 := 0x01fc6fb3.
Lemma F_7c0f0 : fetch_word Plain.M.loaded_segments (0x7c148 : word) = Some W_7c0f0.
Proof. vm_refl. Qed.
Lemma D_7c0f0 : decode_any W_7c0f0 = Some (Op ALU_OR 31 24 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0f4 : bv 32 := 0xffffcf93.
Lemma F_7c0f4 : fetch_word Plain.M.loaded_segments (0x7c14c : word) = Some W_7c0f4.
Proof. vm_refl. Qed.
Lemma D_7c0f4 : decode_any W_7c0f4 = Some (OpImm ALU_XOR 31 31 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0f8 : bv 32 := 0x01fba023.
Lemma F_7c0f8 : fetch_word Plain.M.loaded_segments (0x7c150 : word) = Some W_7c0f8.
Proof. vm_refl. Qed.
Lemma D_7c0f8 : decode_any W_7c0f8 = Some (Store SZ4 23 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c0fc : bv 32 := 0x004b8b93.
Lemma F_7c0fc : fetch_word Plain.M.loaded_segments (0x7c154 : word) = Some W_7c0fc.
Proof. vm_refl. Qed.
Lemma D_7c0fc : decode_any W_7c0fc = Some (OpImm ALU_ADD 23 23 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c100 : bv 32 := 0x004b0b13.
Lemma F_7c100 : fetch_word Plain.M.loaded_segments (0x7c158 : word) = Some W_7c100.
Proof. vm_refl. Qed.
Lemma D_7c100 : decode_any W_7c100 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c104 : bv 32 := 0xfc7b9ae3.
Lemma F_7c104 : fetch_word Plain.M.loaded_segments (0x7c15c : word) = Some W_7c104.
Proof. vm_refl. Qed.
Lemma D_7c104 : decode_any W_7c104 = Some (Branch BC_NE 23 7 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c108 : bv 32 := 0xfa5ff06f.
Lemma F_7c108 : fetch_word Plain.M.loaded_segments (0x7c160 : word) = Some W_7c108.
Proof. vm_refl. Qed.
Lemma D_7c108 : decode_any W_7c108 = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

