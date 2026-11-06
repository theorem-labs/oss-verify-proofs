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
Definition W_7b69c : bv 32 := 0x0e0a0463.
Lemma F_7b69c : fetch_word Plain.M.loaded_segments (0x7b6f4 : word) = Some W_7b69c.
Proof. vm_refl. Qed.
Lemma D_7b69c : decode_any W_7b69c = Some (Branch BC_EQ 20 0 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6a0 : bv 32 := 0xfff94513.
Lemma F_7b6a0 : fetch_word Plain.M.loaded_segments (0x7b6f8 : word) = Some W_7b6a0.
Proof. vm_refl. Qed.
Lemma D_7b6a0 : decode_any W_7b6a0 = Some (OpImm ALU_XOR 10 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6a4 : bv 32 := 0xfff8c593.
Lemma F_7b6a4 : fetch_word Plain.M.loaded_segments (0x7b6fc : word) = Some W_7b6a4.
Proof. vm_refl. Qed.
Lemma D_7b6a4 : decode_any W_7b6a4 = Some (OpImm ALU_XOR 11 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6a8 : bv 32 := 0x00408093.
Lemma F_7b6a8 : fetch_word Plain.M.loaded_segments (0x7b700 : word) = Some W_7b6a8.
Proof. vm_refl. Qed.
Lemma D_7b6a8 : decode_any W_7b6a8 = Some (OpImm ALU_ADD 1 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6ac : bv 32 := 0x00269913.
Lemma F_7b6ac : fetch_word Plain.M.loaded_segments (0x7b704 : word) = Some W_7b6ac.
Proof. vm_refl. Qed.
Lemma D_7b6ac : decode_any W_7b6ac = Some (ShiftImm ALU_SLL 18 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6b0 : bv 32 := 0x00271a13.
Lemma F_7b6b0 : fetch_word Plain.M.loaded_segments (0x7b708 : word) = Some W_7b6b0.
Proof. vm_refl. Qed.
Lemma D_7b6b0 : decode_any W_7b6b0 = Some (ShiftImm ALU_SLL 20 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6b4 : bv 32 := 0x001cfa93.
Lemma F_7b6b4 : fetch_word Plain.M.loaded_segments (0x7b70c : word) = Some W_7b6b4.
Proof. vm_refl. Qed.
Lemma D_7b6b4 : decode_any W_7b6b4 = Some (OpImm ALU_AND 21 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6b8 : bv 32 := 0x001c7b13.
Lemma F_7b6b8 : fetch_word Plain.M.loaded_segments (0x7b710 : word) = Some W_7b6b8.
Proof. vm_refl. Qed.
Lemma D_7b6b8 : decode_any W_7b6b8 = Some (OpImm ALU_AND 22 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6bc : bv 32 := 0x00060b93.
Lemma F_7b6bc : fetch_word Plain.M.loaded_segments (0x7b714 : word) = Some W_7b6bc.
Proof. vm_refl. Qed.
Lemma D_7b6bc : decode_any W_7b6bc = Some (OpImm ALU_ADD 23 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6c0 : bv 32 := 0x0280006f.
Lemma F_7b6c0 : fetch_word Plain.M.loaded_segments (0x7b718 : word) = Some W_7b6c0.
Proof. vm_refl. Qed.
Lemma D_7b6c0 : decode_any W_7b6c0 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6c4 : bv 32 := 0x0103d3bb.
Lemma F_7b6c4 : fetch_word Plain.M.loaded_segments (0x7b71c : word) = Some W_7b6c4.
Proof. vm_refl. Qed.
Lemma D_7b6c4 : decode_any W_7b6c4 = Some (Op32 ALU_SRL 7 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6c8 : bv 32 := 0x00042f83.
Lemma F_7b6c8 : fetch_word Plain.M.loaded_segments (0x7b720 : word) = Some W_7b6c8.
Proof. vm_refl. Qed.
Lemma D_7b6c8 : decode_any W_7b6c8 = Some (Load SZ4 true 31 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6cc : bv 32 := 0x00a3e3b3.
Lemma F_7b6cc : fetch_word Plain.M.loaded_segments (0x7b724 : word) = Some W_7b6cc.
Proof. vm_refl. Qed.
Lemma D_7b6cc : decode_any W_7b6cc = Some (Op ALU_OR 7 7 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6d0 : bv 32 := 0xfffb8b9b.
Lemma F_7b6d0 : fetch_word Plain.M.loaded_segments (0x7b728 : word) = Some W_7b6d0.
Proof. vm_refl. Qed.
Lemma D_7b6d0 : decode_any W_7b6d0 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6d4 : bv 32 := 0x012080b3.
Lemma F_7b6d4 : fetch_word Plain.M.loaded_segments (0x7b72c : word) = Some W_7b6d4.
Proof. vm_refl. Qed.
Lemma D_7b6d4 : decode_any W_7b6d4 = Some (Op ALU_ADD 1 1 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6d8 : bv 32 := 0x01f3f3b3.
Lemma F_7b6d8 : fetch_word Plain.M.loaded_segments (0x7b730 : word) = Some W_7b6d8.
Proof. vm_refl. Qed.
Lemma D_7b6d8 : decode_any W_7b6d8 = Some (Op ALU_AND 7 7 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6dc : bv 32 := 0x00742023.
Lemma F_7b6dc : fetch_word Plain.M.loaded_segments (0x7b734 : word) = Some W_7b6dc.
Proof. vm_refl. Qed.
Lemma D_7b6dc : decode_any W_7b6dc = Some (Store SZ4 8 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6e0 : bv 32 := 0x01440433.
Lemma F_7b6e0 : fetch_word Plain.M.loaded_segments (0x7b738 : word) = Some W_7b6e0.
Proof. vm_refl. Qed.
Lemma D_7b6e0 : decode_any W_7b6e0 = Some (Op ALU_ADD 8 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6e4 : bv 32 := 0x0a0b8063.
Lemma F_7b6e4 : fetch_word Plain.M.loaded_segments (0x7b73c : word) = Some W_7b6e4.
Proof. vm_refl. Qed.
Lemma D_7b6e4 : decode_any W_7b6e4 = Some (Branch BC_EQ 23 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6e8 : bv 32 := 0xffc0a383.
Lemma F_7b6e8 : fetch_word Plain.M.loaded_segments (0x7b740 : word) = Some W_7b6e8.
Proof. vm_refl. Qed.
Lemma D_7b6e8 : decode_any W_7b6e8 = Some (Load SZ4 true 7 1 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6ec : bv 32 := 0xfc0a8ce3.
Lemma F_7b6ec : fetch_word Plain.M.loaded_segments (0x7b744 : word) = Some W_7b6ec.
Proof. vm_refl. Qed.
Lemma D_7b6ec : decode_any W_7b6ec = Some (Branch BC_EQ 21 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6f0 : bv 32 := 0x00f393bb.
Lemma F_7b6f0 : fetch_word Plain.M.loaded_segments (0x7b748 : word) = Some W_7b6f0.
Proof. vm_refl. Qed.
Lemma D_7b6f0 : decode_any W_7b6f0 = Some (Op32 ALU_SLL 7 7 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6f4 : bv 32 := 0xfc0b1ae3.
Lemma F_7b6f4 : fetch_word Plain.M.loaded_segments (0x7b74c : word) = Some W_7b6f4.
Proof. vm_refl. Qed.
Lemma D_7b6f4 : decode_any W_7b6f4 = Some (Branch BC_NE 22 0 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6f8 : bv 32 := 0x0000af83.
Lemma F_7b6f8 : fetch_word Plain.M.loaded_segments (0x7b750 : word) = Some W_7b6f8.
Proof. vm_refl. Qed.
Lemma D_7b6f8 : decode_any W_7b6f8 = Some (Load SZ4 true 31 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6fc : bv 32 := 0x00b3f3b3.
Lemma F_7b6fc : fetch_word Plain.M.loaded_segments (0x7b754 : word) = Some W_7b6fc.
Proof. vm_refl. Qed.
Lemma D_7b6fc : decode_any W_7b6fc = Some (Op ALU_AND 7 7 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b700 : bv 32 := 0x010fdfbb.
Lemma F_7b700 : fetch_word Plain.M.loaded_segments (0x7b758 : word) = Some W_7b700.
Proof. vm_refl. Qed.
Lemma D_7b700 : decode_any W_7b700 = Some (Op32 ALU_SRL 31 31 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b704 : bv 32 := 0x011fffb3.
Lemma F_7b704 : fetch_word Plain.M.loaded_segments (0x7b75c : word) = Some W_7b704.
Proof. vm_refl. Qed.
Lemma D_7b704 : decode_any W_7b704 = Some (Op ALU_AND 31 31 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b708 : bv 32 := 0x007fe3b3.
Lemma F_7b708 : fetch_word Plain.M.loaded_segments (0x7b760 : word) = Some W_7b708.
Proof. vm_refl. Qed.
Lemma D_7b708 : decode_any W_7b708 = Some (Op ALU_OR 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b70c : bv 32 := 0xfbdff06f.
Lemma F_7b70c : fetch_word Plain.M.loaded_segments (0x7b764 : word) = Some W_7b70c.
Proof. vm_refl. Qed.
Lemma D_7b70c : decode_any W_7b70c = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b784 : bv 32 := 0x5c0980e3.
Lemma F_7b784 : fetch_word Plain.M.loaded_segments (0x7b7dc : word) = Some W_7b784.
Proof. vm_refl. Qed.
Lemma D_7b784 : decode_any W_7b784 = Some (Branch BC_EQ 19 0 3520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b788 : bv 32 := 0x00013503.
Lemma F_7b788 : fetch_word Plain.M.loaded_segments (0x7b7e0 : word) = Some W_7b788.
Proof. vm_refl. Qed.
Lemma D_7b788 : decode_any W_7b788 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b78c : bv 32 := 0x76051263.
Lemma F_7b78c : fetch_word Plain.M.loaded_segments (0x7b7e4 : word) = Some W_7b78c.
Proof. vm_refl. Qed.
Lemma D_7b78c : decode_any W_7b78c = Some (Branch BC_NE 10 0 1892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b790 : bv 32 := 0xfff34513.
Lemma F_7b790 : fetch_word Plain.M.loaded_segments (0x7b7e8 : word) = Some W_7b790.
Proof. vm_refl. Qed.
Lemma D_7b790 : decode_any W_7b790 = Some (OpImm ALU_XOR 10 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b794 : bv 32 := 0xfff8c593.
Lemma F_7b794 : fetch_word Plain.M.loaded_segments (0x7b7ec : word) = Some W_7b794.
Proof. vm_refl. Qed.
Lemma D_7b794 : decode_any W_7b794 = Some (OpImm ALU_XOR 11 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b798 : bv 32 := 0x004d0393.
Lemma F_7b798 : fetch_word Plain.M.loaded_segments (0x7b7f0 : word) = Some W_7b798.
Proof. vm_refl. Qed.
Lemma D_7b798 : decode_any W_7b798 = Some (OpImm ALU_ADD 7 26 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b79c : bv 32 := 0x00269693.
Lemma F_7b79c : fetch_word Plain.M.loaded_segments (0x7b7f4 : word) = Some W_7b79c.
Proof. vm_refl. Qed.
Lemma D_7b79c : decode_any W_7b79c = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7a0 : bv 32 := 0x00271713.
Lemma F_7b7a0 : fetch_word Plain.M.loaded_segments (0x7b7f8 : word) = Some W_7b7a0.
Proof. vm_refl. Qed.
Lemma D_7b7a0 : decode_any W_7b7a0 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7a4 : bv 32 := 0x001f7313.
Lemma F_7b7a4 : fetch_word Plain.M.loaded_segments (0x7b7fc : word) = Some W_7b7a4.
Proof. vm_refl. Qed.
Lemma D_7b7a4 : decode_any W_7b7a4 = Some (OpImm ALU_AND 6 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7a8 : bv 32 := 0x0240006f.
Lemma F_7b7a8 : fetch_word Plain.M.loaded_segments (0x7b800 : word) = Some W_7b7a8.
Proof. vm_refl. Qed.
Lemma D_7b7a8 : decode_any W_7b7a8 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7ac : bv 32 := 0x0002ae83.
Lemma F_7b7ac : fetch_word Plain.M.loaded_segments (0x7b804 : word) = Some W_7b7ac.
Proof. vm_refl. Qed.
Lemma D_7b7ac : decode_any W_7b7ac = Some (Load SZ4 true 29 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7b0 : bv 32 := 0x00ae6e33.
Lemma F_7b7b0 : fetch_word Plain.M.loaded_segments (0x7b808 : word) = Some W_7b7b0.
Proof. vm_refl. Qed.
Lemma D_7b7b0 : decode_any W_7b7b0 = Some (Op ALU_OR 28 28 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7b4 : bv 32 := 0xfff6061b.
Lemma F_7b7b4 : fetch_word Plain.M.loaded_segments (0x7b80c : word) = Some W_7b7b4.
Proof. vm_refl. Qed.
Lemma D_7b7b4 : decode_any W_7b7b4 = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7b8 : bv 32 := 0x00d383b3.
Lemma F_7b7b8 : fetch_word Plain.M.loaded_segments (0x7b810 : word) = Some W_7b7b8.
Proof. vm_refl. Qed.
Lemma D_7b7b8 : decode_any W_7b7b8 = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7bc : bv 32 := 0x01de7e33.
Lemma F_7b7bc : fetch_word Plain.M.loaded_segments (0x7b814 : word) = Some W_7b7bc.
Proof. vm_refl. Qed.
Lemma D_7b7bc : decode_any W_7b7bc = Some (Op ALU_AND 28 28 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7c0 : bv 32 := 0x01c2a023.
Lemma F_7b7c0 : fetch_word Plain.M.loaded_segments (0x7b818 : word) = Some W_7b7c0.
Proof. vm_refl. Qed.
Lemma D_7b7c0 : decode_any W_7b7c0 = Some (Store SZ4 5 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7c4 : bv 32 := 0x00e282b3.
Lemma F_7b7c4 : fetch_word Plain.M.loaded_segments (0x7b81c : word) = Some W_7b7c4.
Proof. vm_refl. Qed.
Lemma D_7b7c4 : decode_any W_7b7c4 = Some (Op ALU_ADD 5 5 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7c8 : bv 32 := 0x72060463.
Lemma F_7b7c8 : fetch_word Plain.M.loaded_segments (0x7b820 : word) = Some W_7b7c8.
Proof. vm_refl. Qed.
Lemma D_7b7c8 : decode_any W_7b7c8 = Some (Branch BC_EQ 12 0 1832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7cc : bv 32 := 0xffc3ae03.
Lemma F_7b7cc : fetch_word Plain.M.loaded_segments (0x7b824 : word) = Some W_7b7cc.
Proof. vm_refl. Qed.
Lemma D_7b7cc : decode_any W_7b7cc = Some (Load SZ4 true 28 7 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7d0 : bv 32 := 0x00fe1e3b.
Lemma F_7b7d0 : fetch_word Plain.M.loaded_segments (0x7b828 : word) = Some W_7b7d0.
Proof. vm_refl. Qed.
Lemma D_7b7d0 : decode_any W_7b7d0 = Some (Op32 ALU_SLL 28 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7d4 : bv 32 := 0xfc031ce3.
Lemma F_7b7d4 : fetch_word Plain.M.loaded_segments (0x7b82c : word) = Some W_7b7d4.
Proof. vm_refl. Qed.
Lemma D_7b7d4 : decode_any W_7b7d4 = Some (Branch BC_NE 6 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7d8 : bv 32 := 0x0003ae83.
Lemma F_7b7d8 : fetch_word Plain.M.loaded_segments (0x7b830 : word) = Some W_7b7d8.
Proof. vm_refl. Qed.
Lemma D_7b7d8 : decode_any W_7b7d8 = Some (Load SZ4 true 29 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7dc : bv 32 := 0x00be7e33.
Lemma F_7b7dc : fetch_word Plain.M.loaded_segments (0x7b834 : word) = Some W_7b7dc.
Proof. vm_refl. Qed.
Lemma D_7b7dc : decode_any W_7b7dc = Some (Op ALU_AND 28 28 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7e0 : bv 32 := 0x010edebb.
Lemma F_7b7e0 : fetch_word Plain.M.loaded_segments (0x7b838 : word) = Some W_7b7e0.
Proof. vm_refl. Qed.
Lemma D_7b7e0 : decode_any W_7b7e0 = Some (Op32 ALU_SRL 29 29 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7e4 : bv 32 := 0x011efeb3.
Lemma F_7b7e4 : fetch_word Plain.M.loaded_segments (0x7b83c : word) = Some W_7b7e4.
Proof. vm_refl. Qed.
Lemma D_7b7e4 : decode_any W_7b7e4 = Some (Op ALU_AND 29 29 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7e8 : bv 32 := 0x01ceee33.
Lemma F_7b7e8 : fetch_word Plain.M.loaded_segments (0x7b840 : word) = Some W_7b7e8.
Proof. vm_refl. Qed.
Lemma D_7b7e8 : decode_any W_7b7e8 = Some (Op ALU_OR 28 29 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7ec : bv 32 := 0xfc1ff06f.
Lemma F_7b7ec : fetch_word Plain.M.loaded_segments (0x7b844 : word) = Some W_7b7ec.
Proof. vm_refl. Qed.
Lemma D_7b7ec : decode_any W_7b7ec = Some (Jal 0 2097088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c544 : bv 32 := 0x00000513.
Lemma F_7c544 : fetch_word Plain.M.loaded_segments (0x7c59c : word) = Some W_7c544.
Proof. vm_refl. Qed.
Lemma D_7c544 : decode_any W_7c544 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c548 : bv 32 := 0x00000593.
Lemma F_7c548 : fetch_word Plain.M.loaded_segments (0x7c5a0 : word) = Some W_7c548.
Proof. vm_refl. Qed.
Lemma D_7c548 : decode_any W_7c548 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c54c : bv 32 := 0xfff8c413.
Lemma F_7c54c : fetch_word Plain.M.loaded_segments (0x7c5a4 : word) = Some W_7c54c.
Proof. vm_refl. Qed.
Lemma D_7c54c : decode_any W_7c54c = Some (OpImm ALU_XOR 8 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c550 : bv 32 := 0x00271913.
Lemma F_7c550 : fetch_word Plain.M.loaded_segments (0x7c5a8 : word) = Some W_7c550.
Proof. vm_refl. Qed.
Lemma D_7c550 : decode_any W_7c550 = Some (ShiftImm ALU_SLL 18 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c554 : bv 32 := 0x00448493.
Lemma F_7c554 : fetch_word Plain.M.loaded_segments (0x7c5ac : word) = Some W_7c554.
Proof. vm_refl. Qed.
Lemma D_7c554 : decode_any W_7c554 = Some (OpImm ALU_ADD 9 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c558 : bv 32 := 0x00269993.
Lemma F_7c558 : fetch_word Plain.M.loaded_segments (0x7c5b0 : word) = Some W_7c558.
Proof. vm_refl. Qed.
Lemma D_7c558 : decode_any W_7c558 = Some (ShiftImm ALU_SLL 19 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c55c : bv 32 := 0x002e1a13.
Lemma F_7c55c : fetch_word Plain.M.loaded_segments (0x7c5b4 : word) = Some W_7c55c.
Proof. vm_refl. Qed.
Lemma D_7c55c : decode_any W_7c55c = Some (ShiftImm ALU_SLL 20 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c560 : bv 32 := 0x000e8a93.
Lemma F_7c560 : fetch_word Plain.M.loaded_segments (0x7c5b8 : word) = Some W_7c560.
Proof. vm_refl. Qed.
Lemma D_7c560 : decode_any W_7c560 = Some (OpImm ALU_ADD 21 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c564 : bv 32 := 0x0180006f.
Lemma F_7c564 : fetch_word Plain.M.loaded_segments (0x7c5bc : word) = Some W_7c564.
Proof. vm_refl. Qed.
Lemma D_7c564 : decode_any W_7c564 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c568 : bv 32 := 0x0015859b.
Lemma F_7c568 : fetch_word Plain.M.loaded_segments (0x7c5c0 : word) = Some W_7c568.
Proof. vm_refl. Qed.
Lemma D_7c568 : decode_any W_7c568 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c56c : bv 32 := 0x012a8ab3.
Lemma F_7c56c : fetch_word Plain.M.loaded_segments (0x7c5c4 : word) = Some W_7c56c.
Proof. vm_refl. Qed.
Lemma D_7c56c : decode_any W_7c56c = Some (Op ALU_ADD 21 21 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c570 : bv 32 := 0x013484b3.
Lemma F_7c570 : fetch_word Plain.M.loaded_segments (0x7c5c8 : word) = Some W_7c570.
Proof. vm_refl. Qed.
Lemma D_7c570 : decode_any W_7c570 = Some (Op ALU_ADD 9 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c574 : bv 32 := 0x00150513.
Lemma F_7c574 : fetch_word Plain.M.loaded_segments (0x7c5cc : word) = Some W_7c574.
Proof. vm_refl. Qed.
Lemma D_7c574 : decode_any W_7c574 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c578 : bv 32 := 0xa0c58863.
Lemma F_7c578 : fetch_word Plain.M.loaded_segments (0x7c5d0 : word) = Some W_7c578.
Proof. vm_refl. Qed.
Lemma D_7c578 : decode_any W_7c578 = Some (Branch BC_EQ 11 12 4624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c57c : bv 32 := 0xfe0e06e3.
Lemma F_7c57c : fetch_word Plain.M.loaded_segments (0x7c5d4 : word) = Some W_7c57c.
Proof. vm_refl. Qed.
Lemma D_7c57c : decode_any W_7c57c = Some (Branch BC_EQ 28 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c580 : bv 32 := 0x02a903b3.
Lemma F_7c580 : fetch_word Plain.M.loaded_segments (0x7c5d8 : word) = Some W_7c580.
Proof. vm_refl. Qed.
Lemma D_7c580 : decode_any W_7c580 = Some (Mul M_MUL 7 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c584 : bv 32 := 0x007a03b3.
Lemma F_7c584 : fetch_word Plain.M.loaded_segments (0x7c5dc : word) = Some W_7c584.
Proof. vm_refl. Qed.
Lemma D_7c584 : decode_any W_7c584 = Some (Op ALU_ADD 7 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c588 : bv 32 := 0x007e83b3.
Lemma F_7c588 : fetch_word Plain.M.loaded_segments (0x7c5e0 : word) = Some W_7c588.
Proof. vm_refl. Qed.
Lemma D_7c588 : decode_any W_7c588 = Some (Op ALU_ADD 7 29 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c58c : bv 32 := 0x00048b13.
Lemma F_7c58c : fetch_word Plain.M.loaded_segments (0x7c5e4 : word) = Some W_7c58c.
Proof. vm_refl. Qed.
Lemma D_7c58c : decode_any W_7c58c = Some (OpImm ALU_ADD 22 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c590 : bv 32 := 0x000a8b93.
Lemma F_7c590 : fetch_word Plain.M.loaded_segments (0x7c5e8 : word) = Some W_7c590.
Proof. vm_refl. Qed.
Lemma D_7c590 : decode_any W_7c590 = Some (OpImm ALU_ADD 23 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c594 : bv 32 := 0xffcb2f83.
Lemma F_7c594 : fetch_word Plain.M.loaded_segments (0x7c5ec : word) = Some W_7c594.
Proof. vm_refl. Qed.
Lemma D_7c594 : decode_any W_7c594 = Some (Load SZ4 true 31 22 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c598 : bv 32 := 0x000b2c03.
Lemma F_7c598 : fetch_word Plain.M.loaded_segments (0x7c5f0 : word) = Some W_7c598.
Proof. vm_refl. Qed.
Lemma D_7c598 : decode_any W_7c598 = Some (Load SZ4 true 24 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c59c : bv 32 := 0x000bac83.
Lemma F_7c59c : fetch_word Plain.M.loaded_segments (0x7c5f4 : word) = Some W_7c59c.
Proof. vm_refl. Qed.
Lemma D_7c59c : decode_any W_7c59c = Some (Load SZ4 true 25 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5a0 : bv 32 := 0x00ff9fbb.
Lemma F_7c5a0 : fetch_word Plain.M.loaded_segments (0x7c5f8 : word) = Some W_7c5a0.
Proof. vm_refl. Qed.
Lemma D_7c5a0 : decode_any W_7c5a0 = Some (Op32 ALU_SLL 31 31 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5a4 : bv 32 := 0x010c5c3b.
Lemma F_7c5a4 : fetch_word Plain.M.loaded_segments (0x7c5fc : word) = Some W_7c5a4.
Proof. vm_refl. Qed.
Lemma D_7c5a4 : decode_any W_7c5a4 = Some (Op32 ALU_SRL 24 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5a8 : bv 32 := 0x008fffb3.
Lemma F_7c5a8 : fetch_word Plain.M.loaded_segments (0x7c600 : word) = Some W_7c5a8.
Proof. vm_refl. Qed.
Lemma D_7c5a8 : decode_any W_7c5a8 = Some (Op ALU_AND 31 31 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5ac : bv 32 := 0x011c7c33.
Lemma F_7c5ac : fetch_word Plain.M.loaded_segments (0x7c604 : word) = Some W_7c5ac.
Proof. vm_refl. Qed.
Lemma D_7c5ac : decode_any W_7c5ac = Some (Op ALU_AND 24 24 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5b0 : bv 32 := 0x01fc6fb3.
Lemma F_7c5b0 : fetch_word Plain.M.loaded_segments (0x7c608 : word) = Some W_7c5b0.
Proof. vm_refl. Qed.
Lemma D_7c5b0 : decode_any W_7c5b0 = Some (Op ALU_OR 31 24 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5b4 : bv 32 := 0x019fffb3.
Lemma F_7c5b4 : fetch_word Plain.M.loaded_segments (0x7c60c : word) = Some W_7c5b4.
Proof. vm_refl. Qed.
Lemma D_7c5b4 : decode_any W_7c5b4 = Some (Op ALU_AND 31 31 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5b8 : bv 32 := 0x01fba023.
Lemma F_7c5b8 : fetch_word Plain.M.loaded_segments (0x7c610 : word) = Some W_7c5b8.
Proof. vm_refl. Qed.
Lemma D_7c5b8 : decode_any W_7c5b8 = Some (Store SZ4 23 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5bc : bv 32 := 0x004b8b93.
Lemma F_7c5bc : fetch_word Plain.M.loaded_segments (0x7c614 : word) = Some W_7c5bc.
Proof. vm_refl. Qed.
Lemma D_7c5bc : decode_any W_7c5bc = Some (OpImm ALU_ADD 23 23 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5c0 : bv 32 := 0x004b0b13.
Lemma F_7c5c0 : fetch_word Plain.M.loaded_segments (0x7c618 : word) = Some W_7c5c0.
Proof. vm_refl. Qed.
Lemma D_7c5c0 : decode_any W_7c5c0 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5c4 : bv 32 := 0xfc7b98e3.
Lemma F_7c5c4 : fetch_word Plain.M.loaded_segments (0x7c61c : word) = Some W_7c5c4.
Proof. vm_refl. Qed.
Lemma D_7c5c4 : decode_any W_7c5c4 = Some (Branch BC_NE 23 7 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c5c8 : bv 32 := 0xfa1ff06f.
Lemma F_7c5c8 : fetch_word Plain.M.loaded_segments (0x7c620 : word) = Some W_7c5c8.
Proof. vm_refl. Qed.
Lemma D_7c5c8 : decode_any W_7c5c8 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

