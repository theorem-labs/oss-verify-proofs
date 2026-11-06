(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.punycode.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_52a484 : bv 32 := 0x0035f693.
Lemma F_52a484 : fetch_word Asan.M.loaded_segments (0x52a4b8 : word) = Some W_52a484.
Proof. vm_refl. Qed.
Lemma D_52a484 : decode_any W_52a484 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a488 : bv 32 := 0x10068863.
Lemma F_52a488 : fetch_word Asan.M.loaded_segments (0x52a4bc : word) = Some W_52a488.
Proof. vm_refl. Qed.
Lemma D_52a488 : decode_any W_52a488 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a48c : bv 32 := 0x02060e63.
Lemma F_52a48c : fetch_word Asan.M.loaded_segments (0x52a4c0 : word) = Some W_52a48c.
Proof. vm_refl. Qed.
Lemma D_52a48c : decode_any W_52a48c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a490 : bv 32 := 0x00158713.
Lemma F_52a490 : fetch_word Asan.M.loaded_segments (0x52a4c4 : word) = Some W_52a490.
Proof. vm_refl. Qed.
Lemma D_52a490 : decode_any W_52a490 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a494 : bv 32 := 0x00100793.
Lemma F_52a494 : fetch_word Asan.M.loaded_segments (0x52a4c8 : word) = Some W_52a494.
Proof. vm_refl. Qed.
Lemma D_52a494 : decode_any W_52a494 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a498 : bv 32 := 0x00050693.
Lemma F_52a498 : fetch_word Asan.M.loaded_segments (0x52a4cc : word) = Some W_52a498.
Proof. vm_refl. Qed.
Lemma D_52a498 : decode_any W_52a498 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a49c : bv 32 := 0x0005c883.
Lemma F_52a49c : fetch_word Asan.M.loaded_segments (0x52a4d0 : word) = Some W_52a49c.
Proof. vm_refl. Qed.
Lemma D_52a49c : decode_any W_52a49c = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4a0 : bv 32 := 0x00060813.
Lemma F_52a4a0 : fetch_word Asan.M.loaded_segments (0x52a4d4 : word) = Some W_52a4a0.
Proof. vm_refl. Qed.
Lemma D_52a4a0 : decode_any W_52a4a0 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4a4 : bv 32 := 0x00158593.
Lemma F_52a4a4 : fetch_word Asan.M.loaded_segments (0x52a4d8 : word) = Some W_52a4a4.
Proof. vm_refl. Qed.
Lemma D_52a4a4 : decode_any W_52a4a4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4a8 : bv 32 := 0x00377293.
Lemma F_52a4a8 : fetch_word Asan.M.loaded_segments (0x52a4dc : word) = Some W_52a4a8.
Proof. vm_refl. Qed.
Lemma D_52a4a8 : decode_any W_52a4a8 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4ac : bv 32 := 0x01168023.
Lemma F_52a4ac : fetch_word Asan.M.loaded_segments (0x52a4e0 : word) = Some W_52a4ac.
Proof. vm_refl. Qed.
Lemma D_52a4ac : decode_any W_52a4ac = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4b0 : bv 32 := 0x00168693.
Lemma F_52a4b0 : fetch_word Asan.M.loaded_segments (0x52a4e4 : word) = Some W_52a4b0.
Proof. vm_refl. Qed.
Lemma D_52a4b0 : decode_any W_52a4b0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4b4 : bv 32 := 0xfff60613.
Lemma F_52a4b4 : fetch_word Asan.M.loaded_segments (0x52a4e8 : word) = Some W_52a4b4.
Proof. vm_refl. Qed.
Lemma D_52a4b4 : decode_any W_52a4b4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4b8 : bv 32 := 0x00028a63.
Lemma F_52a4b8 : fetch_word Asan.M.loaded_segments (0x52a4ec : word) = Some W_52a4b8.
Proof. vm_refl. Qed.
Lemma D_52a4b8 : decode_any W_52a4b8 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4bc : bv 32 := 0x00170713.
Lemma F_52a4bc : fetch_word Asan.M.loaded_segments (0x52a4f0 : word) = Some W_52a4bc.
Proof. vm_refl. Qed.
Lemma D_52a4bc : decode_any W_52a4bc = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4c0 : bv 32 := 0xfcf81ee3.
Lemma F_52a4c0 : fetch_word Asan.M.loaded_segments (0x52a4f4 : word) = Some W_52a4c0.
Proof. vm_refl. Qed.
Lemma D_52a4c0 : decode_any W_52a4c0 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4c4 : bv 32 := 0x0080006f.
Lemma F_52a4c4 : fetch_word Asan.M.loaded_segments (0x52a4f8 : word) = Some W_52a4c4.
Proof. vm_refl. Qed.
Lemma D_52a4c4 : decode_any W_52a4c4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4c8 : bv 32 := 0x00050693.
Lemma F_52a4c8 : fetch_word Asan.M.loaded_segments (0x52a4fc : word) = Some W_52a4c8.
Proof. vm_refl. Qed.
Lemma D_52a4c8 : decode_any W_52a4c8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4cc : bv 32 := 0x0036f793.
Lemma F_52a4cc : fetch_word Asan.M.loaded_segments (0x52a500 : word) = Some W_52a4cc.
Proof. vm_refl. Qed.
Lemma D_52a4cc : decode_any W_52a4cc = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4d0 : bv 32 := 0x0c078a63.
Lemma F_52a4d0 : fetch_word Asan.M.loaded_segments (0x52a504 : word) = Some W_52a4d0.
Proof. vm_refl. Qed.
Lemma D_52a4d0 : decode_any W_52a4d0 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4d4 : bv 32 := 0x02000713.
Lemma F_52a4d4 : fetch_word Asan.M.loaded_segments (0x52a508 : word) = Some W_52a4d4.
Proof. vm_refl. Qed.
Lemma D_52a4d4 : decode_any W_52a4d4 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4d8 : bv 32 := 0x02e67063.
Lemma F_52a4d8 : fetch_word Asan.M.loaded_segments (0x52a50c : word) = Some W_52a4d8.
Proof. vm_refl. Qed.
Lemma D_52a4d8 : decode_any W_52a4d8 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4dc : bv 32 := 0x01000713.
Lemma F_52a4dc : fetch_word Asan.M.loaded_segments (0x52a510 : word) = Some W_52a4dc.
Proof. vm_refl. Qed.
Lemma D_52a4dc : decode_any W_52a4dc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4e0 : bv 32 := 0x24e67863.
Lemma F_52a4e0 : fetch_word Asan.M.loaded_segments (0x52a514 : word) = Some W_52a4e0.
Proof. vm_refl. Qed.
Lemma D_52a4e0 : decode_any W_52a4e0 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4e4 : bv 32 := 0x00867713.
Lemma F_52a4e4 : fetch_word Asan.M.loaded_segments (0x52a518 : word) = Some W_52a4e4.
Proof. vm_refl. Qed.
Lemma D_52a4e4 : decode_any W_52a4e4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4e8 : bv 32 := 0x2c071e63.
Lemma F_52a4e8 : fetch_word Asan.M.loaded_segments (0x52a51c : word) = Some W_52a4e8.
Proof. vm_refl. Qed.
Lemma D_52a4e8 : decode_any W_52a4e8 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4ec : bv 32 := 0x00467713.
Lemma F_52a4ec : fetch_word Asan.M.loaded_segments (0x52a520 : word) = Some W_52a4ec.
Proof. vm_refl. Qed.
Lemma D_52a4ec : decode_any W_52a4ec = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4f0 : bv 32 := 0x32071463.
Lemma F_52a4f0 : fetch_word Asan.M.loaded_segments (0x52a524 : word) = Some W_52a4f0.
Proof. vm_refl. Qed.
Lemma D_52a4f0 : decode_any W_52a4f0 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4f4 : bv 32 := 0x3500006f.
Lemma F_52a4f4 : fetch_word Asan.M.loaded_segments (0x52a528 : word) = Some W_52a4f4.
Proof. vm_refl. Qed.
Lemma D_52a4f4 : decode_any W_52a4f4 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4f8 : bv 32 := 0x0005a703.
Lemma F_52a4f8 : fetch_word Asan.M.loaded_segments (0x52a52c : word) = Some W_52a4f8.
Proof. vm_refl. Qed.
Lemma D_52a4f8 : decode_any W_52a4f8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a4fc : bv 32 := 0x00300813.
Lemma F_52a4fc : fetch_word Asan.M.loaded_segments (0x52a530 : word) = Some W_52a4fc.
Proof. vm_refl. Qed.
Lemma D_52a4fc : decode_any W_52a4fc = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a500 : bv 32 := 0x11078e63.
Lemma F_52a500 : fetch_word Asan.M.loaded_segments (0x52a534 : word) = Some W_52a500.
Proof. vm_refl. Qed.
Lemma D_52a500 : decode_any W_52a500 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a504 : bv 32 := 0x00200813.
Lemma F_52a504 : fetch_word Asan.M.loaded_segments (0x52a538 : word) = Some W_52a504.
Proof. vm_refl. Qed.
Lemma D_52a504 : decode_any W_52a504 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a508 : bv 32 := 0x19079c63.
Lemma F_52a508 : fetch_word Asan.M.loaded_segments (0x52a53c : word) = Some W_52a508.
Proof. vm_refl. Qed.
Lemma D_52a508 : decode_any W_52a508 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a50c : bv 32 := 0x00875793.
Lemma F_52a50c : fetch_word Asan.M.loaded_segments (0x52a540 : word) = Some W_52a50c.
Proof. vm_refl. Qed.
Lemma D_52a50c : decode_any W_52a50c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a510 : bv 32 := 0xffe60613.
Lemma F_52a510 : fetch_word Asan.M.loaded_segments (0x52a544 : word) = Some W_52a510.
Proof. vm_refl. Qed.
Lemma D_52a510 : decode_any W_52a510 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a514 : bv 32 := 0x00e68023.
Lemma F_52a514 : fetch_word Asan.M.loaded_segments (0x52a548 : word) = Some W_52a514.
Proof. vm_refl. Qed.
Lemma D_52a514 : decode_any W_52a514 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a518 : bv 32 := 0x00f680a3.
Lemma F_52a518 : fetch_word Asan.M.loaded_segments (0x52a54c : word) = Some W_52a518.
Proof. vm_refl. Qed.
Lemma D_52a518 : decode_any W_52a518 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a51c : bv 32 := 0x00268693.
Lemma F_52a51c : fetch_word Asan.M.loaded_segments (0x52a550 : word) = Some W_52a51c.
Proof. vm_refl. Qed.
Lemma D_52a51c : decode_any W_52a51c = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a520 : bv 32 := 0x01058593.
Lemma F_52a520 : fetch_word Asan.M.loaded_segments (0x52a554 : word) = Some W_52a520.
Proof. vm_refl. Qed.
Lemma D_52a520 : decode_any W_52a520 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a524 : bv 32 := 0x01100793.
Lemma F_52a524 : fetch_word Asan.M.loaded_segments (0x52a558 : word) = Some W_52a524.
Proof. vm_refl. Qed.
Lemma D_52a524 : decode_any W_52a524 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a528 : bv 32 := 0x0107581b.
Lemma F_52a528 : fetch_word Asan.M.loaded_segments (0x52a55c : word) = Some W_52a528.
Proof. vm_refl. Qed.
Lemma D_52a528 : decode_any W_52a528 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a52c : bv 32 := 0xff45a883.
Lemma F_52a52c : fetch_word Asan.M.loaded_segments (0x52a560 : word) = Some W_52a52c.
Proof. vm_refl. Qed.
Lemma D_52a52c : decode_any W_52a52c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a530 : bv 32 := 0xff85a283.
Lemma F_52a530 : fetch_word Asan.M.loaded_segments (0x52a564 : word) = Some W_52a530.
Proof. vm_refl. Qed.
Lemma D_52a530 : decode_any W_52a530 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a534 : bv 32 := 0xffc5a303.
Lemma F_52a534 : fetch_word Asan.M.loaded_segments (0x52a568 : word) = Some W_52a534.
Proof. vm_refl. Qed.
Lemma D_52a534 : decode_any W_52a534 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a538 : bv 32 := 0x0005a703.
Lemma F_52a538 : fetch_word Asan.M.loaded_segments (0x52a56c : word) = Some W_52a538.
Proof. vm_refl. Qed.
Lemma D_52a538 : decode_any W_52a538 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a53c : bv 32 := 0x01089393.
Lemma F_52a53c : fetch_word Asan.M.loaded_segments (0x52a570 : word) = Some W_52a53c.
Proof. vm_refl. Qed.
Lemma D_52a53c : decode_any W_52a53c = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a540 : bv 32 := 0x0108d89b.
Lemma F_52a540 : fetch_word Asan.M.loaded_segments (0x52a574 : word) = Some W_52a540.
Proof. vm_refl. Qed.
Lemma D_52a540 : decode_any W_52a540 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a544 : bv 32 := 0x0103e833.
Lemma F_52a544 : fetch_word Asan.M.loaded_segments (0x52a578 : word) = Some W_52a544.
Proof. vm_refl. Qed.
Lemma D_52a544 : decode_any W_52a544 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a548 : bv 32 := 0x01029393.
Lemma F_52a548 : fetch_word Asan.M.loaded_segments (0x52a57c : word) = Some W_52a548.
Proof. vm_refl. Qed.
Lemma D_52a548 : decode_any W_52a548 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a54c : bv 32 := 0x0102d29b.
Lemma F_52a54c : fetch_word Asan.M.loaded_segments (0x52a580 : word) = Some W_52a54c.
Proof. vm_refl. Qed.
Lemma D_52a54c : decode_any W_52a54c = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a550 : bv 32 := 0x0113e8b3.
Lemma F_52a550 : fetch_word Asan.M.loaded_segments (0x52a584 : word) = Some W_52a550.
Proof. vm_refl. Qed.
Lemma D_52a550 : decode_any W_52a550 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a554 : bv 32 := 0x01031393.
Lemma F_52a554 : fetch_word Asan.M.loaded_segments (0x52a588 : word) = Some W_52a554.
Proof. vm_refl. Qed.
Lemma D_52a554 : decode_any W_52a554 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a558 : bv 32 := 0x0103531b.
Lemma F_52a558 : fetch_word Asan.M.loaded_segments (0x52a58c : word) = Some W_52a558.
Proof. vm_refl. Qed.
Lemma D_52a558 : decode_any W_52a558 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a55c : bv 32 := 0x0053e2b3.
Lemma F_52a55c : fetch_word Asan.M.loaded_segments (0x52a590 : word) = Some W_52a55c.
Proof. vm_refl. Qed.
Lemma D_52a55c : decode_any W_52a55c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a560 : bv 32 := 0x01071393.
Lemma F_52a560 : fetch_word Asan.M.loaded_segments (0x52a594 : word) = Some W_52a560.
Proof. vm_refl. Qed.
Lemma D_52a560 : decode_any W_52a560 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a564 : bv 32 := 0x0063e333.
Lemma F_52a564 : fetch_word Asan.M.loaded_segments (0x52a598 : word) = Some W_52a564.
Proof. vm_refl. Qed.
Lemma D_52a564 : decode_any W_52a564 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a568 : bv 32 := 0xff060613.
Lemma F_52a568 : fetch_word Asan.M.loaded_segments (0x52a59c : word) = Some W_52a568.
Proof. vm_refl. Qed.
Lemma D_52a568 : decode_any W_52a568 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a56c : bv 32 := 0x0106a023.
Lemma F_52a56c : fetch_word Asan.M.loaded_segments (0x52a5a0 : word) = Some W_52a56c.
Proof. vm_refl. Qed.
Lemma D_52a56c : decode_any W_52a56c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a570 : bv 32 := 0x0116a223.
Lemma F_52a570 : fetch_word Asan.M.loaded_segments (0x52a5a4 : word) = Some W_52a570.
Proof. vm_refl. Qed.
Lemma D_52a570 : decode_any W_52a570 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a574 : bv 32 := 0x0056a423.
Lemma F_52a574 : fetch_word Asan.M.loaded_segments (0x52a5a8 : word) = Some W_52a574.
Proof. vm_refl. Qed.
Lemma D_52a574 : decode_any W_52a574 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a578 : bv 32 := 0x0066a623.
Lemma F_52a578 : fetch_word Asan.M.loaded_segments (0x52a5ac : word) = Some W_52a578.
Proof. vm_refl. Qed.
Lemma D_52a578 : decode_any W_52a578 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a57c : bv 32 := 0x01068693.
Lemma F_52a57c : fetch_word Asan.M.loaded_segments (0x52a5b0 : word) = Some W_52a57c.
Proof. vm_refl. Qed.
Lemma D_52a57c : decode_any W_52a57c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a580 : bv 32 := 0x01058593.
Lemma F_52a580 : fetch_word Asan.M.loaded_segments (0x52a5b4 : word) = Some W_52a580.
Proof. vm_refl. Qed.
Lemma D_52a580 : decode_any W_52a580 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a584 : bv 32 := 0xfac7e2e3.
Lemma F_52a584 : fetch_word Asan.M.loaded_segments (0x52a5b8 : word) = Some W_52a584.
Proof. vm_refl. Qed.
Lemma D_52a584 : decode_any W_52a584 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a588 : bv 32 := 0xff258593.
Lemma F_52a588 : fetch_word Asan.M.loaded_segments (0x52a5bc : word) = Some W_52a588.
Proof. vm_refl. Qed.
Lemma D_52a588 : decode_any W_52a588 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a58c : bv 32 := 0x01000713.
Lemma F_52a58c : fetch_word Asan.M.loaded_segments (0x52a5c0 : word) = Some W_52a58c.
Proof. vm_refl. Qed.
Lemma D_52a58c : decode_any W_52a58c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a590 : bv 32 := 0xf4e66ae3.
Lemma F_52a590 : fetch_word Asan.M.loaded_segments (0x52a5c4 : word) = Some W_52a590.
Proof. vm_refl. Qed.
Lemma D_52a590 : decode_any W_52a590 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a594 : bv 32 := 0x19c0006f.
Lemma F_52a594 : fetch_word Asan.M.loaded_segments (0x52a5c8 : word) = Some W_52a594.
Proof. vm_refl. Qed.
Lemma D_52a594 : decode_any W_52a594 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a598 : bv 32 := 0x00050693.
Lemma F_52a598 : fetch_word Asan.M.loaded_segments (0x52a5cc : word) = Some W_52a598.
Proof. vm_refl. Qed.
Lemma D_52a598 : decode_any W_52a598 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a59c : bv 32 := 0x00357793.
Lemma F_52a59c : fetch_word Asan.M.loaded_segments (0x52a5d0 : word) = Some W_52a59c.
Proof. vm_refl. Qed.
Lemma D_52a59c : decode_any W_52a59c = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5a0 : bv 32 := 0xf2079ae3.
Lemma F_52a5a0 : fetch_word Asan.M.loaded_segments (0x52a5d4 : word) = Some W_52a5a0.
Proof. vm_refl. Qed.
Lemma D_52a5a0 : decode_any W_52a5a0 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5a4 : bv 32 := 0x01000713.
Lemma F_52a5a4 : fetch_word Asan.M.loaded_segments (0x52a5d8 : word) = Some W_52a5a4.
Proof. vm_refl. Qed.
Lemma D_52a5a4 : decode_any W_52a5a4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5a8 : bv 32 := 0x02e66c63.
Lemma F_52a5a8 : fetch_word Asan.M.loaded_segments (0x52a5dc : word) = Some W_52a5a8.
Proof. vm_refl. Qed.
Lemma D_52a5a8 : decode_any W_52a5a8 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5ac : bv 32 := 0x00f00713.
Lemma F_52a5ac : fetch_word Asan.M.loaded_segments (0x52a5e0 : word) = Some W_52a5ac.
Proof. vm_refl. Qed.
Lemma D_52a5ac : decode_any W_52a5ac = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5b0 : bv 32 := 0x0005a783.
Lemma F_52a5b0 : fetch_word Asan.M.loaded_segments (0x52a5e4 : word) = Some W_52a5b0.
Proof. vm_refl. Qed.
Lemma D_52a5b0 : decode_any W_52a5b0 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5b4 : bv 32 := 0x0045a803.
Lemma F_52a5b4 : fetch_word Asan.M.loaded_segments (0x52a5e8 : word) = Some W_52a5b4.
Proof. vm_refl. Qed.
Lemma D_52a5b4 : decode_any W_52a5b4 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5b8 : bv 32 := 0x0085a883.
Lemma F_52a5b8 : fetch_word Asan.M.loaded_segments (0x52a5ec : word) = Some W_52a5b8.
Proof. vm_refl. Qed.
Lemma D_52a5b8 : decode_any W_52a5b8 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5bc : bv 32 := 0x00c5a283.
Lemma F_52a5bc : fetch_word Asan.M.loaded_segments (0x52a5f0 : word) = Some W_52a5bc.
Proof. vm_refl. Qed.
Lemma D_52a5bc : decode_any W_52a5bc = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5c0 : bv 32 := 0x01058593.
Lemma F_52a5c0 : fetch_word Asan.M.loaded_segments (0x52a5f4 : word) = Some W_52a5c0.
Proof. vm_refl. Qed.
Lemma D_52a5c0 : decode_any W_52a5c0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5c4 : bv 32 := 0xff060613.
Lemma F_52a5c4 : fetch_word Asan.M.loaded_segments (0x52a5f8 : word) = Some W_52a5c4.
Proof. vm_refl. Qed.
Lemma D_52a5c4 : decode_any W_52a5c4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5c8 : bv 32 := 0x00f6a023.
Lemma F_52a5c8 : fetch_word Asan.M.loaded_segments (0x52a5fc : word) = Some W_52a5c8.
Proof. vm_refl. Qed.
Lemma D_52a5c8 : decode_any W_52a5c8 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5cc : bv 32 := 0x0106a223.
Lemma F_52a5cc : fetch_word Asan.M.loaded_segments (0x52a600 : word) = Some W_52a5cc.
Proof. vm_refl. Qed.
Lemma D_52a5cc : decode_any W_52a5cc = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5d0 : bv 32 := 0x0116a423.
Lemma F_52a5d0 : fetch_word Asan.M.loaded_segments (0x52a604 : word) = Some W_52a5d0.
Proof. vm_refl. Qed.
Lemma D_52a5d0 : decode_any W_52a5d0 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5d4 : bv 32 := 0x0056a623.
Lemma F_52a5d4 : fetch_word Asan.M.loaded_segments (0x52a608 : word) = Some W_52a5d4.
Proof. vm_refl. Qed.
Lemma D_52a5d4 : decode_any W_52a5d4 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5d8 : bv 32 := 0x01068693.
Lemma F_52a5d8 : fetch_word Asan.M.loaded_segments (0x52a60c : word) = Some W_52a5d8.
Proof. vm_refl. Qed.
Lemma D_52a5d8 : decode_any W_52a5d8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5dc : bv 32 := 0xfcc76ae3.
Lemma F_52a5dc : fetch_word Asan.M.loaded_segments (0x52a610 : word) = Some W_52a5dc.
Proof. vm_refl. Qed.
Lemma D_52a5dc : decode_any W_52a5dc = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5e0 : bv 32 := 0x00800713.
Lemma F_52a5e0 : fetch_word Asan.M.loaded_segments (0x52a614 : word) = Some W_52a5e0.
Proof. vm_refl. Qed.
Lemma D_52a5e0 : decode_any W_52a5e0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5e4 : bv 32 := 0x00e66e63.
Lemma F_52a5e4 : fetch_word Asan.M.loaded_segments (0x52a618 : word) = Some W_52a5e4.
Proof. vm_refl. Qed.
Lemma D_52a5e4 : decode_any W_52a5e4 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5e8 : bv 32 := 0x0005a703.
Lemma F_52a5e8 : fetch_word Asan.M.loaded_segments (0x52a61c : word) = Some W_52a5e8.
Proof. vm_refl. Qed.
Lemma D_52a5e8 : decode_any W_52a5e8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5ec : bv 32 := 0x0045a783.
Lemma F_52a5ec : fetch_word Asan.M.loaded_segments (0x52a620 : word) = Some W_52a5ec.
Proof. vm_refl. Qed.
Lemma D_52a5ec : decode_any W_52a5ec = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5f0 : bv 32 := 0x00e6a023.
Lemma F_52a5f0 : fetch_word Asan.M.loaded_segments (0x52a624 : word) = Some W_52a5f0.
Proof. vm_refl. Qed.
Lemma D_52a5f0 : decode_any W_52a5f0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5f4 : bv 32 := 0x00f6a223.
Lemma F_52a5f4 : fetch_word Asan.M.loaded_segments (0x52a628 : word) = Some W_52a5f4.
Proof. vm_refl. Qed.
Lemma D_52a5f4 : decode_any W_52a5f4 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5f8 : bv 32 := 0x00868693.
Lemma F_52a5f8 : fetch_word Asan.M.loaded_segments (0x52a62c : word) = Some W_52a5f8.
Proof. vm_refl. Qed.
Lemma D_52a5f8 : decode_any W_52a5f8 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a5fc : bv 32 := 0x00858593.
Lemma F_52a5fc : fetch_word Asan.M.loaded_segments (0x52a630 : word) = Some W_52a5fc.
Proof. vm_refl. Qed.
Lemma D_52a5fc : decode_any W_52a5fc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a600 : bv 32 := 0x00467713.
Lemma F_52a600 : fetch_word Asan.M.loaded_segments (0x52a634 : word) = Some W_52a600.
Proof. vm_refl. Qed.
Lemma D_52a600 : decode_any W_52a600 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a604 : bv 32 := 0x24070063.
Lemma F_52a604 : fetch_word Asan.M.loaded_segments (0x52a638 : word) = Some W_52a604.
Proof. vm_refl. Qed.
Lemma D_52a604 : decode_any W_52a604 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a608 : bv 32 := 0x0005a703.
Lemma F_52a608 : fetch_word Asan.M.loaded_segments (0x52a63c : word) = Some W_52a608.
Proof. vm_refl. Qed.
Lemma D_52a608 : decode_any W_52a608 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a60c : bv 32 := 0x00458593.
Lemma F_52a60c : fetch_word Asan.M.loaded_segments (0x52a640 : word) = Some W_52a60c.
Proof. vm_refl. Qed.
Lemma D_52a60c : decode_any W_52a60c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a610 : bv 32 := 0x00e6a023.
Lemma F_52a610 : fetch_word Asan.M.loaded_segments (0x52a644 : word) = Some W_52a610.
Proof. vm_refl. Qed.
Lemma D_52a610 : decode_any W_52a610 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a614 : bv 32 := 0x00468693.
Lemma F_52a614 : fetch_word Asan.M.loaded_segments (0x52a648 : word) = Some W_52a614.
Proof. vm_refl. Qed.
Lemma D_52a614 : decode_any W_52a614 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a618 : bv 32 := 0x22c0006f.
Lemma F_52a618 : fetch_word Asan.M.loaded_segments (0x52a64c : word) = Some W_52a618.
Proof. vm_refl. Qed.
Lemma D_52a618 : decode_any W_52a618 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a61c : bv 32 := 0x00e68023.
Lemma F_52a61c : fetch_word Asan.M.loaded_segments (0x52a650 : word) = Some W_52a61c.
Proof. vm_refl. Qed.
Lemma D_52a61c : decode_any W_52a61c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a620 : bv 32 := 0x00168693.
Lemma F_52a620 : fetch_word Asan.M.loaded_segments (0x52a654 : word) = Some W_52a620.
Proof. vm_refl. Qed.
Lemma D_52a620 : decode_any W_52a620 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a624 : bv 32 := 0xfff60613.
Lemma F_52a624 : fetch_word Asan.M.loaded_segments (0x52a658 : word) = Some W_52a624.
Proof. vm_refl. Qed.
Lemma D_52a624 : decode_any W_52a624 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a628 : bv 32 := 0x01058593.
Lemma F_52a628 : fetch_word Asan.M.loaded_segments (0x52a65c : word) = Some W_52a628.
Proof. vm_refl. Qed.
Lemma D_52a628 : decode_any W_52a628 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a62c : bv 32 := 0x01200793.
Lemma F_52a62c : fetch_word Asan.M.loaded_segments (0x52a660 : word) = Some W_52a62c.
Proof. vm_refl. Qed.
Lemma D_52a62c : decode_any W_52a62c = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a630 : bv 32 := 0x0087581b.
Lemma F_52a630 : fetch_word Asan.M.loaded_segments (0x52a664 : word) = Some W_52a630.
Proof. vm_refl. Qed.
Lemma D_52a630 : decode_any W_52a630 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a634 : bv 32 := 0xff45a883.
Lemma F_52a634 : fetch_word Asan.M.loaded_segments (0x52a668 : word) = Some W_52a634.
Proof. vm_refl. Qed.
Lemma D_52a634 : decode_any W_52a634 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a638 : bv 32 := 0xff85a283.
Lemma F_52a638 : fetch_word Asan.M.loaded_segments (0x52a66c : word) = Some W_52a638.
Proof. vm_refl. Qed.
Lemma D_52a638 : decode_any W_52a638 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a63c : bv 32 := 0xffc5a303.
Lemma F_52a63c : fetch_word Asan.M.loaded_segments (0x52a670 : word) = Some W_52a63c.
Proof. vm_refl. Qed.
Lemma D_52a63c : decode_any W_52a63c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a640 : bv 32 := 0x0005a703.
Lemma F_52a640 : fetch_word Asan.M.loaded_segments (0x52a674 : word) = Some W_52a640.
Proof. vm_refl. Qed.
Lemma D_52a640 : decode_any W_52a640 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a644 : bv 32 := 0x01889393.
Lemma F_52a644 : fetch_word Asan.M.loaded_segments (0x52a678 : word) = Some W_52a644.
Proof. vm_refl. Qed.
Lemma D_52a644 : decode_any W_52a644 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a648 : bv 32 := 0x0088d89b.
Lemma F_52a648 : fetch_word Asan.M.loaded_segments (0x52a67c : word) = Some W_52a648.
Proof. vm_refl. Qed.
Lemma D_52a648 : decode_any W_52a648 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a64c : bv 32 := 0x0103e833.
Lemma F_52a64c : fetch_word Asan.M.loaded_segments (0x52a680 : word) = Some W_52a64c.
Proof. vm_refl. Qed.
Lemma D_52a64c : decode_any W_52a64c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a650 : bv 32 := 0x01829393.
Lemma F_52a650 : fetch_word Asan.M.loaded_segments (0x52a684 : word) = Some W_52a650.
Proof. vm_refl. Qed.
Lemma D_52a650 : decode_any W_52a650 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a654 : bv 32 := 0x0082d29b.
Lemma F_52a654 : fetch_word Asan.M.loaded_segments (0x52a688 : word) = Some W_52a654.
Proof. vm_refl. Qed.
Lemma D_52a654 : decode_any W_52a654 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a658 : bv 32 := 0x0113e8b3.
Lemma F_52a658 : fetch_word Asan.M.loaded_segments (0x52a68c : word) = Some W_52a658.
Proof. vm_refl. Qed.
Lemma D_52a658 : decode_any W_52a658 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a65c : bv 32 := 0x01831393.
Lemma F_52a65c : fetch_word Asan.M.loaded_segments (0x52a690 : word) = Some W_52a65c.
Proof. vm_refl. Qed.
Lemma D_52a65c : decode_any W_52a65c = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a660 : bv 32 := 0x0083531b.
Lemma F_52a660 : fetch_word Asan.M.loaded_segments (0x52a694 : word) = Some W_52a660.
Proof. vm_refl. Qed.
Lemma D_52a660 : decode_any W_52a660 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a664 : bv 32 := 0x0053e2b3.
Lemma F_52a664 : fetch_word Asan.M.loaded_segments (0x52a698 : word) = Some W_52a664.
Proof. vm_refl. Qed.
Lemma D_52a664 : decode_any W_52a664 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a668 : bv 32 := 0x01871393.
Lemma F_52a668 : fetch_word Asan.M.loaded_segments (0x52a69c : word) = Some W_52a668.
Proof. vm_refl. Qed.
Lemma D_52a668 : decode_any W_52a668 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a66c : bv 32 := 0x0063e333.
Lemma F_52a66c : fetch_word Asan.M.loaded_segments (0x52a6a0 : word) = Some W_52a66c.
Proof. vm_refl. Qed.
Lemma D_52a66c : decode_any W_52a66c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a670 : bv 32 := 0xff060613.
Lemma F_52a670 : fetch_word Asan.M.loaded_segments (0x52a6a4 : word) = Some W_52a670.
Proof. vm_refl. Qed.
Lemma D_52a670 : decode_any W_52a670 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a674 : bv 32 := 0x0106a023.
Lemma F_52a674 : fetch_word Asan.M.loaded_segments (0x52a6a8 : word) = Some W_52a674.
Proof. vm_refl. Qed.
Lemma D_52a674 : decode_any W_52a674 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a678 : bv 32 := 0x0116a223.
Lemma F_52a678 : fetch_word Asan.M.loaded_segments (0x52a6ac : word) = Some W_52a678.
Proof. vm_refl. Qed.
Lemma D_52a678 : decode_any W_52a678 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a67c : bv 32 := 0x0056a423.
Lemma F_52a67c : fetch_word Asan.M.loaded_segments (0x52a6b0 : word) = Some W_52a67c.
Proof. vm_refl. Qed.
Lemma D_52a67c : decode_any W_52a67c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a680 : bv 32 := 0x0066a623.
Lemma F_52a680 : fetch_word Asan.M.loaded_segments (0x52a6b4 : word) = Some W_52a680.
Proof. vm_refl. Qed.
Lemma D_52a680 : decode_any W_52a680 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a684 : bv 32 := 0x01068693.
Lemma F_52a684 : fetch_word Asan.M.loaded_segments (0x52a6b8 : word) = Some W_52a684.
Proof. vm_refl. Qed.
Lemma D_52a684 : decode_any W_52a684 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a688 : bv 32 := 0x01058593.
Lemma F_52a688 : fetch_word Asan.M.loaded_segments (0x52a6bc : word) = Some W_52a688.
Proof. vm_refl. Qed.
Lemma D_52a688 : decode_any W_52a688 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a68c : bv 32 := 0xfac7e2e3.
Lemma F_52a68c : fetch_word Asan.M.loaded_segments (0x52a6c0 : word) = Some W_52a68c.
Proof. vm_refl. Qed.
Lemma D_52a68c : decode_any W_52a68c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a690 : bv 32 := 0xff158593.
Lemma F_52a690 : fetch_word Asan.M.loaded_segments (0x52a6c4 : word) = Some W_52a690.
Proof. vm_refl. Qed.
Lemma D_52a690 : decode_any W_52a690 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a694 : bv 32 := 0x01000713.
Lemma F_52a694 : fetch_word Asan.M.loaded_segments (0x52a6c8 : word) = Some W_52a694.
Proof. vm_refl. Qed.
Lemma D_52a694 : decode_any W_52a694 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a698 : bv 32 := 0xe4e666e3.
Lemma F_52a698 : fetch_word Asan.M.loaded_segments (0x52a6cc : word) = Some W_52a698.
Proof. vm_refl. Qed.
Lemma D_52a698 : decode_any W_52a698 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a69c : bv 32 := 0x0940006f.
Lemma F_52a69c : fetch_word Asan.M.loaded_segments (0x52a6d0 : word) = Some W_52a69c.
Proof. vm_refl. Qed.
Lemma D_52a69c : decode_any W_52a69c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6a0 : bv 32 := 0x00875793.
Lemma F_52a6a0 : fetch_word Asan.M.loaded_segments (0x52a6d4 : word) = Some W_52a6a0.
Proof. vm_refl. Qed.
Lemma D_52a6a0 : decode_any W_52a6a0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6a4 : bv 32 := 0x01075813.
Lemma F_52a6a4 : fetch_word Asan.M.loaded_segments (0x52a6d8 : word) = Some W_52a6a4.
Proof. vm_refl. Qed.
Lemma D_52a6a4 : decode_any W_52a6a4 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6a8 : bv 32 := 0xffd60613.
Lemma F_52a6a8 : fetch_word Asan.M.loaded_segments (0x52a6dc : word) = Some W_52a6a8.
Proof. vm_refl. Qed.
Lemma D_52a6a8 : decode_any W_52a6a8 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6ac : bv 32 := 0x00e68023.
Lemma F_52a6ac : fetch_word Asan.M.loaded_segments (0x52a6e0 : word) = Some W_52a6ac.
Proof. vm_refl. Qed.
Lemma D_52a6ac : decode_any W_52a6ac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6b0 : bv 32 := 0x00f680a3.
Lemma F_52a6b0 : fetch_word Asan.M.loaded_segments (0x52a6e4 : word) = Some W_52a6b0.
Proof. vm_refl. Qed.
Lemma D_52a6b0 : decode_any W_52a6b0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6b4 : bv 32 := 0x01068123.
Lemma F_52a6b4 : fetch_word Asan.M.loaded_segments (0x52a6e8 : word) = Some W_52a6b4.
Proof. vm_refl. Qed.
Lemma D_52a6b4 : decode_any W_52a6b4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6b8 : bv 32 := 0x00368693.
Lemma F_52a6b8 : fetch_word Asan.M.loaded_segments (0x52a6ec : word) = Some W_52a6b8.
Proof. vm_refl. Qed.
Lemma D_52a6b8 : decode_any W_52a6b8 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6bc : bv 32 := 0x01058593.
Lemma F_52a6bc : fetch_word Asan.M.loaded_segments (0x52a6f0 : word) = Some W_52a6bc.
Proof. vm_refl. Qed.
Lemma D_52a6bc : decode_any W_52a6bc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6c0 : bv 32 := 0x01000793.
Lemma F_52a6c0 : fetch_word Asan.M.loaded_segments (0x52a6f4 : word) = Some W_52a6c0.
Proof. vm_refl. Qed.
Lemma D_52a6c0 : decode_any W_52a6c0 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6c4 : bv 32 := 0x0187581b.
Lemma F_52a6c4 : fetch_word Asan.M.loaded_segments (0x52a6f8 : word) = Some W_52a6c4.
Proof. vm_refl. Qed.
Lemma D_52a6c4 : decode_any W_52a6c4 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6c8 : bv 32 := 0xff45a883.
Lemma F_52a6c8 : fetch_word Asan.M.loaded_segments (0x52a6fc : word) = Some W_52a6c8.
Proof. vm_refl. Qed.
Lemma D_52a6c8 : decode_any W_52a6c8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6cc : bv 32 := 0xff85a283.
Lemma F_52a6cc : fetch_word Asan.M.loaded_segments (0x52a700 : word) = Some W_52a6cc.
Proof. vm_refl. Qed.
Lemma D_52a6cc : decode_any W_52a6cc = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6d0 : bv 32 := 0xffc5a303.
Lemma F_52a6d0 : fetch_word Asan.M.loaded_segments (0x52a704 : word) = Some W_52a6d0.
Proof. vm_refl. Qed.
Lemma D_52a6d0 : decode_any W_52a6d0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6d4 : bv 32 := 0x0005a703.
Lemma F_52a6d4 : fetch_word Asan.M.loaded_segments (0x52a708 : word) = Some W_52a6d4.
Proof. vm_refl. Qed.
Lemma D_52a6d4 : decode_any W_52a6d4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6d8 : bv 32 := 0x00889393.
Lemma F_52a6d8 : fetch_word Asan.M.loaded_segments (0x52a70c : word) = Some W_52a6d8.
Proof. vm_refl. Qed.
Lemma D_52a6d8 : decode_any W_52a6d8 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6dc : bv 32 := 0x0188d89b.
Lemma F_52a6dc : fetch_word Asan.M.loaded_segments (0x52a710 : word) = Some W_52a6dc.
Proof. vm_refl. Qed.
Lemma D_52a6dc : decode_any W_52a6dc = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6e0 : bv 32 := 0x0103e833.
Lemma F_52a6e0 : fetch_word Asan.M.loaded_segments (0x52a714 : word) = Some W_52a6e0.
Proof. vm_refl. Qed.
Lemma D_52a6e0 : decode_any W_52a6e0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6e4 : bv 32 := 0x00829393.
Lemma F_52a6e4 : fetch_word Asan.M.loaded_segments (0x52a718 : word) = Some W_52a6e4.
Proof. vm_refl. Qed.
Lemma D_52a6e4 : decode_any W_52a6e4 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6e8 : bv 32 := 0x0182d29b.
Lemma F_52a6e8 : fetch_word Asan.M.loaded_segments (0x52a71c : word) = Some W_52a6e8.
Proof. vm_refl. Qed.
Lemma D_52a6e8 : decode_any W_52a6e8 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6ec : bv 32 := 0x0113e8b3.
Lemma F_52a6ec : fetch_word Asan.M.loaded_segments (0x52a720 : word) = Some W_52a6ec.
Proof. vm_refl. Qed.
Lemma D_52a6ec : decode_any W_52a6ec = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6f0 : bv 32 := 0x00831393.
Lemma F_52a6f0 : fetch_word Asan.M.loaded_segments (0x52a724 : word) = Some W_52a6f0.
Proof. vm_refl. Qed.
Lemma D_52a6f0 : decode_any W_52a6f0 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6f4 : bv 32 := 0x0183531b.
Lemma F_52a6f4 : fetch_word Asan.M.loaded_segments (0x52a728 : word) = Some W_52a6f4.
Proof. vm_refl. Qed.
Lemma D_52a6f4 : decode_any W_52a6f4 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6f8 : bv 32 := 0x0053e2b3.
Lemma F_52a6f8 : fetch_word Asan.M.loaded_segments (0x52a72c : word) = Some W_52a6f8.
Proof. vm_refl. Qed.
Lemma D_52a6f8 : decode_any W_52a6f8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a6fc : bv 32 := 0x00871393.
Lemma F_52a6fc : fetch_word Asan.M.loaded_segments (0x52a730 : word) = Some W_52a6fc.
Proof. vm_refl. Qed.
Lemma D_52a6fc : decode_any W_52a6fc = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a700 : bv 32 := 0x0063e333.
Lemma F_52a700 : fetch_word Asan.M.loaded_segments (0x52a734 : word) = Some W_52a700.
Proof. vm_refl. Qed.
Lemma D_52a700 : decode_any W_52a700 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a704 : bv 32 := 0xff060613.
Lemma F_52a704 : fetch_word Asan.M.loaded_segments (0x52a738 : word) = Some W_52a704.
Proof. vm_refl. Qed.
Lemma D_52a704 : decode_any W_52a704 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a708 : bv 32 := 0x0106a023.
Lemma F_52a708 : fetch_word Asan.M.loaded_segments (0x52a73c : word) = Some W_52a708.
Proof. vm_refl. Qed.
Lemma D_52a708 : decode_any W_52a708 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a70c : bv 32 := 0x0116a223.
Lemma F_52a70c : fetch_word Asan.M.loaded_segments (0x52a740 : word) = Some W_52a70c.
Proof. vm_refl. Qed.
Lemma D_52a70c : decode_any W_52a70c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a710 : bv 32 := 0x0056a423.
Lemma F_52a710 : fetch_word Asan.M.loaded_segments (0x52a744 : word) = Some W_52a710.
Proof. vm_refl. Qed.
Lemma D_52a710 : decode_any W_52a710 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a714 : bv 32 := 0x0066a623.
Lemma F_52a714 : fetch_word Asan.M.loaded_segments (0x52a748 : word) = Some W_52a714.
Proof. vm_refl. Qed.
Lemma D_52a714 : decode_any W_52a714 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a718 : bv 32 := 0x01068693.
Lemma F_52a718 : fetch_word Asan.M.loaded_segments (0x52a74c : word) = Some W_52a718.
Proof. vm_refl. Qed.
Lemma D_52a718 : decode_any W_52a718 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a71c : bv 32 := 0x01058593.
Lemma F_52a71c : fetch_word Asan.M.loaded_segments (0x52a750 : word) = Some W_52a71c.
Proof. vm_refl. Qed.
Lemma D_52a71c : decode_any W_52a71c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a720 : bv 32 := 0xfac7e2e3.
Lemma F_52a720 : fetch_word Asan.M.loaded_segments (0x52a754 : word) = Some W_52a720.
Proof. vm_refl. Qed.
Lemma D_52a720 : decode_any W_52a720 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a724 : bv 32 := 0xff358593.
Lemma F_52a724 : fetch_word Asan.M.loaded_segments (0x52a758 : word) = Some W_52a724.
Proof. vm_refl. Qed.
Lemma D_52a724 : decode_any W_52a724 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a728 : bv 32 := 0x01000713.
Lemma F_52a728 : fetch_word Asan.M.loaded_segments (0x52a75c : word) = Some W_52a728.
Proof. vm_refl. Qed.
Lemma D_52a728 : decode_any W_52a728 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a72c : bv 32 := 0xdae66ce3.
Lemma F_52a72c : fetch_word Asan.M.loaded_segments (0x52a760 : word) = Some W_52a72c.
Proof. vm_refl. Qed.
Lemma D_52a72c : decode_any W_52a72c = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a730 : bv 32 := 0x0005c703.
Lemma F_52a730 : fetch_word Asan.M.loaded_segments (0x52a764 : word) = Some W_52a730.
Proof. vm_refl. Qed.
Lemma D_52a730 : decode_any W_52a730 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a734 : bv 32 := 0x0015c783.
Lemma F_52a734 : fetch_word Asan.M.loaded_segments (0x52a768 : word) = Some W_52a734.
Proof. vm_refl. Qed.
Lemma D_52a734 : decode_any W_52a734 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a738 : bv 32 := 0x0025c803.
Lemma F_52a738 : fetch_word Asan.M.loaded_segments (0x52a76c : word) = Some W_52a738.
Proof. vm_refl. Qed.
Lemma D_52a738 : decode_any W_52a738 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a73c : bv 32 := 0x0035c883.
Lemma F_52a73c : fetch_word Asan.M.loaded_segments (0x52a770 : word) = Some W_52a73c.
Proof. vm_refl. Qed.
Lemma D_52a73c : decode_any W_52a73c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a740 : bv 32 := 0x0045c283.
Lemma F_52a740 : fetch_word Asan.M.loaded_segments (0x52a774 : word) = Some W_52a740.
Proof. vm_refl. Qed.
Lemma D_52a740 : decode_any W_52a740 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a744 : bv 32 := 0x0055c303.
Lemma F_52a744 : fetch_word Asan.M.loaded_segments (0x52a778 : word) = Some W_52a744.
Proof. vm_refl. Qed.
Lemma D_52a744 : decode_any W_52a744 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a748 : bv 32 := 0x0065c383.
Lemma F_52a748 : fetch_word Asan.M.loaded_segments (0x52a77c : word) = Some W_52a748.
Proof. vm_refl. Qed.
Lemma D_52a748 : decode_any W_52a748 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a74c : bv 32 := 0x0075ce03.
Lemma F_52a74c : fetch_word Asan.M.loaded_segments (0x52a780 : word) = Some W_52a74c.
Proof. vm_refl. Qed.
Lemma D_52a74c : decode_any W_52a74c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a750 : bv 32 := 0x00e68023.
Lemma F_52a750 : fetch_word Asan.M.loaded_segments (0x52a784 : word) = Some W_52a750.
Proof. vm_refl. Qed.
Lemma D_52a750 : decode_any W_52a750 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a754 : bv 32 := 0x00f680a3.
Lemma F_52a754 : fetch_word Asan.M.loaded_segments (0x52a788 : word) = Some W_52a754.
Proof. vm_refl. Qed.
Lemma D_52a754 : decode_any W_52a754 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a758 : bv 32 := 0x01068123.
Lemma F_52a758 : fetch_word Asan.M.loaded_segments (0x52a78c : word) = Some W_52a758.
Proof. vm_refl. Qed.
Lemma D_52a758 : decode_any W_52a758 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a75c : bv 32 := 0x011681a3.
Lemma F_52a75c : fetch_word Asan.M.loaded_segments (0x52a790 : word) = Some W_52a75c.
Proof. vm_refl. Qed.
Lemma D_52a75c : decode_any W_52a75c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a760 : bv 32 := 0x0085c703.
Lemma F_52a760 : fetch_word Asan.M.loaded_segments (0x52a794 : word) = Some W_52a760.
Proof. vm_refl. Qed.
Lemma D_52a760 : decode_any W_52a760 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a764 : bv 32 := 0x0095c783.
Lemma F_52a764 : fetch_word Asan.M.loaded_segments (0x52a798 : word) = Some W_52a764.
Proof. vm_refl. Qed.
Lemma D_52a764 : decode_any W_52a764 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a768 : bv 32 := 0x00a5c803.
Lemma F_52a768 : fetch_word Asan.M.loaded_segments (0x52a79c : word) = Some W_52a768.
Proof. vm_refl. Qed.
Lemma D_52a768 : decode_any W_52a768 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a76c : bv 32 := 0x00b5c883.
Lemma F_52a76c : fetch_word Asan.M.loaded_segments (0x52a7a0 : word) = Some W_52a76c.
Proof. vm_refl. Qed.
Lemma D_52a76c : decode_any W_52a76c = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a770 : bv 32 := 0x00568223.
Lemma F_52a770 : fetch_word Asan.M.loaded_segments (0x52a7a4 : word) = Some W_52a770.
Proof. vm_refl. Qed.
Lemma D_52a770 : decode_any W_52a770 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a774 : bv 32 := 0x006682a3.
Lemma F_52a774 : fetch_word Asan.M.loaded_segments (0x52a7a8 : word) = Some W_52a774.
Proof. vm_refl. Qed.
Lemma D_52a774 : decode_any W_52a774 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a778 : bv 32 := 0x00768323.
Lemma F_52a778 : fetch_word Asan.M.loaded_segments (0x52a7ac : word) = Some W_52a778.
Proof. vm_refl. Qed.
Lemma D_52a778 : decode_any W_52a778 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a77c : bv 32 := 0x01c683a3.
Lemma F_52a77c : fetch_word Asan.M.loaded_segments (0x52a7b0 : word) = Some W_52a77c.
Proof. vm_refl. Qed.
Lemma D_52a77c : decode_any W_52a77c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a780 : bv 32 := 0x00c5c283.
Lemma F_52a780 : fetch_word Asan.M.loaded_segments (0x52a7b4 : word) = Some W_52a780.
Proof. vm_refl. Qed.
Lemma D_52a780 : decode_any W_52a780 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a784 : bv 32 := 0x00d5c303.
Lemma F_52a784 : fetch_word Asan.M.loaded_segments (0x52a7b8 : word) = Some W_52a784.
Proof. vm_refl. Qed.
Lemma D_52a784 : decode_any W_52a784 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a788 : bv 32 := 0x00e5c383.
Lemma F_52a788 : fetch_word Asan.M.loaded_segments (0x52a7bc : word) = Some W_52a788.
Proof. vm_refl. Qed.
Lemma D_52a788 : decode_any W_52a788 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a78c : bv 32 := 0x00f5ce03.
Lemma F_52a78c : fetch_word Asan.M.loaded_segments (0x52a7c0 : word) = Some W_52a78c.
Proof. vm_refl. Qed.
Lemma D_52a78c : decode_any W_52a78c = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a790 : bv 32 := 0x01058593.
Lemma F_52a790 : fetch_word Asan.M.loaded_segments (0x52a7c4 : word) = Some W_52a790.
Proof. vm_refl. Qed.
Lemma D_52a790 : decode_any W_52a790 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a794 : bv 32 := 0x00e68423.
Lemma F_52a794 : fetch_word Asan.M.loaded_segments (0x52a7c8 : word) = Some W_52a794.
Proof. vm_refl. Qed.
Lemma D_52a794 : decode_any W_52a794 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a798 : bv 32 := 0x00f684a3.
Lemma F_52a798 : fetch_word Asan.M.loaded_segments (0x52a7cc : word) = Some W_52a798.
Proof. vm_refl. Qed.
Lemma D_52a798 : decode_any W_52a798 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a79c : bv 32 := 0x01068523.
Lemma F_52a79c : fetch_word Asan.M.loaded_segments (0x52a7d0 : word) = Some W_52a79c.
Proof. vm_refl. Qed.
Lemma D_52a79c : decode_any W_52a79c = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7a0 : bv 32 := 0x011685a3.
Lemma F_52a7a0 : fetch_word Asan.M.loaded_segments (0x52a7d4 : word) = Some W_52a7a0.
Proof. vm_refl. Qed.
Lemma D_52a7a0 : decode_any W_52a7a0 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7a4 : bv 32 := 0x01068713.
Lemma F_52a7a4 : fetch_word Asan.M.loaded_segments (0x52a7d8 : word) = Some W_52a7a4.
Proof. vm_refl. Qed.
Lemma D_52a7a4 : decode_any W_52a7a4 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7a8 : bv 32 := 0x00568623.
Lemma F_52a7a8 : fetch_word Asan.M.loaded_segments (0x52a7dc : word) = Some W_52a7a8.
Proof. vm_refl. Qed.
Lemma D_52a7a8 : decode_any W_52a7a8 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7ac : bv 32 := 0x006686a3.
Lemma F_52a7ac : fetch_word Asan.M.loaded_segments (0x52a7e0 : word) = Some W_52a7ac.
Proof. vm_refl. Qed.
Lemma D_52a7ac : decode_any W_52a7ac = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7b0 : bv 32 := 0x00768723.
Lemma F_52a7b0 : fetch_word Asan.M.loaded_segments (0x52a7e4 : word) = Some W_52a7b0.
Proof. vm_refl. Qed.
Lemma D_52a7b0 : decode_any W_52a7b0 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7b4 : bv 32 := 0x01c687a3.
Lemma F_52a7b4 : fetch_word Asan.M.loaded_segments (0x52a7e8 : word) = Some W_52a7b4.
Proof. vm_refl. Qed.
Lemma D_52a7b4 : decode_any W_52a7b4 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7b8 : bv 32 := 0x00070693.
Lemma F_52a7b8 : fetch_word Asan.M.loaded_segments (0x52a7ec : word) = Some W_52a7b8.
Proof. vm_refl. Qed.
Lemma D_52a7b8 : decode_any W_52a7b8 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7bc : bv 32 := 0x00867713.
Lemma F_52a7bc : fetch_word Asan.M.loaded_segments (0x52a7f0 : word) = Some W_52a7bc.
Proof. vm_refl. Qed.
Lemma D_52a7bc : decode_any W_52a7bc = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7c0 : bv 32 := 0xd20706e3.
Lemma F_52a7c0 : fetch_word Asan.M.loaded_segments (0x52a7f4 : word) = Some W_52a7c0.
Proof. vm_refl. Qed.
Lemma D_52a7c0 : decode_any W_52a7c0 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7c4 : bv 32 := 0x0005c703.
Lemma F_52a7c4 : fetch_word Asan.M.loaded_segments (0x52a7f8 : word) = Some W_52a7c4.
Proof. vm_refl. Qed.
Lemma D_52a7c4 : decode_any W_52a7c4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7c8 : bv 32 := 0x0015c783.
Lemma F_52a7c8 : fetch_word Asan.M.loaded_segments (0x52a7fc : word) = Some W_52a7c8.
Proof. vm_refl. Qed.
Lemma D_52a7c8 : decode_any W_52a7c8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7cc : bv 32 := 0x0025c803.
Lemma F_52a7cc : fetch_word Asan.M.loaded_segments (0x52a800 : word) = Some W_52a7cc.
Proof. vm_refl. Qed.
Lemma D_52a7cc : decode_any W_52a7cc = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7d0 : bv 32 := 0x0035c883.
Lemma F_52a7d0 : fetch_word Asan.M.loaded_segments (0x52a804 : word) = Some W_52a7d0.
Proof. vm_refl. Qed.
Lemma D_52a7d0 : decode_any W_52a7d0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7d4 : bv 32 := 0x0045c283.
Lemma F_52a7d4 : fetch_word Asan.M.loaded_segments (0x52a808 : word) = Some W_52a7d4.
Proof. vm_refl. Qed.
Lemma D_52a7d4 : decode_any W_52a7d4 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7d8 : bv 32 := 0x0055c303.
Lemma F_52a7d8 : fetch_word Asan.M.loaded_segments (0x52a80c : word) = Some W_52a7d8.
Proof. vm_refl. Qed.
Lemma D_52a7d8 : decode_any W_52a7d8 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7dc : bv 32 := 0x0065c383.
Lemma F_52a7dc : fetch_word Asan.M.loaded_segments (0x52a810 : word) = Some W_52a7dc.
Proof. vm_refl. Qed.
Lemma D_52a7dc : decode_any W_52a7dc = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7e0 : bv 32 := 0x0075ce03.
Lemma F_52a7e0 : fetch_word Asan.M.loaded_segments (0x52a814 : word) = Some W_52a7e0.
Proof. vm_refl. Qed.
Lemma D_52a7e0 : decode_any W_52a7e0 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7e4 : bv 32 := 0x00858593.
Lemma F_52a7e4 : fetch_word Asan.M.loaded_segments (0x52a818 : word) = Some W_52a7e4.
Proof. vm_refl. Qed.
Lemma D_52a7e4 : decode_any W_52a7e4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7e8 : bv 32 := 0x00e68023.
Lemma F_52a7e8 : fetch_word Asan.M.loaded_segments (0x52a81c : word) = Some W_52a7e8.
Proof. vm_refl. Qed.
Lemma D_52a7e8 : decode_any W_52a7e8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7ec : bv 32 := 0x00f680a3.
Lemma F_52a7ec : fetch_word Asan.M.loaded_segments (0x52a820 : word) = Some W_52a7ec.
Proof. vm_refl. Qed.
Lemma D_52a7ec : decode_any W_52a7ec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7f0 : bv 32 := 0x01068123.
Lemma F_52a7f0 : fetch_word Asan.M.loaded_segments (0x52a824 : word) = Some W_52a7f0.
Proof. vm_refl. Qed.
Lemma D_52a7f0 : decode_any W_52a7f0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7f4 : bv 32 := 0x011681a3.
Lemma F_52a7f4 : fetch_word Asan.M.loaded_segments (0x52a828 : word) = Some W_52a7f4.
Proof. vm_refl. Qed.
Lemma D_52a7f4 : decode_any W_52a7f4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7f8 : bv 32 := 0x00868713.
Lemma F_52a7f8 : fetch_word Asan.M.loaded_segments (0x52a82c : word) = Some W_52a7f8.
Proof. vm_refl. Qed.
Lemma D_52a7f8 : decode_any W_52a7f8 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a7fc : bv 32 := 0x00568223.
Lemma F_52a7fc : fetch_word Asan.M.loaded_segments (0x52a830 : word) = Some W_52a7fc.
Proof. vm_refl. Qed.
Lemma D_52a7fc : decode_any W_52a7fc = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a800 : bv 32 := 0x006682a3.
Lemma F_52a800 : fetch_word Asan.M.loaded_segments (0x52a834 : word) = Some W_52a800.
Proof. vm_refl. Qed.
Lemma D_52a800 : decode_any W_52a800 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a804 : bv 32 := 0x00768323.
Lemma F_52a804 : fetch_word Asan.M.loaded_segments (0x52a838 : word) = Some W_52a804.
Proof. vm_refl. Qed.
Lemma D_52a804 : decode_any W_52a804 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a808 : bv 32 := 0x01c683a3.
Lemma F_52a808 : fetch_word Asan.M.loaded_segments (0x52a83c : word) = Some W_52a808.
Proof. vm_refl. Qed.
Lemma D_52a808 : decode_any W_52a808 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a80c : bv 32 := 0x00070693.
Lemma F_52a80c : fetch_word Asan.M.loaded_segments (0x52a840 : word) = Some W_52a80c.
Proof. vm_refl. Qed.
Lemma D_52a80c : decode_any W_52a80c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a810 : bv 32 := 0x00467713.
Lemma F_52a810 : fetch_word Asan.M.loaded_segments (0x52a844 : word) = Some W_52a810.
Proof. vm_refl. Qed.
Lemma D_52a810 : decode_any W_52a810 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a814 : bv 32 := 0x02070863.
Lemma F_52a814 : fetch_word Asan.M.loaded_segments (0x52a848 : word) = Some W_52a814.
Proof. vm_refl. Qed.
Lemma D_52a814 : decode_any W_52a814 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a818 : bv 32 := 0x0005c703.
Lemma F_52a818 : fetch_word Asan.M.loaded_segments (0x52a84c : word) = Some W_52a818.
Proof. vm_refl. Qed.
Lemma D_52a818 : decode_any W_52a818 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a81c : bv 32 := 0x0015c783.
Lemma F_52a81c : fetch_word Asan.M.loaded_segments (0x52a850 : word) = Some W_52a81c.
Proof. vm_refl. Qed.
Lemma D_52a81c : decode_any W_52a81c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a820 : bv 32 := 0x0025c803.
Lemma F_52a820 : fetch_word Asan.M.loaded_segments (0x52a854 : word) = Some W_52a820.
Proof. vm_refl. Qed.
Lemma D_52a820 : decode_any W_52a820 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a824 : bv 32 := 0x0035c883.
Lemma F_52a824 : fetch_word Asan.M.loaded_segments (0x52a858 : word) = Some W_52a824.
Proof. vm_refl. Qed.
Lemma D_52a824 : decode_any W_52a824 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a828 : bv 32 := 0x00458593.
Lemma F_52a828 : fetch_word Asan.M.loaded_segments (0x52a85c : word) = Some W_52a828.
Proof. vm_refl. Qed.
Lemma D_52a828 : decode_any W_52a828 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a82c : bv 32 := 0x00468293.
Lemma F_52a82c : fetch_word Asan.M.loaded_segments (0x52a860 : word) = Some W_52a82c.
Proof. vm_refl. Qed.
Lemma D_52a82c : decode_any W_52a82c = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a830 : bv 32 := 0x00e68023.
Lemma F_52a830 : fetch_word Asan.M.loaded_segments (0x52a864 : word) = Some W_52a830.
Proof. vm_refl. Qed.
Lemma D_52a830 : decode_any W_52a830 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a834 : bv 32 := 0x00f680a3.
Lemma F_52a834 : fetch_word Asan.M.loaded_segments (0x52a868 : word) = Some W_52a834.
Proof. vm_refl. Qed.
Lemma D_52a834 : decode_any W_52a834 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a838 : bv 32 := 0x01068123.
Lemma F_52a838 : fetch_word Asan.M.loaded_segments (0x52a86c : word) = Some W_52a838.
Proof. vm_refl. Qed.
Lemma D_52a838 : decode_any W_52a838 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a83c : bv 32 := 0x011681a3.
Lemma F_52a83c : fetch_word Asan.M.loaded_segments (0x52a870 : word) = Some W_52a83c.
Proof. vm_refl. Qed.
Lemma D_52a83c : decode_any W_52a83c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a840 : bv 32 := 0x00028693.
Lemma F_52a840 : fetch_word Asan.M.loaded_segments (0x52a874 : word) = Some W_52a840.
Proof. vm_refl. Qed.
Lemma D_52a840 : decode_any W_52a840 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a844 : bv 32 := 0x00267713.
Lemma F_52a844 : fetch_word Asan.M.loaded_segments (0x52a878 : word) = Some W_52a844.
Proof. vm_refl. Qed.
Lemma D_52a844 : decode_any W_52a844 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a848 : bv 32 := 0x00071863.
Lemma F_52a848 : fetch_word Asan.M.loaded_segments (0x52a87c : word) = Some W_52a848.
Proof. vm_refl. Qed.
Lemma D_52a848 : decode_any W_52a848 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a84c : bv 32 := 0x00167613.
Lemma F_52a84c : fetch_word Asan.M.loaded_segments (0x52a880 : word) = Some W_52a84c.
Proof. vm_refl. Qed.
Lemma D_52a84c : decode_any W_52a84c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a850 : bv 32 := 0x02061663.
Lemma F_52a850 : fetch_word Asan.M.loaded_segments (0x52a884 : word) = Some W_52a850.
Proof. vm_refl. Qed.
Lemma D_52a850 : decode_any W_52a850 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a854 : bv 32 := 0x00008067.
Lemma F_52a854 : fetch_word Asan.M.loaded_segments (0x52a888 : word) = Some W_52a854.
Proof. vm_refl. Qed.
Lemma D_52a854 : decode_any W_52a854 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a858 : bv 32 := 0x0005c703.
Lemma F_52a858 : fetch_word Asan.M.loaded_segments (0x52a88c : word) = Some W_52a858.
Proof. vm_refl. Qed.
Lemma D_52a858 : decode_any W_52a858 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a85c : bv 32 := 0x0015c783.
Lemma F_52a85c : fetch_word Asan.M.loaded_segments (0x52a890 : word) = Some W_52a85c.
Proof. vm_refl. Qed.
Lemma D_52a85c : decode_any W_52a85c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a860 : bv 32 := 0x00258593.
Lemma F_52a860 : fetch_word Asan.M.loaded_segments (0x52a894 : word) = Some W_52a860.
Proof. vm_refl. Qed.
Lemma D_52a860 : decode_any W_52a860 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a864 : bv 32 := 0x00268813.
Lemma F_52a864 : fetch_word Asan.M.loaded_segments (0x52a898 : word) = Some W_52a864.
Proof. vm_refl. Qed.
Lemma D_52a864 : decode_any W_52a864 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a868 : bv 32 := 0x00e68023.
Lemma F_52a868 : fetch_word Asan.M.loaded_segments (0x52a89c : word) = Some W_52a868.
Proof. vm_refl. Qed.
Lemma D_52a868 : decode_any W_52a868 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a86c : bv 32 := 0x00f680a3.
Lemma F_52a86c : fetch_word Asan.M.loaded_segments (0x52a8a0 : word) = Some W_52a86c.
Proof. vm_refl. Qed.
Lemma D_52a86c : decode_any W_52a86c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a870 : bv 32 := 0x00080693.
Lemma F_52a870 : fetch_word Asan.M.loaded_segments (0x52a8a4 : word) = Some W_52a870.
Proof. vm_refl. Qed.
Lemma D_52a870 : decode_any W_52a870 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a874 : bv 32 := 0x00167613.
Lemma F_52a874 : fetch_word Asan.M.loaded_segments (0x52a8a8 : word) = Some W_52a874.
Proof. vm_refl. Qed.
Lemma D_52a874 : decode_any W_52a874 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a878 : bv 32 := 0xfc060ee3.
Lemma F_52a878 : fetch_word Asan.M.loaded_segments (0x52a8ac : word) = Some W_52a878.
Proof. vm_refl. Qed.
Lemma D_52a878 : decode_any W_52a878 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a87c : bv 32 := 0x0005c583.
Lemma F_52a87c : fetch_word Asan.M.loaded_segments (0x52a8b0 : word) = Some W_52a87c.
Proof. vm_refl. Qed.
Lemma D_52a87c : decode_any W_52a87c = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a880 : bv 32 := 0x00b68023.
Lemma F_52a880 : fetch_word Asan.M.loaded_segments (0x52a8b4 : word) = Some W_52a880.
Proof. vm_refl. Qed.
Lemma D_52a880 : decode_any W_52a880 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a884 : bv 32 := 0x00008067.
Lemma F_52a884 : fetch_word Asan.M.loaded_segments (0x52a8b8 : word) = Some W_52a884.
Proof. vm_refl. Qed.
Lemma D_52a884 : decode_any W_52a884 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
