(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5a49c : bv 32 := 0x00060793.
Lemma F_5a49c : fetch_word Asan.M.loaded_segments (0x5a4ec : word) = Some W_5a49c.
Proof. vm_refl. Qed.
Lemma D_5a49c : decode_any W_5a49c = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4a0 : bv 32 := 0x00058713.
Lemma F_5a4a0 : fetch_word Asan.M.loaded_segments (0x5a4f0 : word) = Some W_5a4a0.
Proof. vm_refl. Qed.
Lemma D_5a4a0 : decode_any W_5a4a0 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4a4 : bv 32 := 0x0010c597.
Lemma F_5a4a4 : fetch_word Asan.M.loaded_segments (0x5a4f4 : word) = Some W_5a4a4.
Proof. vm_refl. Qed.
Lemma D_5a4a4 : decode_any W_5a4a4 = Some (Auipc 11 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4a8 : bv 32 := 0x3a458593.
Lemma F_5a4a8 : fetch_word Asan.M.loaded_segments (0x5a4f8 : word) = Some W_5a4a8.
Proof. vm_refl. Qed.
Lemma D_5a4a8 : decode_any W_5a4a8 = Some (OpImm ALU_ADD 11 11 932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4ac : bv 32 := 0x00050613.
Lemma F_5a4ac : fetch_word Asan.M.loaded_segments (0x5a4fc : word) = Some W_5a4ac.
Proof. vm_refl. Qed.
Lemma D_5a4ac : decode_any W_5a4ac = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4b0 : bv 32 := 0x00058513.
Lemma F_5a4b0 : fetch_word Asan.M.loaded_segments (0x5a500 : word) = Some W_5a4b0.
Proof. vm_refl. Qed.
Lemma D_5a4b0 : decode_any W_5a4b0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4b4 : bv 32 := 0x00060593.
Lemma F_5a4b4 : fetch_word Asan.M.loaded_segments (0x5a504 : word) = Some W_5a4b4.
Proof. vm_refl. Qed.
Lemma D_5a4b4 : decode_any W_5a4b4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4b8 : bv 32 := 0x00000613.
Lemma F_5a4b8 : fetch_word Asan.M.loaded_segments (0x5a508 : word) = Some W_5a4b8.
Proof. vm_refl. Qed.
Lemma D_5a4b8 : decode_any W_5a4b8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4bc : bv 32 := 0x00000693.
Lemma F_5a4bc : fetch_word Asan.M.loaded_segments (0x5a50c : word) = Some W_5a4bc.
Proof. vm_refl. Qed.
Lemma D_5a4bc : decode_any W_5a4bc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4c0 : bv 32 := 0x0040006f.
Lemma F_5a4c0 : fetch_word Asan.M.loaded_segments (0x5a510 : word) = Some W_5a4c0.
Proof. vm_refl. Qed.
Lemma D_5a4c0 : decode_any W_5a4c0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4c4 : bv 32 := 0xfc010113.
Lemma F_5a4c4 : fetch_word Asan.M.loaded_segments (0x5a514 : word) = Some W_5a4c4.
Proof. vm_refl. Qed.
Lemma D_5a4c4 : decode_any W_5a4c4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4c8 : bv 32 := 0x02113c23.
Lemma F_5a4c8 : fetch_word Asan.M.loaded_segments (0x5a518 : word) = Some W_5a4c8.
Proof. vm_refl. Qed.
Lemma D_5a4c8 : decode_any W_5a4c8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4cc : bv 32 := 0x02813823.
Lemma F_5a4cc : fetch_word Asan.M.loaded_segments (0x5a51c : word) = Some W_5a4cc.
Proof. vm_refl. Qed.
Lemma D_5a4cc : decode_any W_5a4cc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4d0 : bv 32 := 0x02913423.
Lemma F_5a4d0 : fetch_word Asan.M.loaded_segments (0x5a520 : word) = Some W_5a4d0.
Proof. vm_refl. Qed.
Lemma D_5a4d0 : decode_any W_5a4d0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4d4 : bv 32 := 0x03213023.
Lemma F_5a4d4 : fetch_word Asan.M.loaded_segments (0x5a524 : word) = Some W_5a4d4.
Proof. vm_refl. Qed.
Lemma D_5a4d4 : decode_any W_5a4d4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4d8 : bv 32 := 0x01313c23.
Lemma F_5a4d8 : fetch_word Asan.M.loaded_segments (0x5a528 : word) = Some W_5a4d8.
Proof. vm_refl. Qed.
Lemma D_5a4d8 : decode_any W_5a4d8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4dc : bv 32 := 0x01413823.
Lemma F_5a4dc : fetch_word Asan.M.loaded_segments (0x5a52c : word) = Some W_5a4dc.
Proof. vm_refl. Qed.
Lemma D_5a4dc : decode_any W_5a4dc = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4e0 : bv 32 := 0x01513423.
Lemma F_5a4e0 : fetch_word Asan.M.loaded_segments (0x5a530 : word) = Some W_5a4e0.
Proof. vm_refl. Qed.
Lemma D_5a4e0 : decode_any W_5a4e0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4e4 : bv 32 := 0x01613023.
Lemma F_5a4e4 : fetch_word Asan.M.loaded_segments (0x5a534 : word) = Some W_5a4e4.
Proof. vm_refl. Qed.
Lemma D_5a4e4 : decode_any W_5a4e4 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4e8 : bv 32 := 0x02058e63.
Lemma F_5a4e8 : fetch_word Asan.M.loaded_segments (0x5a538 : word) = Some W_5a4e8.
Proof. vm_refl. Qed.
Lemma D_5a4e8 : decode_any W_5a4e8 = Some (Branch BC_EQ 11 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4ec : bv 32 := 0x00078a13.
Lemma F_5a4ec : fetch_word Asan.M.loaded_segments (0x5a53c : word) = Some W_5a4ec.
Proof. vm_refl. Qed.
Lemma D_5a4ec : decode_any W_5a4ec = Some (OpImm ALU_ADD 20 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4f0 : bv 32 := 0x00070413.
Lemma F_5a4f0 : fetch_word Asan.M.loaded_segments (0x5a540 : word) = Some W_5a4f0.
Proof. vm_refl. Qed.
Lemma D_5a4f0 : decode_any W_5a4f0 = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4f4 : bv 32 := 0x00058493.
Lemma F_5a4f4 : fetch_word Asan.M.loaded_segments (0x5a544 : word) = Some W_5a4f4.
Proof. vm_refl. Qed.
Lemma D_5a4f4 : decode_any W_5a4f4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4f8 : bv 32 := 0x00050993.
Lemma F_5a4f8 : fetch_word Asan.M.loaded_segments (0x5a548 : word) = Some W_5a4f8.
Proof. vm_refl. Qed.
Lemma D_5a4f8 : decode_any W_5a4f8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a4fc : bv 32 := 0x00060a93.
Lemma F_5a4fc : fetch_word Asan.M.loaded_segments (0x5a54c : word) = Some W_5a4fc.
Proof. vm_refl. Qed.
Lemma D_5a4fc : decode_any W_5a4fc = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a500 : bv 32 := 0x00068b13.
Lemma F_5a500 : fetch_word Asan.M.loaded_segments (0x5a550 : word) = Some W_5a500.
Proof. vm_refl. Qed.
Lemma D_5a500 : decode_any W_5a500 = Some (OpImm ALU_ADD 22 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a504 : bv 32 := 0xff058913.
Lemma F_5a504 : fetch_word Asan.M.loaded_segments (0x5a554 : word) = Some W_5a504.
Proof. vm_refl. Qed.
Lemma D_5a504 : decode_any W_5a504 = Some (OpImm ALU_ADD 18 11 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a508 : bv 32 := 0x00058513.
Lemma F_5a508 : fetch_word Asan.M.loaded_segments (0x5a558 : word) = Some W_5a508.
Proof. vm_refl. Qed.
Lemma D_5a508 : decode_any W_5a508 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a50c : bv 32 := 0x1c4360ef.
Lemma F_5a50c : fetch_word Asan.M.loaded_segments (0x5a55c : word) = Some W_5a50c.
Proof. vm_refl. Qed.
Lemma D_5a50c : decode_any W_5a50c = Some (Jal 1 221636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a510 : bv 32 := 0x02050e63.
Lemma F_5a510 : fetch_word Asan.M.loaded_segments (0x5a560 : word) = Some W_5a510.
Proof. vm_refl. Qed.
Lemma D_5a510 : decode_any W_5a510 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a524 : bv 32 := 0x03813083.
Lemma F_5a524 : fetch_word Asan.M.loaded_segments (0x5a574 : word) = Some W_5a524.
Proof. vm_refl. Qed.
Lemma D_5a524 : decode_any W_5a524 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a528 : bv 32 := 0x03013403.
Lemma F_5a528 : fetch_word Asan.M.loaded_segments (0x5a578 : word) = Some W_5a528.
Proof. vm_refl. Qed.
Lemma D_5a528 : decode_any W_5a528 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a52c : bv 32 := 0x02813483.
Lemma F_5a52c : fetch_word Asan.M.loaded_segments (0x5a57c : word) = Some W_5a52c.
Proof. vm_refl. Qed.
Lemma D_5a52c : decode_any W_5a52c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a530 : bv 32 := 0x02013903.
Lemma F_5a530 : fetch_word Asan.M.loaded_segments (0x5a580 : word) = Some W_5a530.
Proof. vm_refl. Qed.
Lemma D_5a530 : decode_any W_5a530 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a534 : bv 32 := 0x01813983.
Lemma F_5a534 : fetch_word Asan.M.loaded_segments (0x5a584 : word) = Some W_5a534.
Proof. vm_refl. Qed.
Lemma D_5a534 : decode_any W_5a534 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a538 : bv 32 := 0x01013a03.
Lemma F_5a538 : fetch_word Asan.M.loaded_segments (0x5a588 : word) = Some W_5a538.
Proof. vm_refl. Qed.
Lemma D_5a538 : decode_any W_5a538 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a53c : bv 32 := 0x00813a83.
Lemma F_5a53c : fetch_word Asan.M.loaded_segments (0x5a58c : word) = Some W_5a53c.
Proof. vm_refl. Qed.
Lemma D_5a53c : decode_any W_5a53c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a540 : bv 32 := 0x00013b03.
Lemma F_5a540 : fetch_word Asan.M.loaded_segments (0x5a590 : word) = Some W_5a540.
Proof. vm_refl. Qed.
Lemma D_5a540 : decode_any W_5a540 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a544 : bv 32 := 0x04010113.
Lemma F_5a544 : fetch_word Asan.M.loaded_segments (0x5a594 : word) = Some W_5a544.
Proof. vm_refl. Qed.
Lemma D_5a544 : decode_any W_5a544 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a548 : bv 32 := 0x00008067.
Lemma F_5a548 : fetch_word Asan.M.loaded_segments (0x5a598 : word) = Some W_5a548.
Proof. vm_refl. Qed.
Lemma D_5a548 : decode_any W_5a548 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a54c : bv 32 := 0xffc97693.
Lemma F_5a54c : fetch_word Asan.M.loaded_segments (0x5a59c : word) = Some W_5a54c.
Proof. vm_refl. Qed.
Lemma D_5a54c : decode_any W_5a54c = Some (OpImm ALU_AND 13 18 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a550 : bv 32 := 0x00391513.
Lemma F_5a550 : fetch_word Asan.M.loaded_segments (0x5a5a0 : word) = Some W_5a550.
Proof. vm_refl. Qed.
Lemma D_5a550 : decode_any W_5a550 = Some (ShiftImm ALU_SLL 10 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a554 : bv 32 := 0x0ff00613.
Lemma F_5a554 : fetch_word Asan.M.loaded_segments (0x5a5a4 : word) = Some W_5a554.
Proof. vm_refl. Qed.
Lemma D_5a554 : decode_any W_5a554 = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a558 : bv 32 := 0x00200713.
Lemma F_5a558 : fetch_word Asan.M.loaded_segments (0x5a5a8 : word) = Some W_5a558.
Proof. vm_refl. Qed.
Lemma D_5a558 : decode_any W_5a558 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a55c : bv 32 := 0x00300593.
Lemma F_5a55c : fetch_word Asan.M.loaded_segments (0x5a5ac : word) = Some W_5a55c.
Proof. vm_refl. Qed.
Lemma D_5a55c : decode_any W_5a55c = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a560 : bv 32 := 0x00a617bb.
Lemma F_5a560 : fetch_word Asan.M.loaded_segments (0x5a5b0 : word) = Some W_5a560.
Proof. vm_refl. Qed.
Lemma D_5a560 : decode_any W_5a560 = Some (Op32 ALU_SLL 15 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a564 : bv 32 := 0x00a7173b.
Lemma F_5a564 : fetch_word Asan.M.loaded_segments (0x5a5b4 : word) = Some W_5a564.
Proof. vm_refl. Qed.
Lemma D_5a564 : decode_any W_5a564 = Some (Op32 ALU_SLL 14 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a568 : bv 32 := 0x00a5983b.
Lemma F_5a568 : fetch_word Asan.M.loaded_segments (0x5a5b8 : word) = Some W_5a568.
Proof. vm_refl. Qed.
Lemma D_5a568 : decode_any W_5a568 = Some (Op32 ALU_SLL 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a56c : bv 32 := 0x1606a62f.
Lemma F_5a56c : fetch_word Asan.M.loaded_segments (0x5a5bc : word) = Some W_5a56c.
Proof. vm_refl. Qed.
Lemma D_5a56c : decode_any W_5a56c = Some (Lr AW true true 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a570 : bv 32 := 0x00f678b3.
Lemma F_5a570 : fetch_word Asan.M.loaded_segments (0x5a5c0 : word) = Some W_5a570.
Proof. vm_refl. Qed.
Lemma D_5a570 : decode_any W_5a570 = Some (Op ALU_AND 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a574 : bv 32 := 0x08e89063.
Lemma F_5a574 : fetch_word Asan.M.loaded_segments (0x5a5c4 : word) = Some W_5a574.
Proof. vm_refl. Qed.
Lemma D_5a574 : decode_any W_5a574 = Some (Branch BC_NE 17 14 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a578 : bv 32 := 0x010648b3.
Lemma F_5a578 : fetch_word Asan.M.loaded_segments (0x5a5c8 : word) = Some W_5a578.
Proof. vm_refl. Qed.
Lemma D_5a578 : decode_any W_5a578 = Some (Op ALU_XOR 17 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a57c : bv 32 := 0x00f8f8b3.
Lemma F_5a57c : fetch_word Asan.M.loaded_segments (0x5a5cc : word) = Some W_5a57c.
Proof. vm_refl. Qed.
Lemma D_5a57c : decode_any W_5a57c = Some (Op ALU_AND 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a580 : bv 32 := 0x011648b3.
Lemma F_5a580 : fetch_word Asan.M.loaded_segments (0x5a5d0 : word) = Some W_5a580.
Proof. vm_refl. Qed.
Lemma D_5a580 : decode_any W_5a580 = Some (Op ALU_XOR 17 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a584 : bv 32 := 0x1b16a8af.
Lemma F_5a584 : fetch_word Asan.M.loaded_segments (0x5a5d4 : word) = Some W_5a584.
Proof. vm_refl. Qed.
Lemma D_5a584 : decode_any W_5a584 = Some (Sc AW false true 17 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a588 : bv 32 := 0xfe0892e3.
Lemma F_5a588 : fetch_word Asan.M.loaded_segments (0x5a5d8 : word) = Some W_5a588.
Proof. vm_refl. Qed.
Lemma D_5a588 : decode_any W_5a588 = Some (Branch BC_NE 17 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a58c : bv 32 := 0xfff00513.
Lemma F_5a58c : fetch_word Asan.M.loaded_segments (0x5a5dc : word) = Some W_5a58c.
Proof. vm_refl. Qed.
Lemma D_5a58c : decode_any W_5a58c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a590 : bv 32 := 0x02051513.
Lemma F_5a590 : fetch_word Asan.M.loaded_segments (0x5a5e0 : word) = Some W_5a590.
Proof. vm_refl. Qed.
Lemma D_5a590 : decode_any W_5a590 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a594 : bv 32 := 0x00a93823.
Lemma F_5a594 : fetch_word Asan.M.loaded_segments (0x5a5e4 : word) = Some W_5a594.
Proof. vm_refl. Qed.
Lemma D_5a594 : decode_any W_5a594 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a598 : bv 32 := 0x00194503.
Lemma F_5a598 : fetch_word Asan.M.loaded_segments (0x5a5e8 : word) = Some W_5a598.
Proof. vm_refl. Qed.
Lemma D_5a598 : decode_any W_5a598 = Some (Load SZ1 false 10 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a59c : bv 32 := 0x00357593.
Lemma F_5a59c : fetch_word Asan.M.loaded_segments (0x5a5ec : word) = Some W_5a59c.
Proof. vm_refl. Qed.
Lemma D_5a59c : decode_any W_5a59c = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a5a0 : bv 32 := 0x08ba1863.
Lemma F_5a5a0 : fetch_word Asan.M.loaded_segments (0x5a5f0 : word) = Some W_5a5a0.
Proof. vm_refl. Qed.
Lemma D_5a5a0 : decode_any W_5a5a0 = Some (Branch BC_NE 20 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a5a4 : bv 32 := 0xffea7693.
Lemma F_5a5a4 : fetch_word Asan.M.loaded_segments (0x5a5f4 : word) = Some W_5a5a4.
Proof. vm_refl. Qed.
Lemma D_5a5a4 : decode_any W_5a5a4 = Some (OpImm ALU_AND 13 20 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a5a8 : bv 32 := 0x00200713.
Lemma F_5a5a8 : fetch_word Asan.M.loaded_segments (0x5a5f8 : word) = Some W_5a5a8.
Proof. vm_refl. Qed.
Lemma D_5a5a8 : decode_any W_5a5a8 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a5ac : bv 32 := 0x14e69663.
Lemma F_5a5ac : fetch_word Asan.M.loaded_segments (0x5a5fc : word) = Some W_5a5ac.
Proof. vm_refl. Qed.
Lemma D_5a5ac : decode_any W_5a5ac = Some (Branch BC_NE 13 14 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a6f8 : bv 32 := 0x115300ef.
Lemma F_5a6f8 : fetch_word Asan.M.loaded_segments (0x5a748 : word) = Some W_5a6f8.
Proof. vm_refl. Qed.
Lemma D_5a6f8 : decode_any W_5a6f8 = Some (Jal 1 198932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a6fc : bv 32 := 0xff24d583.
Lemma F_5a6fc : fetch_word Asan.M.loaded_segments (0x5a74c : word) = Some W_5a6fc.
Proof. vm_refl. Qed.
Lemma D_5a6fc : decode_any W_5a6fc = Some (Load SZ2 false 11 9 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a700 : bv 32 := 0xff44e603.
Lemma F_5a700 : fetch_word Asan.M.loaded_segments (0x5a750 : word) = Some W_5a700.
Proof. vm_refl. Qed.
Lemma D_5a700 : decode_any W_5a700 = Some (Load SZ4 false 12 9 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a704 : bv 32 := 0x02053683.
Lemma F_5a704 : fetch_word Asan.M.loaded_segments (0x5a754 : word) = Some W_5a704.
Proof. vm_refl. Qed.
Lemma D_5a704 : decode_any W_5a704 = Some (Load SZ8 true 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a708 : bv 32 := 0x01853703.
Lemma F_5a708 : fetch_word Asan.M.loaded_segments (0x5a758 : word) = Some W_5a708.
Proof. vm_refl. Qed.
Lemma D_5a708 : decode_any W_5a708 = Some (Load SZ8 true 14 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a70c : bv 32 := 0x02059593.
Lemma F_5a70c : fetch_word Asan.M.loaded_segments (0x5a75c : word) = Some W_5a70c.
Proof. vm_refl. Qed.
Lemma D_5a70c : decode_any W_5a70c = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a710 : bv 32 := 0x00c5e5b3.
Lemma F_5a710 : fetch_word Asan.M.loaded_segments (0x5a760 : word) = Some W_5a710.
Proof. vm_refl. Qed.
Lemma D_5a710 : decode_any W_5a710 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a714 : bv 32 := 0x00d585b3.
Lemma F_5a714 : fetch_word Asan.M.loaded_segments (0x5a764 : word) = Some W_5a714.
Proof. vm_refl. Qed.
Lemma D_5a714 : decode_any W_5a714 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a718 : bv 32 := 0x00170713.
Lemma F_5a718 : fetch_word Asan.M.loaded_segments (0x5a768 : word) = Some W_5a718.
Proof. vm_refl. Qed.
Lemma D_5a718 : decode_any W_5a718 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a71c : bv 32 := 0x00e53c23.
Lemma F_5a71c : fetch_word Asan.M.loaded_segments (0x5a76c : word) = Some W_5a71c.
Proof. vm_refl. Qed.
Lemma D_5a71c : decode_any W_5a71c = Some (Store SZ8 10 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a720 : bv 32 := 0x02b53023.
Lemma F_5a720 : fetch_word Asan.M.loaded_segments (0x5a770 : word) = Some W_5a720.
Proof. vm_refl. Qed.
Lemma D_5a720 : decode_any W_5a720 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a724 : bv 32 := 0x00098513.
Lemma F_5a724 : fetch_word Asan.M.loaded_segments (0x5a774 : word) = Some W_5a724.
Proof. vm_refl. Qed.
Lemma D_5a724 : decode_any W_5a724 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a728 : bv 32 := 0x00090593.
Lemma F_5a728 : fetch_word Asan.M.loaded_segments (0x5a778 : word) = Some W_5a728.
Proof. vm_refl. Qed.
Lemma D_5a728 : decode_any W_5a728 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a72c : bv 32 := 0x00048613.
Lemma F_5a72c : fetch_word Asan.M.loaded_segments (0x5a77c : word) = Some W_5a72c.
Proof. vm_refl. Qed.
Lemma D_5a72c : decode_any W_5a72c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a730 : bv 32 := 0x00040693.
Lemma F_5a730 : fetch_word Asan.M.loaded_segments (0x5a780 : word) = Some W_5a730.
Proof. vm_refl. Qed.
Lemma D_5a730 : decode_any W_5a730 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a734 : bv 32 := 0x03813083.
Lemma F_5a734 : fetch_word Asan.M.loaded_segments (0x5a784 : word) = Some W_5a734.
Proof. vm_refl. Qed.
Lemma D_5a734 : decode_any W_5a734 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a738 : bv 32 := 0x03013403.
Lemma F_5a738 : fetch_word Asan.M.loaded_segments (0x5a788 : word) = Some W_5a738.
Proof. vm_refl. Qed.
Lemma D_5a738 : decode_any W_5a738 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a73c : bv 32 := 0x02813483.
Lemma F_5a73c : fetch_word Asan.M.loaded_segments (0x5a78c : word) = Some W_5a73c.
Proof. vm_refl. Qed.
Lemma D_5a73c : decode_any W_5a73c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a740 : bv 32 := 0x02013903.
Lemma F_5a740 : fetch_word Asan.M.loaded_segments (0x5a790 : word) = Some W_5a740.
Proof. vm_refl. Qed.
Lemma D_5a740 : decode_any W_5a740 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a744 : bv 32 := 0x01813983.
Lemma F_5a744 : fetch_word Asan.M.loaded_segments (0x5a794 : word) = Some W_5a744.
Proof. vm_refl. Qed.
Lemma D_5a744 : decode_any W_5a744 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a748 : bv 32 := 0x01013a03.
Lemma F_5a748 : fetch_word Asan.M.loaded_segments (0x5a798 : word) = Some W_5a748.
Proof. vm_refl. Qed.
Lemma D_5a748 : decode_any W_5a748 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a74c : bv 32 := 0x00813a83.
Lemma F_5a74c : fetch_word Asan.M.loaded_segments (0x5a79c : word) = Some W_5a74c.
Proof. vm_refl. Qed.
Lemma D_5a74c : decode_any W_5a74c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a750 : bv 32 := 0x00013b03.
Lemma F_5a750 : fetch_word Asan.M.loaded_segments (0x5a7a0 : word) = Some W_5a750.
Proof. vm_refl. Qed.
Lemma D_5a750 : decode_any W_5a750 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a754 : bv 32 := 0x04010113.
Lemma F_5a754 : fetch_word Asan.M.loaded_segments (0x5a7a4 : word) = Some W_5a754.
Proof. vm_refl. Qed.
Lemma D_5a754 : decode_any W_5a754 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a758 : bv 32 := 0x2cc0406f.
Lemma F_5a758 : fetch_word Asan.M.loaded_segments (0x5a7a8 : word) = Some W_5a758.
Proof. vm_refl. Qed.
Lemma D_5a758 : decode_any W_5a758 = Some (Jal 0 17100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a77c : bv 32 := 0xff010113.
Lemma F_5a77c : fetch_word Asan.M.loaded_segments (0x5a7cc : word) = Some W_5a77c.
Proof. vm_refl. Qed.
Lemma D_5a77c : decode_any W_5a77c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a780 : bv 32 := 0x00113423.
Lemma F_5a780 : fetch_word Asan.M.loaded_segments (0x5a7d0 : word) = Some W_5a780.
Proof. vm_refl. Qed.
Lemma D_5a780 : decode_any W_5a780 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a784 : bv 32 := 0x00813023.
Lemma F_5a784 : fetch_word Asan.M.loaded_segments (0x5a7d4 : word) = Some W_5a784.
Proof. vm_refl. Qed.
Lemma D_5a784 : decode_any W_5a784 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a788 : bv 32 := 0x00058693.
Lemma F_5a788 : fetch_word Asan.M.loaded_segments (0x5a7d8 : word) = Some W_5a788.
Proof. vm_refl. Qed.
Lemma D_5a788 : decode_any W_5a788 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a78c : bv 32 := 0x00050593.
Lemma F_5a78c : fetch_word Asan.M.loaded_segments (0x5a7dc : word) = Some W_5a78c.
Proof. vm_refl. Qed.
Lemma D_5a78c : decode_any W_5a78c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a790 : bv 32 := 0x0010c517.
Lemma F_5a790 : fetch_word Asan.M.loaded_segments (0x5a7e0 : word) = Some W_5a790.
Proof. vm_refl. Qed.
Lemma D_5a790 : decode_any W_5a790 = Some (Auipc 10 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a794 : bv 32 := 0x00800613.
Lemma F_5a794 : fetch_word Asan.M.loaded_segments (0x5a7e4 : word) = Some W_5a794.
Proof. vm_refl. Qed.
Lemma D_5a794 : decode_any W_5a794 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a798 : bv 32 := 0x00100713.
Lemma F_5a798 : fetch_word Asan.M.loaded_segments (0x5a7e8 : word) = Some W_5a798.
Proof. vm_refl. Qed.
Lemma D_5a798 : decode_any W_5a798 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a79c : bv 32 := 0x0b850513.
Lemma F_5a79c : fetch_word Asan.M.loaded_segments (0x5a7ec : word) = Some W_5a79c.
Proof. vm_refl. Qed.
Lemma D_5a79c : decode_any W_5a79c = Some (OpImm ALU_ADD 10 10 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7a0 : bv 32 := 0x00100793.
Lemma F_5a7a0 : fetch_word Asan.M.loaded_segments (0x5a7f0 : word) = Some W_5a7a0.
Proof. vm_refl. Qed.
Lemma D_5a7a0 : decode_any W_5a7a0 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7a4 : bv 32 := 0x034000ef.
Lemma F_5a7a4 : fetch_word Asan.M.loaded_segments (0x5a7f4 : word) = Some W_5a7a4.
Proof. vm_refl. Qed.
Lemma D_5a7a4 : decode_any W_5a7a4 = Some (Jal 1 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7a8 : bv 32 := 0x00050a63.
Lemma F_5a7a8 : fetch_word Asan.M.loaded_segments (0x5a7f8 : word) = Some W_5a7a8.
Proof. vm_refl. Qed.
Lemma D_5a7a8 : decode_any W_5a7a8 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7ac : bv 32 := 0x00813083.
Lemma F_5a7ac : fetch_word Asan.M.loaded_segments (0x5a7fc : word) = Some W_5a7ac.
Proof. vm_refl. Qed.
Lemma D_5a7ac : decode_any W_5a7ac = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7b0 : bv 32 := 0x00013403.
Lemma F_5a7b0 : fetch_word Asan.M.loaded_segments (0x5a800 : word) = Some W_5a7b0.
Proof. vm_refl. Qed.
Lemma D_5a7b0 : decode_any W_5a7b0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7b4 : bv 32 := 0x01010113.
Lemma F_5a7b4 : fetch_word Asan.M.loaded_segments (0x5a804 : word) = Some W_5a7b4.
Proof. vm_refl. Qed.
Lemma D_5a7b4 : decode_any W_5a7b4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7b8 : bv 32 := 0x00008067.
Lemma F_5a7b8 : fetch_word Asan.M.loaded_segments (0x5a808 : word) = Some W_5a7b8.
Proof. vm_refl. Qed.
Lemma D_5a7b8 : decode_any W_5a7b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7d8 : bv 32 := 0xf8010113.
Lemma F_5a7d8 : fetch_word Asan.M.loaded_segments (0x5a828 : word) = Some W_5a7d8.
Proof. vm_refl. Qed.
Lemma D_5a7d8 : decode_any W_5a7d8 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7dc : bv 32 := 0x06113c23.
Lemma F_5a7dc : fetch_word Asan.M.loaded_segments (0x5a82c : word) = Some W_5a7dc.
Proof. vm_refl. Qed.
Lemma D_5a7dc : decode_any W_5a7dc = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7e0 : bv 32 := 0x06813823.
Lemma F_5a7e0 : fetch_word Asan.M.loaded_segments (0x5a830 : word) = Some W_5a7e0.
Proof. vm_refl. Qed.
Lemma D_5a7e0 : decode_any W_5a7e0 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7e4 : bv 32 := 0x06913423.
Lemma F_5a7e4 : fetch_word Asan.M.loaded_segments (0x5a834 : word) = Some W_5a7e4.
Proof. vm_refl. Qed.
Lemma D_5a7e4 : decode_any W_5a7e4 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7e8 : bv 32 := 0x07213023.
Lemma F_5a7e8 : fetch_word Asan.M.loaded_segments (0x5a838 : word) = Some W_5a7e8.
Proof. vm_refl. Qed.
Lemma D_5a7e8 : decode_any W_5a7e8 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7ec : bv 32 := 0x05313c23.
Lemma F_5a7ec : fetch_word Asan.M.loaded_segments (0x5a83c : word) = Some W_5a7ec.
Proof. vm_refl. Qed.
Lemma D_5a7ec : decode_any W_5a7ec = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7f0 : bv 32 := 0x05413823.
Lemma F_5a7f0 : fetch_word Asan.M.loaded_segments (0x5a840 : word) = Some W_5a7f0.
Proof. vm_refl. Qed.
Lemma D_5a7f0 : decode_any W_5a7f0 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7f4 : bv 32 := 0x05513423.
Lemma F_5a7f4 : fetch_word Asan.M.loaded_segments (0x5a844 : word) = Some W_5a7f4.
Proof. vm_refl. Qed.
Lemma D_5a7f4 : decode_any W_5a7f4 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7f8 : bv 32 := 0x05613023.
Lemma F_5a7f8 : fetch_word Asan.M.loaded_segments (0x5a848 : word) = Some W_5a7f8.
Proof. vm_refl. Qed.
Lemma D_5a7f8 : decode_any W_5a7f8 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a7fc : bv 32 := 0x03713c23.
Lemma F_5a7fc : fetch_word Asan.M.loaded_segments (0x5a84c : word) = Some W_5a7fc.
Proof. vm_refl. Qed.
Lemma D_5a7fc : decode_any W_5a7fc = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a800 : bv 32 := 0x03813823.
Lemma F_5a800 : fetch_word Asan.M.loaded_segments (0x5a850 : word) = Some W_5a800.
Proof. vm_refl. Qed.
Lemma D_5a800 : decode_any W_5a800 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a804 : bv 32 := 0x03913423.
Lemma F_5a804 : fetch_word Asan.M.loaded_segments (0x5a854 : word) = Some W_5a804.
Proof. vm_refl. Qed.
Lemma D_5a804 : decode_any W_5a804 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a808 : bv 32 := 0x03a13023.
Lemma F_5a808 : fetch_word Asan.M.loaded_segments (0x5a858 : word) = Some W_5a808.
Proof. vm_refl. Qed.
Lemma D_5a808 : decode_any W_5a808 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a80c : bv 32 := 0x01b13c23.
Lemma F_5a80c : fetch_word Asan.M.loaded_segments (0x5a85c : word) = Some W_5a80c.
Proof. vm_refl. Qed.
Lemma D_5a80c : decode_any W_5a80c = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a810 : bv 32 := 0x00078493.
Lemma F_5a810 : fetch_word Asan.M.loaded_segments (0x5a860 : word) = Some W_5a810.
Proof. vm_refl. Qed.
Lemma D_5a810 : decode_any W_5a810 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a814 : bv 32 := 0x00070d93.
Lemma F_5a814 : fetch_word Asan.M.loaded_segments (0x5a864 : word) = Some W_5a814.
Proof. vm_refl. Qed.
Lemma D_5a814 : decode_any W_5a814 = Some (OpImm ALU_ADD 27 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a818 : bv 32 := 0x00068b93.
Lemma F_5a818 : fetch_word Asan.M.loaded_segments (0x5a868 : word) = Some W_5a818.
Proof. vm_refl. Qed.
Lemma D_5a818 : decode_any W_5a818 = Some (OpImm ALU_ADD 23 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a81c : bv 32 := 0x00060913.
Lemma F_5a81c : fetch_word Asan.M.loaded_segments (0x5a86c : word) = Some W_5a81c.
Proof. vm_refl. Qed.
Lemma D_5a81c : decode_any W_5a81c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a820 : bv 32 := 0x00058a93.
Lemma F_5a820 : fetch_word Asan.M.loaded_segments (0x5a870 : word) = Some W_5a820.
Proof. vm_refl. Qed.
Lemma D_5a820 : decode_any W_5a820 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a824 : bv 32 := 0x00050b13.
Lemma F_5a824 : fetch_word Asan.M.loaded_segments (0x5a874 : word) = Some W_5a824.
Proof. vm_refl. Qed.
Lemma D_5a824 : decode_any W_5a824 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a828 : bv 32 := 0x7092d0ef.
Lemma F_5a828 : fetch_word Asan.M.loaded_segments (0x5a878 : word) = Some W_5a828.
Proof. vm_refl. Qed.
Lemma D_5a828 : decode_any W_5a828 = Some (Jal 1 188168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a82c : bv 32 := 0x7e050463.
Lemma F_5a82c : fetch_word Asan.M.loaded_segments (0x5a87c : word) = Some W_5a82c.
Proof. vm_refl. Qed.
Lemma D_5a82c : decode_any W_5a82c = Some (Branch BC_EQ 10 0 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a830 : bv 32 := 0x3c9330ef.
Lemma F_5a830 : fetch_word Asan.M.loaded_segments (0x5a880 : word) = Some W_5a830.
Proof. vm_refl. Qed.
Lemma D_5a830 : decode_any W_5a830 = Some (Jal 1 211912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a834 : bv 32 := 0x7e051663.
Lemma F_5a834 : fetch_word Asan.M.loaded_segments (0x5a884 : word) = Some W_5a834.
Proof. vm_refl. Qed.
Lemma D_5a834 : decode_any W_5a834 = Some (Branch BC_NE 10 0 2028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a838 : bv 32 := 0x080b86e3.
Lemma F_5a838 : fetch_word Asan.M.loaded_segments (0x5a888 : word) = Some W_5a838.
Proof. vm_refl. Qed.
Lemma D_5a838 : decode_any W_5a838 = Some (Branch BC_EQ 23 0 2188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a83c : bv 32 := 0x00800513.
Lemma F_5a83c : fetch_word Asan.M.loaded_segments (0x5a88c : word) = Some W_5a83c.
Proof. vm_refl. Qed.
Lemma D_5a83c : decode_any W_5a83c = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a840 : bv 32 := 0x02a97e63.
Lemma F_5a840 : fetch_word Asan.M.loaded_segments (0x5a890 : word) = Some W_5a840.
Proof. vm_refl. Qed.
Lemma D_5a840 : decode_any W_5a840 = Some (Branch BC_GEU 18 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a850 : bv 32 := 0x00800413.
Lemma F_5a850 : fetch_word Asan.M.loaded_segments (0x5a8a0 : word) = Some W_5a850.
Proof. vm_refl. Qed.
Lemma D_5a850 : decode_any W_5a850 = Some (OpImm ALU_ADD 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a854 : bv 32 := 0xfff40c93.
Lemma F_5a854 : fetch_word Asan.M.loaded_segments (0x5a8a4 : word) = Some W_5a854.
Proof. vm_refl. Qed.
Lemma D_5a854 : decode_any W_5a854 = Some (OpImm ALU_ADD 25 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a858 : bv 32 := 0x01947533.
Lemma F_5a858 : fetch_word Asan.M.loaded_segments (0x5a8a8 : word) = Some W_5a858.
Proof. vm_refl. Qed.
Lemma D_5a858 : decode_any W_5a858 = Some (Op ALU_AND 10 8 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a85c : bv 32 := 0x7c051a63.
Lemma F_5a85c : fetch_word Asan.M.loaded_segments (0x5a8ac : word) = Some W_5a85c.
Proof. vm_refl. Qed.
Lemma D_5a85c : decode_any W_5a85c = Some (Branch BC_NE 10 0 2004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a860 : bv 32 := 0x03100513.
Lemma F_5a860 : fetch_word Asan.M.loaded_segments (0x5a8b0 : word) = Some W_5a860.
Proof. vm_refl. Qed.
Lemma D_5a860 : decode_any W_5a860 = Some (OpImm ALU_ADD 10 0 49, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a864 : bv 32 := 0x7ffb0d13.
Lemma F_5a864 : fetch_word Asan.M.loaded_segments (0x5a8b4 : word) = Some W_5a864.
Proof. vm_refl. Qed.
Lemma D_5a864 : decode_any W_5a864 = Some (OpImm ALU_ADD 26 22 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a868 : bv 32 := 0x00913423.
Lemma F_5a868 : fetch_word Asan.M.loaded_segments (0x5a8b8 : word) = Some W_5a868.
Proof. vm_refl. Qed.
Lemma D_5a868 : decode_any W_5a868 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a86c : bv 32 := 0x00b13823.
Lemma F_5a86c : fetch_word Asan.M.loaded_segments (0x5a8bc : word) = Some W_5a86c.
Proof. vm_refl. Qed.
Lemma D_5a86c : decode_any W_5a86c = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a870 : bv 32 := 0x06aaf463.
Lemma F_5a870 : fetch_word Asan.M.loaded_segments (0x5a8c0 : word) = Some W_5a870.
Proof. vm_refl. Qed.
Lemma D_5a870 : decode_any W_5a870 = Some (Branch BC_GEU 21 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a874 : bv 32 := 0x00000993.
Lemma F_5a874 : fetch_word Asan.M.loaded_segments (0x5a8c4 : word) = Some W_5a874.
Proof. vm_refl. Qed.
Lemma D_5a874 : decode_any W_5a874 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a878 : bv 32 := 0x0cc0006f.
Lemma F_5a878 : fetch_word Asan.M.loaded_segments (0x5a8c8 : word) = Some W_5a878.
Proof. vm_refl. Qed.
Lemma D_5a878 : decode_any W_5a878 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a87c : bv 32 := 0x20000613.
Lemma F_5a87c : fetch_word Asan.M.loaded_segments (0x5a8cc : word) = Some W_5a87c.
Proof. vm_refl. Qed.
Lemma D_5a87c : decode_any W_5a87c = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a880 : bv 32 := 0x00090593.
Lemma F_5a880 : fetch_word Asan.M.loaded_segments (0x5a8d0 : word) = Some W_5a880.
Proof. vm_refl. Qed.
Lemma D_5a880 : decode_any W_5a880 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a884 : bv 32 := 0x00c96463.
Lemma F_5a884 : fetch_word Asan.M.loaded_segments (0x5a8d4 : word) = Some W_5a884.
Proof. vm_refl. Qed.
Lemma D_5a884 : decode_any W_5a884 = Some (Branch BC_LTU 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a88c : bv 32 := 0xfff58613.
Lemma F_5a88c : fetch_word Asan.M.loaded_segments (0x5a8dc : word) = Some W_5a88c.
Proof. vm_refl. Qed.
Lemma D_5a88c : decode_any W_5a88c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a890 : bv 32 := 0x00c5f633.
Lemma F_5a890 : fetch_word Asan.M.loaded_segments (0x5a8e0 : word) = Some W_5a890.
Proof. vm_refl. Qed.
Lemma D_5a890 : decode_any W_5a890 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a894 : bv 32 := 0x040618e3.
Lemma F_5a894 : fetch_word Asan.M.loaded_segments (0x5a8e4 : word) = Some W_5a894.
Proof. vm_refl. Qed.
Lemma D_5a894 : decode_any W_5a894 = Some (Branch BC_NE 12 0 2128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a898 : bv 32 := 0xfffb6617.
Lemma F_5a898 : fetch_word Asan.M.loaded_segments (0x5a8e8 : word) = Some W_5a898.
Proof. vm_refl. Qed.
Lemma D_5a898 : decode_any W_5a898 = Some (Auipc 12 1048502, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a89c : bv 32 := 0xb7863603.
Lemma F_5a89c : fetch_word Asan.M.loaded_segments (0x5a8ec : word) = Some W_5a89c.
Proof. vm_refl. Qed.
Lemma D_5a89c : decode_any W_5a89c = Some (Load SZ8 true 12 12 2936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8a0 : bv 32 := 0x40b006b3.
Lemma F_5a8a0 : fetch_word Asan.M.loaded_segments (0x5a8f0 : word) = Some W_5a8a0.
Proof. vm_refl. Qed.
Lemma D_5a8a0 : decode_any W_5a8a0 = Some (Op ALU_SUB 13 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8a4 : bv 32 := 0x00d5f5b3.
Lemma F_5a8a4 : fetch_word Asan.M.loaded_segments (0x5a8f4 : word) = Some W_5a8a4.
Proof. vm_refl. Qed.
Lemma D_5a8a4 : decode_any W_5a8a4 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8a8 : bv 32 := 0x02c585b3.
Lemma F_5a8a8 : fetch_word Asan.M.loaded_segments (0x5a8f8 : word) = Some W_5a8a8.
Proof. vm_refl. Qed.
Lemma D_5a8a8 : decode_any W_5a8a8 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8ac : bv 32 := 0xfffb6617.
Lemma F_5a8ac : fetch_word Asan.M.loaded_segments (0x5a8fc : word) = Some W_5a8ac.
Proof. vm_refl. Qed.
Lemma D_5a8ac : decode_any W_5a8ac = Some (Auipc 12 1048502, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8b0 : bv 32 := 0x03a5d593.
Lemma F_5a8b0 : fetch_word Asan.M.loaded_segments (0x5a900 : word) = Some W_5a8b0.
Proof. vm_refl. Qed.
Lemma D_5a8b0 : decode_any W_5a8b0 = Some (ShiftImm ALU_SRL 11 11 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8b4 : bv 32 := 0xbdc60613.
Lemma F_5a8b4 : fetch_word Asan.M.loaded_segments (0x5a904 : word) = Some W_5a8b4.
Proof. vm_refl. Qed.
Lemma D_5a8b4 : decode_any W_5a8b4 = Some (OpImm ALU_ADD 12 12 3036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8b8 : bv 32 := 0x00b605b3.
Lemma F_5a8b8 : fetch_word Asan.M.loaded_segments (0x5a908 : word) = Some W_5a8b8.
Proof. vm_refl. Qed.
Lemma D_5a8b8 : decode_any W_5a8b8 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8bc : bv 32 := 0x0005c583.
Lemma F_5a8bc : fetch_word Asan.M.loaded_segments (0x5a90c : word) = Some W_5a8bc.
Proof. vm_refl. Qed.
Lemma D_5a8bc : decode_any W_5a8bc = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8c0 : bv 32 := 0x00459593.
Lemma F_5a8c0 : fetch_word Asan.M.loaded_segments (0x5a910 : word) = Some W_5a8c0.
Proof. vm_refl. Qed.
Lemma D_5a8c0 : decode_any W_5a8c0 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8c4 : bv 32 := 0x06058593.
Lemma F_5a8c4 : fetch_word Asan.M.loaded_segments (0x5a914 : word) = Some W_5a8c4.
Proof. vm_refl. Qed.
Lemma D_5a8c4 : decode_any W_5a8c4 = Some (OpImm ALU_ADD 11 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8c8 : bv 32 := 0x0705f593.
Lemma F_5a8c8 : fetch_word Asan.M.loaded_segments (0x5a918 : word) = Some W_5a8c8.
Proof. vm_refl. Qed.
Lemma D_5a8c8 : decode_any W_5a8c8 = Some (OpImm ALU_AND 11 11 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8cc : bv 32 := 0x00090413.
Lemma F_5a8cc : fetch_word Asan.M.loaded_segments (0x5a91c : word) = Some W_5a8cc.
Proof. vm_refl. Qed.
Lemma D_5a8cc : decode_any W_5a8cc = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8d0 : bv 32 := 0xf92570e3.
Lemma F_5a8d0 : fetch_word Asan.M.loaded_segments (0x5a920 : word) = Some W_5a8d0.
Proof. vm_refl. Qed.
Lemma D_5a8d0 : decode_any W_5a8d0 = Some (Branch BC_GEU 10 18 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8d4 : bv 32 := 0xf81ff06f.
Lemma F_5a8d4 : fetch_word Asan.M.loaded_segments (0x5a924 : word) = Some W_5a8d4.
Proof. vm_refl. Qed.
Lemma D_5a8d4 : decode_any W_5a8d4 = Some (Jal 0 2097024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8d8 : bv 32 := 0x06100513.
Lemma F_5a8d8 : fetch_word Asan.M.loaded_segments (0x5a928 : word) = Some W_5a8d8.
Proof. vm_refl. Qed.
Lemma D_5a8d8 : decode_any W_5a8d8 = Some (OpImm ALU_ADD 10 0 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8dc : bv 32 := 0x00aaf663.
Lemma F_5a8dc : fetch_word Asan.M.loaded_segments (0x5a92c : word) = Some W_5a8dc.
Proof. vm_refl. Qed.
Lemma D_5a8dc : decode_any W_5a8dc = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8e0 : bv 32 := 0x00100993.
Lemma F_5a8e0 : fetch_word Asan.M.loaded_segments (0x5a930 : word) = Some W_5a8e0.
Proof. vm_refl. Qed.
Lemma D_5a8e0 : decode_any W_5a8e0 = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8e4 : bv 32 := 0x0600006f.
Lemma F_5a8e4 : fetch_word Asan.M.loaded_segments (0x5a934 : word) = Some W_5a8e4.
Proof. vm_refl. Qed.
Lemma D_5a8e4 : decode_any W_5a8e4 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8e8 : bv 32 := 0x1c100513.
Lemma F_5a8e8 : fetch_word Asan.M.loaded_segments (0x5a938 : word) = Some W_5a8e8.
Proof. vm_refl. Qed.
Lemma D_5a8e8 : decode_any W_5a8e8 = Some (OpImm ALU_ADD 10 0 449, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8ec : bv 32 := 0x00aaf663.
Lemma F_5a8ec : fetch_word Asan.M.loaded_segments (0x5a93c : word) = Some W_5a8ec.
Proof. vm_refl. Qed.
Lemma D_5a8ec : decode_any W_5a8ec = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8f0 : bv 32 := 0x00200993.
Lemma F_5a8f0 : fetch_word Asan.M.loaded_segments (0x5a940 : word) = Some W_5a8f0.
Proof. vm_refl. Qed.
Lemma D_5a8f0 : decode_any W_5a8f0 = Some (OpImm ALU_ADD 19 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8f4 : bv 32 := 0x0500006f.
Lemma F_5a8f4 : fetch_word Asan.M.loaded_segments (0x5a944 : word) = Some W_5a8f4.
Proof. vm_refl. Qed.
Lemma D_5a8f4 : decode_any W_5a8f4 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8f8 : bv 32 := 0x00001537.
Lemma F_5a8f8 : fetch_word Asan.M.loaded_segments (0x5a948 : word) = Some W_5a8f8.
Proof. vm_refl. Qed.
Lemma D_5a8f8 : decode_any W_5a8f8 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a8fc : bv 32 := 0xf815051b.
Lemma F_5a8fc : fetch_word Asan.M.loaded_segments (0x5a94c : word) = Some W_5a8fc.
Proof. vm_refl. Qed.
Lemma D_5a8fc : decode_any W_5a8fc = Some (OpImm32 10 10 3969, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a900 : bv 32 := 0x00aaf663.
Lemma F_5a900 : fetch_word Asan.M.loaded_segments (0x5a950 : word) = Some W_5a900.
Proof. vm_refl. Qed.
Lemma D_5a900 : decode_any W_5a900 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a904 : bv 32 := 0x00300993.
Lemma F_5a904 : fetch_word Asan.M.loaded_segments (0x5a954 : word) = Some W_5a904.
Proof. vm_refl. Qed.
Lemma D_5a904 : decode_any W_5a904 = Some (OpImm ALU_ADD 19 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a908 : bv 32 := 0x03c0006f.
Lemma F_5a908 : fetch_word Asan.M.loaded_segments (0x5a958 : word) = Some W_5a908.
Proof. vm_refl. Qed.
Lemma D_5a908 : decode_any W_5a908 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a90c : bv 32 := 0x00004537.
Lemma F_5a90c : fetch_word Asan.M.loaded_segments (0x5a95c : word) = Some W_5a90c.
Proof. vm_refl. Qed.
Lemma D_5a90c : decode_any W_5a90c = Some (Lui 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a910 : bv 32 := 0xf015051b.
Lemma F_5a910 : fetch_word Asan.M.loaded_segments (0x5a960 : word) = Some W_5a910.
Proof. vm_refl. Qed.
Lemma D_5a910 : decode_any W_5a910 = Some (OpImm32 10 10 3841, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a914 : bv 32 := 0x00aaf663.
Lemma F_5a914 : fetch_word Asan.M.loaded_segments (0x5a964 : word) = Some W_5a914.
Proof. vm_refl. Qed.
Lemma D_5a914 : decode_any W_5a914 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a918 : bv 32 := 0x00400993.
Lemma F_5a918 : fetch_word Asan.M.loaded_segments (0x5a968 : word) = Some W_5a918.
Proof. vm_refl. Qed.
Lemma D_5a918 : decode_any W_5a918 = Some (OpImm ALU_ADD 19 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a91c : bv 32 := 0x0280006f.
Lemma F_5a91c : fetch_word Asan.M.loaded_segments (0x5a96c : word) = Some W_5a91c.
Proof. vm_refl. Qed.
Lemma D_5a91c : decode_any W_5a91c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a920 : bv 32 := 0x00008537.
Lemma F_5a920 : fetch_word Asan.M.loaded_segments (0x5a970 : word) = Some W_5a920.
Proof. vm_refl. Qed.
Lemma D_5a920 : decode_any W_5a920 = Some (Lui 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a924 : bv 32 := 0xe015051b.
Lemma F_5a924 : fetch_word Asan.M.loaded_segments (0x5a974 : word) = Some W_5a924.
Proof. vm_refl. Qed.
Lemma D_5a924 : decode_any W_5a924 = Some (OpImm32 10 10 3585, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a928 : bv 32 := 0x00aaf663.
Lemma F_5a928 : fetch_word Asan.M.loaded_segments (0x5a978 : word) = Some W_5a928.
Proof. vm_refl. Qed.
Lemma D_5a928 : decode_any W_5a928 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a92c : bv 32 := 0x00500993.
Lemma F_5a92c : fetch_word Asan.M.loaded_segments (0x5a97c : word) = Some W_5a92c.
Proof. vm_refl. Qed.
Lemma D_5a92c : decode_any W_5a92c = Some (OpImm ALU_ADD 19 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a930 : bv 32 := 0x0140006f.
Lemma F_5a930 : fetch_word Asan.M.loaded_segments (0x5a980 : word) = Some W_5a930.
Proof. vm_refl. Qed.
Lemma D_5a930 : decode_any W_5a930 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a934 : bv 32 := 0x00010537.
Lemma F_5a934 : fetch_word Asan.M.loaded_segments (0x5a984 : word) = Some W_5a934.
Proof. vm_refl. Qed.
Lemma D_5a934 : decode_any W_5a934 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a938 : bv 32 := 0xc015051b.
Lemma F_5a938 : fetch_word Asan.M.loaded_segments (0x5a988 : word) = Some W_5a938.
Proof. vm_refl. Qed.
Lemma D_5a938 : decode_any W_5a938 = Some (OpImm32 10 10 3073, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a93c : bv 32 := 0x00aab533.
Lemma F_5a93c : fetch_word Asan.M.loaded_segments (0x5a98c : word) = Some W_5a93c.
Proof. vm_refl. Qed.
Lemma D_5a93c : decode_any W_5a93c = Some (Op ALU_SLTU 10 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a940 : bv 32 := 0x00754993.
Lemma F_5a940 : fetch_word Asan.M.loaded_segments (0x5a990 : word) = Some W_5a940.
Proof. vm_refl. Qed.
Lemma D_5a940 : decode_any W_5a940 = Some (OpImm ALU_XOR 19 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a944 : bv 32 := 0x629d1503.
Lemma F_5a944 : fetch_word Asan.M.loaded_segments (0x5a994 : word) = Some W_5a944.
Proof. vm_refl. Qed.
Lemma D_5a944 : decode_any W_5a944 = Some (Load SZ2 true 10 26 1577, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a948 : bv 32 := 0x0230000f.
Lemma F_5a948 : fetch_word Asan.M.loaded_segments (0x5a998 : word) = Some W_5a948.
Proof. vm_refl. Qed.
Lemma D_5a948 : decode_any W_5a948 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a94c : bv 32 := 0x00010a37.
Lemma F_5a94c : fetch_word Asan.M.loaded_segments (0x5a99c : word) = Some W_5a94c.
Proof. vm_refl. Qed.
Lemma D_5a94c : decode_any W_5a94c = Some (Lui 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a950 : bv 32 := 0xfffa0c1b.
Lemma F_5a950 : fetch_word Asan.M.loaded_segments (0x5a9a0 : word) = Some W_5a950.
Proof. vm_refl. Qed.
Lemma D_5a950 : decode_any W_5a950 = Some (OpImm32 24 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a954 : bv 32 := 0x01857533.
Lemma F_5a954 : fetch_word Asan.M.loaded_segments (0x5a9a4 : word) = Some W_5a954.
Proof. vm_refl. Qed.
Lemma D_5a954 : decode_any W_5a954 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a958 : bv 32 := 0x4a0050ef.
Lemma F_5a958 : fetch_word Asan.M.loaded_segments (0x5a9a8 : word) = Some W_5a958.
Proof. vm_refl. Qed.
Lemma D_5a958 : decode_any W_5a958 = Some (Jal 1 21664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a95c : bv 32 := 0x00050493.
Lemma F_5a95c : fetch_word Asan.M.loaded_segments (0x5a9ac : word) = Some W_5a95c.
Proof. vm_refl. Qed.
Lemma D_5a95c : decode_any W_5a95c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a960 : bv 32 := 0x62bd1503.
Lemma F_5a960 : fetch_word Asan.M.loaded_segments (0x5a9b0 : word) = Some W_5a960.
Proof. vm_refl. Qed.
Lemma D_5a960 : decode_any W_5a960 = Some (Load SZ2 true 10 26 1579, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a964 : bv 32 := 0x0230000f.
Lemma F_5a964 : fetch_word Asan.M.loaded_segments (0x5a9b4 : word) = Some W_5a964.
Proof. vm_refl. Qed.
Lemma D_5a964 : decode_any W_5a964 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a968 : bv 32 := 0x01857533.
Lemma F_5a968 : fetch_word Asan.M.loaded_segments (0x5a9b8 : word) = Some W_5a968.
Proof. vm_refl. Qed.
Lemma D_5a968 : decode_any W_5a968 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a96c : bv 32 := 0x48c050ef.
Lemma F_5a96c : fetch_word Asan.M.loaded_segments (0x5a9bc : word) = Some W_5a96c.
Proof. vm_refl. Qed.
Lemma D_5a96c : decode_any W_5a96c = Some (Jal 1 21644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a970 : bv 32 := 0x0b34e663.
Lemma F_5a970 : fetch_word Asan.M.loaded_segments (0x5a9c0 : word) = Some W_5a970.
Proof. vm_refl. Qed.
Lemma D_5a970 : decode_any W_5a970 = Some (Branch BC_LTU 9 19 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a974 : bv 32 := 0x00048993.
Lemma F_5a974 : fetch_word Asan.M.loaded_segments (0x5a9c4 : word) = Some W_5a974.
Proof. vm_refl. Qed.
Lemma D_5a974 : decode_any W_5a974 = Some (OpImm ALU_ADD 19 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a978 : bv 32 := 0x0aa4f463.
Lemma F_5a978 : fetch_word Asan.M.loaded_segments (0x5a9c8 : word) = Some W_5a978.
Proof. vm_refl. Qed.
Lemma D_5a978 : decode_any W_5a978 = Some (Branch BC_GEU 9 10 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a97c : bv 32 := 0x00800593.
Lemma F_5a97c : fetch_word Asan.M.loaded_segments (0x5a9cc : word) = Some W_5a97c.
Proof. vm_refl. Qed.
Lemma D_5a97c : decode_any W_5a97c = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a980 : bv 32 := 0x000a8513.
Lemma F_5a980 : fetch_word Asan.M.loaded_segments (0x5a9d0 : word) = Some W_5a980.
Proof. vm_refl. Qed.
Lemma D_5a980 : decode_any W_5a980 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a984 : bv 32 := 0x0155e463.
Lemma F_5a984 : fetch_word Asan.M.loaded_segments (0x5a9d4 : word) = Some W_5a984.
Proof. vm_refl. Qed.
Lemma D_5a984 : decode_any W_5a984 = Some (Branch BC_LTU 11 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a988 : bv 32 := 0x00800513.
Lemma F_5a988 : fetch_word Asan.M.loaded_segments (0x5a9d8 : word) = Some W_5a988.
Proof. vm_refl. Qed.
Lemma D_5a988 : decode_any W_5a988 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a98c : bv 32 := 0x00850533.
Lemma F_5a98c : fetch_word Asan.M.loaded_segments (0x5a9dc : word) = Some W_5a98c.
Proof. vm_refl. Qed.
Lemma D_5a98c : decode_any W_5a98c = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a990 : bv 32 := 0x40800c33.
Lemma F_5a990 : fetch_word Asan.M.loaded_segments (0x5a9e0 : word) = Some W_5a990.
Proof. vm_refl. Qed.
Lemma D_5a990 : decode_any W_5a990 = Some (Op ALU_SUB 24 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a994 : bv 32 := 0x00993593.
Lemma F_5a994 : fetch_word Asan.M.loaded_segments (0x5a9e4 : word) = Some W_5a994.
Proof. vm_refl. Qed.
Lemma D_5a994 : decode_any W_5a994 = Some (OpImm ALU_SLTU 11 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a998 : bv 32 := 0xfff50513.
Lemma F_5a998 : fetch_word Asan.M.loaded_segments (0x5a9e8 : word) = Some W_5a998.
Proof. vm_refl. Qed.
Lemma D_5a998 : decode_any W_5a998 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a99c : bv 32 := 0xfff58593.
Lemma F_5a99c : fetch_word Asan.M.loaded_segments (0x5a9ec : word) = Some W_5a99c.
Proof. vm_refl. Qed.
Lemma D_5a99c : decode_any W_5a99c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9a0 : bv 32 := 0x01857533.
Lemma F_5a9a0 : fetch_word Asan.M.loaded_segments (0x5a9f0 : word) = Some W_5a9a0.
Proof. vm_refl. Qed.
Lemma D_5a9a0 : decode_any W_5a9a0 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9a4 : bv 32 := 0x0085f5b3.
Lemma F_5a9a4 : fetch_word Asan.M.loaded_segments (0x5a9f4 : word) = Some W_5a9a4.
Proof. vm_refl. Qed.
Lemma D_5a9a4 : decode_any W_5a9a4 = Some (Op ALU_AND 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9a8 : bv 32 := 0x00b50533.
Lemma F_5a9a8 : fetch_word Asan.M.loaded_segments (0x5a9f8 : word) = Some W_5a9a8.
Proof. vm_refl. Qed.
Lemma D_5a9a8 : decode_any W_5a9a8 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9ac : bv 32 := 0x00757593.
Lemma F_5a9ac : fetch_word Asan.M.loaded_segments (0x5a9fc : word) = Some W_5a9ac.
Proof. vm_refl. Qed.
Lemma D_5a9ac : decode_any W_5a9ac = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9b0 : bv 32 := 0x6a059063.
Lemma F_5a9b0 : fetch_word Asan.M.loaded_segments (0x5aa00 : word) = Some W_5a9b0.
Proof. vm_refl. Qed.
Lemma D_5a9b0 : decode_any W_5a9b0 = Some (Branch BC_NE 11 0 1696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9b4 : bv 32 := 0x01000593.
Lemma F_5a9b4 : fetch_word Asan.M.loaded_segments (0x5aa04 : word) = Some W_5a9b4.
Proof. vm_refl. Qed.
Lemma D_5a9b4 : decode_any W_5a9b4 = Some (OpImm ALU_ADD 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9b8 : bv 32 := 0x001ab493.
Lemma F_5a9b8 : fetch_word Asan.M.loaded_segments (0x5aa08 : word) = Some W_5a9b8.
Proof. vm_refl. Qed.
Lemma D_5a9b8 : decode_any W_5a9b8 = Some (OpImm ALU_SLTU 9 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9bc : bv 32 := 0x001a061b.
Lemma F_5a9bc : fetch_word Asan.M.loaded_segments (0x5aa0c : word) = Some W_5a9bc.
Proof. vm_refl. Qed.
Lemma D_5a9bc : decode_any W_5a9bc = Some (OpImm32 12 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9c0 : bv 32 := 0x01359a3b.
Lemma F_5a9c0 : fetch_word Asan.M.loaded_segments (0x5aa10 : word) = Some W_5a9c0.
Proof. vm_refl. Qed.
Lemma D_5a9c0 : decode_any W_5a9c0 = Some (Op32 ALU_SLL 20 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9c4 : bv 32 := 0x00100593.
Lemma F_5a9c4 : fetch_word Asan.M.loaded_segments (0x5aa14 : word) = Some W_5a9c4.
Proof. vm_refl. Qed.
Lemma D_5a9c4 : decode_any W_5a9c4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9c8 : bv 32 := 0x009a84b3.
Lemma F_5a9c8 : fetch_word Asan.M.loaded_segments (0x5aa18 : word) = Some W_5a9c8.
Proof. vm_refl. Qed.
Lemma D_5a9c8 : decode_any W_5a9c8 = Some (Op ALU_ADD 9 21 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9cc : bv 32 := 0x00c936b3.
Lemma F_5a9cc : fetch_word Asan.M.loaded_segments (0x5aa1c : word) = Some W_5a9cc.
Proof. vm_refl. Qed.
Lemma D_5a9cc : decode_any W_5a9cc = Some (Op ALU_SLTU 13 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9d0 : bv 32 := 0x014509b3.
Lemma F_5a9d0 : fetch_word Asan.M.loaded_segments (0x5aa20 : word) = Some W_5a9d0.
Proof. vm_refl. Qed.
Lemma D_5a9d0 : decode_any W_5a9d0 = Some (Op ALU_ADD 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9d4 : bv 32 := 0x00c9b433.
Lemma F_5a9d4 : fetch_word Asan.M.loaded_segments (0x5aa24 : word) = Some W_5a9d4.
Proof. vm_refl. Qed.
Lemma D_5a9d4 : decode_any W_5a9d4 = Some (Op ALU_SLTU 8 19 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9d8 : bv 32 := 0x0086f433.
Lemma F_5a9d8 : fetch_word Asan.M.loaded_segments (0x5aa28 : word) = Some W_5a9d8.
Proof. vm_refl. Qed.
Lemma D_5a9d8 : decode_any W_5a9d8 = Some (Op ALU_AND 8 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9dc : bv 32 := 0xfff40513.
Lemma F_5a9dc : fetch_word Asan.M.loaded_segments (0x5aa2c : word) = Some W_5a9dc.
Proof. vm_refl. Qed.
Lemma D_5a9dc : decode_any W_5a9dc = Some (OpImm ALU_ADD 10 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9e0 : bv 32 := 0x01457633.
Lemma F_5a9e0 : fetch_word Asan.M.loaded_segments (0x5aa30 : word) = Some W_5a9e0.
Proof. vm_refl. Qed.
Lemma D_5a9e0 : decode_any W_5a9e0 = Some (Op ALU_AND 12 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9e4 : bv 32 := 0x02859513.
Lemma F_5a9e4 : fetch_word Asan.M.loaded_segments (0x5aa34 : word) = Some W_5a9e4.
Proof. vm_refl. Qed.
Lemma D_5a9e4 : decode_any W_5a9e4 = Some (ShiftImm ALU_SLL 10 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9e8 : bv 32 := 0x013609b3.
Lemma F_5a9e8 : fetch_word Asan.M.loaded_segments (0x5aa38 : word) = Some W_5a9e8.
Proof. vm_refl. Qed.
Lemma D_5a9e8 : decode_any W_5a9e8 = Some (Op ALU_ADD 19 12 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9ec : bv 32 := 0x01556863.
Lemma F_5a9ec : fetch_word Asan.M.loaded_segments (0x5aa3c : word) = Some W_5a9ec.
Proof. vm_refl. Qed.
Lemma D_5a9ec : decode_any W_5a9ec = Some (Branch BC_LTU 10 21 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9f0 : bv 32 := 0x01356663.
Lemma F_5a9f0 : fetch_word Asan.M.loaded_segments (0x5aa40 : word) = Some W_5a9f0.
Proof. vm_refl. Qed.
Lemma D_5a9f0 : decode_any W_5a9f0 = Some (Branch BC_LTU 10 19 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9f4 : bv 32 := 0x621d3503.
Lemma F_5a9f4 : fetch_word Asan.M.loaded_segments (0x5aa44 : word) = Some W_5a9f4.
Proof. vm_refl. Qed.
Lemma D_5a9f4 : decode_any W_5a9f4 = Some (Load SZ8 true 10 26 1569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5a9f8 : bv 32 := 0x06957063.
Lemma F_5a9f8 : fetch_word Asan.M.loaded_segments (0x5aa48 : word) = Some W_5a9f8.
Proof. vm_refl. Qed.
Lemma D_5a9f8 : decode_any W_5a9f8 = Some (Branch BC_GEU 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa1c : bv 32 := 0xf6a9e0e3.
Lemma F_5aa1c : fetch_word Asan.M.loaded_segments (0x5aa6c : word) = Some W_5aa1c.
Proof. vm_refl. Qed.
Lemma D_5aa1c : decode_any W_5aa1c = Some (Branch BC_LTU 19 10 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa20 : bv 32 := 0x00050993.
Lemma F_5aa20 : fetch_word Asan.M.loaded_segments (0x5aa70 : word) = Some W_5aa20.
Proof. vm_refl. Qed.
Lemma D_5aa20 : decode_any W_5aa20 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa24 : bv 32 := 0x00800593.
Lemma F_5aa24 : fetch_word Asan.M.loaded_segments (0x5aa74 : word) = Some W_5aa24.
Proof. vm_refl. Qed.
Lemma D_5aa24 : decode_any W_5aa24 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa28 : bv 32 := 0x000a8513.
Lemma F_5aa28 : fetch_word Asan.M.loaded_segments (0x5aa78 : word) = Some W_5aa28.
Proof. vm_refl. Qed.
Lemma D_5aa28 : decode_any W_5aa28 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa2c : bv 32 := 0xf555fee3.
Lemma F_5aa2c : fetch_word Asan.M.loaded_segments (0x5aa7c : word) = Some W_5aa2c.
Proof. vm_refl. Qed.
Lemma D_5aa2c : decode_any W_5aa2c = Some (Branch BC_GEU 11 21 8028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa30 : bv 32 := 0xf5dff06f.
Lemma F_5aa30 : fetch_word Asan.M.loaded_segments (0x5aa80 : word) = Some W_5aa30.
Proof. vm_refl. Qed.
Lemma D_5aa30 : decode_any W_5aa30 = Some (Jal 0 2096988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa58 : bv 32 := 0x3e8310ef.
Lemma F_5aa58 : fetch_word Asan.M.loaded_segments (0x5aaa8 : word) = Some W_5aa58.
Proof. vm_refl. Qed.
Lemma D_5aa58 : decode_any W_5aa58 = Some (Jal 1 201704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa5c : bv 32 := 0x00050d13.
Lemma F_5aa5c : fetch_word Asan.M.loaded_segments (0x5aaac : word) = Some W_5aa5c.
Proof. vm_refl. Qed.
Lemma D_5aa5c : decode_any W_5aa5c = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa60 : bv 32 := 0x08050863.
Lemma F_5aa60 : fetch_word Asan.M.loaded_segments (0x5aab0 : word) = Some W_5aa60.
Proof. vm_refl. Qed.
Lemma D_5aa60 : decode_any W_5aa60 = Some (Branch BC_EQ 10 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa64 : bv 32 := 0x0d0d0593.
Lemma F_5aa64 : fetch_word Asan.M.loaded_segments (0x5aab4 : word) = Some W_5aa64.
Proof. vm_refl. Qed.
Lemma D_5aa64 : decode_any W_5aa64 = Some (OpImm ALU_ADD 11 26 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa68 : bv 32 := 0x00800693.
Lemma F_5aa68 : fetch_word Asan.M.loaded_segments (0x5aab8 : word) = Some W_5aa68.
Proof. vm_refl. Qed.
Lemma D_5aa68 : decode_any W_5aa68 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa6c : bv 32 := 0x000b0513.
Lemma F_5aa6c : fetch_word Asan.M.loaded_segments (0x5aabc : word) = Some W_5aa6c.
Proof. vm_refl. Qed.
Lemma D_5aa6c : decode_any W_5aa6c = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa70 : bv 32 := 0x00098613.
Lemma F_5aa70 : fetch_word Asan.M.loaded_segments (0x5aac0 : word) = Some W_5aa70.
Proof. vm_refl. Qed.
Lemma D_5aa70 : decode_any W_5aa70 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa74 : bv 32 := 0x4bc040ef.
Lemma F_5aa74 : fetch_word Asan.M.loaded_segments (0x5aac4 : word) = Some W_5aa74.
Proof. vm_refl. Qed.
Lemma D_5aa74 : decode_any W_5aa74 = Some (Jal 1 17596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa78 : bv 32 := 0x00050913.
Lemma F_5aa78 : fetch_word Asan.M.loaded_segments (0x5aac8 : word) = Some W_5aa78.
Proof. vm_refl. Qed.
Lemma D_5aa78 : decode_any W_5aa78 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa7c : bv 32 := 0x0c050663.
Lemma F_5aa7c : fetch_word Asan.M.loaded_segments (0x5aacc : word) = Some W_5aa7c.
Proof. vm_refl. Qed.
Lemma D_5aa7c : decode_any W_5aa7c = Some (Branch BC_EQ 10 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa80 : bv 32 := 0x01490a33.
Lemma F_5aa80 : fetch_word Asan.M.loaded_segments (0x5aad0 : word) = Some W_5aa80.
Proof. vm_refl. Qed.
Lemma D_5aa80 : decode_any W_5aa80 = Some (Op ALU_ADD 20 18 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa84 : bv 32 := 0x019a7533.
Lemma F_5aa84 : fetch_word Asan.M.loaded_segments (0x5aad4 : word) = Some W_5aa84.
Proof. vm_refl. Qed.
Lemma D_5aa84 : decode_any W_5aa84 = Some (Op ALU_AND 10 20 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa88 : bv 32 := 0x01298733.
Lemma F_5aa88 : fetch_word Asan.M.loaded_segments (0x5aad8 : word) = Some W_5aa88.
Proof. vm_refl. Qed.
Lemma D_5aa88 : decode_any W_5aa88 = Some (Op ALU_ADD 14 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa8c : bv 32 := 0x00050663.
Lemma F_5aa8c : fetch_word Asan.M.loaded_segments (0x5aadc : word) = Some W_5aa8c.
Proof. vm_refl. Qed.
Lemma D_5aa8c : decode_any W_5aa8c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa98 : bv 32 := 0x009a0cb3.
Lemma F_5aa98 : fetch_word Asan.M.loaded_segments (0x5aae8 : word) = Some W_5aa98.
Proof. vm_refl. Qed.
Lemma D_5aa98 : decode_any W_5aa98 = Some (Op ALU_ADD 25 20 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aa9c : bv 32 := 0x5d976a63.
Lemma F_5aa9c : fetch_word Asan.M.loaded_segments (0x5aaec : word) = Some W_5aa9c.
Proof. vm_refl. Qed.
Lemma D_5aa9c : decode_any W_5aa9c = Some (Branch BC_LTU 14 25 1492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aaa0 : bv 32 := 0xff1a4503.
Lemma F_5aaa0 : fetch_word Asan.M.loaded_segments (0x5aaf0 : word) = Some W_5aaa0.
Proof. vm_refl. Qed.
Lemma D_5aaa0 : decode_any W_5aaa0 = Some (Load SZ1 false 10 20 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aaa4 : bv 32 := 0x003df593.
Lemma F_5aaa4 : fetch_word Asan.M.loaded_segments (0x5aaf4 : word) = Some W_5aaa4.
Proof. vm_refl. Qed.
Lemma D_5aaa4 : decode_any W_5aaa4 = Some (OpImm ALU_AND 11 27 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aaa8 : bv 32 := 0xffc57513.
Lemma F_5aaa8 : fetch_word Asan.M.loaded_segments (0x5aaf8 : word) = Some W_5aaa8.
Proof. vm_refl. Qed.
Lemma D_5aaa8 : decode_any W_5aaa8 = Some (OpImm ALU_AND 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aaac : bv 32 := 0x00b56533.
Lemma F_5aaac : fetch_word Asan.M.loaded_segments (0x5aafc : word) = Some W_5aaac.
Proof. vm_refl. Qed.
Lemma D_5aaac : decode_any W_5aaac = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aab0 : bv 32 := 0x0204d593.
Lemma F_5aab0 : fetch_word Asan.M.loaded_segments (0x5ab00 : word) = Some W_5aab0.
Proof. vm_refl. Qed.
Lemma D_5aab0 : decode_any W_5aab0 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aab4 : bv 32 := 0x030ad613.
Lemma F_5aab4 : fetch_word Asan.M.loaded_segments (0x5ab04 : word) = Some W_5aab4.
Proof. vm_refl. Qed.
Lemma D_5aab4 : decode_any W_5aab4 = Some (ShiftImm ALU_SRL 12 21 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aab8 : bv 32 := 0xfeaa08a3.
Lemma F_5aab8 : fetch_word Asan.M.loaded_segments (0x5ab08 : word) = Some W_5aab8.
Proof. vm_refl. Qed.
Lemma D_5aab8 : decode_any W_5aab8 = Some (Store SZ1 20 10 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aabc : bv 32 := 0xfeba1923.
Lemma F_5aabc : fetch_word Asan.M.loaded_segments (0x5ab0c : word) = Some W_5aabc.
Proof. vm_refl. Qed.
Lemma D_5aabc : decode_any W_5aabc = Some (Store SZ2 20 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aac0 : bv 32 := 0xfe9a2a23.
Lemma F_5aac0 : fetch_word Asan.M.loaded_segments (0x5ab10 : word) = Some W_5aac0.
Proof. vm_refl. Qed.
Lemma D_5aac0 : decode_any W_5aac0 = Some (Store SZ4 20 9 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aac4 : bv 32 := 0x5c061463.
Lemma F_5aac4 : fetch_word Asan.M.loaded_segments (0x5ab14 : word) = Some W_5aac4.
Proof. vm_refl. Qed.
Lemma D_5aac4 : decode_any W_5aac4 = Some (Branch BC_NE 12 0 1480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aac8 : bv 32 := 0xff0a0a93.
Lemma F_5aac8 : fetch_word Asan.M.loaded_segments (0x5ab18 : word) = Some W_5aac8.
Proof. vm_refl. Qed.
Lemma D_5aac8 : decode_any W_5aac8 = Some (OpImm ALU_ADD 21 20 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aacc : bv 32 := 0x08f57513.
Lemma F_5aacc : fetch_word Asan.M.loaded_segments (0x5ab1c : word) = Some W_5aacc.
Proof. vm_refl. Qed.
Lemma D_5aacc : decode_any W_5aacc = Some (OpImm ALU_AND 10 10 143, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aad0 : bv 32 := 0x01013583.
Lemma F_5aad0 : fetch_word Asan.M.loaded_segments (0x5ab20 : word) = Some W_5aad0.
Proof. vm_refl. Qed.
Lemma D_5aad0 : decode_any W_5aad0 = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aad4 : bv 32 := 0x00b56533.
Lemma F_5aad4 : fetch_word Asan.M.loaded_segments (0x5ab24 : word) = Some W_5aad4.
Proof. vm_refl. Qed.
Lemma D_5aad4 : decode_any W_5aad4 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aad8 : bv 32 := 0x00aa80a3.
Lemma F_5aad8 : fetch_word Asan.M.loaded_segments (0x5ab28 : word) = Some W_5aad8.
Proof. vm_refl. Qed.
Lemma D_5aad8 : decode_any W_5aad8 = Some (Store SZ1 21 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aadc : bv 32 := 0x080d0c63.
Lemma F_5aadc : fetch_word Asan.M.loaded_segments (0x5ab2c : word) = Some W_5aadc.
Proof. vm_refl. Qed.
Lemma D_5aadc : decode_any W_5aadc = Some (Branch BC_EQ 26 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aae0 : bv 32 := 0x000d3503.
Lemma F_5aae0 : fetch_word Asan.M.loaded_segments (0x5ab30 : word) = Some W_5aae0.
Proof. vm_refl. Qed.
Lemma D_5aae0 : decode_any W_5aae0 = Some (Load SZ8 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aae4 : bv 32 := 0x00852c03.
Lemma F_5aae4 : fetch_word Asan.M.loaded_segments (0x5ab34 : word) = Some W_5aae4.
Proof. vm_refl. Qed.
Lemma D_5aae4 : decode_any W_5aae4 = Some (Load SZ4 true 24 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aae8 : bv 32 := 0x020c1c13.
Lemma F_5aae8 : fetch_word Asan.M.loaded_segments (0x5ab38 : word) = Some W_5aae8.
Proof. vm_refl. Qed.
Lemma D_5aae8 : decode_any W_5aae8 = Some (ShiftImm ALU_SLL 24 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aaec : bv 32 := 0x08c0006f.
Lemma F_5aaec : fetch_word Asan.M.loaded_segments (0x5ab3c : word) = Some W_5aaec.
Proof. vm_refl. Qed.
Lemma D_5aaec : decode_any W_5aaec = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ab78 : bv 32 := 0x000bb503.
Lemma F_5ab78 : fetch_word Asan.M.loaded_segments (0x5abc8 : word) = Some W_5ab78.
Proof. vm_refl. Qed.
Lemma D_5ab78 : decode_any W_5ab78 = Some (Load SZ8 true 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ab7c : bv 32 := 0x008bb583.
Lemma F_5ab7c : fetch_word Asan.M.loaded_segments (0x5abcc : word) = Some W_5ab7c.
Proof. vm_refl. Qed.
Lemma D_5ab7c : decode_any W_5ab7c = Some (Load SZ8 true 11 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ab80 : bv 32 := 0x1a1470ef.
Lemma F_5ab80 : fetch_word Asan.M.loaded_segments (0x5abd0 : word) = Some W_5ab80.
Proof. vm_refl. Qed.
Lemma D_5ab80 : decode_any W_5ab80 = Some (Jal 1 293280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ab84 : bv 32 := 0x02051513.
Lemma F_5ab84 : fetch_word Asan.M.loaded_segments (0x5abd4 : word) = Some W_5ab84.
Proof. vm_refl. Qed.
Lemma D_5ab84 : decode_any W_5ab84 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ab88 : bv 32 := 0x02055513.
Lemma F_5ab88 : fetch_word Asan.M.loaded_segments (0x5abd8 : word) = Some W_5ab88.
Proof. vm_refl. Qed.
Lemma D_5ab88 : decode_any W_5ab88 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ab8c : bv 32 := 0x00ac6533.
Lemma F_5ab8c : fetch_word Asan.M.loaded_segments (0x5abdc : word) = Some W_5ab8c.
Proof. vm_refl. Qed.
Lemma D_5ab8c : decode_any W_5ab8c = Some (Op ALU_OR 10 24 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ab90 : bv 32 := 0x00aab423.
Lemma F_5ab90 : fetch_word Asan.M.loaded_segments (0x5abe0 : word) = Some W_5ab90.
Proof. vm_refl. Qed.
Lemma D_5ab90 : decode_any W_5ab90 = Some (Store SZ8 21 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ab94 : bv 32 := 0x02040063.
Lemma F_5ab94 : fetch_word Asan.M.loaded_segments (0x5abe4 : word) = Some W_5ab94.
Proof. vm_refl. Qed.
Lemma D_5ab94 : decode_any W_5ab94 = Some (Branch BC_EQ 8 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ab98 : bv 32 := 0x00106517.
Lemma F_5ab98 : fetch_word Asan.M.loaded_segments (0x5abe8 : word) = Some W_5ab98.
Proof. vm_refl. Qed.
Lemma D_5ab98 : decode_any W_5ab98 = Some (Auipc 10 262, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ab9c : bv 32 := 0x03053503.
Lemma F_5ab9c : fetch_word Asan.M.loaded_segments (0x5abec : word) = Some W_5ab9c.
Proof. vm_refl. Qed.
Lemma D_5ab9c : decode_any W_5ab9c = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aba0 : bv 32 := 0x00053503.
Lemma F_5aba0 : fetch_word Asan.M.loaded_segments (0x5abf0 : word) = Some W_5aba0.
Proof. vm_refl. Qed.
Lemma D_5aba0 : decode_any W_5aba0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aba4 : bv 32 := 0x00395593.
Lemma F_5aba4 : fetch_word Asan.M.loaded_segments (0x5abf4 : word) = Some W_5aba4.
Proof. vm_refl. Qed.
Lemma D_5aba4 : decode_any W_5aba4 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aba8 : bv 32 := 0x00b50533.
Lemma F_5aba8 : fetch_word Asan.M.loaded_segments (0x5abf8 : word) = Some W_5aba8.
Proof. vm_refl. Qed.
Lemma D_5aba8 : decode_any W_5aba8 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abac : bv 32 := 0x00054503.
Lemma F_5abac : fetch_word Asan.M.loaded_segments (0x5abfc : word) = Some W_5abac.
Proof. vm_refl. Qed.
Lemma D_5abac : decode_any W_5abac = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abb0 : bv 32 := 0x0c051063.
Lemma F_5abb0 : fetch_word Asan.M.loaded_segments (0x5ac00 : word) = Some W_5abb0.
Proof. vm_refl. Qed.
Lemma D_5abb0 : decode_any W_5abb0 = Some (Branch BC_NE 10 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abb4 : bv 32 := 0x020b3503.
Lemma F_5abb4 : fetch_word Asan.M.loaded_segments (0x5ac04 : word) = Some W_5abb4.
Proof. vm_refl. Qed.
Lemma D_5abb4 : decode_any W_5abb4 = Some (Load SZ8 true 10 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abb8 : bv 32 := 0x02a96c63.
Lemma F_5abb8 : fetch_word Asan.M.loaded_segments (0x5ac08 : word) = Some W_5abb8.
Proof. vm_refl. Qed.
Lemma D_5abb8 : decode_any W_5abb8 = Some (Branch BC_LTU 18 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abbc : bv 32 := 0x00100593.
Lemma F_5abbc : fetch_word Asan.M.loaded_segments (0x5ac0c : word) = Some W_5abbc.
Proof. vm_refl. Qed.
Lemma D_5abbc : decode_any W_5abbc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abc0 : bv 32 := 0x02559593.
Lemma F_5abc0 : fetch_word Asan.M.loaded_segments (0x5ac10 : word) = Some W_5abc0.
Proof. vm_refl. Qed.
Lemma D_5abc0 : decode_any W_5abc0 = Some (ShiftImm ALU_SLL 11 11 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abc4 : bv 32 := 0x00b505b3.
Lemma F_5abc4 : fetch_word Asan.M.loaded_segments (0x5ac14 : word) = Some W_5abc4.
Proof. vm_refl. Qed.
Lemma D_5abc4 : decode_any W_5abc4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abc8 : bv 32 := 0x02b97463.
Lemma F_5abc8 : fetch_word Asan.M.loaded_segments (0x5ac18 : word) = Some W_5abc8.
Proof. vm_refl. Qed.
Lemma D_5abc8 : decode_any W_5abc8 = Some (Branch BC_GEU 18 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abf0 : bv 32 := 0x040b3503.
Lemma F_5abf0 : fetch_word Asan.M.loaded_segments (0x5ac40 : word) = Some W_5abf0.
Proof. vm_refl. Qed.
Lemma D_5abf0 : decode_any W_5abf0 = Some (Load SZ8 true 10 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abf4 : bv 32 := 0xfff50593.
Lemma F_5abf4 : fetch_word Asan.M.loaded_segments (0x5ac44 : word) = Some W_5abf4.
Proof. vm_refl. Qed.
Lemma D_5abf4 : decode_any W_5abf4 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abf8 : bv 32 := 0x0125f633.
Lemma F_5abf8 : fetch_word Asan.M.loaded_segments (0x5ac48 : word) = Some W_5abf8.
Proof. vm_refl. Qed.
Lemma D_5abf8 : decode_any W_5abf8 = Some (Op ALU_AND 12 11 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5abfc : bv 32 := 0x52061663.
Lemma F_5abfc : fetch_word Asan.M.loaded_segments (0x5ac4c : word) = Some W_5abfc.
Proof. vm_refl. Qed.
Lemma D_5abfc : decode_any W_5abfc = Some (Branch BC_NE 12 0 1324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac00 : bv 32 := 0x00b57633.
Lemma F_5ac00 : fetch_word Asan.M.loaded_segments (0x5ac50 : word) = Some W_5ac00.
Proof. vm_refl. Qed.
Lemma D_5ac00 : decode_any W_5ac00 = Some (Op ALU_AND 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac04 : bv 32 := 0x54061663.
Lemma F_5ac04 : fetch_word Asan.M.loaded_segments (0x5ac54 : word) = Some W_5ac04.
Proof. vm_refl. Qed.
Lemma D_5ac04 : decode_any W_5ac04 = Some (Branch BC_NE 12 0 1356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac08 : bv 32 := 0x40a90633.
Lemma F_5ac08 : fetch_word Asan.M.loaded_segments (0x5ac58 : word) = Some W_5ac08.
Proof. vm_refl. Qed.
Lemma D_5ac08 : decode_any W_5ac08 = Some (Op ALU_SUB 12 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac0c : bv 32 := 0x01063603.
Lemma F_5ac0c : fetch_word Asan.M.loaded_segments (0x5ac5c : word) = Some W_5ac0c.
Proof. vm_refl. Qed.
Lemma D_5ac0c : decode_any W_5ac0c = Some (Load SZ8 true 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac10 : bv 32 := 0x00b605b3.
Lemma F_5ac10 : fetch_word Asan.M.loaded_segments (0x5ac60 : word) = Some W_5ac10.
Proof. vm_refl. Qed.
Lemma D_5ac10 : decode_any W_5ac10 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac14 : bv 32 := 0x40a00433.
Lemma F_5ac14 : fetch_word Asan.M.loaded_segments (0x5ac64 : word) = Some W_5ac14.
Proof. vm_refl. Qed.
Lemma D_5ac14 : decode_any W_5ac14 = Some (Op ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac18 : bv 32 := 0x0085f433.
Lemma F_5ac18 : fetch_word Asan.M.loaded_segments (0x5ac68 : word) = Some W_5ac18.
Proof. vm_refl. Qed.
Lemma D_5ac18 : decode_any W_5ac18 = Some (Op ALU_AND 8 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac1c : bv 32 := 0x0280006f.
Lemma F_5ac1c : fetch_word Asan.M.loaded_segments (0x5ac6c : word) = Some W_5ac1c.
Proof. vm_refl. Qed.
Lemma D_5ac1c : decode_any W_5ac1c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac44 : bv 32 := 0x007c8c93.
Lemma F_5ac44 : fetch_word Asan.M.loaded_segments (0x5ac94 : word) = Some W_5ac44.
Proof. vm_refl. Qed.
Lemma D_5ac44 : decode_any W_5ac44 = Some (OpImm ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac48 : bv 32 := 0xff8cfb13.
Lemma F_5ac48 : fetch_word Asan.M.loaded_segments (0x5ac98 : word) = Some W_5ac48.
Proof. vm_refl. Qed.
Lemma D_5ac48 : decode_any W_5ac48 = Some (OpImm ALU_AND 22 25 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac4c : bv 32 := 0x412a05b3.
Lemma F_5ac4c : fetch_word Asan.M.loaded_segments (0x5ac9c : word) = Some W_5ac4c.
Proof. vm_refl. Qed.
Lemma D_5ac4c : decode_any W_5ac4c = Some (Op ALU_SUB 11 20 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac50 : bv 32 := 0x0fa00613.
Lemma F_5ac50 : fetch_word Asan.M.loaded_segments (0x5aca0 : word) = Some W_5ac50.
Proof. vm_refl. Qed.
Lemma D_5ac50 : decode_any W_5ac50 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac54 : bv 32 := 0x00090513.
Lemma F_5ac54 : fetch_word Asan.M.loaded_segments (0x5aca4 : word) = Some W_5ac54.
Proof. vm_refl. Qed.
Lemma D_5ac54 : decode_any W_5ac54 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac58 : bv 32 := 0x43c280ef.
Lemma F_5ac58 : fetch_word Asan.M.loaded_segments (0x5aca8 : word) = Some W_5ac58.
Proof. vm_refl. Qed.
Lemma D_5ac58 : decode_any W_5ac58 = Some (Jal 1 164924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac5c : bv 32 := 0x416905b3.
Lemma F_5ac5c : fetch_word Asan.M.loaded_segments (0x5acac : word) = Some W_5ac5c.
Proof. vm_refl. Qed.
Lemma D_5ac5c : decode_any W_5ac5c = Some (Op ALU_SUB 11 18 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac60 : bv 32 := 0x008585b3.
Lemma F_5ac60 : fetch_word Asan.M.loaded_segments (0x5acb0 : word) = Some W_5ac60.
Proof. vm_refl. Qed.
Lemma D_5ac60 : decode_any W_5ac60 = Some (Op ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac64 : bv 32 := 0x0fa00613.
Lemma F_5ac64 : fetch_word Asan.M.loaded_segments (0x5acb4 : word) = Some W_5ac64.
Proof. vm_refl. Qed.
Lemma D_5ac64 : decode_any W_5ac64 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac68 : bv 32 := 0x000b0513.
Lemma F_5ac68 : fetch_word Asan.M.loaded_segments (0x5acb8 : word) = Some W_5ac68.
Proof. vm_refl. Qed.
Lemma D_5ac68 : decode_any W_5ac68 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac6c : bv 32 := 0x428280ef.
Lemma F_5ac6c : fetch_word Asan.M.loaded_segments (0x5acbc : word) = Some W_5ac6c.
Proof. vm_refl. Qed.
Lemma D_5ac6c : decode_any W_5ac6c = Some (Jal 1 164904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac70 : bv 32 := 0xfff80537.
Lemma F_5ac70 : fetch_word Asan.M.loaded_segments (0x5acc0 : word) = Some W_5ac70.
Proof. vm_refl. Qed.
Lemma D_5ac70 : decode_any W_5ac70 = Some (Lui 10 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac74 : bv 32 := 0x01055513.
Lemma F_5ac74 : fetch_word Asan.M.loaded_segments (0x5acc4 : word) = Some W_5ac74.
Proof. vm_refl. Qed.
Lemma D_5ac74 : decode_any W_5ac74 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac78 : bv 32 := 0x00a4fb33.
Lemma F_5ac78 : fetch_word Asan.M.loaded_segments (0x5acc8 : word) = Some W_5ac78.
Proof. vm_refl. Qed.
Lemma D_5ac78 : decode_any W_5ac78 = Some (Op ALU_AND 22 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac7c : bv 32 := 0x000b0a63.
Lemma F_5ac7c : fetch_word Asan.M.loaded_segments (0x5accc : word) = Some W_5ac7c.
Proof. vm_refl. Qed.
Lemma D_5ac7c : decode_any W_5ac7c = Some (Branch BC_EQ 22 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac80 : bv 32 := 0x000a0513.
Lemma F_5ac80 : fetch_word Asan.M.loaded_segments (0x5acd0 : word) = Some W_5ac80.
Proof. vm_refl. Qed.
Lemma D_5ac80 : decode_any W_5ac80 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac84 : bv 32 := 0x000b0593.
Lemma F_5ac84 : fetch_word Asan.M.loaded_segments (0x5acd4 : word) = Some W_5ac84.
Proof. vm_refl. Qed.
Lemma D_5ac84 : decode_any W_5ac84 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac88 : bv 32 := 0x00000613.
Lemma F_5ac88 : fetch_word Asan.M.loaded_segments (0x5acd8 : word) = Some W_5ac88.
Proof. vm_refl. Qed.
Lemma D_5ac88 : decode_any W_5ac88 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac8c : bv 32 := 0x408280ef.
Lemma F_5ac8c : fetch_word Asan.M.loaded_segments (0x5acdc : word) = Some W_5ac8c.
Proof. vm_refl. Qed.
Lemma D_5ac8c : decode_any W_5ac8c = Some (Jal 1 164872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac90 : bv 32 := 0x09648a63.
Lemma F_5ac90 : fetch_word Asan.M.loaded_segments (0x5ace0 : word) = Some W_5ac90.
Proof. vm_refl. Qed.
Lemma D_5ac90 : decode_any W_5ac90 = Some (Branch BC_EQ 9 22 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac94 : bv 32 := 0x3ec280ef.
Lemma F_5ac94 : fetch_word Asan.M.loaded_segments (0x5ace4 : word) = Some W_5ac94.
Proof. vm_refl. Qed.
Lemma D_5ac94 : decode_any W_5ac94 = Some (Jal 1 164844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac98 : bv 32 := 0x08050663.
Lemma F_5ac98 : fetch_word Asan.M.loaded_segments (0x5ace8 : word) = Some W_5ac98.
Proof. vm_refl. Qed.
Lemma D_5ac98 : decode_any W_5ac98 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ac9c : bv 32 := 0x00106517.
Lemma F_5ac9c : fetch_word Asan.M.loaded_segments (0x5acec : word) = Some W_5ac9c.
Proof. vm_refl. Qed.
Lemma D_5ac9c : decode_any W_5ac9c = Some (Auipc 10 262, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aca0 : bv 32 := 0xf2c53503.
Lemma F_5aca0 : fetch_word Asan.M.loaded_segments (0x5acf0 : word) = Some W_5aca0.
Proof. vm_refl. Qed.
Lemma D_5aca0 : decode_any W_5aca0 = Some (Load SZ8 true 10 10 3884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aca4 : bv 32 := 0x00053503.
Lemma F_5aca4 : fetch_word Asan.M.loaded_segments (0x5acf4 : word) = Some W_5aca4.
Proof. vm_refl. Qed.
Lemma D_5aca4 : decode_any W_5aca4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aca8 : bv 32 := 0x016a0b33.
Lemma F_5aca8 : fetch_word Asan.M.loaded_segments (0x5acf8 : word) = Some W_5aca8.
Proof. vm_refl. Qed.
Lemma D_5aca8 : decode_any W_5aca8 = Some (Op ALU_ADD 22 20 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acac : bv 32 := 0xfff50593.
Lemma F_5acac : fetch_word Asan.M.loaded_segments (0x5acfc : word) = Some W_5acac.
Proof. vm_refl. Qed.
Lemma D_5acac : decode_any W_5acac = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acb0 : bv 32 := 0x00b53633.
Lemma F_5acb0 : fetch_word Asan.M.loaded_segments (0x5ad00 : word) = Some W_5acb0.
Proof. vm_refl. Qed.
Lemma D_5acb0 : decode_any W_5acb0 = Some (Op ALU_SLTU 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acb4 : bv 32 := 0xfff60613.
Lemma F_5acb4 : fetch_word Asan.M.loaded_segments (0x5ad04 : word) = Some W_5acb4.
Proof. vm_refl. Qed.
Lemma D_5acb4 : decode_any W_5acb4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acb8 : bv 32 := 0x00b67633.
Lemma F_5acb8 : fetch_word Asan.M.loaded_segments (0x5ad08 : word) = Some W_5acb8.
Proof. vm_refl. Qed.
Lemma D_5acb8 : decode_any W_5acb8 = Some (Op ALU_AND 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acbc : bv 32 := 0x05667263.
Lemma F_5acbc : fetch_word Asan.M.loaded_segments (0x5ad0c : word) = Some W_5acbc.
Proof. vm_refl. Qed.
Lemma D_5acbc : decode_any W_5acbc = Some (Branch BC_GEU 12 22 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acc0 : bv 32 := 0x00106617.
Lemma F_5acc0 : fetch_word Asan.M.loaded_segments (0x5ad10 : word) = Some W_5acc0.
Proof. vm_refl. Qed.
Lemma D_5acc0 : decode_any W_5acc0 = Some (Auipc 12 262, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acc4 : bv 32 := 0xf1063603.
Lemma F_5acc4 : fetch_word Asan.M.loaded_segments (0x5ad14 : word) = Some W_5acc4.
Proof. vm_refl. Qed.
Lemma D_5acc4 : decode_any W_5acc4 = Some (Load SZ8 true 12 12 3856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acc8 : bv 32 := 0x00106697.
Lemma F_5acc8 : fetch_word Asan.M.loaded_segments (0x5ad18 : word) = Some W_5acc8.
Proof. vm_refl. Qed.
Lemma D_5acc8 : decode_any W_5acc8 = Some (Auipc 13 262, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5accc : bv 32 := 0xf106b683.
Lemma F_5accc : fetch_word Asan.M.loaded_segments (0x5ad1c : word) = Some W_5accc.
Proof. vm_refl. Qed.
Lemma D_5accc : decode_any W_5accc = Some (Load SZ8 true 13 13 3856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acd0 : bv 32 := 0x00063783.
Lemma F_5acd0 : fetch_word Asan.M.loaded_segments (0x5ad20 : word) = Some W_5acd0.
Proof. vm_refl. Qed.
Lemma D_5acd0 : decode_any W_5acd0 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acd4 : bv 32 := 0x0006b603.
Lemma F_5acd4 : fetch_word Asan.M.loaded_segments (0x5ad24 : word) = Some W_5acd4.
Proof. vm_refl. Qed.
Lemma D_5acd4 : decode_any W_5acd4 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acd8 : bv 32 := 0xfff78713.
Lemma F_5acd8 : fetch_word Asan.M.loaded_segments (0x5ad28 : word) = Some W_5acd8.
Proof. vm_refl. Qed.
Lemma D_5acd8 : decode_any W_5acd8 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acdc : bv 32 := 0x01677463.
Lemma F_5acdc : fetch_word Asan.M.loaded_segments (0x5ad2c : word) = Some W_5acdc.
Proof. vm_refl. Qed.
Lemma D_5acdc : decode_any W_5acdc = Some (Branch BC_GEU 14 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ace4 : bv 32 := 0x00106697.
Lemma F_5ace4 : fetch_word Asan.M.loaded_segments (0x5ad34 : word) = Some W_5ace4.
Proof. vm_refl. Qed.
Lemma D_5ace4 : decode_any W_5ace4 = Some (Auipc 13 262, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ace8 : bv 32 := 0xefc6b683.
Lemma F_5ace8 : fetch_word Asan.M.loaded_segments (0x5ad38 : word) = Some W_5ace8.
Proof. vm_refl. Qed.
Lemma D_5ace8 : decode_any W_5ace8 = Some (Load SZ8 true 13 13 3836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acec : bv 32 := 0x0006b883.
Lemma F_5acec : fetch_word Asan.M.loaded_segments (0x5ad3c : word) = Some W_5acec.
Proof. vm_refl. Qed.
Lemma D_5acec : decode_any W_5acec = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acf0 : bv 32 := 0x0038d693.
Lemma F_5acf0 : fetch_word Asan.M.loaded_segments (0x5ad40 : word) = Some W_5acf0.
Proof. vm_refl. Qed.
Lemma D_5acf0 : decode_any W_5acf0 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acf4 : bv 32 := 0x00a68833.
Lemma F_5acf4 : fetch_word Asan.M.loaded_segments (0x5ad44 : word) = Some W_5acf4.
Proof. vm_refl. Qed.
Lemma D_5acf4 : decode_any W_5acf4 = Some (Op ALU_ADD 16 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acf8 : bv 32 := 0x2568ea63.
Lemma F_5acf8 : fetch_word Asan.M.loaded_segments (0x5ad48 : word) = Some W_5acf8.
Proof. vm_refl. Qed.
Lemma D_5acf8 : decode_any W_5acf8 = Some (Branch BC_LTU 17 22 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5acfc : bv 32 := 0x25687863.
Lemma F_5acfc : fetch_word Asan.M.loaded_segments (0x5ad4c : word) = Some W_5acfc.
Proof. vm_refl. Qed.
Lemma D_5acfc : decode_any W_5acfc = Some (Branch BC_GEU 16 22 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad00 : bv 32 := 0x00106597.
Lemma F_5ad00 : fetch_word Asan.M.loaded_segments (0x5ad50 : word) = Some W_5ad00.
Proof. vm_refl. Qed.
Lemma D_5ad00 : decode_any W_5ad00 = Some (Auipc 11 262, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad04 : bv 32 := 0xec05b583.
Lemma F_5ad04 : fetch_word Asan.M.loaded_segments (0x5ad54 : word) = Some W_5ad04.
Proof. vm_refl. Qed.
Lemma D_5ad04 : decode_any W_5ad04 = Some (Load SZ8 true 11 11 3776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad08 : bv 32 := 0x0555c583.
Lemma F_5ad08 : fetch_word Asan.M.loaded_segments (0x5ad58 : word) = Some W_5ad08.
Proof. vm_refl. Qed.
Lemma D_5ad08 : decode_any W_5ad08 = Some (Load SZ1 false 11 11 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad0c : bv 32 := 0x003b5613.
Lemma F_5ad0c : fetch_word Asan.M.loaded_segments (0x5ad5c : word) = Some W_5ad0c.
Proof. vm_refl. Qed.
Lemma D_5ad0c : decode_any W_5ad0c = Some (ShiftImm ALU_SRL 12 22 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad10 : bv 32 := 0x00c50533.
Lemma F_5ad10 : fetch_word Asan.M.loaded_segments (0x5ad60 : word) = Some W_5ad10.
Proof. vm_refl. Qed.
Lemma D_5ad10 : decode_any W_5ad10 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad14 : bv 32 := 0x40b005bb.
Lemma F_5ad14 : fetch_word Asan.M.loaded_segments (0x5ad64 : word) = Some W_5ad14.
Proof. vm_refl. Qed.
Lemma D_5ad14 : decode_any W_5ad14 = Some (Op32 ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad18 : bv 32 := 0x00b4f5b3.
Lemma F_5ad18 : fetch_word Asan.M.loaded_segments (0x5ad68 : word) = Some W_5ad18.
Proof. vm_refl. Qed.
Lemma D_5ad18 : decode_any W_5ad18 = Some (Op ALU_AND 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad1c : bv 32 := 0x0075f593.
Lemma F_5ad1c : fetch_word Asan.M.loaded_segments (0x5ad6c : word) = Some W_5ad1c.
Proof. vm_refl. Qed.
Lemma D_5ad1c : decode_any W_5ad1c = Some (OpImm ALU_AND 11 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad20 : bv 32 := 0x00b50023.
Lemma F_5ad20 : fetch_word Asan.M.loaded_segments (0x5ad70 : word) = Some W_5ad20.
Proof. vm_refl. Qed.
Lemma D_5ad20 : decode_any W_5ad20 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad24 : bv 32 := 0x2e8300ef.
Lemma F_5ad24 : fetch_word Asan.M.loaded_segments (0x5ad74 : word) = Some W_5ad24.
Proof. vm_refl. Qed.
Lemma D_5ad24 : decode_any W_5ad24 = Some (Jal 1 197352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad28 : bv 32 := 0x01053583.
Lemma F_5ad28 : fetch_word Asan.M.loaded_segments (0x5ad78 : word) = Some W_5ad28.
Proof. vm_refl. Qed.
Lemma D_5ad28 : decode_any W_5ad28 = Some (Load SZ8 true 11 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad2c : bv 32 := 0x00053603.
Lemma F_5ad2c : fetch_word Asan.M.loaded_segments (0x5ad7c : word) = Some W_5ad2c.
Proof. vm_refl. Qed.
Lemma D_5ad2c : decode_any W_5ad2c = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad30 : bv 32 := 0x00853683.
Lemma F_5ad30 : fetch_word Asan.M.loaded_segments (0x5ad80 : word) = Some W_5ad30.
Proof. vm_refl. Qed.
Lemma D_5ad30 : decode_any W_5ad30 = Some (Load SZ8 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad34 : bv 32 := 0x40998733.
Lemma F_5ad34 : fetch_word Asan.M.loaded_segments (0x5ad84 : word) = Some W_5ad34.
Proof. vm_refl. Qed.
Lemma D_5ad34 : decode_any W_5ad34 = Some (Op ALU_SUB 14 19 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad38 : bv 32 := 0x00b705b3.
Lemma F_5ad38 : fetch_word Asan.M.loaded_segments (0x5ad88 : word) = Some W_5ad38.
Proof. vm_refl. Qed.
Lemma D_5ad38 : decode_any W_5ad38 = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad3c : bv 32 := 0x00010737.
Lemma F_5ad3c : fetch_word Asan.M.loaded_segments (0x5ad8c : word) = Some W_5ad3c.
Proof. vm_refl. Qed.
Lemma D_5ad3c : decode_any W_5ad3c = Some (Lui 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad40 : bv 32 := 0x0017071b.
Lemma F_5ad40 : fetch_word Asan.M.loaded_segments (0x5ad90 : word) = Some W_5ad40.
Proof. vm_refl. Qed.
Lemma D_5ad40 : decode_any W_5ad40 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad44 : bv 32 := 0x00160613.
Lemma F_5ad44 : fetch_word Asan.M.loaded_segments (0x5ad94 : word) = Some W_5ad44.
Proof. vm_refl. Qed.
Lemma D_5ad44 : decode_any W_5ad44 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad48 : bv 32 := 0x009686b3.
Lemma F_5ad48 : fetch_word Asan.M.loaded_segments (0x5ad98 : word) = Some W_5ad48.
Proof. vm_refl. Qed.
Lemma D_5ad48 : decode_any W_5ad48 = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad4c : bv 32 := 0x00c53023.
Lemma F_5ad4c : fetch_word Asan.M.loaded_segments (0x5ad9c : word) = Some W_5ad4c.
Proof. vm_refl. Qed.
Lemma D_5ad4c : decode_any W_5ad4c = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad50 : bv 32 := 0x00d53423.
Lemma F_5ad50 : fetch_word Asan.M.loaded_segments (0x5ada0 : word) = Some W_5ad50.
Proof. vm_refl. Qed.
Lemma D_5ad50 : decode_any W_5ad50 = Some (Store SZ8 10 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad54 : bv 32 := 0x00b53823.
Lemma F_5ad54 : fetch_word Asan.M.loaded_segments (0x5ada4 : word) = Some W_5ad54.
Proof. vm_refl. Qed.
Lemma D_5ad54 : decode_any W_5ad54 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad58 : bv 32 := 0x00e9ee63.
Lemma F_5ad58 : fetch_word Asan.M.loaded_segments (0x5ada8 : word) = Some W_5ad58.
Proof. vm_refl. Qed.
Lemma D_5ad58 : decode_any W_5ad58 = Some (Branch BC_LTU 19 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad5c : bv 32 := 0x06853583.
Lemma F_5ad5c : fetch_word Asan.M.loaded_segments (0x5adac : word) = Some W_5ad5c.
Proof. vm_refl. Qed.
Lemma D_5ad5c : decode_any W_5ad5c = Some (Load SZ8 true 11 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad60 : bv 32 := 0x00158593.
Lemma F_5ad60 : fetch_word Asan.M.loaded_segments (0x5adb0 : word) = Some W_5ad60.
Proof. vm_refl. Qed.
Lemma D_5ad60 : decode_any W_5ad60 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad64 : bv 32 := 0x06b53423.
Lemma F_5ad64 : fetch_word Asan.M.loaded_segments (0x5adb4 : word) = Some W_5ad64.
Proof. vm_refl. Qed.
Lemma D_5ad64 : decode_any W_5ad64 = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad68 : bv 32 := 0x00813503.
Lemma F_5ad68 : fetch_word Asan.M.loaded_segments (0x5adb8 : word) = Some W_5ad68.
Proof. vm_refl. Qed.
Lemma D_5ad68 : decode_any W_5ad68 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad6c : bv 32 := 0x10051c63.
Lemma F_5ad6c : fetch_word Asan.M.loaded_segments (0x5adbc : word) = Some W_5ad6c.
Proof. vm_refl. Qed.
Lemma D_5ad6c : decode_any W_5ad6c = Some (Branch BC_NE 10 0 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad74 : bv 32 := 0x20000593.
Lemma F_5ad74 : fetch_word Asan.M.loaded_segments (0x5adc4 : word) = Some W_5ad74.
Proof. vm_refl. Qed.
Lemma D_5ad74 : decode_any W_5ad74 = Some (OpImm ALU_ADD 11 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad78 : bv 32 := 0x07050513.
Lemma F_5ad78 : fetch_word Asan.M.loaded_segments (0x5adc8 : word) = Some W_5ad78.
Proof. vm_refl. Qed.
Lemma D_5ad78 : decode_any W_5ad78 = Some (OpImm ALU_ADD 10 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad7c : bv 32 := 0x0135e863.
Lemma F_5ad7c : fetch_word Asan.M.loaded_segments (0x5adcc : word) = Some W_5ad7c.
Proof. vm_refl. Qed.
Lemma D_5ad7c : decode_any W_5ad7c = Some (Branch BC_LTU 11 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad80 : bv 32 := 0x01f98593.
Lemma F_5ad80 : fetch_word Asan.M.loaded_segments (0x5add0 : word) = Some W_5ad80.
Proof. vm_refl. Qed.
Lemma D_5ad80 : decode_any W_5ad80 = Some (OpImm ALU_ADD 11 19 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad84 : bv 32 := 0x0055d593.
Lemma F_5ad84 : fetch_word Asan.M.loaded_segments (0x5add4 : word) = Some W_5ad84.
Proof. vm_refl. Qed.
Lemma D_5ad84 : decode_any W_5ad84 = Some (ShiftImm ALU_SRL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad88 : bv 32 := 0x0e00006f.
Lemma F_5ad88 : fetch_word Asan.M.loaded_segments (0x5add8 : word) = Some W_5ad88.
Proof. vm_refl. Qed.
Lemma D_5ad88 : decode_any W_5ad88 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad8c : bv 32 := 0x0019d593.
Lemma F_5ad8c : fetch_word Asan.M.loaded_segments (0x5addc : word) = Some W_5ad8c.
Proof. vm_refl. Qed.
Lemma D_5ad8c : decode_any W_5ad8c = Some (ShiftImm ALU_SRL 11 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad90 : bv 32 := 0x55555637.
Lemma F_5ad90 : fetch_word Asan.M.loaded_segments (0x5ade0 : word) = Some W_5ad90.
Proof. vm_refl. Qed.
Lemma D_5ad90 : decode_any W_5ad90 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad94 : bv 32 := 0x333336b7.
Lemma F_5ad94 : fetch_word Asan.M.loaded_segments (0x5ade4 : word) = Some W_5ad94.
Proof. vm_refl. Qed.
Lemma D_5ad94 : decode_any W_5ad94 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad98 : bv 32 := 0x0f0f1737.
Lemma F_5ad98 : fetch_word Asan.M.loaded_segments (0x5ade8 : word) = Some W_5ad98.
Proof. vm_refl. Qed.
Lemma D_5ad98 : decode_any W_5ad98 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ad9c : bv 32 := 0x010107b7.
Lemma F_5ad9c : fetch_word Asan.M.loaded_segments (0x5adec : word) = Some W_5ad9c.
Proof. vm_refl. Qed.
Lemma D_5ad9c : decode_any W_5ad9c = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ada0 : bv 32 := 0x00b9e5b3.
Lemma F_5ada0 : fetch_word Asan.M.loaded_segments (0x5adf0 : word) = Some W_5ada0.
Proof. vm_refl. Qed.
Lemma D_5ada0 : decode_any W_5ada0 = Some (Op ALU_OR 11 19 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ada4 : bv 32 := 0x5556061b.
Lemma F_5ada4 : fetch_word Asan.M.loaded_segments (0x5adf4 : word) = Some W_5ada4.
Proof. vm_refl. Qed.
Lemma D_5ada4 : decode_any W_5ada4 = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ada8 : bv 32 := 0x3336869b.
Lemma F_5ada8 : fetch_word Asan.M.loaded_segments (0x5adf8 : word) = Some W_5ada8.
Proof. vm_refl. Qed.
Lemma D_5ada8 : decode_any W_5ada8 = Some (OpImm32 13 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adac : bv 32 := 0xf0f7071b.
Lemma F_5adac : fetch_word Asan.M.loaded_segments (0x5adfc : word) = Some W_5adac.
Proof. vm_refl. Qed.
Lemma D_5adac : decode_any W_5adac = Some (OpImm32 14 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adb0 : bv 32 := 0x1017879b.
Lemma F_5adb0 : fetch_word Asan.M.loaded_segments (0x5ae00 : word) = Some W_5adb0.
Proof. vm_refl. Qed.
Lemma D_5adb0 : decode_any W_5adb0 = Some (OpImm32 15 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adb4 : bv 32 := 0x0025d813.
Lemma F_5adb4 : fetch_word Asan.M.loaded_segments (0x5ae04 : word) = Some W_5adb4.
Proof. vm_refl. Qed.
Lemma D_5adb4 : decode_any W_5adb4 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adb8 : bv 32 := 0x0105e5b3.
Lemma F_5adb8 : fetch_word Asan.M.loaded_segments (0x5ae08 : word) = Some W_5adb8.
Proof. vm_refl. Qed.
Lemma D_5adb8 : decode_any W_5adb8 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adbc : bv 32 := 0x02061813.
Lemma F_5adbc : fetch_word Asan.M.loaded_segments (0x5ae0c : word) = Some W_5adbc.
Proof. vm_refl. Qed.
Lemma D_5adbc : decode_any W_5adbc = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adc0 : bv 32 := 0x01060633.
Lemma F_5adc0 : fetch_word Asan.M.loaded_segments (0x5ae10 : word) = Some W_5adc0.
Proof. vm_refl. Qed.
Lemma D_5adc0 : decode_any W_5adc0 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adc4 : bv 32 := 0x02069813.
Lemma F_5adc4 : fetch_word Asan.M.loaded_segments (0x5ae14 : word) = Some W_5adc4.
Proof. vm_refl. Qed.
Lemma D_5adc4 : decode_any W_5adc4 = Some (ShiftImm ALU_SLL 16 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adc8 : bv 32 := 0x010686b3.
Lemma F_5adc8 : fetch_word Asan.M.loaded_segments (0x5ae18 : word) = Some W_5adc8.
Proof. vm_refl. Qed.
Lemma D_5adc8 : decode_any W_5adc8 = Some (Op ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adcc : bv 32 := 0x02071813.
Lemma F_5adcc : fetch_word Asan.M.loaded_segments (0x5ae1c : word) = Some W_5adcc.
Proof. vm_refl. Qed.
Lemma D_5adcc : decode_any W_5adcc = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5add0 : bv 32 := 0x01070733.
Lemma F_5add0 : fetch_word Asan.M.loaded_segments (0x5ae20 : word) = Some W_5add0.
Proof. vm_refl. Qed.
Lemma D_5add0 : decode_any W_5add0 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5add4 : bv 32 := 0x02079813.
Lemma F_5add4 : fetch_word Asan.M.loaded_segments (0x5ae24 : word) = Some W_5add4.
Proof. vm_refl. Qed.
Lemma D_5add4 : decode_any W_5add4 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5add8 : bv 32 := 0x010787b3.
Lemma F_5add8 : fetch_word Asan.M.loaded_segments (0x5ae28 : word) = Some W_5add8.
Proof. vm_refl. Qed.
Lemma D_5add8 : decode_any W_5add8 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5addc : bv 32 := 0x0045d813.
Lemma F_5addc : fetch_word Asan.M.loaded_segments (0x5ae2c : word) = Some W_5addc.
Proof. vm_refl. Qed.
Lemma D_5addc : decode_any W_5addc = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ade0 : bv 32 := 0x0105e5b3.
Lemma F_5ade0 : fetch_word Asan.M.loaded_segments (0x5ae30 : word) = Some W_5ade0.
Proof. vm_refl. Qed.
Lemma D_5ade0 : decode_any W_5ade0 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ade4 : bv 32 := 0x0085d813.
Lemma F_5ade4 : fetch_word Asan.M.loaded_segments (0x5ae34 : word) = Some W_5ade4.
Proof. vm_refl. Qed.
Lemma D_5ade4 : decode_any W_5ade4 = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ade8 : bv 32 := 0x0105e5b3.
Lemma F_5ade8 : fetch_word Asan.M.loaded_segments (0x5ae38 : word) = Some W_5ade8.
Proof. vm_refl. Qed.
Lemma D_5ade8 : decode_any W_5ade8 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adec : bv 32 := 0x0105d813.
Lemma F_5adec : fetch_word Asan.M.loaded_segments (0x5ae3c : word) = Some W_5adec.
Proof. vm_refl. Qed.
Lemma D_5adec : decode_any W_5adec = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adf0 : bv 32 := 0x0105e5b3.
Lemma F_5adf0 : fetch_word Asan.M.loaded_segments (0x5ae40 : word) = Some W_5adf0.
Proof. vm_refl. Qed.
Lemma D_5adf0 : decode_any W_5adf0 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adf4 : bv 32 := 0x0205d813.
Lemma F_5adf4 : fetch_word Asan.M.loaded_segments (0x5ae44 : word) = Some W_5adf4.
Proof. vm_refl. Qed.
Lemma D_5adf4 : decode_any W_5adf4 = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adf8 : bv 32 := 0x0105e5b3.
Lemma F_5adf8 : fetch_word Asan.M.loaded_segments (0x5ae48 : word) = Some W_5adf8.
Proof. vm_refl. Qed.
Lemma D_5adf8 : decode_any W_5adf8 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5adfc : bv 32 := 0xfff5c593.
Lemma F_5adfc : fetch_word Asan.M.loaded_segments (0x5ae4c : word) = Some W_5adfc.
Proof. vm_refl. Qed.
Lemma D_5adfc : decode_any W_5adfc = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae00 : bv 32 := 0x0015d813.
Lemma F_5ae00 : fetch_word Asan.M.loaded_segments (0x5ae50 : word) = Some W_5ae00.
Proof. vm_refl. Qed.
Lemma D_5ae00 : decode_any W_5ae00 = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae04 : bv 32 := 0x00c87633.
Lemma F_5ae04 : fetch_word Asan.M.loaded_segments (0x5ae54 : word) = Some W_5ae04.
Proof. vm_refl. Qed.
Lemma D_5ae04 : decode_any W_5ae04 = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae08 : bv 32 := 0x40c585b3.
Lemma F_5ae08 : fetch_word Asan.M.loaded_segments (0x5ae58 : word) = Some W_5ae08.
Proof. vm_refl. Qed.
Lemma D_5ae08 : decode_any W_5ae08 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae0c : bv 32 := 0x00d5f633.
Lemma F_5ae0c : fetch_word Asan.M.loaded_segments (0x5ae5c : word) = Some W_5ae0c.
Proof. vm_refl. Qed.
Lemma D_5ae0c : decode_any W_5ae0c = Some (Op ALU_AND 12 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae10 : bv 32 := 0x0025d593.
Lemma F_5ae10 : fetch_word Asan.M.loaded_segments (0x5ae60 : word) = Some W_5ae10.
Proof. vm_refl. Qed.
Lemma D_5ae10 : decode_any W_5ae10 = Some (ShiftImm ALU_SRL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae14 : bv 32 := 0x00d5f5b3.
Lemma F_5ae14 : fetch_word Asan.M.loaded_segments (0x5ae64 : word) = Some W_5ae14.
Proof. vm_refl. Qed.
Lemma D_5ae14 : decode_any W_5ae14 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae18 : bv 32 := 0x00b605b3.
Lemma F_5ae18 : fetch_word Asan.M.loaded_segments (0x5ae68 : word) = Some W_5ae18.
Proof. vm_refl. Qed.
Lemma D_5ae18 : decode_any W_5ae18 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae1c : bv 32 := 0x0045d613.
Lemma F_5ae1c : fetch_word Asan.M.loaded_segments (0x5ae6c : word) = Some W_5ae1c.
Proof. vm_refl. Qed.
Lemma D_5ae1c : decode_any W_5ae1c = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae20 : bv 32 := 0x00c585b3.
Lemma F_5ae20 : fetch_word Asan.M.loaded_segments (0x5ae70 : word) = Some W_5ae20.
Proof. vm_refl. Qed.
Lemma D_5ae20 : decode_any W_5ae20 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae24 : bv 32 := 0x03e00613.
Lemma F_5ae24 : fetch_word Asan.M.loaded_segments (0x5ae74 : word) = Some W_5ae24.
Proof. vm_refl. Qed.
Lemma D_5ae24 : decode_any W_5ae24 = Some (OpImm ALU_ADD 12 0 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae28 : bv 32 := 0x00e5f5b3.
Lemma F_5ae28 : fetch_word Asan.M.loaded_segments (0x5ae78 : word) = Some W_5ae28.
Proof. vm_refl. Qed.
Lemma D_5ae28 : decode_any W_5ae28 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae2c : bv 32 := 0xfff00693.
Lemma F_5ae2c : fetch_word Asan.M.loaded_segments (0x5ae7c : word) = Some W_5ae2c.
Proof. vm_refl. Qed.
Lemma D_5ae2c : decode_any W_5ae2c = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae30 : bv 32 := 0x02f585b3.
Lemma F_5ae30 : fetch_word Asan.M.loaded_segments (0x5ae80 : word) = Some W_5ae30.
Proof. vm_refl. Qed.
Lemma D_5ae30 : decode_any W_5ae30 = Some (Mul M_MUL 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae34 : bv 32 := 0x0385d593.
Lemma F_5ae34 : fetch_word Asan.M.loaded_segments (0x5ae84 : word) = Some W_5ae34.
Proof. vm_refl. Qed.
Lemma D_5ae34 : decode_any W_5ae34 = Some (ShiftImm ALU_SRL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae38 : bv 32 := 0x40b6063b.
Lemma F_5ae38 : fetch_word Asan.M.loaded_segments (0x5ae88 : word) = Some W_5ae38.
Proof. vm_refl. Qed.
Lemma D_5ae38 : decode_any W_5ae38 = Some (Op32 ALU_SUB 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae3c : bv 32 := 0x00159593.
Lemma F_5ae3c : fetch_word Asan.M.loaded_segments (0x5ae8c : word) = Some W_5ae3c.
Proof. vm_refl. Qed.
Lemma D_5ae3c : decode_any W_5ae3c = Some (ShiftImm ALU_SLL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae40 : bv 32 := 0x00c9d733.
Lemma F_5ae40 : fetch_word Asan.M.loaded_segments (0x5ae90 : word) = Some W_5ae40.
Proof. vm_refl. Qed.
Lemma D_5ae40 : decode_any W_5ae40 = Some (Op ALU_SRL 14 19 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae44 : bv 32 := 0x00c6963b.
Lemma F_5ae44 : fetch_word Asan.M.loaded_segments (0x5ae94 : word) = Some W_5ae44.
Proof. vm_refl. Qed.
Lemma D_5ae44 : decode_any W_5ae44 = Some (Op32 ALU_SLL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae48 : bv 32 := 0x07e5c593.
Lemma F_5ae48 : fetch_word Asan.M.loaded_segments (0x5ae98 : word) = Some W_5ae48.
Proof. vm_refl. Qed.
Lemma D_5ae48 : decode_any W_5ae48 = Some (OpImm ALU_XOR 11 11 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae4c : bv 32 := 0x00177713.
Lemma F_5ae4c : fetch_word Asan.M.loaded_segments (0x5ae9c : word) = Some W_5ae4c.
Proof. vm_refl. Qed.
Lemma D_5ae4c : decode_any W_5ae4c = Some (OpImm ALU_AND 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae50 : bv 32 := 0xfff64613.
Lemma F_5ae50 : fetch_word Asan.M.loaded_segments (0x5aea0 : word) = Some W_5ae50.
Proof. vm_refl. Qed.
Lemma D_5ae50 : decode_any W_5ae50 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae54 : bv 32 := 0x00c9f633.
Lemma F_5ae54 : fetch_word Asan.M.loaded_segments (0x5aea4 : word) = Some W_5ae54.
Proof. vm_refl. Qed.
Lemma D_5ae54 : decode_any W_5ae54 = Some (Op ALU_AND 12 19 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae58 : bv 32 := 0x00e5e5b3.
Lemma F_5ae58 : fetch_word Asan.M.loaded_segments (0x5aea8 : word) = Some W_5ae58.
Proof. vm_refl. Qed.
Lemma D_5ae58 : decode_any W_5ae58 = Some (Op ALU_OR 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae5c : bv 32 := 0x00c03633.
Lemma F_5ae5c : fetch_word Asan.M.loaded_segments (0x5aeac : word) = Some W_5ae5c.
Proof. vm_refl. Qed.
Lemma D_5ae5c : decode_any W_5ae5c = Some (Op ALU_SLTU 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae60 : bv 32 := 0x00c585b3.
Lemma F_5ae60 : fetch_word Asan.M.loaded_segments (0x5aeb0 : word) = Some W_5ae60.
Proof. vm_refl. Qed.
Lemma D_5ae60 : decode_any W_5ae60 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae64 : bv 32 := 0xffe58593.
Lemma F_5ae64 : fetch_word Asan.M.loaded_segments (0x5aeb4 : word) = Some W_5ae64.
Proof. vm_refl. Qed.
Lemma D_5ae64 : decode_any W_5ae64 = Some (OpImm ALU_ADD 11 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae68 : bv 32 := 0x00359593.
Lemma F_5ae68 : fetch_word Asan.M.loaded_segments (0x5aeb8 : word) = Some W_5ae68.
Proof. vm_refl. Qed.
Lemma D_5ae68 : decode_any W_5ae68 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae6c : bv 32 := 0x00b50533.
Lemma F_5ae6c : fetch_word Asan.M.loaded_segments (0x5aebc : word) = Some W_5ae6c.
Proof. vm_refl. Qed.
Lemma D_5ae6c : decode_any W_5ae6c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae70 : bv 32 := 0x00053583.
Lemma F_5ae70 : fetch_word Asan.M.loaded_segments (0x5aec0 : word) = Some W_5ae70.
Proof. vm_refl. Qed.
Lemma D_5ae70 : decode_any W_5ae70 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae74 : bv 32 := 0x00158593.
Lemma F_5ae74 : fetch_word Asan.M.loaded_segments (0x5aec4 : word) = Some W_5ae74.
Proof. vm_refl. Qed.
Lemma D_5ae74 : decode_any W_5ae74 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae78 : bv 32 := 0x00b53023.
Lemma F_5ae78 : fetch_word Asan.M.loaded_segments (0x5aec8 : word) = Some W_5ae78.
Proof. vm_refl. Qed.
Lemma D_5ae78 : decode_any W_5ae78 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae7c : bv 32 := 0x00813503.
Lemma F_5ae7c : fetch_word Asan.M.loaded_segments (0x5aecc : word) = Some W_5ae7c.
Proof. vm_refl. Qed.
Lemma D_5ae7c : decode_any W_5ae7c = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae80 : bv 32 := 0x02050c63.
Lemma F_5ae80 : fetch_word Asan.M.loaded_segments (0x5aed0 : word) = Some W_5ae80.
Proof. vm_refl. Qed.
Lemma D_5ae80 : decode_any W_5ae80 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae84 : bv 32 := 0x00106517.
Lemma F_5ae84 : fetch_word Asan.M.loaded_segments (0x5aed4 : word) = Some W_5ae84.
Proof. vm_refl. Qed.
Lemma D_5ae84 : decode_any W_5ae84 = Some (Auipc 10 262, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae88 : bv 32 := 0xd3c53503.
Lemma F_5ae88 : fetch_word Asan.M.loaded_segments (0x5aed8 : word) = Some W_5ae88.
Proof. vm_refl. Qed.
Lemma D_5ae88 : decode_any W_5ae88 = Some (Load SZ8 true 10 10 3388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae8c : bv 32 := 0x02c52583.
Lemma F_5ae8c : fetch_word Asan.M.loaded_segments (0x5aedc : word) = Some W_5ae8c.
Proof. vm_refl. Qed.
Lemma D_5ae8c : decode_any W_5ae8c = Some (Load SZ4 true 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae90 : bv 32 := 0x02058463.
Lemma F_5ae90 : fetch_word Asan.M.loaded_segments (0x5aee0 : word) = Some W_5ae90.
Proof. vm_refl. Qed.
Lemma D_5ae90 : decode_any W_5ae90 = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae94 : bv 32 := 0x00048613.
Lemma F_5ae94 : fetch_word Asan.M.loaded_segments (0x5aee4 : word) = Some W_5ae94.
Proof. vm_refl. Qed.
Lemma D_5ae94 : decode_any W_5ae94 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae98 : bv 32 := 0x00b4e463.
Lemma F_5ae98 : fetch_word Asan.M.loaded_segments (0x5aee8 : word) = Some W_5ae98.
Proof. vm_refl. Qed.
Lemma D_5ae98 : decode_any W_5ae98 = Some (Branch BC_LTU 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ae9c : bv 32 := 0x00058613.
Lemma F_5ae9c : fetch_word Asan.M.loaded_segments (0x5aeec : word) = Some W_5ae9c.
Proof. vm_refl. Qed.
Lemma D_5ae9c : decode_any W_5ae9c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aea0 : bv 32 := 0x00106597.
Lemma F_5aea0 : fetch_word Asan.M.loaded_segments (0x5aef0 : word) = Some W_5aea0.
Proof. vm_refl. Qed.
Lemma D_5aea0 : decode_any W_5aea0 = Some (Auipc 11 262, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aea4 : bv 32 := 0xd485b583.
Lemma F_5aea4 : fetch_word Asan.M.loaded_segments (0x5aef4 : word) = Some W_5aea4.
Proof. vm_refl. Qed.
Lemma D_5aea4 : decode_any W_5aea4 = Some (Load SZ8 true 11 11 3400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aea8 : bv 32 := 0x0005b683.
Lemma F_5aea8 : fetch_word Asan.M.loaded_segments (0x5aef8 : word) = Some W_5aea8.
Proof. vm_refl. Qed.
Lemma D_5aea8 : decode_any W_5aea8 = Some (Load SZ8 true 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aeac : bv 32 := 0x03452583.
Lemma F_5aeac : fetch_word Asan.M.loaded_segments (0x5aefc : word) = Some W_5aeac.
Proof. vm_refl. Qed.
Lemma D_5aeac : decode_any W_5aeac = Some (Load SZ4 true 11 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aeb0 : bv 32 := 0x000a0513.
Lemma F_5aeb0 : fetch_word Asan.M.loaded_segments (0x5af00 : word) = Some W_5aeb0.
Proof. vm_refl. Qed.
Lemma D_5aeb0 : decode_any W_5aeb0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aeb4 : bv 32 := 0x000680e7.
Lemma F_5aeb4 : fetch_word Asan.M.loaded_segments (0x5af04 : word) = Some W_5aeb4.
Proof. vm_refl. Qed.
Lemma D_5aeb4 : decode_any W_5aeb4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aeb8 : bv 32 := 0x369540ef.
Lemma F_5aeb8 : fetch_word Asan.M.loaded_segments (0x5af08 : word) = Some W_5aeb8.
Proof. vm_refl. Qed.
Lemma D_5aeb8 : decode_any W_5aeb8 = Some (Jal 1 346984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aebc : bv 32 := 0x001ac583.
Lemma F_5aebc : fetch_word Asan.M.loaded_segments (0x5af0c : word) = Some W_5aebc.
Proof. vm_refl. Qed.
Lemma D_5aebc : decode_any W_5aebc = Some (Load SZ1 false 11 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aec0 : bv 32 := 0x40a0053b.
Lemma F_5aec0 : fetch_word Asan.M.loaded_segments (0x5af10 : word) = Some W_5aec0.
Proof. vm_refl. Qed.
Lemma D_5aec0 : decode_any W_5aec0 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aec4 : bv 32 := 0x00c57513.
Lemma F_5aec4 : fetch_word Asan.M.loaded_segments (0x5af14 : word) = Some W_5aec4.
Proof. vm_refl. Qed.
Lemma D_5aec4 : decode_any W_5aec4 = Some (OpImm ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aec8 : bv 32 := 0x0f35f593.
Lemma F_5aec8 : fetch_word Asan.M.loaded_segments (0x5af18 : word) = Some W_5aec8.
Proof. vm_refl. Qed.
Lemma D_5aec8 : decode_any W_5aec8 = Some (OpImm ALU_AND 11 11 243, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aecc : bv 32 := 0x00a5e533.
Lemma F_5aecc : fetch_word Asan.M.loaded_segments (0x5af1c : word) = Some W_5aecc.
Proof. vm_refl. Qed.
Lemma D_5aecc : decode_any W_5aecc = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aed0 : bv 32 := 0x00200593.
Lemma F_5aed0 : fetch_word Asan.M.loaded_segments (0x5af20 : word) = Some W_5aed0.
Proof. vm_refl. Qed.
Lemma D_5aed0 : decode_any W_5aed0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aed4 : bv 32 := 0x00aa80a3.
Lemma F_5aed4 : fetch_word Asan.M.loaded_segments (0x5af24 : word) = Some W_5aed4.
Proof. vm_refl. Qed.
Lemma D_5aed4 : decode_any W_5aed4 = Some (Store SZ1 21 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aed8 : bv 32 := 0x0310000f.
Lemma F_5aed8 : fetch_word Asan.M.loaded_segments (0x5af28 : word) = Some W_5aed8.
Proof. vm_refl. Qed.
Lemma D_5aed8 : decode_any W_5aed8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aedc : bv 32 := 0x00ba8023.
Lemma F_5aedc : fetch_word Asan.M.loaded_segments (0x5af2c : word) = Some W_5aedc.
Proof. vm_refl. Qed.
Lemma D_5aedc : decode_any W_5aedc = Some (Store SZ1 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aee0 : bv 32 := 0x032a8063.
Lemma F_5aee0 : fetch_word Asan.M.loaded_segments (0x5af30 : word) = Some W_5aee0.
Proof. vm_refl. Qed.
Lemma D_5aee0 : decode_any W_5aee0 = Some (Branch BC_EQ 21 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aee4 : bv 32 := 0x01090693.
Lemma F_5aee4 : fetch_word Asan.M.loaded_segments (0x5af34 : word) = Some W_5aee4.
Proof. vm_refl. Qed.
Lemma D_5aee4 : decode_any W_5aee4 = Some (OpImm ALU_ADD 13 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aee8 : bv 32 := 0x20daee63.
Lemma F_5aee8 : fetch_word Asan.M.loaded_segments (0x5af38 : word) = Some W_5aee8.
Proof. vm_refl. Qed.
Lemma D_5aee8 : decode_any W_5aee8 = Some (Branch BC_LTU 21 13 540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aeec : bv 32 := 0xfffb5517.
Lemma F_5aeec : fetch_word Asan.M.loaded_segments (0x5af3c : word) = Some W_5aeec.
Proof. vm_refl. Qed.
Lemma D_5aeec : decode_any W_5aeec = Some (Auipc 10 1048501, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aef0 : bv 32 := 0x43c53503.
Lemma F_5aef0 : fetch_word Asan.M.loaded_segments (0x5af40 : word) = Some W_5aef0.
Proof. vm_refl. Qed.
Lemma D_5aef0 : decode_any W_5aef0 = Some (Load SZ8 true 10 10 1084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aef4 : bv 32 := 0x01593423.
Lemma F_5aef4 : fetch_word Asan.M.loaded_segments (0x5af44 : word) = Some W_5aef4.
Proof. vm_refl. Qed.
Lemma D_5aef4 : decode_any W_5aef4 = Some (Store SZ8 18 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aef8 : bv 32 := 0x0310000f.
Lemma F_5aef8 : fetch_word Asan.M.loaded_segments (0x5af48 : word) = Some W_5aef8.
Proof. vm_refl. Qed.
Lemma D_5aef8 : decode_any W_5aef8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5aefc : bv 32 := 0x00a93023.
Lemma F_5aefc : fetch_word Asan.M.loaded_segments (0x5af4c : word) = Some W_5aefc.
Proof. vm_refl. Qed.
Lemma D_5aefc : decode_any W_5aefc = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af00 : bv 32 := 0x000a0513.
Lemma F_5af00 : fetch_word Asan.M.loaded_segments (0x5af50 : word) = Some W_5af00.
Proof. vm_refl. Qed.
Lemma D_5af00 : decode_any W_5af00 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af04 : bv 32 := 0x00048593.
Lemma F_5af04 : fetch_word Asan.M.loaded_segments (0x5af54 : word) = Some W_5af04.
Proof. vm_refl. Qed.
Lemma D_5af04 : decode_any W_5af04 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af08 : bv 32 := 0x70c350ef.
Lemma F_5af08 : fetch_word Asan.M.loaded_segments (0x5af58 : word) = Some W_5af08.
Proof. vm_refl. Qed.
Lemma D_5af08 : decode_any W_5af08 = Some (Jal 1 218892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af0c : bv 32 := 0x000a0513.
Lemma F_5af0c : fetch_word Asan.M.loaded_segments (0x5af5c : word) = Some W_5af0c.
Proof. vm_refl. Qed.
Lemma D_5af0c : decode_any W_5af0c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af10 : bv 32 := 0x07813083.
Lemma F_5af10 : fetch_word Asan.M.loaded_segments (0x5af60 : word) = Some W_5af10.
Proof. vm_refl. Qed.
Lemma D_5af10 : decode_any W_5af10 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af14 : bv 32 := 0x07013403.
Lemma F_5af14 : fetch_word Asan.M.loaded_segments (0x5af64 : word) = Some W_5af14.
Proof. vm_refl. Qed.
Lemma D_5af14 : decode_any W_5af14 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af18 : bv 32 := 0x06813483.
Lemma F_5af18 : fetch_word Asan.M.loaded_segments (0x5af68 : word) = Some W_5af18.
Proof. vm_refl. Qed.
Lemma D_5af18 : decode_any W_5af18 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af1c : bv 32 := 0x06013903.
Lemma F_5af1c : fetch_word Asan.M.loaded_segments (0x5af6c : word) = Some W_5af1c.
Proof. vm_refl. Qed.
Lemma D_5af1c : decode_any W_5af1c = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af20 : bv 32 := 0x05813983.
Lemma F_5af20 : fetch_word Asan.M.loaded_segments (0x5af70 : word) = Some W_5af20.
Proof. vm_refl. Qed.
Lemma D_5af20 : decode_any W_5af20 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af24 : bv 32 := 0x05013a03.
Lemma F_5af24 : fetch_word Asan.M.loaded_segments (0x5af74 : word) = Some W_5af24.
Proof. vm_refl. Qed.
Lemma D_5af24 : decode_any W_5af24 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af28 : bv 32 := 0x04813a83.
Lemma F_5af28 : fetch_word Asan.M.loaded_segments (0x5af78 : word) = Some W_5af28.
Proof. vm_refl. Qed.
Lemma D_5af28 : decode_any W_5af28 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af2c : bv 32 := 0x04013b03.
Lemma F_5af2c : fetch_word Asan.M.loaded_segments (0x5af7c : word) = Some W_5af2c.
Proof. vm_refl. Qed.
Lemma D_5af2c : decode_any W_5af2c = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af30 : bv 32 := 0x03813b83.
Lemma F_5af30 : fetch_word Asan.M.loaded_segments (0x5af80 : word) = Some W_5af30.
Proof. vm_refl. Qed.
Lemma D_5af30 : decode_any W_5af30 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af34 : bv 32 := 0x03013c03.
Lemma F_5af34 : fetch_word Asan.M.loaded_segments (0x5af84 : word) = Some W_5af34.
Proof. vm_refl. Qed.
Lemma D_5af34 : decode_any W_5af34 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af38 : bv 32 := 0x02813c83.
Lemma F_5af38 : fetch_word Asan.M.loaded_segments (0x5af88 : word) = Some W_5af38.
Proof. vm_refl. Qed.
Lemma D_5af38 : decode_any W_5af38 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af3c : bv 32 := 0x02013d03.
Lemma F_5af3c : fetch_word Asan.M.loaded_segments (0x5af8c : word) = Some W_5af3c.
Proof. vm_refl. Qed.
Lemma D_5af3c : decode_any W_5af3c = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af40 : bv 32 := 0x01813d83.
Lemma F_5af40 : fetch_word Asan.M.loaded_segments (0x5af90 : word) = Some W_5af40.
Proof. vm_refl. Qed.
Lemma D_5af40 : decode_any W_5af40 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af44 : bv 32 := 0x08010113.
Lemma F_5af44 : fetch_word Asan.M.loaded_segments (0x5af94 : word) = Some W_5af44.
Proof. vm_refl. Qed.
Lemma D_5af44 : decode_any W_5af44 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af48 : bv 32 := 0x00008067.
Lemma F_5af48 : fetch_word Asan.M.loaded_segments (0x5af98 : word) = Some W_5af48.
Proof. vm_refl. Qed.
Lemma D_5af48 : decode_any W_5af48 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

