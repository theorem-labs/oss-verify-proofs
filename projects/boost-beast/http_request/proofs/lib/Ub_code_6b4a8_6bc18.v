(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6b4a8 : bv 32 := 0xfc010113.
Lemma F_6b4a8 : fetch_word Ubsan.M.loaded_segments (0x6b4a8 : word) = Some W_6b4a8.
Proof. vm_refl. Qed.
Lemma D_6b4a8 : decode_any W_6b4a8 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4ac : bv 32 := 0x02113c23.
Lemma F_6b4ac : fetch_word Ubsan.M.loaded_segments (0x6b4ac : word) = Some W_6b4ac.
Proof. vm_refl. Qed.
Lemma D_6b4ac : decode_any W_6b4ac = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4b0 : bv 32 := 0x02813823.
Lemma F_6b4b0 : fetch_word Ubsan.M.loaded_segments (0x6b4b0 : word) = Some W_6b4b0.
Proof. vm_refl. Qed.
Lemma D_6b4b0 : decode_any W_6b4b0 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4b4 : bv 32 := 0x02913423.
Lemma F_6b4b4 : fetch_word Ubsan.M.loaded_segments (0x6b4b4 : word) = Some W_6b4b4.
Proof. vm_refl. Qed.
Lemma D_6b4b4 : decode_any W_6b4b4 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4b8 : bv 32 := 0x03213023.
Lemma F_6b4b8 : fetch_word Ubsan.M.loaded_segments (0x6b4b8 : word) = Some W_6b4b8.
Proof. vm_refl. Qed.
Lemma D_6b4b8 : decode_any W_6b4b8 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4bc : bv 32 := 0x01313c23.
Lemma F_6b4bc : fetch_word Ubsan.M.loaded_segments (0x6b4bc : word) = Some W_6b4bc.
Proof. vm_refl. Qed.
Lemma D_6b4bc : decode_any W_6b4bc = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4c0 : bv 32 := 0x01413823.
Lemma F_6b4c0 : fetch_word Ubsan.M.loaded_segments (0x6b4c0 : word) = Some W_6b4c0.
Proof. vm_refl. Qed.
Lemma D_6b4c0 : decode_any W_6b4c0 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4c4 : bv 32 := 0x01513423.
Lemma F_6b4c4 : fetch_word Ubsan.M.loaded_segments (0x6b4c4 : word) = Some W_6b4c4.
Proof. vm_refl. Qed.
Lemma D_6b4c4 : decode_any W_6b4c4 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4c8 : bv 32 := 0x0004b597.
Lemma F_6b4c8 : fetch_word Ubsan.M.loaded_segments (0x6b4c8 : word) = Some W_6b4c8.
Proof. vm_refl. Qed.
Lemma D_6b4c8 : decode_any W_6b4c8 = Some (Auipc 11 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4cc : bv 32 := 0xf3800693.
Lemma F_6b4cc : fetch_word Ubsan.M.loaded_segments (0x6b4cc : word) = Some W_6b4cc.
Proof. vm_refl. Qed.
Lemma D_6b4cc : decode_any W_6b4cc = Some (OpImm ALU_ADD 13 0 3896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4d0 : bv 32 := 0x73858493.
Lemma F_6b4d0 : fetch_word Ubsan.M.loaded_segments (0x6b4d0 : word) = Some W_6b4d0.
Proof. vm_refl. Qed.
Lemma D_6b4d0 : decode_any W_6b4d0 = Some (OpImm ALU_ADD 9 11 1848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4d4 : bv 32 := 0x0104b903.
Lemma F_6b4d4 : fetch_word Ubsan.M.loaded_segments (0x6b4d4 : word) = Some W_6b4d4.
Proof. vm_refl. Qed.
Lemma D_6b4d4 : decode_any W_6b4d4 = Some (Load SZ8 true 18 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4d8 : bv 32 := 0x0184b603.
Lemma F_6b4d8 : fetch_word Ubsan.M.loaded_segments (0x6b4d8 : word) = Some W_6b4d8.
Proof. vm_refl. Qed.
Lemma D_6b4d8 : decode_any W_6b4d8 = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4dc : bv 32 := 0x0204b703.
Lemma F_6b4dc : fetch_word Ubsan.M.loaded_segments (0x6b4dc : word) = Some W_6b4dc.
Proof. vm_refl. Qed.
Lemma D_6b4dc : decode_any W_6b4dc = Some (Load SZ8 true 14 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4e0 : bv 32 := 0x40a686b3.
Lemma F_6b4e0 : fetch_word Ubsan.M.loaded_segments (0x6b4e0 : word) = Some W_6b4e0.
Proof. vm_refl. Qed.
Lemma D_6b4e0 : decode_any W_6b4e0 = Some (Op ALU_SUB 13 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4e4 : bv 32 := 0x0284b583.
Lemma F_6b4e4 : fetch_word Ubsan.M.loaded_segments (0x6b4e4 : word) = Some W_6b4e4.
Proof. vm_refl. Qed.
Lemma D_6b4e4 : decode_any W_6b4e4 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4e8 : bv 32 := 0x00c509b3.
Lemma F_6b4e8 : fetch_word Ubsan.M.loaded_segments (0x6b4e8 : word) = Some W_6b4e8.
Proof. vm_refl. Qed.
Lemma D_6b4e8 : decode_any W_6b4e8 = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4ec : bv 32 := 0xfff70713.
Lemma F_6b4ec : fetch_word Ubsan.M.loaded_segments (0x6b4ec : word) = Some W_6b4ec.
Proof. vm_refl. Qed.
Lemma D_6b4ec : decode_any W_6b4ec = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4f0 : bv 32 := 0x00d776b3.
Lemma F_6b4f0 : fetch_word Ubsan.M.loaded_segments (0x6b4f0 : word) = Some W_6b4f0.
Proof. vm_refl. Qed.
Lemma D_6b4f0 : decode_any W_6b4f0 = Some (Op ALU_AND 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4f4 : bv 32 := 0xfff5c713.
Lemma F_6b4f4 : fetch_word Ubsan.M.loaded_segments (0x6b4f4 : word) = Some W_6b4f4.
Proof. vm_refl. Qed.
Lemma D_6b4f4 : decode_any W_6b4f4 = Some (OpImm ALU_XOR 14 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4f8 : bv 32 := 0x00371713.
Lemma F_6b4f8 : fetch_word Ubsan.M.loaded_segments (0x6b4f8 : word) = Some W_6b4f8.
Proof. vm_refl. Qed.
Lemma D_6b4f8 : decode_any W_6b4f8 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4fc : bv 32 := 0x00e989b3.
Lemma F_6b4fc : fetch_word Ubsan.M.loaded_segments (0x6b4fc : word) = Some W_6b4fc.
Proof. vm_refl. Qed.
Lemma D_6b4fc : decode_any W_6b4fc = Some (Op ALU_ADD 19 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b500 : bv 32 := 0x00d50433.
Lemma F_6b500 : fetch_word Ubsan.M.loaded_segments (0x6b500 : word) = Some W_6b500.
Proof. vm_refl. Qed.
Lemma D_6b500 : decode_any W_6b500 = Some (Op ALU_ADD 8 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b504 : bv 32 := 0x04090663.
Lemma F_6b504 : fetch_word Ubsan.M.loaded_segments (0x6b504 : word) = Some W_6b504.
Proof. vm_refl. Qed.
Lemma D_6b504 : decode_any W_6b504 = Some (Branch BC_EQ 18 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b508 : bv 32 := 0x0c840a13.
Lemma F_6b508 : fetch_word Ubsan.M.loaded_segments (0x6b508 : word) = Some W_6b508.
Proof. vm_refl. Qed.
Lemma D_6b508 : decode_any W_6b508 = Some (OpImm ALU_ADD 20 8 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b50c : bv 32 := 0x00359593.
Lemma F_6b50c : fetch_word Ubsan.M.loaded_segments (0x6b50c : word) = Some W_6b50c.
Proof. vm_refl. Qed.
Lemma D_6b50c : decode_any W_6b50c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b510 : bv 32 := 0x00c50533.
Lemma F_6b510 : fetch_word Ubsan.M.loaded_segments (0x6b510 : word) = Some W_6b510.
Proof. vm_refl. Qed.
Lemma D_6b510 : decode_any W_6b510 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b514 : bv 32 := 0x40b50ab3.
Lemma F_6b514 : fetch_word Ubsan.M.loaded_segments (0x6b514 : word) = Some W_6b514.
Proof. vm_refl. Qed.
Lemma D_6b514 : decode_any W_6b514 = Some (Op ALU_SUB 21 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b518 : bv 32 := 0x02893503.
Lemma F_6b518 : fetch_word Ubsan.M.loaded_segments (0x6b518 : word) = Some W_6b518.
Proof. vm_refl. Qed.
Lemma D_6b518 : decode_any W_6b518 = Some (Load SZ8 true 10 18 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b51c : bv 32 := 0x00aa0533.
Lemma F_6b51c : fetch_word Ubsan.M.loaded_segments (0x6b51c : word) = Some W_6b51c.
Proof. vm_refl. Qed.
Lemma D_6b51c : decode_any W_6b51c = Some (Op ALU_ADD 10 20 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b520 : bv 32 := 0x7ff50513.
Lemma F_6b520 : fetch_word Ubsan.M.loaded_segments (0x6b520 : word) = Some W_6b520.
Proof. vm_refl. Qed.
Lemma D_6b520 : decode_any W_6b520 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b524 : bv 32 := 0x00150513.
Lemma F_6b524 : fetch_word Ubsan.M.loaded_segments (0x6b524 : word) = Some W_6b524.
Proof. vm_refl. Qed.
Lemma D_6b524 : decode_any W_6b524 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b528 : bv 32 := 0x00aab023.
Lemma F_6b528 : fetch_word Ubsan.M.loaded_segments (0x6b528 : word) = Some W_6b528.
Proof. vm_refl. Qed.
Lemma D_6b528 : decode_any W_6b528 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b52c : bv 32 := 0x02893503.
Lemma F_6b52c : fetch_word Ubsan.M.loaded_segments (0x6b52c : word) = Some W_6b52c.
Proof. vm_refl. Qed.
Lemma D_6b52c : decode_any W_6b52c = Some (Load SZ8 true 10 18 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b530 : bv 32 := 0x00893583.
Lemma F_6b530 : fetch_word Ubsan.M.loaded_segments (0x6b530 : word) = Some W_6b530.
Proof. vm_refl. Qed.
Lemma D_6b530 : decode_any W_6b530 = Some (Load SZ8 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b534 : bv 32 := 0x01093603.
Lemma F_6b534 : fetch_word Ubsan.M.loaded_segments (0x6b534 : word) = Some W_6b534.
Proof. vm_refl. Qed.
Lemma D_6b534 : decode_any W_6b534 = Some (Load SZ8 true 12 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b538 : bv 32 := 0x00aa0533.
Lemma F_6b538 : fetch_word Ubsan.M.loaded_segments (0x6b538 : word) = Some W_6b538.
Proof. vm_refl. Qed.
Lemma D_6b538 : decode_any W_6b538 = Some (Op ALU_ADD 10 20 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b53c : bv 32 := 0x0140e0ef.
Lemma F_6b53c : fetch_word Ubsan.M.loaded_segments (0x6b53c : word) = Some W_6b53c.
Proof. vm_refl. Qed.
Lemma D_6b53c : decode_any W_6b53c = Some (Jal 1 57364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b540 : bv 32 := 0x00093903.
Lemma F_6b540 : fetch_word Ubsan.M.loaded_segments (0x6b540 : word) = Some W_6b540.
Proof. vm_refl. Qed.
Lemma D_6b540 : decode_any W_6b540 = Some (Load SZ8 true 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b544 : bv 32 := 0x008a8a93.
Lemma F_6b544 : fetch_word Ubsan.M.loaded_segments (0x6b544 : word) = Some W_6b544.
Proof. vm_refl. Qed.
Lemma D_6b544 : decode_any W_6b544 = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b548 : bv 32 := 0xfc0918e3.
Lemma F_6b548 : fetch_word Ubsan.M.loaded_segments (0x6b548 : word) = Some W_6b548.
Proof. vm_refl. Qed.
Lemma D_6b548 : decode_any W_6b548 = Some (Branch BC_NE 18 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b54c : bv 32 := 0x0284b583.
Lemma F_6b54c : fetch_word Ubsan.M.loaded_segments (0x6b54c : word) = Some W_6b54c.
Proof. vm_refl. Qed.
Lemma D_6b54c : decode_any W_6b54c = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b550 : bv 32 := 0x00b9b023.
Lemma F_6b550 : fetch_word Ubsan.M.loaded_segments (0x6b550 : word) = Some W_6b550.
Proof. vm_refl. Qed.
Lemma D_6b550 : decode_any W_6b550 = Some (Store SZ8 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b554 : bv 32 := 0x0d343023.
Lemma F_6b554 : fetch_word Ubsan.M.loaded_segments (0x6b554 : word) = Some W_6b554.
Proof. vm_refl. Qed.
Lemma D_6b554 : decode_any W_6b554 = Some (Store SZ8 8 19 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b558 : bv 32 := 0x00040513.
Lemma F_6b558 : fetch_word Ubsan.M.loaded_segments (0x6b558 : word) = Some W_6b558.
Proof. vm_refl. Qed.
Lemma D_6b558 : decode_any W_6b558 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b55c : bv 32 := 0x03813083.
Lemma F_6b55c : fetch_word Ubsan.M.loaded_segments (0x6b55c : word) = Some W_6b55c.
Proof. vm_refl. Qed.
Lemma D_6b55c : decode_any W_6b55c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b560 : bv 32 := 0x03013403.
Lemma F_6b560 : fetch_word Ubsan.M.loaded_segments (0x6b560 : word) = Some W_6b560.
Proof. vm_refl. Qed.
Lemma D_6b560 : decode_any W_6b560 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b564 : bv 32 := 0x02813483.
Lemma F_6b564 : fetch_word Ubsan.M.loaded_segments (0x6b564 : word) = Some W_6b564.
Proof. vm_refl. Qed.
Lemma D_6b564 : decode_any W_6b564 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b568 : bv 32 := 0x02013903.
Lemma F_6b568 : fetch_word Ubsan.M.loaded_segments (0x6b568 : word) = Some W_6b568.
Proof. vm_refl. Qed.
Lemma D_6b568 : decode_any W_6b568 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b56c : bv 32 := 0x01813983.
Lemma F_6b56c : fetch_word Ubsan.M.loaded_segments (0x6b56c : word) = Some W_6b56c.
Proof. vm_refl. Qed.
Lemma D_6b56c : decode_any W_6b56c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b570 : bv 32 := 0x01013a03.
Lemma F_6b570 : fetch_word Ubsan.M.loaded_segments (0x6b570 : word) = Some W_6b570.
Proof. vm_refl. Qed.
Lemma D_6b570 : decode_any W_6b570 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b574 : bv 32 := 0x00813a83.
Lemma F_6b574 : fetch_word Ubsan.M.loaded_segments (0x6b574 : word) = Some W_6b574.
Proof. vm_refl. Qed.
Lemma D_6b574 : decode_any W_6b574 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b578 : bv 32 := 0x04010113.
Lemma F_6b578 : fetch_word Ubsan.M.loaded_segments (0x6b578 : word) = Some W_6b578.
Proof. vm_refl. Qed.
Lemma D_6b578 : decode_any W_6b578 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b57c : bv 32 := 0x00008067.
Lemma F_6b57c : fetch_word Ubsan.M.loaded_segments (0x6b57c : word) = Some W_6b57c.
Proof. vm_refl. Qed.
Lemma D_6b57c : decode_any W_6b57c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b830 : bv 32 := 0xff010113.
Lemma F_6b830 : fetch_word Ubsan.M.loaded_segments (0x6b830 : word) = Some W_6b830.
Proof. vm_refl. Qed.
Lemma D_6b830 : decode_any W_6b830 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b834 : bv 32 := 0x00113423.
Lemma F_6b834 : fetch_word Ubsan.M.loaded_segments (0x6b834 : word) = Some W_6b834.
Proof. vm_refl. Qed.
Lemma D_6b834 : decode_any W_6b834 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b838 : bv 32 := 0x00050e63.
Lemma F_6b838 : fetch_word Ubsan.M.loaded_segments (0x6b838 : word) = Some W_6b838.
Proof. vm_refl. Qed.
Lemma D_6b838 : decode_any W_6b838 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b83c : bv 32 := 0x00050593.
Lemma F_6b83c : fetch_word Ubsan.M.loaded_segments (0x6b83c : word) = Some W_6b83c.
Proof. vm_refl. Qed.
Lemma D_6b83c : decode_any W_6b83c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b840 : bv 32 := 0x00018517.
Lemma F_6b840 : fetch_word Ubsan.M.loaded_segments (0x6b840 : word) = Some W_6b840.
Proof. vm_refl. Qed.
Lemma D_6b840 : decode_any W_6b840 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b844 : bv 32 := 0x2f053503.
Lemma F_6b844 : fetch_word Ubsan.M.loaded_segments (0x6b844 : word) = Some W_6b844.
Proof. vm_refl. Qed.
Lemma D_6b844 : decode_any W_6b844 = Some (Load SZ8 true 10 10 752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b848 : bv 32 := 0x00800613.
Lemma F_6b848 : fetch_word Ubsan.M.loaded_segments (0x6b848 : word) = Some W_6b848.
Proof. vm_refl. Qed.
Lemma D_6b848 : decode_any W_6b848 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b84c : bv 32 := 0x5050d0ef.
Lemma F_6b84c : fetch_word Ubsan.M.loaded_segments (0x6b84c : word) = Some W_6b84c.
Proof. vm_refl. Qed.
Lemma D_6b84c : decode_any W_6b84c = Some (Jal 1 56580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b850 : bv 32 := 0x01c0006f.
Lemma F_6b850 : fetch_word Ubsan.M.loaded_segments (0x6b850 : word) = Some W_6b850.
Proof. vm_refl. Qed.
Lemma D_6b850 : decode_any W_6b850 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b854 : bv 32 := 0x00018517.
Lemma F_6b854 : fetch_word Ubsan.M.loaded_segments (0x6b854 : word) = Some W_6b854.
Proof. vm_refl. Qed.
Lemma D_6b854 : decode_any W_6b854 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b858 : bv 32 := 0x2dc53503.
Lemma F_6b858 : fetch_word Ubsan.M.loaded_segments (0x6b858 : word) = Some W_6b858.
Proof. vm_refl. Qed.
Lemma D_6b858 : decode_any W_6b858 = Some (Load SZ8 true 10 10 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b85c : bv 32 := 0x41c655b7.
Lemma F_6b85c : fetch_word Ubsan.M.loaded_segments (0x6b85c : word) = Some W_6b85c.
Proof. vm_refl. Qed.
Lemma D_6b85c : decode_any W_6b85c = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b860 : bv 32 := 0xe6d5859b.
Lemma F_6b860 : fetch_word Ubsan.M.loaded_segments (0x6b860 : word) = Some W_6b860.
Proof. vm_refl. Qed.
Lemma D_6b860 : decode_any W_6b860 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b864 : bv 32 := 0x02b505b3.
Lemma F_6b864 : fetch_word Ubsan.M.loaded_segments (0x6b864 : word) = Some W_6b864.
Proof. vm_refl. Qed.
Lemma D_6b864 : decode_any W_6b864 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b868 : bv 32 := 0x00b53023.
Lemma F_6b868 : fetch_word Ubsan.M.loaded_segments (0x6b868 : word) = Some W_6b868.
Proof. vm_refl. Qed.
Lemma D_6b868 : decode_any W_6b868 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b86c : bv 32 := 0x00018517.
Lemma F_6b86c : fetch_word Ubsan.M.loaded_segments (0x6b86c : word) = Some W_6b86c.
Proof. vm_refl. Qed.
Lemma D_6b86c : decode_any W_6b86c = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b870 : bv 32 := 0x2c453503.
Lemma F_6b870 : fetch_word Ubsan.M.loaded_segments (0x6b870 : word) = Some W_6b870.
Proof. vm_refl. Qed.
Lemma D_6b870 : decode_any W_6b870 = Some (Load SZ8 true 10 10 708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b874 : bv 32 := 0x000500a3.
Lemma F_6b874 : fetch_word Ubsan.M.loaded_segments (0x6b874 : word) = Some W_6b874.
Proof. vm_refl. Qed.
Lemma D_6b874 : decode_any W_6b874 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b878 : bv 32 := 0x00053503.
Lemma F_6b878 : fetch_word Ubsan.M.loaded_segments (0x6b878 : word) = Some W_6b878.
Proof. vm_refl. Qed.
Lemma D_6b878 : decode_any W_6b878 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b87c : bv 32 := 0x00020593.
Lemma F_6b87c : fetch_word Ubsan.M.loaded_segments (0x6b87c : word) = Some W_6b87c.
Proof. vm_refl. Qed.
Lemma D_6b87c : decode_any W_6b87c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b880 : bv 32 := 0xfea5b823.
Lemma F_6b880 : fetch_word Ubsan.M.loaded_segments (0x6b880 : word) = Some W_6b880.
Proof. vm_refl. Qed.
Lemma D_6b880 : decode_any W_6b880 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b884 : bv 32 := 0x00813083.
Lemma F_6b884 : fetch_word Ubsan.M.loaded_segments (0x6b884 : word) = Some W_6b884.
Proof. vm_refl. Qed.
Lemma D_6b884 : decode_any W_6b884 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b888 : bv 32 := 0x01010113.
Lemma F_6b888 : fetch_word Ubsan.M.loaded_segments (0x6b888 : word) = Some W_6b888.
Proof. vm_refl. Qed.
Lemma D_6b888 : decode_any W_6b888 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b88c : bv 32 := 0x00008067.
Lemma F_6b88c : fetch_word Ubsan.M.loaded_segments (0x6b88c : word) = Some W_6b88c.
Proof. vm_refl. Qed.
Lemma D_6b88c : decode_any W_6b88c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b890 : bv 32 := 0x00000023.
Lemma F_6b890 : fetch_word Ubsan.M.loaded_segments (0x6b890 : word) = Some W_6b890.
Proof. vm_refl. Qed.
Lemma D_6b890 : decode_any W_6b890 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b894 : bv 32 := 0x00008067.
Lemma F_6b894 : fetch_word Ubsan.M.loaded_segments (0x6b894 : word) = Some W_6b894.
Proof. vm_refl. Qed.
Lemma D_6b894 : decode_any W_6b894 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b898 : bv 32 := 0x00020513.
Lemma F_6b898 : fetch_word Ubsan.M.loaded_segments (0x6b898 : word) = Some W_6b898.
Proof. vm_refl. Qed.
Lemma D_6b898 : decode_any W_6b898 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b89c : bv 32 := 0xf5c50513.
Lemma F_6b89c : fetch_word Ubsan.M.loaded_segments (0x6b89c : word) = Some W_6b89c.
Proof. vm_refl. Qed.
Lemma D_6b89c : decode_any W_6b89c = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8a0 : bv 32 := 0x00008067.
Lemma F_6b8a0 : fetch_word Ubsan.M.loaded_segments (0x6b8a0 : word) = Some W_6b8a0.
Proof. vm_refl. Qed.
Lemma D_6b8a0 : decode_any W_6b8a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8a4 : bv 32 := 0x00020593.
Lemma F_6b8a4 : fetch_word Ubsan.M.loaded_segments (0x6b8a4 : word) = Some W_6b8a4.
Proof. vm_refl. Qed.
Lemma D_6b8a4 : decode_any W_6b8a4 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8a8 : bv 32 := 0x08453613.
Lemma F_6b8a8 : fetch_word Ubsan.M.loaded_segments (0x6b8a8 : word) = Some W_6b8a8.
Proof. vm_refl. Qed.
Lemma D_6b8a8 : decode_any W_6b8a8 = Some (OpImm ALU_SLTU 12 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8ac : bv 32 := 0x40c00633.
Lemma F_6b8ac : fetch_word Ubsan.M.loaded_segments (0x6b8ac : word) = Some W_6b8ac.
Proof. vm_refl. Qed.
Lemma D_6b8ac : decode_any W_6b8ac = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8b0 : bv 32 := 0x00a67533.
Lemma F_6b8b0 : fetch_word Ubsan.M.loaded_segments (0x6b8b0 : word) = Some W_6b8b0.
Proof. vm_refl. Qed.
Lemma D_6b8b0 : decode_any W_6b8b0 = Some (Op ALU_AND 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8b4 : bv 32 := 0xfffad617.
Lemma F_6b8b4 : fetch_word Ubsan.M.loaded_segments (0x6b8b4 : word) = Some W_6b8b4.
Proof. vm_refl. Qed.
Lemma D_6b8b4 : decode_any W_6b8b4 = Some (Auipc 12 1048493, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8b8 : bv 32 := 0xfd05b583.
Lemma F_6b8b8 : fetch_word Ubsan.M.loaded_segments (0x6b8b8 : word) = Some W_6b8b8.
Proof. vm_refl. Qed.
Lemma D_6b8b8 : decode_any W_6b8b8 = Some (Load SZ8 true 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8bc : bv 32 := 0x00151513.
Lemma F_6b8bc : fetch_word Ubsan.M.loaded_segments (0x6b8bc : word) = Some W_6b8bc.
Proof. vm_refl. Qed.
Lemma D_6b8bc : decode_any W_6b8bc = Some (ShiftImm ALU_SLL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8c0 : bv 32 := 0x4b260613.
Lemma F_6b8c0 : fetch_word Ubsan.M.loaded_segments (0x6b8c0 : word) = Some W_6b8c0.
Proof. vm_refl. Qed.
Lemma D_6b8c0 : decode_any W_6b8c0 = Some (OpImm ALU_ADD 12 12 1202, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8c4 : bv 32 := 0x00a60533.
Lemma F_6b8c4 : fetch_word Ubsan.M.loaded_segments (0x6b8c4 : word) = Some W_6b8c4.
Proof. vm_refl. Qed.
Lemma D_6b8c4 : decode_any W_6b8c4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8c8 : bv 32 := 0x00055503.
Lemma F_6b8c8 : fetch_word Ubsan.M.loaded_segments (0x6b8c8 : word) = Some W_6b8c8.
Proof. vm_refl. Qed.
Lemma D_6b8c8 : decode_any W_6b8c8 = Some (Load SZ2 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8cc : bv 32 := 0x0285b583.
Lemma F_6b8cc : fetch_word Ubsan.M.loaded_segments (0x6b8cc : word) = Some W_6b8cc.
Proof. vm_refl. Qed.
Lemma D_6b8cc : decode_any W_6b8cc = Some (Load SZ8 true 11 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8d0 : bv 32 := 0xfffad617.
Lemma F_6b8d0 : fetch_word Ubsan.M.loaded_segments (0x6b8d0 : word) = Some W_6b8d0.
Proof. vm_refl. Qed.
Lemma D_6b8d0 : decode_any W_6b8d0 = Some (Auipc 12 1048493, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8d4 : bv 32 := 0xcee60613.
Lemma F_6b8d4 : fetch_word Ubsan.M.loaded_segments (0x6b8d4 : word) = Some W_6b8d4.
Proof. vm_refl. Qed.
Lemma D_6b8d4 : decode_any W_6b8d4 = Some (OpImm ALU_ADD 12 12 3310, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8d8 : bv 32 := 0x00a60533.
Lemma F_6b8d8 : fetch_word Ubsan.M.loaded_segments (0x6b8d8 : word) = Some W_6b8d8.
Proof. vm_refl. Qed.
Lemma D_6b8d8 : decode_any W_6b8d8 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8dc : bv 32 := 0x1250006f.
Lemma F_6b8dc : fetch_word Ubsan.M.loaded_segments (0x6b8dc : word) = Some W_6b8dc.
Proof. vm_refl. Qed.
Lemma D_6b8dc : decode_any W_6b8dc = Some (Jal 0 2340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8e0 : bv 32 := 0xfd010113.
Lemma F_6b8e0 : fetch_word Ubsan.M.loaded_segments (0x6b8e0 : word) = Some W_6b8e0.
Proof. vm_refl. Qed.
Lemma D_6b8e0 : decode_any W_6b8e0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8e4 : bv 32 := 0x02113423.
Lemma F_6b8e4 : fetch_word Ubsan.M.loaded_segments (0x6b8e4 : word) = Some W_6b8e4.
Proof. vm_refl. Qed.
Lemma D_6b8e4 : decode_any W_6b8e4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8e8 : bv 32 := 0x00600513.
Lemma F_6b8e8 : fetch_word Ubsan.M.loaded_segments (0x6b8e8 : word) = Some W_6b8e8.
Proof. vm_refl. Qed.
Lemma D_6b8e8 : decode_any W_6b8e8 = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8ec : bv 32 := 0x775020ef.
Lemma F_6b8ec : fetch_word Ubsan.M.loaded_segments (0x6b8ec : word) = Some W_6b8ec.
Proof. vm_refl. Qed.
Lemma D_6b8ec : decode_any W_6b8ec = Some (Jal 1 12148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8f0 : bv 32 := 0x00000513.
Lemma F_6b8f0 : fetch_word Ubsan.M.loaded_segments (0x6b8f0 : word) = Some W_6b8f0.
Proof. vm_refl. Qed.
Lemma D_6b8f0 : decode_any W_6b8f0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8f4 : bv 32 := 0x711020ef.
Lemma F_6b8f4 : fetch_word Ubsan.M.loaded_segments (0x6b8f4 : word) = Some W_6b8f4.
Proof. vm_refl. Qed.
Lemma D_6b8f4 : decode_any W_6b8f4 = Some (Jal 1 12048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8f8 : bv 32 := 0x0004b517.
Lemma F_6b8f8 : fetch_word Ubsan.M.loaded_segments (0x6b8f8 : word) = Some W_6b8f8.
Proof. vm_refl. Qed.
Lemma D_6b8f8 : decode_any W_6b8f8 = Some (Auipc 10 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8fc : bv 32 := 0x0c050513.
Lemma F_6b8fc : fetch_word Ubsan.M.loaded_segments (0x6b8fc : word) = Some W_6b8fc.
Proof. vm_refl. Qed.
Lemma D_6b8fc : decode_any W_6b8fc = Some (OpImm ALU_ADD 10 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b900 : bv 32 := 0x68c0e0ef.
Lemma F_6b900 : fetch_word Ubsan.M.loaded_segments (0x6b900 : word) = Some W_6b900.
Proof. vm_refl. Qed.
Lemma D_6b900 : decode_any W_6b900 = Some (Jal 1 59020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b904 : bv 32 := 0x00000613.
Lemma F_6b904 : fetch_word Ubsan.M.loaded_segments (0x6b904 : word) = Some W_6b904.
Proof. vm_refl. Qed.
Lemma D_6b904 : decode_any W_6b904 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b908 : bv 32 := 0x00013423.
Lemma F_6b908 : fetch_word Ubsan.M.loaded_segments (0x6b908 : word) = Some W_6b908.
Proof. vm_refl. Qed.
Lemma D_6b908 : decode_any W_6b908 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b90c : bv 32 := 0x00013823.
Lemma F_6b90c : fetch_word Ubsan.M.loaded_segments (0x6b90c : word) = Some W_6b90c.
Proof. vm_refl. Qed.
Lemma D_6b90c : decode_any W_6b90c = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b910 : bv 32 := 0x00013c23.
Lemma F_6b910 : fetch_word Ubsan.M.loaded_segments (0x6b910 : word) = Some W_6b910.
Proof. vm_refl. Qed.
Lemma D_6b910 : decode_any W_6b910 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b914 : bv 32 := 0x02013023.
Lemma F_6b914 : fetch_word Ubsan.M.loaded_segments (0x6b914 : word) = Some W_6b914.
Proof. vm_refl. Qed.
Lemma D_6b914 : decode_any W_6b914 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b918 : bv 32 := 0x08600893.
Lemma F_6b918 : fetch_word Ubsan.M.loaded_segments (0x6b918 : word) = Some W_6b918.
Proof. vm_refl. Qed.
Lemma D_6b918 : decode_any W_6b918 = Some (OpImm ALU_ADD 17 0 134, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b91c : bv 32 := 0x00600513.
Lemma F_6b91c : fetch_word Ubsan.M.loaded_segments (0x6b91c : word) = Some W_6b91c.
Proof. vm_refl. Qed.
Lemma D_6b91c : decode_any W_6b91c = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b920 : bv 32 := 0x00810593.
Lemma F_6b920 : fetch_word Ubsan.M.loaded_segments (0x6b920 : word) = Some W_6b920.
Proof. vm_refl. Qed.
Lemma D_6b920 : decode_any W_6b920 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b924 : bv 32 := 0x00800693.
Lemma F_6b924 : fetch_word Ubsan.M.loaded_segments (0x6b924 : word) = Some W_6b924.
Proof. vm_refl. Qed.
Lemma D_6b924 : decode_any W_6b924 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b928 : bv 32 := 0x00000073.
Lemma F_6b928 : fetch_word Ubsan.M.loaded_segments (0x6b928 : word) = Some W_6b928.
Proof. vm_refl. Qed.
Lemma D_6b928 : decode_any W_6b928 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b928 : is_ecall W_6b928 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b92c : bv 32 := 0x00020513.
Lemma F_6b92c : fetch_word Ubsan.M.loaded_segments (0x6b92c : word) = Some W_6b92c.
Proof. vm_refl. Qed.
Lemma D_6b92c : decode_any W_6b92c = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b930 : bv 32 := 0xf5852503.
Lemma F_6b930 : fetch_word Ubsan.M.loaded_segments (0x6b930 : word) = Some W_6b930.
Proof. vm_refl. Qed.
Lemma D_6b930 : decode_any W_6b930 = Some (Load SZ4 true 10 10 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b934 : bv 32 := 0x02000613.
Lemma F_6b934 : fetch_word Ubsan.M.loaded_segments (0x6b934 : word) = Some W_6b934.
Proof. vm_refl. Qed.
Lemma D_6b934 : decode_any W_6b934 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b938 : bv 32 := 0x08200893.
Lemma F_6b938 : fetch_word Ubsan.M.loaded_segments (0x6b938 : word) = Some W_6b938.
Proof. vm_refl. Qed.
Lemma D_6b938 : decode_any W_6b938 = Some (OpImm ALU_ADD 17 0 130, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b93c : bv 32 := 0x00600593.
Lemma F_6b93c : fetch_word Ubsan.M.loaded_segments (0x6b93c : word) = Some W_6b93c.
Proof. vm_refl. Qed.
Lemma D_6b93c : decode_any W_6b93c = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b940 : bv 32 := 0x00000073.
Lemma F_6b940 : fetch_word Ubsan.M.loaded_segments (0x6b940 : word) = Some W_6b940.
Proof. vm_refl. Qed.
Lemma D_6b940 : decode_any W_6b940 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b940 : is_ecall W_6b940 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b944 : bv 32 := 0x00c13023.
Lemma F_6b944 : fetch_word Ubsan.M.loaded_segments (0x6b944 : word) = Some W_6b944.
Proof. vm_refl. Qed.
Lemma D_6b944 : decode_any W_6b944 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b948 : bv 32 := 0x08700893.
Lemma F_6b948 : fetch_word Ubsan.M.loaded_segments (0x6b948 : word) = Some W_6b948.
Proof. vm_refl. Qed.
Lemma D_6b948 : decode_any W_6b948 = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b94c : bv 32 := 0x00010593.
Lemma F_6b94c : fetch_word Ubsan.M.loaded_segments (0x6b94c : word) = Some W_6b94c.
Proof. vm_refl. Qed.
Lemma D_6b94c : decode_any W_6b94c = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b950 : bv 32 := 0x00100513.
Lemma F_6b950 : fetch_word Ubsan.M.loaded_segments (0x6b950 : word) = Some W_6b950.
Proof. vm_refl. Qed.
Lemma D_6b950 : decode_any W_6b950 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b954 : bv 32 := 0x00800693.
Lemma F_6b954 : fetch_word Ubsan.M.loaded_segments (0x6b954 : word) = Some W_6b954.
Proof. vm_refl. Qed.
Lemma D_6b954 : decode_any W_6b954 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b958 : bv 32 := 0x00000613.
Lemma F_6b958 : fetch_word Ubsan.M.loaded_segments (0x6b958 : word) = Some W_6b958.
Proof. vm_refl. Qed.
Lemma D_6b958 : decode_any W_6b958 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b95c : bv 32 := 0x00000073.
Lemma F_6b95c : fetch_word Ubsan.M.loaded_segments (0x6b95c : word) = Some W_6b95c.
Proof. vm_refl. Qed.
Lemma D_6b95c : decode_any W_6b95c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b95c : is_ecall W_6b95c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b960 : bv 32 := 0x00000023.
Lemma F_6b960 : fetch_word Ubsan.M.loaded_segments (0x6b960 : word) = Some W_6b960.
Proof. vm_refl. Qed.
Lemma D_6b960 : decode_any W_6b960 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b964 : bv 32 := 0x00900513.
Lemma F_6b964 : fetch_word Ubsan.M.loaded_segments (0x6b964 : word) = Some W_6b964.
Proof. vm_refl. Qed.
Lemma D_6b964 : decode_any W_6b964 = Some (OpImm ALU_ADD 10 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b968 : bv 32 := 0x6f9020ef.
Lemma F_6b968 : fetch_word Ubsan.M.loaded_segments (0x6b968 : word) = Some W_6b968.
Proof. vm_refl. Qed.
Lemma D_6b968 : decode_any W_6b968 = Some (Jal 1 12024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b96c : bv 32 := 0x07f00513.
Lemma F_6b96c : fetch_word Ubsan.M.loaded_segments (0x6b96c : word) = Some W_6b96c.
Proof. vm_refl. Qed.
Lemma D_6b96c : decode_any W_6b96c = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b970 : bv 32 := 0x004000ef.
Lemma F_6b970 : fetch_word Ubsan.M.loaded_segments (0x6b970 : word) = Some W_6b970.
Proof. vm_refl. Qed.
Lemma D_6b970 : decode_any W_6b970 = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b974 : bv 32 := 0x00050593.
Lemma F_6b974 : fetch_word Ubsan.M.loaded_segments (0x6b974 : word) = Some W_6b974.
Proof. vm_refl. Qed.
Lemma D_6b974 : decode_any W_6b974 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b978 : bv 32 := 0x05e00893.
Lemma F_6b978 : fetch_word Ubsan.M.loaded_segments (0x6b978 : word) = Some W_6b978.
Proof. vm_refl. Qed.
Lemma D_6b978 : decode_any W_6b978 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b97c : bv 32 := 0x00000073.
Lemma F_6b97c : fetch_word Ubsan.M.loaded_segments (0x6b97c : word) = Some W_6b97c.
Proof. vm_refl. Qed.
Lemma D_6b97c : decode_any W_6b97c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b97c : is_ecall W_6b97c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b980 : bv 32 := 0x05d00893.
Lemma F_6b980 : fetch_word Ubsan.M.loaded_segments (0x6b980 : word) = Some W_6b980.
Proof. vm_refl. Qed.
Lemma D_6b980 : decode_any W_6b980 = Some (OpImm ALU_ADD 17 0 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b984 : bv 32 := 0x00058513.
Lemma F_6b984 : fetch_word Ubsan.M.loaded_segments (0x6b984 : word) = Some W_6b984.
Proof. vm_refl. Qed.
Lemma D_6b984 : decode_any W_6b984 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b988 : bv 32 := 0x00000073.
Lemma F_6b988 : fetch_word Ubsan.M.loaded_segments (0x6b988 : word) = Some W_6b988.
Proof. vm_refl. Qed.
Lemma D_6b988 : decode_any W_6b988 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b988 : is_ecall W_6b988 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b98c : bv 32 := 0xff9ff06f.
Lemma F_6b98c : fetch_word Ubsan.M.loaded_segments (0x6b98c : word) = Some W_6b98c.
Proof. vm_refl. Qed.
Lemma D_6b98c : decode_any W_6b98c = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b990 : bv 32 := 0xff010113.
Lemma F_6b990 : fetch_word Ubsan.M.loaded_segments (0x6b990 : word) = Some W_6b990.
Proof. vm_refl. Qed.
Lemma D_6b990 : decode_any W_6b990 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b994 : bv 32 := 0x00113423.
Lemma F_6b994 : fetch_word Ubsan.M.loaded_segments (0x6b994 : word) = Some W_6b994.
Proof. vm_refl. Qed.
Lemma D_6b994 : decode_any W_6b994 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b998 : bv 32 := 0x00068713.
Lemma F_6b998 : fetch_word Ubsan.M.loaded_segments (0x6b998 : word) = Some W_6b998.
Proof. vm_refl. Qed.
Lemma D_6b998 : decode_any W_6b998 = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b99c : bv 32 := 0x00060793.
Lemma F_6b99c : fetch_word Ubsan.M.loaded_segments (0x6b99c : word) = Some W_6b99c.
Proof. vm_refl. Qed.
Lemma D_6b99c : decode_any W_6b99c = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9a0 : bv 32 := 0x00058693.
Lemma F_6b9a0 : fetch_word Ubsan.M.loaded_segments (0x6b9a0 : word) = Some W_6b9a0.
Proof. vm_refl. Qed.
Lemma D_6b9a0 : decode_any W_6b9a0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9a4 : bv 32 := 0x00050613.
Lemma F_6b9a4 : fetch_word Ubsan.M.loaded_segments (0x6b9a4 : word) = Some W_6b9a4.
Proof. vm_refl. Qed.
Lemma D_6b9a4 : decode_any W_6b9a4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9a8 : bv 32 := 0x00019517.
Lemma F_6b9a8 : fetch_word Ubsan.M.loaded_segments (0x6b9a8 : word) = Some W_6b9a8.
Proof. vm_refl. Qed.
Lemma D_6b9a8 : decode_any W_6b9a8 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9ac : bv 32 := 0xfffa6597.
Lemma F_6b9ac : fetch_word Ubsan.M.loaded_segments (0x6b9ac : word) = Some W_6b9ac.
Proof. vm_refl. Qed.
Lemma D_6b9ac : decode_any W_6b9ac = Some (Auipc 11 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9b0 : bv 32 := 0x3a050513.
Lemma F_6b9b0 : fetch_word Ubsan.M.loaded_segments (0x6b9b0 : word) = Some W_6b9b0.
Proof. vm_refl. Qed.
Lemma D_6b9b0 : decode_any W_6b9b0 = Some (OpImm ALU_ADD 10 10 928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9b4 : bv 32 := 0x45558593.
Lemma F_6b9b4 : fetch_word Ubsan.M.loaded_segments (0x6b9b4 : word) = Some W_6b9b4.
Proof. vm_refl. Qed.
Lemma D_6b9b4 : decode_any W_6b9b4 = Some (OpImm ALU_ADD 11 11 1109, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9b8 : bv 32 := 0x204030ef.
Lemma F_6b9b8 : fetch_word Ubsan.M.loaded_segments (0x6b9b8 : word) = Some W_6b9b8.
Proof. vm_refl. Qed.
Lemma D_6b9b8 : decode_any W_6b9b8 = Some (Jal 1 12804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9bc : bv 32 := 0xf25ff0ef.
Lemma F_6b9bc : fetch_word Ubsan.M.loaded_segments (0x6b9bc : word) = Some W_6b9bc.
Proof. vm_refl. Qed.
Lemma D_6b9bc : decode_any W_6b9bc = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9c0 : bv 32 := 0xfd010113.
Lemma F_6b9c0 : fetch_word Ubsan.M.loaded_segments (0x6b9c0 : word) = Some W_6b9c0.
Proof. vm_refl. Qed.
Lemma D_6b9c0 : decode_any W_6b9c0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9c4 : bv 32 := 0x02113423.
Lemma F_6b9c4 : fetch_word Ubsan.M.loaded_segments (0x6b9c4 : word) = Some W_6b9c4.
Proof. vm_refl. Qed.
Lemma D_6b9c4 : decode_any W_6b9c4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9c8 : bv 32 := 0x02813023.
Lemma F_6b9c8 : fetch_word Ubsan.M.loaded_segments (0x6b9c8 : word) = Some W_6b9c8.
Proof. vm_refl. Qed.
Lemma D_6b9c8 : decode_any W_6b9c8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9cc : bv 32 := 0x00913c23.
Lemma F_6b9cc : fetch_word Ubsan.M.loaded_segments (0x6b9cc : word) = Some W_6b9cc.
Proof. vm_refl. Qed.
Lemma D_6b9cc : decode_any W_6b9cc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9d0 : bv 32 := 0x01213823.
Lemma F_6b9d0 : fetch_word Ubsan.M.loaded_segments (0x6b9d0 : word) = Some W_6b9d0.
Proof. vm_refl. Qed.
Lemma D_6b9d0 : decode_any W_6b9d0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9d4 : bv 32 := 0x01313423.
Lemma F_6b9d4 : fetch_word Ubsan.M.loaded_segments (0x6b9d4 : word) = Some W_6b9d4.
Proof. vm_refl. Qed.
Lemma D_6b9d4 : decode_any W_6b9d4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9d8 : bv 32 := 0x0004b517.
Lemma F_6b9d8 : fetch_word Ubsan.M.loaded_segments (0x6b9d8 : word) = Some W_6b9d8.
Proof. vm_refl. Qed.
Lemma D_6b9d8 : decode_any W_6b9d8 = Some (Auipc 10 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9dc : bv 32 := 0xfe850913.
Lemma F_6b9dc : fetch_word Ubsan.M.loaded_segments (0x6b9dc : word) = Some W_6b9dc.
Proof. vm_refl. Qed.
Lemma D_6b9dc : decode_any W_6b9dc = Some (OpImm ALU_ADD 18 10 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9e0 : bv 32 := 0x00490413.
Lemma F_6b9e0 : fetch_word Ubsan.M.loaded_segments (0x6b9e0 : word) = Some W_6b9e0.
Proof. vm_refl. Qed.
Lemma D_6b9e0 : decode_any W_6b9e0 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9e4 : bv 32 := 0x00040513.
Lemma F_6b9e4 : fetch_word Ubsan.M.loaded_segments (0x6b9e4 : word) = Some W_6b9e4.
Proof. vm_refl. Qed.
Lemma D_6b9e4 : decode_any W_6b9e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9e8 : bv 32 := 0x5a40e0ef.
Lemma F_6b9e8 : fetch_word Ubsan.M.loaded_segments (0x6b9e8 : word) = Some W_6b9e8.
Proof. vm_refl. Qed.
Lemma D_6b9e8 : decode_any W_6b9e8 = Some (Jal 1 58788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9ec : bv 32 := 0x01093503.
Lemma F_6b9ec : fetch_word Ubsan.M.loaded_segments (0x6b9ec : word) = Some W_6b9ec.
Proof. vm_refl. Qed.
Lemma D_6b9ec : decode_any W_6b9ec = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9f0 : bv 32 := 0x06050863.
Lemma F_6b9f0 : fetch_word Ubsan.M.loaded_segments (0x6b9f0 : word) = Some W_6b9f0.
Proof. vm_refl. Qed.
Lemma D_6b9f0 : decode_any W_6b9f0 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9f4 : bv 32 := 0x00892583.
Lemma F_6b9f4 : fetch_word Ubsan.M.loaded_segments (0x6b9f4 : word) = Some W_6b9f4.
Proof. vm_refl. Qed.
Lemma D_6b9f4 : decode_any W_6b9f4 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9f8 : bv 32 := 0x0180006f.
Lemma F_6b9f8 : fetch_word Ubsan.M.loaded_segments (0x6b9f8 : word) = Some W_6b9f8.
Proof. vm_refl. Qed.
Lemma D_6b9f8 : decode_any W_6b9f8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9fc : bv 32 := 0x00053503.
Lemma F_6b9fc : fetch_word Ubsan.M.loaded_segments (0x6b9fc : word) = Some W_6b9fc.
Proof. vm_refl. Qed.
Lemma D_6b9fc : decode_any W_6b9fc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba00 : bv 32 := 0x02000593.
Lemma F_6ba00 : fetch_word Ubsan.M.loaded_segments (0x6ba00 : word) = Some W_6ba00.
Proof. vm_refl. Qed.
Lemma D_6ba00 : decode_any W_6ba00 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba04 : bv 32 := 0x00b92423.
Lemma F_6ba04 : fetch_word Ubsan.M.loaded_segments (0x6ba04 : word) = Some W_6ba04.
Proof. vm_refl. Qed.
Lemma D_6ba04 : decode_any W_6ba04 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba08 : bv 32 := 0x00a93823.
Lemma F_6ba08 : fetch_word Ubsan.M.loaded_segments (0x6ba08 : word) = Some W_6ba08.
Proof. vm_refl. Qed.
Lemma D_6ba08 : decode_any W_6ba08 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba0c : bv 32 := 0x04050a63.
Lemma F_6ba0c : fetch_word Ubsan.M.loaded_segments (0x6ba0c : word) = Some W_6ba0c.
Proof. vm_refl. Qed.
Lemma D_6ba0c : decode_any W_6ba0c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba10 : bv 32 := 0xfff5861b.
Lemma F_6ba10 : fetch_word Ubsan.M.loaded_segments (0x6ba10 : word) = Some W_6ba10.
Proof. vm_refl. Qed.
Lemma D_6ba10 : decode_any W_6ba10 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba14 : bv 32 := 0x00c92423.
Lemma F_6ba14 : fetch_word Ubsan.M.loaded_segments (0x6ba14 : word) = Some W_6ba14.
Proof. vm_refl. Qed.
Lemma D_6ba14 : decode_any W_6ba14 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba18 : bv 32 := 0xfeb052e3.
Lemma F_6ba18 : fetch_word Ubsan.M.loaded_segments (0x6ba18 : word) = Some W_6ba18.
Proof. vm_refl. Qed.
Lemma D_6ba18 : decode_any W_6ba18 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba1c : bv 32 := 0x01093503.
Lemma F_6ba1c : fetch_word Ubsan.M.loaded_segments (0x6ba1c : word) = Some W_6ba1c.
Proof. vm_refl. Qed.
Lemma D_6ba1c : decode_any W_6ba1c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba20 : bv 32 := 0x00361613.
Lemma F_6ba20 : fetch_word Ubsan.M.loaded_segments (0x6ba20 : word) = Some W_6ba20.
Proof. vm_refl. Qed.
Lemma D_6ba20 : decode_any W_6ba20 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba24 : bv 32 := 0x00c50533.
Lemma F_6ba24 : fetch_word Ubsan.M.loaded_segments (0x6ba24 : word) = Some W_6ba24.
Proof. vm_refl. Qed.
Lemma D_6ba24 : decode_any W_6ba24 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba28 : bv 32 := 0x00853983.
Lemma F_6ba28 : fetch_word Ubsan.M.loaded_segments (0x6ba28 : word) = Some W_6ba28.
Proof. vm_refl. Qed.
Lemma D_6ba28 : decode_any W_6ba28 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba2c : bv 32 := 0x10853483.
Lemma F_6ba2c : fetch_word Ubsan.M.loaded_segments (0x6ba2c : word) = Some W_6ba2c.
Proof. vm_refl. Qed.
Lemma D_6ba2c : decode_any W_6ba2c = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba30 : bv 32 := 0x00040513.
Lemma F_6ba30 : fetch_word Ubsan.M.loaded_segments (0x6ba30 : word) = Some W_6ba30.
Proof. vm_refl. Qed.
Lemma D_6ba30 : decode_any W_6ba30 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba34 : bv 32 := 0x7e00e0ef.
Lemma F_6ba34 : fetch_word Ubsan.M.loaded_segments (0x6ba34 : word) = Some W_6ba34.
Proof. vm_refl. Qed.
Lemma D_6ba34 : decode_any W_6ba34 = Some (Jal 1 59360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba38 : bv 32 := 0x00048513.
Lemma F_6ba38 : fetch_word Ubsan.M.loaded_segments (0x6ba38 : word) = Some W_6ba38.
Proof. vm_refl. Qed.
Lemma D_6ba38 : decode_any W_6ba38 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba3c : bv 32 := 0x000980e7.
Lemma F_6ba3c : fetch_word Ubsan.M.loaded_segments (0x6ba3c : word) = Some W_6ba3c.
Proof. vm_refl. Qed.
Lemma D_6ba3c : decode_any W_6ba3c = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba40 : bv 32 := 0x00040513.
Lemma F_6ba40 : fetch_word Ubsan.M.loaded_segments (0x6ba40 : word) = Some W_6ba40.
Proof. vm_refl. Qed.
Lemma D_6ba40 : decode_any W_6ba40 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba44 : bv 32 := 0x5480e0ef.
Lemma F_6ba44 : fetch_word Ubsan.M.loaded_segments (0x6ba44 : word) = Some W_6ba44.
Proof. vm_refl. Qed.
Lemma D_6ba44 : decode_any W_6ba44 = Some (Jal 1 58696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba48 : bv 32 := 0x00892503.
Lemma F_6ba48 : fetch_word Ubsan.M.loaded_segments (0x6ba48 : word) = Some W_6ba48.
Proof. vm_refl. Qed.
Lemma D_6ba48 : decode_any W_6ba48 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba4c : bv 32 := 0xfff5061b.
Lemma F_6ba4c : fetch_word Ubsan.M.loaded_segments (0x6ba4c : word) = Some W_6ba4c.
Proof. vm_refl. Qed.
Lemma D_6ba4c : decode_any W_6ba4c = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba50 : bv 32 := 0x00c92423.
Lemma F_6ba50 : fetch_word Ubsan.M.loaded_segments (0x6ba50 : word) = Some W_6ba50.
Proof. vm_refl. Qed.
Lemma D_6ba50 : decode_any W_6ba50 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba54 : bv 32 := 0xfca044e3.
Lemma F_6ba54 : fetch_word Ubsan.M.loaded_segments (0x6ba54 : word) = Some W_6ba54.
Proof. vm_refl. Qed.
Lemma D_6ba54 : decode_any W_6ba54 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba58 : bv 32 := 0x01093503.
Lemma F_6ba58 : fetch_word Ubsan.M.loaded_segments (0x6ba58 : word) = Some W_6ba58.
Proof. vm_refl. Qed.
Lemma D_6ba58 : decode_any W_6ba58 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba5c : bv 32 := 0xfa1ff06f.
Lemma F_6ba5c : fetch_word Ubsan.M.loaded_segments (0x6ba5c : word) = Some W_6ba5c.
Proof. vm_refl. Qed.
Lemma D_6ba5c : decode_any W_6ba5c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba60 : bv 32 := 0x00100513.
Lemma F_6ba60 : fetch_word Ubsan.M.loaded_segments (0x6ba60 : word) = Some W_6ba60.
Proof. vm_refl. Qed.
Lemma D_6ba60 : decode_any W_6ba60 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba64 : bv 32 := 0x00a90023.
Lemma F_6ba64 : fetch_word Ubsan.M.loaded_segments (0x6ba64 : word) = Some W_6ba64.
Proof. vm_refl. Qed.
Lemma D_6ba64 : decode_any W_6ba64 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba68 : bv 32 := 0x00040513.
Lemma F_6ba68 : fetch_word Ubsan.M.loaded_segments (0x6ba68 : word) = Some W_6ba68.
Proof. vm_refl. Qed.
Lemma D_6ba68 : decode_any W_6ba68 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba6c : bv 32 := 0x02813083.
Lemma F_6ba6c : fetch_word Ubsan.M.loaded_segments (0x6ba6c : word) = Some W_6ba6c.
Proof. vm_refl. Qed.
Lemma D_6ba6c : decode_any W_6ba6c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba70 : bv 32 := 0x02013403.
Lemma F_6ba70 : fetch_word Ubsan.M.loaded_segments (0x6ba70 : word) = Some W_6ba70.
Proof. vm_refl. Qed.
Lemma D_6ba70 : decode_any W_6ba70 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba74 : bv 32 := 0x01813483.
Lemma F_6ba74 : fetch_word Ubsan.M.loaded_segments (0x6ba74 : word) = Some W_6ba74.
Proof. vm_refl. Qed.
Lemma D_6ba74 : decode_any W_6ba74 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba78 : bv 32 := 0x01013903.
Lemma F_6ba78 : fetch_word Ubsan.M.loaded_segments (0x6ba78 : word) = Some W_6ba78.
Proof. vm_refl. Qed.
Lemma D_6ba78 : decode_any W_6ba78 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba7c : bv 32 := 0x00813983.
Lemma F_6ba7c : fetch_word Ubsan.M.loaded_segments (0x6ba7c : word) = Some W_6ba7c.
Proof. vm_refl. Qed.
Lemma D_6ba7c : decode_any W_6ba7c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba80 : bv 32 := 0x03010113.
Lemma F_6ba80 : fetch_word Ubsan.M.loaded_segments (0x6ba80 : word) = Some W_6ba80.
Proof. vm_refl. Qed.
Lemma D_6ba80 : decode_any W_6ba80 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba84 : bv 32 := 0x7900e06f.
Lemma F_6ba84 : fetch_word Ubsan.M.loaded_segments (0x6ba84 : word) = Some W_6ba84.
Proof. vm_refl. Qed.
Lemma D_6ba84 : decode_any W_6ba84 = Some (Jal 0 59280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba88 : bv 32 := 0x00008067.
Lemma F_6ba88 : fetch_word Ubsan.M.loaded_segments (0x6ba88 : word) = Some W_6ba88.
Proof. vm_refl. Qed.
Lemma D_6ba88 : decode_any W_6ba88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba8c : bv 32 := 0xfd010113.
Lemma F_6ba8c : fetch_word Ubsan.M.loaded_segments (0x6ba8c : word) = Some W_6ba8c.
Proof. vm_refl. Qed.
Lemma D_6ba8c : decode_any W_6ba8c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba90 : bv 32 := 0x02113423.
Lemma F_6ba90 : fetch_word Ubsan.M.loaded_segments (0x6ba90 : word) = Some W_6ba90.
Proof. vm_refl. Qed.
Lemma D_6ba90 : decode_any W_6ba90 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba94 : bv 32 := 0x02813023.
Lemma F_6ba94 : fetch_word Ubsan.M.loaded_segments (0x6ba94 : word) = Some W_6ba94.
Proof. vm_refl. Qed.
Lemma D_6ba94 : decode_any W_6ba94 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba98 : bv 32 := 0x00913c23.
Lemma F_6ba98 : fetch_word Ubsan.M.loaded_segments (0x6ba98 : word) = Some W_6ba98.
Proof. vm_refl. Qed.
Lemma D_6ba98 : decode_any W_6ba98 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba9c : bv 32 := 0x01213823.
Lemma F_6ba9c : fetch_word Ubsan.M.loaded_segments (0x6ba9c : word) = Some W_6ba9c.
Proof. vm_refl. Qed.
Lemma D_6ba9c : decode_any W_6ba9c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6baa0 : bv 32 := 0x01313423.
Lemma F_6baa0 : fetch_word Ubsan.M.loaded_segments (0x6baa0 : word) = Some W_6baa0.
Proof. vm_refl. Qed.
Lemma D_6baa0 : decode_any W_6baa0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6baa4 : bv 32 := 0x00050493.
Lemma F_6baa4 : fetch_word Ubsan.M.loaded_segments (0x6baa4 : word) = Some W_6baa4.
Proof. vm_refl. Qed.
Lemma D_6baa4 : decode_any W_6baa4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6baa8 : bv 32 := 0x0004b517.
Lemma F_6baa8 : fetch_word Ubsan.M.loaded_segments (0x6baa8 : word) = Some W_6baa8.
Proof. vm_refl. Qed.
Lemma D_6baa8 : decode_any W_6baa8 = Some (Auipc 10 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6baac : bv 32 := 0xf1850993.
Lemma F_6baac : fetch_word Ubsan.M.loaded_segments (0x6baac : word) = Some W_6baac.
Proof. vm_refl. Qed.
Lemma D_6baac : decode_any W_6baac = Some (OpImm ALU_ADD 19 10 3864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bab0 : bv 32 := 0x00498413.
Lemma F_6bab0 : fetch_word Ubsan.M.loaded_segments (0x6bab0 : word) = Some W_6bab0.
Proof. vm_refl. Qed.
Lemma D_6bab0 : decode_any W_6bab0 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bab4 : bv 32 := 0x00040513.
Lemma F_6bab4 : fetch_word Ubsan.M.loaded_segments (0x6bab4 : word) = Some W_6bab4.
Proof. vm_refl. Qed.
Lemma D_6bab4 : decode_any W_6bab4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bab8 : bv 32 := 0x4d40e0ef.
Lemma F_6bab8 : fetch_word Ubsan.M.loaded_segments (0x6bab8 : word) = Some W_6bab8.
Proof. vm_refl. Qed.
Lemma D_6bab8 : decode_any W_6bab8 = Some (Jal 1 58580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6babc : bv 32 := 0x0009c503.
Lemma F_6babc : fetch_word Ubsan.M.loaded_segments (0x6babc : word) = Some W_6babc.
Proof. vm_refl. Qed.
Lemma D_6babc : decode_any W_6babc = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bac0 : bv 32 := 0xfff00913.
Lemma F_6bac0 : fetch_word Ubsan.M.loaded_segments (0x6bac0 : word) = Some W_6bac0.
Proof. vm_refl. Qed.
Lemma D_6bac0 : decode_any W_6bac0 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bac4 : bv 32 := 0x06051263.
Lemma F_6bac4 : fetch_word Ubsan.M.loaded_segments (0x6bac4 : word) = Some W_6bac4.
Proof. vm_refl. Qed.
Lemma D_6bac4 : decode_any W_6bac4 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bac8 : bv 32 := 0x0109b503.
Lemma F_6bac8 : fetch_word Ubsan.M.loaded_segments (0x6bac8 : word) = Some W_6bac8.
Proof. vm_refl. Qed.
Lemma D_6bac8 : decode_any W_6bac8 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bacc : bv 32 := 0x00051663.
Lemma F_6bacc : fetch_word Ubsan.M.loaded_segments (0x6bacc : word) = Some W_6bacc.
Proof. vm_refl. Qed.
Lemma D_6bacc : decode_any W_6bacc = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bad0 : bv 32 := 0x01898513.
Lemma F_6bad0 : fetch_word Ubsan.M.loaded_segments (0x6bad0 : word) = Some W_6bad0.
Proof. vm_refl. Qed.
Lemma D_6bad0 : decode_any W_6bad0 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bad4 : bv 32 := 0x00a9b823.
Lemma F_6bad4 : fetch_word Ubsan.M.loaded_segments (0x6bad4 : word) = Some W_6bad4.
Proof. vm_refl. Qed.
Lemma D_6bad4 : decode_any W_6bad4 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bad8 : bv 32 := 0x0089a583.
Lemma F_6bad8 : fetch_word Ubsan.M.loaded_segments (0x6bad8 : word) = Some W_6bad8.
Proof. vm_refl. Qed.
Lemma D_6bad8 : decode_any W_6bad8 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6badc : bv 32 := 0x02000613.
Lemma F_6badc : fetch_word Ubsan.M.loaded_segments (0x6badc : word) = Some W_6badc.
Proof. vm_refl. Qed.
Lemma D_6badc : decode_any W_6badc = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bae0 : bv 32 := 0x02c59263.
Lemma F_6bae0 : fetch_word Ubsan.M.loaded_segments (0x6bae0 : word) = Some W_6bae0.
Proof. vm_refl. Qed.
Lemma D_6bae0 : decode_any W_6bae0 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bae4 : bv 32 := 0x20800513.
Lemma F_6bae4 : fetch_word Ubsan.M.loaded_segments (0x6bae4 : word) = Some W_6bae4.
Proof. vm_refl. Qed.
Lemma D_6bae4 : decode_any W_6bae4 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bae8 : bv 32 := 0x00100593.
Lemma F_6bae8 : fetch_word Ubsan.M.loaded_segments (0x6bae8 : word) = Some W_6bae8.
Proof. vm_refl. Qed.
Lemma D_6bae8 : decode_any W_6bae8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6baec : bv 32 := 0x71c000ef.
Lemma F_6baec : fetch_word Ubsan.M.loaded_segments (0x6baec : word) = Some W_6baec.
Proof. vm_refl. Qed.
Lemma D_6baec : decode_any W_6baec = Some (Jal 1 1820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6baf0 : bv 32 := 0x02050c63.
Lemma F_6baf0 : fetch_word Ubsan.M.loaded_segments (0x6baf0 : word) = Some W_6baf0.
Proof. vm_refl. Qed.
Lemma D_6baf0 : decode_any W_6baf0 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6baf4 : bv 32 := 0x00000593.
Lemma F_6baf4 : fetch_word Ubsan.M.loaded_segments (0x6baf4 : word) = Some W_6baf4.
Proof. vm_refl. Qed.
Lemma D_6baf4 : decode_any W_6baf4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6baf8 : bv 32 := 0x0109b603.
Lemma F_6baf8 : fetch_word Ubsan.M.loaded_segments (0x6baf8 : word) = Some W_6baf8.
Proof. vm_refl. Qed.
Lemma D_6baf8 : decode_any W_6baf8 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bafc : bv 32 := 0x00c53023.
Lemma F_6bafc : fetch_word Ubsan.M.loaded_segments (0x6bafc : word) = Some W_6bafc.
Proof. vm_refl. Qed.
Lemma D_6bafc : decode_any W_6bafc = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb00 : bv 32 := 0x00a9b823.
Lemma F_6bb00 : fetch_word Ubsan.M.loaded_segments (0x6bb00 : word) = Some W_6bb00.
Proof. vm_refl. Qed.
Lemma D_6bb00 : decode_any W_6bb00 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb04 : bv 32 := 0x00000913.
Lemma F_6bb04 : fetch_word Ubsan.M.loaded_segments (0x6bb04 : word) = Some W_6bb04.
Proof. vm_refl. Qed.
Lemma D_6bb04 : decode_any W_6bb04 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb08 : bv 32 := 0x00359613.
Lemma F_6bb08 : fetch_word Ubsan.M.loaded_segments (0x6bb08 : word) = Some W_6bb08.
Proof. vm_refl. Qed.
Lemma D_6bb08 : decode_any W_6bb08 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb0c : bv 32 := 0x00c50533.
Lemma F_6bb0c : fetch_word Ubsan.M.loaded_segments (0x6bb0c : word) = Some W_6bb0c.
Proof. vm_refl. Qed.
Lemma D_6bb0c : decode_any W_6bb0c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb10 : bv 32 := 0x00000617.
Lemma F_6bb10 : fetch_word Ubsan.M.loaded_segments (0x6bb10 : word) = Some W_6bb10.
Proof. vm_refl. Qed.
Lemma D_6bb10 : decode_any W_6bb10 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb14 : bv 32 := 0x00158593.
Lemma F_6bb14 : fetch_word Ubsan.M.loaded_segments (0x6bb14 : word) = Some W_6bb14.
Proof. vm_refl. Qed.
Lemma D_6bb14 : decode_any W_6bb14 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb18 : bv 32 := 0x04060613.
Lemma F_6bb18 : fetch_word Ubsan.M.loaded_segments (0x6bb18 : word) = Some W_6bb18.
Proof. vm_refl. Qed.
Lemma D_6bb18 : decode_any W_6bb18 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb1c : bv 32 := 0x00c53423.
Lemma F_6bb1c : fetch_word Ubsan.M.loaded_segments (0x6bb1c : word) = Some W_6bb1c.
Proof. vm_refl. Qed.
Lemma D_6bb1c : decode_any W_6bb1c = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb20 : bv 32 := 0x10953423.
Lemma F_6bb20 : fetch_word Ubsan.M.loaded_segments (0x6bb20 : word) = Some W_6bb20.
Proof. vm_refl. Qed.
Lemma D_6bb20 : decode_any W_6bb20 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb24 : bv 32 := 0x00b9a423.
Lemma F_6bb24 : fetch_word Ubsan.M.loaded_segments (0x6bb24 : word) = Some W_6bb24.
Proof. vm_refl. Qed.
Lemma D_6bb24 : decode_any W_6bb24 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb28 : bv 32 := 0x00040513.
Lemma F_6bb28 : fetch_word Ubsan.M.loaded_segments (0x6bb28 : word) = Some W_6bb28.
Proof. vm_refl. Qed.
Lemma D_6bb28 : decode_any W_6bb28 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb2c : bv 32 := 0x6e80e0ef.
Lemma F_6bb2c : fetch_word Ubsan.M.loaded_segments (0x6bb2c : word) = Some W_6bb2c.
Proof. vm_refl. Qed.
Lemma D_6bb2c : decode_any W_6bb2c = Some (Jal 1 59112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb30 : bv 32 := 0x00090513.
Lemma F_6bb30 : fetch_word Ubsan.M.loaded_segments (0x6bb30 : word) = Some W_6bb30.
Proof. vm_refl. Qed.
Lemma D_6bb30 : decode_any W_6bb30 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb34 : bv 32 := 0x02813083.
Lemma F_6bb34 : fetch_word Ubsan.M.loaded_segments (0x6bb34 : word) = Some W_6bb34.
Proof. vm_refl. Qed.
Lemma D_6bb34 : decode_any W_6bb34 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb38 : bv 32 := 0x02013403.
Lemma F_6bb38 : fetch_word Ubsan.M.loaded_segments (0x6bb38 : word) = Some W_6bb38.
Proof. vm_refl. Qed.
Lemma D_6bb38 : decode_any W_6bb38 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb3c : bv 32 := 0x01813483.
Lemma F_6bb3c : fetch_word Ubsan.M.loaded_segments (0x6bb3c : word) = Some W_6bb3c.
Proof. vm_refl. Qed.
Lemma D_6bb3c : decode_any W_6bb3c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb40 : bv 32 := 0x01013903.
Lemma F_6bb40 : fetch_word Ubsan.M.loaded_segments (0x6bb40 : word) = Some W_6bb40.
Proof. vm_refl. Qed.
Lemma D_6bb40 : decode_any W_6bb40 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb44 : bv 32 := 0x00813983.
Lemma F_6bb44 : fetch_word Ubsan.M.loaded_segments (0x6bb44 : word) = Some W_6bb44.
Proof. vm_refl. Qed.
Lemma D_6bb44 : decode_any W_6bb44 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb48 : bv 32 := 0x03010113.
Lemma F_6bb48 : fetch_word Ubsan.M.loaded_segments (0x6bb48 : word) = Some W_6bb48.
Proof. vm_refl. Qed.
Lemma D_6bb48 : decode_any W_6bb48 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb4c : bv 32 := 0x00008067.
Lemma F_6bb4c : fetch_word Ubsan.M.loaded_segments (0x6bb4c : word) = Some W_6bb4c.
Proof. vm_refl. Qed.
Lemma D_6bb4c : decode_any W_6bb4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb50 : bv 32 := 0x00050067.
Lemma F_6bb50 : fetch_word Ubsan.M.loaded_segments (0x6bb50 : word) = Some W_6bb50.
Proof. vm_refl. Qed.
Lemma D_6bb50 : decode_any W_6bb50 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb54 : bv 32 := 0x00008067.
Lemma F_6bb54 : fetch_word Ubsan.M.loaded_segments (0x6bb54 : word) = Some W_6bb54.
Proof. vm_refl. Qed.
Lemma D_6bb54 : decode_any W_6bb54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb58 : bv 32 := 0xfe010113.
Lemma F_6bb58 : fetch_word Ubsan.M.loaded_segments (0x6bb58 : word) = Some W_6bb58.
Proof. vm_refl. Qed.
Lemma D_6bb58 : decode_any W_6bb58 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb5c : bv 32 := 0x00113c23.
Lemma F_6bb5c : fetch_word Ubsan.M.loaded_segments (0x6bb5c : word) = Some W_6bb5c.
Proof. vm_refl. Qed.
Lemma D_6bb5c : decode_any W_6bb5c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb60 : bv 32 := 0x00813823.
Lemma F_6bb60 : fetch_word Ubsan.M.loaded_segments (0x6bb60 : word) = Some W_6bb60.
Proof. vm_refl. Qed.
Lemma D_6bb60 : decode_any W_6bb60 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb64 : bv 32 := 0x00913423.
Lemma F_6bb64 : fetch_word Ubsan.M.loaded_segments (0x6bb64 : word) = Some W_6bb64.
Proof. vm_refl. Qed.
Lemma D_6bb64 : decode_any W_6bb64 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb68 : bv 32 := 0x00018517.
Lemma F_6bb68 : fetch_word Ubsan.M.loaded_segments (0x6bb68 : word) = Some W_6bb68.
Proof. vm_refl. Qed.
Lemma D_6bb68 : decode_any W_6bb68 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb6c : bv 32 := 0x00018597.
Lemma F_6bb6c : fetch_word Ubsan.M.loaded_segments (0x6bb6c : word) = Some W_6bb6c.
Proof. vm_refl. Qed.
Lemma D_6bb6c : decode_any W_6bb6c = Some (Auipc 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb70 : bv 32 := 0xff853503.
Lemma F_6bb70 : fetch_word Ubsan.M.loaded_segments (0x6bb70 : word) = Some W_6bb70.
Proof. vm_refl. Qed.
Lemma D_6bb70 : decode_any W_6bb70 = Some (Load SZ8 true 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb74 : bv 32 := 0xffc5b403.
Lemma F_6bb74 : fetch_word Ubsan.M.loaded_segments (0x6bb74 : word) = Some W_6bb74.
Proof. vm_refl. Qed.
Lemma D_6bb74 : decode_any W_6bb74 = Some (Load SZ8 true 8 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb78 : bv 32 := 0x00a47c63.
Lemma F_6bb78 : fetch_word Ubsan.M.loaded_segments (0x6bb78 : word) = Some W_6bb78.
Proof. vm_refl. Qed.
Lemma D_6bb78 : decode_any W_6bb78 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb7c : bv 32 := 0xff853583.
Lemma F_6bb7c : fetch_word Ubsan.M.loaded_segments (0x6bb7c : word) = Some W_6bb7c.
Proof. vm_refl. Qed.
Lemma D_6bb7c : decode_any W_6bb7c = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb80 : bv 32 := 0xff850493.
Lemma F_6bb80 : fetch_word Ubsan.M.loaded_segments (0x6bb80 : word) = Some W_6bb80.
Proof. vm_refl. Qed.
Lemma D_6bb80 : decode_any W_6bb80 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb84 : bv 32 := 0x000580e7.
Lemma F_6bb84 : fetch_word Ubsan.M.loaded_segments (0x6bb84 : word) = Some W_6bb84.
Proof. vm_refl. Qed.
Lemma D_6bb84 : decode_any W_6bb84 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb88 : bv 32 := 0x00048513.
Lemma F_6bb88 : fetch_word Ubsan.M.loaded_segments (0x6bb88 : word) = Some W_6bb88.
Proof. vm_refl. Qed.
Lemma D_6bb88 : decode_any W_6bb88 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb8c : bv 32 := 0xfe9468e3.
Lemma F_6bb8c : fetch_word Ubsan.M.loaded_segments (0x6bb8c : word) = Some W_6bb8c.
Proof. vm_refl. Qed.
Lemma D_6bb8c : decode_any W_6bb8c = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb90 : bv 32 := 0x01813083.
Lemma F_6bb90 : fetch_word Ubsan.M.loaded_segments (0x6bb90 : word) = Some W_6bb90.
Proof. vm_refl. Qed.
Lemma D_6bb90 : decode_any W_6bb90 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb94 : bv 32 := 0x01013403.
Lemma F_6bb94 : fetch_word Ubsan.M.loaded_segments (0x6bb94 : word) = Some W_6bb94.
Proof. vm_refl. Qed.
Lemma D_6bb94 : decode_any W_6bb94 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb98 : bv 32 := 0x00813483.
Lemma F_6bb98 : fetch_word Ubsan.M.loaded_segments (0x6bb98 : word) = Some W_6bb98.
Proof. vm_refl. Qed.
Lemma D_6bb98 : decode_any W_6bb98 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb9c : bv 32 := 0x02010113.
Lemma F_6bb9c : fetch_word Ubsan.M.loaded_segments (0x6bb9c : word) = Some W_6bb9c.
Proof. vm_refl. Qed.
Lemma D_6bb9c : decode_any W_6bb9c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bba0 : bv 32 := 0xfb5ff06f.
Lemma F_6bba0 : fetch_word Ubsan.M.loaded_segments (0x6bba0 : word) = Some W_6bba0.
Proof. vm_refl. Qed.
Lemma D_6bba0 : decode_any W_6bba0 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bba4 : bv 32 := 0xff010113.
Lemma F_6bba4 : fetch_word Ubsan.M.loaded_segments (0x6bba4 : word) = Some W_6bba4.
Proof. vm_refl. Qed.
Lemma D_6bba4 : decode_any W_6bba4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bba8 : bv 32 := 0x00113423.
Lemma F_6bba8 : fetch_word Ubsan.M.loaded_segments (0x6bba8 : word) = Some W_6bba8.
Proof. vm_refl. Qed.
Lemma D_6bba8 : decode_any W_6bba8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbac : bv 32 := 0x00813023.
Lemma F_6bbac : fetch_word Ubsan.M.loaded_segments (0x6bbac : word) = Some W_6bbac.
Proof. vm_refl. Qed.
Lemma D_6bbac : decode_any W_6bbac = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbb0 : bv 32 := 0x00000593.
Lemma F_6bbb0 : fetch_word Ubsan.M.loaded_segments (0x6bbb0 : word) = Some W_6bbb0.
Proof. vm_refl. Qed.
Lemma D_6bbb0 : decode_any W_6bbb0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbb4 : bv 32 := 0x00020613.
Lemma F_6bbb4 : fetch_word Ubsan.M.loaded_segments (0x6bbb4 : word) = Some W_6bbb4.
Proof. vm_refl. Qed.
Lemma D_6bbb4 : decode_any W_6bbb4 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbb8 : bv 32 := 0xf5862603.
Lemma F_6bbb8 : fetch_word Ubsan.M.loaded_segments (0x6bbb8 : word) = Some W_6bbb8.
Proof. vm_refl. Qed.
Lemma D_6bbb8 : decode_any W_6bbb8 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbbc : bv 32 := 0x0004b697.
Lemma F_6bbbc : fetch_word Ubsan.M.loaded_segments (0x6bbbc : word) = Some W_6bbbc.
Proof. vm_refl. Qed.
Lemma D_6bbbc : decode_any W_6bbbc = Some (Auipc 13 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbc0 : bv 32 := 0x02468693.
Lemma F_6bbc0 : fetch_word Ubsan.M.loaded_segments (0x6bbc0 : word) = Some W_6bbc0.
Proof. vm_refl. Qed.
Lemma D_6bbc0 : decode_any W_6bbc0 = Some (OpImm ALU_ADD 13 13 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbc4 : bv 32 := 0x1606a72f.
Lemma F_6bbc4 : fetch_word Ubsan.M.loaded_segments (0x6bbc4 : word) = Some W_6bbc4.
Proof. vm_refl. Qed.
Lemma D_6bbc4 : decode_any W_6bbc4 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbc8 : bv 32 := 0x00b71663.
Lemma F_6bbc8 : fetch_word Ubsan.M.loaded_segments (0x6bbc8 : word) = Some W_6bbc8.
Proof. vm_refl. Qed.
Lemma D_6bbc8 : decode_any W_6bbc8 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbcc : bv 32 := 0x1ec6a7af.
Lemma F_6bbcc : fetch_word Ubsan.M.loaded_segments (0x6bbcc : word) = Some W_6bbcc.
Proof. vm_refl. Qed.
Lemma D_6bbcc : decode_any W_6bbcc = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbd0 : bv 32 := 0xfe079ae3.
Lemma F_6bbd0 : fetch_word Ubsan.M.loaded_segments (0x6bbd0 : word) = Some W_6bbd0.
Proof. vm_refl. Qed.
Lemma D_6bbd0 : decode_any W_6bbd0 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbd4 : bv 32 := 0x0007059b.
Lemma F_6bbd4 : fetch_word Ubsan.M.loaded_segments (0x6bbd4 : word) = Some W_6bbd4.
Proof. vm_refl. Qed.
Lemma D_6bbd4 : decode_any W_6bbd4 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbd8 : bv 32 := 0x02c58263.
Lemma F_6bbd8 : fetch_word Ubsan.M.loaded_segments (0x6bbd8 : word) = Some W_6bbd8.
Proof. vm_refl. Qed.
Lemma D_6bbd8 : decode_any W_6bbd8 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbdc : bv 32 := 0x02058263.
Lemma F_6bbdc : fetch_word Ubsan.M.loaded_segments (0x6bbdc : word) = Some W_6bbdc.
Proof. vm_refl. Qed.
Lemma D_6bbdc : decode_any W_6bbdc = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbe0 : bv 32 := 0x04900893.
Lemma F_6bbe0 : fetch_word Ubsan.M.loaded_segments (0x6bbe0 : word) = Some W_6bbe0.
Proof. vm_refl. Qed.
Lemma D_6bbe0 : decode_any W_6bbe0 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbe4 : bv 32 := 0x00000593.
Lemma F_6bbe4 : fetch_word Ubsan.M.loaded_segments (0x6bbe4 : word) = Some W_6bbe4.
Proof. vm_refl. Qed.
Lemma D_6bbe4 : decode_any W_6bbe4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbe8 : bv 32 := 0x00000613.
Lemma F_6bbe8 : fetch_word Ubsan.M.loaded_segments (0x6bbe8 : word) = Some W_6bbe8.
Proof. vm_refl. Qed.
Lemma D_6bbe8 : decode_any W_6bbe8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbec : bv 32 := 0x00000693.
Lemma F_6bbec : fetch_word Ubsan.M.loaded_segments (0x6bbec : word) = Some W_6bbec.
Proof. vm_refl. Qed.
Lemma D_6bbec : decode_any W_6bbec = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbf0 : bv 32 := 0x00000513.
Lemma F_6bbf0 : fetch_word Ubsan.M.loaded_segments (0x6bbf0 : word) = Some W_6bbf0.
Proof. vm_refl. Qed.
Lemma D_6bbf0 : decode_any W_6bbf0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbf4 : bv 32 := 0x00000073.
Lemma F_6bbf4 : fetch_word Ubsan.M.loaded_segments (0x6bbf4 : word) = Some W_6bbf4.
Proof. vm_refl. Qed.
Lemma D_6bbf4 : decode_any W_6bbf4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6bbf4 : is_ecall W_6bbf4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6bbf8 : bv 32 := 0xff9ff06f.
Lemma F_6bbf8 : fetch_word Ubsan.M.loaded_segments (0x6bbf8 : word) = Some W_6bbf8.
Proof. vm_refl. Qed.
Lemma D_6bbf8 : decode_any W_6bbf8 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bbfc : bv 32 := 0x00000023.
Lemma F_6bbfc : fetch_word Ubsan.M.loaded_segments (0x6bbfc : word) = Some W_6bbfc.
Proof. vm_refl. Qed.
Lemma D_6bbfc : decode_any W_6bbfc = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc00 : bv 32 := 0x00050413.
Lemma F_6bc00 : fetch_word Ubsan.M.loaded_segments (0x6bc00 : word) = Some W_6bc00.
Proof. vm_refl. Qed.
Lemma D_6bc00 : decode_any W_6bc00 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc04 : bv 32 := 0xdbdff0ef.
Lemma F_6bc04 : fetch_word Ubsan.M.loaded_segments (0x6bc04 : word) = Some W_6bc04.
Proof. vm_refl. Qed.
Lemma D_6bc04 : decode_any W_6bc04 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc08 : bv 32 := 0xf51ff0ef.
Lemma F_6bc08 : fetch_word Ubsan.M.loaded_segments (0x6bc08 : word) = Some W_6bc08.
Proof. vm_refl. Qed.
Lemma D_6bc08 : decode_any W_6bc08 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc0c : bv 32 := 0x288030ef.
Lemma F_6bc0c : fetch_word Ubsan.M.loaded_segments (0x6bc0c : word) = Some W_6bc0c.
Proof. vm_refl. Qed.
Lemma D_6bc0c : decode_any W_6bc0c = Some (Jal 1 12936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc10 : bv 32 := 0x00040513.
Lemma F_6bc10 : fetch_word Ubsan.M.loaded_segments (0x6bc10 : word) = Some W_6bc10.
Proof. vm_refl. Qed.
Lemma D_6bc10 : decode_any W_6bc10 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc14 : bv 32 := 0xd61ff0ef.
Lemma F_6bc14 : fetch_word Ubsan.M.loaded_segments (0x6bc14 : word) = Some W_6bc14.
Proof. vm_refl. Qed.
Lemma D_6bc14 : decode_any W_6bc14 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.
