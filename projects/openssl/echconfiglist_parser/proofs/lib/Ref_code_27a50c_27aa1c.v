(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_27a50c : bv 32 := 0xfe010113.
Lemma F_27a50c : fetch_word Plain.M.loaded_segments (0x27a548 : word) = Some W_27a50c.
Proof. vm_refl. Qed.
Lemma D_27a50c : decode_any W_27a50c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a510 : bv 32 := 0x00113c23.
Lemma F_27a510 : fetch_word Plain.M.loaded_segments (0x27a54c : word) = Some W_27a510.
Proof. vm_refl. Qed.
Lemma D_27a510 : decode_any W_27a510 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a514 : bv 32 := 0x00813823.
Lemma F_27a514 : fetch_word Plain.M.loaded_segments (0x27a550 : word) = Some W_27a514.
Proof. vm_refl. Qed.
Lemma D_27a514 : decode_any W_27a514 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a518 : bv 32 := 0x00913423.
Lemma F_27a518 : fetch_word Plain.M.loaded_segments (0x27a554 : word) = Some W_27a518.
Proof. vm_refl. Qed.
Lemma D_27a518 : decode_any W_27a518 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a51c : bv 32 := 0x00058413.
Lemma F_27a51c : fetch_word Plain.M.loaded_segments (0x27a558 : word) = Some W_27a51c.
Proof. vm_refl. Qed.
Lemma D_27a51c : decode_any W_27a51c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a520 : bv 32 := 0x00050493.
Lemma F_27a520 : fetch_word Plain.M.loaded_segments (0x27a55c : word) = Some W_27a520.
Proof. vm_refl. Qed.
Lemma D_27a520 : decode_any W_27a520 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a524 : bv 32 := 0x00000593.
Lemma F_27a524 : fetch_word Plain.M.loaded_segments (0x27a560 : word) = Some W_27a524.
Proof. vm_refl. Qed.
Lemma D_27a524 : decode_any W_27a524 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a528 : bv 32 := 0x00040613.
Lemma F_27a528 : fetch_word Plain.M.loaded_segments (0x27a564 : word) = Some W_27a528.
Proof. vm_refl. Qed.
Lemma D_27a528 : decode_any W_27a528 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a52c : bv 32 := 0xa58ff0ef.
Lemma F_27a52c : fetch_word Plain.M.loaded_segments (0x27a568 : word) = Some W_27a52c.
Proof. vm_refl. Qed.
Lemma D_27a52c : decode_any W_27a52c = Some (Jal 1 2093656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a530 : bv 32 := 0x00050463.
Lemma F_27a530 : fetch_word Plain.M.loaded_segments (0x27a56c : word) = Some W_27a530.
Proof. vm_refl. Qed.
Lemma D_27a530 : decode_any W_27a530 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a534 : bv 32 := 0x40950433.
Lemma F_27a534 : fetch_word Plain.M.loaded_segments (0x27a570 : word) = Some W_27a534.
Proof. vm_refl. Qed.
Lemma D_27a534 : decode_any W_27a534 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a538 : bv 32 := 0x00040513.
Lemma F_27a538 : fetch_word Plain.M.loaded_segments (0x27a574 : word) = Some W_27a538.
Proof. vm_refl. Qed.
Lemma D_27a538 : decode_any W_27a538 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a53c : bv 32 := 0x01813083.
Lemma F_27a53c : fetch_word Plain.M.loaded_segments (0x27a578 : word) = Some W_27a53c.
Proof. vm_refl. Qed.
Lemma D_27a53c : decode_any W_27a53c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a540 : bv 32 := 0x01013403.
Lemma F_27a540 : fetch_word Plain.M.loaded_segments (0x27a57c : word) = Some W_27a540.
Proof. vm_refl. Qed.
Lemma D_27a540 : decode_any W_27a540 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a544 : bv 32 := 0x00813483.
Lemma F_27a544 : fetch_word Plain.M.loaded_segments (0x27a580 : word) = Some W_27a544.
Proof. vm_refl. Qed.
Lemma D_27a544 : decode_any W_27a544 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a548 : bv 32 := 0x02010113.
Lemma F_27a548 : fetch_word Plain.M.loaded_segments (0x27a584 : word) = Some W_27a548.
Proof. vm_refl. Qed.
Lemma D_27a548 : decode_any W_27a548 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a54c : bv 32 := 0x00008067.
Lemma F_27a54c : fetch_word Plain.M.loaded_segments (0x27a588 : word) = Some W_27a54c.
Proof. vm_refl. Qed.
Lemma D_27a54c : decode_any W_27a54c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a550 : bv 32 := 0xfe010113.
Lemma F_27a550 : fetch_word Plain.M.loaded_segments (0x27a58c : word) = Some W_27a550.
Proof. vm_refl. Qed.
Lemma D_27a550 : decode_any W_27a550 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a554 : bv 32 := 0x00113c23.
Lemma F_27a554 : fetch_word Plain.M.loaded_segments (0x27a590 : word) = Some W_27a554.
Proof. vm_refl. Qed.
Lemma D_27a554 : decode_any W_27a554 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a558 : bv 32 := 0x00813823.
Lemma F_27a558 : fetch_word Plain.M.loaded_segments (0x27a594 : word) = Some W_27a558.
Proof. vm_refl. Qed.
Lemma D_27a558 : decode_any W_27a558 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a55c : bv 32 := 0x00913423.
Lemma F_27a55c : fetch_word Plain.M.loaded_segments (0x27a598 : word) = Some W_27a55c.
Proof. vm_refl. Qed.
Lemma D_27a55c : decode_any W_27a55c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a560 : bv 32 := 0x00058413.
Lemma F_27a560 : fetch_word Plain.M.loaded_segments (0x27a59c : word) = Some W_27a560.
Proof. vm_refl. Qed.
Lemma D_27a560 : decode_any W_27a560 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a564 : bv 32 := 0x00050493.
Lemma F_27a564 : fetch_word Plain.M.loaded_segments (0x27a5a0 : word) = Some W_27a564.
Proof. vm_refl. Qed.
Lemma D_27a564 : decode_any W_27a564 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a568 : bv 32 := 0xd7dff0ef.
Lemma F_27a568 : fetch_word Plain.M.loaded_segments (0x27a5a4 : word) = Some W_27a568.
Proof. vm_refl. Qed.
Lemma D_27a568 : decode_any W_27a568 = Some (Jal 1 2096508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a56c : bv 32 := 0x00150613.
Lemma F_27a56c : fetch_word Plain.M.loaded_segments (0x27a5a8 : word) = Some W_27a56c.
Proof. vm_refl. Qed.
Lemma D_27a56c : decode_any W_27a56c = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a570 : bv 32 := 0x00048513.
Lemma F_27a570 : fetch_word Plain.M.loaded_segments (0x27a5ac : word) = Some W_27a570.
Proof. vm_refl. Qed.
Lemma D_27a570 : decode_any W_27a570 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a574 : bv 32 := 0x00040593.
Lemma F_27a574 : fetch_word Plain.M.loaded_segments (0x27a5b0 : word) = Some W_27a574.
Proof. vm_refl. Qed.
Lemma D_27a574 : decode_any W_27a574 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a578 : bv 32 := 0x01813083.
Lemma F_27a578 : fetch_word Plain.M.loaded_segments (0x27a5b4 : word) = Some W_27a578.
Proof. vm_refl. Qed.
Lemma D_27a578 : decode_any W_27a578 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a57c : bv 32 := 0x01013403.
Lemma F_27a57c : fetch_word Plain.M.loaded_segments (0x27a5b8 : word) = Some W_27a57c.
Proof. vm_refl. Qed.
Lemma D_27a57c : decode_any W_27a57c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a580 : bv 32 := 0x00813483.
Lemma F_27a580 : fetch_word Plain.M.loaded_segments (0x27a5bc : word) = Some W_27a580.
Proof. vm_refl. Qed.
Lemma D_27a580 : decode_any W_27a580 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a584 : bv 32 := 0x02010113.
Lemma F_27a584 : fetch_word Plain.M.loaded_segments (0x27a5c0 : word) = Some W_27a584.
Proof. vm_refl. Qed.
Lemma D_27a584 : decode_any W_27a584 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a588 : bv 32 := 0x0040006f.
Lemma F_27a588 : fetch_word Plain.M.loaded_segments (0x27a5c4 : word) = Some W_27a588.
Proof. vm_refl. Qed.
Lemma D_27a588 : decode_any W_27a588 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a58c : bv 32 := 0x0ff5f593.
Lemma F_27a58c : fetch_word Plain.M.loaded_segments (0x27a5c8 : word) = Some W_27a58c.
Proof. vm_refl. Qed.
Lemma D_27a58c : decode_any W_27a58c = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a590 : bv 32 := 0x40c006b3.
Lemma F_27a590 : fetch_word Plain.M.loaded_segments (0x27a5cc : word) = Some W_27a590.
Proof. vm_refl. Qed.
Lemma D_27a590 : decode_any W_27a590 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a594 : bv 32 := 0x00c50633.
Lemma F_27a594 : fetch_word Plain.M.loaded_segments (0x27a5d0 : word) = Some W_27a594.
Proof. vm_refl. Qed.
Lemma D_27a594 : decode_any W_27a594 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a598 : bv 32 := 0x00068e63.
Lemma F_27a598 : fetch_word Plain.M.loaded_segments (0x27a5d4 : word) = Some W_27a598.
Proof. vm_refl. Qed.
Lemma D_27a598 : decode_any W_27a598 = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a59c : bv 32 := 0xfff64703.
Lemma F_27a59c : fetch_word Plain.M.loaded_segments (0x27a5d8 : word) = Some W_27a59c.
Proof. vm_refl. Qed.
Lemma D_27a59c : decode_any W_27a59c = Some (Load SZ1 false 14 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5a0 : bv 32 := 0xfff60513.
Lemma F_27a5a0 : fetch_word Plain.M.loaded_segments (0x27a5dc : word) = Some W_27a5a0.
Proof. vm_refl. Qed.
Lemma D_27a5a0 : decode_any W_27a5a0 = Some (OpImm ALU_ADD 10 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5a4 : bv 32 := 0x00168693.
Lemma F_27a5a4 : fetch_word Plain.M.loaded_segments (0x27a5e0 : word) = Some W_27a5a4.
Proof. vm_refl. Qed.
Lemma D_27a5a4 : decode_any W_27a5a4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5a8 : bv 32 := 0x00050613.
Lemma F_27a5a8 : fetch_word Plain.M.loaded_segments (0x27a5e4 : word) = Some W_27a5a8.
Proof. vm_refl. Qed.
Lemma D_27a5a8 : decode_any W_27a5a8 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5ac : bv 32 := 0xfeb716e3.
Lemma F_27a5ac : fetch_word Plain.M.loaded_segments (0x27a5e8 : word) = Some W_27a5ac.
Proof. vm_refl. Qed.
Lemma D_27a5ac : decode_any W_27a5ac = Some (Branch BC_NE 14 11 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5b0 : bv 32 := 0x00008067.
Lemma F_27a5b0 : fetch_word Plain.M.loaded_segments (0x27a5ec : word) = Some W_27a5b0.
Proof. vm_refl. Qed.
Lemma D_27a5b0 : decode_any W_27a5b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5b4 : bv 32 := 0x00000513.
Lemma F_27a5b4 : fetch_word Plain.M.loaded_segments (0x27a5f0 : word) = Some W_27a5b4.
Proof. vm_refl. Qed.
Lemma D_27a5b4 : decode_any W_27a5b4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5b8 : bv 32 := 0x00008067.
Lemma F_27a5b8 : fetch_word Plain.M.loaded_segments (0x27a5f4 : word) = Some W_27a5b8.
Proof. vm_refl. Qed.
Lemma D_27a5b8 : decode_any W_27a5b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5bc : bv 32 := 0xfd010113.
Lemma F_27a5bc : fetch_word Plain.M.loaded_segments (0x27a5f8 : word) = Some W_27a5bc.
Proof. vm_refl. Qed.
Lemma D_27a5bc : decode_any W_27a5bc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5c0 : bv 32 := 0x02113423.
Lemma F_27a5c0 : fetch_word Plain.M.loaded_segments (0x27a5fc : word) = Some W_27a5c0.
Proof. vm_refl. Qed.
Lemma D_27a5c0 : decode_any W_27a5c0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5c4 : bv 32 := 0x00061617.
Lemma F_27a5c4 : fetch_word Plain.M.loaded_segments (0x27a600 : word) = Some W_27a5c4.
Proof. vm_refl. Qed.
Lemma D_27a5c4 : decode_any W_27a5c4 = Some (Auipc 12 97, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5c8 : bv 32 := 0xb2063603.
Lemma F_27a5c8 : fetch_word Plain.M.loaded_segments (0x27a604 : word) = Some W_27a5c8.
Proof. vm_refl. Qed.
Lemma D_27a5c8 : decode_any W_27a5c8 = Some (Load SZ8 true 12 12 2848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5cc : bv 32 := 0x00063683.
Lemma F_27a5cc : fetch_word Plain.M.loaded_segments (0x27a608 : word) = Some W_27a5cc.
Proof. vm_refl. Qed.
Lemma D_27a5cc : decode_any W_27a5cc = Some (Load SZ8 true 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5d0 : bv 32 := 0x02d13023.
Lemma F_27a5d0 : fetch_word Plain.M.loaded_segments (0x27a60c : word) = Some W_27a5d0.
Proof. vm_refl. Qed.
Lemma D_27a5d0 : decode_any W_27a5d0 = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5d4 : bv 32 := 0x0005c683.
Lemma F_27a5d4 : fetch_word Plain.M.loaded_segments (0x27a610 : word) = Some W_27a5d4.
Proof. vm_refl. Qed.
Lemma D_27a5d4 : decode_any W_27a5d4 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5d8 : bv 32 := 0x00013023.
Lemma F_27a5d8 : fetch_word Plain.M.loaded_segments (0x27a614 : word) = Some W_27a5d8.
Proof. vm_refl. Qed.
Lemma D_27a5d8 : decode_any W_27a5d8 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5dc : bv 32 := 0x00013423.
Lemma F_27a5dc : fetch_word Plain.M.loaded_segments (0x27a618 : word) = Some W_27a5dc.
Proof. vm_refl. Qed.
Lemma D_27a5dc : decode_any W_27a5dc = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5e0 : bv 32 := 0x00013823.
Lemma F_27a5e0 : fetch_word Plain.M.loaded_segments (0x27a61c : word) = Some W_27a5e0.
Proof. vm_refl. Qed.
Lemma D_27a5e0 : decode_any W_27a5e0 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5e4 : bv 32 := 0x00013c23.
Lemma F_27a5e4 : fetch_word Plain.M.loaded_segments (0x27a620 : word) = Some W_27a5e4.
Proof. vm_refl. Qed.
Lemma D_27a5e4 : decode_any W_27a5e4 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5e8 : bv 32 := 0x08068263.
Lemma F_27a5e8 : fetch_word Plain.M.loaded_segments (0x27a624 : word) = Some W_27a5e8.
Proof. vm_refl. Qed.
Lemma D_27a5e8 : decode_any W_27a5e8 = Some (Branch BC_EQ 13 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5ec : bv 32 := 0x0015c703.
Lemma F_27a5ec : fetch_word Plain.M.loaded_segments (0x27a628 : word) = Some W_27a5ec.
Proof. vm_refl. Qed.
Lemma D_27a5ec : decode_any W_27a5ec = Some (Load SZ1 false 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5f0 : bv 32 := 0x08070263.
Lemma F_27a5f0 : fetch_word Plain.M.loaded_segments (0x27a62c : word) = Some W_27a5f0.
Proof. vm_refl. Qed.
Lemma D_27a5f0 : decode_any W_27a5f0 = Some (Branch BC_EQ 14 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5f4 : bv 32 := 0x00158593.
Lemma F_27a5f4 : fetch_word Plain.M.loaded_segments (0x27a630 : word) = Some W_27a5f4.
Proof. vm_refl. Qed.
Lemma D_27a5f4 : decode_any W_27a5f4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5f8 : bv 32 := 0x00100713.
Lemma F_27a5f8 : fetch_word Plain.M.loaded_segments (0x27a634 : word) = Some W_27a5f8.
Proof. vm_refl. Qed.
Lemma D_27a5f8 : decode_any W_27a5f8 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a5fc : bv 32 := 0x00010793.
Lemma F_27a5fc : fetch_word Plain.M.loaded_segments (0x27a638 : word) = Some W_27a5fc.
Proof. vm_refl. Qed.
Lemma D_27a5fc : decode_any W_27a5fc = Some (OpImm ALU_ADD 15 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a600 : bv 32 := 0x0036d813.
Lemma F_27a600 : fetch_word Plain.M.loaded_segments (0x27a63c : word) = Some W_27a600.
Proof. vm_refl. Qed.
Lemma D_27a600 : decode_any W_27a600 = Some (ShiftImm ALU_SRL 16 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a604 : bv 32 := 0xff887813.
Lemma F_27a604 : fetch_word Plain.M.loaded_segments (0x27a640 : word) = Some W_27a604.
Proof. vm_refl. Qed.
Lemma D_27a604 : decode_any W_27a604 = Some (OpImm ALU_AND 16 16 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a608 : bv 32 := 0x01078833.
Lemma F_27a608 : fetch_word Plain.M.loaded_segments (0x27a644 : word) = Some W_27a608.
Proof. vm_refl. Qed.
Lemma D_27a608 : decode_any W_27a608 = Some (Op ALU_ADD 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a60c : bv 32 := 0x00083883.
Lemma F_27a60c : fetch_word Plain.M.loaded_segments (0x27a648 : word) = Some W_27a60c.
Proof. vm_refl. Qed.
Lemma D_27a60c : decode_any W_27a60c = Some (Load SZ8 true 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a610 : bv 32 := 0x00d712b3.
Lemma F_27a610 : fetch_word Plain.M.loaded_segments (0x27a64c : word) = Some W_27a610.
Proof. vm_refl. Qed.
Lemma D_27a610 : decode_any W_27a610 = Some (Op ALU_SLL 5 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a614 : bv 32 := 0x0005c683.
Lemma F_27a614 : fetch_word Plain.M.loaded_segments (0x27a650 : word) = Some W_27a614.
Proof. vm_refl. Qed.
Lemma D_27a614 : decode_any W_27a614 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a618 : bv 32 := 0x0058e8b3.
Lemma F_27a618 : fetch_word Plain.M.loaded_segments (0x27a654 : word) = Some W_27a618.
Proof. vm_refl. Qed.
Lemma D_27a618 : decode_any W_27a618 = Some (Op ALU_OR 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a61c : bv 32 := 0x01183023.
Lemma F_27a61c : fetch_word Plain.M.loaded_segments (0x27a658 : word) = Some W_27a61c.
Proof. vm_refl. Qed.
Lemma D_27a61c : decode_any W_27a61c = Some (Store SZ8 16 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a620 : bv 32 := 0x00158593.
Lemma F_27a620 : fetch_word Plain.M.loaded_segments (0x27a65c : word) = Some W_27a620.
Proof. vm_refl. Qed.
Lemma D_27a620 : decode_any W_27a620 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a624 : bv 32 := 0xfc069ee3.
Lemma F_27a624 : fetch_word Plain.M.loaded_segments (0x27a660 : word) = Some W_27a624.
Proof. vm_refl. Qed.
Lemma D_27a624 : decode_any W_27a624 = Some (Branch BC_NE 13 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a628 : bv 32 := 0x00054683.
Lemma F_27a628 : fetch_word Plain.M.loaded_segments (0x27a664 : word) = Some W_27a628.
Proof. vm_refl. Qed.
Lemma D_27a628 : decode_any W_27a628 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a62c : bv 32 := 0x00050793.
Lemma F_27a62c : fetch_word Plain.M.loaded_segments (0x27a668 : word) = Some W_27a62c.
Proof. vm_refl. Qed.
Lemma D_27a62c : decode_any W_27a62c = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a630 : bv 32 := 0x06068263.
Lemma F_27a630 : fetch_word Plain.M.loaded_segments (0x27a66c : word) = Some W_27a630.
Proof. vm_refl. Qed.
Lemma D_27a630 : decode_any W_27a630 = Some (Branch BC_EQ 13 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a634 : bv 32 := 0x00010593.
Lemma F_27a634 : fetch_word Plain.M.loaded_segments (0x27a670 : word) = Some W_27a634.
Proof. vm_refl. Qed.
Lemma D_27a634 : decode_any W_27a634 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a638 : bv 32 := 0x00050713.
Lemma F_27a638 : fetch_word Plain.M.loaded_segments (0x27a674 : word) = Some W_27a638.
Proof. vm_refl. Qed.
Lemma D_27a638 : decode_any W_27a638 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a63c : bv 32 := 0x0036d793.
Lemma F_27a63c : fetch_word Plain.M.loaded_segments (0x27a678 : word) = Some W_27a63c.
Proof. vm_refl. Qed.
Lemma D_27a63c : decode_any W_27a63c = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a640 : bv 32 := 0xff87f793.
Lemma F_27a640 : fetch_word Plain.M.loaded_segments (0x27a67c : word) = Some W_27a640.
Proof. vm_refl. Qed.
Lemma D_27a640 : decode_any W_27a640 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a644 : bv 32 := 0x00f587b3.
Lemma F_27a644 : fetch_word Plain.M.loaded_segments (0x27a680 : word) = Some W_27a644.
Proof. vm_refl. Qed.
Lemma D_27a644 : decode_any W_27a644 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a648 : bv 32 := 0x0007b783.
Lemma F_27a648 : fetch_word Plain.M.loaded_segments (0x27a684 : word) = Some W_27a648.
Proof. vm_refl. Qed.
Lemma D_27a648 : decode_any W_27a648 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a64c : bv 32 := 0x00d7d6b3.
Lemma F_27a64c : fetch_word Plain.M.loaded_segments (0x27a688 : word) = Some W_27a64c.
Proof. vm_refl. Qed.
Lemma D_27a64c : decode_any W_27a64c = Some (Op ALU_SRL 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a650 : bv 32 := 0x0016f693.
Lemma F_27a650 : fetch_word Plain.M.loaded_segments (0x27a68c : word) = Some W_27a650.
Proof. vm_refl. Qed.
Lemma D_27a650 : decode_any W_27a650 = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a654 : bv 32 := 0x02068e63.
Lemma F_27a654 : fetch_word Plain.M.loaded_segments (0x27a690 : word) = Some W_27a654.
Proof. vm_refl. Qed.
Lemma D_27a654 : decode_any W_27a654 = Some (Branch BC_EQ 13 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a658 : bv 32 := 0x00174683.
Lemma F_27a658 : fetch_word Plain.M.loaded_segments (0x27a694 : word) = Some W_27a658.
Proof. vm_refl. Qed.
Lemma D_27a658 : decode_any W_27a658 = Some (Load SZ1 false 13 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a65c : bv 32 := 0x00170793.
Lemma F_27a65c : fetch_word Plain.M.loaded_segments (0x27a698 : word) = Some W_27a65c.
Proof. vm_refl. Qed.
Lemma D_27a65c : decode_any W_27a65c = Some (OpImm ALU_ADD 15 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a660 : bv 32 := 0x00078713.
Lemma F_27a660 : fetch_word Plain.M.loaded_segments (0x27a69c : word) = Some W_27a660.
Proof. vm_refl. Qed.
Lemma D_27a660 : decode_any W_27a660 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a664 : bv 32 := 0xfc069ce3.
Lemma F_27a664 : fetch_word Plain.M.loaded_segments (0x27a6a0 : word) = Some W_27a664.
Proof. vm_refl. Qed.
Lemma D_27a664 : decode_any W_27a664 = Some (Branch BC_NE 13 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a668 : bv 32 := 0x02c0006f.
Lemma F_27a668 : fetch_word Plain.M.loaded_segments (0x27a6a4 : word) = Some W_27a668.
Proof. vm_refl. Qed.
Lemma D_27a668 : decode_any W_27a668 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a66c : bv 32 := 0x00000513.
Lemma F_27a66c : fetch_word Plain.M.loaded_segments (0x27a6a8 : word) = Some W_27a66c.
Proof. vm_refl. Qed.
Lemma D_27a66c : decode_any W_27a66c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a670 : bv 32 := 0x0280006f.
Lemma F_27a670 : fetch_word Plain.M.loaded_segments (0x27a6ac : word) = Some W_27a670.
Proof. vm_refl. Qed.
Lemma D_27a670 : decode_any W_27a670 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a674 : bv 32 := 0x00000593.
Lemma F_27a674 : fetch_word Plain.M.loaded_segments (0x27a6b0 : word) = Some W_27a674.
Proof. vm_refl. Qed.
Lemma D_27a674 : decode_any W_27a674 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a678 : bv 32 := 0x00b50733.
Lemma F_27a678 : fetch_word Plain.M.loaded_segments (0x27a6b4 : word) = Some W_27a678.
Proof. vm_refl. Qed.
Lemma D_27a678 : decode_any W_27a678 = Some (Op ALU_ADD 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a67c : bv 32 := 0x00074703.
Lemma F_27a67c : fetch_word Plain.M.loaded_segments (0x27a6b8 : word) = Some W_27a67c.
Proof. vm_refl. Qed.
Lemma D_27a67c : decode_any W_27a67c = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a680 : bv 32 := 0x00158593.
Lemma F_27a680 : fetch_word Plain.M.loaded_segments (0x27a6bc : word) = Some W_27a680.
Proof. vm_refl. Qed.
Lemma D_27a680 : decode_any W_27a680 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a684 : bv 32 := 0xfed70ae3.
Lemma F_27a684 : fetch_word Plain.M.loaded_segments (0x27a6c0 : word) = Some W_27a684.
Proof. vm_refl. Qed.
Lemma D_27a684 : decode_any W_27a684 = Some (Branch BC_EQ 14 13 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a688 : bv 32 := 0xfff58513.
Lemma F_27a688 : fetch_word Plain.M.loaded_segments (0x27a6c4 : word) = Some W_27a688.
Proof. vm_refl. Qed.
Lemma D_27a688 : decode_any W_27a688 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a68c : bv 32 := 0x00c0006f.
Lemma F_27a68c : fetch_word Plain.M.loaded_segments (0x27a6c8 : word) = Some W_27a68c.
Proof. vm_refl. Qed.
Lemma D_27a68c : decode_any W_27a68c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a690 : bv 32 := 0x00070793.
Lemma F_27a690 : fetch_word Plain.M.loaded_segments (0x27a6cc : word) = Some W_27a690.
Proof. vm_refl. Qed.
Lemma D_27a690 : decode_any W_27a690 = Some (OpImm ALU_ADD 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a694 : bv 32 := 0x40a78533.
Lemma F_27a694 : fetch_word Plain.M.loaded_segments (0x27a6d0 : word) = Some W_27a694.
Proof. vm_refl. Qed.
Lemma D_27a694 : decode_any W_27a694 = Some (Op ALU_SUB 10 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a698 : bv 32 := 0x00063583.
Lemma F_27a698 : fetch_word Plain.M.loaded_segments (0x27a6d4 : word) = Some W_27a698.
Proof. vm_refl. Qed.
Lemma D_27a698 : decode_any W_27a698 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a69c : bv 32 := 0x02013603.
Lemma F_27a69c : fetch_word Plain.M.loaded_segments (0x27a6d8 : word) = Some W_27a69c.
Proof. vm_refl. Qed.
Lemma D_27a69c : decode_any W_27a69c = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6a0 : bv 32 := 0x00c59863.
Lemma F_27a6a0 : fetch_word Plain.M.loaded_segments (0x27a6dc : word) = Some W_27a6a0.
Proof. vm_refl. Qed.
Lemma D_27a6a0 : decode_any W_27a6a0 = Some (Branch BC_NE 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6a4 : bv 32 := 0x02813083.
Lemma F_27a6a4 : fetch_word Plain.M.loaded_segments (0x27a6e0 : word) = Some W_27a6a4.
Proof. vm_refl. Qed.
Lemma D_27a6a4 : decode_any W_27a6a4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6a8 : bv 32 := 0x03010113.
Lemma F_27a6a8 : fetch_word Plain.M.loaded_segments (0x27a6e4 : word) = Some W_27a6a8.
Proof. vm_refl. Qed.
Lemma D_27a6a8 : decode_any W_27a6a8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6ac : bv 32 := 0x00008067.
Lemma F_27a6ac : fetch_word Plain.M.loaded_segments (0x27a6e8 : word) = Some W_27a6ac.
Proof. vm_refl. Qed.
Lemma D_27a6ac : decode_any W_27a6ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6b0 : bv 32 := 0xef0f40ef.
Lemma F_27a6b0 : fetch_word Plain.M.loaded_segments (0x27a6ec : word) = Some W_27a6b0.
Proof. vm_refl. Qed.
Lemma D_27a6b0 : decode_any W_27a6b0 = Some (Jal 1 2049776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6b4 : bv 32 := 0xff010113.
Lemma F_27a6b4 : fetch_word Plain.M.loaded_segments (0x27a6f0 : word) = Some W_27a6b4.
Proof. vm_refl. Qed.
Lemma D_27a6b4 : decode_any W_27a6b4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6b8 : bv 32 := 0x00113423.
Lemma F_27a6b8 : fetch_word Plain.M.loaded_segments (0x27a6f4 : word) = Some W_27a6b8.
Proof. vm_refl. Qed.
Lemma D_27a6b8 : decode_any W_27a6b8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6bc : bv 32 := 0x00058613.
Lemma F_27a6bc : fetch_word Plain.M.loaded_segments (0x27a6f8 : word) = Some W_27a6bc.
Proof. vm_refl. Qed.
Lemma D_27a6bc : decode_any W_27a6bc = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6c0 : bv 32 := 0x000055b7.
Lemma F_27a6c0 : fetch_word Plain.M.loaded_segments (0x27a6fc : word) = Some W_27a6c0.
Proof. vm_refl. Qed.
Lemma D_27a6c0 : decode_any W_27a6c0 = Some (Lui 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6c4 : bv 32 := 0x4015859b.
Lemma F_27a6c4 : fetch_word Plain.M.loaded_segments (0x27a700 : word) = Some W_27a6c4.
Proof. vm_refl. Qed.
Lemma D_27a6c4 : decode_any W_27a6c4 = Some (OpImm32 11 11 1025, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6c8 : bv 32 := 0xdd9f60ef.
Lemma F_27a6c8 : fetch_word Plain.M.loaded_segments (0x27a704 : word) = Some W_27a6c8.
Proof. vm_refl. Qed.
Lemma D_27a6c8 : decode_any W_27a6c8 = Some (Jal 1 2059736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6cc : bv 32 := 0x00153513.
Lemma F_27a6cc : fetch_word Plain.M.loaded_segments (0x27a708 : word) = Some W_27a6cc.
Proof. vm_refl. Qed.
Lemma D_27a6cc : decode_any W_27a6cc = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6d0 : bv 32 := 0xfff50513.
Lemma F_27a6d0 : fetch_word Plain.M.loaded_segments (0x27a70c : word) = Some W_27a6d0.
Proof. vm_refl. Qed.
Lemma D_27a6d0 : decode_any W_27a6d0 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6d4 : bv 32 := 0x00813083.
Lemma F_27a6d4 : fetch_word Plain.M.loaded_segments (0x27a710 : word) = Some W_27a6d4.
Proof. vm_refl. Qed.
Lemma D_27a6d4 : decode_any W_27a6d4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6d8 : bv 32 := 0x01010113.
Lemma F_27a6d8 : fetch_word Plain.M.loaded_segments (0x27a714 : word) = Some W_27a6d8.
Proof. vm_refl. Qed.
Lemma D_27a6d8 : decode_any W_27a6d8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6dc : bv 32 := 0x00008067.
Lemma F_27a6dc : fetch_word Plain.M.loaded_segments (0x27a718 : word) = Some W_27a6dc.
Proof. vm_refl. Qed.
Lemma D_27a6dc : decode_any W_27a6dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6e0 : bv 32 := 0x00300693.
Lemma F_27a6e0 : fetch_word Plain.M.loaded_segments (0x27a71c : word) = Some W_27a6e0.
Proof. vm_refl. Qed.
Lemma D_27a6e0 : decode_any W_27a6e0 = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6e4 : bv 32 := 0x02d5e663.
Lemma F_27a6e4 : fetch_word Plain.M.loaded_segments (0x27a720 : word) = Some W_27a6e4.
Proof. vm_refl. Qed.
Lemma D_27a6e4 : decode_any W_27a6e4 = Some (Branch BC_LTU 11 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6e8 : bv 32 := 0xff010113.
Lemma F_27a6e8 : fetch_word Plain.M.loaded_segments (0x27a724 : word) = Some W_27a6e8.
Proof. vm_refl. Qed.
Lemma D_27a6e8 : decode_any W_27a6e8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6ec : bv 32 := 0x00113423.
Lemma F_27a6ec : fetch_word Plain.M.loaded_segments (0x27a728 : word) = Some W_27a6ec.
Proof. vm_refl. Qed.
Lemma D_27a6ec : decode_any W_27a6ec = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6f0 : bv 32 := 0xeb8f40ef.
Lemma F_27a6f0 : fetch_word Plain.M.loaded_segments (0x27a72c : word) = Some W_27a6f0.
Proof. vm_refl. Qed.
Lemma D_27a6f0 : decode_any W_27a6f0 = Some (Jal 1 2049720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6f4 : bv 32 := 0x00050593.
Lemma F_27a6f4 : fetch_word Plain.M.loaded_segments (0x27a730 : word) = Some W_27a6f4.
Proof. vm_refl. Qed.
Lemma D_27a6f4 : decode_any W_27a6f4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6f8 : bv 32 := 0x01600613.
Lemma F_27a6f8 : fetch_word Plain.M.loaded_segments (0x27a734 : word) = Some W_27a6f8.
Proof. vm_refl. Qed.
Lemma D_27a6f8 : decode_any W_27a6f8 = Some (OpImm ALU_ADD 12 0 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a6fc : bv 32 := 0xfff00513.
Lemma F_27a6fc : fetch_word Plain.M.loaded_segments (0x27a738 : word) = Some W_27a6fc.
Proof. vm_refl. Qed.
Lemma D_27a6fc : decode_any W_27a6fc = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a700 : bv 32 := 0x00c5a023.
Lemma F_27a700 : fetch_word Plain.M.loaded_segments (0x27a73c : word) = Some W_27a700.
Proof. vm_refl. Qed.
Lemma D_27a700 : decode_any W_27a700 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a704 : bv 32 := 0x00813083.
Lemma F_27a704 : fetch_word Plain.M.loaded_segments (0x27a740 : word) = Some W_27a704.
Proof. vm_refl. Qed.
Lemma D_27a704 : decode_any W_27a704 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a708 : bv 32 := 0x01010113.
Lemma F_27a708 : fetch_word Plain.M.loaded_segments (0x27a744 : word) = Some W_27a708.
Proof. vm_refl. Qed.
Lemma D_27a708 : decode_any W_27a708 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a70c : bv 32 := 0x00008067.
Lemma F_27a70c : fetch_word Plain.M.loaded_segments (0x27a748 : word) = Some W_27a70c.
Proof. vm_refl. Qed.
Lemma D_27a70c : decode_any W_27a70c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a710 : bv 32 := 0x000056b7.
Lemma F_27a710 : fetch_word Plain.M.loaded_segments (0x27a74c : word) = Some W_27a710.
Proof. vm_refl. Qed.
Lemma D_27a710 : decode_any W_27a710 = Some (Lui 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a714 : bv 32 := 0x40268693.
Lemma F_27a714 : fetch_word Plain.M.loaded_segments (0x27a750 : word) = Some W_27a714.
Proof. vm_refl. Qed.
Lemma D_27a714 : decode_any W_27a714 = Some (OpImm ALU_ADD 13 13 1026, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a718 : bv 32 := 0x00d585bb.
Lemma F_27a718 : fetch_word Plain.M.loaded_segments (0x27a754 : word) = Some W_27a718.
Proof. vm_refl. Qed.
Lemma D_27a718 : decode_any W_27a718 = Some (Op32 ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a71c : bv 32 := 0xd85f606f.
Lemma F_27a71c : fetch_word Plain.M.loaded_segments (0x27a758 : word) = Some W_27a71c.
Proof. vm_refl. Qed.
Lemma D_27a71c : decode_any W_27a71c = Some (Jal 0 2059652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a720 : bv 32 := 0x00095597.
Lemma F_27a720 : fetch_word Plain.M.loaded_segments (0x27a75c : word) = Some W_27a720.
Proof. vm_refl. Qed.
Lemma D_27a720 : decode_any W_27a720 = Some (Auipc 11 149, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a724 : bv 32 := 0xfaf58683.
Lemma F_27a724 : fetch_word Plain.M.loaded_segments (0x27a760 : word) = Some W_27a724.
Proof. vm_refl. Qed.
Lemma D_27a724 : decode_any W_27a724 = Some (Load SZ1 true 13 11 4015, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a728 : bv 32 := 0x1e068863.
Lemma F_27a728 : fetch_word Plain.M.loaded_segments (0x27a764 : word) = Some W_27a728.
Proof. vm_refl. Qed.
Lemma D_27a728 : decode_any W_27a728 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a72c : bv 32 := 0x00000613.
Lemma F_27a72c : fetch_word Plain.M.loaded_segments (0x27a768 : word) = Some W_27a72c.
Proof. vm_refl. Qed.
Lemma D_27a72c : decode_any W_27a72c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a730 : bv 32 := 0x80000737.
Lemma F_27a730 : fetch_word Plain.M.loaded_segments (0x27a76c : word) = Some W_27a730.
Proof. vm_refl. Qed.
Lemma D_27a730 : decode_any W_27a730 = Some (Lui 14 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a734 : bv 32 := 0x0017071b.
Lemma F_27a734 : fetch_word Plain.M.loaded_segments (0x27a770 : word) = Some W_27a734.
Proof. vm_refl. Qed.
Lemma D_27a734 : decode_any W_27a734 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a738 : bv 32 := 0x160527af.
Lemma F_27a738 : fetch_word Plain.M.loaded_segments (0x27a774 : word) = Some W_27a738.
Proof. vm_refl. Qed.
Lemma D_27a738 : decode_any W_27a738 = Some (Lr AW true true 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a73c : bv 32 := 0x00c79663.
Lemma F_27a73c : fetch_word Plain.M.loaded_segments (0x27a778 : word) = Some W_27a73c.
Proof. vm_refl. Qed.
Lemma D_27a73c : decode_any W_27a73c = Some (Branch BC_NE 15 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a740 : bv 32 := 0x1ee5282f.
Lemma F_27a740 : fetch_word Plain.M.loaded_segments (0x27a77c : word) = Some W_27a740.
Proof. vm_refl. Qed.
Lemma D_27a740 : decode_any W_27a740 = Some (Sc AW true true 16 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a744 : bv 32 := 0xfe081ae3.
Lemma F_27a744 : fetch_word Plain.M.loaded_segments (0x27a780 : word) = Some W_27a744.
Proof. vm_refl. Qed.
Lemma D_27a744 : decode_any W_27a744 = Some (Branch BC_NE 16 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a748 : bv 32 := 0x0007861b.
Lemma F_27a748 : fetch_word Plain.M.loaded_segments (0x27a784 : word) = Some W_27a748.
Proof. vm_refl. Qed.
Lemma D_27a748 : decode_any W_27a748 = Some (OpImm32 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a74c : bv 32 := 0x0006d463.
Lemma F_27a74c : fetch_word Plain.M.loaded_segments (0x27a788 : word) = Some W_27a74c.
Proof. vm_refl. Qed.
Lemma D_27a74c : decode_any W_27a74c = Some (Branch BC_GE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a750 : bv 32 := 0xfa0587a3.
Lemma F_27a750 : fetch_word Plain.M.loaded_segments (0x27a78c : word) = Some W_27a750.
Proof. vm_refl. Qed.
Lemma D_27a750 : decode_any W_27a750 = Some (Store SZ1 11 0 4015, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a754 : bv 32 := 0x1c060263.
Lemma F_27a754 : fetch_word Plain.M.loaded_segments (0x27a790 : word) = Some W_27a754.
Proof. vm_refl. Qed.
Lemma D_27a754 : decode_any W_27a754 = Some (Branch BC_EQ 12 0 452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a758 : bv 32 := 0x800007b7.
Lemma F_27a758 : fetch_word Plain.M.loaded_segments (0x27a794 : word) = Some W_27a758.
Proof. vm_refl. Qed.
Lemma D_27a758 : decode_any W_27a758 = Some (Lui 15 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a75c : bv 32 := 0x00261593.
Lemma F_27a75c : fetch_word Plain.M.loaded_segments (0x27a798 : word) = Some W_27a75c.
Proof. vm_refl. Qed.
Lemma D_27a75c : decode_any W_27a75c = Some (ShiftImm ALU_SLL 11 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a760 : bv 32 := 0xfff78793.
Lemma F_27a760 : fetch_word Plain.M.loaded_segments (0x27a79c : word) = Some W_27a760.
Proof. vm_refl. Qed.
Lemma D_27a760 : decode_any W_27a760 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a764 : bv 32 := 0x0215d593.
Lemma F_27a764 : fetch_word Plain.M.loaded_segments (0x27a7a0 : word) = Some W_27a764.
Proof. vm_refl. Qed.
Lemma D_27a764 : decode_any W_27a764 = Some (ShiftImm ALU_SRL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a768 : bv 32 := 0x00b6063b.
Lemma F_27a768 : fetch_word Plain.M.loaded_segments (0x27a7a4 : word) = Some W_27a768.
Proof. vm_refl. Qed.
Lemma D_27a768 : decode_any W_27a768 = Some (Op32 ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a76c : bv 32 := 0x00f605b3.
Lemma F_27a76c : fetch_word Plain.M.loaded_segments (0x27a7a8 : word) = Some W_27a76c.
Proof. vm_refl. Qed.
Lemma D_27a76c : decode_any W_27a76c = Some (Op ALU_ADD 11 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a770 : bv 32 := 0x0025859b.
Lemma F_27a770 : fetch_word Plain.M.loaded_segments (0x27a7ac : word) = Some W_27a770.
Proof. vm_refl. Qed.
Lemma D_27a770 : decode_any W_27a770 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a774 : bv 32 := 0x160526af.
Lemma F_27a774 : fetch_word Plain.M.loaded_segments (0x27a7b0 : word) = Some W_27a774.
Proof. vm_refl. Qed.
Lemma D_27a774 : decode_any W_27a774 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a778 : bv 32 := 0x00c69663.
Lemma F_27a778 : fetch_word Plain.M.loaded_segments (0x27a7b4 : word) = Some W_27a778.
Proof. vm_refl. Qed.
Lemma D_27a778 : decode_any W_27a778 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a77c : bv 32 := 0x1eb5272f.
Lemma F_27a77c : fetch_word Plain.M.loaded_segments (0x27a7b8 : word) = Some W_27a77c.
Proof. vm_refl. Qed.
Lemma D_27a77c : decode_any W_27a77c = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a780 : bv 32 := 0xfe071ae3.
Lemma F_27a780 : fetch_word Plain.M.loaded_segments (0x27a7bc : word) = Some W_27a780.
Proof. vm_refl. Qed.
Lemma D_27a780 : decode_any W_27a780 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a784 : bv 32 := 0x0006859b.
Lemma F_27a784 : fetch_word Plain.M.loaded_segments (0x27a7c0 : word) = Some W_27a784.
Proof. vm_refl. Qed.
Lemma D_27a784 : decode_any W_27a784 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a788 : bv 32 := 0x18c58863.
Lemma F_27a788 : fetch_word Plain.M.loaded_segments (0x27a7c4 : word) = Some W_27a788.
Proof. vm_refl. Qed.
Lemma D_27a788 : decode_any W_27a788 = Some (Branch BC_EQ 11 12 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a78c : bv 32 := 0x01f5d613.
Lemma F_27a78c : fetch_word Plain.M.loaded_segments (0x27a7c8 : word) = Some W_27a78c.
Proof. vm_refl. Qed.
Lemma D_27a78c : decode_any W_27a78c = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a790 : bv 32 := 0x00f67633.
Lemma F_27a790 : fetch_word Plain.M.loaded_segments (0x27a7cc : word) = Some W_27a790.
Proof. vm_refl. Qed.
Lemma D_27a790 : decode_any W_27a790 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a794 : bv 32 := 0x00c5863b.
Lemma F_27a794 : fetch_word Plain.M.loaded_segments (0x27a7d0 : word) = Some W_27a794.
Proof. vm_refl. Qed.
Lemma D_27a794 : decode_any W_27a794 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a798 : bv 32 := 0x00c785b3.
Lemma F_27a798 : fetch_word Plain.M.loaded_segments (0x27a7d4 : word) = Some W_27a798.
Proof. vm_refl. Qed.
Lemma D_27a798 : decode_any W_27a798 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a79c : bv 32 := 0x0025859b.
Lemma F_27a79c : fetch_word Plain.M.loaded_segments (0x27a7d8 : word) = Some W_27a79c.
Proof. vm_refl. Qed.
Lemma D_27a79c : decode_any W_27a79c = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7a0 : bv 32 := 0x160526af.
Lemma F_27a7a0 : fetch_word Plain.M.loaded_segments (0x27a7dc : word) = Some W_27a7a0.
Proof. vm_refl. Qed.
Lemma D_27a7a0 : decode_any W_27a7a0 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7a4 : bv 32 := 0x00c69663.
Lemma F_27a7a4 : fetch_word Plain.M.loaded_segments (0x27a7e0 : word) = Some W_27a7a4.
Proof. vm_refl. Qed.
Lemma D_27a7a4 : decode_any W_27a7a4 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7a8 : bv 32 := 0x1eb5272f.
Lemma F_27a7a8 : fetch_word Plain.M.loaded_segments (0x27a7e4 : word) = Some W_27a7a8.
Proof. vm_refl. Qed.
Lemma D_27a7a8 : decode_any W_27a7a8 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7ac : bv 32 := 0xfe071ae3.
Lemma F_27a7ac : fetch_word Plain.M.loaded_segments (0x27a7e8 : word) = Some W_27a7ac.
Proof. vm_refl. Qed.
Lemma D_27a7ac : decode_any W_27a7ac = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7b0 : bv 32 := 0x0006859b.
Lemma F_27a7b0 : fetch_word Plain.M.loaded_segments (0x27a7ec : word) = Some W_27a7b0.
Proof. vm_refl. Qed.
Lemma D_27a7b0 : decode_any W_27a7b0 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7b4 : bv 32 := 0x16c58263.
Lemma F_27a7b4 : fetch_word Plain.M.loaded_segments (0x27a7f0 : word) = Some W_27a7b4.
Proof. vm_refl. Qed.
Lemma D_27a7b4 : decode_any W_27a7b4 = Some (Branch BC_EQ 11 12 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7b8 : bv 32 := 0x01f5d613.
Lemma F_27a7b8 : fetch_word Plain.M.loaded_segments (0x27a7f4 : word) = Some W_27a7b8.
Proof. vm_refl. Qed.
Lemma D_27a7b8 : decode_any W_27a7b8 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7bc : bv 32 := 0x00f67633.
Lemma F_27a7bc : fetch_word Plain.M.loaded_segments (0x27a7f8 : word) = Some W_27a7bc.
Proof. vm_refl. Qed.
Lemma D_27a7bc : decode_any W_27a7bc = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7c0 : bv 32 := 0x00c5863b.
Lemma F_27a7c0 : fetch_word Plain.M.loaded_segments (0x27a7fc : word) = Some W_27a7c0.
Proof. vm_refl. Qed.
Lemma D_27a7c0 : decode_any W_27a7c0 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7c4 : bv 32 := 0x00c785b3.
Lemma F_27a7c4 : fetch_word Plain.M.loaded_segments (0x27a800 : word) = Some W_27a7c4.
Proof. vm_refl. Qed.
Lemma D_27a7c4 : decode_any W_27a7c4 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7c8 : bv 32 := 0x0025859b.
Lemma F_27a7c8 : fetch_word Plain.M.loaded_segments (0x27a804 : word) = Some W_27a7c8.
Proof. vm_refl. Qed.
Lemma D_27a7c8 : decode_any W_27a7c8 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7cc : bv 32 := 0x160526af.
Lemma F_27a7cc : fetch_word Plain.M.loaded_segments (0x27a808 : word) = Some W_27a7cc.
Proof. vm_refl. Qed.
Lemma D_27a7cc : decode_any W_27a7cc = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7d0 : bv 32 := 0x00c69663.
Lemma F_27a7d0 : fetch_word Plain.M.loaded_segments (0x27a80c : word) = Some W_27a7d0.
Proof. vm_refl. Qed.
Lemma D_27a7d0 : decode_any W_27a7d0 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7d4 : bv 32 := 0x1eb5272f.
Lemma F_27a7d4 : fetch_word Plain.M.loaded_segments (0x27a810 : word) = Some W_27a7d4.
Proof. vm_refl. Qed.
Lemma D_27a7d4 : decode_any W_27a7d4 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7d8 : bv 32 := 0xfe071ae3.
Lemma F_27a7d8 : fetch_word Plain.M.loaded_segments (0x27a814 : word) = Some W_27a7d8.
Proof. vm_refl. Qed.
Lemma D_27a7d8 : decode_any W_27a7d8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7dc : bv 32 := 0x0006859b.
Lemma F_27a7dc : fetch_word Plain.M.loaded_segments (0x27a818 : word) = Some W_27a7dc.
Proof. vm_refl. Qed.
Lemma D_27a7dc : decode_any W_27a7dc = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7e0 : bv 32 := 0x12c58c63.
Lemma F_27a7e0 : fetch_word Plain.M.loaded_segments (0x27a81c : word) = Some W_27a7e0.
Proof. vm_refl. Qed.
Lemma D_27a7e0 : decode_any W_27a7e0 = Some (Branch BC_EQ 11 12 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7e4 : bv 32 := 0x01f5d613.
Lemma F_27a7e4 : fetch_word Plain.M.loaded_segments (0x27a820 : word) = Some W_27a7e4.
Proof. vm_refl. Qed.
Lemma D_27a7e4 : decode_any W_27a7e4 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7e8 : bv 32 := 0x00f67633.
Lemma F_27a7e8 : fetch_word Plain.M.loaded_segments (0x27a824 : word) = Some W_27a7e8.
Proof. vm_refl. Qed.
Lemma D_27a7e8 : decode_any W_27a7e8 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7ec : bv 32 := 0x00c5863b.
Lemma F_27a7ec : fetch_word Plain.M.loaded_segments (0x27a828 : word) = Some W_27a7ec.
Proof. vm_refl. Qed.
Lemma D_27a7ec : decode_any W_27a7ec = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7f0 : bv 32 := 0x00c785b3.
Lemma F_27a7f0 : fetch_word Plain.M.loaded_segments (0x27a82c : word) = Some W_27a7f0.
Proof. vm_refl. Qed.
Lemma D_27a7f0 : decode_any W_27a7f0 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7f4 : bv 32 := 0x0025859b.
Lemma F_27a7f4 : fetch_word Plain.M.loaded_segments (0x27a830 : word) = Some W_27a7f4.
Proof. vm_refl. Qed.
Lemma D_27a7f4 : decode_any W_27a7f4 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7f8 : bv 32 := 0x160526af.
Lemma F_27a7f8 : fetch_word Plain.M.loaded_segments (0x27a834 : word) = Some W_27a7f8.
Proof. vm_refl. Qed.
Lemma D_27a7f8 : decode_any W_27a7f8 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a7fc : bv 32 := 0x00c69663.
Lemma F_27a7fc : fetch_word Plain.M.loaded_segments (0x27a838 : word) = Some W_27a7fc.
Proof. vm_refl. Qed.
Lemma D_27a7fc : decode_any W_27a7fc = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a800 : bv 32 := 0x1eb5272f.
Lemma F_27a800 : fetch_word Plain.M.loaded_segments (0x27a83c : word) = Some W_27a800.
Proof. vm_refl. Qed.
Lemma D_27a800 : decode_any W_27a800 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a804 : bv 32 := 0xfe071ae3.
Lemma F_27a804 : fetch_word Plain.M.loaded_segments (0x27a840 : word) = Some W_27a804.
Proof. vm_refl. Qed.
Lemma D_27a804 : decode_any W_27a804 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a808 : bv 32 := 0x0006859b.
Lemma F_27a808 : fetch_word Plain.M.loaded_segments (0x27a844 : word) = Some W_27a808.
Proof. vm_refl. Qed.
Lemma D_27a808 : decode_any W_27a808 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a80c : bv 32 := 0x10c58663.
Lemma F_27a80c : fetch_word Plain.M.loaded_segments (0x27a848 : word) = Some W_27a80c.
Proof. vm_refl. Qed.
Lemma D_27a80c : decode_any W_27a80c = Some (Branch BC_EQ 11 12 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a810 : bv 32 := 0x01f5d613.
Lemma F_27a810 : fetch_word Plain.M.loaded_segments (0x27a84c : word) = Some W_27a810.
Proof. vm_refl. Qed.
Lemma D_27a810 : decode_any W_27a810 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a814 : bv 32 := 0x00f67633.
Lemma F_27a814 : fetch_word Plain.M.loaded_segments (0x27a850 : word) = Some W_27a814.
Proof. vm_refl. Qed.
Lemma D_27a814 : decode_any W_27a814 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a818 : bv 32 := 0x00c5863b.
Lemma F_27a818 : fetch_word Plain.M.loaded_segments (0x27a854 : word) = Some W_27a818.
Proof. vm_refl. Qed.
Lemma D_27a818 : decode_any W_27a818 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a81c : bv 32 := 0x00c785b3.
Lemma F_27a81c : fetch_word Plain.M.loaded_segments (0x27a858 : word) = Some W_27a81c.
Proof. vm_refl. Qed.
Lemma D_27a81c : decode_any W_27a81c = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a820 : bv 32 := 0x0025859b.
Lemma F_27a820 : fetch_word Plain.M.loaded_segments (0x27a85c : word) = Some W_27a820.
Proof. vm_refl. Qed.
Lemma D_27a820 : decode_any W_27a820 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a824 : bv 32 := 0x160526af.
Lemma F_27a824 : fetch_word Plain.M.loaded_segments (0x27a860 : word) = Some W_27a824.
Proof. vm_refl. Qed.
Lemma D_27a824 : decode_any W_27a824 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a828 : bv 32 := 0x00c69663.
Lemma F_27a828 : fetch_word Plain.M.loaded_segments (0x27a864 : word) = Some W_27a828.
Proof. vm_refl. Qed.
Lemma D_27a828 : decode_any W_27a828 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a82c : bv 32 := 0x1eb5272f.
Lemma F_27a82c : fetch_word Plain.M.loaded_segments (0x27a868 : word) = Some W_27a82c.
Proof. vm_refl. Qed.
Lemma D_27a82c : decode_any W_27a82c = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a830 : bv 32 := 0xfe071ae3.
Lemma F_27a830 : fetch_word Plain.M.loaded_segments (0x27a86c : word) = Some W_27a830.
Proof. vm_refl. Qed.
Lemma D_27a830 : decode_any W_27a830 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a834 : bv 32 := 0x0006859b.
Lemma F_27a834 : fetch_word Plain.M.loaded_segments (0x27a870 : word) = Some W_27a834.
Proof. vm_refl. Qed.
Lemma D_27a834 : decode_any W_27a834 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a838 : bv 32 := 0x0ec58063.
Lemma F_27a838 : fetch_word Plain.M.loaded_segments (0x27a874 : word) = Some W_27a838.
Proof. vm_refl. Qed.
Lemma D_27a838 : decode_any W_27a838 = Some (Branch BC_EQ 11 12 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a83c : bv 32 := 0x01f5d613.
Lemma F_27a83c : fetch_word Plain.M.loaded_segments (0x27a878 : word) = Some W_27a83c.
Proof. vm_refl. Qed.
Lemma D_27a83c : decode_any W_27a83c = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a840 : bv 32 := 0x00f67633.
Lemma F_27a840 : fetch_word Plain.M.loaded_segments (0x27a87c : word) = Some W_27a840.
Proof. vm_refl. Qed.
Lemma D_27a840 : decode_any W_27a840 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a844 : bv 32 := 0x00c5863b.
Lemma F_27a844 : fetch_word Plain.M.loaded_segments (0x27a880 : word) = Some W_27a844.
Proof. vm_refl. Qed.
Lemma D_27a844 : decode_any W_27a844 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a848 : bv 32 := 0x00c785b3.
Lemma F_27a848 : fetch_word Plain.M.loaded_segments (0x27a884 : word) = Some W_27a848.
Proof. vm_refl. Qed.
Lemma D_27a848 : decode_any W_27a848 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a84c : bv 32 := 0x0025859b.
Lemma F_27a84c : fetch_word Plain.M.loaded_segments (0x27a888 : word) = Some W_27a84c.
Proof. vm_refl. Qed.
Lemma D_27a84c : decode_any W_27a84c = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a850 : bv 32 := 0x160526af.
Lemma F_27a850 : fetch_word Plain.M.loaded_segments (0x27a88c : word) = Some W_27a850.
Proof. vm_refl. Qed.
Lemma D_27a850 : decode_any W_27a850 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a854 : bv 32 := 0x00c69663.
Lemma F_27a854 : fetch_word Plain.M.loaded_segments (0x27a890 : word) = Some W_27a854.
Proof. vm_refl. Qed.
Lemma D_27a854 : decode_any W_27a854 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a858 : bv 32 := 0x1eb5272f.
Lemma F_27a858 : fetch_word Plain.M.loaded_segments (0x27a894 : word) = Some W_27a858.
Proof. vm_refl. Qed.
Lemma D_27a858 : decode_any W_27a858 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a85c : bv 32 := 0xfe071ae3.
Lemma F_27a85c : fetch_word Plain.M.loaded_segments (0x27a898 : word) = Some W_27a85c.
Proof. vm_refl. Qed.
Lemma D_27a85c : decode_any W_27a85c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a860 : bv 32 := 0x0006859b.
Lemma F_27a860 : fetch_word Plain.M.loaded_segments (0x27a89c : word) = Some W_27a860.
Proof. vm_refl. Qed.
Lemma D_27a860 : decode_any W_27a860 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a864 : bv 32 := 0x0ac58a63.
Lemma F_27a864 : fetch_word Plain.M.loaded_segments (0x27a8a0 : word) = Some W_27a864.
Proof. vm_refl. Qed.
Lemma D_27a864 : decode_any W_27a864 = Some (Branch BC_EQ 11 12 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a868 : bv 32 := 0x01f5d613.
Lemma F_27a868 : fetch_word Plain.M.loaded_segments (0x27a8a4 : word) = Some W_27a868.
Proof. vm_refl. Qed.
Lemma D_27a868 : decode_any W_27a868 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a86c : bv 32 := 0x00f67633.
Lemma F_27a86c : fetch_word Plain.M.loaded_segments (0x27a8a8 : word) = Some W_27a86c.
Proof. vm_refl. Qed.
Lemma D_27a86c : decode_any W_27a86c = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a870 : bv 32 := 0x00c5863b.
Lemma F_27a870 : fetch_word Plain.M.loaded_segments (0x27a8ac : word) = Some W_27a870.
Proof. vm_refl. Qed.
Lemma D_27a870 : decode_any W_27a870 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a874 : bv 32 := 0x00c785b3.
Lemma F_27a874 : fetch_word Plain.M.loaded_segments (0x27a8b0 : word) = Some W_27a874.
Proof. vm_refl. Qed.
Lemma D_27a874 : decode_any W_27a874 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a878 : bv 32 := 0x0025859b.
Lemma F_27a878 : fetch_word Plain.M.loaded_segments (0x27a8b4 : word) = Some W_27a878.
Proof. vm_refl. Qed.
Lemma D_27a878 : decode_any W_27a878 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a87c : bv 32 := 0x160526af.
Lemma F_27a87c : fetch_word Plain.M.loaded_segments (0x27a8b8 : word) = Some W_27a87c.
Proof. vm_refl. Qed.
Lemma D_27a87c : decode_any W_27a87c = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a880 : bv 32 := 0x00c69663.
Lemma F_27a880 : fetch_word Plain.M.loaded_segments (0x27a8bc : word) = Some W_27a880.
Proof. vm_refl. Qed.
Lemma D_27a880 : decode_any W_27a880 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a884 : bv 32 := 0x1eb5272f.
Lemma F_27a884 : fetch_word Plain.M.loaded_segments (0x27a8c0 : word) = Some W_27a884.
Proof. vm_refl. Qed.
Lemma D_27a884 : decode_any W_27a884 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a888 : bv 32 := 0xfe071ae3.
Lemma F_27a888 : fetch_word Plain.M.loaded_segments (0x27a8c4 : word) = Some W_27a888.
Proof. vm_refl. Qed.
Lemma D_27a888 : decode_any W_27a888 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a88c : bv 32 := 0x0006859b.
Lemma F_27a88c : fetch_word Plain.M.loaded_segments (0x27a8c8 : word) = Some W_27a88c.
Proof. vm_refl. Qed.
Lemma D_27a88c : decode_any W_27a88c = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a890 : bv 32 := 0x08c58463.
Lemma F_27a890 : fetch_word Plain.M.loaded_segments (0x27a8cc : word) = Some W_27a890.
Proof. vm_refl. Qed.
Lemma D_27a890 : decode_any W_27a890 = Some (Branch BC_EQ 11 12 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a894 : bv 32 := 0x01f5d613.
Lemma F_27a894 : fetch_word Plain.M.loaded_segments (0x27a8d0 : word) = Some W_27a894.
Proof. vm_refl. Qed.
Lemma D_27a894 : decode_any W_27a894 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a898 : bv 32 := 0x00f67633.
Lemma F_27a898 : fetch_word Plain.M.loaded_segments (0x27a8d4 : word) = Some W_27a898.
Proof. vm_refl. Qed.
Lemma D_27a898 : decode_any W_27a898 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a89c : bv 32 := 0x00c5863b.
Lemma F_27a89c : fetch_word Plain.M.loaded_segments (0x27a8d8 : word) = Some W_27a89c.
Proof. vm_refl. Qed.
Lemma D_27a89c : decode_any W_27a89c = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8a0 : bv 32 := 0x00c785b3.
Lemma F_27a8a0 : fetch_word Plain.M.loaded_segments (0x27a8dc : word) = Some W_27a8a0.
Proof. vm_refl. Qed.
Lemma D_27a8a0 : decode_any W_27a8a0 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8a4 : bv 32 := 0x0025859b.
Lemma F_27a8a4 : fetch_word Plain.M.loaded_segments (0x27a8e0 : word) = Some W_27a8a4.
Proof. vm_refl. Qed.
Lemma D_27a8a4 : decode_any W_27a8a4 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8a8 : bv 32 := 0x160526af.
Lemma F_27a8a8 : fetch_word Plain.M.loaded_segments (0x27a8e4 : word) = Some W_27a8a8.
Proof. vm_refl. Qed.
Lemma D_27a8a8 : decode_any W_27a8a8 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8ac : bv 32 := 0x00c69663.
Lemma F_27a8ac : fetch_word Plain.M.loaded_segments (0x27a8e8 : word) = Some W_27a8ac.
Proof. vm_refl. Qed.
Lemma D_27a8ac : decode_any W_27a8ac = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8b0 : bv 32 := 0x1eb5272f.
Lemma F_27a8b0 : fetch_word Plain.M.loaded_segments (0x27a8ec : word) = Some W_27a8b0.
Proof. vm_refl. Qed.
Lemma D_27a8b0 : decode_any W_27a8b0 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8b4 : bv 32 := 0xfe071ae3.
Lemma F_27a8b4 : fetch_word Plain.M.loaded_segments (0x27a8f0 : word) = Some W_27a8b4.
Proof. vm_refl. Qed.
Lemma D_27a8b4 : decode_any W_27a8b4 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8b8 : bv 32 := 0x0006859b.
Lemma F_27a8b8 : fetch_word Plain.M.loaded_segments (0x27a8f4 : word) = Some W_27a8b8.
Proof. vm_refl. Qed.
Lemma D_27a8b8 : decode_any W_27a8b8 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8bc : bv 32 := 0x04c58e63.
Lemma F_27a8bc : fetch_word Plain.M.loaded_segments (0x27a8f8 : word) = Some W_27a8bc.
Proof. vm_refl. Qed.
Lemma D_27a8bc : decode_any W_27a8bc = Some (Branch BC_EQ 11 12 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8c0 : bv 32 := 0x01f5d613.
Lemma F_27a8c0 : fetch_word Plain.M.loaded_segments (0x27a8fc : word) = Some W_27a8c0.
Proof. vm_refl. Qed.
Lemma D_27a8c0 : decode_any W_27a8c0 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8c4 : bv 32 := 0x00f67633.
Lemma F_27a8c4 : fetch_word Plain.M.loaded_segments (0x27a900 : word) = Some W_27a8c4.
Proof. vm_refl. Qed.
Lemma D_27a8c4 : decode_any W_27a8c4 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8c8 : bv 32 := 0x00c5863b.
Lemma F_27a8c8 : fetch_word Plain.M.loaded_segments (0x27a904 : word) = Some W_27a8c8.
Proof. vm_refl. Qed.
Lemma D_27a8c8 : decode_any W_27a8c8 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8cc : bv 32 := 0x00c785b3.
Lemma F_27a8cc : fetch_word Plain.M.loaded_segments (0x27a908 : word) = Some W_27a8cc.
Proof. vm_refl. Qed.
Lemma D_27a8cc : decode_any W_27a8cc = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8d0 : bv 32 := 0x0025859b.
Lemma F_27a8d0 : fetch_word Plain.M.loaded_segments (0x27a90c : word) = Some W_27a8d0.
Proof. vm_refl. Qed.
Lemma D_27a8d0 : decode_any W_27a8d0 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8d4 : bv 32 := 0x160526af.
Lemma F_27a8d4 : fetch_word Plain.M.loaded_segments (0x27a910 : word) = Some W_27a8d4.
Proof. vm_refl. Qed.
Lemma D_27a8d4 : decode_any W_27a8d4 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8d8 : bv 32 := 0x00c69663.
Lemma F_27a8d8 : fetch_word Plain.M.loaded_segments (0x27a914 : word) = Some W_27a8d8.
Proof. vm_refl. Qed.
Lemma D_27a8d8 : decode_any W_27a8d8 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8dc : bv 32 := 0x1eb5272f.
Lemma F_27a8dc : fetch_word Plain.M.loaded_segments (0x27a918 : word) = Some W_27a8dc.
Proof. vm_refl. Qed.
Lemma D_27a8dc : decode_any W_27a8dc = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8e0 : bv 32 := 0xfe071ae3.
Lemma F_27a8e0 : fetch_word Plain.M.loaded_segments (0x27a91c : word) = Some W_27a8e0.
Proof. vm_refl. Qed.
Lemma D_27a8e0 : decode_any W_27a8e0 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8e4 : bv 32 := 0x0006859b.
Lemma F_27a8e4 : fetch_word Plain.M.loaded_segments (0x27a920 : word) = Some W_27a8e4.
Proof. vm_refl. Qed.
Lemma D_27a8e4 : decode_any W_27a8e4 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8e8 : bv 32 := 0x02c58863.
Lemma F_27a8e8 : fetch_word Plain.M.loaded_segments (0x27a924 : word) = Some W_27a8e8.
Proof. vm_refl. Qed.
Lemma D_27a8e8 : decode_any W_27a8e8 = Some (Branch BC_EQ 11 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8ec : bv 32 := 0x01f5d613.
Lemma F_27a8ec : fetch_word Plain.M.loaded_segments (0x27a928 : word) = Some W_27a8ec.
Proof. vm_refl. Qed.
Lemma D_27a8ec : decode_any W_27a8ec = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8f0 : bv 32 := 0x00f67633.
Lemma F_27a8f0 : fetch_word Plain.M.loaded_segments (0x27a92c : word) = Some W_27a8f0.
Proof. vm_refl. Qed.
Lemma D_27a8f0 : decode_any W_27a8f0 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8f4 : bv 32 := 0x00c585bb.
Lemma F_27a8f4 : fetch_word Plain.M.loaded_segments (0x27a930 : word) = Some W_27a8f4.
Proof. vm_refl. Qed.
Lemma D_27a8f4 : decode_any W_27a8f4 = Some (Op32 ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8f8 : bv 32 := 0x00b78633.
Lemma F_27a8f8 : fetch_word Plain.M.loaded_segments (0x27a934 : word) = Some W_27a8f8.
Proof. vm_refl. Qed.
Lemma D_27a8f8 : decode_any W_27a8f8 = Some (Op ALU_ADD 12 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a8fc : bv 32 := 0x0026061b.
Lemma F_27a8fc : fetch_word Plain.M.loaded_segments (0x27a938 : word) = Some W_27a8fc.
Proof. vm_refl. Qed.
Lemma D_27a8fc : decode_any W_27a8fc = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a900 : bv 32 := 0x160526af.
Lemma F_27a900 : fetch_word Plain.M.loaded_segments (0x27a93c : word) = Some W_27a900.
Proof. vm_refl. Qed.
Lemma D_27a900 : decode_any W_27a900 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a904 : bv 32 := 0x00b69663.
Lemma F_27a904 : fetch_word Plain.M.loaded_segments (0x27a940 : word) = Some W_27a904.
Proof. vm_refl. Qed.
Lemma D_27a904 : decode_any W_27a904 = Some (Branch BC_NE 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a908 : bv 32 := 0x1ec5272f.
Lemma F_27a908 : fetch_word Plain.M.loaded_segments (0x27a944 : word) = Some W_27a908.
Proof. vm_refl. Qed.
Lemma D_27a908 : decode_any W_27a908 = Some (Sc AW true true 14 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a90c : bv 32 := 0xfe071ae3.
Lemma F_27a90c : fetch_word Plain.M.loaded_segments (0x27a948 : word) = Some W_27a90c.
Proof. vm_refl. Qed.
Lemma D_27a90c : decode_any W_27a90c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a910 : bv 32 := 0x0006869b.
Lemma F_27a910 : fetch_word Plain.M.loaded_segments (0x27a94c : word) = Some W_27a910.
Proof. vm_refl. Qed.
Lemma D_27a910 : decode_any W_27a910 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a914 : bv 32 := 0x00b69463.
Lemma F_27a914 : fetch_word Plain.M.loaded_segments (0x27a950 : word) = Some W_27a914.
Proof. vm_refl. Qed.
Lemma D_27a914 : decode_any W_27a914 = Some (Branch BC_NE 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a918 : bv 32 := 0x00008067.
Lemma F_27a918 : fetch_word Plain.M.loaded_segments (0x27a954 : word) = Some W_27a918.
Proof. vm_refl. Qed.
Lemma D_27a918 : decode_any W_27a918 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a91c : bv 32 := 0x00052583.
Lemma F_27a91c : fetch_word Plain.M.loaded_segments (0x27a958 : word) = Some W_27a91c.
Proof. vm_refl. Qed.
Lemma D_27a91c : decode_any W_27a91c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a920 : bv 32 := 0x0015881b.
Lemma F_27a920 : fetch_word Plain.M.loaded_segments (0x27a95c : word) = Some W_27a920.
Proof. vm_refl. Qed.
Lemma D_27a920 : decode_any W_27a920 = Some (OpImm32 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a924 : bv 32 := 0x1605262f.
Lemma F_27a924 : fetch_word Plain.M.loaded_segments (0x27a960 : word) = Some W_27a924.
Proof. vm_refl. Qed.
Lemma D_27a924 : decode_any W_27a924 = Some (Lr AW true true 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a928 : bv 32 := 0x00b61663.
Lemma F_27a928 : fetch_word Plain.M.loaded_segments (0x27a964 : word) = Some W_27a928.
Proof. vm_refl. Qed.
Lemma D_27a928 : decode_any W_27a928 = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a92c : bv 32 := 0x1f0526af.
Lemma F_27a92c : fetch_word Plain.M.loaded_segments (0x27a968 : word) = Some W_27a92c.
Proof. vm_refl. Qed.
Lemma D_27a92c : decode_any W_27a92c = Some (Sc AW true true 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a930 : bv 32 := 0xfe069ae3.
Lemma F_27a930 : fetch_word Plain.M.loaded_segments (0x27a96c : word) = Some W_27a930.
Proof. vm_refl. Qed.
Lemma D_27a930 : decode_any W_27a930 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a934 : bv 32 := 0x0006061b.
Lemma F_27a934 : fetch_word Plain.M.loaded_segments (0x27a970 : word) = Some W_27a934.
Proof. vm_refl. Qed.
Lemma D_27a934 : decode_any W_27a934 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a938 : bv 32 := 0xfeb612e3.
Lemma F_27a938 : fetch_word Plain.M.loaded_segments (0x27a974 : word) = Some W_27a938.
Proof. vm_refl. Qed.
Lemma D_27a938 : decode_any W_27a938 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a93c : bv 32 := 0xfda00293.
Lemma F_27a93c : fetch_word Plain.M.loaded_segments (0x27a978 : word) = Some W_27a93c.
Proof. vm_refl. Qed.
Lemma D_27a93c : decode_any W_27a93c = Some (OpImm ALU_ADD 5 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a940 : bv 32 := 0x80000337.
Lemma F_27a940 : fetch_word Plain.M.loaded_segments (0x27a97c : word) = Some W_27a940.
Proof. vm_refl. Qed.
Lemma D_27a940 : decode_any W_27a940 = Some (Lui 6 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a944 : bv 32 := 0x02c0006f.
Lemma F_27a944 : fetch_word Plain.M.loaded_segments (0x27a980 : word) = Some W_27a944.
Proof. vm_refl. Qed.
Lemma D_27a944 : decode_any W_27a944 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a948 : bv 32 := 0x00f8083b.
Lemma F_27a948 : fetch_word Plain.M.loaded_segments (0x27a984 : word) = Some W_27a948.
Proof. vm_refl. Qed.
Lemma D_27a948 : decode_any W_27a948 = Some (Op32 ALU_ADD 16 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a94c : bv 32 := 0x00070513.
Lemma F_27a94c : fetch_word Plain.M.loaded_segments (0x27a988 : word) = Some W_27a94c.
Proof. vm_refl. Qed.
Lemma D_27a94c : decode_any W_27a94c = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a950 : bv 32 := 0x006865b3.
Lemma F_27a950 : fetch_word Plain.M.loaded_segments (0x27a98c : word) = Some W_27a950.
Proof. vm_refl. Qed.
Lemma D_27a950 : decode_any W_27a950 = Some (Op ALU_OR 11 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a954 : bv 32 := 0x0008061b.
Lemma F_27a954 : fetch_word Plain.M.loaded_segments (0x27a990 : word) = Some W_27a954.
Proof. vm_refl. Qed.
Lemma D_27a954 : decode_any W_27a954 = Some (OpImm32 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a958 : bv 32 := 0x1605282f.
Lemma F_27a958 : fetch_word Plain.M.loaded_segments (0x27a994 : word) = Some W_27a958.
Proof. vm_refl. Qed.
Lemma D_27a958 : decode_any W_27a958 = Some (Lr AW true true 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a95c : bv 32 := 0x00c81663.
Lemma F_27a95c : fetch_word Plain.M.loaded_segments (0x27a998 : word) = Some W_27a95c.
Proof. vm_refl. Qed.
Lemma D_27a95c : decode_any W_27a95c = Some (Branch BC_NE 16 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a960 : bv 32 := 0x1eb526af.
Lemma F_27a960 : fetch_word Plain.M.loaded_segments (0x27a99c : word) = Some W_27a960.
Proof. vm_refl. Qed.
Lemma D_27a960 : decode_any W_27a960 = Some (Sc AW true true 13 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a964 : bv 32 := 0xfe069ae3.
Lemma F_27a964 : fetch_word Plain.M.loaded_segments (0x27a9a0 : word) = Some W_27a964.
Proof. vm_refl. Qed.
Lemma D_27a964 : decode_any W_27a964 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a968 : bv 32 := 0x0008059b.
Lemma F_27a968 : fetch_word Plain.M.loaded_segments (0x27a9a4 : word) = Some W_27a968.
Proof. vm_refl. Qed.
Lemma D_27a968 : decode_any W_27a968 = Some (OpImm32 11 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a96c : bv 32 := 0xfac586e3.
Lemma F_27a96c : fetch_word Plain.M.loaded_segments (0x27a9a8 : word) = Some W_27a96c.
Proof. vm_refl. Qed.
Lemma D_27a96c : decode_any W_27a96c = Some (Branch BC_EQ 11 12 8108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a970 : bv 32 := 0x0008061b.
Lemma F_27a970 : fetch_word Plain.M.loaded_segments (0x27a9ac : word) = Some W_27a970.
Proof. vm_refl. Qed.
Lemma D_27a970 : decode_any W_27a970 = Some (OpImm32 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a974 : bv 32 := 0xfc065ee3.
Lemma F_27a974 : fetch_word Plain.M.loaded_segments (0x27a9b0 : word) = Some W_27a974.
Proof. vm_refl. Qed.
Lemma D_27a974 : decode_any W_27a974 = Some (Branch BC_GE 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a978 : bv 32 := 0x06200893.
Lemma F_27a978 : fetch_word Plain.M.loaded_segments (0x27a9b4 : word) = Some W_27a978.
Proof. vm_refl. Qed.
Lemma D_27a978 : decode_any W_27a978 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a97c : bv 32 := 0x08000593.
Lemma F_27a97c : fetch_word Plain.M.loaded_segments (0x27a9b8 : word) = Some W_27a97c.
Proof. vm_refl. Qed.
Lemma D_27a97c : decode_any W_27a97c = Some (OpImm ALU_ADD 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a980 : bv 32 := 0x00050713.
Lemma F_27a980 : fetch_word Plain.M.loaded_segments (0x27a9bc : word) = Some W_27a980.
Proof. vm_refl. Qed.
Lemma D_27a980 : decode_any W_27a980 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a984 : bv 32 := 0x00000693.
Lemma F_27a984 : fetch_word Plain.M.loaded_segments (0x27a9c0 : word) = Some W_27a984.
Proof. vm_refl. Qed.
Lemma D_27a984 : decode_any W_27a984 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a988 : bv 32 := 0x00000073.
Lemma F_27a988 : fetch_word Plain.M.loaded_segments (0x27a9c4 : word) = Some W_27a988.
Proof. vm_refl. Qed.
Lemma D_27a988 : decode_any W_27a988 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_27a988 : is_ecall W_27a988 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_27a98c : bv 32 := 0xfa551ee3.
Lemma F_27a98c : fetch_word Plain.M.loaded_segments (0x27a9c8 : word) = Some W_27a98c.
Proof. vm_refl. Qed.
Lemma D_27a98c : decode_any W_27a98c = Some (Branch BC_NE 10 5 8124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a990 : bv 32 := 0x06200893.
Lemma F_27a990 : fetch_word Plain.M.loaded_segments (0x27a9cc : word) = Some W_27a990.
Proof. vm_refl. Qed.
Lemma D_27a990 : decode_any W_27a990 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a994 : bv 32 := 0x00070513.
Lemma F_27a994 : fetch_word Plain.M.loaded_segments (0x27a9d0 : word) = Some W_27a994.
Proof. vm_refl. Qed.
Lemma D_27a994 : decode_any W_27a994 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a998 : bv 32 := 0x00000593.
Lemma F_27a998 : fetch_word Plain.M.loaded_segments (0x27a9d4 : word) = Some W_27a998.
Proof. vm_refl. Qed.
Lemma D_27a998 : decode_any W_27a998 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a99c : bv 32 := 0x00000693.
Lemma F_27a99c : fetch_word Plain.M.loaded_segments (0x27a9d8 : word) = Some W_27a99c.
Proof. vm_refl. Qed.
Lemma D_27a99c : decode_any W_27a99c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9a0 : bv 32 := 0x00000073.
Lemma F_27a9a0 : fetch_word Plain.M.loaded_segments (0x27a9dc : word) = Some W_27a9a0.
Proof. vm_refl. Qed.
Lemma D_27a9a0 : decode_any W_27a9a0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_27a9a0 : is_ecall W_27a9a0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_27a9a4 : bv 32 := 0xfa5ff06f.
Lemma F_27a9a4 : fetch_word Plain.M.loaded_segments (0x27a9e0 : word) = Some W_27a9a4.
Proof. vm_refl. Qed.
Lemma D_27a9a4 : decode_any W_27a9a4 = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9a8 : bv 32 := 0x00052583.
Lemma F_27a9a8 : fetch_word Plain.M.loaded_segments (0x27a9e4 : word) = Some W_27a9a8.
Proof. vm_refl. Qed.
Lemma D_27a9a8 : decode_any W_27a9a8 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9ac : bv 32 := 0x0005c463.
Lemma F_27a9ac : fetch_word Plain.M.loaded_segments (0x27a9e8 : word) = Some W_27a9ac.
Proof. vm_refl. Qed.
Lemma D_27a9ac : decode_any W_27a9ac = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9b0 : bv 32 := 0x00008067.
Lemma F_27a9b0 : fetch_word Plain.M.loaded_segments (0x27a9ec : word) = Some W_27a9b0.
Proof. vm_refl. Qed.
Lemma D_27a9b0 : decode_any W_27a9b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9b4 : bv 32 := 0x80000637.
Lemma F_27a9b4 : fetch_word Plain.M.loaded_segments (0x27a9f0 : word) = Some W_27a9b4.
Proof. vm_refl. Qed.
Lemma D_27a9b4 : decode_any W_27a9b4 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9b8 : bv 32 := 0xfff60613.
Lemma F_27a9b8 : fetch_word Plain.M.loaded_segments (0x27a9f4 : word) = Some W_27a9b8.
Proof. vm_refl. Qed.
Lemma D_27a9b8 : decode_any W_27a9b8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9bc : bv 32 := 0x00052583.
Lemma F_27a9bc : fetch_word Plain.M.loaded_segments (0x27a9f8 : word) = Some W_27a9bc.
Proof. vm_refl. Qed.
Lemma D_27a9bc : decode_any W_27a9bc = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9c0 : bv 32 := 0x00c586bb.
Lemma F_27a9c0 : fetch_word Plain.M.loaded_segments (0x27a9fc : word) = Some W_27a9c0.
Proof. vm_refl. Qed.
Lemma D_27a9c0 : decode_any W_27a9c0 = Some (Op32 ALU_ADD 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9c4 : bv 32 := 0x1605272f.
Lemma F_27a9c4 : fetch_word Plain.M.loaded_segments (0x27aa00 : word) = Some W_27a9c4.
Proof. vm_refl. Qed.
Lemma D_27a9c4 : decode_any W_27a9c4 = Some (Lr AW true true 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9c8 : bv 32 := 0x00b71663.
Lemma F_27a9c8 : fetch_word Plain.M.loaded_segments (0x27aa04 : word) = Some W_27a9c8.
Proof. vm_refl. Qed.
Lemma D_27a9c8 : decode_any W_27a9c8 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9cc : bv 32 := 0x1ed527af.
Lemma F_27a9cc : fetch_word Plain.M.loaded_segments (0x27aa08 : word) = Some W_27a9cc.
Proof. vm_refl. Qed.
Lemma D_27a9cc : decode_any W_27a9cc = Some (Sc AW true true 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9d0 : bv 32 := 0xfe079ae3.
Lemma F_27a9d0 : fetch_word Plain.M.loaded_segments (0x27aa0c : word) = Some W_27a9d0.
Proof. vm_refl. Qed.
Lemma D_27a9d0 : decode_any W_27a9d0 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9d4 : bv 32 := 0x0007071b.
Lemma F_27a9d4 : fetch_word Plain.M.loaded_segments (0x27aa10 : word) = Some W_27a9d4.
Proof. vm_refl. Qed.
Lemma D_27a9d4 : decode_any W_27a9d4 = Some (OpImm32 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9d8 : bv 32 := 0xfeb712e3.
Lemma F_27a9d8 : fetch_word Plain.M.loaded_segments (0x27aa14 : word) = Some W_27a9d8.
Proof. vm_refl. Qed.
Lemma D_27a9d8 : decode_any W_27a9d8 = Some (Branch BC_NE 14 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9dc : bv 32 := 0x80000637.
Lemma F_27a9dc : fetch_word Plain.M.loaded_segments (0x27aa18 : word) = Some W_27a9dc.
Proof. vm_refl. Qed.
Lemma D_27a9dc : decode_any W_27a9dc = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9e0 : bv 32 := 0x0016061b.
Lemma F_27a9e0 : fetch_word Plain.M.loaded_segments (0x27aa1c : word) = Some W_27a9e0.
Proof. vm_refl. Qed.
Lemma D_27a9e0 : decode_any W_27a9e0 = Some (OpImm32 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9e4 : bv 32 := 0xfcc586e3.
Lemma F_27a9e4 : fetch_word Plain.M.loaded_segments (0x27aa20 : word) = Some W_27a9e4.
Proof. vm_refl. Qed.
Lemma D_27a9e4 : decode_any W_27a9e4 = Some (Branch BC_EQ 11 12 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9e8 : bv 32 := 0x06200893.
Lemma F_27a9e8 : fetch_word Plain.M.loaded_segments (0x27aa24 : word) = Some W_27a9e8.
Proof. vm_refl. Qed.
Lemma D_27a9e8 : decode_any W_27a9e8 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9ec : bv 32 := 0x08100593.
Lemma F_27a9ec : fetch_word Plain.M.loaded_segments (0x27aa28 : word) = Some W_27a9ec.
Proof. vm_refl. Qed.
Lemma D_27a9ec : decode_any W_27a9ec = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9f0 : bv 32 := 0x00100613.
Lemma F_27a9f0 : fetch_word Plain.M.loaded_segments (0x27aa2c : word) = Some W_27a9f0.
Proof. vm_refl. Qed.
Lemma D_27a9f0 : decode_any W_27a9f0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9f4 : bv 32 := 0xfda00713.
Lemma F_27a9f4 : fetch_word Plain.M.loaded_segments (0x27aa30 : word) = Some W_27a9f4.
Proof. vm_refl. Qed.
Lemma D_27a9f4 : decode_any W_27a9f4 = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9f8 : bv 32 := 0x00050693.
Lemma F_27a9f8 : fetch_word Plain.M.loaded_segments (0x27aa34 : word) = Some W_27a9f8.
Proof. vm_refl. Qed.
Lemma D_27a9f8 : decode_any W_27a9f8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27a9fc : bv 32 := 0x00000073.
Lemma F_27a9fc : fetch_word Plain.M.loaded_segments (0x27aa38 : word) = Some W_27a9fc.
Proof. vm_refl. Qed.
Lemma D_27a9fc : decode_any W_27a9fc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_27a9fc : is_ecall W_27a9fc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_27aa00 : bv 32 := 0xfae518e3.
Lemma F_27aa00 : fetch_word Plain.M.loaded_segments (0x27aa3c : word) = Some W_27aa00.
Proof. vm_refl. Qed.
Lemma D_27aa00 : decode_any W_27aa00 = Some (Branch BC_NE 10 14 8112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27aa04 : bv 32 := 0x06200893.
Lemma F_27aa04 : fetch_word Plain.M.loaded_segments (0x27aa40 : word) = Some W_27aa04.
Proof. vm_refl. Qed.
Lemma D_27aa04 : decode_any W_27aa04 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27aa08 : bv 32 := 0x00100593.
Lemma F_27aa08 : fetch_word Plain.M.loaded_segments (0x27aa44 : word) = Some W_27aa08.
Proof. vm_refl. Qed.
Lemma D_27aa08 : decode_any W_27aa08 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27aa0c : bv 32 := 0x00100613.
Lemma F_27aa0c : fetch_word Plain.M.loaded_segments (0x27aa48 : word) = Some W_27aa0c.
Proof. vm_refl. Qed.
Lemma D_27aa0c : decode_any W_27aa0c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27aa10 : bv 32 := 0x00068513.
Lemma F_27aa10 : fetch_word Plain.M.loaded_segments (0x27aa4c : word) = Some W_27aa10.
Proof. vm_refl. Qed.
Lemma D_27aa10 : decode_any W_27aa10 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27aa14 : bv 32 := 0x00000073.
Lemma F_27aa14 : fetch_word Plain.M.loaded_segments (0x27aa50 : word) = Some W_27aa14.
Proof. vm_refl. Qed.
Lemma D_27aa14 : decode_any W_27aa14 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_27aa14 : is_ecall W_27aa14 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_27aa18 : bv 32 := 0x00008067.
Lemma F_27aa18 : fetch_word Plain.M.loaded_segments (0x27aa54 : word) = Some W_27aa18.
Proof. vm_refl. Qed.
Lemma D_27aa18 : decode_any W_27aa18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
