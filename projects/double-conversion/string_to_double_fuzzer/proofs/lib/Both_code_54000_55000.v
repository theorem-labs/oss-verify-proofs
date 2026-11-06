(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation BSEGS_I := ImgB.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_54a28 : bv 32 := 0x00195593.
Lemma F_54a28 : fetch_word BSEGS_I (0x54a28 : word) = Some W_54a28.
Proof. vm_refl. Qed.
Lemma D_54a28 : decode_any W_54a28 = Some (ShiftImm ALU_SRL 11 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a2c : bv 32 := 0x55555637.
Lemma F_54a2c : fetch_word BSEGS_I (0x54a2c : word) = Some W_54a2c.
Proof. vm_refl. Qed.
Lemma D_54a2c : decode_any W_54a2c = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a30 : bv 32 := 0x33333737.
Lemma F_54a30 : fetch_word BSEGS_I (0x54a30 : word) = Some W_54a30.
Proof. vm_refl. Qed.
Lemma D_54a30 : decode_any W_54a30 = Some (Lui 14 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a34 : bv 32 := 0x0f0f17b7.
Lemma F_54a34 : fetch_word BSEGS_I (0x54a34 : word) = Some W_54a34.
Proof. vm_refl. Qed.
Lemma D_54a34 : decode_any W_54a34 = Some (Lui 15 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a38 : bv 32 := 0x00b965b3.
Lemma F_54a38 : fetch_word BSEGS_I (0x54a38 : word) = Some W_54a38.
Proof. vm_refl. Qed.
Lemma D_54a38 : decode_any W_54a38 = Some (Op ALU_OR 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a3c : bv 32 := 0x5556061b.
Lemma F_54a3c : fetch_word BSEGS_I (0x54a3c : word) = Some W_54a3c.
Proof. vm_refl. Qed.
Lemma D_54a3c : decode_any W_54a3c = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a40 : bv 32 := 0x3337071b.
Lemma F_54a40 : fetch_word BSEGS_I (0x54a40 : word) = Some W_54a40.
Proof. vm_refl. Qed.
Lemma D_54a40 : decode_any W_54a40 = Some (OpImm32 14 14 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a44 : bv 32 := 0xf0f7879b.
Lemma F_54a44 : fetch_word BSEGS_I (0x54a44 : word) = Some W_54a44.
Proof. vm_refl. Qed.
Lemma D_54a44 : decode_any W_54a44 = Some (OpImm32 15 15 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a48 : bv 32 := 0x0025d813.
Lemma F_54a48 : fetch_word BSEGS_I (0x54a48 : word) = Some W_54a48.
Proof. vm_refl. Qed.
Lemma D_54a48 : decode_any W_54a48 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a4c : bv 32 := 0x0105e5b3.
Lemma F_54a4c : fetch_word BSEGS_I (0x54a4c : word) = Some W_54a4c.
Proof. vm_refl. Qed.
Lemma D_54a4c : decode_any W_54a4c = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a50 : bv 32 := 0x02061813.
Lemma F_54a50 : fetch_word BSEGS_I (0x54a50 : word) = Some W_54a50.
Proof. vm_refl. Qed.
Lemma D_54a50 : decode_any W_54a50 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a54 : bv 32 := 0x01060633.
Lemma F_54a54 : fetch_word BSEGS_I (0x54a54 : word) = Some W_54a54.
Proof. vm_refl. Qed.
Lemma D_54a54 : decode_any W_54a54 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a58 : bv 32 := 0x02071813.
Lemma F_54a58 : fetch_word BSEGS_I (0x54a58 : word) = Some W_54a58.
Proof. vm_refl. Qed.
Lemma D_54a58 : decode_any W_54a58 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a5c : bv 32 := 0x01070733.
Lemma F_54a5c : fetch_word BSEGS_I (0x54a5c : word) = Some W_54a5c.
Proof. vm_refl. Qed.
Lemma D_54a5c : decode_any W_54a5c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a60 : bv 32 := 0x02079813.
Lemma F_54a60 : fetch_word BSEGS_I (0x54a60 : word) = Some W_54a60.
Proof. vm_refl. Qed.
Lemma D_54a60 : decode_any W_54a60 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a64 : bv 32 := 0x010787b3.
Lemma F_54a64 : fetch_word BSEGS_I (0x54a64 : word) = Some W_54a64.
Proof. vm_refl. Qed.
Lemma D_54a64 : decode_any W_54a64 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a68 : bv 32 := 0x0045d813.
Lemma F_54a68 : fetch_word BSEGS_I (0x54a68 : word) = Some W_54a68.
Proof. vm_refl. Qed.
Lemma D_54a68 : decode_any W_54a68 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a6c : bv 32 := 0x0105e5b3.
Lemma F_54a6c : fetch_word BSEGS_I (0x54a6c : word) = Some W_54a6c.
Proof. vm_refl. Qed.
Lemma D_54a6c : decode_any W_54a6c = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a70 : bv 32 := 0x0085d813.
Lemma F_54a70 : fetch_word BSEGS_I (0x54a70 : word) = Some W_54a70.
Proof. vm_refl. Qed.
Lemma D_54a70 : decode_any W_54a70 = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a74 : bv 32 := 0x0105e5b3.
Lemma F_54a74 : fetch_word BSEGS_I (0x54a74 : word) = Some W_54a74.
Proof. vm_refl. Qed.
Lemma D_54a74 : decode_any W_54a74 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a78 : bv 32 := 0x0105d813.
Lemma F_54a78 : fetch_word BSEGS_I (0x54a78 : word) = Some W_54a78.
Proof. vm_refl. Qed.
Lemma D_54a78 : decode_any W_54a78 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a7c : bv 32 := 0x0105e5b3.
Lemma F_54a7c : fetch_word BSEGS_I (0x54a7c : word) = Some W_54a7c.
Proof. vm_refl. Qed.
Lemma D_54a7c : decode_any W_54a7c = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a80 : bv 32 := 0x0205d813.
Lemma F_54a80 : fetch_word BSEGS_I (0x54a80 : word) = Some W_54a80.
Proof. vm_refl. Qed.
Lemma D_54a80 : decode_any W_54a80 = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a84 : bv 32 := 0x0105e5b3.
Lemma F_54a84 : fetch_word BSEGS_I (0x54a84 : word) = Some W_54a84.
Proof. vm_refl. Qed.
Lemma D_54a84 : decode_any W_54a84 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a88 : bv 32 := 0xfff5c593.
Lemma F_54a88 : fetch_word BSEGS_I (0x54a88 : word) = Some W_54a88.
Proof. vm_refl. Qed.
Lemma D_54a88 : decode_any W_54a88 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a8c : bv 32 := 0x0015d813.
Lemma F_54a8c : fetch_word BSEGS_I (0x54a8c : word) = Some W_54a8c.
Proof. vm_refl. Qed.
Lemma D_54a8c : decode_any W_54a8c = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a90 : bv 32 := 0x00c87633.
Lemma F_54a90 : fetch_word BSEGS_I (0x54a90 : word) = Some W_54a90.
Proof. vm_refl. Qed.
Lemma D_54a90 : decode_any W_54a90 = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a94 : bv 32 := 0x01010837.
Lemma F_54a94 : fetch_word BSEGS_I (0x54a94 : word) = Some W_54a94.
Proof. vm_refl. Qed.
Lemma D_54a94 : decode_any W_54a94 = Some (Lui 16 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a98 : bv 32 := 0x40c585b3.
Lemma F_54a98 : fetch_word BSEGS_I (0x54a98 : word) = Some W_54a98.
Proof. vm_refl. Qed.
Lemma D_54a98 : decode_any W_54a98 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54a9c : bv 32 := 0x0025d613.
Lemma F_54a9c : fetch_word BSEGS_I (0x54a9c : word) = Some W_54a9c.
Proof. vm_refl. Qed.
Lemma D_54a9c : decode_any W_54a9c = Some (ShiftImm ALU_SRL 12 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54aa0 : bv 32 := 0x00e5f5b3.
Lemma F_54aa0 : fetch_word BSEGS_I (0x54aa0 : word) = Some W_54aa0.
Proof. vm_refl. Qed.
Lemma D_54aa0 : decode_any W_54aa0 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54aa4 : bv 32 := 0x00e67633.
Lemma F_54aa4 : fetch_word BSEGS_I (0x54aa4 : word) = Some W_54aa4.
Proof. vm_refl. Qed.
Lemma D_54aa4 : decode_any W_54aa4 = Some (Op ALU_AND 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54aa8 : bv 32 := 0x0304b703.
Lemma F_54aa8 : fetch_word BSEGS_I (0x54aa8 : word) = Some W_54aa8.
Proof. vm_refl. Qed.
Lemma D_54aa8 : decode_any W_54aa8 = Some (Load SZ8 true 14 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54aac : bv 32 := 0x1018081b.
Lemma F_54aac : fetch_word BSEGS_I (0x54aac : word) = Some W_54aac.
Proof. vm_refl. Qed.
Lemma D_54aac : decode_any W_54aac = Some (OpImm32 16 16 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ab0 : bv 32 := 0x00c585b3.
Lemma F_54ab0 : fetch_word BSEGS_I (0x54ab0 : word) = Some W_54ab0.
Proof. vm_refl. Qed.
Lemma D_54ab0 : decode_any W_54ab0 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ab4 : bv 32 := 0x0045d613.
Lemma F_54ab4 : fetch_word BSEGS_I (0x54ab4 : word) = Some W_54ab4.
Proof. vm_refl. Qed.
Lemma D_54ab4 : decode_any W_54ab4 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ab8 : bv 32 := 0x00c585b3.
Lemma F_54ab8 : fetch_word BSEGS_I (0x54ab8 : word) = Some W_54ab8.
Proof. vm_refl. Qed.
Lemma D_54ab8 : decode_any W_54ab8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54abc : bv 32 := 0x02081613.
Lemma F_54abc : fetch_word BSEGS_I (0x54abc : word) = Some W_54abc.
Proof. vm_refl. Qed.
Lemma D_54abc : decode_any W_54abc = Some (ShiftImm ALU_SLL 12 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ac0 : bv 32 := 0x00f5f5b3.
Lemma F_54ac0 : fetch_word BSEGS_I (0x54ac0 : word) = Some W_54ac0.
Proof. vm_refl. Qed.
Lemma D_54ac0 : decode_any W_54ac0 = Some (Op ALU_AND 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ac4 : bv 32 := 0x00c80633.
Lemma F_54ac4 : fetch_word BSEGS_I (0x54ac4 : word) = Some W_54ac4.
Proof. vm_refl. Qed.
Lemma D_54ac4 : decode_any W_54ac4 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ac8 : bv 32 := 0x02c585b3.
Lemma F_54ac8 : fetch_word BSEGS_I (0x54ac8 : word) = Some W_54ac8.
Proof. vm_refl. Qed.
Lemma D_54ac8 : decode_any W_54ac8 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54acc : bv 32 := 0x0385d993.
Lemma F_54acc : fetch_word BSEGS_I (0x54acc : word) = Some W_54acc.
Proof. vm_refl. Qed.
Lemma D_54acc : decode_any W_54acc = Some (ShiftImm ALU_SRL 19 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ad0 : bv 32 := 0x1ce68c63.
Lemma F_54ad0 : fetch_word BSEGS_I (0x54ad0 : word) = Some W_54ad0.
Proof. vm_refl. Qed.
Lemma D_54ad0 : decode_any W_54ad0 = Some (Branch BC_EQ 13 14 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ad4 : bv 32 := 0x0084b603.
Lemma F_54ad4 : fetch_word BSEGS_I (0x54ad4 : word) = Some W_54ad4.
Proof. vm_refl. Qed.
Lemma D_54ad4 : decode_any W_54ad4 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ad8 : bv 32 := 0x03f9c593.
Lemma F_54ad8 : fetch_word BSEGS_I (0x54ad8 : word) = Some W_54ad8.
Proof. vm_refl. Qed.
Lemma D_54ad8 : decode_any W_54ad8 = Some (OpImm ALU_XOR 11 19 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54adc : bv 32 := 0x00dabc23.
Lemma F_54adc : fetch_word BSEGS_I (0x54adc : word) = Some W_54adc.
Proof. vm_refl. Qed.
Lemma D_54adc : decode_any W_54adc = Some (Store SZ8 21 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ae0 : bv 32 := 0x00369713.
Lemma F_54ae0 : fetch_word BSEGS_I (0x54ae0 : word) = Some W_54ae0.
Proof. vm_refl. Qed.
Lemma D_54ae0 : decode_any W_54ae0 = Some (ShiftImm ALU_SLL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ae4 : bv 32 := 0x00e60633.
Lemma F_54ae4 : fetch_word BSEGS_I (0x54ae4 : word) = Some W_54ae4.
Proof. vm_refl. Qed.
Lemma D_54ae4 : decode_any W_54ae4 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54ae8 : bv 32 := 0x01563023.
Lemma F_54ae8 : fetch_word BSEGS_I (0x54ae8 : word) = Some W_54ae8.
Proof. vm_refl. Qed.
Lemma D_54ae8 : decode_any W_54ae8 = Some (Store SZ8 12 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54aec : bv 32 := 0x0484b703.
Lemma F_54aec : fetch_word BSEGS_I (0x54aec : word) = Some W_54aec.
Proof. vm_refl. Qed.
Lemma D_54aec : decode_any W_54aec = Some (Load SZ8 true 14 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54af0 : bv 32 := 0x0584b783.
Lemma F_54af0 : fetch_word BSEGS_I (0x54af0 : word) = Some W_54af0.
Proof. vm_refl. Qed.
Lemma D_54af0 : decode_any W_54af0 = Some (Load SZ8 true 15 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54af4 : bv 32 := 0x00168813.
Lemma F_54af4 : fetch_word BSEGS_I (0x54af4 : word) = Some W_54af4.
Proof. vm_refl. Qed.
Lemma D_54af4 : decode_any W_54af4 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54af8 : bv 32 := 0x0604b603.
Lemma F_54af8 : fetch_word BSEGS_I (0x54af8 : word) = Some W_54af8.
Proof. vm_refl. Qed.
Lemma D_54af8 : decode_any W_54af8 = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54afc : bv 32 := 0x00170713.
Lemma F_54afc : fetch_word BSEGS_I (0x54afc : word) = Some W_54afc.
Proof. vm_refl. Qed.
Lemma D_54afc : decode_any W_54afc = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b00 : bv 32 := 0x012786b3.
Lemma F_54b00 : fetch_word BSEGS_I (0x54b00 : word) = Some W_54b00.
Proof. vm_refl. Qed.
Lemma D_54b00 : decode_any W_54b00 = Some (Op ALU_ADD 13 15 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b04 : bv 32 := 0x0304bc23.
Lemma F_54b04 : fetch_word BSEGS_I (0x54b04 : word) = Some W_54b04.
Proof. vm_refl. Qed.
Lemma D_54b04 : decode_any W_54b04 = Some (Store SZ8 9 16 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b08 : bv 32 := 0x04048023.
Lemma F_54b08 : fetch_word BSEGS_I (0x54b08 : word) = Some W_54b08.
Proof. vm_refl. Qed.
Lemma D_54b08 : decode_any W_54b08 = Some (Store SZ1 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b0c : bv 32 := 0x04e4b423.
Lemma F_54b0c : fetch_word BSEGS_I (0x54b0c : word) = Some W_54b0c.
Proof. vm_refl. Qed.
Lemma D_54b0c : decode_any W_54b0c = Some (Store SZ8 9 14 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b10 : bv 32 := 0x04d4bc23.
Lemma F_54b10 : fetch_word BSEGS_I (0x54b10 : word) = Some W_54b10.
Proof. vm_refl. Qed.
Lemma D_54b10 : decode_any W_54b10 = Some (Store SZ8 9 13 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b14 : bv 32 := 0x00c6e463.
Lemma F_54b14 : fetch_word BSEGS_I (0x54b14 : word) = Some W_54b14.
Proof. vm_refl. Qed.
Lemma D_54b14 : decode_any W_54b14 = Some (Branch BC_LTU 13 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b18 : bv 32 := 0x00068613.
Lemma F_54b18 : fetch_word BSEGS_I (0x54b18 : word) = Some W_54b18.
Proof. vm_refl. Qed.
Lemma D_54b18 : decode_any W_54b18 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b1c : bv 32 := 0x00359593.
Lemma F_54b1c : fetch_word BSEGS_I (0x54b1c : word) = Some W_54b1c.
Proof. vm_refl. Qed.
Lemma D_54b1c : decode_any W_54b1c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b20 : bv 32 := 0x00b485b3.
Lemma F_54b20 : fetch_word BSEGS_I (0x54b20 : word) = Some W_54b20.
Proof. vm_refl. Qed.
Lemma D_54b20 : decode_any W_54b20 = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b24 : bv 32 := 0x0685b683.
Lemma F_54b24 : fetch_word BSEGS_I (0x54b24 : word) = Some W_54b24.
Proof. vm_refl. Qed.
Lemma D_54b24 : decode_any W_54b24 = Some (Load SZ8 true 13 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b28 : bv 32 := 0x00168693.
Lemma F_54b28 : fetch_word BSEGS_I (0x54b28 : word) = Some W_54b28.
Proof. vm_refl. Qed.
Lemma D_54b28 : decode_any W_54b28 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b2c : bv 32 := 0x06c4b023.
Lemma F_54b2c : fetch_word BSEGS_I (0x54b2c : word) = Some W_54b2c.
Proof. vm_refl. Qed.
Lemma D_54b2c : decode_any W_54b2c = Some (Store SZ8 9 12 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b30 : bv 32 := 0x06d5b423.
Lemma F_54b30 : fetch_word BSEGS_I (0x54b30 : word) = Some W_54b30.
Proof. vm_refl. Qed.
Lemma D_54b30 : decode_any W_54b30 = Some (Store SZ8 11 13 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54b34 : bv 32 := 0x01040593.
Lemma F_54b34 : fetch_word BSEGS_I (0x54b34 : word) = Some W_54b34.
Proof. vm_refl. Qed.
Lemma D_54b34 : decode_any W_54b34 = Some (OpImm ALU_ADD 11 8 16, 4%Z).
Proof. vm_refl. Qed.
