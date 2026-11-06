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
Definition W_87b10 : bv 32 := 0x02060063.
Lemma F_87b10 : fetch_word BSEGS_I (0x87b10 : word) = Some W_87b10.
Proof. vm_refl. Qed.
Lemma D_87b10 : decode_any W_87b10 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b14 : bv 32 := 0x00c50633.
Lemma F_87b14 : fetch_word BSEGS_I (0x87b14 : word) = Some W_87b14.
Proof. vm_refl. Qed.
Lemma D_87b14 : decode_any W_87b14 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b18 : bv 32 := 0x00050693.
Lemma F_87b18 : fetch_word BSEGS_I (0x87b18 : word) = Some W_87b18.
Proof. vm_refl. Qed.
Lemma D_87b18 : decode_any W_87b18 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b1c : bv 32 := 0x0005c703.
Lemma F_87b1c : fetch_word BSEGS_I (0x87b1c : word) = Some W_87b1c.
Proof. vm_refl. Qed.
Lemma D_87b1c : decode_any W_87b1c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b20 : bv 32 := 0x00e68023.
Lemma F_87b20 : fetch_word BSEGS_I (0x87b20 : word) = Some W_87b20.
Proof. vm_refl. Qed.
Lemma D_87b20 : decode_any W_87b20 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b24 : bv 32 := 0x00168693.
Lemma F_87b24 : fetch_word BSEGS_I (0x87b24 : word) = Some W_87b24.
Proof. vm_refl. Qed.
Lemma D_87b24 : decode_any W_87b24 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b28 : bv 32 := 0x00158593.
Lemma F_87b28 : fetch_word BSEGS_I (0x87b28 : word) = Some W_87b28.
Proof. vm_refl. Qed.
Lemma D_87b28 : decode_any W_87b28 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b2c : bv 32 := 0xfec698e3.
Lemma F_87b2c : fetch_word BSEGS_I (0x87b2c : word) = Some W_87b2c.
Proof. vm_refl. Qed.
Lemma D_87b2c : decode_any W_87b2c = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b30 : bv 32 := 0x00008067.
Lemma F_87b30 : fetch_word BSEGS_I (0x87b30 : word) = Some W_87b30.
Proof. vm_refl. Qed.
Lemma D_87b30 : decode_any W_87b30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b8c : bv 32 := 0x00a666b3.
Lemma F_87b8c : fetch_word BSEGS_I (0x87b8c : word) = Some W_87b8c.
Proof. vm_refl. Qed.
Lemma D_87b8c : decode_any W_87b8c = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b90 : bv 32 := 0x00f6f693.
Lemma F_87b90 : fetch_word BSEGS_I (0x87b90 : word) = Some W_87b90.
Proof. vm_refl. Qed.
Lemma D_87b90 : decode_any W_87b90 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b94 : bv 32 := 0x02068063.
Lemma F_87b94 : fetch_word BSEGS_I (0x87b94 : word) = Some W_87b94.
Proof. vm_refl. Qed.
Lemma D_87b94 : decode_any W_87b94 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b98 : bv 32 := 0x04060863.
Lemma F_87b98 : fetch_word BSEGS_I (0x87b98 : word) = Some W_87b98.
Proof. vm_refl. Qed.
Lemma D_87b98 : decode_any W_87b98 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b9c : bv 32 := 0x00c50633.
Lemma F_87b9c : fetch_word BSEGS_I (0x87b9c : word) = Some W_87b9c.
Proof. vm_refl. Qed.
Lemma D_87b9c : decode_any W_87b9c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ba0 : bv 32 := 0x00050693.
Lemma F_87ba0 : fetch_word BSEGS_I (0x87ba0 : word) = Some W_87ba0.
Proof. vm_refl. Qed.
Lemma D_87ba0 : decode_any W_87ba0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ba4 : bv 32 := 0x00b68023.
Lemma F_87ba4 : fetch_word BSEGS_I (0x87ba4 : word) = Some W_87ba4.
Proof. vm_refl. Qed.
Lemma D_87ba4 : decode_any W_87ba4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ba8 : bv 32 := 0x00168693.
Lemma F_87ba8 : fetch_word BSEGS_I (0x87ba8 : word) = Some W_87ba8.
Proof. vm_refl. Qed.
Lemma D_87ba8 : decode_any W_87ba8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bac : bv 32 := 0xfec69ce3.
Lemma F_87bac : fetch_word BSEGS_I (0x87bac : word) = Some W_87bac.
Proof. vm_refl. Qed.
Lemma D_87bac : decode_any W_87bac = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bb0 : bv 32 := 0x0380006f.
Lemma F_87bb0 : fetch_word BSEGS_I (0x87bb0 : word) = Some W_87bb0.
Proof. vm_refl. Qed.
Lemma D_87bb0 : decode_any W_87bb0 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bb4 : bv 32 := 0x02060a63.
Lemma F_87bb4 : fetch_word BSEGS_I (0x87bb4 : word) = Some W_87bb4.
Proof. vm_refl. Qed.
Lemma D_87bb4 : decode_any W_87bb4 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bb8 : bv 32 := 0x00c50633.
Lemma F_87bb8 : fetch_word BSEGS_I (0x87bb8 : word) = Some W_87bb8.
Proof. vm_refl. Qed.
Lemma D_87bb8 : decode_any W_87bb8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bbc : bv 32 := 0x00859693.
Lemma F_87bbc : fetch_word BSEGS_I (0x87bbc : word) = Some W_87bbc.
Proof. vm_refl. Qed.
Lemma D_87bbc : decode_any W_87bbc = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bc0 : bv 32 := 0x00b6e5b3.
Lemma F_87bc0 : fetch_word BSEGS_I (0x87bc0 : word) = Some W_87bc0.
Proof. vm_refl. Qed.
Lemma D_87bc0 : decode_any W_87bc0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bc4 : bv 32 := 0x01059693.
Lemma F_87bc4 : fetch_word BSEGS_I (0x87bc4 : word) = Some W_87bc4.
Proof. vm_refl. Qed.
Lemma D_87bc4 : decode_any W_87bc4 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bc8 : bv 32 := 0x00b6e5b3.
Lemma F_87bc8 : fetch_word BSEGS_I (0x87bc8 : word) = Some W_87bc8.
Proof. vm_refl. Qed.
Lemma D_87bc8 : decode_any W_87bc8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bcc : bv 32 := 0x02059693.
Lemma F_87bcc : fetch_word BSEGS_I (0x87bcc : word) = Some W_87bcc.
Proof. vm_refl. Qed.
Lemma D_87bcc : decode_any W_87bcc = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bd0 : bv 32 := 0x00b6e5b3.
Lemma F_87bd0 : fetch_word BSEGS_I (0x87bd0 : word) = Some W_87bd0.
Proof. vm_refl. Qed.
Lemma D_87bd0 : decode_any W_87bd0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bd4 : bv 32 := 0x00050693.
Lemma F_87bd4 : fetch_word BSEGS_I (0x87bd4 : word) = Some W_87bd4.
Proof. vm_refl. Qed.
Lemma D_87bd4 : decode_any W_87bd4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bd8 : bv 32 := 0x00b6b023.
Lemma F_87bd8 : fetch_word BSEGS_I (0x87bd8 : word) = Some W_87bd8.
Proof. vm_refl. Qed.
Lemma D_87bd8 : decode_any W_87bd8 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bdc : bv 32 := 0x00b6b423.
Lemma F_87bdc : fetch_word BSEGS_I (0x87bdc : word) = Some W_87bdc.
Proof. vm_refl. Qed.
Lemma D_87bdc : decode_any W_87bdc = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87be0 : bv 32 := 0x01068693.
Lemma F_87be0 : fetch_word BSEGS_I (0x87be0 : word) = Some W_87be0.
Proof. vm_refl. Qed.
Lemma D_87be0 : decode_any W_87be0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87be4 : bv 32 := 0xfec6eae3.
Lemma F_87be4 : fetch_word BSEGS_I (0x87be4 : word) = Some W_87be4.
Proof. vm_refl. Qed.
Lemma D_87be4 : decode_any W_87be4 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87be8 : bv 32 := 0x00008067.
Lemma F_87be8 : fetch_word BSEGS_I (0x87be8 : word) = Some W_87be8.
Proof. vm_refl. Qed.
Lemma D_87be8 : decode_any W_87be8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ce0 : bv 32 := 0x00000593.
Lemma F_87ce0 : fetch_word BSEGS_I (0x87ce0 : word) = Some W_87ce0.
Proof. vm_refl. Qed.
Lemma D_87ce0 : decode_any W_87ce0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ce4 : bv 32 := 0x00b50633.
Lemma F_87ce4 : fetch_word BSEGS_I (0x87ce4 : word) = Some W_87ce4.
Proof. vm_refl. Qed.
Lemma D_87ce4 : decode_any W_87ce4 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ce8 : bv 32 := 0x00064603.
Lemma F_87ce8 : fetch_word BSEGS_I (0x87ce8 : word) = Some W_87ce8.
Proof. vm_refl. Qed.
Lemma D_87ce8 : decode_any W_87ce8 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cec : bv 32 := 0x00158593.
Lemma F_87cec : fetch_word BSEGS_I (0x87cec : word) = Some W_87cec.
Proof. vm_refl. Qed.
Lemma D_87cec : decode_any W_87cec = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cf0 : bv 32 := 0xfe061ae3.
Lemma F_87cf0 : fetch_word BSEGS_I (0x87cf0 : word) = Some W_87cf0.
Proof. vm_refl. Qed.
Lemma D_87cf0 : decode_any W_87cf0 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cf4 : bv 32 := 0xfff58513.
Lemma F_87cf4 : fetch_word BSEGS_I (0x87cf4 : word) = Some W_87cf4.
Proof. vm_refl. Qed.
Lemma D_87cf4 : decode_any W_87cf4 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87cf8 : bv 32 := 0x00008067.
Lemma F_87cf8 : fetch_word BSEGS_I (0x87cf8 : word) = Some W_87cf8.
Proof. vm_refl. Qed.
Lemma D_87cf8 : decode_any W_87cf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fb8 : bv 32 := 0x06060663.
Lemma F_87fb8 : fetch_word BSEGS_I (0x87fb8 : word) = Some W_87fb8.
Proof. vm_refl. Qed.
Lemma D_87fb8 : decode_any W_87fb8 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fbc : bv 32 := 0x00000693.
Lemma F_87fbc : fetch_word BSEGS_I (0x87fbc : word) = Some W_87fbc.
Proof. vm_refl. Qed.
Lemma D_87fbc : decode_any W_87fbc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fc0 : bv 32 := 0x00d58733.
Lemma F_87fc0 : fetch_word BSEGS_I (0x87fc0 : word) = Some W_87fc0.
Proof. vm_refl. Qed.
Lemma D_87fc0 : decode_any W_87fc0 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fc4 : bv 32 := 0x00074703.
Lemma F_87fc4 : fetch_word BSEGS_I (0x87fc4 : word) = Some W_87fc4.
Proof. vm_refl. Qed.
Lemma D_87fc4 : decode_any W_87fc4 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fc8 : bv 32 := 0x00070c63.
Lemma F_87fc8 : fetch_word BSEGS_I (0x87fc8 : word) = Some W_87fc8.
Proof. vm_refl. Qed.
Lemma D_87fc8 : decode_any W_87fc8 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fcc : bv 32 := 0x00d507b3.
Lemma F_87fcc : fetch_word BSEGS_I (0x87fcc : word) = Some W_87fcc.
Proof. vm_refl. Qed.
Lemma D_87fcc : decode_any W_87fcc = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fd0 : bv 32 := 0x00168693.
Lemma F_87fd0 : fetch_word BSEGS_I (0x87fd0 : word) = Some W_87fd0.
Proof. vm_refl. Qed.
Lemma D_87fd0 : decode_any W_87fd0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fd4 : bv 32 := 0x00e78023.
Lemma F_87fd4 : fetch_word BSEGS_I (0x87fd4 : word) = Some W_87fd4.
Proof. vm_refl. Qed.
Lemma D_87fd4 : decode_any W_87fd4 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fd8 : bv 32 := 0xfed614e3.
Lemma F_87fd8 : fetch_word BSEGS_I (0x87fd8 : word) = Some W_87fd8.
Proof. vm_refl. Qed.
Lemma D_87fd8 : decode_any W_87fd8 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fdc : bv 32 := 0x00060693.
Lemma F_87fdc : fetch_word BSEGS_I (0x87fdc : word) = Some W_87fdc.
Proof. vm_refl. Qed.
Lemma D_87fdc : decode_any W_87fdc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe0 : bv 32 := 0x00d505b3.
Lemma F_87fe0 : fetch_word BSEGS_I (0x87fe0 : word) = Some W_87fe0.
Proof. vm_refl. Qed.
Lemma D_87fe0 : decode_any W_87fe0 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe4 : bv 32 := 0x40d6073b.
Lemma F_87fe4 : fetch_word BSEGS_I (0x87fe4 : word) = Some W_87fe4.
Proof. vm_refl. Qed.
Lemma D_87fe4 : decode_any W_87fe4 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe8 : bv 32 := 0x00b76733.
Lemma F_87fe8 : fetch_word BSEGS_I (0x87fe8 : word) = Some W_87fe8.
Proof. vm_refl. Qed.
Lemma D_87fe8 : decode_any W_87fe8 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fec : bv 32 := 0x00f77713.
Lemma F_87fec : fetch_word BSEGS_I (0x87fec : word) = Some W_87fec.
Proof. vm_refl. Qed.
Lemma D_87fec : decode_any W_87fec = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ff0 : bv 32 := 0x00070e63.
Lemma F_87ff0 : fetch_word BSEGS_I (0x87ff0 : word) = Some W_87ff0.
Proof. vm_refl. Qed.
Lemma D_87ff0 : decode_any W_87ff0 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ff4 : bv 32 := 0x02d60863.
Lemma F_87ff4 : fetch_word BSEGS_I (0x87ff4 : word) = Some W_87ff4.
Proof. vm_refl. Qed.
Lemma D_87ff4 : decode_any W_87ff4 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ff8 : bv 32 := 0x00c50633.
Lemma F_87ff8 : fetch_word BSEGS_I (0x87ff8 : word) = Some W_87ff8.
Proof. vm_refl. Qed.
Lemma D_87ff8 : decode_any W_87ff8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ffc : bv 32 := 0x00058023.
Lemma F_87ffc : fetch_word BSEGS_I (0x87ffc : word) = Some W_87ffc.
Proof. vm_refl. Qed.
Lemma D_87ffc : decode_any W_87ffc = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88000 : bv 32 := 0x00158593.
Lemma F_88000 : fetch_word BSEGS_I (0x88000 : word) = Some W_88000.
Proof. vm_refl. Qed.
Lemma D_88000 : decode_any W_88000 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88004 : bv 32 := 0xfec59ce3.
Lemma F_88004 : fetch_word BSEGS_I (0x88004 : word) = Some W_88004.
Proof. vm_refl. Qed.
Lemma D_88004 : decode_any W_88004 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88008 : bv 32 := 0x01c0006f.
Lemma F_88008 : fetch_word BSEGS_I (0x88008 : word) = Some W_88008.
Proof. vm_refl. Qed.
Lemma D_88008 : decode_any W_88008 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8800c : bv 32 := 0x00d60c63.
Lemma F_8800c : fetch_word BSEGS_I (0x8800c : word) = Some W_8800c.
Proof. vm_refl. Qed.
Lemma D_8800c : decode_any W_8800c = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88010 : bv 32 := 0x00c50633.
Lemma F_88010 : fetch_word BSEGS_I (0x88010 : word) = Some W_88010.
Proof. vm_refl. Qed.
Lemma D_88010 : decode_any W_88010 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88014 : bv 32 := 0x0005b023.
Lemma F_88014 : fetch_word BSEGS_I (0x88014 : word) = Some W_88014.
Proof. vm_refl. Qed.
Lemma D_88014 : decode_any W_88014 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88018 : bv 32 := 0x0005b423.
Lemma F_88018 : fetch_word BSEGS_I (0x88018 : word) = Some W_88018.
Proof. vm_refl. Qed.
Lemma D_88018 : decode_any W_88018 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8801c : bv 32 := 0x01058593.
Lemma F_8801c : fetch_word BSEGS_I (0x8801c : word) = Some W_8801c.
Proof. vm_refl. Qed.
Lemma D_8801c : decode_any W_8801c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88020 : bv 32 := 0xfec5eae3.
Lemma F_88020 : fetch_word BSEGS_I (0x88020 : word) = Some W_88020.
Proof. vm_refl. Qed.
Lemma D_88020 : decode_any W_88020 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88024 : bv 32 := 0x00008067.
Lemma F_88024 : fetch_word BSEGS_I (0x88024 : word) = Some W_88024.
Proof. vm_refl. Qed.
Lemma D_88024 : decode_any W_88024 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_880d8 : bv 32 := 0xff010113.
Lemma F_880d8 : fetch_word BSEGS_I (0x880d8 : word) = Some W_880d8.
Proof. vm_refl. Qed.
Lemma D_880d8 : decode_any W_880d8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_880dc : bv 32 := 0x00113423.
Lemma F_880dc : fetch_word BSEGS_I (0x880dc : word) = Some W_880dc.
Proof. vm_refl. Qed.
Lemma D_880dc : decode_any W_880dc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_880e0 : bv 32 := 0x00058693.
Lemma F_880e0 : fetch_word BSEGS_I (0x880e0 : word) = Some W_880e0.
Proof. vm_refl. Qed.
Lemma D_880e0 : decode_any W_880e0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_880e4 : bv 32 := 0x00100713.
Lemma F_880e4 : fetch_word BSEGS_I (0x880e4 : word) = Some W_880e4.
Proof. vm_refl. Qed.
Lemma D_880e4 : decode_any W_880e4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_880e8 : bv 32 := 0x02871713.
Lemma F_880e8 : fetch_word BSEGS_I (0x880e8 : word) = Some W_880e8.
Proof. vm_refl. Qed.
Lemma D_880e8 : decode_any W_880e8 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_880ec : bv 32 := 0x00170593.
Lemma F_880ec : fetch_word BSEGS_I (0x880ec : word) = Some W_880ec.
Proof. vm_refl. Qed.
Lemma D_880ec : decode_any W_880ec = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_880f0 : bv 32 := 0x08b6f263.
Lemma F_880f0 : fetch_word BSEGS_I (0x880f0 : word) = Some W_880f0.
Proof. vm_refl. Qed.
Lemma D_880f0 : decode_any W_880f0 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_880f4 : bv 32 := 0x00000593.
Lemma F_880f4 : fetch_word BSEGS_I (0x880f4 : word) = Some W_880f4.
Proof. vm_refl. Qed.
Lemma D_880f4 : decode_any W_880f4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_880f8 : bv 32 := 0x00d50733.
Lemma F_880f8 : fetch_word BSEGS_I (0x880f8 : word) = Some W_880f8.
Proof. vm_refl. Qed.
Lemma D_880f8 : decode_any W_880f8 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_880fc : bv 32 := 0x00750793.
Lemma F_880fc : fetch_word BSEGS_I (0x880fc : word) = Some W_880fc.
Proof. vm_refl. Qed.
Lemma D_880fc : decode_any W_880fc = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88100 : bv 32 := 0xff87f793.
Lemma F_88100 : fetch_word BSEGS_I (0x88100 : word) = Some W_88100.
Proof. vm_refl. Qed.
Lemma D_88100 : decode_any W_88100 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88104 : bv 32 := 0xff877613.
Lemma F_88104 : fetch_word BSEGS_I (0x88104 : word) = Some W_88104.
Proof. vm_refl. Qed.
Lemma D_88104 : decode_any W_88104 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88108 : bv 32 := 0x02f57463.
Lemma F_88108 : fetch_word BSEGS_I (0x88108 : word) = Some W_88108.
Proof. vm_refl. Qed.
Lemma D_88108 : decode_any W_88108 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8810c : bv 32 := 0x02068263.
Lemma F_8810c : fetch_word BSEGS_I (0x8810c : word) = Some W_8810c.
Proof. vm_refl. Qed.
Lemma D_8810c : decode_any W_8810c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88110 : bv 32 := 0x00000593.
Lemma F_88110 : fetch_word BSEGS_I (0x88110 : word) = Some W_88110.
Proof. vm_refl. Qed.
Lemma D_88110 : decode_any W_88110 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88114 : bv 32 := 0x00150693.
Lemma F_88114 : fetch_word BSEGS_I (0x88114 : word) = Some W_88114.
Proof. vm_refl. Qed.
Lemma D_88114 : decode_any W_88114 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88118 : bv 32 := 0x00068813.
Lemma F_88118 : fetch_word BSEGS_I (0x88118 : word) = Some W_88118.
Proof. vm_refl. Qed.
Lemma D_88118 : decode_any W_88118 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8811c : bv 32 := 0xfff6c683.
Lemma F_8811c : fetch_word BSEGS_I (0x8811c : word) = Some W_8811c.
Proof. vm_refl. Qed.
Lemma D_8811c : decode_any W_8811c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88120 : bv 32 := 0x00d5e5b3.
Lemma F_88120 : fetch_word BSEGS_I (0x88120 : word) = Some W_88120.
Proof. vm_refl. Qed.
Lemma D_88120 : decode_any W_88120 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88124 : bv 32 := 0x00f87663.
Lemma F_88124 : fetch_word BSEGS_I (0x88124 : word) = Some W_88124.
Proof. vm_refl. Qed.
Lemma D_88124 : decode_any W_88124 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88128 : bv 32 := 0x00180693.
Lemma F_88128 : fetch_word BSEGS_I (0x88128 : word) = Some W_88128.
Proof. vm_refl. Qed.
Lemma D_88128 : decode_any W_88128 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8812c : bv 32 := 0xfee866e3.
Lemma F_8812c : fetch_word BSEGS_I (0x8812c : word) = Some W_8812c.
Proof. vm_refl. Qed.
Lemma D_8812c : decode_any W_8812c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88130 : bv 32 := 0x00c7fa63.
Lemma F_88130 : fetch_word BSEGS_I (0x88130 : word) = Some W_88130.
Proof. vm_refl. Qed.
Lemma D_88130 : decode_any W_88130 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.
