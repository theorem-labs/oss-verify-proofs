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
Definition W_62cc8 : bv 32 := 0xfff4c593.
Lemma F_62cc8 : fetch_word BSEGS_I (0x62cc8 : word) = Some W_62cc8.
Proof. vm_refl. Qed.
Lemma D_62cc8 : decode_any W_62cc8 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ccc : bv 32 := 0x80040a13.
Lemma F_62ccc : fetch_word BSEGS_I (0x62ccc : word) = Some W_62ccc.
Proof. vm_refl. Qed.
Lemma D_62ccc : decode_any W_62ccc = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62cd0 : bv 32 := 0xfb8a0a13.
Lemma F_62cd0 : fetch_word BSEGS_I (0x62cd0 : word) = Some W_62cd0.
Proof. vm_refl. Qed.
Lemma D_62cd0 : decode_any W_62cd0 = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62cd4 : bv 32 := 0x06a5e863.
Lemma F_62cd4 : fetch_word BSEGS_I (0x62cd4 : word) = Some W_62cd4.
Proof. vm_refl. Qed.
Lemma D_62cd4 : decode_any W_62cd4 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62cd8 : bv 32 := 0xfbf50593.
Lemma F_62cd8 : fetch_word BSEGS_I (0x62cd8 : word) = Some W_62cd8.
Proof. vm_refl. Qed.
Lemma D_62cd8 : decode_any W_62cd8 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62cdc : bv 32 := 0xfc000613.
Lemma F_62cdc : fetch_word BSEGS_I (0x62cdc : word) = Some W_62cdc.
Proof. vm_refl. Qed.
Lemma D_62cdc : decode_any W_62cdc = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ce0 : bv 32 := 0x0cc5ee63.
Lemma F_62ce0 : fetch_word BSEGS_I (0x62ce0 : word) = Some W_62ce0.
Proof. vm_refl. Qed.
Lemma D_62ce0 : decode_any W_62ce0 = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ce4 : bv 32 := 0x000c7597.
Lemma F_62ce4 : fetch_word BSEGS_I (0x62ce4 : word) = Some W_62ce4.
Proof. vm_refl. Qed.
Lemma D_62ce4 : decode_any W_62ce4 = Some (Auipc 11 199, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ce8 : bv 32 := 0x69c5b583.
Lemma F_62ce8 : fetch_word BSEGS_I (0x62ce8 : word) = Some W_62ce8.
Proof. vm_refl. Qed.
Lemma D_62ce8 : decode_any W_62ce8 = Some (Load SZ8 true 11 11 1692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62cec : bv 32 := 0x00a486b3.
Lemma F_62cec : fetch_word BSEGS_I (0x62cec : word) = Some W_62cec.
Proof. vm_refl. Qed.
Lemma D_62cec : decode_any W_62cec = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62cf0 : bv 32 := 0x0005b603.
Lemma F_62cf0 : fetch_word BSEGS_I (0x62cf0 : word) = Some W_62cf0.
Proof. vm_refl. Qed.
Lemma D_62cf0 : decode_any W_62cf0 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62cf4 : bv 32 := 0x0034d593.
Lemma F_62cf4 : fetch_word BSEGS_I (0x62cf4 : word) = Some W_62cf4.
Proof. vm_refl. Qed.
Lemma D_62cf4 : decode_any W_62cf4 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62cf8 : bv 32 := 0xfff68693.
Lemma F_62cf8 : fetch_word BSEGS_I (0x62cf8 : word) = Some W_62cf8.
Proof. vm_refl. Qed.
Lemma D_62cf8 : decode_any W_62cf8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62cfc : bv 32 := 0x0036d713.
Lemma F_62cfc : fetch_word BSEGS_I (0x62cfc : word) = Some W_62cfc.
Proof. vm_refl. Qed.
Lemma D_62cfc : decode_any W_62cfc = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62d00 : bv 32 := 0x00b605b3.
Lemma F_62d00 : fetch_word BSEGS_I (0x62d00 : word) = Some W_62d00.
Proof. vm_refl. Qed.
Lemma D_62d00 : decode_any W_62d00 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62d04 : bv 32 := 0x00e60633.
Lemma F_62d04 : fetch_word BSEGS_I (0x62d04 : word) = Some W_62d04.
Proof. vm_refl. Qed.
Lemma D_62d04 : decode_any W_62d04 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62d08 : bv 32 := 0xff85f713.
Lemma F_62d08 : fetch_word BSEGS_I (0x62d08 : word) = Some W_62d08.
Proof. vm_refl. Qed.
Lemma D_62d08 : decode_any W_62d08 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62d0c : bv 32 := 0xff867793.
Lemma F_62d0c : fetch_word BSEGS_I (0x62d0c : word) = Some W_62d0c.
Proof. vm_refl. Qed.
Lemma D_62d0c : decode_any W_62d0c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62d10 : bv 32 := 0x00073703.
Lemma F_62d10 : fetch_word BSEGS_I (0x62d10 : word) = Some W_62d10.
Proof. vm_refl. Qed.
Lemma D_62d10 : decode_any W_62d10 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62d14 : bv 32 := 0x0007b783.
Lemma F_62d14 : fetch_word BSEGS_I (0x62d14 : word) = Some W_62d14.
Proof. vm_refl. Qed.
Lemma D_62d14 : decode_any W_62d14 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62d18 : bv 32 := 0x00e7e733.
Lemma F_62d18 : fetch_word BSEGS_I (0x62d18 : word) = Some W_62d18.
Proof. vm_refl. Qed.
Lemma D_62d18 : decode_any W_62d18 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62d1c : bv 32 := 0x14071663.
Lemma F_62d1c : fetch_word BSEGS_I (0x62d1c : word) = Some W_62d1c.
Proof. vm_refl. Qed.
Lemma D_62d1c : decode_any W_62d1c = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62d20 : bv 32 := 0x06010113.
Lemma F_62d20 : fetch_word BSEGS_I (0x62d20 : word) = Some W_62d20.
Proof. vm_refl. Qed.
Lemma D_62d20 : decode_any W_62d20 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.
