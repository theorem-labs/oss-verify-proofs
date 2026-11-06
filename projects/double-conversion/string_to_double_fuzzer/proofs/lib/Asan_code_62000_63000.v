(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS_I := ImgA.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_62b84 : bv 32 := 0xfff4c593.
Lemma F_62b84 : fetch_word ASEGS_I (0x62b84 : word) = Some W_62b84.
Proof. vm_refl. Qed.
Lemma D_62b84 : decode_any W_62b84 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b88 : bv 32 := 0x80040a13.
Lemma F_62b88 : fetch_word ASEGS_I (0x62b88 : word) = Some W_62b88.
Proof. vm_refl. Qed.
Lemma D_62b88 : decode_any W_62b88 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b8c : bv 32 := 0xfb8a0a13.
Lemma F_62b8c : fetch_word ASEGS_I (0x62b8c : word) = Some W_62b8c.
Proof. vm_refl. Qed.
Lemma D_62b8c : decode_any W_62b8c = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b90 : bv 32 := 0x06a5e863.
Lemma F_62b90 : fetch_word ASEGS_I (0x62b90 : word) = Some W_62b90.
Proof. vm_refl. Qed.
Lemma D_62b90 : decode_any W_62b90 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b94 : bv 32 := 0xfbf50593.
Lemma F_62b94 : fetch_word ASEGS_I (0x62b94 : word) = Some W_62b94.
Proof. vm_refl. Qed.
Lemma D_62b94 : decode_any W_62b94 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b98 : bv 32 := 0xfc000613.
Lemma F_62b98 : fetch_word ASEGS_I (0x62b98 : word) = Some W_62b98.
Proof. vm_refl. Qed.
Lemma D_62b98 : decode_any W_62b98 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b9c : bv 32 := 0x0cc5ee63.
Lemma F_62b9c : fetch_word ASEGS_I (0x62b9c : word) = Some W_62b9c.
Proof. vm_refl. Qed.
Lemma D_62b9c : decode_any W_62b9c = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ba0 : bv 32 := 0x000c7597.
Lemma F_62ba0 : fetch_word ASEGS_I (0x62ba0 : word) = Some W_62ba0.
Proof. vm_refl. Qed.
Lemma D_62ba0 : decode_any W_62ba0 = Some (Auipc 11 199, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ba4 : bv 32 := 0x3085b583.
Lemma F_62ba4 : fetch_word ASEGS_I (0x62ba4 : word) = Some W_62ba4.
Proof. vm_refl. Qed.
Lemma D_62ba4 : decode_any W_62ba4 = Some (Load SZ8 true 11 11 776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ba8 : bv 32 := 0x00a486b3.
Lemma F_62ba8 : fetch_word ASEGS_I (0x62ba8 : word) = Some W_62ba8.
Proof. vm_refl. Qed.
Lemma D_62ba8 : decode_any W_62ba8 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bac : bv 32 := 0x0005b603.
Lemma F_62bac : fetch_word ASEGS_I (0x62bac : word) = Some W_62bac.
Proof. vm_refl. Qed.
Lemma D_62bac : decode_any W_62bac = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bb0 : bv 32 := 0x0034d593.
Lemma F_62bb0 : fetch_word ASEGS_I (0x62bb0 : word) = Some W_62bb0.
Proof. vm_refl. Qed.
Lemma D_62bb0 : decode_any W_62bb0 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bb4 : bv 32 := 0xfff68693.
Lemma F_62bb4 : fetch_word ASEGS_I (0x62bb4 : word) = Some W_62bb4.
Proof. vm_refl. Qed.
Lemma D_62bb4 : decode_any W_62bb4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bb8 : bv 32 := 0x0036d713.
Lemma F_62bb8 : fetch_word ASEGS_I (0x62bb8 : word) = Some W_62bb8.
Proof. vm_refl. Qed.
Lemma D_62bb8 : decode_any W_62bb8 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bbc : bv 32 := 0x00b605b3.
Lemma F_62bbc : fetch_word ASEGS_I (0x62bbc : word) = Some W_62bbc.
Proof. vm_refl. Qed.
Lemma D_62bbc : decode_any W_62bbc = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bc0 : bv 32 := 0x00e60633.
Lemma F_62bc0 : fetch_word ASEGS_I (0x62bc0 : word) = Some W_62bc0.
Proof. vm_refl. Qed.
Lemma D_62bc0 : decode_any W_62bc0 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bc4 : bv 32 := 0xff85f713.
Lemma F_62bc4 : fetch_word ASEGS_I (0x62bc4 : word) = Some W_62bc4.
Proof. vm_refl. Qed.
Lemma D_62bc4 : decode_any W_62bc4 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bc8 : bv 32 := 0xff867793.
Lemma F_62bc8 : fetch_word ASEGS_I (0x62bc8 : word) = Some W_62bc8.
Proof. vm_refl. Qed.
Lemma D_62bc8 : decode_any W_62bc8 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bcc : bv 32 := 0x00073703.
Lemma F_62bcc : fetch_word ASEGS_I (0x62bcc : word) = Some W_62bcc.
Proof. vm_refl. Qed.
Lemma D_62bcc : decode_any W_62bcc = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bd0 : bv 32 := 0x0007b783.
Lemma F_62bd0 : fetch_word ASEGS_I (0x62bd0 : word) = Some W_62bd0.
Proof. vm_refl. Qed.
Lemma D_62bd0 : decode_any W_62bd0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bd4 : bv 32 := 0x00e7e733.
Lemma F_62bd4 : fetch_word ASEGS_I (0x62bd4 : word) = Some W_62bd4.
Proof. vm_refl. Qed.
Lemma D_62bd4 : decode_any W_62bd4 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bd8 : bv 32 := 0x14071663.
Lemma F_62bd8 : fetch_word ASEGS_I (0x62bd8 : word) = Some W_62bd8.
Proof. vm_refl. Qed.
Lemma D_62bd8 : decode_any W_62bd8 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62bdc : bv 32 := 0x06010113.
Lemma F_62bdc : fetch_word ASEGS_I (0x62bdc : word) = Some W_62bdc.
Proof. vm_refl. Qed.
Lemma D_62bdc : decode_any W_62bdc = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.
