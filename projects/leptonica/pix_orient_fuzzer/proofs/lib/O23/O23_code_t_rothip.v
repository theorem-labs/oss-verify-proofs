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
Definition W_7caf0 : bv 32 := 0x00e028b3.
Lemma F_7caf0 : fetch_word Plain.M.loaded_segments (0x7cb48 : word) = Some W_7caf0.
Proof. vm_refl. Qed.
Lemma D_7caf0 : decode_any W_7caf0 = Some (Op ALU_SLT 17 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7caf4 : bv 32 := 0x411008b3.
Lemma F_7caf4 : fetch_word Plain.M.loaded_segments (0x7cb4c : word) = Some W_7caf4.
Proof. vm_refl. Qed.
Lemma D_7caf4 : decode_any W_7caf4 = Some (Op ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7caf8 : bv 32 := 0x00e8f8b3.
Lemma F_7caf8 : fetch_word Plain.M.loaded_segments (0x7cb50 : word) = Some W_7caf8.
Proof. vm_refl. Qed.
Lemma D_7caf8 : decode_any W_7caf8 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cafc : bv 32 := 0x3b15c063.
Lemma F_7cafc : fetch_word Plain.M.loaded_segments (0x7cb54 : word) = Some W_7cafc.
Proof. vm_refl. Qed.
Lemma D_7cafc : decode_any W_7cafc = Some (Branch BC_LT 11 17 928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb00 : bv 32 := 0xf2010113.
Lemma F_7cb00 : fetch_word Plain.M.loaded_segments (0x7cb58 : word) = Some W_7cb00.
Proof. vm_refl. Qed.
Lemma D_7cb00 : decode_any W_7cb00 = Some (OpImm ALU_ADD 2 2 3872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb04 : bv 32 := 0x0c113c23.
Lemma F_7cb04 : fetch_word Plain.M.loaded_segments (0x7cb5c : word) = Some W_7cb04.
Proof. vm_refl. Qed.
Lemma D_7cb04 : decode_any W_7cb04 = Some (Store SZ8 2 1 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb08 : bv 32 := 0x0c813823.
Lemma F_7cb08 : fetch_word Plain.M.loaded_segments (0x7cb60 : word) = Some W_7cb08.
Proof. vm_refl. Qed.
Lemma D_7cb08 : decode_any W_7cb08 = Some (Store SZ8 2 8 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb0c : bv 32 := 0x0c913423.
Lemma F_7cb0c : fetch_word Plain.M.loaded_segments (0x7cb64 : word) = Some W_7cb0c.
Proof. vm_refl. Qed.
Lemma D_7cb0c : decode_any W_7cb0c = Some (Store SZ8 2 9 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb10 : bv 32 := 0x0d213023.
Lemma F_7cb10 : fetch_word Plain.M.loaded_segments (0x7cb68 : word) = Some W_7cb10.
Proof. vm_refl. Qed.
Lemma D_7cb10 : decode_any W_7cb10 = Some (Store SZ8 2 18 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb14 : bv 32 := 0x0b313c23.
Lemma F_7cb14 : fetch_word Plain.M.loaded_segments (0x7cb6c : word) = Some W_7cb14.
Proof. vm_refl. Qed.
Lemma D_7cb14 : decode_any W_7cb14 = Some (Store SZ8 2 19 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb18 : bv 32 := 0x0b413823.
Lemma F_7cb18 : fetch_word Plain.M.loaded_segments (0x7cb70 : word) = Some W_7cb18.
Proof. vm_refl. Qed.
Lemma D_7cb18 : decode_any W_7cb18 = Some (Store SZ8 2 20 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb1c : bv 32 := 0x0b513423.
Lemma F_7cb1c : fetch_word Plain.M.loaded_segments (0x7cb74 : word) = Some W_7cb1c.
Proof. vm_refl. Qed.
Lemma D_7cb1c : decode_any W_7cb1c = Some (Store SZ8 2 21 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb20 : bv 32 := 0x0b613023.
Lemma F_7cb20 : fetch_word Plain.M.loaded_segments (0x7cb78 : word) = Some W_7cb20.
Proof. vm_refl. Qed.
Lemma D_7cb20 : decode_any W_7cb20 = Some (Store SZ8 2 22 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb24 : bv 32 := 0x09713c23.
Lemma F_7cb24 : fetch_word Plain.M.loaded_segments (0x7cb7c : word) = Some W_7cb24.
Proof. vm_refl. Qed.
Lemma D_7cb24 : decode_any W_7cb24 = Some (Store SZ8 2 23 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb28 : bv 32 := 0x09813823.
Lemma F_7cb28 : fetch_word Plain.M.loaded_segments (0x7cb80 : word) = Some W_7cb28.
Proof. vm_refl. Qed.
Lemma D_7cb28 : decode_any W_7cb28 = Some (Store SZ8 2 24 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb2c : bv 32 := 0x09913423.
Lemma F_7cb2c : fetch_word Plain.M.loaded_segments (0x7cb84 : word) = Some W_7cb2c.
Proof. vm_refl. Qed.
Lemma D_7cb2c : decode_any W_7cb2c = Some (Store SZ8 2 25 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb30 : bv 32 := 0x09a13023.
Lemma F_7cb30 : fetch_word Plain.M.loaded_segments (0x7cb88 : word) = Some W_7cb30.
Proof. vm_refl. Qed.
Lemma D_7cb30 : decode_any W_7cb30 = Some (Store SZ8 2 26 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb34 : bv 32 := 0x07b13c23.
Lemma F_7cb34 : fetch_word Plain.M.loaded_segments (0x7cb8c : word) = Some W_7cb34.
Proof. vm_refl. Qed.
Lemma D_7cb34 : decode_any W_7cb34 = Some (Store SZ8 2 27 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb38 : bv 32 := 0x00050d13.
Lemma F_7cb38 : fetch_word Plain.M.loaded_segments (0x7cb90 : word) = Some W_7cb38.
Proof. vm_refl. Qed.
Lemma D_7cb38 : decode_any W_7cb38 = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb3c : bv 32 := 0x43f75513.
Lemma F_7cb3c : fetch_word Plain.M.loaded_segments (0x7cb94 : word) = Some W_7cb3c.
Proof. vm_refl. Qed.
Lemma D_7cb3c : decode_any W_7cb3c = Some (ShiftImm ALU_SRA 10 14 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb40 : bv 32 := 0x00e57533.
Lemma F_7cb40 : fetch_word Plain.M.loaded_segments (0x7cb98 : word) = Some W_7cb40.
Proof. vm_refl. Qed.
Lemma D_7cb40 : decode_any W_7cb40 = Some (Op ALU_AND 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb44 : bv 32 := 0x00a7853b.
Lemma F_7cb44 : fetch_word Plain.M.loaded_segments (0x7cb9c : word) = Some W_7cb44.
Proof. vm_refl. Qed.
Lemma D_7cb44 : decode_any W_7cb44 = Some (Op32 ALU_ADD 10 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb48 : bv 32 := 0x30a05e63.
Lemma F_7cb48 : fetch_word Plain.M.loaded_segments (0x7cba0 : word) = Some W_7cb48.
Proof. vm_refl. Qed.
Lemma D_7cb48 : decode_any W_7cb48 = Some (Branch BC_GE 0 10 796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb4c : bv 32 := 0x0115073b.
Lemma F_7cb4c : fetch_word Plain.M.loaded_segments (0x7cba4 : word) = Some W_7cb4c.
Proof. vm_refl. Qed.
Lemma D_7cb4c : decode_any W_7cb4c = Some (Op32 ALU_ADD 14 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb50 : bv 32 := 0x00e5f463.
Lemma F_7cb50 : fetch_word Plain.M.loaded_segments (0x7cba8 : word) = Some W_7cb50.
Proof. vm_refl. Qed.
Lemma D_7cb50 : decode_any W_7cb50 = Some (Branch BC_GEU 11 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb58 : bv 32 := 0x30a05663.
Lemma F_7cb58 : fetch_word Plain.M.loaded_segments (0x7cbb0 : word) = Some W_7cb58.
Proof. vm_refl. Qed.
Lemma D_7cb58 : decode_any W_7cb58 = Some (Branch BC_GE 0 10 780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb5c : bv 32 := 0x02c80a3b.
Lemma F_7cb5c : fetch_word Plain.M.loaded_segments (0x7cbb4 : word) = Some W_7cb5c.
Proof. vm_refl. Qed.
Lemma D_7cb5c : decode_any W_7cb5c = Some (Mul32 M_MUL 20 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb60 : bv 32 := 0x414005bb.
Lemma F_7cb60 : fetch_word Plain.M.loaded_segments (0x7cbb8 : word) = Some W_7cb60.
Proof. vm_refl. Qed.
Lemma D_7cb60 : decode_any W_7cb60 = Some (Op32 ALU_SUB 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb64 : bv 32 := 0x02b13c23.
Lemma F_7cb64 : fetch_word Plain.M.loaded_segments (0x7cbbc : word) = Some W_7cb64.
Proof. vm_refl. Qed.
Lemma D_7cb64 : decode_any W_7cb64 = Some (Store SZ8 2 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb68 : bv 32 := 0x0055d91b.
Lemma F_7cb68 : fetch_word Plain.M.loaded_segments (0x7cbc0 : word) = Some W_7cb68.
Proof. vm_refl. Qed.
Lemma D_7cb68 : decode_any W_7cb68 = Some (ShiftImm32 ALU_SRL 18 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb6c : bv 32 := 0x412685bb.
Lemma F_7cb6c : fetch_word Plain.M.loaded_segments (0x7cbc4 : word) = Some W_7cb6c.
Proof. vm_refl. Qed.
Lemma D_7cb6c : decode_any W_7cb6c = Some (Op32 ALU_SUB 11 13 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb70 : bv 32 := 0x04b13823.
Lemma F_7cb70 : fetch_word Plain.M.loaded_segments (0x7cbc8 : word) = Some W_7cb70.
Proof. vm_refl. Qed.
Lemma D_7cb70 : decode_any W_7cb70 = Some (Store SZ8 2 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb74 : bv 32 := 0x00d5c463.
Lemma F_7cb74 : fetch_word Plain.M.loaded_segments (0x7cbcc : word) = Some W_7cb74.
Proof. vm_refl. Qed.
Lemma D_7cb74 : decode_any W_7cb74 = Some (Branch BC_LT 11 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb7c : bv 32 := 0x03813583.
Lemma F_7cb7c : fetch_word Plain.M.loaded_segments (0x7cbd4 : word) = Some W_7cb7c.
Proof. vm_refl. Qed.
Lemma D_7cb7c : decode_any W_7cb7c = Some (Load SZ8 true 11 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb80 : bv 32 := 0x01f5fb93.
Lemma F_7cb80 : fetch_word Plain.M.loaded_segments (0x7cbd8 : word) = Some W_7cb80.
Proof. vm_refl. Qed.
Lemma D_7cb80 : decode_any W_7cb80 = Some (OpImm ALU_AND 23 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb84 : bv 32 := 0xfffa2717.
Lemma F_7cb84 : fetch_word Plain.M.loaded_segments (0x7cbdc : word) = Some W_7cb84.
Proof. vm_refl. Qed.
Lemma D_7cb84 : decode_any W_7cb84 = Some (Auipc 14 1048482, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb88 : bv 32 := 0x00193793.
Lemma F_7cb88 : fetch_word Plain.M.loaded_segments (0x7cbe0 : word) = Some W_7cb88.
Proof. vm_refl. Qed.
Lemma D_7cb88 : decode_any W_7cb88 = Some (OpImm ALU_SLTU 15 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb8c : bv 32 := 0x005a559b.
Lemma F_7cb8c : fetch_word Plain.M.loaded_segments (0x7cbe4 : word) = Some W_7cb8c.
Proof. vm_refl. Qed.
Lemma D_7cb8c : decode_any W_7cb8c = Some (ShiftImm32 ALU_SRL 11 20 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb90 : bv 32 := 0x002b9613.
Lemma F_7cb90 : fetch_word Plain.M.loaded_segments (0x7cbe8 : word) = Some W_7cb90.
Proof. vm_refl. Qed.
Lemma D_7cb90 : decode_any W_7cb90 = Some (ShiftImm ALU_SLL 12 23 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb94 : bv 32 := 0x7c470713.
Lemma F_7cb94 : fetch_word Plain.M.loaded_segments (0x7cbec : word) = Some W_7cb94.
Proof. vm_refl. Qed.
Lemma D_7cb94 : decode_any W_7cb94 = Some (OpImm ALU_ADD 14 14 1988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb98 : bv 32 := 0x40b6883b.
Lemma F_7cb98 : fetch_word Plain.M.loaded_segments (0x7cbf0 : word) = Some W_7cb98.
Proof. vm_refl. Qed.
Lemma D_7cb98 : decode_any W_7cb98 = Some (Op32 ALU_SUB 16 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cb9c : bv 32 := 0x00f907b3.
Lemma F_7cb9c : fetch_word Plain.M.loaded_segments (0x7cbf4 : word) = Some W_7cb9c.
Proof. vm_refl. Qed.
Lemma D_7cb9c : decode_any W_7cb9c = Some (Op ALU_ADD 15 18 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cba0 : bv 32 := 0x00068313.
Lemma F_7cba0 : fetch_word Plain.M.loaded_segments (0x7cbf8 : word) = Some W_7cba0.
Proof. vm_refl. Qed.
Lemma D_7cba0 : decode_any W_7cba0 = Some (OpImm ALU_ADD 6 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cba4 : bv 32 := 0x0106c463.
Lemma F_7cba4 : fetch_word Plain.M.loaded_segments (0x7cbfc : word) = Some W_7cba4.
Proof. vm_refl. Qed.
Lemma D_7cba4 : decode_any W_7cba4 = Some (Branch BC_LT 13 16 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cba8 : bv 32 := 0x00080313.
Lemma F_7cba8 : fetch_word Plain.M.loaded_segments (0x7cc00 : word) = Some W_7cba8.
Proof. vm_refl. Qed.
Lemma D_7cba8 : decode_any W_7cba8 = Some (OpImm ALU_ADD 6 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbac : bv 32 := 0x00000c93.
Lemma F_7cbac : fetch_word Plain.M.loaded_segments (0x7cc04 : word) = Some W_7cbac.
Proof. vm_refl. Qed.
Lemma D_7cbac : decode_any W_7cbac = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbb0 : bv 32 := 0x0115053b.
Lemma F_7cbb0 : fetch_word Plain.M.loaded_segments (0x7cc08 : word) = Some W_7cbb0.
Proof. vm_refl. Qed.
Lemma D_7cbb0 : decode_any W_7cbb0 = Some (Op32 ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbb4 : bv 32 := 0x06a13823.
Lemma F_7cbb4 : fetch_word Plain.M.loaded_segments (0x7cc0c : word) = Some W_7cbb4.
Proof. vm_refl. Qed.
Lemma D_7cbb4 : decode_any W_7cbb4 = Some (Store SZ8 2 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbb8 : bv 32 := 0x00c70633.
Lemma F_7cbb8 : fetch_word Plain.M.loaded_segments (0x7cc10 : word) = Some W_7cbb8.
Proof. vm_refl. Qed.
Lemma D_7cbb8 : decode_any W_7cbb8 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbbc : bv 32 := 0x02c13423.
Lemma F_7cbbc : fetch_word Plain.M.loaded_segments (0x7cc14 : word) = Some W_7cbbc.
Proof. vm_refl. Qed.
Lemma D_7cbbc : decode_any W_7cbbc = Some (Store SZ8 2 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbc0 : bv 32 := 0x00279793.
Lemma F_7cbc0 : fetch_word Plain.M.loaded_segments (0x7cc18 : word) = Some W_7cbc0.
Proof. vm_refl. Qed.
Lemma D_7cbc0 : decode_any W_7cbc0 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbc4 : bv 32 := 0x02f13823.
Lemma F_7cbc4 : fetch_word Plain.M.loaded_segments (0x7cc1c : word) = Some W_7cbc4.
Proof. vm_refl. Qed.
Lemma D_7cbc4 : decode_any W_7cbc4 = Some (Store SZ8 2 15 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbc8 : bv 32 := 0x00b3053b.
Lemma F_7cbc8 : fetch_word Plain.M.loaded_segments (0x7cc20 : word) = Some W_7cbc8.
Proof. vm_refl. Qed.
Lemma D_7cbc8 : decode_any W_7cbc8 = Some (Op32 ALU_ADD 10 6 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbcc : bv 32 := 0x01fa7d93.
Lemma F_7cbcc : fetch_word Plain.M.loaded_segments (0x7cc24 : word) = Some W_7cbcc.
Proof. vm_refl. Qed.
Lemma D_7cbcc : decode_any W_7cbcc = Some (OpImm ALU_AND 27 20 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbd0 : bv 32 := 0xfffa2617.
Lemma F_7cbd0 : fetch_word Plain.M.loaded_segments (0x7cc28 : word) = Some W_7cbd0.
Proof. vm_refl. Qed.
Lemma D_7cbd0 : decode_any W_7cbd0 = Some (Auipc 12 1048482, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbd4 : bv 32 := 0xfff58593.
Lemma F_7cbd4 : fetch_word Plain.M.loaded_segments (0x7cc2c : word) = Some W_7cbd4.
Proof. vm_refl. Qed.
Lemma D_7cbd4 : decode_any W_7cbd4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbd8 : bv 32 := 0x02089293.
Lemma F_7cbd8 : fetch_word Plain.M.loaded_segments (0x7cc30 : word) = Some W_7cbd8.
Proof. vm_refl. Qed.
Lemma D_7cbd8 : decode_any W_7cbd8 = Some (ShiftImm ALU_SLL 5 17 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbdc : bv 32 := 0x00291913.
Lemma F_7cbdc : fetch_word Plain.M.loaded_segments (0x7cc34 : word) = Some W_7cbdc.
Proof. vm_refl. Qed.
Lemma D_7cbdc : decode_any W_7cbdc = Some (ShiftImm ALU_SLL 18 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbe0 : bv 32 := 0x00100713.
Lemma F_7cbe0 : fetch_word Plain.M.loaded_segments (0x7cc38 : word) = Some W_7cbe0.
Proof. vm_refl. Qed.
Lemma D_7cbe0 : decode_any W_7cbe0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbe4 : bv 32 := 0x00231c13.
Lemma F_7cbe4 : fetch_word Plain.M.loaded_segments (0x7cc3c : word) = Some W_7cbe4.
Proof. vm_refl. Qed.
Lemma D_7cbe4 : decode_any W_7cbe4 = Some (ShiftImm ALU_SLL 24 6 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbe8 : bv 32 := 0x00269a93.
Lemma F_7cbe8 : fetch_word Plain.M.loaded_segments (0x7cc40 : word) = Some W_7cbe8.
Proof. vm_refl. Qed.
Lemma D_7cbe8 : decode_any W_7cbe8 = Some (ShiftImm ALU_SLL 21 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbec : bv 32 := 0xffe30793.
Lemma F_7cbec : fetch_word Plain.M.loaded_segments (0x7cc44 : word) = Some W_7cbec.
Proof. vm_refl. Qed.
Lemma D_7cbec : decode_any W_7cbec = Some (OpImm ALU_ADD 15 6 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbf0 : bv 32 := 0xfff30813.
Lemma F_7cbf0 : fetch_word Plain.M.loaded_segments (0x7cc48 : word) = Some W_7cbf0.
Proof. vm_refl. Qed.
Lemma D_7cbf0 : decode_any W_7cbf0 = Some (OpImm ALU_ADD 16 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbf4 : bv 32 := 0x002d9893.
Lemma F_7cbf4 : fetch_word Plain.M.loaded_segments (0x7cc4c : word) = Some W_7cbf4.
Proof. vm_refl. Qed.
Lemma D_7cbf4 : decode_any W_7cbf4 = Some (ShiftImm ALU_SLL 17 27 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbf8 : bv 32 := 0x7fc60613.
Lemma F_7cbf8 : fetch_word Plain.M.loaded_segments (0x7cc50 : word) = Some W_7cbf8.
Proof. vm_refl. Qed.
Lemma D_7cbf8 : decode_any W_7cbf8 = Some (OpImm ALU_ADD 12 12 2044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cbfc : bv 32 := 0x02059593.
Lemma F_7cbfc : fetch_word Plain.M.loaded_segments (0x7cc54 : word) = Some W_7cbfc.
Proof. vm_refl. Qed.
Lemma D_7cbfc : decode_any W_7cbfc = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc00 : bv 32 := 0x0202db13.
Lemma F_7cc00 : fetch_word Plain.M.loaded_segments (0x7cc58 : word) = Some W_7cc00.
Proof. vm_refl. Qed.
Lemma D_7cc00 : decode_any W_7cc00 = Some (ShiftImm ALU_SRL 22 5 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc04 : bv 32 := 0x05013283.
Lemma F_7cc04 : fetch_word Plain.M.loaded_segments (0x7cc5c : word) = Some W_7cc04.
Proof. vm_refl. Qed.
Lemma D_7cc04 : decode_any W_7cc04 = Some (Load SZ8 true 5 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc08 : bv 32 := 0x4057073b.
Lemma F_7cc08 : fetch_word Plain.M.loaded_segments (0x7cc60 : word) = Some W_7cc08.
Proof. vm_refl. Qed.
Lemma D_7cc08 : decode_any W_7cc08 = Some (Op32 ALU_SUB 14 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc0c : bv 32 := 0x02e13023.
Lemma F_7cc0c : fetch_word Plain.M.loaded_segments (0x7cc64 : word) = Some W_7cc0c.
Proof. vm_refl. Qed.
Lemma D_7cc0c : decode_any W_7cc0c = Some (Store SZ8 2 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc10 : bv 32 := 0x00251713.
Lemma F_7cc10 : fetch_word Plain.M.loaded_segments (0x7cc68 : word) = Some W_7cc10.
Proof. vm_refl. Qed.
Lemma D_7cc10 : decode_any W_7cc10 = Some (ShiftImm ALU_SLL 14 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc14 : bv 32 := 0x02079793.
Lemma F_7cc14 : fetch_word Plain.M.loaded_segments (0x7cc6c : word) = Some W_7cc14.
Proof. vm_refl. Qed.
Lemma D_7cc14 : decode_any W_7cc14 = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc18 : bv 32 := 0x02081813.
Lemma F_7cc18 : fetch_word Plain.M.loaded_segments (0x7cc70 : word) = Some W_7cc18.
Proof. vm_refl. Qed.
Lemma D_7cc18 : decode_any W_7cc18 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc1c : bv 32 := 0x01160633.
Lemma F_7cc1c : fetch_word Plain.M.loaded_segments (0x7cc74 : word) = Some W_7cc1c.
Proof. vm_refl. Qed.
Lemma D_7cc1c : decode_any W_7cc1c = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc20 : bv 32 := 0x04c13423.
Lemma F_7cc20 : fetch_word Plain.M.loaded_segments (0x7cc78 : word) = Some W_7cc20.
Proof. vm_refl. Qed.
Lemma D_7cc20 : decode_any W_7cc20 = Some (Store SZ8 2 12 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc24 : bv 32 := 0x01e5d593.
Lemma F_7cc24 : fetch_word Plain.M.loaded_segments (0x7cc7c : word) = Some W_7cc24.
Proof. vm_refl. Qed.
Lemma D_7cc24 : decode_any W_7cc24 = Some (ShiftImm ALU_SRL 11 11 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc28 : bv 32 := 0x03668533.
Lemma F_7cc28 : fetch_word Plain.M.loaded_segments (0x7cc80 : word) = Some W_7cc28.
Proof. vm_refl. Qed.
Lemma D_7cc28 : decode_any W_7cc28 = Some (Mul M_MUL 10 13 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc2c : bv 32 := 0xffc70993.
Lemma F_7cc2c : fetch_word Plain.M.loaded_segments (0x7cc84 : word) = Some W_7cc2c.
Proof. vm_refl. Qed.
Lemma D_7cc2c : decode_any W_7cc2c = Some (OpImm ALU_ADD 19 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc30 : bv 32 := 0x01e7d793.
Lemma F_7cc30 : fetch_word Plain.M.loaded_segments (0x7cc88 : word) = Some W_7cc30.
Proof. vm_refl. Qed.
Lemma D_7cc30 : decode_any W_7cc30 = Some (ShiftImm ALU_SRL 15 15 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc34 : bv 32 := 0x01e85613.
Lemma F_7cc34 : fetch_word Plain.M.loaded_segments (0x7cc8c : word) = Some W_7cc34.
Proof. vm_refl. Qed.
Lemma D_7cc34 : decode_any W_7cc34 = Some (ShiftImm ALU_SRL 12 16 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc38 : bv 32 := 0xffc5c813.
Lemma F_7cc38 : fetch_word Plain.M.loaded_segments (0x7cc90 : word) = Some W_7cc38.
Proof. vm_refl. Qed.
Lemma D_7cc38 : decode_any W_7cc38 = Some (OpImm ALU_XOR 16 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc3c : bv 32 := 0x01013c23.
Lemma F_7cc3c : fetch_word Plain.M.loaded_segments (0x7cc94 : word) = Some W_7cc3c.
Proof. vm_refl. Qed.
Lemma D_7cc3c : decode_any W_7cc3c = Some (Store SZ8 2 16 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc40 : bv 32 := 0x00458813.
Lemma F_7cc40 : fetch_word Plain.M.loaded_segments (0x7cc98 : word) = Some W_7cc40.
Proof. vm_refl. Qed.
Lemma D_7cc40 : decode_any W_7cc40 = Some (OpImm ALU_ADD 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc44 : bv 32 := 0x05013023.
Lemma F_7cc44 : fetch_word Plain.M.loaded_segments (0x7cc9c : word) = Some W_7cc44.
Proof. vm_refl. Qed.
Lemma D_7cc44 : decode_any W_7cc44 = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc48 : bv 32 := 0x40b005b3.
Lemma F_7cc48 : fetch_word Plain.M.loaded_segments (0x7cca0 : word) = Some W_7cc48.
Proof. vm_refl. Qed.
Lemma D_7cc48 : decode_any W_7cc48 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc4c : bv 32 := 0x00b13023.
Lemma F_7cc4c : fetch_word Plain.M.loaded_segments (0x7cca4 : word) = Some W_7cc4c.
Proof. vm_refl. Qed.
Lemma D_7cc4c : decode_any W_7cc4c = Some (Store SZ8 2 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc50 : bv 32 := 0x00251513.
Lemma F_7cc50 : fetch_word Plain.M.loaded_segments (0x7cca8 : word) = Some W_7cc50.
Proof. vm_refl. Qed.
Lemma D_7cc50 : decode_any W_7cc50 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc54 : bv 32 := 0x00ad0433.
Lemma F_7cc54 : fetch_word Plain.M.loaded_segments (0x7ccac : word) = Some W_7cc54.
Proof. vm_refl. Qed.
Lemma D_7cc54 : decode_any W_7cc54 = Some (Op ALU_ADD 8 26 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc58 : bv 32 := 0x40f505b3.
Lemma F_7cc58 : fetch_word Plain.M.loaded_segments (0x7ccb0 : word) = Some W_7cc58.
Proof. vm_refl. Qed.
Lemma D_7cc58 : decode_any W_7cc58 = Some (Op ALU_SUB 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc5c : bv 32 := 0x06e13423.
Lemma F_7cc5c : fetch_word Plain.M.loaded_segments (0x7ccb4 : word) = Some W_7cc5c.
Proof. vm_refl. Qed.
Lemma D_7cc5c : decode_any W_7cc5c = Some (Store SZ8 2 14 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc60 : bv 32 := 0x00e50533.
Lemma F_7cc60 : fetch_word Plain.M.loaded_segments (0x7ccb8 : word) = Some W_7cc60.
Proof. vm_refl. Qed.
Lemma D_7cc60 : decode_any W_7cc60 = Some (Op ALU_ADD 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc64 : bv 32 := 0xffc58593.
Lemma F_7cc64 : fetch_word Plain.M.loaded_segments (0x7ccbc : word) = Some W_7cc64.
Proof. vm_refl. Qed.
Lemma D_7cc64 : decode_any W_7cc64 = Some (OpImm ALU_ADD 11 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc68 : bv 32 := 0x00b13823.
Lemma F_7cc68 : fetch_word Plain.M.loaded_segments (0x7ccc0 : word) = Some W_7cc68.
Proof. vm_refl. Qed.
Lemma D_7cc68 : decode_any W_7cc68 = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc6c : bv 32 := 0x00ad04b3.
Lemma F_7cc6c : fetch_word Plain.M.loaded_segments (0x7ccc4 : word) = Some W_7cc6c.
Proof. vm_refl. Qed.
Lemma D_7cc6c : decode_any W_7cc6c = Some (Op ALU_ADD 9 26 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc70 : bv 32 := 0x40c50533.
Lemma F_7cc70 : fetch_word Plain.M.loaded_segments (0x7ccc8 : word) = Some W_7cc70.
Proof. vm_refl. Qed.
Lemma D_7cc70 : decode_any W_7cc70 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc74 : bv 32 := 0xffc50513.
Lemma F_7cc74 : fetch_word Plain.M.loaded_segments (0x7cccc : word) = Some W_7cc74.
Proof. vm_refl. Qed.
Lemma D_7cc74 : decode_any W_7cc74 = Some (OpImm ALU_ADD 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc78 : bv 32 := 0x00a13423.
Lemma F_7cc78 : fetch_word Plain.M.loaded_segments (0x7ccd0 : word) = Some W_7cc78.
Proof. vm_refl. Qed.
Lemma D_7cc78 : decode_any W_7cc78 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc7c : bv 32 := 0x06d13023.
Lemma F_7cc7c : fetch_word Plain.M.loaded_segments (0x7ccd4 : word) = Some W_7cc7c.
Proof. vm_refl. Qed.
Lemma D_7cc7c : decode_any W_7cc7c = Some (Store SZ8 2 13 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc80 : bv 32 := 0x04613c23.
Lemma F_7cc80 : fetch_word Plain.M.loaded_segments (0x7ccd8 : word) = Some W_7cc80.
Proof. vm_refl. Qed.
Lemma D_7cc80 : decode_any W_7cc80 = Some (Store SZ8 2 6 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc84 : bv 32 := 0x0300006f.
Lemma F_7cc84 : fetch_word Plain.M.loaded_segments (0x7ccdc : word) = Some W_7cc84.
Proof. vm_refl. Qed.
Lemma D_7cc84 : decode_any W_7cc84 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cc9c : bv 32 := 0x001b0b13.
Lemma F_7cc9c : fetch_word Plain.M.loaded_segments (0x7ccf4 : word) = Some W_7cc9c.
Proof. vm_refl. Qed.
Lemma D_7cc9c : decode_any W_7cc9c = Some (OpImm ALU_ADD 22 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cca0 : bv 32 := 0x01540433.
Lemma F_7cca0 : fetch_word Plain.M.loaded_segments (0x7ccf8 : word) = Some W_7cca0.
Proof. vm_refl. Qed.
Lemma D_7cca0 : decode_any W_7cca0 = Some (Op ALU_ADD 8 8 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cca4 : bv 32 := 0x001c8c93.
Lemma F_7cca4 : fetch_word Plain.M.loaded_segments (0x7ccfc : word) = Some W_7cca4.
Proof. vm_refl. Qed.
Lemma D_7cca4 : decode_any W_7cca4 = Some (OpImm ALU_ADD 25 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cca8 : bv 32 := 0x015484b3.
Lemma F_7cca8 : fetch_word Plain.M.loaded_segments (0x7cd00 : word) = Some W_7cca8.
Proof. vm_refl. Qed.
Lemma D_7cca8 : decode_any W_7cca8 = Some (Op ALU_ADD 9 9 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccac : bv 32 := 0x07013503.
Lemma F_7ccac : fetch_word Plain.M.loaded_segments (0x7cd04 : word) = Some W_7ccac.
Proof. vm_refl. Qed.
Lemma D_7ccac : decode_any W_7ccac = Some (Load SZ8 true 10 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccb0 : bv 32 := 0x1aab7a63.
Lemma F_7ccb0 : fetch_word Plain.M.loaded_segments (0x7cd08 : word) = Some W_7ccb0.
Proof. vm_refl. Qed.
Lemma D_7ccb0 : decode_any W_7ccb0 = Some (Branch BC_GEU 22 10 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccb4 : bv 32 := 0x02db0533.
Lemma F_7ccb4 : fetch_word Plain.M.loaded_segments (0x7cd0c : word) = Some W_7ccb4.
Proof. vm_refl. Qed.
Lemma D_7ccb4 : decode_any W_7ccb4 = Some (Mul M_MUL 10 22 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccb8 : bv 32 := 0x00251513.
Lemma F_7ccb8 : fetch_word Plain.M.loaded_segments (0x7cd10 : word) = Some W_7ccb8.
Proof. vm_refl. Qed.
Lemma D_7ccb8 : decode_any W_7ccb8 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccbc : bv 32 := 0x00ad0533.
Lemma F_7ccbc : fetch_word Plain.M.loaded_segments (0x7cd14 : word) = Some W_7ccbc.
Proof. vm_refl. Qed.
Lemma D_7ccbc : decode_any W_7ccbc = Some (Op ALU_ADD 10 26 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccc0 : bv 32 := 0x060a4663.
Lemma F_7ccc0 : fetch_word Plain.M.loaded_segments (0x7cd18 : word) = Some W_7ccc0.
Proof. vm_refl. Qed.
Lemma D_7ccc0 : decode_any W_7ccc0 = Some (Branch BC_LT 20 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccc4 : bv 32 := 0x039a8633.
Lemma F_7ccc4 : fetch_word Plain.M.loaded_segments (0x7cd1c : word) = Some W_7ccc4.
Proof. vm_refl. Qed.
Lemma D_7ccc4 : decode_any W_7ccc4 = Some (Mul M_MUL 12 21 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccc8 : bv 32 := 0x06813583.
Lemma F_7ccc8 : fetch_word Plain.M.loaded_segments (0x7cd20 : word) = Some W_7ccc8.
Proof. vm_refl. Qed.
Lemma D_7ccc8 : decode_any W_7ccc8 = Some (Load SZ8 true 11 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cccc : bv 32 := 0x00b505b3.
Lemma F_7cccc : fetch_word Plain.M.loaded_segments (0x7cd24 : word) = Some W_7cccc.
Proof. vm_refl. Qed.
Lemma D_7cccc : decode_any W_7cccc = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccd0 : bv 32 := 0x01850533.
Lemma F_7ccd0 : fetch_word Plain.M.loaded_segments (0x7cd28 : word) = Some W_7ccd0.
Proof. vm_refl. Qed.
Lemma D_7ccd0 : decode_any W_7ccd0 = Some (Op ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccd4 : bv 32 := 0xffc50513.
Lemma F_7ccd4 : fetch_word Plain.M.loaded_segments (0x7cd2c : word) = Some W_7ccd4.
Proof. vm_refl. Qed.
Lemma D_7ccd4 : decode_any W_7ccd4 = Some (OpImm ALU_ADD 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccd8 : bv 32 := 0x0c0d8a63.
Lemma F_7ccd8 : fetch_word Plain.M.loaded_segments (0x7cd30 : word) = Some W_7ccd8.
Proof. vm_refl. Qed.
Lemma D_7ccd8 : decode_any W_7ccd8 = Some (Branch BC_EQ 27 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccdc : bv 32 := 0x00200713.
Lemma F_7ccdc : fetch_word Plain.M.loaded_segments (0x7cd34 : word) = Some W_7ccdc.
Proof. vm_refl. Qed.
Lemma D_7ccdc : decode_any W_7ccdc = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cce0 : bv 32 := 0x10e34863.
Lemma F_7cce0 : fetch_word Plain.M.loaded_segments (0x7cd38 : word) = Some W_7cce0.
Proof. vm_refl. Qed.
Lemma D_7cce0 : decode_any W_7cce0 = Some (Branch BC_LT 6 14 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cce4 : bv 32 := 0x01013503.
Lemma F_7cce4 : fetch_word Plain.M.loaded_segments (0x7cd3c : word) = Some W_7cce4.
Proof. vm_refl. Qed.
Lemma D_7cce4 : decode_any W_7cce4 = Some (Load SZ8 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cce8 : bv 32 := 0x00c50533.
Lemma F_7cce8 : fetch_word Plain.M.loaded_segments (0x7cd40 : word) = Some W_7cce8.
Proof. vm_refl. Qed.
Lemma D_7cce8 : decode_any W_7cce8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccec : bv 32 := 0x00ad0533.
Lemma F_7ccec : fetch_word Plain.M.loaded_segments (0x7cd44 : word) = Some W_7ccec.
Proof. vm_refl. Qed.
Lemma D_7ccec : decode_any W_7ccec = Some (Op ALU_ADD 10 26 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccf0 : bv 32 := 0x00040593.
Lemma F_7ccf0 : fetch_word Plain.M.loaded_segments (0x7cd48 : word) = Some W_7ccf0.
Proof. vm_refl. Qed.
Lemma D_7ccf0 : decode_any W_7ccf0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccf4 : bv 32 := 0x01858633.
Lemma F_7ccf4 : fetch_word Plain.M.loaded_segments (0x7cd4c : word) = Some W_7ccf4.
Proof. vm_refl. Qed.
Lemma D_7ccf4 : decode_any W_7ccf4 = Some (Op ALU_ADD 12 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccf8 : bv 32 := 0xff862783.
Lemma F_7ccf8 : fetch_word Plain.M.loaded_segments (0x7cd50 : word) = Some W_7ccf8.
Proof. vm_refl. Qed.
Lemma D_7ccf8 : decode_any W_7ccf8 = Some (Load SZ4 true 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ccfc : bv 32 := 0xffc66603.
Lemma F_7ccfc : fetch_word Plain.M.loaded_segments (0x7cd54 : word) = Some W_7ccfc.
Proof. vm_refl. Qed.
Lemma D_7ccfc : decode_any W_7ccfc = Some (Load SZ4 false 12 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd00 : bv 32 := 0x01358733.
Lemma F_7cd00 : fetch_word Plain.M.loaded_segments (0x7cd58 : word) = Some W_7cd00.
Proof. vm_refl. Qed.
Lemma D_7cd00 : decode_any W_7cd00 = Some (Op ALU_ADD 14 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd04 : bv 32 := 0x02079793.
Lemma F_7cd04 : fetch_word Plain.M.loaded_segments (0x7cd5c : word) = Some W_7cd04.
Proof. vm_refl. Qed.
Lemma D_7cd04 : decode_any W_7cd04 = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd08 : bv 32 := 0x00c7e633.
Lemma F_7cd08 : fetch_word Plain.M.loaded_segments (0x7cd60 : word) = Some W_7cd08.
Proof. vm_refl. Qed.
Lemma D_7cd08 : decode_any W_7cd08 = Some (Op ALU_OR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd0c : bv 32 := 0x01b65633.
Lemma F_7cd0c : fetch_word Plain.M.loaded_segments (0x7cd64 : word) = Some W_7cd0c.
Proof. vm_refl. Qed.
Lemma D_7cd0c : decode_any W_7cd0c = Some (Op ALU_SRL 12 12 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd10 : bv 32 := 0xffc58593.
Lemma F_7cd10 : fetch_word Plain.M.loaded_segments (0x7cd68 : word) = Some W_7cd10.
Proof. vm_refl. Qed.
Lemma D_7cd10 : decode_any W_7cd10 = Some (OpImm ALU_ADD 11 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd14 : bv 32 := 0x00c72023.
Lemma F_7cd14 : fetch_word Plain.M.loaded_segments (0x7cd6c : word) = Some W_7cd14.
Proof. vm_refl. Qed.
Lemma D_7cd14 : decode_any W_7cd14 = Some (Store SZ4 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd18 : bv 32 := 0xfca59ee3.
Lemma F_7cd18 : fetch_word Plain.M.loaded_segments (0x7cd70 : word) = Some W_7cd18.
Proof. vm_refl. Qed.
Lemma D_7cd18 : decode_any W_7cd18 = Some (Branch BC_NE 11 10 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd1c : bv 32 := 0x01858533.
Lemma F_7cd1c : fetch_word Plain.M.loaded_segments (0x7cd74 : word) = Some W_7cd1c.
Proof. vm_refl. Qed.
Lemma D_7cd1c : decode_any W_7cd1c = Some (Op ALU_ADD 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd20 : bv 32 := 0xffc50513.
Lemma F_7cd20 : fetch_word Plain.M.loaded_segments (0x7cd78 : word) = Some W_7cd20.
Proof. vm_refl. Qed.
Lemma D_7cd20 : decode_any W_7cd20 = Some (OpImm ALU_ADD 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd24 : bv 32 := 0x013585b3.
Lemma F_7cd24 : fetch_word Plain.M.loaded_segments (0x7cd7c : word) = Some W_7cd24.
Proof. vm_refl. Qed.
Lemma D_7cd24 : decode_any W_7cd24 = Some (Op ALU_ADD 11 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cd28 : bv 32 := 0x0cc0006f.
Lemma F_7cd28 : fetch_word Plain.M.loaded_segments (0x7cd80 : word) = Some W_7cd28.
Proof. vm_refl. Qed.
Lemma D_7cd28 : decode_any W_7cd28 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cdf0 : bv 32 := 0xffc58593.
Lemma F_7cdf0 : fetch_word Plain.M.loaded_segments (0x7ce48 : word) = Some W_7cdf0.
Proof. vm_refl. Qed.
Lemma D_7cdf0 : decode_any W_7cdf0 = Some (OpImm ALU_ADD 11 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cdf4 : bv 32 := 0x00052503.
Lemma F_7cdf4 : fetch_word Plain.M.loaded_segments (0x7ce4c : word) = Some W_7cdf4.
Proof. vm_refl. Qed.
Lemma D_7cdf4 : decode_any W_7cdf4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cdf8 : bv 32 := 0x04813603.
Lemma F_7cdf8 : fetch_word Plain.M.loaded_segments (0x7ce50 : word) = Some W_7cdf8.
Proof. vm_refl. Qed.
Lemma D_7cdf8 : decode_any W_7cdf8 = Some (Load SZ8 true 12 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7cdfc : bv 32 := 0x00062603.
Lemma F_7cdfc : fetch_word Plain.M.loaded_segments (0x7ce54 : word) = Some W_7cdfc.
Proof. vm_refl. Qed.
Lemma D_7cdfc : decode_any W_7cdfc = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce00 : bv 32 := 0x01b5553b.
Lemma F_7ce00 : fetch_word Plain.M.loaded_segments (0x7ce58 : word) = Some W_7ce00.
Proof. vm_refl. Qed.
Lemma D_7ce00 : decode_any W_7ce00 = Some (Op32 ALU_SRL 10 10 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce04 : bv 32 := 0xfff64613.
Lemma F_7ce04 : fetch_word Plain.M.loaded_segments (0x7ce5c : word) = Some W_7ce04.
Proof. vm_refl. Qed.
Lemma D_7ce04 : decode_any W_7ce04 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce08 : bv 32 := 0x00c57533.
Lemma F_7ce08 : fetch_word Plain.M.loaded_segments (0x7ce60 : word) = Some W_7ce08.
Proof. vm_refl. Qed.
Lemma D_7ce08 : decode_any W_7ce08 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce0c : bv 32 := 0x00a5a023.
Lemma F_7ce0c : fetch_word Plain.M.loaded_segments (0x7ce64 : word) = Some W_7ce0c.
Proof. vm_refl. Qed.
Lemma D_7ce0c : decode_any W_7ce0c = Some (Store SZ4 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce10 : bv 32 := 0x02000513.
Lemma F_7ce10 : fetch_word Plain.M.loaded_segments (0x7ce68 : word) = Some W_7ce10.
Proof. vm_refl. Qed.
Lemma D_7ce10 : decode_any W_7ce10 = Some (OpImm ALU_ADD 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce14 : bv 32 := 0xe8aa64e3.
Lemma F_7ce14 : fetch_word Plain.M.loaded_segments (0x7ce6c : word) = Some W_7ce14.
Proof. vm_refl. Qed.
Lemma D_7ce14 : decode_any W_7ce14 = Some (Branch BC_LTU 20 10 7816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce64 : bv 32 := 0x0d813083.
Lemma F_7ce64 : fetch_word Plain.M.loaded_segments (0x7cebc : word) = Some W_7ce64.
Proof. vm_refl. Qed.
Lemma D_7ce64 : decode_any W_7ce64 = Some (Load SZ8 true 1 2 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce68 : bv 32 := 0x0d013403.
Lemma F_7ce68 : fetch_word Plain.M.loaded_segments (0x7cec0 : word) = Some W_7ce68.
Proof. vm_refl. Qed.
Lemma D_7ce68 : decode_any W_7ce68 = Some (Load SZ8 true 8 2 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce6c : bv 32 := 0x0c813483.
Lemma F_7ce6c : fetch_word Plain.M.loaded_segments (0x7cec4 : word) = Some W_7ce6c.
Proof. vm_refl. Qed.
Lemma D_7ce6c : decode_any W_7ce6c = Some (Load SZ8 true 9 2 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce70 : bv 32 := 0x0c013903.
Lemma F_7ce70 : fetch_word Plain.M.loaded_segments (0x7cec8 : word) = Some W_7ce70.
Proof. vm_refl. Qed.
Lemma D_7ce70 : decode_any W_7ce70 = Some (Load SZ8 true 18 2 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce74 : bv 32 := 0x0b813983.
Lemma F_7ce74 : fetch_word Plain.M.loaded_segments (0x7cecc : word) = Some W_7ce74.
Proof. vm_refl. Qed.
Lemma D_7ce74 : decode_any W_7ce74 = Some (Load SZ8 true 19 2 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce78 : bv 32 := 0x0b013a03.
Lemma F_7ce78 : fetch_word Plain.M.loaded_segments (0x7ced0 : word) = Some W_7ce78.
Proof. vm_refl. Qed.
Lemma D_7ce78 : decode_any W_7ce78 = Some (Load SZ8 true 20 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce7c : bv 32 := 0x0a813a83.
Lemma F_7ce7c : fetch_word Plain.M.loaded_segments (0x7ced4 : word) = Some W_7ce7c.
Proof. vm_refl. Qed.
Lemma D_7ce7c : decode_any W_7ce7c = Some (Load SZ8 true 21 2 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce80 : bv 32 := 0x0a013b03.
Lemma F_7ce80 : fetch_word Plain.M.loaded_segments (0x7ced8 : word) = Some W_7ce80.
Proof. vm_refl. Qed.
Lemma D_7ce80 : decode_any W_7ce80 = Some (Load SZ8 true 22 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce84 : bv 32 := 0x09813b83.
Lemma F_7ce84 : fetch_word Plain.M.loaded_segments (0x7cedc : word) = Some W_7ce84.
Proof. vm_refl. Qed.
Lemma D_7ce84 : decode_any W_7ce84 = Some (Load SZ8 true 23 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce88 : bv 32 := 0x09013c03.
Lemma F_7ce88 : fetch_word Plain.M.loaded_segments (0x7cee0 : word) = Some W_7ce88.
Proof. vm_refl. Qed.
Lemma D_7ce88 : decode_any W_7ce88 = Some (Load SZ8 true 24 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce8c : bv 32 := 0x08813c83.
Lemma F_7ce8c : fetch_word Plain.M.loaded_segments (0x7cee4 : word) = Some W_7ce8c.
Proof. vm_refl. Qed.
Lemma D_7ce8c : decode_any W_7ce8c = Some (Load SZ8 true 25 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce90 : bv 32 := 0x08013d03.
Lemma F_7ce90 : fetch_word Plain.M.loaded_segments (0x7cee8 : word) = Some W_7ce90.
Proof. vm_refl. Qed.
Lemma D_7ce90 : decode_any W_7ce90 = Some (Load SZ8 true 26 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce94 : bv 32 := 0x07813d83.
Lemma F_7ce94 : fetch_word Plain.M.loaded_segments (0x7ceec : word) = Some W_7ce94.
Proof. vm_refl. Qed.
Lemma D_7ce94 : decode_any W_7ce94 = Some (Load SZ8 true 27 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce98 : bv 32 := 0x0e010113.
Lemma F_7ce98 : fetch_word Plain.M.loaded_segments (0x7cef0 : word) = Some W_7ce98.
Proof. vm_refl. Qed.
Lemma D_7ce98 : decode_any W_7ce98 = Some (OpImm ALU_ADD 2 2 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ce9c : bv 32 := 0x00008067.
Lemma F_7ce9c : fetch_word Plain.M.loaded_segments (0x7cef4 : word) = Some W_7ce9c.
Proof. vm_refl. Qed.
Lemma D_7ce9c : decode_any W_7ce9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
