(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_aadf8 : bv 32 := 0x00008067.
Lemma F_aadf8 : fetch_word Ubsan.M.loaded_segments (0xac42c : word) = Some W_aadf8.
Proof. vm_refl. Qed.
Lemma D_aadf8 : decode_any W_aadf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aadfc : bv 32 := 0xfddff06f.
Lemma F_aadfc : fetch_word Ubsan.M.loaded_segments (0xac430 : word) = Some W_aadfc.
Proof. vm_refl. Qed.
Lemma D_aadfc : decode_any W_aadfc = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ac50c : bv 32 := 0x00050213.
Lemma F_ac50c : fetch_word Ubsan.M.loaded_segments (0xadb40 : word) = Some W_ac50c.
Proof. vm_refl. Qed.
Lemma D_ac50c : decode_any W_ac50c = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ac510 : bv 32 := 0x00000513.
Lemma F_ac510 : fetch_word Ubsan.M.loaded_segments (0xadb44 : word) = Some W_ac510.
Proof. vm_refl. Qed.
Lemma D_ac510 : decode_any W_ac510 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ac514 : bv 32 := 0x00008067.
Lemma F_ac514 : fetch_word Ubsan.M.loaded_segments (0xadb48 : word) = Some W_ac514.
Proof. vm_refl. Qed.
Lemma D_ac514 : decode_any W_ac514 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aecf0 : bv 32 := 0xff010113.
Lemma F_aecf0 : fetch_word Ubsan.M.loaded_segments (0xb0324 : word) = Some W_aecf0.
Proof. vm_refl. Qed.
Lemma D_aecf0 : decode_any W_aecf0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aecf4 : bv 32 := 0x00113423.
Lemma F_aecf4 : fetch_word Ubsan.M.loaded_segments (0xb0328 : word) = Some W_aecf4.
Proof. vm_refl. Qed.
Lemma D_aecf4 : decode_any W_aecf4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aecf8 : bv 32 := 0xdc5ef0ef.
Lemma F_aecf8 : fetch_word Ubsan.M.loaded_segments (0xb032c : word) = Some W_aecf8.
Proof. vm_refl. Qed.
Lemma D_aecf8 : decode_any W_aecf8 = Some (Jal 1 2031044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aecfc : bv 32 := 0x00050593.
Lemma F_aecfc : fetch_word Ubsan.M.loaded_segments (0xb0330 : word) = Some W_aecfc.
Proof. vm_refl. Qed.
Lemma D_aecfc : decode_any W_aecfc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed00 : bv 32 := 0x03900513.
Lemma F_aed00 : fetch_word Ubsan.M.loaded_segments (0xb0334 : word) = Some W_aed00.
Proof. vm_refl. Qed.
Lemma D_aed00 : decode_any W_aed00 = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed04 : bv 32 := 0x00000613.
Lemma F_aed04 : fetch_word Ubsan.M.loaded_segments (0xb0338 : word) = Some W_aed04.
Proof. vm_refl. Qed.
Lemma D_aed04 : decode_any W_aed04 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed08 : bv 32 := 0x00000693.
Lemma F_aed08 : fetch_word Ubsan.M.loaded_segments (0xb033c : word) = Some W_aed08.
Proof. vm_refl. Qed.
Lemma D_aed08 : decode_any W_aed08 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed0c : bv 32 := 0x00000713.
Lemma F_aed0c : fetch_word Ubsan.M.loaded_segments (0xb0340 : word) = Some W_aed0c.
Proof. vm_refl. Qed.
Lemma D_aed0c : decode_any W_aed0c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed10 : bv 32 := 0x00000793.
Lemma F_aed10 : fetch_word Ubsan.M.loaded_segments (0xb0344 : word) = Some W_aed10.
Proof. vm_refl. Qed.
Lemma D_aed10 : decode_any W_aed10 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed14 : bv 32 := 0x00000813.
Lemma F_aed14 : fetch_word Ubsan.M.loaded_segments (0xb0348 : word) = Some W_aed14.
Proof. vm_refl. Qed.
Lemma D_aed14 : decode_any W_aed14 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed18 : bv 32 := 0x8e4fc0ef.
Lemma F_aed18 : fetch_word Ubsan.M.loaded_segments (0xb034c : word) = Some W_aed18.
Proof. vm_refl. Qed.
Lemma D_aed18 : decode_any W_aed18 = Some (Jal 1 2080996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed1c : bv 32 := 0x0005051b.
Lemma F_aed1c : fetch_word Ubsan.M.loaded_segments (0xb0350 : word) = Some W_aed1c.
Proof. vm_refl. Qed.
Lemma D_aed1c : decode_any W_aed1c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed20 : bv 32 := 0x00450593.
Lemma F_aed20 : fetch_word Ubsan.M.loaded_segments (0xb0354 : word) = Some W_aed20.
Proof. vm_refl. Qed.
Lemma D_aed20 : decode_any W_aed20 = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed24 : bv 32 := 0x0015b593.
Lemma F_aed24 : fetch_word Ubsan.M.loaded_segments (0xb0358 : word) = Some W_aed24.
Proof. vm_refl. Qed.
Lemma D_aed24 : decode_any W_aed24 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed28 : bv 32 := 0xfff58593.
Lemma F_aed28 : fetch_word Ubsan.M.loaded_segments (0xb035c : word) = Some W_aed28.
Proof. vm_refl. Qed.
Lemma D_aed28 : decode_any W_aed28 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed2c : bv 32 := 0x00a5f533.
Lemma F_aed2c : fetch_word Ubsan.M.loaded_segments (0xb0360 : word) = Some W_aed2c.
Proof. vm_refl. Qed.
Lemma D_aed2c : decode_any W_aed2c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed30 : bv 32 := 0xc4dea0ef.
Lemma F_aed30 : fetch_word Ubsan.M.loaded_segments (0xb0364 : word) = Some W_aed30.
Proof. vm_refl. Qed.
Lemma D_aed30 : decode_any W_aed30 = Some (Jal 1 2010188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed34 : bv 32 := 0x0005051b.
Lemma F_aed34 : fetch_word Ubsan.M.loaded_segments (0xb0368 : word) = Some W_aed34.
Proof. vm_refl. Qed.
Lemma D_aed34 : decode_any W_aed34 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed38 : bv 32 := 0x00813083.
Lemma F_aed38 : fetch_word Ubsan.M.loaded_segments (0xb036c : word) = Some W_aed38.
Proof. vm_refl. Qed.
Lemma D_aed38 : decode_any W_aed38 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed3c : bv 32 := 0x01010113.
Lemma F_aed3c : fetch_word Ubsan.M.loaded_segments (0xb0370 : word) = Some W_aed3c.
Proof. vm_refl. Qed.
Lemma D_aed3c : decode_any W_aed3c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed40 : bv 32 := 0x00008067.
Lemma F_aed40 : fetch_word Ubsan.M.loaded_segments (0xb0374 : word) = Some W_aed40.
Proof. vm_refl. Qed.
Lemma D_aed40 : decode_any W_aed40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed50 : bv 32 := 0xff010113.
Lemma F_aed50 : fetch_word Ubsan.M.loaded_segments (0xb0384 : word) = Some W_aed50.
Proof. vm_refl. Qed.
Lemma D_aed50 : decode_any W_aed50 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed54 : bv 32 := 0x00113423.
Lemma F_aed54 : fetch_word Ubsan.M.loaded_segments (0xb0388 : word) = Some W_aed54.
Proof. vm_refl. Qed.
Lemma D_aed54 : decode_any W_aed54 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed58 : bv 32 := 0x00060693.
Lemma F_aed58 : fetch_word Ubsan.M.loaded_segments (0xb038c : word) = Some W_aed58.
Proof. vm_refl. Qed.
Lemma D_aed58 : decode_any W_aed58 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed5c : bv 32 := 0x00058613.
Lemma F_aed5c : fetch_word Ubsan.M.loaded_segments (0xb0390 : word) = Some W_aed5c.
Proof. vm_refl. Qed.
Lemma D_aed5c : decode_any W_aed5c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed60 : bv 32 := 0x00050593.
Lemma F_aed60 : fetch_word Ubsan.M.loaded_segments (0xb0394 : word) = Some W_aed60.
Proof. vm_refl. Qed.
Lemma D_aed60 : decode_any W_aed60 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed64 : bv 32 := 0x03f00513.
Lemma F_aed64 : fetch_word Ubsan.M.loaded_segments (0xb0398 : word) = Some W_aed64.
Proof. vm_refl. Qed.
Lemma D_aed64 : decode_any W_aed64 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed68 : bv 32 := 0x00000713.
Lemma F_aed68 : fetch_word Ubsan.M.loaded_segments (0xb039c : word) = Some W_aed68.
Proof. vm_refl. Qed.
Lemma D_aed68 : decode_any W_aed68 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed6c : bv 32 := 0x00000793.
Lemma F_aed6c : fetch_word Ubsan.M.loaded_segments (0xb03a0 : word) = Some W_aed6c.
Proof. vm_refl. Qed.
Lemma D_aed6c : decode_any W_aed6c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed70 : bv 32 := 0x00000813.
Lemma F_aed70 : fetch_word Ubsan.M.loaded_segments (0xb03a4 : word) = Some W_aed70.
Proof. vm_refl. Qed.
Lemma D_aed70 : decode_any W_aed70 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed74 : bv 32 := 0x888fc0ef.
Lemma F_aed74 : fetch_word Ubsan.M.loaded_segments (0xb03a8 : word) = Some W_aed74.
Proof. vm_refl. Qed.
Lemma D_aed74 : decode_any W_aed74 = Some (Jal 1 2080904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed78 : bv 32 := 0x00813083.
Lemma F_aed78 : fetch_word Ubsan.M.loaded_segments (0xb03ac : word) = Some W_aed78.
Proof. vm_refl. Qed.
Lemma D_aed78 : decode_any W_aed78 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed7c : bv 32 := 0x01010113.
Lemma F_aed7c : fetch_word Ubsan.M.loaded_segments (0xb03b0 : word) = Some W_aed7c.
Proof. vm_refl. Qed.
Lemma D_aed7c : decode_any W_aed7c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aed80 : bv 32 := 0xbfdea06f.
Lemma F_aed80 : fetch_word Ubsan.M.loaded_segments (0xb03b4 : word) = Some W_aed80.
Proof. vm_refl. Qed.
Lemma D_aed80 : decode_any W_aed80 = Some (Jal 0 2010108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aedc8 : bv 32 := 0x00008067.
Lemma F_aedc8 : fetch_word Ubsan.M.loaded_segments (0xb03fc : word) = Some W_aedc8.
Proof. vm_refl. Qed.
Lemma D_aedc8 : decode_any W_aedc8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
