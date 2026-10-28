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
Definition W_aa250 : bv 32 := 0x08b50663.
Lemma F_aa250 : fetch_word Ubsan.M.loaded_segments (0xab884 : word) = Some W_aa250.
Proof. vm_refl. Qed.
Lemma D_aa250 : decode_any W_aa250 = Some (Branch BC_EQ 10 11 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa254 : bv 32 := 0x00a606b3.
Lemma F_aa254 : fetch_word Ubsan.M.loaded_segments (0xab888 : word) = Some W_aa254.
Proof. vm_refl. Qed.
Lemma D_aa254 : decode_any W_aa254 = Some (Op ALU_ADD 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa258 : bv 32 := 0x00161713.
Lemma F_aa258 : fetch_word Ubsan.M.loaded_segments (0xab88c : word) = Some W_aa258.
Proof. vm_refl. Qed.
Lemma D_aa258 : decode_any W_aa258 = Some (ShiftImm ALU_SLL 14 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa25c : bv 32 := 0x40d586b3.
Lemma F_aa25c : fetch_word Ubsan.M.loaded_segments (0xab890 : word) = Some W_aa25c.
Proof. vm_refl. Qed.
Lemma D_aa25c : decode_any W_aa25c = Some (Op ALU_SUB 13 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa260 : bv 32 := 0x40e00733.
Lemma F_aa260 : fetch_word Ubsan.M.loaded_segments (0xab894 : word) = Some W_aa260.
Proof. vm_refl. Qed.
Lemma D_aa260 : decode_any W_aa260 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa264 : bv 32 := 0x04d77063.
Lemma F_aa264 : fetch_word Ubsan.M.loaded_segments (0xab898 : word) = Some W_aa264.
Proof. vm_refl. Qed.
Lemma D_aa264 : decode_any W_aa264 = Some (Branch BC_GEU 14 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa268 : bv 32 := 0x00a5c6b3.
Lemma F_aa268 : fetch_word Ubsan.M.loaded_segments (0xab89c : word) = Some W_aa268.
Proof. vm_refl. Qed.
Lemma D_aa268 : decode_any W_aa268 = Some (Op ALU_XOR 13 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa26c : bv 32 := 0x0076f693.
Lemma F_aa26c : fetch_word Ubsan.M.loaded_segments (0xab8a0 : word) = Some W_aa26c.
Proof. vm_refl. Qed.
Lemma D_aa26c : decode_any W_aa26c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa270 : bv 32 := 0x02b57c63.
Lemma F_aa270 : fetch_word Ubsan.M.loaded_segments (0xab8a4 : word) = Some W_aa270.
Proof. vm_refl. Qed.
Lemma D_aa270 : decode_any W_aa270 = Some (Branch BC_GEU 10 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa274 : bv 32 := 0x06068663.
Lemma F_aa274 : fetch_word Ubsan.M.loaded_segments (0xab8a8 : word) = Some W_aa274.
Proof. vm_refl. Qed.
Lemma D_aa274 : decode_any W_aa274 = Some (Branch BC_EQ 13 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa278 : bv 32 := 0x00050693.
Lemma F_aa278 : fetch_word Ubsan.M.loaded_segments (0xab8ac : word) = Some W_aa278.
Proof. vm_refl. Qed.
Lemma D_aa278 : decode_any W_aa278 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa27c : bv 32 := 0x00058713.
Lemma F_aa27c : fetch_word Ubsan.M.loaded_segments (0xab8b0 : word) = Some W_aa27c.
Proof. vm_refl. Qed.
Lemma D_aa27c : decode_any W_aa27c = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa280 : bv 32 := 0x04060e63.
Lemma F_aa280 : fetch_word Ubsan.M.loaded_segments (0xab8b4 : word) = Some W_aa280.
Proof. vm_refl. Qed.
Lemma D_aa280 : decode_any W_aa280 = Some (Branch BC_EQ 12 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa284 : bv 32 := 0x00c68633.
Lemma F_aa284 : fetch_word Ubsan.M.loaded_segments (0xab8b8 : word) = Some W_aa284.
Proof. vm_refl. Qed.
Lemma D_aa284 : decode_any W_aa284 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa288 : bv 32 := 0x00074583.
Lemma F_aa288 : fetch_word Ubsan.M.loaded_segments (0xab8bc : word) = Some W_aa288.
Proof. vm_refl. Qed.
Lemma D_aa288 : decode_any W_aa288 = Some (Load SZ1 false 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa28c : bv 32 := 0x00170713.
Lemma F_aa28c : fetch_word Ubsan.M.loaded_segments (0xab8c0 : word) = Some W_aa28c.
Proof. vm_refl. Qed.
Lemma D_aa28c : decode_any W_aa28c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa290 : bv 32 := 0x00168793.
Lemma F_aa290 : fetch_word Ubsan.M.loaded_segments (0xab8c4 : word) = Some W_aa290.
Proof. vm_refl. Qed.
Lemma D_aa290 : decode_any W_aa290 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa294 : bv 32 := 0x00b68023.
Lemma F_aa294 : fetch_word Ubsan.M.loaded_segments (0xab8c8 : word) = Some W_aa294.
Proof. vm_refl. Qed.
Lemma D_aa294 : decode_any W_aa294 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa298 : bv 32 := 0x00078693.
Lemma F_aa298 : fetch_word Ubsan.M.loaded_segments (0xab8cc : word) = Some W_aa298.
Proof. vm_refl. Qed.
Lemma D_aa298 : decode_any W_aa298 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa29c : bv 32 := 0xfec796e3.
Lemma F_aa29c : fetch_word Ubsan.M.loaded_segments (0xab8d0 : word) = Some W_aa29c.
Proof. vm_refl. Qed.
Lemma D_aa29c : decode_any W_aa29c = Some (Branch BC_NE 15 12 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa2a0 : bv 32 := 0x03c0006f.
Lemma F_aa2a0 : fetch_word Ubsan.M.loaded_segments (0xab8d4 : word) = Some W_aa2a0.
Proof. vm_refl. Qed.
Lemma D_aa2a0 : decode_any W_aa2a0 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa2a4 : bv 32 := 0xba9ff06f.
Lemma F_aa2a4 : fetch_word Ubsan.M.loaded_segments (0xab8d8 : word) = Some W_aa2a4.
Proof. vm_refl. Qed.
Lemma D_aa2a4 : decode_any W_aa2a4 = Some (Jal 0 2096040, 4%Z).
Proof. vm_refl. Qed.
