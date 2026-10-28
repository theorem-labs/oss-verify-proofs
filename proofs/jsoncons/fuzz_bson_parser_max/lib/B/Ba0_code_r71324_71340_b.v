(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8b19c : bv 32 := 0x00000593.
Lemma F_8b19c : fetch_word AsanUbsan.M.loaded_segments (0x8b5b4 : word) = Some W_8b19c.
Proof. vm_refl. Qed.
Lemma D_8b19c : decode_any W_8b19c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b1a0 : bv 32 := 0x00b50633.
Lemma F_8b1a0 : fetch_word AsanUbsan.M.loaded_segments (0x8b5b8 : word) = Some W_8b1a0.
Proof. vm_refl. Qed.
Lemma D_8b1a0 : decode_any W_8b1a0 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b1a4 : bv 32 := 0x00064603.
Lemma F_8b1a4 : fetch_word AsanUbsan.M.loaded_segments (0x8b5bc : word) = Some W_8b1a4.
Proof. vm_refl. Qed.
Lemma D_8b1a4 : decode_any W_8b1a4 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b1a8 : bv 32 := 0x00158593.
Lemma F_8b1a8 : fetch_word AsanUbsan.M.loaded_segments (0x8b5c0 : word) = Some W_8b1a8.
Proof. vm_refl. Qed.
Lemma D_8b1a8 : decode_any W_8b1a8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b1ac : bv 32 := 0xfe061ae3.
Lemma F_8b1ac : fetch_word AsanUbsan.M.loaded_segments (0x8b5c4 : word) = Some W_8b1ac.
Proof. vm_refl. Qed.
Lemma D_8b1ac : decode_any W_8b1ac = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b1b0 : bv 32 := 0xfff58513.
Lemma F_8b1b0 : fetch_word AsanUbsan.M.loaded_segments (0x8b5c8 : word) = Some W_8b1b0.
Proof. vm_refl. Qed.
Lemma D_8b1b0 : decode_any W_8b1b0 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b1b4 : bv 32 := 0x00008067.
Lemma F_8b1b4 : fetch_word AsanUbsan.M.loaded_segments (0x8b5cc : word) = Some W_8b1b4.
Proof. vm_refl. Qed.
Lemma D_8b1b4 : decode_any W_8b1b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
