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
Definition W_8b88c : bv 32 := 0x000ac697.
Lemma F_8b88c : fetch_word AsanUbsan.M.loaded_segments (0x8bca4 : word) = Some W_8b88c.
Proof. vm_refl. Qed.
Lemma D_8b88c : decode_any W_8b88c = Some (Auipc 13 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b890 : bv 32 := 0x85c6b683.
Lemma F_8b890 : fetch_word AsanUbsan.M.loaded_segments (0x8bca8 : word) = Some W_8b890.
Proof. vm_refl. Qed.
Lemma D_8b890 : decode_any W_8b890 = Some (Load SZ8 true 13 13 2140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b894 : bv 32 := 0x00068a63.
Lemma F_8b894 : fetch_word AsanUbsan.M.loaded_segments (0x8bcac : word) = Some W_8b894.
Proof. vm_refl. Qed.
Lemma D_8b894 : decode_any W_8b894 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b898 : bv 32 := 0x00400693.
Lemma F_8b898 : fetch_word AsanUbsan.M.loaded_segments (0x8bcb0 : word) = Some W_8b898.
Proof. vm_refl. Qed.
Lemma D_8b898 : decode_any W_8b898 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b89c : bv 32 := 0x00d60663.
Lemma F_8b89c : fetch_word AsanUbsan.M.loaded_segments (0x8bcb4 : word) = Some W_8b89c.
Proof. vm_refl. Qed.
Lemma D_8b89c : decode_any W_8b89c = Some (Branch BC_EQ 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b8a8 : bv 32 := 0x0e900893.
Lemma F_8b8a8 : fetch_word AsanUbsan.M.loaded_segments (0x8bcc0 : word) = Some W_8b8a8.
Proof. vm_refl. Qed.
Lemma D_8b8a8 : decode_any W_8b8a8 = Some (OpImm ALU_ADD 17 0 233, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b8ac : bv 32 := 0x00000073.
Lemma F_8b8ac : fetch_word AsanUbsan.M.loaded_segments (0x8bcc4 : word) = Some W_8b8ac.
Proof. vm_refl. Qed.
Lemma D_8b8ac : decode_any W_8b8ac = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_8b8ac : is_ecall W_8b8ac = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_8b8b0 : bv 32 := 0x0005051b.
Lemma F_8b8b0 : fetch_word AsanUbsan.M.loaded_segments (0x8bcc8 : word) = Some W_8b8b0.
Proof. vm_refl. Qed.
Lemma D_8b8b0 : decode_any W_8b8b0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b8b4 : bv 32 := 0x00008067.
Lemma F_8b8b4 : fetch_word AsanUbsan.M.loaded_segments (0x8bccc : word) = Some W_8b8b4.
Proof. vm_refl. Qed.
Lemma D_8b8b4 : decode_any W_8b8b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
