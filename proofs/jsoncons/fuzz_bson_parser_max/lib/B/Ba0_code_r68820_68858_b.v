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
Definition W_82698 : bv 32 := 0xff010113.
Lemma F_82698 : fetch_word AsanUbsan.M.loaded_segments (0x82ab0 : word) = Some W_82698.
Proof. vm_refl. Qed.
Lemma D_82698 : decode_any W_82698 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8269c : bv 32 := 0x00113423.
Lemma F_8269c : fetch_word AsanUbsan.M.loaded_segments (0x82ab4 : word) = Some W_8269c.
Proof. vm_refl. Qed.
Lemma D_8269c : decode_any W_8269c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826a0 : bv 32 := 0x62d000ef.
Lemma F_826a0 : fetch_word AsanUbsan.M.loaded_segments (0x82ab8 : word) = Some W_826a0.
Proof. vm_refl. Qed.
Lemma D_826a0 : decode_any W_826a0 = Some (Jal 1 3628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826a4 : bv 32 := 0x00050c63.
Lemma F_826a4 : fetch_word AsanUbsan.M.loaded_segments (0x82abc : word) = Some W_826a4.
Proof. vm_refl. Qed.
Lemma D_826a4 : decode_any W_826a4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826a8 : bv 32 := 0x7ff50513.
Lemma F_826a8 : fetch_word AsanUbsan.M.loaded_segments (0x82ac0 : word) = Some W_826a8.
Proof. vm_refl. Qed.
Lemma D_826a8 : decode_any W_826a8 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826ac : bv 32 := 0x2f150513.
Lemma F_826ac : fetch_word AsanUbsan.M.loaded_segments (0x82ac4 : word) = Some W_826ac.
Proof. vm_refl. Qed.
Lemma D_826ac : decode_any W_826ac = Some (OpImm ALU_ADD 10 10 753, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826b0 : bv 32 := 0x00813083.
Lemma F_826b0 : fetch_word AsanUbsan.M.loaded_segments (0x82ac8 : word) = Some W_826b0.
Proof. vm_refl. Qed.
Lemma D_826b0 : decode_any W_826b0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826b4 : bv 32 := 0x01010113.
Lemma F_826b4 : fetch_word AsanUbsan.M.loaded_segments (0x82acc : word) = Some W_826b4.
Proof. vm_refl. Qed.
Lemma D_826b4 : decode_any W_826b4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826b8 : bv 32 := 0x00008067.
Lemma F_826b8 : fetch_word AsanUbsan.M.loaded_segments (0x82ad0 : word) = Some W_826b8.
Proof. vm_refl. Qed.
Lemma D_826b8 : decode_any W_826b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
