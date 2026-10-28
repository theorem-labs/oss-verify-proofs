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
Definition W_8b844 : bv 32 := 0xfffff637.
Lemma F_8b844 : fetch_word AsanUbsan.M.loaded_segments (0x8bc5c : word) = Some W_8b844.
Proof. vm_refl. Qed.
Lemma D_8b844 : decode_any W_8b844 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b848 : bv 32 := 0x0016069b.
Lemma F_8b848 : fetch_word AsanUbsan.M.loaded_segments (0x8bc60 : word) = Some W_8b848.
Proof. vm_refl. Qed.
Lemma D_8b848 : decode_any W_8b848 = Some (OpImm32 13 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b84c : bv 32 := 0x00d56863.
Lemma F_8b84c : fetch_word AsanUbsan.M.loaded_segments (0x8bc64 : word) = Some W_8b84c.
Proof. vm_refl. Qed.
Lemma D_8b84c : decode_any W_8b84c = Some (Branch BC_LTU 10 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b85c : bv 32 := 0x00a63533.
Lemma F_8b85c : fetch_word AsanUbsan.M.loaded_segments (0x8bc74 : word) = Some W_8b85c.
Proof. vm_refl. Qed.
Lemma D_8b85c : decode_any W_8b85c = Some (Op ALU_SLTU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b860 : bv 32 := 0x00008067.
Lemma F_8b860 : fetch_word AsanUbsan.M.loaded_segments (0x8bc78 : word) = Some W_8b860.
Proof. vm_refl. Qed.
Lemma D_8b860 : decode_any W_8b860 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b864 : bv 32 := 0x0de00893.
Lemma F_8b864 : fetch_word AsanUbsan.M.loaded_segments (0x8bc7c : word) = Some W_8b864.
Proof. vm_refl. Qed.
Lemma D_8b864 : decode_any W_8b864 = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b868 : bv 32 := 0x00000073.
Lemma F_8b868 : fetch_word AsanUbsan.M.loaded_segments (0x8bc80 : word) = Some W_8b868.
Proof. vm_refl. Qed.
Lemma D_8b868 : decode_any W_8b868 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_8b868 : is_ecall W_8b868 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_8b86c : bv 32 := 0x00008067.
Lemma F_8b86c : fetch_word AsanUbsan.M.loaded_segments (0x8bc84 : word) = Some W_8b86c.
Proof. vm_refl. Qed.
Lemma D_8b86c : decode_any W_8b86c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b870 : bv 32 := 0x0d700893.
Lemma F_8b870 : fetch_word AsanUbsan.M.loaded_segments (0x8bc88 : word) = Some W_8b870.
Proof. vm_refl. Qed.
Lemma D_8b870 : decode_any W_8b870 = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b874 : bv 32 := 0x00000073.
Lemma F_8b874 : fetch_word AsanUbsan.M.loaded_segments (0x8bc8c : word) = Some W_8b874.
Proof. vm_refl. Qed.
Lemma D_8b874 : decode_any W_8b874 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_8b874 : is_ecall W_8b874 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_8b878 : bv 32 := 0x00008067.
Lemma F_8b878 : fetch_word AsanUbsan.M.loaded_segments (0x8bc90 : word) = Some W_8b878.
Proof. vm_refl. Qed.
Lemma D_8b878 : decode_any W_8b878 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
