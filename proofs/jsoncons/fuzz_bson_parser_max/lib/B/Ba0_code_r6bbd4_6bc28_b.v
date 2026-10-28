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
Definition W_85a5c : bv 32 := 0x0013c517.
Lemma F_85a5c : fetch_word AsanUbsan.M.loaded_segments (0x85e74 : word) = Some W_85a5c.
Proof. vm_refl. Qed.
Lemma D_85a5c : decode_any W_85a5c = Some (Auipc 10 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85a60 : bv 32 := 0x02d50503.
Lemma F_85a60 : fetch_word AsanUbsan.M.loaded_segments (0x85e78 : word) = Some W_85a60.
Proof. vm_refl. Qed.
Lemma D_85a60 : decode_any W_85a60 = Some (Load SZ1 true 10 10 45, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85a64 : bv 32 := 0x00a03533.
Lemma F_85a64 : fetch_word AsanUbsan.M.loaded_segments (0x85e7c : word) = Some W_85a64.
Proof. vm_refl. Qed.
Lemma D_85a64 : decode_any W_85a64 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85a68 : bv 32 := 0x00008067.
Lemma F_85a68 : fetch_word AsanUbsan.M.loaded_segments (0x85e80 : word) = Some W_85a68.
Proof. vm_refl. Qed.
Lemma D_85a68 : decode_any W_85a68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85a84 : bv 32 := 0x0013c517.
Lemma F_85a84 : fetch_word AsanUbsan.M.loaded_segments (0x85e9c : word) = Some W_85a84.
Proof. vm_refl. Qed.
Lemma D_85a84 : decode_any W_85a84 = Some (Auipc 10 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85a88 : bv 32 := 0x00650503.
Lemma F_85a88 : fetch_word AsanUbsan.M.loaded_segments (0x85ea0 : word) = Some W_85a88.
Proof. vm_refl. Qed.
Lemma D_85a88 : decode_any W_85a88 = Some (Load SZ1 true 10 10 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85a8c : bv 32 := 0x00a03533.
Lemma F_85a8c : fetch_word AsanUbsan.M.loaded_segments (0x85ea4 : word) = Some W_85a8c.
Proof. vm_refl. Qed.
Lemma D_85a8c : decode_any W_85a8c = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85a90 : bv 32 := 0x00008067.
Lemma F_85a90 : fetch_word AsanUbsan.M.loaded_segments (0x85ea8 : word) = Some W_85a90.
Proof. vm_refl. Qed.
Lemma D_85a90 : decode_any W_85a90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
