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
Definition W_a70ac : bv 32 := 0x00091517.
Lemma F_a70ac : fetch_word AsanUbsan.M.loaded_segments (0xa74c4 : word) = Some W_a70ac.
Proof. vm_refl. Qed.
Lemma D_a70ac : decode_any W_a70ac = Some (Auipc 10 145, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70b0 : bv 32 := 0xc5c53503.
Lemma F_a70b0 : fetch_word AsanUbsan.M.loaded_segments (0xa74c8 : word) = Some W_a70b0.
Proof. vm_refl. Qed.
Lemma D_a70b0 : decode_any W_a70b0 = Some (Load SZ8 true 10 10 3164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70b4 : bv 32 := 0x00450533.
Lemma F_a70b4 : fetch_word AsanUbsan.M.loaded_segments (0xa74cc : word) = Some W_a70b4.
Proof. vm_refl. Qed.
Lemma D_a70b4 : decode_any W_a70b4 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70b8 : bv 32 := 0x00052503.
Lemma F_a70b8 : fetch_word AsanUbsan.M.loaded_segments (0xa74d0 : word) = Some W_a70b8.
Proof. vm_refl. Qed.
Lemma D_a70b8 : decode_any W_a70b8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70bc : bv 32 := 0x00a02533.
Lemma F_a70bc : fetch_word AsanUbsan.M.loaded_segments (0xa74d4 : word) = Some W_a70bc.
Proof. vm_refl. Qed.
Lemma D_a70bc : decode_any W_a70bc = Some (Op ALU_SLT 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70c0 : bv 32 := 0x00008067.
Lemma F_a70c0 : fetch_word AsanUbsan.M.loaded_segments (0xa74d8 : word) = Some W_a70c0.
Proof. vm_refl. Qed.
Lemma D_a70c0 : decode_any W_a70c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
