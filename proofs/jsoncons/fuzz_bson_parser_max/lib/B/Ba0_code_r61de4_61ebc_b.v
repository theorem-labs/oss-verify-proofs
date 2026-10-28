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
Definition W_7b9e0 : bv 32 := 0xfb010113.
Lemma F_7b9e0 : fetch_word AsanUbsan.M.loaded_segments (0x7bdf8 : word) = Some W_7b9e0.
Proof. vm_refl. Qed.
Lemma D_7b9e0 : decode_any W_7b9e0 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b9e4 : bv 32 := 0x04113423.
Lemma F_7b9e4 : fetch_word AsanUbsan.M.loaded_segments (0x7bdfc : word) = Some W_7b9e4.
Proof. vm_refl. Qed.
Lemma D_7b9e4 : decode_any W_7b9e4 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b9e8 : bv 32 := 0x04813023.
Lemma F_7b9e8 : fetch_word AsanUbsan.M.loaded_segments (0x7be00 : word) = Some W_7b9e8.
Proof. vm_refl. Qed.
Lemma D_7b9e8 : decode_any W_7b9e8 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b9ec : bv 32 := 0x000bb517.
Lemma F_7b9ec : fetch_word AsanUbsan.M.loaded_segments (0x7be04 : word) = Some W_7b9ec.
Proof. vm_refl. Qed.
Lemma D_7b9ec : decode_any W_7b9ec = Some (Auipc 10 187, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b9f0 : bv 32 := 0x6fc53503.
Lemma F_7b9f0 : fetch_word AsanUbsan.M.loaded_segments (0x7be08 : word) = Some W_7b9f0.
Proof. vm_refl. Qed.
Lemma D_7b9f0 : decode_any W_7b9f0 = Some (Load SZ8 true 10 10 1788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b9f4 : bv 32 := 0x0a051463.
Lemma F_7b9f4 : fetch_word AsanUbsan.M.loaded_segments (0x7be0c : word) = Some W_7b9f4.
Proof. vm_refl. Qed.
Lemma D_7b9f4 : decode_any W_7b9f4 = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ba9c : bv 32 := 0x00000513.
Lemma F_7ba9c : fetch_word AsanUbsan.M.loaded_segments (0x7beb4 : word) = Some W_7ba9c.
Proof. vm_refl. Qed.
Lemma D_7ba9c : decode_any W_7ba9c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7baa0 : bv 32 := 0x04813083.
Lemma F_7baa0 : fetch_word AsanUbsan.M.loaded_segments (0x7beb8 : word) = Some W_7baa0.
Proof. vm_refl. Qed.
Lemma D_7baa0 : decode_any W_7baa0 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7baa4 : bv 32 := 0x04013403.
Lemma F_7baa4 : fetch_word AsanUbsan.M.loaded_segments (0x7bebc : word) = Some W_7baa4.
Proof. vm_refl. Qed.
Lemma D_7baa4 : decode_any W_7baa4 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7baa8 : bv 32 := 0x05010113.
Lemma F_7baa8 : fetch_word AsanUbsan.M.loaded_segments (0x7bec0 : word) = Some W_7baa8.
Proof. vm_refl. Qed.
Lemma D_7baa8 : decode_any W_7baa8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7baac : bv 32 := 0x00008067.
Lemma F_7baac : fetch_word AsanUbsan.M.loaded_segments (0x7bec4 : word) = Some W_7baac.
Proof. vm_refl. Qed.
Lemma D_7baac : decode_any W_7baac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
