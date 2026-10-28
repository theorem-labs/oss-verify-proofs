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
Definition W_998c4 : bv 32 := 0xfe010113.
Lemma F_998c4 : fetch_word AsanUbsan.M.loaded_segments (0x99cdc : word) = Some W_998c4.
Proof. vm_refl. Qed.
Lemma D_998c4 : decode_any W_998c4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998c8 : bv 32 := 0x00113c23.
Lemma F_998c8 : fetch_word AsanUbsan.M.loaded_segments (0x99ce0 : word) = Some W_998c8.
Proof. vm_refl. Qed.
Lemma D_998c8 : decode_any W_998c8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998cc : bv 32 := 0x00813823.
Lemma F_998cc : fetch_word AsanUbsan.M.loaded_segments (0x99ce4 : word) = Some W_998cc.
Proof. vm_refl. Qed.
Lemma D_998cc : decode_any W_998cc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998d0 : bv 32 := 0x00060593.
Lemma F_998d0 : fetch_word AsanUbsan.M.loaded_segments (0x99ce8 : word) = Some W_998d0.
Proof. vm_refl. Qed.
Lemma D_998d0 : decode_any W_998d0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998d4 : bv 32 := 0x00050413.
Lemma F_998d4 : fetch_word AsanUbsan.M.loaded_segments (0x99cec : word) = Some W_998d4.
Proof. vm_refl. Qed.
Lemma D_998d4 : decode_any W_998d4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998d8 : bv 32 := 0x00d53023.
Lemma F_998d8 : fetch_word AsanUbsan.M.loaded_segments (0x99cf0 : word) = Some W_998d8.
Proof. vm_refl. Qed.
Lemma D_998d8 : decode_any W_998d8 = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998dc : bv 32 := 0x00013423.
Lemma F_998dc : fetch_word AsanUbsan.M.loaded_segments (0x99cf4 : word) = Some W_998dc.
Proof. vm_refl. Qed.
Lemma D_998dc : decode_any W_998dc = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998e0 : bv 32 := 0x00178517.
Lemma F_998e0 : fetch_word AsanUbsan.M.loaded_segments (0x99cf8 : word) = Some W_998e0.
Proof. vm_refl. Qed.
Lemma D_998e0 : decode_any W_998e0 = Some (Auipc 10 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998e4 : bv 32 := 0xe1050513.
Lemma F_998e4 : fetch_word AsanUbsan.M.loaded_segments (0x99cfc : word) = Some W_998e4.
Proof. vm_refl. Qed.
Lemma D_998e4 : decode_any W_998e4 = Some (OpImm ALU_ADD 10 10 3600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998e8 : bv 32 := 0x00810613.
Lemma F_998e8 : fetch_word AsanUbsan.M.loaded_segments (0x99d00 : word) = Some W_998e8.
Proof. vm_refl. Qed.
Lemma D_998e8 : decode_any W_998e8 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998ec : bv 32 := 0xcc5fd0ef.
Lemma F_998ec : fetch_word AsanUbsan.M.loaded_segments (0x99d04 : word) = Some W_998ec.
Proof. vm_refl. Qed.
Lemma D_998ec : decode_any W_998ec = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998f0 : bv 32 := 0x00813583.
Lemma F_998f0 : fetch_word AsanUbsan.M.loaded_segments (0x99d08 : word) = Some W_998f0.
Proof. vm_refl. Qed.
Lemma D_998f0 : decode_any W_998f0 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998f4 : bv 32 := 0x00a42623.
Lemma F_998f4 : fetch_word AsanUbsan.M.loaded_segments (0x99d0c : word) = Some W_998f4.
Proof. vm_refl. Qed.
Lemma D_998f4 : decode_any W_998f4 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998f8 : bv 32 := 0x00059a63.
Lemma F_998f8 : fetch_word AsanUbsan.M.loaded_segments (0x99d10 : word) = Some W_998f8.
Proof. vm_refl. Qed.
Lemma D_998f8 : decode_any W_998f8 = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_998fc : bv 32 := 0x01813083.
Lemma F_998fc : fetch_word AsanUbsan.M.loaded_segments (0x99d14 : word) = Some W_998fc.
Proof. vm_refl. Qed.
Lemma D_998fc : decode_any W_998fc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99900 : bv 32 := 0x01013403.
Lemma F_99900 : fetch_word AsanUbsan.M.loaded_segments (0x99d18 : word) = Some W_99900.
Proof. vm_refl. Qed.
Lemma D_99900 : decode_any W_99900 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99904 : bv 32 := 0x02010113.
Lemma F_99904 : fetch_word AsanUbsan.M.loaded_segments (0x99d1c : word) = Some W_99904.
Proof. vm_refl. Qed.
Lemma D_99904 : decode_any W_99904 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99908 : bv 32 := 0x00008067.
Lemma F_99908 : fetch_word AsanUbsan.M.loaded_segments (0x99d20 : word) = Some W_99908.
Proof. vm_refl. Qed.
Lemma D_99908 : decode_any W_99908 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
