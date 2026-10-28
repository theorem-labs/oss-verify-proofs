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
Definition W_129f3c : bv 32 := 0x00020593.
Lemma F_129f3c : fetch_word AsanUbsan.M.loaded_segments (0x12c52c : word) = Some W_129f3c.
Proof. vm_refl. Qed.
Lemma D_129f3c : decode_any W_129f3c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_129f40 : bv 32 := 0xfa85b583.
Lemma F_129f40 : fetch_word AsanUbsan.M.loaded_segments (0x12c530 : word) = Some W_129f40.
Proof. vm_refl. Qed.
Lemma D_129f40 : decode_any W_129f40 = Some (Load SZ8 true 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_129f44 : bv 32 := 0x02051513.
Lemma F_129f44 : fetch_word AsanUbsan.M.loaded_segments (0x12c534 : word) = Some W_129f44.
Proof. vm_refl. Qed.
Lemma D_129f44 : decode_any W_129f44 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_129f48 : bv 32 := 0x01d55513.
Lemma F_129f48 : fetch_word AsanUbsan.M.loaded_segments (0x12c538 : word) = Some W_129f48.
Proof. vm_refl. Qed.
Lemma D_129f48 : decode_any W_129f48 = Some (ShiftImm ALU_SRL 10 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_129f4c : bv 32 := 0x00a58533.
Lemma F_129f4c : fetch_word AsanUbsan.M.loaded_segments (0x12c53c : word) = Some W_129f4c.
Proof. vm_refl. Qed.
Lemma D_129f4c : decode_any W_129f4c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_129f50 : bv 32 := 0x00053503.
Lemma F_129f50 : fetch_word AsanUbsan.M.loaded_segments (0x12c540 : word) = Some W_129f50.
Proof. vm_refl. Qed.
Lemma D_129f50 : decode_any W_129f50 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_129f54 : bv 32 := 0x00008067.
Lemma F_129f54 : fetch_word AsanUbsan.M.loaded_segments (0x12c544 : word) = Some W_129f54.
Proof. vm_refl. Qed.
Lemma D_129f54 : decode_any W_129f54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
