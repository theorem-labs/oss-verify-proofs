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
Definition W_957b4 : bv 32 := 0xfe010113.
Lemma F_957b4 : fetch_word AsanUbsan.M.loaded_segments (0x95bcc : word) = Some W_957b4.
Proof. vm_refl. Qed.
Lemma D_957b4 : decode_any W_957b4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95900 : bv 32 := 0x00058513.
Lemma F_95900 : fetch_word AsanUbsan.M.loaded_segments (0x95d18 : word) = Some W_95900.
Proof. vm_refl. Qed.
Lemma D_95900 : decode_any W_95900 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95904 : bv 32 := 0x00060593.
Lemma F_95904 : fetch_word AsanUbsan.M.loaded_segments (0x95d1c : word) = Some W_95904.
Proof. vm_refl. Qed.
Lemma D_95904 : decode_any W_95904 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95908 : bv 32 := 0x00068613.
Lemma F_95908 : fetch_word AsanUbsan.M.loaded_segments (0x95d20 : word) = Some W_95908.
Proof. vm_refl. Qed.
Lemma D_95908 : decode_any W_95908 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9590c : bv 32 := 0xc65f706f.
Lemma F_9590c : fetch_word AsanUbsan.M.loaded_segments (0x95d24 : word) = Some W_9590c.
Proof. vm_refl. Qed.
Lemma D_9590c : decode_any W_9590c = Some (Jal 0 2063460, 4%Z).
Proof. vm_refl. Qed.
