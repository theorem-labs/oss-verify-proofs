(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_56df0 : bv 32 := 0x00054583.
Lemma F_56df0 : fetch_word Ubsan.M.loaded_segments (0x58430 : word) = Some W_56df0.
Proof. vm_refl. Qed.
Lemma D_56df0 : decode_any W_56df0 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56df4 : bv 32 := 0x0015f593.
Lemma F_56df4 : fetch_word Ubsan.M.loaded_segments (0x58434 : word) = Some W_56df4.
Proof. vm_refl. Qed.
Lemma D_56df4 : decode_any W_56df4 = Some (OpImm ALU_AND 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56df8 : bv 32 := 0x00059463.
Lemma F_56df8 : fetch_word Ubsan.M.loaded_segments (0x58438 : word) = Some W_56df8.
Proof. vm_refl. Qed.
Lemma D_56df8 : decode_any W_56df8 = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56dfc : bv 32 := 0x00008067.
Lemma F_56dfc : fetch_word Ubsan.M.loaded_segments (0x5843c : word) = Some W_56dfc.
Proof. vm_refl. Qed.
Lemma D_56dfc : decode_any W_56dfc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
