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
Definition W_1282cc : bv 32 := 0x00050893.
Lemma F_1282cc : fetch_word AsanUbsan.M.loaded_segments (0x12a8bc : word) = Some W_1282cc.
Proof. vm_refl. Qed.
Lemma D_1282cc : decode_any W_1282cc = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1282d0 : bv 32 := 0x00058513.
Lemma F_1282d0 : fetch_word AsanUbsan.M.loaded_segments (0x12a8c0 : word) = Some W_1282d0.
Proof. vm_refl. Qed.
Lemma D_1282d0 : decode_any W_1282d0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1282d4 : bv 32 := 0x00060593.
Lemma F_1282d4 : fetch_word AsanUbsan.M.loaded_segments (0x12a8c4 : word) = Some W_1282d4.
Proof. vm_refl. Qed.
Lemma D_1282d4 : decode_any W_1282d4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1282d8 : bv 32 := 0x00068613.
Lemma F_1282d8 : fetch_word AsanUbsan.M.loaded_segments (0x12a8c8 : word) = Some W_1282d8.
Proof. vm_refl. Qed.
Lemma D_1282d8 : decode_any W_1282d8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1282dc : bv 32 := 0x00070693.
Lemma F_1282dc : fetch_word AsanUbsan.M.loaded_segments (0x12a8cc : word) = Some W_1282dc.
Proof. vm_refl. Qed.
Lemma D_1282dc : decode_any W_1282dc = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1282e0 : bv 32 := 0x00078713.
Lemma F_1282e0 : fetch_word AsanUbsan.M.loaded_segments (0x12a8d0 : word) = Some W_1282e0.
Proof. vm_refl. Qed.
Lemma D_1282e0 : decode_any W_1282e0 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1282e4 : bv 32 := 0x00080793.
Lemma F_1282e4 : fetch_word AsanUbsan.M.loaded_segments (0x12a8d4 : word) = Some W_1282e4.
Proof. vm_refl. Qed.
Lemma D_1282e4 : decode_any W_1282e4 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1282e8 : bv 32 := 0x00000073.
Lemma F_1282e8 : fetch_word AsanUbsan.M.loaded_segments (0x12a8d8 : word) = Some W_1282e8.
Proof. vm_refl. Qed.
Lemma D_1282e8 : decode_any W_1282e8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1282e8 : is_ecall W_1282e8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1282ec : bv 32 := 0x00008067.
Lemma F_1282ec : fetch_word AsanUbsan.M.loaded_segments (0x12a8dc : word) = Some W_1282ec.
Proof. vm_refl. Qed.
Lemma D_1282ec : decode_any W_1282ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1282f0 : bv 32 := 0xfddff06f.
Lemma F_1282f0 : fetch_word AsanUbsan.M.loaded_segments (0x12a8e0 : word) = Some W_1282f0.
Proof. vm_refl. Qed.
Lemma D_1282f0 : decode_any W_1282f0 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.
