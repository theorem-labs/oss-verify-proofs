(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.zstd.zstd_frame_info.images Require Import AsanUbsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_88100 : bv 32 := 0x0004b503.
Lemma F_88100 : fetch_word AsanUbsan.M.loaded_segments (0x88148 : word) = Some W_88100.
Proof. vm_refl. Qed.
Lemma D_88100 : decode_any W_88100 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88104 : bv 32 := 0x00848493.
Lemma F_88104 : fetch_word AsanUbsan.M.loaded_segments (0x8814c : word) = Some W_88104.
Proof. vm_refl. Qed.
Lemma D_88104 : decode_any W_88104 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88108 : bv 32 := 0xfe051ce3.
Lemma F_88108 : fetch_word AsanUbsan.M.loaded_segments (0x88150 : word) = Some W_88108.
Proof. vm_refl. Qed.
Lemma D_88108 : decode_any W_88108 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_881bc : bv 32 := 0x00b53023.
Lemma F_881bc : fetch_word AsanUbsan.M.loaded_segments (0x88204 : word) = Some W_881bc.
Proof. vm_refl. Qed.
Lemma D_881bc : decode_any W_881bc = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_881c0 : bv 32 := 0x00158593.
Lemma F_881c0 : fetch_word AsanUbsan.M.loaded_segments (0x88208 : word) = Some W_881c0.
Proof. vm_refl. Qed.
Lemma D_881c0 : decode_any W_881c0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_881c4 : bv 32 := 0xfff5c683.
Lemma F_881c4 : fetch_word AsanUbsan.M.loaded_segments (0x8820c : word) = Some W_881c4.
Proof. vm_refl. Qed.
Lemma D_881c4 : decode_any W_881c4 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_881c8 : bv 32 := 0xfec68ae3.
Lemma F_881c8 : fetch_word AsanUbsan.M.loaded_segments (0x88210 : word) = Some W_881c8.
Proof. vm_refl. Qed.
Lemma D_881c8 : decode_any W_881c8 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_881cc : bv 32 := 0xfe069ae3.
Lemma F_881cc : fetch_word AsanUbsan.M.loaded_segments (0x88214 : word) = Some W_881cc.
Proof. vm_refl. Qed.
Lemma D_881cc : decode_any W_881cc = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
