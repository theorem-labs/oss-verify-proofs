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
From OSSVerify.zstd.zstd_frame_info.images Require Import Asan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_87f1c : bv 32 := 0x0004b503.
Lemma F_87f1c : fetch_word Asan.M.loaded_segments (0x87f6c : word) = Some W_87f1c.
Proof. vm_refl. Qed.
Lemma D_87f1c : decode_any W_87f1c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87f20 : bv 32 := 0x00848493.
Lemma F_87f20 : fetch_word Asan.M.loaded_segments (0x87f70 : word) = Some W_87f20.
Proof. vm_refl. Qed.
Lemma D_87f20 : decode_any W_87f20 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87f24 : bv 32 := 0xfe051ce3.
Lemma F_87f24 : fetch_word Asan.M.loaded_segments (0x87f74 : word) = Some W_87f24.
Proof. vm_refl. Qed.
Lemma D_87f24 : decode_any W_87f24 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_87fd8 : bv 32 := 0x00b53023.
Lemma F_87fd8 : fetch_word Asan.M.loaded_segments (0x88028 : word) = Some W_87fd8.
Proof. vm_refl. Qed.
Lemma D_87fd8 : decode_any W_87fd8 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fdc : bv 32 := 0x00158593.
Lemma F_87fdc : fetch_word Asan.M.loaded_segments (0x8802c : word) = Some W_87fdc.
Proof. vm_refl. Qed.
Lemma D_87fdc : decode_any W_87fdc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe0 : bv 32 := 0xfff5c683.
Lemma F_87fe0 : fetch_word Asan.M.loaded_segments (0x88030 : word) = Some W_87fe0.
Proof. vm_refl. Qed.
Lemma D_87fe0 : decode_any W_87fe0 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe4 : bv 32 := 0xfec68ae3.
Lemma F_87fe4 : fetch_word Asan.M.loaded_segments (0x88034 : word) = Some W_87fe4.
Proof. vm_refl. Qed.
Lemma D_87fe4 : decode_any W_87fe4 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe8 : bv 32 := 0xfe069ae3.
Lemma F_87fe8 : fetch_word Asan.M.loaded_segments (0x88038 : word) = Some W_87fe8.
Proof. vm_refl. Qed.
Lemma D_87fe8 : decode_any W_87fe8 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
