(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_b4584 : bv 32 := 0x0004b503.
Lemma F_b4584 : fetch_word Asan.M.loaded_segments (0x1f254c : word) = Some W_b4584.
Proof. vm_refl. Qed.
Lemma D_b4584 : decode_any W_b4584 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b4588 : bv 32 := 0x00848493.
Lemma F_b4588 : fetch_word Asan.M.loaded_segments (0x1f2550 : word) = Some W_b4588.
Proof. vm_refl. Qed.
Lemma D_b4588 : decode_any W_b4588 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b458c : bv 32 := 0xfe051ce3.
Lemma F_b458c : fetch_word Asan.M.loaded_segments (0x1f2554 : word) = Some W_b458c.
Proof. vm_refl. Qed.
Lemma D_b458c : decode_any W_b458c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_b4640 : bv 32 := 0x00b53023.
Lemma F_b4640 : fetch_word Asan.M.loaded_segments (0x1f2608 : word) = Some W_b4640.
Proof. vm_refl. Qed.
Lemma D_b4640 : decode_any W_b4640 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b4644 : bv 32 := 0x00158593.
Lemma F_b4644 : fetch_word Asan.M.loaded_segments (0x1f260c : word) = Some W_b4644.
Proof. vm_refl. Qed.
Lemma D_b4644 : decode_any W_b4644 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b4648 : bv 32 := 0xfff5c683.
Lemma F_b4648 : fetch_word Asan.M.loaded_segments (0x1f2610 : word) = Some W_b4648.
Proof. vm_refl. Qed.
Lemma D_b4648 : decode_any W_b4648 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b464c : bv 32 := 0xfec68ae3.
Lemma F_b464c : fetch_word Asan.M.loaded_segments (0x1f2614 : word) = Some W_b464c.
Proof. vm_refl. Qed.
Lemma D_b464c : decode_any W_b464c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b4650 : bv 32 := 0xfe069ae3.
Lemma F_b4650 : fetch_word Asan.M.loaded_segments (0x1f2618 : word) = Some W_b4650.
Proof. vm_refl. Qed.
Lemma D_b4650 : decode_any W_b4650 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
