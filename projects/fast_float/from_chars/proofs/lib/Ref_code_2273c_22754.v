(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2273c : bv 32 := 0x00148a83.
Lemma F_2273c : fetch_word Plain.M.loaded_segments (0x2273c : word) = Some W_2273c.
Proof. vm_refl. Qed.
Lemma D_2273c : decode_any W_2273c = Some (Load SZ1 true 21 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22740 : bv 32 := 0x0004c503.
Lemma F_22740 : fetch_word Plain.M.loaded_segments (0x22740 : word) = Some W_22740.
Proof. vm_refl. Qed.
Lemma D_22740 : decode_any W_22740 = Some (Load SZ1 false 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22744 : bv 32 := 0x039a9593.
Lemma F_22744 : fetch_word Plain.M.loaded_segments (0x22744 : word) = Some W_22744.
Proof. vm_refl. Qed.
Lemma D_22744 : decode_any W_22744 = Some (ShiftImm ALU_SLL 11 21 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22748 : bv 32 := 0x0315d593.
Lemma F_22748 : fetch_word Plain.M.loaded_segments (0x22748 : word) = Some W_22748.
Proof. vm_refl. Qed.
Lemma D_22748 : decode_any W_22748 = Some (ShiftImm ALU_SRL 11 11 49, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2274c : bv 32 := 0x00a5e933.
Lemma F_2274c : fetch_word Plain.M.loaded_segments (0x2274c : word) = Some W_2274c.
Proof. vm_refl. Qed.
Lemma D_2274c : decode_any W_2274c = Some (Op ALU_OR 18 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22750 : bv 32 := 0x00690513.
Lemma F_22750 : fetch_word Plain.M.loaded_segments (0x22750 : word) = Some W_22750.
Proof. vm_refl. Qed.
Lemma D_22750 : decode_any W_22750 = Some (OpImm ALU_ADD 10 18 6, 4%Z).
Proof. vm_refl. Qed.
