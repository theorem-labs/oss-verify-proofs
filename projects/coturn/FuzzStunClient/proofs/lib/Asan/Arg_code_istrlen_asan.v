(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_66310 : bv 32 := 0x00000593.
Lemma F_66310 : fetch_word Asan.M.loaded_segments (0x66310 : word) = Some W_66310.
Proof. vm_refl. Qed.
Lemma D_66310 : decode_any W_66310 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66314 : bv 32 := 0x00b50633.
Lemma F_66314 : fetch_word Asan.M.loaded_segments (0x66314 : word) = Some W_66314.
Proof. vm_refl. Qed.
Lemma D_66314 : decode_any W_66314 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66318 : bv 32 := 0x00064603.
Lemma F_66318 : fetch_word Asan.M.loaded_segments (0x66318 : word) = Some W_66318.
Proof. vm_refl. Qed.
Lemma D_66318 : decode_any W_66318 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6631c : bv 32 := 0x00158593.
Lemma F_6631c : fetch_word Asan.M.loaded_segments (0x6631c : word) = Some W_6631c.
Proof. vm_refl. Qed.
Lemma D_6631c : decode_any W_6631c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66320 : bv 32 := 0xfe061ae3.
Lemma F_66320 : fetch_word Asan.M.loaded_segments (0x66320 : word) = Some W_66320.
Proof. vm_refl. Qed.
Lemma D_66320 : decode_any W_66320 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66324 : bv 32 := 0xfff58513.
Lemma F_66324 : fetch_word Asan.M.loaded_segments (0x66324 : word) = Some W_66324.
Proof. vm_refl. Qed.
Lemma D_66324 : decode_any W_66324 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66328 : bv 32 := 0x00008067.
Lemma F_66328 : fetch_word Asan.M.loaded_segments (0x66328 : word) = Some W_66328.
Proof. vm_refl. Qed.
Lemma D_66328 : decode_any W_66328 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
