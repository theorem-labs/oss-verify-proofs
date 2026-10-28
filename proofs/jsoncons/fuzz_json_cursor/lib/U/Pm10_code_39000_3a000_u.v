(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_39088 : bv 32 := 0x000ac663.
Lemma F_39088 : fetch_word Ubsan.M.loaded_segments (0x393c0 : word) = Some W_39088.
Proof. vm_refl. Qed.
Lemma D_39088 : decode_any W_39088 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3908c : bv 32 := 0x00050413.
Lemma F_3908c : fetch_word Ubsan.M.loaded_segments (0x393c4 : word) = Some W_3908c.
Proof. vm_refl. Qed.
Lemma D_3908c : decode_any W_3908c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39090 : bv 32 := 0x0780006f.
Lemma F_39090 : fetch_word Ubsan.M.loaded_segments (0x393c8 : word) = Some W_39090.
Proof. vm_refl. Qed.
Lemma D_39090 : decode_any W_39090 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_39094 : bv 32 := 0x148000ef.
Lemma F_39094 : fetch_word Ubsan.M.loaded_segments (0x393cc : word) = Some W_39094.
Proof. vm_refl. Qed.
Lemma D_39094 : decode_any W_39094 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_39098 : bv 32 := 0x0fb00593.
Lemma F_39098 : fetch_word Ubsan.M.loaded_segments (0x393d0 : word) = Some W_39098.
Proof. vm_refl. Qed.
Lemma D_39098 : decode_any W_39098 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_3909c : bv 32 := 0x00050413.
Lemma F_3909c : fetch_word Ubsan.M.loaded_segments (0x393d4 : word) = Some W_3909c.
Proof. vm_refl. Qed.
Lemma D_3909c : decode_any W_3909c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_390a0 : bv 32 := 0x06b56463.
Lemma F_390a0 : fetch_word Ubsan.M.loaded_segments (0x393d8 : word) = Some W_390a0.
Proof. vm_refl. Qed.
Lemma D_390a0 : decode_any W_390a0 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_391dc : bv 32 := 0x00000513.
Lemma F_391dc : fetch_word Ubsan.M.loaded_segments (0x39514 : word) = Some W_391dc.
Proof. vm_refl. Qed.
Lemma D_391dc : decode_any W_391dc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_391e0 : bv 32 := 0x00008067.
Lemma F_391e0 : fetch_word Ubsan.M.loaded_segments (0x39518 : word) = Some W_391e0.
Proof. vm_refl. Qed.
Lemma D_391e0 : decode_any W_391e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3933c : bv 32 := 0x0009b517.
Lemma F_3933c : fetch_word Ubsan.M.loaded_segments (0x39674 : word) = Some W_3933c.
Proof. vm_refl. Qed.
Lemma D_3933c : decode_any W_3933c = Some (Auipc 10 155, 4%Z).
Proof. vm_refl. Qed.

Definition W_39340 : bv 32 := 0x75054503.
Lemma F_39340 : fetch_word Ubsan.M.loaded_segments (0x39678 : word) = Some W_39340.
Proof. vm_refl. Qed.
Lemma D_39340 : decode_any W_39340 = Some (Load SZ1 false 10 10 1872, 4%Z).
Proof. vm_refl. Qed.

Definition W_39344 : bv 32 := 0x00051463.
Lemma F_39344 : fetch_word Ubsan.M.loaded_segments (0x3967c : word) = Some W_39344.
Proof. vm_refl. Qed.
Lemma D_39344 : decode_any W_39344 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39348 : bv 32 := 0x00008067.
Lemma F_39348 : fetch_word Ubsan.M.loaded_segments (0x39680 : word) = Some W_39348.
Proof. vm_refl. Qed.
Lemma D_39348 : decode_any W_39348 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

