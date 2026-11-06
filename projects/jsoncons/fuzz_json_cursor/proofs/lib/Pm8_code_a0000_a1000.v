(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a0e6c : bv 32 := 0xfe010113.
Lemma F_a0e6c : fetch_word Asan.M.loaded_segments (0xa0ebc : word) = Some W_a0e6c.
Proof. vm_refl. Qed.
Lemma D_a0e6c : decode_any W_a0e6c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e70 : bv 32 := 0x00113c23.
Lemma F_a0e70 : fetch_word Asan.M.loaded_segments (0xa0ec0 : word) = Some W_a0e70.
Proof. vm_refl. Qed.
Lemma D_a0e70 : decode_any W_a0e70 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e74 : bv 32 := 0x00813823.
Lemma F_a0e74 : fetch_word Asan.M.loaded_segments (0xa0ec4 : word) = Some W_a0e74.
Proof. vm_refl. Qed.
Lemma D_a0e74 : decode_any W_a0e74 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e78 : bv 32 := 0x00060593.
Lemma F_a0e78 : fetch_word Asan.M.loaded_segments (0xa0ec8 : word) = Some W_a0e78.
Proof. vm_refl. Qed.
Lemma D_a0e78 : decode_any W_a0e78 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e7c : bv 32 := 0x00050413.
Lemma F_a0e7c : fetch_word Asan.M.loaded_segments (0xa0ecc : word) = Some W_a0e7c.
Proof. vm_refl. Qed.
Lemma D_a0e7c : decode_any W_a0e7c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e80 : bv 32 := 0x00d53023.
Lemma F_a0e80 : fetch_word Asan.M.loaded_segments (0xa0ed0 : word) = Some W_a0e80.
Proof. vm_refl. Qed.
Lemma D_a0e80 : decode_any W_a0e80 = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e84 : bv 32 := 0x00013423.
Lemma F_a0e84 : fetch_word Asan.M.loaded_segments (0xa0ed4 : word) = Some W_a0e84.
Proof. vm_refl. Qed.
Lemma D_a0e84 : decode_any W_a0e84 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e88 : bv 32 := 0x0018e517.
Lemma F_a0e88 : fetch_word Asan.M.loaded_segments (0xa0ed8 : word) = Some W_a0e88.
Proof. vm_refl. Qed.
Lemma D_a0e88 : decode_any W_a0e88 = Some (Auipc 10 398, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e8c : bv 32 := 0x9b050513.
Lemma F_a0e8c : fetch_word Asan.M.loaded_segments (0xa0edc : word) = Some W_a0e8c.
Proof. vm_refl. Qed.
Lemma D_a0e8c : decode_any W_a0e8c = Some (OpImm ALU_ADD 10 10 2480, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e90 : bv 32 := 0x00810613.
Lemma F_a0e90 : fetch_word Asan.M.loaded_segments (0xa0ee0 : word) = Some W_a0e90.
Proof. vm_refl. Qed.
Lemma D_a0e90 : decode_any W_a0e90 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e94 : bv 32 := 0xcc5fd0ef.
Lemma F_a0e94 : fetch_word Asan.M.loaded_segments (0xa0ee4 : word) = Some W_a0e94.
Proof. vm_refl. Qed.
Lemma D_a0e94 : decode_any W_a0e94 = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e98 : bv 32 := 0x00813583.
Lemma F_a0e98 : fetch_word Asan.M.loaded_segments (0xa0ee8 : word) = Some W_a0e98.
Proof. vm_refl. Qed.
Lemma D_a0e98 : decode_any W_a0e98 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0e9c : bv 32 := 0x00a42623.
Lemma F_a0e9c : fetch_word Asan.M.loaded_segments (0xa0eec : word) = Some W_a0e9c.
Proof. vm_refl. Qed.
Lemma D_a0e9c : decode_any W_a0e9c = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ea0 : bv 32 := 0x00059a63.
Lemma F_a0ea0 : fetch_word Asan.M.loaded_segments (0xa0ef0 : word) = Some W_a0ea0.
Proof. vm_refl. Qed.
Lemma D_a0ea0 : decode_any W_a0ea0 = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ea4 : bv 32 := 0x01813083.
Lemma F_a0ea4 : fetch_word Asan.M.loaded_segments (0xa0ef4 : word) = Some W_a0ea4.
Proof. vm_refl. Qed.
Lemma D_a0ea4 : decode_any W_a0ea4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ea8 : bv 32 := 0x01013403.
Lemma F_a0ea8 : fetch_word Asan.M.loaded_segments (0xa0ef8 : word) = Some W_a0ea8.
Proof. vm_refl. Qed.
Lemma D_a0ea8 : decode_any W_a0ea8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0eac : bv 32 := 0x02010113.
Lemma F_a0eac : fetch_word Asan.M.loaded_segments (0xa0efc : word) = Some W_a0eac.
Proof. vm_refl. Qed.
Lemma D_a0eac : decode_any W_a0eac = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0eb0 : bv 32 := 0x00008067.
Lemma F_a0eb0 : fetch_word Asan.M.loaded_segments (0xa0f00 : word) = Some W_a0eb0.
Proof. vm_refl. Qed.
Lemma D_a0eb0 : decode_any W_a0eb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

