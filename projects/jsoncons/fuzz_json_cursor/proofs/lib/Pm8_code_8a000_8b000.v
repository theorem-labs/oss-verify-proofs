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

Definition W_8aa74 : bv 32 := 0xff010113.
Lemma F_8aa74 : fetch_word Asan.M.loaded_segments (0x8aac4 : word) = Some W_8aa74.
Proof. vm_refl. Qed.
Lemma D_8aa74 : decode_any W_8aa74 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa78 : bv 32 := 0x00113423.
Lemma F_8aa78 : fetch_word Asan.M.loaded_segments (0x8aac8 : word) = Some W_8aa78.
Proof. vm_refl. Qed.
Lemma D_8aa78 : decode_any W_8aa78 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa7c : bv 32 := 0xe78f80ef.
Lemma F_8aa7c : fetch_word Asan.M.loaded_segments (0x8aacc : word) = Some W_8aa7c.
Proof. vm_refl. Qed.
Lemma D_8aa7c : decode_any W_8aa7c = Some (Jal 1 2066040, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa80 : bv 32 := 0x00050463.
Lemma F_8aa80 : fetch_word Asan.M.loaded_segments (0x8aad0 : word) = Some W_8aa80.
Proof. vm_refl. Qed.
Lemma D_8aa80 : decode_any W_8aa80 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa84 : bv 32 := 0x09853503.
Lemma F_8aa84 : fetch_word Asan.M.loaded_segments (0x8aad4 : word) = Some W_8aa84.
Proof. vm_refl. Qed.
Lemma D_8aa84 : decode_any W_8aa84 = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa88 : bv 32 := 0x00813083.
Lemma F_8aa88 : fetch_word Asan.M.loaded_segments (0x8aad8 : word) = Some W_8aa88.
Proof. vm_refl. Qed.
Lemma D_8aa88 : decode_any W_8aa88 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa8c : bv 32 := 0x01010113.
Lemma F_8aa8c : fetch_word Asan.M.loaded_segments (0x8aadc : word) = Some W_8aa8c.
Proof. vm_refl. Qed.
Lemma D_8aa8c : decode_any W_8aa8c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa90 : bv 32 := 0x00008067.
Lemma F_8aa90 : fetch_word Asan.M.loaded_segments (0x8aae0 : word) = Some W_8aa90.
Proof. vm_refl. Qed.
Lemma D_8aa90 : decode_any W_8aa90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac38 : bv 32 := 0x02850583.
Lemma F_8ac38 : fetch_word Asan.M.loaded_segments (0x8ac88 : word) = Some W_8ac38.
Proof. vm_refl. Qed.
Lemma D_8ac38 : decode_any W_8ac38 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac3c : bv 32 := 0x0230000f.
Lemma F_8ac3c : fetch_word Asan.M.loaded_segments (0x8ac8c : word) = Some W_8ac3c.
Proof. vm_refl. Qed.
Lemma D_8ac3c : decode_any W_8ac3c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac40 : bv 32 := 0x02058c63.
Lemma F_8ac40 : fetch_word Asan.M.loaded_segments (0x8ac90 : word) = Some W_8ac40.
Proof. vm_refl. Qed.
Lemma D_8ac40 : decode_any W_8ac40 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac78 : bv 32 := 0x00853583.
Lemma F_8ac78 : fetch_word Asan.M.loaded_segments (0x8acc8 : word) = Some W_8ac78.
Proof. vm_refl. Qed.
Lemma D_8ac78 : decode_any W_8ac78 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac7c : bv 32 := 0x01053503.
Lemma F_8ac7c : fetch_word Asan.M.loaded_segments (0x8accc : word) = Some W_8ac7c.
Proof. vm_refl. Qed.
Lemma D_8ac7c : decode_any W_8ac7c = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac80 : bv 32 := 0x00b53533.
Lemma F_8ac80 : fetch_word Asan.M.loaded_segments (0x8acd0 : word) = Some W_8ac80.
Proof. vm_refl. Qed.
Lemma D_8ac80 : decode_any W_8ac80 = Some (Op ALU_SLTU 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac84 : bv 32 := 0x40a00533.
Lemma F_8ac84 : fetch_word Asan.M.loaded_segments (0x8acd4 : word) = Some W_8ac84.
Proof. vm_refl. Qed.
Lemma D_8ac84 : decode_any W_8ac84 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac88 : bv 32 := 0x00b57533.
Lemma F_8ac88 : fetch_word Asan.M.loaded_segments (0x8acd8 : word) = Some W_8ac88.
Proof. vm_refl. Qed.
Lemma D_8ac88 : decode_any W_8ac88 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac8c : bv 32 := 0x00008067.
Lemma F_8ac8c : fetch_word Asan.M.loaded_segments (0x8acdc : word) = Some W_8ac8c.
Proof. vm_refl. Qed.
Lemma D_8ac8c : decode_any W_8ac8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac90 : bv 32 := 0x02850583.
Lemma F_8ac90 : fetch_word Asan.M.loaded_segments (0x8ace0 : word) = Some W_8ac90.
Proof. vm_refl. Qed.
Lemma D_8ac90 : decode_any W_8ac90 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac94 : bv 32 := 0x0230000f.
Lemma F_8ac94 : fetch_word Asan.M.loaded_segments (0x8ace4 : word) = Some W_8ac94.
Proof. vm_refl. Qed.
Lemma D_8ac94 : decode_any W_8ac94 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ac98 : bv 32 := 0x02058c63.
Lemma F_8ac98 : fetch_word Asan.M.loaded_segments (0x8ace8 : word) = Some W_8ac98.
Proof. vm_refl. Qed.
Lemma D_8ac98 : decode_any W_8ac98 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8acd0 : bv 32 := 0x00853583.
Lemma F_8acd0 : fetch_word Asan.M.loaded_segments (0x8ad20 : word) = Some W_8acd0.
Proof. vm_refl. Qed.
Lemma D_8acd0 : decode_any W_8acd0 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8acd4 : bv 32 := 0x01053503.
Lemma F_8acd4 : fetch_word Asan.M.loaded_segments (0x8ad24 : word) = Some W_8acd4.
Proof. vm_refl. Qed.
Lemma D_8acd4 : decode_any W_8acd4 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8acd8 : bv 32 := 0x00b535b3.
Lemma F_8acd8 : fetch_word Asan.M.loaded_segments (0x8ad28 : word) = Some W_8acd8.
Proof. vm_refl. Qed.
Lemma D_8acd8 : decode_any W_8acd8 = Some (Op ALU_SLTU 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8acdc : bv 32 := 0x40b005b3.
Lemma F_8acdc : fetch_word Asan.M.loaded_segments (0x8ad2c : word) = Some W_8acdc.
Proof. vm_refl. Qed.
Lemma D_8acdc : decode_any W_8acdc = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ace0 : bv 32 := 0x00a5f533.
Lemma F_8ace0 : fetch_word Asan.M.loaded_segments (0x8ad30 : word) = Some W_8ace0.
Proof. vm_refl. Qed.
Lemma D_8ace0 : decode_any W_8ace0 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ace4 : bv 32 := 0x00008067.
Lemma F_8ace4 : fetch_word Asan.M.loaded_segments (0x8ad34 : word) = Some W_8ace4.
Proof. vm_refl. Qed.
Lemma D_8ace4 : decode_any W_8ace4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

