(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8b000 : bv 32 := 0x02850583.
Lemma F_8b000 : fetch_word AsanUbsan.M.loaded_segments (0x8b048 : word) = Some W_8b000.
Proof. vm_refl. Qed.
Lemma D_8b000 : decode_any W_8b000 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b004 : bv 32 := 0x0230000f.
Lemma F_8b004 : fetch_word AsanUbsan.M.loaded_segments (0x8b04c : word) = Some W_8b004.
Proof. vm_refl. Qed.
Lemma D_8b004 : decode_any W_8b004 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b008 : bv 32 := 0x02058c63.
Lemma F_8b008 : fetch_word AsanUbsan.M.loaded_segments (0x8b050 : word) = Some W_8b008.
Proof. vm_refl. Qed.
Lemma D_8b008 : decode_any W_8b008 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b040 : bv 32 := 0x00853583.
Lemma F_8b040 : fetch_word AsanUbsan.M.loaded_segments (0x8b088 : word) = Some W_8b040.
Proof. vm_refl. Qed.
Lemma D_8b040 : decode_any W_8b040 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b044 : bv 32 := 0x01053503.
Lemma F_8b044 : fetch_word AsanUbsan.M.loaded_segments (0x8b08c : word) = Some W_8b044.
Proof. vm_refl. Qed.
Lemma D_8b044 : decode_any W_8b044 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b048 : bv 32 := 0x00b53533.
Lemma F_8b048 : fetch_word AsanUbsan.M.loaded_segments (0x8b090 : word) = Some W_8b048.
Proof. vm_refl. Qed.
Lemma D_8b048 : decode_any W_8b048 = Some (Op ALU_SLTU 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b04c : bv 32 := 0x40a00533.
Lemma F_8b04c : fetch_word AsanUbsan.M.loaded_segments (0x8b094 : word) = Some W_8b04c.
Proof. vm_refl. Qed.
Lemma D_8b04c : decode_any W_8b04c = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b050 : bv 32 := 0x00b57533.
Lemma F_8b050 : fetch_word AsanUbsan.M.loaded_segments (0x8b098 : word) = Some W_8b050.
Proof. vm_refl. Qed.
Lemma D_8b050 : decode_any W_8b050 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b054 : bv 32 := 0x00008067.
Lemma F_8b054 : fetch_word AsanUbsan.M.loaded_segments (0x8b09c : word) = Some W_8b054.
Proof. vm_refl. Qed.
Lemma D_8b054 : decode_any W_8b054 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b058 : bv 32 := 0x02850583.
Lemma F_8b058 : fetch_word AsanUbsan.M.loaded_segments (0x8b0a0 : word) = Some W_8b058.
Proof. vm_refl. Qed.
Lemma D_8b058 : decode_any W_8b058 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b05c : bv 32 := 0x0230000f.
Lemma F_8b05c : fetch_word AsanUbsan.M.loaded_segments (0x8b0a4 : word) = Some W_8b05c.
Proof. vm_refl. Qed.
Lemma D_8b05c : decode_any W_8b05c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b060 : bv 32 := 0x02058c63.
Lemma F_8b060 : fetch_word AsanUbsan.M.loaded_segments (0x8b0a8 : word) = Some W_8b060.
Proof. vm_refl. Qed.
Lemma D_8b060 : decode_any W_8b060 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b098 : bv 32 := 0x00853583.
Lemma F_8b098 : fetch_word AsanUbsan.M.loaded_segments (0x8b0e0 : word) = Some W_8b098.
Proof. vm_refl. Qed.
Lemma D_8b098 : decode_any W_8b098 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b09c : bv 32 := 0x01053503.
Lemma F_8b09c : fetch_word AsanUbsan.M.loaded_segments (0x8b0e4 : word) = Some W_8b09c.
Proof. vm_refl. Qed.
Lemma D_8b09c : decode_any W_8b09c = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b0a0 : bv 32 := 0x00b535b3.
Lemma F_8b0a0 : fetch_word AsanUbsan.M.loaded_segments (0x8b0e8 : word) = Some W_8b0a0.
Proof. vm_refl. Qed.
Lemma D_8b0a0 : decode_any W_8b0a0 = Some (Op ALU_SLTU 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b0a4 : bv 32 := 0x40b005b3.
Lemma F_8b0a4 : fetch_word AsanUbsan.M.loaded_segments (0x8b0ec : word) = Some W_8b0a4.
Proof. vm_refl. Qed.
Lemma D_8b0a4 : decode_any W_8b0a4 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b0a8 : bv 32 := 0x00a5f533.
Lemma F_8b0a8 : fetch_word AsanUbsan.M.loaded_segments (0x8b0f0 : word) = Some W_8b0a8.
Proof. vm_refl. Qed.
Lemma D_8b0a8 : decode_any W_8b0a8 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b0ac : bv 32 := 0x00008067.
Lemma F_8b0ac : fetch_word AsanUbsan.M.loaded_segments (0x8b0f4 : word) = Some W_8b0ac.
Proof. vm_refl. Qed.
Lemma D_8b0ac : decode_any W_8b0ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

