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

Definition W_14b8c4 : bv 32 := 0xff010113.
Lemma F_14b8c4 : fetch_word Asan.M.loaded_segments (0x14b908 : word) = Some W_14b8c4.
Proof. vm_refl. Qed.
Lemma D_14b8c4 : decode_any W_14b8c4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8c8 : bv 32 := 0x00113423.
Lemma F_14b8c8 : fetch_word Asan.M.loaded_segments (0x14b90c : word) = Some W_14b8c8.
Proof. vm_refl. Qed.
Lemma D_14b8c8 : decode_any W_14b8c8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8cc : bv 32 := 0x00060693.
Lemma F_14b8cc : fetch_word Asan.M.loaded_segments (0x14b910 : word) = Some W_14b8cc.
Proof. vm_refl. Qed.
Lemma D_14b8cc : decode_any W_14b8cc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8d0 : bv 32 := 0x00058613.
Lemma F_14b8d0 : fetch_word Asan.M.loaded_segments (0x14b914 : word) = Some W_14b8d0.
Proof. vm_refl. Qed.
Lemma D_14b8d0 : decode_any W_14b8d0 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8d4 : bv 32 := 0x00050593.
Lemma F_14b8d4 : fetch_word Asan.M.loaded_segments (0x14b918 : word) = Some W_14b8d4.
Proof. vm_refl. Qed.
Lemma D_14b8d4 : decode_any W_14b8d4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8d8 : bv 32 := 0x03f00513.
Lemma F_14b8d8 : fetch_word Asan.M.loaded_segments (0x14b91c : word) = Some W_14b8d8.
Proof. vm_refl. Qed.
Lemma D_14b8d8 : decode_any W_14b8d8 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8dc : bv 32 := 0x00000713.
Lemma F_14b8dc : fetch_word Asan.M.loaded_segments (0x14b920 : word) = Some W_14b8dc.
Proof. vm_refl. Qed.
Lemma D_14b8dc : decode_any W_14b8dc = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8e0 : bv 32 := 0x00000793.
Lemma F_14b8e0 : fetch_word Asan.M.loaded_segments (0x14b924 : word) = Some W_14b8e0.
Proof. vm_refl. Qed.
Lemma D_14b8e0 : decode_any W_14b8e0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8e4 : bv 32 := 0x00000813.
Lemma F_14b8e4 : fetch_word Asan.M.loaded_segments (0x14b928 : word) = Some W_14b8e4.
Proof. vm_refl. Qed.
Lemma D_14b8e4 : decode_any W_14b8e4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8e8 : bv 32 := 0xdb8fa0ef.
Lemma F_14b8e8 : fetch_word Asan.M.loaded_segments (0x14b92c : word) = Some W_14b8e8.
Proof. vm_refl. Qed.
Lemma D_14b8e8 : decode_any W_14b8e8 = Some (Jal 1 2074040, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8ec : bv 32 := 0x00813083.
Lemma F_14b8ec : fetch_word Asan.M.loaded_segments (0x14b930 : word) = Some W_14b8ec.
Proof. vm_refl. Qed.
Lemma D_14b8ec : decode_any W_14b8ec = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8f0 : bv 32 := 0x01010113.
Lemma F_14b8f0 : fetch_word Asan.M.loaded_segments (0x14b934 : word) = Some W_14b8f0.
Proof. vm_refl. Qed.
Lemma D_14b8f0 : decode_any W_14b8f0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b8f4 : bv 32 := 0x899e806f.
Lemma F_14b8f4 : fetch_word Asan.M.loaded_segments (0x14b938 : word) = Some W_14b8f4.
Proof. vm_refl. Qed.
Lemma D_14b8f4 : decode_any W_14b8f4 = Some (Jal 0 2001048, 4%Z).
Proof. vm_refl. Qed.

