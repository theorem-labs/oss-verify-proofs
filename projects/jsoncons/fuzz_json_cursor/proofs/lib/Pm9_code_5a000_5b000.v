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

Definition W_5a368 : bv 32 := 0xfe010113.
Lemma F_5a368 : fetch_word AsanUbsan.M.loaded_segments (0x5a3b0 : word) = Some W_5a368.
Proof. vm_refl. Qed.
Lemma D_5a368 : decode_any W_5a368 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a36c : bv 32 := 0x00113c23.
Lemma F_5a36c : fetch_word AsanUbsan.M.loaded_segments (0x5a3b4 : word) = Some W_5a36c.
Proof. vm_refl. Qed.
Lemma D_5a36c : decode_any W_5a36c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a370 : bv 32 := 0x00813823.
Lemma F_5a370 : fetch_word AsanUbsan.M.loaded_segments (0x5a3b8 : word) = Some W_5a370.
Proof. vm_refl. Qed.
Lemma D_5a370 : decode_any W_5a370 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a374 : bv 32 := 0x00913423.
Lemma F_5a374 : fetch_word AsanUbsan.M.loaded_segments (0x5a3bc : word) = Some W_5a374.
Proof. vm_refl. Qed.
Lemma D_5a374 : decode_any W_5a374 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a378 : bv 32 := 0x01213023.
Lemma F_5a378 : fetch_word AsanUbsan.M.loaded_segments (0x5a3c0 : word) = Some W_5a378.
Proof. vm_refl. Qed.
Lemma D_5a378 : decode_any W_5a378 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a37c : bv 32 := 0x00060413.
Lemma F_5a37c : fetch_word AsanUbsan.M.loaded_segments (0x5a3c4 : word) = Some W_5a37c.
Proof. vm_refl. Qed.
Lemma D_5a37c : decode_any W_5a37c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a380 : bv 32 := 0x00050493.
Lemma F_5a380 : fetch_word AsanUbsan.M.loaded_segments (0x5a3c8 : word) = Some W_5a380.
Proof. vm_refl. Qed.
Lemma D_5a380 : decode_any W_5a380 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a384 : bv 32 := 0xfff50513.
Lemma F_5a384 : fetch_word AsanUbsan.M.loaded_segments (0x5a3cc : word) = Some W_5a384.
Proof. vm_refl. Qed.
Lemma D_5a384 : decode_any W_5a384 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a388 : bv 32 := 0x00a4c633.
Lemma F_5a388 : fetch_word AsanUbsan.M.loaded_segments (0x5a3d0 : word) = Some W_5a388.
Proof. vm_refl. Qed.
Lemma D_5a388 : decode_any W_5a388 = Some (Op ALU_XOR 12 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a38c : bv 32 := 0x04c57263.
Lemma F_5a38c : fetch_word AsanUbsan.M.loaded_segments (0x5a3d4 : word) = Some W_5a38c.
Proof. vm_refl. Qed.
Lemma D_5a38c : decode_any W_5a38c = Some (Branch BC_GEU 10 12 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a390 : bv 32 := 0x00a5f533.
Lemma F_5a390 : fetch_word AsanUbsan.M.loaded_segments (0x5a3d8 : word) = Some W_5a390.
Proof. vm_refl. Qed.
Lemma D_5a390 : decode_any W_5a390 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a394 : bv 32 := 0x02051e63.
Lemma F_5a394 : fetch_word AsanUbsan.M.loaded_segments (0x5a3dc : word) = Some W_5a394.
Proof. vm_refl. Qed.
Lemma D_5a394 : decode_any W_5a394 = Some (Branch BC_NE 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a398 : bv 32 := 0x00100517.
Lemma F_5a398 : fetch_word AsanUbsan.M.loaded_segments (0x5a3e0 : word) = Some W_5a398.
Proof. vm_refl. Qed.
Lemma D_5a398 : decode_any W_5a398 = Some (Auipc 10 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a39c : bv 32 := 0x00100713.
Lemma F_5a39c : fetch_word AsanUbsan.M.loaded_segments (0x5a3e4 : word) = Some W_5a39c.
Proof. vm_refl. Qed.
Lemma D_5a39c : decode_any W_5a39c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3a0 : bv 32 := 0x2b850513.
Lemma F_5a3a0 : fetch_word AsanUbsan.M.loaded_segments (0x5a3e8 : word) = Some W_5a3a0.
Proof. vm_refl. Qed.
Lemma D_5a3a0 : decode_any W_5a3a0 = Some (OpImm ALU_ADD 10 10 696, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3a4 : bv 32 := 0x00100793.
Lemma F_5a3a4 : fetch_word AsanUbsan.M.loaded_segments (0x5a3ec : word) = Some W_5a3a4.
Proof. vm_refl. Qed.
Lemma D_5a3a4 : decode_any W_5a3a4 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3a8 : bv 32 := 0x00048613.
Lemma F_5a3a8 : fetch_word AsanUbsan.M.loaded_segments (0x5a3f0 : word) = Some W_5a3a8.
Proof. vm_refl. Qed.
Lemma D_5a3a8 : decode_any W_5a3a8 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3ac : bv 32 := 0x00040693.
Lemma F_5a3ac : fetch_word AsanUbsan.M.loaded_segments (0x5a3f4 : word) = Some W_5a3ac.
Proof. vm_refl. Qed.
Lemma D_5a3ac : decode_any W_5a3ac = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3b0 : bv 32 := 0xc24ff0ef.
Lemma F_5a3b0 : fetch_word AsanUbsan.M.loaded_segments (0x5a3f8 : word) = Some W_5a3b0.
Proof. vm_refl. Qed.
Lemma D_5a3b0 : decode_any W_5a3b0 = Some (Jal 1 2094116, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3b4 : bv 32 := 0x04050663.
Lemma F_5a3b4 : fetch_word AsanUbsan.M.loaded_segments (0x5a3fc : word) = Some W_5a3b4.
Proof. vm_refl. Qed.
Lemma D_5a3b4 : decode_any W_5a3b4 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3b8 : bv 32 := 0x01813083.
Lemma F_5a3b8 : fetch_word AsanUbsan.M.loaded_segments (0x5a400 : word) = Some W_5a3b8.
Proof. vm_refl. Qed.
Lemma D_5a3b8 : decode_any W_5a3b8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3bc : bv 32 := 0x01013403.
Lemma F_5a3bc : fetch_word AsanUbsan.M.loaded_segments (0x5a404 : word) = Some W_5a3bc.
Proof. vm_refl. Qed.
Lemma D_5a3bc : decode_any W_5a3bc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3c0 : bv 32 := 0x00813483.
Lemma F_5a3c0 : fetch_word AsanUbsan.M.loaded_segments (0x5a408 : word) = Some W_5a3c0.
Proof. vm_refl. Qed.
Lemma D_5a3c0 : decode_any W_5a3c0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3c4 : bv 32 := 0x00013903.
Lemma F_5a3c4 : fetch_word AsanUbsan.M.loaded_segments (0x5a40c : word) = Some W_5a3c4.
Proof. vm_refl. Qed.
Lemma D_5a3c4 : decode_any W_5a3c4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3c8 : bv 32 := 0x02010113.
Lemma F_5a3c8 : fetch_word AsanUbsan.M.loaded_segments (0x5a410 : word) = Some W_5a3c8.
Proof. vm_refl. Qed.
Lemma D_5a3c8 : decode_any W_5a3c8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a3cc : bv 32 := 0x00008067.
Lemma F_5a3cc : fetch_word AsanUbsan.M.loaded_segments (0x5a414 : word) = Some W_5a3cc.
Proof. vm_refl. Qed.
Lemma D_5a3cc : decode_any W_5a3cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

