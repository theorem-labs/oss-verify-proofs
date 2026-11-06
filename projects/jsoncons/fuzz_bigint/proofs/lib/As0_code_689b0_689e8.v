(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_689b0 : bv 32 := 0xff010113.
Lemma F_689b0 : fetch_word Asan.M.loaded_segments (0x689b0 : word) = Some W_689b0.
Proof. vm_refl. Qed.
Lemma D_689b0 : decode_any W_689b0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_689b4 : bv 32 := 0x00113423.
Lemma F_689b4 : fetch_word Asan.M.loaded_segments (0x689b4 : word) = Some W_689b4.
Proof. vm_refl. Qed.
Lemma D_689b4 : decode_any W_689b4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_689b8 : bv 32 := 0x62d000ef.
Lemma F_689b8 : fetch_word Asan.M.loaded_segments (0x689b8 : word) = Some W_689b8.
Proof. vm_refl. Qed.
Lemma D_689b8 : decode_any W_689b8 = Some (Jal 1 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_689bc : bv 32 := 0x00050c63.
Lemma F_689bc : fetch_word Asan.M.loaded_segments (0x689bc : word) = Some W_689bc.
Proof. vm_refl. Qed.
Lemma D_689bc : decode_any W_689bc = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_689c0 : bv 32 := 0x7ff50513.
Lemma F_689c0 : fetch_word Asan.M.loaded_segments (0x689c0 : word) = Some W_689c0.
Proof. vm_refl. Qed.
Lemma D_689c0 : decode_any W_689c0 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_689c4 : bv 32 := 0x2f150513.
Lemma F_689c4 : fetch_word Asan.M.loaded_segments (0x689c4 : word) = Some W_689c4.
Proof. vm_refl. Qed.
Lemma D_689c4 : decode_any W_689c4 = Some (OpImm ALU_ADD 10 10 753, 4%Z).
Proof. vm_refl. Qed.

Definition W_689c8 : bv 32 := 0x00813083.
Lemma F_689c8 : fetch_word Asan.M.loaded_segments (0x689c8 : word) = Some W_689c8.
Proof. vm_refl. Qed.
Lemma D_689c8 : decode_any W_689c8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_689cc : bv 32 := 0x01010113.
Lemma F_689cc : fetch_word Asan.M.loaded_segments (0x689cc : word) = Some W_689cc.
Proof. vm_refl. Qed.
Lemma D_689cc : decode_any W_689cc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_689d0 : bv 32 := 0x00008067.
Lemma F_689d0 : fetch_word Asan.M.loaded_segments (0x689d0 : word) = Some W_689d0.
Proof. vm_refl. Qed.
Lemma D_689d0 : decode_any W_689d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_689d4 : bv 32 := 0x00076517.
Lemma F_689d4 : fetch_word Asan.M.loaded_segments (0x689d4 : word) = Some W_689d4.
Proof. vm_refl. Qed.
Lemma D_689d4 : decode_any W_689d4 = Some (Auipc 10 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_689d8 : bv 32 := 0xe9450513.
Lemma F_689d8 : fetch_word Asan.M.loaded_segments (0x689d8 : word) = Some W_689d8.
Proof. vm_refl. Qed.
Lemma D_689d8 : decode_any W_689d8 = Some (OpImm ALU_ADD 10 10 3732, 4%Z).
Proof. vm_refl. Qed.

Definition W_689dc : bv 32 := 0x00813083.
Lemma F_689dc : fetch_word Asan.M.loaded_segments (0x689dc : word) = Some W_689dc.
Proof. vm_refl. Qed.
Lemma D_689dc : decode_any W_689dc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_689e0 : bv 32 := 0x01010113.
Lemma F_689e0 : fetch_word Asan.M.loaded_segments (0x689e0 : word) = Some W_689e0.
Proof. vm_refl. Qed.
Lemma D_689e0 : decode_any W_689e0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_689e4 : bv 32 := 0x00008067.
Lemma F_689e4 : fetch_word Asan.M.loaded_segments (0x689e4 : word) = Some W_689e4.
Proof. vm_refl. Qed.
Lemma D_689e4 : decode_any W_689e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
