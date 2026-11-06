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

Definition W_660d4 : bv 32 := 0x00078517.
Lemma F_660d4 : fetch_word Asan.M.loaded_segments (0x660d4 : word) = Some W_660d4.
Proof. vm_refl. Qed.
Lemma D_660d4 : decode_any W_660d4 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_660d8 : bv 32 := 0x74450503.
Lemma F_660d8 : fetch_word Asan.M.loaded_segments (0x660d8 : word) = Some W_660d8.
Proof. vm_refl. Qed.
Lemma D_660d8 : decode_any W_660d8 = Some (Load SZ1 true 10 10 1860, 4%Z).
Proof. vm_refl. Qed.

Definition W_660dc : bv 32 := 0x0230000f.
Lemma F_660dc : fetch_word Asan.M.loaded_segments (0x660dc : word) = Some W_660dc.
Proof. vm_refl. Qed.
Lemma D_660dc : decode_any W_660dc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_660e0 : bv 32 := 0xfff50513.
Lemma F_660e0 : fetch_word Asan.M.loaded_segments (0x660e0 : word) = Some W_660e0.
Proof. vm_refl. Qed.
Lemma D_660e0 : decode_any W_660e0 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_660e4 : bv 32 := 0x00153513.
Lemma F_660e4 : fetch_word Asan.M.loaded_segments (0x660e4 : word) = Some W_660e4.
Proof. vm_refl. Qed.
Lemma D_660e4 : decode_any W_660e4 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_660e8 : bv 32 := 0x00008067.
Lemma F_660e8 : fetch_word Asan.M.loaded_segments (0x660e8 : word) = Some W_660e8.
Proof. vm_refl. Qed.
Lemma D_660e8 : decode_any W_660e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
