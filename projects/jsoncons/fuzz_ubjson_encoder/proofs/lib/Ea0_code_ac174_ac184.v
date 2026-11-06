(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_ac174 : bv 32 := 0x00345513.
Lemma F_ac174 : fetch_word Asan.M.loaded_segments (0xac1c4 : word) = Some W_ac174.
Proof. vm_refl. Qed.
Lemma D_ac174 : decode_any W_ac174 = Some (ShiftImm ALU_SRL 10 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac178 : bv 32 := 0x01450533.
Lemma F_ac178 : fetch_word Asan.M.loaded_segments (0xac1c8 : word) = Some W_ac178.
Proof. vm_refl. Qed.
Lemma D_ac178 : decode_any W_ac178 = Some (Op ALU_ADD 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac17c : bv 32 := 0x00050503.
Lemma F_ac17c : fetch_word Asan.M.loaded_segments (0xac1cc : word) = Some W_ac17c.
Proof. vm_refl. Qed.
Lemma D_ac17c : decode_any W_ac17c = Some (Load SZ1 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac180 : bv 32 := 0x02051a63.
Lemma F_ac180 : fetch_word Asan.M.loaded_segments (0xac1d0 : word) = Some W_ac180.
Proof. vm_refl. Qed.
Lemma D_ac180 : decode_any W_ac180 = Some (Branch BC_NE 10 0 52, 4%Z).
Proof. vm_refl. Qed.
