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

Definition W_ac48c : bv 32 := 0x00395513.
Lemma F_ac48c : fetch_word Asan.M.loaded_segments (0xac4dc : word) = Some W_ac48c.
Proof. vm_refl. Qed.
Lemma D_ac48c : decode_any W_ac48c = Some (ShiftImm ALU_SRL 10 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac490 : bv 32 := 0x01550533.
Lemma F_ac490 : fetch_word Asan.M.loaded_segments (0xac4e0 : word) = Some W_ac490.
Proof. vm_refl. Qed.
Lemma D_ac490 : decode_any W_ac490 = Some (Op ALU_ADD 10 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac494 : bv 32 := 0x00050503.
Lemma F_ac494 : fetch_word Asan.M.loaded_segments (0xac4e4 : word) = Some W_ac494.
Proof. vm_refl. Qed.
Lemma D_ac494 : decode_any W_ac494 = Some (Load SZ1 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac498 : bv 32 := 0x02051a63.
Lemma F_ac498 : fetch_word Asan.M.loaded_segments (0xac4e8 : word) = Some W_ac498.
Proof. vm_refl. Qed.
Lemma D_ac498 : decode_any W_ac498 = Some (Branch BC_NE 10 0 52, 4%Z).
Proof. vm_refl. Qed.
