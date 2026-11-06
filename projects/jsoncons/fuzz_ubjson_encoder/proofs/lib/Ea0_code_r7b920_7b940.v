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

Definition W_96500 : bv 32 := 0xfe010113.
Lemma F_96500 : fetch_word Asan.M.loaded_segments (0x96550 : word) = Some W_96500.
Proof. vm_refl. Qed.
Lemma D_96500 : decode_any W_96500 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9664c : bv 32 := 0x00058513.
Lemma F_9664c : fetch_word Asan.M.loaded_segments (0x9669c : word) = Some W_9664c.
Proof. vm_refl. Qed.
Lemma D_9664c : decode_any W_9664c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96650 : bv 32 := 0x00060593.
Lemma F_96650 : fetch_word Asan.M.loaded_segments (0x966a0 : word) = Some W_96650.
Proof. vm_refl. Qed.
Lemma D_96650 : decode_any W_96650 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96654 : bv 32 := 0x00068613.
Lemma F_96654 : fetch_word Asan.M.loaded_segments (0x966a4 : word) = Some W_96654.
Proof. vm_refl. Qed.
Lemma D_96654 : decode_any W_96654 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96658 : bv 32 := 0xc65f706f.
Lemma F_96658 : fetch_word Asan.M.loaded_segments (0x966a8 : word) = Some W_96658.
Proof. vm_refl. Qed.
Lemma D_96658 : decode_any W_96658 = Some (Jal 0 2063460, 4%Z).
Proof. vm_refl. Qed.
