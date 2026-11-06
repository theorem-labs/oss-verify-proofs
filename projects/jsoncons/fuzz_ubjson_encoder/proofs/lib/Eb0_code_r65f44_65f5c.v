(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_81330 : bv 32 := 0x000c6517.
Lemma F_81330 : fetch_word AsanUbsan.M.loaded_segments (0x81380 : word) = Some W_81330.
Proof. vm_refl. Qed.
Lemma D_81330 : decode_any W_81330 = Some (Auipc 10 198, 4%Z).
Proof. vm_refl. Qed.

Definition W_81334 : bv 32 := 0xa5850503.
Lemma F_81334 : fetch_word AsanUbsan.M.loaded_segments (0x81384 : word) = Some W_81334.
Proof. vm_refl. Qed.
Lemma D_81334 : decode_any W_81334 = Some (Load SZ1 true 10 10 2648, 4%Z).
Proof. vm_refl. Qed.

Definition W_81338 : bv 32 := 0x0230000f.
Lemma F_81338 : fetch_word AsanUbsan.M.loaded_segments (0x81388 : word) = Some W_81338.
Proof. vm_refl. Qed.
Lemma D_81338 : decode_any W_81338 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8133c : bv 32 := 0xfff50513.
Lemma F_8133c : fetch_word AsanUbsan.M.loaded_segments (0x8138c : word) = Some W_8133c.
Proof. vm_refl. Qed.
Lemma D_8133c : decode_any W_8133c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81340 : bv 32 := 0x00153513.
Lemma F_81340 : fetch_word AsanUbsan.M.loaded_segments (0x81390 : word) = Some W_81340.
Proof. vm_refl. Qed.
Lemma D_81340 : decode_any W_81340 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81344 : bv 32 := 0x00008067.
Lemma F_81344 : fetch_word AsanUbsan.M.loaded_segments (0x81394 : word) = Some W_81344.
Proof. vm_refl. Qed.
Lemma D_81344 : decode_any W_81344 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
