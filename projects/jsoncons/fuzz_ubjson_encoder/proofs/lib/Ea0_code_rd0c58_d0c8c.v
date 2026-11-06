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

Definition W_131e48 : bv 32 := 0xff010113.
Lemma F_131e48 : fetch_word Asan.M.loaded_segments (0x131e8c : word) = Some W_131e48.
Proof. vm_refl. Qed.
Lemma D_131e48 : decode_any W_131e48 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e4c : bv 32 := 0x00113423.
Lemma F_131e4c : fetch_word Asan.M.loaded_segments (0x131e90 : word) = Some W_131e4c.
Proof. vm_refl. Qed.
Lemma D_131e4c : decode_any W_131e4c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e50 : bv 32 := 0x00060693.
Lemma F_131e50 : fetch_word Asan.M.loaded_segments (0x131e94 : word) = Some W_131e50.
Proof. vm_refl. Qed.
Lemma D_131e50 : decode_any W_131e50 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e54 : bv 32 := 0x00058613.
Lemma F_131e54 : fetch_word Asan.M.loaded_segments (0x131e98 : word) = Some W_131e54.
Proof. vm_refl. Qed.
Lemma D_131e54 : decode_any W_131e54 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e58 : bv 32 := 0x00050593.
Lemma F_131e58 : fetch_word Asan.M.loaded_segments (0x131e9c : word) = Some W_131e58.
Proof. vm_refl. Qed.
Lemma D_131e58 : decode_any W_131e58 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e5c : bv 32 := 0x03f00513.
Lemma F_131e5c : fetch_word Asan.M.loaded_segments (0x131ea0 : word) = Some W_131e5c.
Proof. vm_refl. Qed.
Lemma D_131e5c : decode_any W_131e5c = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e60 : bv 32 := 0x00000713.
Lemma F_131e60 : fetch_word Asan.M.loaded_segments (0x131ea4 : word) = Some W_131e60.
Proof. vm_refl. Qed.
Lemma D_131e60 : decode_any W_131e60 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e64 : bv 32 := 0x00000793.
Lemma F_131e64 : fetch_word Asan.M.loaded_segments (0x131ea8 : word) = Some W_131e64.
Proof. vm_refl. Qed.
Lemma D_131e64 : decode_any W_131e64 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e68 : bv 32 := 0x00000813.
Lemma F_131e68 : fetch_word Asan.M.loaded_segments (0x131eac : word) = Some W_131e68.
Proof. vm_refl. Qed.
Lemma D_131e68 : decode_any W_131e68 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e6c : bv 32 := 0xdb8fa0ef.
Lemma F_131e6c : fetch_word Asan.M.loaded_segments (0x131eb0 : word) = Some W_131e6c.
Proof. vm_refl. Qed.
Lemma D_131e6c : decode_any W_131e6c = Some (Jal 1 2074040, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e70 : bv 32 := 0x00813083.
Lemma F_131e70 : fetch_word Asan.M.loaded_segments (0x131eb4 : word) = Some W_131e70.
Proof. vm_refl. Qed.
Lemma D_131e70 : decode_any W_131e70 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e74 : bv 32 := 0x01010113.
Lemma F_131e74 : fetch_word Asan.M.loaded_segments (0x131eb8 : word) = Some W_131e74.
Proof. vm_refl. Qed.
Lemma D_131e74 : decode_any W_131e74 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_131e78 : bv 32 := 0x899e806f.
Lemma F_131e78 : fetch_word Asan.M.loaded_segments (0x131ebc : word) = Some W_131e78.
Proof. vm_refl. Qed.
Lemma D_131e78 : decode_any W_131e78 = Some (Jal 0 2001048, 4%Z).
Proof. vm_refl. Qed.
