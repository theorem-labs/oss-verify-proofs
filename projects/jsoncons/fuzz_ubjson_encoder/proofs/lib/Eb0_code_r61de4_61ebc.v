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

Definition W_7cf54 : bv 32 := 0xfb010113.
Lemma F_7cf54 : fetch_word AsanUbsan.M.loaded_segments (0x7cfa4 : word) = Some W_7cf54.
Proof. vm_refl. Qed.
Lemma D_7cf54 : decode_any W_7cf54 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cf58 : bv 32 := 0x04113423.
Lemma F_7cf58 : fetch_word AsanUbsan.M.loaded_segments (0x7cfa8 : word) = Some W_7cf58.
Proof. vm_refl. Qed.
Lemma D_7cf58 : decode_any W_7cf58 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cf5c : bv 32 := 0x04813023.
Lemma F_7cf5c : fetch_word AsanUbsan.M.loaded_segments (0x7cfac : word) = Some W_7cf5c.
Proof. vm_refl. Qed.
Lemma D_7cf5c : decode_any W_7cf5c = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cf60 : bv 32 := 0x000c1517.
Lemma F_7cf60 : fetch_word AsanUbsan.M.loaded_segments (0x7cfb0 : word) = Some W_7cf60.
Proof. vm_refl. Qed.
Lemma D_7cf60 : decode_any W_7cf60 = Some (Auipc 10 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cf64 : bv 32 := 0x95853503.
Lemma F_7cf64 : fetch_word AsanUbsan.M.loaded_segments (0x7cfb4 : word) = Some W_7cf64.
Proof. vm_refl. Qed.
Lemma D_7cf64 : decode_any W_7cf64 = Some (Load SZ8 true 10 10 2392, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cf68 : bv 32 := 0x0a051463.
Lemma F_7cf68 : fetch_word AsanUbsan.M.loaded_segments (0x7cfb8 : word) = Some W_7cf68.
Proof. vm_refl. Qed.
Lemma D_7cf68 : decode_any W_7cf68 = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d010 : bv 32 := 0x00000513.
Lemma F_7d010 : fetch_word AsanUbsan.M.loaded_segments (0x7d060 : word) = Some W_7d010.
Proof. vm_refl. Qed.
Lemma D_7d010 : decode_any W_7d010 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d014 : bv 32 := 0x04813083.
Lemma F_7d014 : fetch_word AsanUbsan.M.loaded_segments (0x7d064 : word) = Some W_7d014.
Proof. vm_refl. Qed.
Lemma D_7d014 : decode_any W_7d014 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d018 : bv 32 := 0x04013403.
Lemma F_7d018 : fetch_word AsanUbsan.M.loaded_segments (0x7d068 : word) = Some W_7d018.
Proof. vm_refl. Qed.
Lemma D_7d018 : decode_any W_7d018 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d01c : bv 32 := 0x05010113.
Lemma F_7d01c : fetch_word AsanUbsan.M.loaded_segments (0x7d06c : word) = Some W_7d01c.
Proof. vm_refl. Qed.
Lemma D_7d01c : decode_any W_7d01c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d020 : bv 32 := 0x00008067.
Lemma F_7d020 : fetch_word AsanUbsan.M.loaded_segments (0x7d070 : word) = Some W_7d020.
Proof. vm_refl. Qed.
Lemma D_7d020 : decode_any W_7d020 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
