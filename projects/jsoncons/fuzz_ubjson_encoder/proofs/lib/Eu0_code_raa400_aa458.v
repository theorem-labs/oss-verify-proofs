(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_ae3c0 : bv 32 := 0x08b50663.
Lemma F_ae3c0 : fetch_word Ubsan.M.loaded_segments (0xae40c : word) = Some W_ae3c0.
Proof. vm_refl. Qed.
Lemma D_ae3c0 : decode_any W_ae3c0 = Some (Branch BC_EQ 10 11 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3c4 : bv 32 := 0x00a606b3.
Lemma F_ae3c4 : fetch_word Ubsan.M.loaded_segments (0xae410 : word) = Some W_ae3c4.
Proof. vm_refl. Qed.
Lemma D_ae3c4 : decode_any W_ae3c4 = Some (Op ALU_ADD 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3c8 : bv 32 := 0x00161713.
Lemma F_ae3c8 : fetch_word Ubsan.M.loaded_segments (0xae414 : word) = Some W_ae3c8.
Proof. vm_refl. Qed.
Lemma D_ae3c8 : decode_any W_ae3c8 = Some (ShiftImm ALU_SLL 14 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3cc : bv 32 := 0x40d586b3.
Lemma F_ae3cc : fetch_word Ubsan.M.loaded_segments (0xae418 : word) = Some W_ae3cc.
Proof. vm_refl. Qed.
Lemma D_ae3cc : decode_any W_ae3cc = Some (Op ALU_SUB 13 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3d0 : bv 32 := 0x40e00733.
Lemma F_ae3d0 : fetch_word Ubsan.M.loaded_segments (0xae41c : word) = Some W_ae3d0.
Proof. vm_refl. Qed.
Lemma D_ae3d0 : decode_any W_ae3d0 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3d4 : bv 32 := 0x04d77063.
Lemma F_ae3d4 : fetch_word Ubsan.M.loaded_segments (0xae420 : word) = Some W_ae3d4.
Proof. vm_refl. Qed.
Lemma D_ae3d4 : decode_any W_ae3d4 = Some (Branch BC_GEU 14 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3d8 : bv 32 := 0x00a5c6b3.
Lemma F_ae3d8 : fetch_word Ubsan.M.loaded_segments (0xae424 : word) = Some W_ae3d8.
Proof. vm_refl. Qed.
Lemma D_ae3d8 : decode_any W_ae3d8 = Some (Op ALU_XOR 13 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3dc : bv 32 := 0x0076f693.
Lemma F_ae3dc : fetch_word Ubsan.M.loaded_segments (0xae428 : word) = Some W_ae3dc.
Proof. vm_refl. Qed.
Lemma D_ae3dc : decode_any W_ae3dc = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3e0 : bv 32 := 0x02b57c63.
Lemma F_ae3e0 : fetch_word Ubsan.M.loaded_segments (0xae42c : word) = Some W_ae3e0.
Proof. vm_refl. Qed.
Lemma D_ae3e0 : decode_any W_ae3e0 = Some (Branch BC_GEU 10 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3e4 : bv 32 := 0x06068663.
Lemma F_ae3e4 : fetch_word Ubsan.M.loaded_segments (0xae430 : word) = Some W_ae3e4.
Proof. vm_refl. Qed.
Lemma D_ae3e4 : decode_any W_ae3e4 = Some (Branch BC_EQ 13 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3e8 : bv 32 := 0x00050693.
Lemma F_ae3e8 : fetch_word Ubsan.M.loaded_segments (0xae434 : word) = Some W_ae3e8.
Proof. vm_refl. Qed.
Lemma D_ae3e8 : decode_any W_ae3e8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3ec : bv 32 := 0x00058713.
Lemma F_ae3ec : fetch_word Ubsan.M.loaded_segments (0xae438 : word) = Some W_ae3ec.
Proof. vm_refl. Qed.
Lemma D_ae3ec : decode_any W_ae3ec = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3f0 : bv 32 := 0x04060e63.
Lemma F_ae3f0 : fetch_word Ubsan.M.loaded_segments (0xae43c : word) = Some W_ae3f0.
Proof. vm_refl. Qed.
Lemma D_ae3f0 : decode_any W_ae3f0 = Some (Branch BC_EQ 12 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3f4 : bv 32 := 0x00c68633.
Lemma F_ae3f4 : fetch_word Ubsan.M.loaded_segments (0xae440 : word) = Some W_ae3f4.
Proof. vm_refl. Qed.
Lemma D_ae3f4 : decode_any W_ae3f4 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3f8 : bv 32 := 0x00074583.
Lemma F_ae3f8 : fetch_word Ubsan.M.loaded_segments (0xae444 : word) = Some W_ae3f8.
Proof. vm_refl. Qed.
Lemma D_ae3f8 : decode_any W_ae3f8 = Some (Load SZ1 false 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3fc : bv 32 := 0x00170713.
Lemma F_ae3fc : fetch_word Ubsan.M.loaded_segments (0xae448 : word) = Some W_ae3fc.
Proof. vm_refl. Qed.
Lemma D_ae3fc : decode_any W_ae3fc = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae400 : bv 32 := 0x00168793.
Lemma F_ae400 : fetch_word Ubsan.M.loaded_segments (0xae44c : word) = Some W_ae400.
Proof. vm_refl. Qed.
Lemma D_ae400 : decode_any W_ae400 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae404 : bv 32 := 0x00b68023.
Lemma F_ae404 : fetch_word Ubsan.M.loaded_segments (0xae450 : word) = Some W_ae404.
Proof. vm_refl. Qed.
Lemma D_ae404 : decode_any W_ae404 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae408 : bv 32 := 0x00078693.
Lemma F_ae408 : fetch_word Ubsan.M.loaded_segments (0xae454 : word) = Some W_ae408.
Proof. vm_refl. Qed.
Lemma D_ae408 : decode_any W_ae408 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae40c : bv 32 := 0xfec796e3.
Lemma F_ae40c : fetch_word Ubsan.M.loaded_segments (0xae458 : word) = Some W_ae40c.
Proof. vm_refl. Qed.
Lemma D_ae40c : decode_any W_ae40c = Some (Branch BC_NE 15 12 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae410 : bv 32 := 0x03c0006f.
Lemma F_ae410 : fetch_word Ubsan.M.loaded_segments (0xae45c : word) = Some W_ae410.
Proof. vm_refl. Qed.
Lemma D_ae410 : decode_any W_ae410 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae414 : bv 32 := 0xba9ff06f.
Lemma F_ae414 : fetch_word Ubsan.M.loaded_segments (0xae460 : word) = Some W_ae414.
Proof. vm_refl. Qed.
Lemma D_ae414 : decode_any W_ae414 = Some (Jal 0 2096040, 4%Z).
Proof. vm_refl. Qed.
