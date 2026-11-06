(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_65e7c : bv 32 := 0x00053703.
Lemma F_65e7c : fetch_word Ubsan.M.loaded_segments (0x65ebc : word) = Some W_65e7c.
Proof. vm_refl. Qed.
Lemma D_65e7c : decode_any W_65e7c = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e80 : bv 32 := 0x00853603.
Lemma F_65e80 : fetch_word Ubsan.M.loaded_segments (0x65ec0 : word) = Some W_65e80.
Proof. vm_refl. Qed.
Lemma D_65e80 : decode_any W_65e80 = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e84 : bv 32 := 0x40e606b3.
Lemma F_65e84 : fetch_word Ubsan.M.loaded_segments (0x65ec4 : word) = Some W_65e84.
Proof. vm_refl. Qed.
Lemma D_65e84 : decode_any W_65e84 = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e88 : bv 32 := 0x4026d693.
Lemma F_65e88 : fetch_word Ubsan.M.loaded_segments (0x65ec8 : word) = Some W_65e88.
Proof. vm_refl. Qed.
Lemma D_65e88 : decode_any W_65e88 = Some (ShiftImm ALU_SRA 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e8c : bv 32 := 0x00b6f663.
Lemma F_65e8c : fetch_word Ubsan.M.loaded_segments (0x65ecc : word) = Some W_65e8c.
Proof. vm_refl. Qed.
Lemma D_65e8c : decode_any W_65e8c = Some (Branch BC_GEU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e90 : bv 32 := 0x40d585b3.
Lemma F_65e90 : fetch_word Ubsan.M.loaded_segments (0x65ed0 : word) = Some W_65e90.
Proof. vm_refl. Qed.
Lemma D_65e90 : decode_any W_65e90 = Some (Op ALU_SUB 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e94 : bv 32 := 0x0e00006f.
Lemma F_65e94 : fetch_word Ubsan.M.loaded_segments (0x65ed4 : word) = Some W_65e94.
Proof. vm_refl. Qed.
Lemma D_65e94 : decode_any W_65e94 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e98 : bv 32 := 0x04d5f463.
Lemma F_65e98 : fetch_word Ubsan.M.loaded_segments (0x65ed8 : word) = Some W_65e98.
Proof. vm_refl. Qed.
Lemma D_65e98 : decode_any W_65e98 = Some (Branch BC_GEU 11 13 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_65e9c : bv 32 := 0x00259693.

Definition W_65ea0 : bv 32 := 0x00e686b3.

Definition W_65ea4 : bv 32 := 0x00e037b3.

Definition W_65ea8 : bv 32 := 0x0016b813.

Definition W_65eac : bv 32 := 0x03078c63.

Definition W_65ec4 : bv 32 := 0x02e6e063.

Definition W_65ec8 : bv 32 := 0x00c68a63.

Definition W_65ecc : bv 32 := 0x00400593.

Definition W_65ed0 : bv 32 := 0x00c5fa63.

Definition W_65ed4 : bv 32 := 0xffc60613.

Definition W_65ed8 : bv 32 := 0xfed61ce3.

Definition W_65edc : bv 32 := 0x00d53423.

Definition W_65ee0 : bv 32 := 0x00008067.
Lemma F_65ee0 : fetch_word Ubsan.M.loaded_segments (0x65f20 : word) = Some W_65ee0.
Proof. vm_refl. Qed.
Lemma D_65ee0 : decode_any W_65ee0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ee4 : bv 32 := 0xc0001073.

