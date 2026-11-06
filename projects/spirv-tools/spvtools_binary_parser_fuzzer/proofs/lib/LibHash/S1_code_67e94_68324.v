(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_67fbc : bv 32 := 0x0a842787.
Lemma F_67fbc : fetch_word Plain.M.loaded_segments (0x67ffc : word) = Some W_67fbc.
Proof. vm_refl. Qed.
Lemma D_67fbc : decode_any W_67fbc = Some (FLoad FMT_S 15 8 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_67fcc : bv 32 := 0xd0357753.
Lemma F_67fcc : fetch_word Plain.M.loaded_segments (0x6800c : word) = Some W_67fcc.
Proof. vm_refl. Qed.
Lemma D_67fcc : decode_any W_67fcc = Some (Fcvt FC_S FC_LU 14 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_67fd4 : bv 32 := 0xd03b76d3.
Lemma F_67fd4 : fetch_word Plain.M.loaded_segments (0x68014 : word) = Some W_67fd4.
Proof. vm_refl. Qed.
Lemma D_67fd4 : decode_any W_67fd4 = Some (Fcvt FC_S FC_LU 13 22 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_67fd8 : bv 32 := 0x10d7f6d3.
Lemma F_67fd8 : fetch_word Plain.M.loaded_segments (0x68018 : word) = Some W_67fd8.
Proof. vm_refl. Qed.
Lemma D_67fd8 : decode_any W_67fd8 = Some (Fari F_MUL FMT_S 13 15 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_67fdc : bv 32 := 0xa0e69553.
Lemma F_67fdc : fetch_word Plain.M.loaded_segments (0x6801c : word) = Some W_67fdc.
Proof. vm_refl. Qed.
Lemma D_67fdc : decode_any W_67fdc = Some (Fcmp F_LT FMT_S 10 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_68004 : bv 32 := 0x18f777d3.
Lemma F_68004 : fetch_word Plain.M.loaded_segments (0x68044 : word) = Some W_68004.
Proof. vm_refl. Qed.
Lemma D_68004 : decode_any W_68004 = Some (Fari F_DIV FMT_S 15 14 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6800c : bv 32 := 0xc037b553.
Lemma F_6800c : fetch_word Plain.M.loaded_segments (0x6804c : word) = Some W_6800c.
Proof. vm_refl. Qed.
Lemma D_6800c : decode_any W_6800c = Some (Fcvt FC_LU FC_S 10 15 3, 4%Z).
Proof. vm_refl. Qed.
