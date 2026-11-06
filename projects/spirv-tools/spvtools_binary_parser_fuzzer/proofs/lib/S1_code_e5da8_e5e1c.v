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

Definition W_e5da8 : bv 32 := 0xff010113.
Lemma F_e5da8 : fetch_word Plain.M.loaded_segments (0xe5ddc : word) = Some W_e5da8.
Proof. vm_refl. Qed.
Lemma D_e5da8 : decode_any W_e5da8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5dac : bv 32 := 0x00113423.
Lemma F_e5dac : fetch_word Plain.M.loaded_segments (0xe5de0 : word) = Some W_e5dac.
Proof. vm_refl. Qed.
Lemma D_e5dac : decode_any W_e5dac = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5db0 : bv 32 := 0x00813023.
Lemma F_e5db0 : fetch_word Plain.M.loaded_segments (0xe5de4 : word) = Some W_e5db0.
Proof. vm_refl. Qed.
Lemma D_e5db0 : decode_any W_e5db0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5db4 : bv 32 := 0x00153413.
Lemma F_e5db4 : fetch_word Plain.M.loaded_segments (0xe5de8 : word) = Some W_e5db4.
Proof. vm_refl. Qed.
Lemma D_e5db4 : decode_any W_e5db4 = Some (OpImm ALU_SLTU 8 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5db8 : bv 32 := 0x00850433.
Lemma F_e5db8 : fetch_word Plain.M.loaded_segments (0xe5dec : word) = Some W_e5db8.
Proof. vm_refl. Qed.
Lemma D_e5db8 : decode_any W_e5db8 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5dbc : bv 32 := 0x00040513.
Lemma F_e5dbc : fetch_word Plain.M.loaded_segments (0xe5df0 : word) = Some W_e5dbc.
Proof. vm_refl. Qed.
Lemma D_e5dbc : decode_any W_e5dbc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5dc0 : bv 32 := 0xaecec0ef.
Lemma F_e5dc0 : fetch_word Plain.M.loaded_segments (0xe5df4 : word) = Some W_e5dc0.
Proof. vm_refl. Qed.
Lemma D_e5dc0 : decode_any W_e5dc0 = Some (Jal 1 2015980, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5dc4 : bv 32 := 0x00051e63.
Lemma F_e5dc4 : fetch_word Plain.M.loaded_segments (0xe5df8 : word) = Some W_e5dc4.
Proof. vm_refl. Qed.
Lemma D_e5dc4 : decode_any W_e5dc4 = Some (Branch BC_NE 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5de0 : bv 32 := 0x00813083.
Lemma F_e5de0 : fetch_word Plain.M.loaded_segments (0xe5e14 : word) = Some W_e5de0.
Proof. vm_refl. Qed.
Lemma D_e5de0 : decode_any W_e5de0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5de4 : bv 32 := 0x00013403.
Lemma F_e5de4 : fetch_word Plain.M.loaded_segments (0xe5e18 : word) = Some W_e5de4.
Proof. vm_refl. Qed.
Lemma D_e5de4 : decode_any W_e5de4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5de8 : bv 32 := 0x01010113.
Lemma F_e5de8 : fetch_word Plain.M.loaded_segments (0xe5e1c : word) = Some W_e5de8.
Proof. vm_refl. Qed.
Lemma D_e5de8 : decode_any W_e5de8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5dec : bv 32 := 0x00008067.
Lemma F_e5dec : fetch_word Plain.M.loaded_segments (0xe5e20 : word) = Some W_e5dec.
Proof. vm_refl. Qed.
Lemma D_e5dec : decode_any W_e5dec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
