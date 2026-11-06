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

Definition W_e7b00 : bv 32 := 0xff010113.
Lemma F_e7b00 : fetch_word Ubsan.M.loaded_segments (0xe7b34 : word) = Some W_e7b00.
Proof. vm_refl. Qed.
Lemma D_e7b00 : decode_any W_e7b00 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b04 : bv 32 := 0x00113423.
Lemma F_e7b04 : fetch_word Ubsan.M.loaded_segments (0xe7b38 : word) = Some W_e7b04.
Proof. vm_refl. Qed.
Lemma D_e7b04 : decode_any W_e7b04 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b08 : bv 32 := 0x00813023.
Lemma F_e7b08 : fetch_word Ubsan.M.loaded_segments (0xe7b3c : word) = Some W_e7b08.
Proof. vm_refl. Qed.
Lemma D_e7b08 : decode_any W_e7b08 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b0c : bv 32 := 0x00153413.
Lemma F_e7b0c : fetch_word Ubsan.M.loaded_segments (0xe7b40 : word) = Some W_e7b0c.
Proof. vm_refl. Qed.
Lemma D_e7b0c : decode_any W_e7b0c = Some (OpImm ALU_SLTU 8 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b10 : bv 32 := 0x00850433.
Lemma F_e7b10 : fetch_word Ubsan.M.loaded_segments (0xe7b44 : word) = Some W_e7b10.
Proof. vm_refl. Qed.
Lemma D_e7b10 : decode_any W_e7b10 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b14 : bv 32 := 0x00040513.
Lemma F_e7b14 : fetch_word Ubsan.M.loaded_segments (0xe7b48 : word) = Some W_e7b14.
Proof. vm_refl. Qed.
Lemma D_e7b14 : decode_any W_e7b14 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b18 : bv 32 := 0xaecec0ef.
Lemma F_e7b18 : fetch_word Ubsan.M.loaded_segments (0xe7b4c : word) = Some W_e7b18.
Proof. vm_refl. Qed.
Lemma D_e7b18 : decode_any W_e7b18 = Some (Jal 1 2015980, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b1c : bv 32 := 0x00051e63.
Lemma F_e7b1c : fetch_word Ubsan.M.loaded_segments (0xe7b50 : word) = Some W_e7b1c.
Proof. vm_refl. Qed.
Lemma D_e7b1c : decode_any W_e7b1c = Some (Branch BC_NE 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b38 : bv 32 := 0x00813083.
Lemma F_e7b38 : fetch_word Ubsan.M.loaded_segments (0xe7b6c : word) = Some W_e7b38.
Proof. vm_refl. Qed.
Lemma D_e7b38 : decode_any W_e7b38 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b3c : bv 32 := 0x00013403.
Lemma F_e7b3c : fetch_word Ubsan.M.loaded_segments (0xe7b70 : word) = Some W_e7b3c.
Proof. vm_refl. Qed.
Lemma D_e7b3c : decode_any W_e7b3c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b40 : bv 32 := 0x01010113.
Lemma F_e7b40 : fetch_word Ubsan.M.loaded_segments (0xe7b74 : word) = Some W_e7b40.
Proof. vm_refl. Qed.
Lemma D_e7b40 : decode_any W_e7b40 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b44 : bv 32 := 0x00008067.
Lemma F_e7b44 : fetch_word Ubsan.M.loaded_segments (0xe7b78 : word) = Some W_e7b44.
Proof. vm_refl. Qed.
Lemma D_e7b44 : decode_any W_e7b44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
