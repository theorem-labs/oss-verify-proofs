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

Definition W_6860c : bv 32 := 0x104240ef.
Lemma F_6860c : fetch_word AsanUbsan.M.loaded_segments (0x6865c : word) = Some W_6860c.
Proof. vm_refl. Qed.
Lemma D_6860c : decode_any W_6860c = Some (Jal 1 147716, 4%Z).
Proof. vm_refl. Qed.

Definition W_68610 : bv 32 := 0x00150b93.
Lemma F_68610 : fetch_word AsanUbsan.M.loaded_segments (0x68660 : word) = Some W_68610.
Proof. vm_refl. Qed.
Lemma D_68610 : decode_any W_68610 = Some (OpImm ALU_ADD 23 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_68614 : bv 32 := 0xfffb4513.
Lemma F_68614 : fetch_word AsanUbsan.M.loaded_segments (0x68664 : word) = Some W_68614.
Proof. vm_refl. Qed.
Lemma D_68614 : decode_any W_68614 = Some (OpImm ALU_XOR 10 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_68618 : bv 32 := 0x25756e63.
Lemma F_68618 : fetch_word AsanUbsan.M.loaded_segments (0x68668 : word) = Some W_68618.
Proof. vm_refl. Qed.
Lemma D_68618 : decode_any W_68618 = Some (Branch BC_LTU 10 23 604, 4%Z).
Proof. vm_refl. Qed.

Definition W_6861c : bv 32 := 0xfbfb8513.
Lemma F_6861c : fetch_word AsanUbsan.M.loaded_segments (0x6866c : word) = Some W_6861c.
Proof. vm_refl. Qed.
Lemma D_6861c : decode_any W_6861c = Some (OpImm ALU_ADD 10 23 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_68620 : bv 32 := 0xfbf00593.
Lemma F_68620 : fetch_word AsanUbsan.M.loaded_segments (0x68670 : word) = Some W_68620.
Proof. vm_refl. Qed.
Lemma D_68620 : decode_any W_68620 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_68624 : bv 32 := 0x2ca5f063.
Lemma F_68624 : fetch_word AsanUbsan.M.loaded_segments (0x68674 : word) = Some W_68624.
Proof. vm_refl. Qed.
Lemma D_68624 : decode_any W_68624 = Some (Branch BC_GEU 11 10 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_68628 : bv 32 := 0x000d5517.
Lemma F_68628 : fetch_word AsanUbsan.M.loaded_segments (0x68678 : word) = Some W_68628.
Proof. vm_refl. Qed.
Lemma D_68628 : decode_any W_68628 = Some (Auipc 10 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_6862c : bv 32 := 0x25053503.
Lemma F_6862c : fetch_word AsanUbsan.M.loaded_segments (0x6867c : word) = Some W_6862c.
Proof. vm_refl. Qed.
Lemma D_6862c : decode_any W_6862c = Some (Load SZ8 true 10 10 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_68630 : bv 32 := 0x017b0633.
Lemma F_68630 : fetch_word AsanUbsan.M.loaded_segments (0x68680 : word) = Some W_68630.
Proof. vm_refl. Qed.
Lemma D_68630 : decode_any W_68630 = Some (Op ALU_ADD 12 22 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_68634 : bv 32 := 0x00053583.
Lemma F_68634 : fetch_word AsanUbsan.M.loaded_segments (0x68684 : word) = Some W_68634.
Proof. vm_refl. Qed.
Lemma D_68634 : decode_any W_68634 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68638 : bv 32 := 0x003b5513.
Lemma F_68638 : fetch_word AsanUbsan.M.loaded_segments (0x68688 : word) = Some W_68638.
Proof. vm_refl. Qed.
Lemma D_68638 : decode_any W_68638 = Some (ShiftImm ALU_SRL 10 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6863c : bv 32 := 0xfff60613.
Lemma F_6863c : fetch_word AsanUbsan.M.loaded_segments (0x6868c : word) = Some W_6863c.
Proof. vm_refl. Qed.
Lemma D_6863c : decode_any W_6863c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_68640 : bv 32 := 0x00365693.
Lemma F_68640 : fetch_word AsanUbsan.M.loaded_segments (0x68690 : word) = Some W_68640.
Proof. vm_refl. Qed.
Lemma D_68640 : decode_any W_68640 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_68644 : bv 32 := 0x00a58533.
Lemma F_68644 : fetch_word AsanUbsan.M.loaded_segments (0x68694 : word) = Some W_68644.
Proof. vm_refl. Qed.
Lemma D_68644 : decode_any W_68644 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_68648 : bv 32 := 0x00d585b3.
Lemma F_68648 : fetch_word AsanUbsan.M.loaded_segments (0x68698 : word) = Some W_68648.
Proof. vm_refl. Qed.
Lemma D_68648 : decode_any W_68648 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6864c : bv 32 := 0xff857693.
Lemma F_6864c : fetch_word AsanUbsan.M.loaded_segments (0x6869c : word) = Some W_6864c.
Proof. vm_refl. Qed.
Lemma D_6864c : decode_any W_6864c = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_68650 : bv 32 := 0xff85f713.
Lemma F_68650 : fetch_word AsanUbsan.M.loaded_segments (0x686a0 : word) = Some W_68650.
Proof. vm_refl. Qed.
Lemma D_68650 : decode_any W_68650 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_68654 : bv 32 := 0x0006b683.
Lemma F_68654 : fetch_word AsanUbsan.M.loaded_segments (0x686a4 : word) = Some W_68654.
Proof. vm_refl. Qed.
Lemma D_68654 : decode_any W_68654 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68658 : bv 32 := 0x00073703.
Lemma F_68658 : fetch_word AsanUbsan.M.loaded_segments (0x686a8 : word) = Some W_68658.
Proof. vm_refl. Qed.
Lemma D_68658 : decode_any W_68658 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6865c : bv 32 := 0x00d766b3.
Lemma F_6865c : fetch_word AsanUbsan.M.loaded_segments (0x686ac : word) = Some W_6865c.
Proof. vm_refl. Qed.
Lemma D_6865c : decode_any W_6865c = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_68660 : bv 32 := 0xf00688e3.
Lemma F_68660 : fetch_word AsanUbsan.M.loaded_segments (0x686b0 : word) = Some W_68660.
Proof. vm_refl. Qed.
Lemma D_68660 : decode_any W_68660 = Some (Branch BC_EQ 13 0 7952, 4%Z).
Proof. vm_refl. Qed.

Definition W_68698 : bv 32 := 0x000b0513.
Lemma F_68698 : fetch_word AsanUbsan.M.loaded_segments (0x686e8 : word) = Some W_68698.
Proof. vm_refl. Qed.
Lemma D_68698 : decode_any W_68698 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6869c : bv 32 := 0x000b8593.
Lemma F_6869c : fetch_word AsanUbsan.M.loaded_segments (0x686ec : word) = Some W_6869c.
Proof. vm_refl. Qed.
Lemma D_6869c : decode_any W_6869c = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_686a0 : bv 32 := 0x77d130ef.
Lemma F_686a0 : fetch_word AsanUbsan.M.loaded_segments (0x686f0 : word) = Some W_686a0.
Proof. vm_refl. Qed.
Lemma D_686a0 : decode_any W_686a0 = Some (Jal 1 81788, 4%Z).
Proof. vm_refl. Qed.

Definition W_686a4 : bv 32 := 0xec0506e3.
Lemma F_686a4 : fetch_word AsanUbsan.M.loaded_segments (0x686f4 : word) = Some W_686a4.
Proof. vm_refl. Qed.
Lemma D_686a4 : decode_any W_686a4 = Some (Branch BC_EQ 10 0 7884, 4%Z).
Proof. vm_refl. Qed.
