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

Definition W_8cdb8 : bv 32 := 0xfffff637.
Lemma F_8cdb8 : fetch_word AsanUbsan.M.loaded_segments (0x8ce08 : word) = Some W_8cdb8.
Proof. vm_refl. Qed.
Lemma D_8cdb8 : decode_any W_8cdb8 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cdbc : bv 32 := 0x0016069b.
Lemma F_8cdbc : fetch_word AsanUbsan.M.loaded_segments (0x8ce0c : word) = Some W_8cdbc.
Proof. vm_refl. Qed.
Lemma D_8cdbc : decode_any W_8cdbc = Some (OpImm32 13 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cdc0 : bv 32 := 0x00d56863.
Lemma F_8cdc0 : fetch_word AsanUbsan.M.loaded_segments (0x8ce10 : word) = Some W_8cdc0.
Proof. vm_refl. Qed.
Lemma D_8cdc0 : decode_any W_8cdc0 = Some (Branch BC_LTU 10 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cdd0 : bv 32 := 0x00a63533.
Lemma F_8cdd0 : fetch_word AsanUbsan.M.loaded_segments (0x8ce20 : word) = Some W_8cdd0.
Proof. vm_refl. Qed.
Lemma D_8cdd0 : decode_any W_8cdd0 = Some (Op ALU_SLTU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cdd4 : bv 32 := 0x00008067.
Lemma F_8cdd4 : fetch_word AsanUbsan.M.loaded_segments (0x8ce24 : word) = Some W_8cdd4.
Proof. vm_refl. Qed.
Lemma D_8cdd4 : decode_any W_8cdd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cdd8 : bv 32 := 0x0de00893.
Lemma F_8cdd8 : fetch_word AsanUbsan.M.loaded_segments (0x8ce28 : word) = Some W_8cdd8.
Proof. vm_refl. Qed.
Lemma D_8cdd8 : decode_any W_8cdd8 = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cddc : bv 32 := 0x00000073.
Lemma F_8cddc : fetch_word AsanUbsan.M.loaded_segments (0x8ce2c : word) = Some W_8cddc.
Proof. vm_refl. Qed.
Lemma D_8cddc : decode_any W_8cddc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_8cddc : is_ecall W_8cddc = true.
Proof. reflexivity. Qed.

Definition W_8cde0 : bv 32 := 0x00008067.
Lemma F_8cde0 : fetch_word AsanUbsan.M.loaded_segments (0x8ce30 : word) = Some W_8cde0.
Proof. vm_refl. Qed.
Lemma D_8cde0 : decode_any W_8cde0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cde4 : bv 32 := 0x0d700893.
Lemma F_8cde4 : fetch_word AsanUbsan.M.loaded_segments (0x8ce34 : word) = Some W_8cde4.
Proof. vm_refl. Qed.
Lemma D_8cde4 : decode_any W_8cde4 = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cde8 : bv 32 := 0x00000073.
Lemma F_8cde8 : fetch_word AsanUbsan.M.loaded_segments (0x8ce38 : word) = Some W_8cde8.
Proof. vm_refl. Qed.
Lemma D_8cde8 : decode_any W_8cde8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_8cde8 : is_ecall W_8cde8 = true.
Proof. reflexivity. Qed.

Definition W_8cdec : bv 32 := 0x00008067.
Lemma F_8cdec : fetch_word AsanUbsan.M.loaded_segments (0x8ce3c : word) = Some W_8cdec.
Proof. vm_refl. Qed.
Lemma D_8cdec : decode_any W_8cdec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
