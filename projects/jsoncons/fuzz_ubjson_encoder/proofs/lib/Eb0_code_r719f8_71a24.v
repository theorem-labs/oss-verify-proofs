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

Definition W_8ce00 : bv 32 := 0x000b1697.
Lemma F_8ce00 : fetch_word AsanUbsan.M.loaded_segments (0x8ce50 : word) = Some W_8ce00.
Proof. vm_refl. Qed.
Lemma D_8ce00 : decode_any W_8ce00 = Some (Auipc 13 177, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ce04 : bv 32 := 0xab86b683.
Lemma F_8ce04 : fetch_word AsanUbsan.M.loaded_segments (0x8ce54 : word) = Some W_8ce04.
Proof. vm_refl. Qed.
Lemma D_8ce04 : decode_any W_8ce04 = Some (Load SZ8 true 13 13 2744, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ce08 : bv 32 := 0x00068a63.
Lemma F_8ce08 : fetch_word AsanUbsan.M.loaded_segments (0x8ce58 : word) = Some W_8ce08.
Proof. vm_refl. Qed.
Lemma D_8ce08 : decode_any W_8ce08 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ce0c : bv 32 := 0x00400693.
Lemma F_8ce0c : fetch_word AsanUbsan.M.loaded_segments (0x8ce5c : word) = Some W_8ce0c.
Proof. vm_refl. Qed.
Lemma D_8ce0c : decode_any W_8ce0c = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ce10 : bv 32 := 0x00d60663.
Lemma F_8ce10 : fetch_word AsanUbsan.M.loaded_segments (0x8ce60 : word) = Some W_8ce10.
Proof. vm_refl. Qed.
Lemma D_8ce10 : decode_any W_8ce10 = Some (Branch BC_EQ 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ce1c : bv 32 := 0x0e900893.
Lemma F_8ce1c : fetch_word AsanUbsan.M.loaded_segments (0x8ce6c : word) = Some W_8ce1c.
Proof. vm_refl. Qed.
Lemma D_8ce1c : decode_any W_8ce1c = Some (OpImm ALU_ADD 17 0 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ce20 : bv 32 := 0x00000073.
Lemma F_8ce20 : fetch_word AsanUbsan.M.loaded_segments (0x8ce70 : word) = Some W_8ce20.
Proof. vm_refl. Qed.
Lemma D_8ce20 : decode_any W_8ce20 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_8ce20 : is_ecall W_8ce20 = true.
Proof. reflexivity. Qed.

Definition W_8ce24 : bv 32 := 0x0005051b.
Lemma F_8ce24 : fetch_word AsanUbsan.M.loaded_segments (0x8ce74 : word) = Some W_8ce24.
Proof. vm_refl. Qed.
Lemma D_8ce24 : decode_any W_8ce24 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ce28 : bv 32 := 0x00008067.
Lemma F_8ce28 : fetch_word AsanUbsan.M.loaded_segments (0x8ce78 : word) = Some W_8ce28.
Proof. vm_refl. Qed.
Lemma D_8ce28 : decode_any W_8ce28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
