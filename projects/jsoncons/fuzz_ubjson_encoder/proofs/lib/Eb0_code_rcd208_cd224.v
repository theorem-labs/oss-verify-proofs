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

Definition W_132818 : bv 32 := 0x00020593.
Lemma F_132818 : fetch_word AsanUbsan.M.loaded_segments (0x13285c : word) = Some W_132818.
Proof. vm_refl. Qed.
Lemma D_132818 : decode_any W_132818 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13281c : bv 32 := 0xfa85b583.
Lemma F_13281c : fetch_word AsanUbsan.M.loaded_segments (0x132860 : word) = Some W_13281c.
Proof. vm_refl. Qed.
Lemma D_13281c : decode_any W_13281c = Some (Load SZ8 true 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_132820 : bv 32 := 0x02051513.
Lemma F_132820 : fetch_word AsanUbsan.M.loaded_segments (0x132864 : word) = Some W_132820.
Proof. vm_refl. Qed.
Lemma D_132820 : decode_any W_132820 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_132824 : bv 32 := 0x01d55513.
Lemma F_132824 : fetch_word AsanUbsan.M.loaded_segments (0x132868 : word) = Some W_132824.
Proof. vm_refl. Qed.
Lemma D_132824 : decode_any W_132824 = Some (ShiftImm ALU_SRL 10 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_132828 : bv 32 := 0x00a58533.
Lemma F_132828 : fetch_word AsanUbsan.M.loaded_segments (0x13286c : word) = Some W_132828.
Proof. vm_refl. Qed.
Lemma D_132828 : decode_any W_132828 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_13282c : bv 32 := 0x00053503.
Lemma F_13282c : fetch_word AsanUbsan.M.loaded_segments (0x132870 : word) = Some W_13282c.
Proof. vm_refl. Qed.
Lemma D_13282c : decode_any W_13282c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_132830 : bv 32 := 0x00008067.
Lemma F_132830 : fetch_word AsanUbsan.M.loaded_segments (0x132874 : word) = Some W_132830.
Proof. vm_refl. Qed.
Lemma D_132830 : decode_any W_132830 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
