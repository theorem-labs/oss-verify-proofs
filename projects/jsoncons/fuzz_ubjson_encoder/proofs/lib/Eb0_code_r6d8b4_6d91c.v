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

Definition W_88ca0 : bv 32 := 0x000b5597.
Lemma F_88ca0 : fetch_word AsanUbsan.M.loaded_segments (0x88cf0 : word) = Some W_88ca0.
Proof. vm_refl. Qed.
Lemma D_88ca0 : decode_any W_88ca0 = Some (Auipc 11 181, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ca4 : bv 32 := 0xbc85b583.
Lemma F_88ca4 : fetch_word AsanUbsan.M.loaded_segments (0x88cf4 : word) = Some W_88ca4.
Proof. vm_refl. Qed.
Lemma D_88ca4 : decode_any W_88ca4 = Some (Load SZ8 true 11 11 3016, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ca8 : bv 32 := 0x0905b583.
Lemma F_88ca8 : fetch_word AsanUbsan.M.loaded_segments (0x88cf8 : word) = Some W_88ca8.
Proof. vm_refl. Qed.
Lemma D_88ca8 : decode_any W_88ca8 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_88cac : bv 32 := 0x00058e63.
Lemma F_88cac : fetch_word AsanUbsan.M.loaded_segments (0x88cfc : word) = Some W_88cac.
Proof. vm_refl. Qed.
Lemma D_88cac : decode_any W_88cac = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_88cc8 : bv 32 := 0x00008067.
Lemma F_88cc8 : fetch_word AsanUbsan.M.loaded_segments (0x88d18 : word) = Some W_88cc8.
Proof. vm_refl. Qed.
Lemma D_88cc8 : decode_any W_88cc8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ce4 : bv 32 := 0x000b5597.
Lemma F_88ce4 : fetch_word AsanUbsan.M.loaded_segments (0x88d34 : word) = Some W_88ce4.
Proof. vm_refl. Qed.
Lemma D_88ce4 : decode_any W_88ce4 = Some (Auipc 11 181, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ce8 : bv 32 := 0xb845b583.
Lemma F_88ce8 : fetch_word AsanUbsan.M.loaded_segments (0x88d38 : word) = Some W_88ce8.
Proof. vm_refl. Qed.
Lemma D_88ce8 : decode_any W_88ce8 = Some (Load SZ8 true 11 11 2948, 4%Z).
Proof. vm_refl. Qed.

Definition W_88cec : bv 32 := 0x0905b583.
Lemma F_88cec : fetch_word AsanUbsan.M.loaded_segments (0x88d3c : word) = Some W_88cec.
Proof. vm_refl. Qed.
Lemma D_88cec : decode_any W_88cec = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_88cf0 : bv 32 := 0x00058a63.
Lemma F_88cf0 : fetch_word AsanUbsan.M.loaded_segments (0x88d40 : word) = Some W_88cf0.
Proof. vm_refl. Qed.
Lemma D_88cf0 : decode_any W_88cf0 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d04 : bv 32 := 0x00008067.
Lemma F_88d04 : fetch_word AsanUbsan.M.loaded_segments (0x88d54 : word) = Some W_88d04.
Proof. vm_refl. Qed.
Lemma D_88d04 : decode_any W_88d04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
