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

Definition W_7d0c0 : bv 32 := 0x000c9517.
Lemma F_7d0c0 : fetch_word AsanUbsan.M.loaded_segments (0x7d110 : word) = Some W_7d0c0.
Proof. vm_refl. Qed.
Lemma D_7d0c0 : decode_any W_7d0c0 = Some (Auipc 10 201, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d0c4 : bv 32 := 0x85050513.
Lemma F_7d0c4 : fetch_word AsanUbsan.M.loaded_segments (0x7d114 : word) = Some W_7d0c4.
Proof. vm_refl. Qed.
Lemma D_7d0c4 : decode_any W_7d0c4 = Some (OpImm ALU_ADD 10 10 2128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d0c8 : bv 32 := 0x00054583.
Lemma F_7d0c8 : fetch_word AsanUbsan.M.loaded_segments (0x7d118 : word) = Some W_7d0c8.
Proof. vm_refl. Qed.
Lemma D_7d0c8 : decode_any W_7d0c8 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d0cc : bv 32 := 0x00058663.
Lemma F_7d0cc : fetch_word AsanUbsan.M.loaded_segments (0x7d11c : word) = Some W_7d0cc.
Proof. vm_refl. Qed.
Lemma D_7d0cc : decode_any W_7d0cc = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d0d0 : bv 32 := 0x00452503.
Lemma F_7d0d0 : fetch_word AsanUbsan.M.loaded_segments (0x7d120 : word) = Some W_7d0d0.
Proof. vm_refl. Qed.
Lemma D_7d0d0 : decode_any W_7d0d0 = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d0d4 : bv 32 := 0x738b506f.
Lemma F_7d0d4 : fetch_word AsanUbsan.M.loaded_segments (0x7d124 : word) = Some W_7d0d4.
Proof. vm_refl. Qed.
Lemma D_7d0d4 : decode_any W_7d0d4 = Some (Jal 0 743224, 4%Z).
Proof. vm_refl. Qed.
