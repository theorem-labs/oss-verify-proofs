(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_66354 : bv 32 := 0x00079517.
Lemma F_66354 : fetch_word AsanUbsan.M.loaded_segments (0x66354 : word) = Some W_66354.
Proof. vm_refl. Qed.
Lemma D_66354 : decode_any W_66354 = Some (Auipc 10 121, 4%Z).
Proof. vm_refl. Qed.

Definition W_66358 : bv 32 := 0x0c450503.
Lemma F_66358 : fetch_word AsanUbsan.M.loaded_segments (0x66358 : word) = Some W_66358.
Proof. vm_refl. Qed.
Lemma D_66358 : decode_any W_66358 = Some (Load SZ1 true 10 10 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_6635c : bv 32 := 0x0230000f.
Lemma F_6635c : fetch_word AsanUbsan.M.loaded_segments (0x6635c : word) = Some W_6635c.
Proof. vm_refl. Qed.
Lemma D_6635c : decode_any W_6635c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66360 : bv 32 := 0xfff50513.
Lemma F_66360 : fetch_word AsanUbsan.M.loaded_segments (0x66360 : word) = Some W_66360.
Proof. vm_refl. Qed.
Lemma D_66360 : decode_any W_66360 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_66364 : bv 32 := 0x00153513.
Lemma F_66364 : fetch_word AsanUbsan.M.loaded_segments (0x66364 : word) = Some W_66364.
Proof. vm_refl. Qed.
Lemma D_66364 : decode_any W_66364 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_66368 : bv 32 := 0x00008067.
Lemma F_66368 : fetch_word AsanUbsan.M.loaded_segments (0x66368 : word) = Some W_66368.
Proof. vm_refl. Qed.
Lemma D_66368 : decode_any W_66368 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
