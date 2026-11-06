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

Definition W_71734 : bv 32 := 0x00000593.
Lemma F_71734 : fetch_word AsanUbsan.M.loaded_segments (0x71734 : word) = Some W_71734.
Proof. vm_refl. Qed.
Lemma D_71734 : decode_any W_71734 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71738 : bv 32 := 0x00b50633.
Lemma F_71738 : fetch_word AsanUbsan.M.loaded_segments (0x71738 : word) = Some W_71738.
Proof. vm_refl. Qed.
Lemma D_71738 : decode_any W_71738 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7173c : bv 32 := 0x00064603.
Lemma F_7173c : fetch_word AsanUbsan.M.loaded_segments (0x7173c : word) = Some W_7173c.
Proof. vm_refl. Qed.
Lemma D_7173c : decode_any W_7173c = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71740 : bv 32 := 0x00158593.
Lemma F_71740 : fetch_word AsanUbsan.M.loaded_segments (0x71740 : word) = Some W_71740.
Proof. vm_refl. Qed.
Lemma D_71740 : decode_any W_71740 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71744 : bv 32 := 0xfe061ae3.
Lemma F_71744 : fetch_word AsanUbsan.M.loaded_segments (0x71744 : word) = Some W_71744.
Proof. vm_refl. Qed.
Lemma D_71744 : decode_any W_71744 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_71748 : bv 32 := 0xfff58513.
Lemma F_71748 : fetch_word AsanUbsan.M.loaded_segments (0x71748 : word) = Some W_71748.
Proof. vm_refl. Qed.
Lemma D_71748 : decode_any W_71748 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7174c : bv 32 := 0x00008067.
Lemma F_7174c : fetch_word AsanUbsan.M.loaded_segments (0x7174c : word) = Some W_7174c.
Proof. vm_refl. Qed.
Lemma D_7174c : decode_any W_7174c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
