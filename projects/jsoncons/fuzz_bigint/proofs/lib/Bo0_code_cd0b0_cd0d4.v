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

Definition W_cd0b0 : bv 32 := 0x00020593.
Lemma F_cd0b0 : fetch_word AsanUbsan.M.loaded_segments (0xcd0b0 : word) = Some W_cd0b0.
Proof. vm_refl. Qed.
Lemma D_cd0b0 : decode_any W_cd0b0 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0b4 : bv 32 := 0x00053603.
Lemma F_cd0b4 : fetch_word AsanUbsan.M.loaded_segments (0xcd0b4 : word) = Some W_cd0b4.
Proof. vm_refl. Qed.
Lemma D_cd0b4 : decode_any W_cd0b4 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0b8 : bv 32 := 0xff85b583.
Lemma F_cd0b8 : fetch_word AsanUbsan.M.loaded_segments (0xcd0b8 : word) = Some W_cd0b8.
Proof. vm_refl. Qed.
Lemma D_cd0b8 : decode_any W_cd0b8 = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0bc : bv 32 := 0x00853503.
Lemma F_cd0bc : fetch_word AsanUbsan.M.loaded_segments (0xcd0bc : word) = Some W_cd0bc.
Proof. vm_refl. Qed.
Lemma D_cd0bc : decode_any W_cd0bc = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0c0 : bv 32 := 0x00361613.
Lemma F_cd0c0 : fetch_word AsanUbsan.M.loaded_segments (0xcd0c0 : word) = Some W_cd0c0.
Proof. vm_refl. Qed.
Lemma D_cd0c0 : decode_any W_cd0c0 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0c4 : bv 32 := 0x00c585b3.
Lemma F_cd0c4 : fetch_word AsanUbsan.M.loaded_segments (0xcd0c4 : word) = Some W_cd0c4.
Proof. vm_refl. Qed.
Lemma D_cd0c4 : decode_any W_cd0c4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0c8 : bv 32 := 0x0005b583.
Lemma F_cd0c8 : fetch_word AsanUbsan.M.loaded_segments (0xcd0c8 : word) = Some W_cd0c8.
Proof. vm_refl. Qed.
Lemma D_cd0c8 : decode_any W_cd0c8 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0cc : bv 32 := 0x00b50533.
Lemma F_cd0cc : fetch_word AsanUbsan.M.loaded_segments (0xcd0cc : word) = Some W_cd0cc.
Proof. vm_refl. Qed.
Lemma D_cd0cc : decode_any W_cd0cc = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0d0 : bv 32 := 0x00008067.
Lemma F_cd0d0 : fetch_word AsanUbsan.M.loaded_segments (0xcd0d0 : word) = Some W_cd0d0.
Proof. vm_refl. Qed.
Lemma D_cd0d0 : decode_any W_cd0d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
