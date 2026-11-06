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

Definition W_be3d0 : bv 32 := 0xfffff5b7.
Lemma F_be3d0 : fetch_word AsanUbsan.M.loaded_segments (0xbe3d0 : word) = Some W_be3d0.
Proof. vm_refl. Qed.
Lemma D_be3d0 : decode_any W_be3d0 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3d4 : bv 32 := 0x0015859b.
Lemma F_be3d4 : fetch_word AsanUbsan.M.loaded_segments (0xbe3d4 : word) = Some W_be3d4.
Proof. vm_refl. Qed.
Lemma D_be3d4 : decode_any W_be3d4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3d8 : bv 32 := 0x02b56663.
Lemma F_be3d8 : fetch_word AsanUbsan.M.loaded_segments (0xbe3d8 : word) = Some W_be3d8.
Proof. vm_refl. Qed.
Lemma D_be3d8 : decode_any W_be3d8 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3dc : bv 32 := 0xff010113.
Lemma F_be3dc : fetch_word AsanUbsan.M.loaded_segments (0xbe3dc : word) = Some W_be3dc.
Proof. vm_refl. Qed.
Lemma D_be3dc : decode_any W_be3dc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3e0 : bv 32 := 0x00113423.
Lemma F_be3e0 : fetch_word AsanUbsan.M.loaded_segments (0xbe3e0 : word) = Some W_be3e0.
Proof. vm_refl. Qed.
Lemma D_be3e0 : decode_any W_be3e0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3e4 : bv 32 := 0x00813023.
Lemma F_be3e4 : fetch_word AsanUbsan.M.loaded_segments (0xbe3e4 : word) = Some W_be3e4.
Proof. vm_refl. Qed.
Lemma D_be3e4 : decode_any W_be3e4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3e8 : bv 32 := 0x40a0043b.
Lemma F_be3e8 : fetch_word AsanUbsan.M.loaded_segments (0xbe3e8 : word) = Some W_be3e8.
Proof. vm_refl. Qed.
Lemma D_be3e8 : decode_any W_be3e8 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3ec : bv 32 := 0x981ff0ef.
Lemma F_be3ec : fetch_word AsanUbsan.M.loaded_segments (0xbe3ec : word) = Some W_be3ec.
Proof. vm_refl. Qed.
Lemma D_be3ec : decode_any W_be3ec = Some (Jal 1 2095488, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3f0 : bv 32 := 0x00852023.
Lemma F_be3f0 : fetch_word AsanUbsan.M.loaded_segments (0xbe3f0 : word) = Some W_be3f0.
Proof. vm_refl. Qed.
Lemma D_be3f0 : decode_any W_be3f0 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3f4 : bv 32 := 0xfff00513.
Lemma F_be3f4 : fetch_word AsanUbsan.M.loaded_segments (0xbe3f4 : word) = Some W_be3f4.
Proof. vm_refl. Qed.
Lemma D_be3f4 : decode_any W_be3f4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3f8 : bv 32 := 0x00813083.
Lemma F_be3f8 : fetch_word AsanUbsan.M.loaded_segments (0xbe3f8 : word) = Some W_be3f8.
Proof. vm_refl. Qed.
Lemma D_be3f8 : decode_any W_be3f8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_be3fc : bv 32 := 0x00013403.
Lemma F_be3fc : fetch_word AsanUbsan.M.loaded_segments (0xbe3fc : word) = Some W_be3fc.
Proof. vm_refl. Qed.
Lemma D_be3fc : decode_any W_be3fc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be400 : bv 32 := 0x01010113.
Lemma F_be400 : fetch_word AsanUbsan.M.loaded_segments (0xbe400 : word) = Some W_be400.
Proof. vm_refl. Qed.
Lemma D_be400 : decode_any W_be400 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_be404 : bv 32 := 0x00008067.
Lemma F_be404 : fetch_word AsanUbsan.M.loaded_segments (0xbe404 : word) = Some W_be404.
Proof. vm_refl. Qed.
Lemma D_be404 : decode_any W_be404 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
