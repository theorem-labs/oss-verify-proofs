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

Definition W_62360 : bv 32 := 0x0007c517.
Lemma F_62360 : fetch_word AsanUbsan.M.loaded_segments (0x62360 : word) = Some W_62360.
Proof. vm_refl. Qed.
Lemma D_62360 : decode_any W_62360 = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_62364 : bv 32 := 0xc4050513.
Lemma F_62364 : fetch_word AsanUbsan.M.loaded_segments (0x62364 : word) = Some W_62364.
Proof. vm_refl. Qed.
Lemma D_62364 : decode_any W_62364 = Some (OpImm ALU_ADD 10 10 3136, 4%Z).
Proof. vm_refl. Qed.

Definition W_62368 : bv 32 := 0x00054583.
Lemma F_62368 : fetch_word AsanUbsan.M.loaded_segments (0x62368 : word) = Some W_62368.
Proof. vm_refl. Qed.
Lemma D_62368 : decode_any W_62368 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6236c : bv 32 := 0x00058663.
Lemma F_6236c : fetch_word AsanUbsan.M.loaded_segments (0x6236c : word) = Some W_6236c.
Proof. vm_refl. Qed.
Lemma D_6236c : decode_any W_6236c = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_62370 : bv 32 := 0x00452503.
Lemma F_62370 : fetch_word AsanUbsan.M.loaded_segments (0x62370 : word) = Some W_62370.
Proof. vm_refl. Qed.
Lemma D_62370 : decode_any W_62370 = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_62374 : bv 32 := 0x5f16b06f.
Lemma F_62374 : fetch_word AsanUbsan.M.loaded_segments (0x62374 : word) = Some W_62374.
Proof. vm_refl. Qed.
Lemma D_62374 : decode_any W_62374 = Some (Jal 0 441840, 4%Z).
Proof. vm_refl. Qed.
