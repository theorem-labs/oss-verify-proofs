(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_cc474 : bv 32 := 0x00050893.
Lemma F_cc474 : fetch_word Asan.M.loaded_segments (0xcc474 : word) = Some W_cc474.
Proof. vm_refl. Qed.
Lemma D_cc474 : decode_any W_cc474 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc478 : bv 32 := 0x00058513.
Lemma F_cc478 : fetch_word Asan.M.loaded_segments (0xcc478 : word) = Some W_cc478.
Proof. vm_refl. Qed.
Lemma D_cc478 : decode_any W_cc478 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc47c : bv 32 := 0x00060593.
Lemma F_cc47c : fetch_word Asan.M.loaded_segments (0xcc47c : word) = Some W_cc47c.
Proof. vm_refl. Qed.
Lemma D_cc47c : decode_any W_cc47c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc480 : bv 32 := 0x00068613.
Lemma F_cc480 : fetch_word Asan.M.loaded_segments (0xcc480 : word) = Some W_cc480.
Proof. vm_refl. Qed.
Lemma D_cc480 : decode_any W_cc480 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc484 : bv 32 := 0x00070693.
Lemma F_cc484 : fetch_word Asan.M.loaded_segments (0xcc484 : word) = Some W_cc484.
Proof. vm_refl. Qed.
Lemma D_cc484 : decode_any W_cc484 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc488 : bv 32 := 0x00078713.
Lemma F_cc488 : fetch_word Asan.M.loaded_segments (0xcc488 : word) = Some W_cc488.
Proof. vm_refl. Qed.
Lemma D_cc488 : decode_any W_cc488 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc48c : bv 32 := 0x00080793.
Lemma F_cc48c : fetch_word Asan.M.loaded_segments (0xcc48c : word) = Some W_cc48c.
Proof. vm_refl. Qed.
Lemma D_cc48c : decode_any W_cc48c = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc490 : bv 32 := 0x00000073.
Lemma F_cc490 : fetch_word Asan.M.loaded_segments (0xcc490 : word) = Some W_cc490.
Proof. vm_refl. Qed.
Lemma D_cc490 : decode_any W_cc490 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_cc490 : is_ecall W_cc490 = true.
Proof. reflexivity. Qed.

Definition W_cc494 : bv 32 := 0x00008067.
Lemma F_cc494 : fetch_word Asan.M.loaded_segments (0xcc494 : word) = Some W_cc494.
Proof. vm_refl. Qed.
Lemma D_cc494 : decode_any W_cc494 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc498 : bv 32 := 0xfddff06f.
Lemma F_cc498 : fetch_word Asan.M.loaded_segments (0xcc498 : word) = Some W_cc498.
Proof. vm_refl. Qed.
Lemma D_cc498 : decode_any W_cc498 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.
