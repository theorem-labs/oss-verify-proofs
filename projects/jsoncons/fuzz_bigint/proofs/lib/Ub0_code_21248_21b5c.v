(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_21248 : bv 32 := 0x00008067.
Lemma F_21248 : fetch_word Ubsan.M.loaded_segments (0x21248 : word) = Some W_21248.
Proof. vm_refl. Qed.
Lemma D_21248 : decode_any W_21248 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21364 : bv 32 := 0x04050063.
Lemma F_21364 : fetch_word Ubsan.M.loaded_segments (0x21364 : word) = Some W_21364.
Proof. vm_refl. Qed.
Lemma D_21364 : decode_any W_21364 = Some (Branch BC_EQ 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_213a0 : bv 32 := 0xfc0516e3.
Lemma F_213a0 : fetch_word Ubsan.M.loaded_segments (0x213a0 : word) = Some W_213a0.
Proof. vm_refl. Qed.
Lemma D_213a0 : decode_any W_213a0 = Some (Branch BC_NE 10 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_213cc : bv 32 := 0x00008067.
Lemma F_213cc : fetch_word Ubsan.M.loaded_segments (0x213cc : word) = Some W_213cc.
Proof. vm_refl. Qed.
Lemma D_213cc : decode_any W_213cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_214dc : bv 32 := 0x00008067.
Lemma F_214dc : fetch_word Ubsan.M.loaded_segments (0x214dc : word) = Some W_214dc.
Proof. vm_refl. Qed.
Lemma D_214dc : decode_any W_214dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21564 : bv 32 := 0x00008067.
Lemma F_21564 : fetch_word Ubsan.M.loaded_segments (0x21564 : word) = Some W_21564.
Proof. vm_refl. Qed.
Lemma D_21564 : decode_any W_21564 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2174c : bv 32 := 0x00008067.
Lemma F_2174c : fetch_word Ubsan.M.loaded_segments (0x2174c : word) = Some W_2174c.
Proof. vm_refl. Qed.
Lemma D_2174c : decode_any W_2174c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_218f0 : bv 32 := 0x00008067.
Lemma F_218f0 : fetch_word Ubsan.M.loaded_segments (0x218f0 : word) = Some W_218f0.
Proof. vm_refl. Qed.
Lemma D_218f0 : decode_any W_218f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b2c : bv 32 := 0x00089c63.
Lemma F_21b2c : fetch_word Ubsan.M.loaded_segments (0x21b2c : word) = Some W_21b2c.
Proof. vm_refl. Qed.
Lemma D_21b2c : decode_any W_21b2c = Some (Branch BC_NE 17 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b4c : bv 32 := 0x00008067.
Lemma F_21b4c : fetch_word Ubsan.M.loaded_segments (0x21b4c : word) = Some W_21b4c.
Proof. vm_refl. Qed.
Lemma D_21b4c : decode_any W_21b4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b58 : bv 32 := 0x00008067.
Lemma F_21b58 : fetch_word Ubsan.M.loaded_segments (0x21b58 : word) = Some W_21b58.
Proof. vm_refl. Qed.
Lemma D_21b58 : decode_any W_21b58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
