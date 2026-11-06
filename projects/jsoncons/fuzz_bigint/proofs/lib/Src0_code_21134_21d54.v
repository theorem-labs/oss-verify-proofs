(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_21134 : bv 32 := 0x00008067.
Lemma F_21134 : fetch_word Plain.M.loaded_segments (0x21134 : word) = Some W_21134.
Proof. vm_refl. Qed.
Lemma D_21134 : decode_any W_21134 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_212a8 : bv 32 := 0x00008067.
Lemma F_212a8 : fetch_word Plain.M.loaded_segments (0x212a8 : word) = Some W_212a8.
Proof. vm_refl. Qed.
Lemma D_212a8 : decode_any W_212a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21468 : bv 32 := 0x00008067.
Lemma F_21468 : fetch_word Plain.M.loaded_segments (0x21468 : word) = Some W_21468.
Proof. vm_refl. Qed.
Lemma D_21468 : decode_any W_21468 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21604 : bv 32 := 0x00079a63.
Lemma F_21604 : fetch_word Plain.M.loaded_segments (0x21604 : word) = Some W_21604.
Proof. vm_refl. Qed.
Lemma D_21604 : decode_any W_21604 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_2161c : bv 32 := 0x00008067.
Lemma F_2161c : fetch_word Plain.M.loaded_segments (0x2161c : word) = Some W_2161c.
Proof. vm_refl. Qed.
Lemma D_2161c : decode_any W_2161c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21628 : bv 32 := 0x00008067.
Lemma F_21628 : fetch_word Plain.M.loaded_segments (0x21628 : word) = Some W_21628.
Proof. vm_refl. Qed.
Lemma D_21628 : decode_any W_21628 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ae0 : bv 32 := 0x04f76463.
Lemma F_21ae0 : fetch_word Plain.M.loaded_segments (0x21ae0 : word) = Some W_21ae0.
Proof. vm_refl. Qed.
Lemma D_21ae0 : decode_any W_21ae0 = Some (Branch BC_LTU 14 15 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ae4 : bv 32 := 0x00e7f863.
Lemma F_21ae4 : fetch_word Plain.M.loaded_segments (0x21ae4 : word) = Some W_21ae4.
Proof. vm_refl. Qed.
Lemma D_21ae4 : decode_any W_21ae4 = Some (Branch BC_GEU 15 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b18 : bv 32 := 0xfce7e8e3.
Lemma F_21b18 : fetch_word Plain.M.loaded_segments (0x21b18 : word) = Some W_21b18.
Proof. vm_refl. Qed.
Lemma D_21b18 : decode_any W_21b18 = Some (Branch BC_LTU 15 14 8144, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b24 : bv 32 := 0xfef772e3.
Lemma F_21b24 : fetch_word Plain.M.loaded_segments (0x21b24 : word) = Some W_21b24.
Proof. vm_refl. Qed.
Lemma D_21b24 : decode_any W_21b24 = Some (Branch BC_GEU 14 15 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b2c : bv 32 := 0x00008067.
Lemma F_21b2c : fetch_word Plain.M.loaded_segments (0x21b2c : word) = Some W_21b2c.
Proof. vm_refl. Qed.
Lemma D_21b2c : decode_any W_21b2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b8c : bv 32 := 0x00008067.
Lemma F_21b8c : fetch_word Plain.M.loaded_segments (0x21b8c : word) = Some W_21b8c.
Proof. vm_refl. Qed.
Lemma D_21b8c : decode_any W_21b8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21d50 : bv 32 := 0x00008067.
Lemma F_21d50 : fetch_word Plain.M.loaded_segments (0x21d50 : word) = Some W_21d50.
Proof. vm_refl. Qed.
Lemma D_21d50 : decode_any W_21d50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
