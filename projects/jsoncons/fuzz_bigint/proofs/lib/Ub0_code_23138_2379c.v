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

Definition W_23138 : bv 32 := 0x00008067.
Lemma F_23138 : fetch_word Ubsan.M.loaded_segments (0x23138 : word) = Some W_23138.
Proof. vm_refl. Qed.
Lemma D_23138 : decode_any W_23138 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_231d4 : bv 32 := 0x00008067.
Lemma F_231d4 : fetch_word Ubsan.M.loaded_segments (0x231d4 : word) = Some W_231d4.
Proof. vm_refl. Qed.
Lemma D_231d4 : decode_any W_231d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_233cc : bv 32 := 0x00008067.
Lemma F_233cc : fetch_word Ubsan.M.loaded_segments (0x233cc : word) = Some W_233cc.
Proof. vm_refl. Qed.
Lemma D_233cc : decode_any W_233cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2358c : bv 32 := 0x00008067.
Lemma F_2358c : fetch_word Ubsan.M.loaded_segments (0x2358c : word) = Some W_2358c.
Proof. vm_refl. Qed.
Lemma D_2358c : decode_any W_2358c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_235f4 : bv 32 := 0x00008067.
Lemma F_235f4 : fetch_word Ubsan.M.loaded_segments (0x235f4 : word) = Some W_235f4.
Proof. vm_refl. Qed.
Lemma D_235f4 : decode_any W_235f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_23798 : bv 32 := 0x00008067.
Lemma F_23798 : fetch_word Ubsan.M.loaded_segments (0x23798 : word) = Some W_23798.
Proof. vm_refl. Qed.
Lemma D_23798 : decode_any W_23798 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
