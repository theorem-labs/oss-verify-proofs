(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_ae654 : bv 32 := 0x000a5517.
Lemma F_ae654 : fetch_word Asan.M.loaded_segments (0xae6a4 : word) = Some W_ae654.
Proof. vm_refl. Qed.
Lemma D_ae654 : decode_any W_ae654 = Some (Auipc 10 165, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae658 : bv 32 := 0x6f453503.
Lemma F_ae658 : fetch_word Asan.M.loaded_segments (0xae6a8 : word) = Some W_ae658.
Proof. vm_refl. Qed.
Lemma D_ae658 : decode_any W_ae658 = Some (Load SZ8 true 10 10 1780, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae65c : bv 32 := 0x00450533.
Lemma F_ae65c : fetch_word Asan.M.loaded_segments (0xae6ac : word) = Some W_ae65c.
Proof. vm_refl. Qed.
Lemma D_ae65c : decode_any W_ae65c = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae660 : bv 32 := 0x00052503.
Lemma F_ae660 : fetch_word Asan.M.loaded_segments (0xae6b0 : word) = Some W_ae660.
Proof. vm_refl. Qed.
Lemma D_ae660 : decode_any W_ae660 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae664 : bv 32 := 0x00a02533.
Lemma F_ae664 : fetch_word Asan.M.loaded_segments (0xae6b4 : word) = Some W_ae664.
Proof. vm_refl. Qed.
Lemma D_ae664 : decode_any W_ae664 = Some (Op ALU_SLT 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae668 : bv 32 := 0x00008067.
Lemma F_ae668 : fetch_word Asan.M.loaded_segments (0xae6b8 : word) = Some W_ae668.
Proof. vm_refl. Qed.
Lemma D_ae668 : decode_any W_ae668 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

