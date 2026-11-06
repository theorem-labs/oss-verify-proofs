(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_aea1c : bv 32 := 0x000a6517.
Lemma F_aea1c : fetch_word AsanUbsan.M.loaded_segments (0xaea64 : word) = Some W_aea1c.
Proof. vm_refl. Qed.
Lemma D_aea1c : decode_any W_aea1c = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea20 : bv 32 := 0x6fc53503.
Lemma F_aea20 : fetch_word AsanUbsan.M.loaded_segments (0xaea68 : word) = Some W_aea20.
Proof. vm_refl. Qed.
Lemma D_aea20 : decode_any W_aea20 = Some (Load SZ8 true 10 10 1788, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea24 : bv 32 := 0x00450533.
Lemma F_aea24 : fetch_word AsanUbsan.M.loaded_segments (0xaea6c : word) = Some W_aea24.
Proof. vm_refl. Qed.
Lemma D_aea24 : decode_any W_aea24 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea28 : bv 32 := 0x00052503.
Lemma F_aea28 : fetch_word AsanUbsan.M.loaded_segments (0xaea70 : word) = Some W_aea28.
Proof. vm_refl. Qed.
Lemma D_aea28 : decode_any W_aea28 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea2c : bv 32 := 0x00a02533.
Lemma F_aea2c : fetch_word AsanUbsan.M.loaded_segments (0xaea74 : word) = Some W_aea2c.
Proof. vm_refl. Qed.
Lemma D_aea2c : decode_any W_aea2c = Some (Op ALU_SLT 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea30 : bv 32 := 0x00008067.
Lemma F_aea30 : fetch_word AsanUbsan.M.loaded_segments (0xaea78 : word) = Some W_aea30.
Proof. vm_refl. Qed.
Lemma D_aea30 : decode_any W_aea30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

