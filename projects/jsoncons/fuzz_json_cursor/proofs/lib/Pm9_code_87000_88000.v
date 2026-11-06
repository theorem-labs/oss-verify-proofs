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

Definition W_8772c : bv 32 := 0x000d7517.
Lemma F_8772c : fetch_word AsanUbsan.M.loaded_segments (0x87774 : word) = Some W_8772c.
Proof. vm_refl. Qed.
Lemma D_8772c : decode_any W_8772c = Some (Auipc 10 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_87730 : bv 32 := 0x26450503.
Lemma F_87730 : fetch_word AsanUbsan.M.loaded_segments (0x87778 : word) = Some W_87730.
Proof. vm_refl. Qed.
Lemma D_87730 : decode_any W_87730 = Some (Load SZ1 true 10 10 612, 4%Z).
Proof. vm_refl. Qed.

Definition W_87734 : bv 32 := 0x0230000f.
Lemma F_87734 : fetch_word AsanUbsan.M.loaded_segments (0x8777c : word) = Some W_87734.
Proof. vm_refl. Qed.
Lemma D_87734 : decode_any W_87734 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87738 : bv 32 := 0xfff50513.
Lemma F_87738 : fetch_word AsanUbsan.M.loaded_segments (0x87780 : word) = Some W_87738.
Proof. vm_refl. Qed.
Lemma D_87738 : decode_any W_87738 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8773c : bv 32 := 0x00153513.
Lemma F_8773c : fetch_word AsanUbsan.M.loaded_segments (0x87784 : word) = Some W_8773c.
Proof. vm_refl. Qed.
Lemma D_8773c : decode_any W_8773c = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87740 : bv 32 := 0x00008067.
Lemma F_87740 : fetch_word AsanUbsan.M.loaded_segments (0x87788 : word) = Some W_87740.
Proof. vm_refl. Qed.
Lemma D_87740 : decode_any W_87740 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

