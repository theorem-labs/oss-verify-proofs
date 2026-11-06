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

Definition W_1348a0 : bv 32 := 0x0004b503.
Lemma F_1348a0 : fetch_word AsanUbsan.M.loaded_segments (0x1348e8 : word) = Some W_1348a0.
Proof. vm_refl. Qed.
Lemma D_1348a0 : decode_any W_1348a0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1348a4 : bv 32 := 0x00848493.
Lemma F_1348a4 : fetch_word AsanUbsan.M.loaded_segments (0x1348ec : word) = Some W_1348a4.
Proof. vm_refl. Qed.
Lemma D_1348a4 : decode_any W_1348a4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1348a8 : bv 32 := 0xfe051ce3.
Lemma F_1348a8 : fetch_word AsanUbsan.M.loaded_segments (0x1348f0 : word) = Some W_1348a8.
Proof. vm_refl. Qed.
Lemma D_1348a8 : decode_any W_1348a8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_13495c : bv 32 := 0x00b53023.
Lemma F_13495c : fetch_word AsanUbsan.M.loaded_segments (0x1349a4 : word) = Some W_13495c.
Proof. vm_refl. Qed.
Lemma D_13495c : decode_any W_13495c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_134960 : bv 32 := 0x00158593.
Lemma F_134960 : fetch_word AsanUbsan.M.loaded_segments (0x1349a8 : word) = Some W_134960.
Proof. vm_refl. Qed.
Lemma D_134960 : decode_any W_134960 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_134964 : bv 32 := 0xfff5c683.
Lemma F_134964 : fetch_word AsanUbsan.M.loaded_segments (0x1349ac : word) = Some W_134964.
Proof. vm_refl. Qed.
Lemma D_134964 : decode_any W_134964 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_134968 : bv 32 := 0xfec68ae3.
Lemma F_134968 : fetch_word AsanUbsan.M.loaded_segments (0x1349b0 : word) = Some W_134968.
Proof. vm_refl. Qed.
Lemma D_134968 : decode_any W_134968 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_13496c : bv 32 := 0xfe069ae3.
Lemma F_13496c : fetch_word AsanUbsan.M.loaded_segments (0x1349b4 : word) = Some W_13496c.
Proof. vm_refl. Qed.
Lemma D_13496c : decode_any W_13496c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_134f84 : bv 32 := 0x00020513.
Lemma F_134f84 : fetch_word AsanUbsan.M.loaded_segments (0x134fc0 : word) = Some W_134f84.
Proof. vm_refl. Qed.
Lemma D_134f84 : decode_any W_134f84 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_134f88 : bv 32 := 0xf5c50513.
Lemma F_134f88 : fetch_word AsanUbsan.M.loaded_segments (0x134fc4 : word) = Some W_134f88.
Proof. vm_refl. Qed.
Lemma D_134f88 : decode_any W_134f88 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

Definition W_134f8c : bv 32 := 0x00008067.
Lemma F_134f8c : fetch_word AsanUbsan.M.loaded_segments (0x134fc8 : word) = Some W_134f8c.
Proof. vm_refl. Qed.
Lemma D_134f8c : decode_any W_134f8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

