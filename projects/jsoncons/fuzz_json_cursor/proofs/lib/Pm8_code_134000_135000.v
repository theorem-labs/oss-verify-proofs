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

Definition W_13418c : bv 32 := 0xfffff5b7.
Lemma F_13418c : fetch_word Asan.M.loaded_segments (0x1341d0 : word) = Some W_13418c.
Proof. vm_refl. Qed.
Lemma D_13418c : decode_any W_13418c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_134190 : bv 32 := 0x0015859b.
Lemma F_134190 : fetch_word Asan.M.loaded_segments (0x1341d4 : word) = Some W_134190.
Proof. vm_refl. Qed.
Lemma D_134190 : decode_any W_134190 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_134194 : bv 32 := 0x02b56663.
Lemma F_134194 : fetch_word Asan.M.loaded_segments (0x1341d8 : word) = Some W_134194.
Proof. vm_refl. Qed.
Lemma D_134194 : decode_any W_134194 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_134198 : bv 32 := 0xff010113.
Lemma F_134198 : fetch_word Asan.M.loaded_segments (0x1341dc : word) = Some W_134198.
Proof. vm_refl. Qed.
Lemma D_134198 : decode_any W_134198 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_13419c : bv 32 := 0x00113423.
Lemma F_13419c : fetch_word Asan.M.loaded_segments (0x1341e0 : word) = Some W_13419c.
Proof. vm_refl. Qed.
Lemma D_13419c : decode_any W_13419c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1341a0 : bv 32 := 0x00813023.
Lemma F_1341a0 : fetch_word Asan.M.loaded_segments (0x1341e4 : word) = Some W_1341a0.
Proof. vm_refl. Qed.
Lemma D_1341a0 : decode_any W_1341a0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1341a4 : bv 32 := 0x40a0043b.
Lemma F_1341a4 : fetch_word Asan.M.loaded_segments (0x1341e8 : word) = Some W_1341a4.
Proof. vm_refl. Qed.
Lemma D_1341a4 : decode_any W_1341a4 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1341a8 : bv 32 := 0x8b9ff0ef.
Lemma F_1341a8 : fetch_word Asan.M.loaded_segments (0x1341ec : word) = Some W_1341a8.
Proof. vm_refl. Qed.
Lemma D_1341a8 : decode_any W_1341a8 = Some (Jal 1 2095288, 4%Z).
Proof. vm_refl. Qed.

Definition W_1341ac : bv 32 := 0x00852023.
Lemma F_1341ac : fetch_word Asan.M.loaded_segments (0x1341f0 : word) = Some W_1341ac.
Proof. vm_refl. Qed.
Lemma D_1341ac : decode_any W_1341ac = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1341b0 : bv 32 := 0xfff00513.
Lemma F_1341b0 : fetch_word Asan.M.loaded_segments (0x1341f4 : word) = Some W_1341b0.
Proof. vm_refl. Qed.
Lemma D_1341b0 : decode_any W_1341b0 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1341b4 : bv 32 := 0x00813083.
Lemma F_1341b4 : fetch_word Asan.M.loaded_segments (0x1341f8 : word) = Some W_1341b4.
Proof. vm_refl. Qed.
Lemma D_1341b4 : decode_any W_1341b4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1341b8 : bv 32 := 0x00013403.
Lemma F_1341b8 : fetch_word Asan.M.loaded_segments (0x1341fc : word) = Some W_1341b8.
Proof. vm_refl. Qed.
Lemma D_1341b8 : decode_any W_1341b8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1341bc : bv 32 := 0x01010113.
Lemma F_1341bc : fetch_word Asan.M.loaded_segments (0x134200 : word) = Some W_1341bc.
Proof. vm_refl. Qed.
Lemma D_1341bc : decode_any W_1341bc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1341c0 : bv 32 := 0x00008067.
Lemma F_1341c0 : fetch_word Asan.M.loaded_segments (0x134204 : word) = Some W_1341c0.
Proof. vm_refl. Qed.
Lemma D_1341c0 : decode_any W_1341c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

