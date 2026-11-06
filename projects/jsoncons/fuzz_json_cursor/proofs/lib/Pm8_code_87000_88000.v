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

Definition W_87364 : bv 32 := 0x000d6517.
Lemma F_87364 : fetch_word Asan.M.loaded_segments (0x873b4 : word) = Some W_87364.
Proof. vm_refl. Qed.
Lemma D_87364 : decode_any W_87364 = Some (Auipc 10 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_87368 : bv 32 := 0x2e450503.
Lemma F_87368 : fetch_word Asan.M.loaded_segments (0x873b8 : word) = Some W_87368.
Proof. vm_refl. Qed.
Lemma D_87368 : decode_any W_87368 = Some (Load SZ1 true 10 10 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_8736c : bv 32 := 0x0230000f.
Lemma F_8736c : fetch_word Asan.M.loaded_segments (0x873bc : word) = Some W_8736c.
Proof. vm_refl. Qed.
Lemma D_8736c : decode_any W_8736c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87370 : bv 32 := 0xfff50513.
Lemma F_87370 : fetch_word Asan.M.loaded_segments (0x873c0 : word) = Some W_87370.
Proof. vm_refl. Qed.
Lemma D_87370 : decode_any W_87370 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_87374 : bv 32 := 0x00153513.
Lemma F_87374 : fetch_word Asan.M.loaded_segments (0x873c4 : word) = Some W_87374.
Proof. vm_refl. Qed.
Lemma D_87374 : decode_any W_87374 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87378 : bv 32 := 0x00008067.
Lemma F_87378 : fetch_word Asan.M.loaded_segments (0x873c8 : word) = Some W_87378.
Proof. vm_refl. Qed.
Lemma D_87378 : decode_any W_87378 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

