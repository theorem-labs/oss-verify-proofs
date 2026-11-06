(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b80c4 : bv 32 := 0x00050213.
Lemma F_b80c4 : fetch_word Plain.M.loaded_segments (0xb8100 : word) = Some W_b80c4.
Proof. vm_refl. Qed.
Lemma D_b80c4 : decode_any W_b80c4 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b80c8 : bv 32 := 0x00000513.
Lemma F_b80c8 : fetch_word Plain.M.loaded_segments (0xb8104 : word) = Some W_b80c8.
Proof. vm_refl. Qed.
Lemma D_b80c8 : decode_any W_b80c8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b80cc : bv 32 := 0x00008067.
Lemma F_b80cc : fetch_word Plain.M.loaded_segments (0xb8108 : word) = Some W_b80cc.
Proof. vm_refl. Qed.
Lemma D_b80cc : decode_any W_b80cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

