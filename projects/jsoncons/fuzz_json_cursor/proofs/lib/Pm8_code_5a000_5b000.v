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

Definition W_5a000 : bv 32 := 0x02010113.
Lemma F_5a000 : fetch_word Asan.M.loaded_segments (0x5a050 : word) = Some W_5a000.
Proof. vm_refl. Qed.
Lemma D_5a000 : decode_any W_5a000 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a004 : bv 32 := 0x00008067.
Lemma F_5a004 : fetch_word Asan.M.loaded_segments (0x5a054 : word) = Some W_5a004.
Proof. vm_refl. Qed.
Lemma D_5a004 : decode_any W_5a004 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

