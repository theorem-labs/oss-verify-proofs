(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_bcce0 : bv 32 := 0x00050213.
Lemma F_bcce0 : fetch_word Ubsan.M.loaded_segments (0xc0708 : word) = Some W_bcce0.
Proof. vm_refl. Qed.
Lemma D_bcce0 : decode_any W_bcce0 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcce4 : bv 32 := 0x00000513.
Lemma F_bcce4 : fetch_word Ubsan.M.loaded_segments (0xc070c : word) = Some W_bcce4.
Proof. vm_refl. Qed.
Lemma D_bcce4 : decode_any W_bcce4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcce8 : bv 32 := 0x00008067.
Lemma F_bcce8 : fetch_word Ubsan.M.loaded_segments (0xc0710 : word) = Some W_bcce8.
Proof. vm_refl. Qed.
Lemma D_bcce8 : decode_any W_bcce8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

