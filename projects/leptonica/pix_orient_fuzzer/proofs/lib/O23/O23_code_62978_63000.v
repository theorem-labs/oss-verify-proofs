(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_62ff4 : bv 32 := 0xff010113.
Lemma F_62ff4 : fetch_word Plain.M.loaded_segments (0x6304c : word) = Some W_62ff4.
Proof. vm_refl. Qed.
Lemma D_62ff4 : decode_any W_62ff4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ff8 : bv 32 := 0x00113423.
Lemma F_62ff8 : fetch_word Plain.M.loaded_segments (0x63050 : word) = Some W_62ff8.
Proof. vm_refl. Qed.
Lemma D_62ff8 : decode_any W_62ff8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ffc : bv 32 := 0x00813023.
Lemma F_62ffc : fetch_word Plain.M.loaded_segments (0x63054 : word) = Some W_62ffc.
Proof. vm_refl. Qed.
Lemma D_62ffc : decode_any W_62ffc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.
