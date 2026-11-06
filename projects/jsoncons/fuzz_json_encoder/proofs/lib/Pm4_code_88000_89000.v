(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_88730 : bv 32 := 0x000e2517.
Lemma F_88730 : fetch_word Asan.M.loaded_segments (0x88780 : word) = Some W_88730.
Proof. vm_refl. Qed.
Lemma D_88730 : decode_any W_88730 = Some (Auipc 10 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88734 : bv 32 := 0x45850503.
Lemma F_88734 : fetch_word Asan.M.loaded_segments (0x88784 : word) = Some W_88734.
Proof. vm_refl. Qed.
Lemma D_88734 : decode_any W_88734 = Some (Load SZ1 true 10 10 1112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88738 : bv 32 := 0x0230000f.
Lemma F_88738 : fetch_word Asan.M.loaded_segments (0x88788 : word) = Some W_88738.
Proof. vm_refl. Qed.
Lemma D_88738 : decode_any W_88738 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8873c : bv 32 := 0xfff50513.
Lemma F_8873c : fetch_word Asan.M.loaded_segments (0x8878c : word) = Some W_8873c.
Proof. vm_refl. Qed.
Lemma D_8873c : decode_any W_8873c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88740 : bv 32 := 0x00153513.
Lemma F_88740 : fetch_word Asan.M.loaded_segments (0x88790 : word) = Some W_88740.
Proof. vm_refl. Qed.
Lemma D_88740 : decode_any W_88740 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88744 : bv 32 := 0x00008067.
Lemma F_88744 : fetch_word Asan.M.loaded_segments (0x88794 : word) = Some W_88744.
Proof. vm_refl. Qed.
Lemma D_88744 : decode_any W_88744 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

