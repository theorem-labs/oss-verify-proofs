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
Definition W_140f18 : bv 32 := 0x0004b503.
Lemma F_140f18 : fetch_word Asan.M.loaded_segments (0x140f68 : word) = Some W_140f18.
Proof. vm_refl. Qed.
Lemma D_140f18 : decode_any W_140f18 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140f1c : bv 32 := 0x00848493.
Lemma F_140f1c : fetch_word Asan.M.loaded_segments (0x140f6c : word) = Some W_140f1c.
Proof. vm_refl. Qed.
Lemma D_140f1c : decode_any W_140f1c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140f20 : bv 32 := 0xfe051ce3.
Lemma F_140f20 : fetch_word Asan.M.loaded_segments (0x140f70 : word) = Some W_140f20.
Proof. vm_refl. Qed.
Lemma D_140f20 : decode_any W_140f20 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140fd4 : bv 32 := 0x00b53023.
Lemma F_140fd4 : fetch_word Asan.M.loaded_segments (0x141024 : word) = Some W_140fd4.
Proof. vm_refl. Qed.
Lemma D_140fd4 : decode_any W_140fd4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140fd8 : bv 32 := 0x00158593.
Lemma F_140fd8 : fetch_word Asan.M.loaded_segments (0x141028 : word) = Some W_140fd8.
Proof. vm_refl. Qed.
Lemma D_140fd8 : decode_any W_140fd8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140fdc : bv 32 := 0xfff5c683.
Lemma F_140fdc : fetch_word Asan.M.loaded_segments (0x14102c : word) = Some W_140fdc.
Proof. vm_refl. Qed.
Lemma D_140fdc : decode_any W_140fdc = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140fe0 : bv 32 := 0xfec68ae3.
Lemma F_140fe0 : fetch_word Asan.M.loaded_segments (0x141030 : word) = Some W_140fe0.
Proof. vm_refl. Qed.
Lemma D_140fe0 : decode_any W_140fe0 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_140fe4 : bv 32 := 0xfe069ae3.
Lemma F_140fe4 : fetch_word Asan.M.loaded_segments (0x141034 : word) = Some W_140fe4.
Proof. vm_refl. Qed.
Lemma D_140fe4 : decode_any W_140fe4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

