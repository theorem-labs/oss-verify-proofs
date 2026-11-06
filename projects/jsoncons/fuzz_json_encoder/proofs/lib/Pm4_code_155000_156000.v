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
Definition W_155688 : bv 32 := 0x00020593.
Lemma F_155688 : fetch_word Asan.M.loaded_segments (0x1556cc : word) = Some W_155688.
Proof. vm_refl. Qed.
Lemma D_155688 : decode_any W_155688 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15568c : bv 32 := 0xfa85b583.
Lemma F_15568c : fetch_word Asan.M.loaded_segments (0x1556d0 : word) = Some W_15568c.
Proof. vm_refl. Qed.
Lemma D_15568c : decode_any W_15568c = Some (Load SZ8 true 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155690 : bv 32 := 0x02051513.
Lemma F_155690 : fetch_word Asan.M.loaded_segments (0x1556d4 : word) = Some W_155690.
Proof. vm_refl. Qed.
Lemma D_155690 : decode_any W_155690 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155694 : bv 32 := 0x01d55513.
Lemma F_155694 : fetch_word Asan.M.loaded_segments (0x1556d8 : word) = Some W_155694.
Proof. vm_refl. Qed.
Lemma D_155694 : decode_any W_155694 = Some (ShiftImm ALU_SRL 10 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155698 : bv 32 := 0x00a58533.
Lemma F_155698 : fetch_word Asan.M.loaded_segments (0x1556dc : word) = Some W_155698.
Proof. vm_refl. Qed.
Lemma D_155698 : decode_any W_155698 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15569c : bv 32 := 0x00053503.
Lemma F_15569c : fetch_word Asan.M.loaded_segments (0x1556e0 : word) = Some W_15569c.
Proof. vm_refl. Qed.
Lemma D_15569c : decode_any W_15569c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1556a0 : bv 32 := 0x00008067.
Lemma F_1556a0 : fetch_word Asan.M.loaded_segments (0x1556e4 : word) = Some W_1556a0.
Proof. vm_refl. Qed.
Lemma D_1556a0 : decode_any W_1556a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

