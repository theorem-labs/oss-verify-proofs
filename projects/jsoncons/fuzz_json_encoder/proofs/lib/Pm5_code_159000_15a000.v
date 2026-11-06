(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1590a8 : bv 32 := 0x00020593.
Lemma F_1590a8 : fetch_word AsanUbsan.M.loaded_segments (0x1590e4 : word) = Some W_1590a8.
Proof. vm_refl. Qed.
Lemma D_1590a8 : decode_any W_1590a8 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590ac : bv 32 := 0xfa85b583.
Lemma F_1590ac : fetch_word AsanUbsan.M.loaded_segments (0x1590e8 : word) = Some W_1590ac.
Proof. vm_refl. Qed.
Lemma D_1590ac : decode_any W_1590ac = Some (Load SZ8 true 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590b0 : bv 32 := 0x02051513.
Lemma F_1590b0 : fetch_word AsanUbsan.M.loaded_segments (0x1590ec : word) = Some W_1590b0.
Proof. vm_refl. Qed.
Lemma D_1590b0 : decode_any W_1590b0 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590b4 : bv 32 := 0x01d55513.
Lemma F_1590b4 : fetch_word AsanUbsan.M.loaded_segments (0x1590f0 : word) = Some W_1590b4.
Proof. vm_refl. Qed.
Lemma D_1590b4 : decode_any W_1590b4 = Some (ShiftImm ALU_SRL 10 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590b8 : bv 32 := 0x00a58533.
Lemma F_1590b8 : fetch_word AsanUbsan.M.loaded_segments (0x1590f4 : word) = Some W_1590b8.
Proof. vm_refl. Qed.
Lemma D_1590b8 : decode_any W_1590b8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590bc : bv 32 := 0x00053503.
Lemma F_1590bc : fetch_word AsanUbsan.M.loaded_segments (0x1590f8 : word) = Some W_1590bc.
Proof. vm_refl. Qed.
Lemma D_1590bc : decode_any W_1590bc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590c0 : bv 32 := 0x00008067.
Lemma F_1590c0 : fetch_word AsanUbsan.M.loaded_segments (0x1590fc : word) = Some W_1590c0.
Proof. vm_refl. Qed.
Lemma D_1590c0 : decode_any W_1590c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

