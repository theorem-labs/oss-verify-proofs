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
Definition W_b02f8 : bv 32 := 0x000b5517.
Lemma F_b02f8 : fetch_word AsanUbsan.M.loaded_segments (0xb0340 : word) = Some W_b02f8.
Proof. vm_refl. Qed.
Lemma D_b02f8 : decode_any W_b02f8 = Some (Auipc 10 181, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b02fc : bv 32 := 0xe3853503.
Lemma F_b02fc : fetch_word AsanUbsan.M.loaded_segments (0xb0344 : word) = Some W_b02fc.
Proof. vm_refl. Qed.
Lemma D_b02fc : decode_any W_b02fc = Some (Load SZ8 true 10 10 3640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b0300 : bv 32 := 0x00450533.
Lemma F_b0300 : fetch_word AsanUbsan.M.loaded_segments (0xb0348 : word) = Some W_b0300.
Proof. vm_refl. Qed.
Lemma D_b0300 : decode_any W_b0300 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b0304 : bv 32 := 0x00052503.
Lemma F_b0304 : fetch_word AsanUbsan.M.loaded_segments (0xb034c : word) = Some W_b0304.
Proof. vm_refl. Qed.
Lemma D_b0304 : decode_any W_b0304 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b0308 : bv 32 := 0x00a02533.
Lemma F_b0308 : fetch_word AsanUbsan.M.loaded_segments (0xb0350 : word) = Some W_b0308.
Proof. vm_refl. Qed.
Lemma D_b0308 : decode_any W_b0308 = Some (Op ALU_SLT 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b030c : bv 32 := 0x00008067.
Lemma F_b030c : fetch_word AsanUbsan.M.loaded_segments (0xb0354 : word) = Some W_b030c.
Proof. vm_refl. Qed.
Lemma D_b030c : decode_any W_b030c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

