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
Definition W_9103c : bv 32 := 0x00000513.
Lemma F_9103c : fetch_word AsanUbsan.M.loaded_segments (0x91084 : word) = Some W_9103c.
Proof. vm_refl. Qed.
Lemma D_9103c : decode_any W_9103c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91040 : bv 32 := 0x01813083.
Lemma F_91040 : fetch_word AsanUbsan.M.loaded_segments (0x91088 : word) = Some W_91040.
Proof. vm_refl. Qed.
Lemma D_91040 : decode_any W_91040 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91044 : bv 32 := 0x01013403.
Lemma F_91044 : fetch_word AsanUbsan.M.loaded_segments (0x9108c : word) = Some W_91044.
Proof. vm_refl. Qed.
Lemma D_91044 : decode_any W_91044 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91048 : bv 32 := 0x00813483.
Lemma F_91048 : fetch_word AsanUbsan.M.loaded_segments (0x91090 : word) = Some W_91048.
Proof. vm_refl. Qed.
Lemma D_91048 : decode_any W_91048 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9104c : bv 32 := 0x02010113.
Lemma F_9104c : fetch_word AsanUbsan.M.loaded_segments (0x91094 : word) = Some W_9104c.
Proof. vm_refl. Qed.
Lemma D_9104c : decode_any W_9104c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91050 : bv 32 := 0x00008067.
Lemma F_91050 : fetch_word AsanUbsan.M.loaded_segments (0x91098 : word) = Some W_91050.
Proof. vm_refl. Qed.
Lemma D_91050 : decode_any W_91050 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91054 : bv 32 := 0x00000513.
Lemma F_91054 : fetch_word AsanUbsan.M.loaded_segments (0x9109c : word) = Some W_91054.
Proof. vm_refl. Qed.
Lemma D_91054 : decode_any W_91054 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91058 : bv 32 := 0x00008067.
Lemma F_91058 : fetch_word AsanUbsan.M.loaded_segments (0x910a0 : word) = Some W_91058.
Proof. vm_refl. Qed.
Lemma D_91058 : decode_any W_91058 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9105c : bv 32 := 0x00008067.
Lemma F_9105c : fetch_word AsanUbsan.M.loaded_segments (0x910a4 : word) = Some W_9105c.
Proof. vm_refl. Qed.
Lemma D_9105c : decode_any W_9105c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

