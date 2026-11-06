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
Definition W_afa20 : bv 32 := 0x000b2517.
Lemma F_afa20 : fetch_word Asan.M.loaded_segments (0xafa70 : word) = Some W_afa20.
Proof. vm_refl. Qed.
Lemma D_afa20 : decode_any W_afa20 = Some (Auipc 10 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa24 : bv 32 := 0xe0853503.
Lemma F_afa24 : fetch_word Asan.M.loaded_segments (0xafa74 : word) = Some W_afa24.
Proof. vm_refl. Qed.
Lemma D_afa24 : decode_any W_afa24 = Some (Load SZ8 true 10 10 3592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa28 : bv 32 := 0x00450533.
Lemma F_afa28 : fetch_word Asan.M.loaded_segments (0xafa78 : word) = Some W_afa28.
Proof. vm_refl. Qed.
Lemma D_afa28 : decode_any W_afa28 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa2c : bv 32 := 0x00052503.
Lemma F_afa2c : fetch_word Asan.M.loaded_segments (0xafa7c : word) = Some W_afa2c.
Proof. vm_refl. Qed.
Lemma D_afa2c : decode_any W_afa2c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa30 : bv 32 := 0x00a02533.
Lemma F_afa30 : fetch_word Asan.M.loaded_segments (0xafa80 : word) = Some W_afa30.
Proof. vm_refl. Qed.
Lemma D_afa30 : decode_any W_afa30 = Some (Op ALU_SLT 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa34 : bv 32 := 0x00008067.
Lemma F_afa34 : fetch_word Asan.M.loaded_segments (0xafa84 : word) = Some W_afa34.
Proof. vm_refl. Qed.
Lemma D_afa34 : decode_any W_afa34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

