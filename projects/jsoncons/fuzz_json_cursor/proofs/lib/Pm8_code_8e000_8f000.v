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

Definition W_8ecd4 : bv 32 := 0x000c4597.
Lemma F_8ecd4 : fetch_word Asan.M.loaded_segments (0x8ed24 : word) = Some W_8ecd4.
Proof. vm_refl. Qed.
Lemma D_8ecd4 : decode_any W_8ecd4 = Some (Auipc 11 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ecd8 : bv 32 := 0x4045b583.
Lemma F_8ecd8 : fetch_word Asan.M.loaded_segments (0x8ed28 : word) = Some W_8ecd8.
Proof. vm_refl. Qed.
Lemma D_8ecd8 : decode_any W_8ecd8 = Some (Load SZ8 true 11 11 1028, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ecdc : bv 32 := 0x0905b583.
Lemma F_8ecdc : fetch_word Asan.M.loaded_segments (0x8ed2c : word) = Some W_8ecdc.
Proof. vm_refl. Qed.
Lemma D_8ecdc : decode_any W_8ecdc = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ece0 : bv 32 := 0x00058e63.
Lemma F_8ece0 : fetch_word Asan.M.loaded_segments (0x8ed30 : word) = Some W_8ece0.
Proof. vm_refl. Qed.
Lemma D_8ece0 : decode_any W_8ece0 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ecfc : bv 32 := 0x00008067.
Lemma F_8ecfc : fetch_word Asan.M.loaded_segments (0x8ed4c : word) = Some W_8ecfc.
Proof. vm_refl. Qed.
Lemma D_8ecfc : decode_any W_8ecfc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ed18 : bv 32 := 0x000c4597.
Lemma F_8ed18 : fetch_word Asan.M.loaded_segments (0x8ed68 : word) = Some W_8ed18.
Proof. vm_refl. Qed.
Lemma D_8ed18 : decode_any W_8ed18 = Some (Auipc 11 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ed1c : bv 32 := 0x3c05b583.
Lemma F_8ed1c : fetch_word Asan.M.loaded_segments (0x8ed6c : word) = Some W_8ed1c.
Proof. vm_refl. Qed.
Lemma D_8ed1c : decode_any W_8ed1c = Some (Load SZ8 true 11 11 960, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ed20 : bv 32 := 0x0905b583.
Lemma F_8ed20 : fetch_word Asan.M.loaded_segments (0x8ed70 : word) = Some W_8ed20.
Proof. vm_refl. Qed.
Lemma D_8ed20 : decode_any W_8ed20 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ed24 : bv 32 := 0x00058a63.
Lemma F_8ed24 : fetch_word Asan.M.loaded_segments (0x8ed74 : word) = Some W_8ed24.
Proof. vm_refl. Qed.
Lemma D_8ed24 : decode_any W_8ed24 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ed38 : bv 32 := 0x00008067.
Lemma F_8ed38 : fetch_word Asan.M.loaded_segments (0x8ed88 : word) = Some W_8ed38.
Proof. vm_refl. Qed.
Lemma D_8ed38 : decode_any W_8ed38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

