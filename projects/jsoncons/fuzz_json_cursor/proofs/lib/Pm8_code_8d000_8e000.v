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

Definition W_8d004 : bv 32 := 0x00152517.
Lemma F_8d004 : fetch_word Asan.M.loaded_segments (0x8d054 : word) = Some W_8d004.
Proof. vm_refl. Qed.
Lemma D_8d004 : decode_any W_8d004 = Some (Auipc 10 338, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d008 : bv 32 := 0xbcd50503.
Lemma F_8d008 : fetch_word Asan.M.loaded_segments (0x8d058 : word) = Some W_8d008.
Proof. vm_refl. Qed.
Lemma D_8d008 : decode_any W_8d008 = Some (Load SZ1 true 10 10 3021, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d00c : bv 32 := 0x00a03533.
Lemma F_8d00c : fetch_word Asan.M.loaded_segments (0x8d05c : word) = Some W_8d00c.
Proof. vm_refl. Qed.
Lemma D_8d00c : decode_any W_8d00c = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d010 : bv 32 := 0x00008067.
Lemma F_8d010 : fetch_word Asan.M.loaded_segments (0x8d060 : word) = Some W_8d010.
Proof. vm_refl. Qed.
Lemma D_8d010 : decode_any W_8d010 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d02c : bv 32 := 0x00152517.
Lemma F_8d02c : fetch_word Asan.M.loaded_segments (0x8d07c : word) = Some W_8d02c.
Proof. vm_refl. Qed.
Lemma D_8d02c : decode_any W_8d02c = Some (Auipc 10 338, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d030 : bv 32 := 0xba650503.
Lemma F_8d030 : fetch_word Asan.M.loaded_segments (0x8d080 : word) = Some W_8d030.
Proof. vm_refl. Qed.
Lemma D_8d030 : decode_any W_8d030 = Some (Load SZ1 true 10 10 2982, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d034 : bv 32 := 0x00a03533.
Lemma F_8d034 : fetch_word Asan.M.loaded_segments (0x8d084 : word) = Some W_8d034.
Proof. vm_refl. Qed.
Lemma D_8d034 : decode_any W_8d034 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d038 : bv 32 := 0x00008067.
Lemma F_8d038 : fetch_word Asan.M.loaded_segments (0x8d088 : word) = Some W_8d038.
Proof. vm_refl. Qed.
Lemma D_8d038 : decode_any W_8d038 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

