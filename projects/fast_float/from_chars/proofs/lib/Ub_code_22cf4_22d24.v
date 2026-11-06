(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_22cf4 : bv 32 := 0x00054517.
Lemma F_22cf4 : fetch_word Ubsan.M.loaded_segments (0x22cf4 : word) = Some W_22cf4.
Proof. vm_refl. Qed.
Lemma D_22cf4 : decode_any W_22cf4 = Some (Auipc 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22cf8 : bv 32 := 0x13054503.
Lemma F_22cf8 : fetch_word Ubsan.M.loaded_segments (0x22cf8 : word) = Some W_22cf8.
Proof. vm_refl. Qed.
Lemma D_22cf8 : decode_any W_22cf8 = Some (Load SZ1 false 10 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22cfc : bv 32 := 0x00051463.
Lemma F_22cfc : fetch_word Ubsan.M.loaded_segments (0x22cfc : word) = Some W_22cfc.
Proof. vm_refl. Qed.
Lemma D_22cfc : decode_any W_22cfc = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22d00 : bv 32 := 0x00008067.
Lemma F_22d00 : fetch_word Ubsan.M.loaded_segments (0x22d00 : word) = Some W_22d00.
Proof. vm_refl. Qed.
Lemma D_22d00 : decode_any W_22d00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22d04 : bv 32 := 0xff010113.
Lemma F_22d04 : fetch_word Ubsan.M.loaded_segments (0x22d04 : word) = Some W_22d04.
Proof. vm_refl. Qed.
Lemma D_22d04 : decode_any W_22d04 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22d08 : bv 32 := 0x00113423.
Lemma F_22d08 : fetch_word Ubsan.M.loaded_segments (0x22d08 : word) = Some W_22d08.
Proof. vm_refl. Qed.
Lemma D_22d08 : decode_any W_22d08 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22d0c : bv 32 := 0x00043517.
Lemma F_22d0c : fetch_word Ubsan.M.loaded_segments (0x22d0c : word) = Some W_22d0c.
Proof. vm_refl. Qed.
Lemma D_22d0c : decode_any W_22d0c = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22d10 : bv 32 := 0xd5c53503.
Lemma F_22d10 : fetch_word Ubsan.M.loaded_segments (0x22d10 : word) = Some W_22d10.
Proof. vm_refl. Qed.
Lemma D_22d10 : decode_any W_22d10 = Some (Load SZ8 true 10 10 3420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22d14 : bv 32 := 0x00053503.
Lemma F_22d14 : fetch_word Ubsan.M.loaded_segments (0x22d14 : word) = Some W_22d14.
Proof. vm_refl. Qed.
Lemma D_22d14 : decode_any W_22d14 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22d18 : bv 32 := 0x6ec320ef.
Lemma F_22d18 : fetch_word Ubsan.M.loaded_segments (0x22d18 : word) = Some W_22d18.
Proof. vm_refl. Qed.
Lemma D_22d18 : decode_any W_22d18 = Some (Jal 1 206572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22d1c : bv 32 := 0x04d00513.
Lemma F_22d1c : fetch_word Ubsan.M.loaded_segments (0x22d1c : word) = Some W_22d1c.
Proof. vm_refl. Qed.
Lemma D_22d1c : decode_any W_22d1c = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22d20 : bv 32 := 0x1dd3e0ef.
Lemma F_22d20 : fetch_word Ubsan.M.loaded_segments (0x22d20 : word) = Some W_22d20.
Proof. vm_refl. Qed.
Lemma D_22d20 : decode_any W_22d20 = Some (Jal 1 256476, 4%Z).
Proof. vm_refl. Qed.
