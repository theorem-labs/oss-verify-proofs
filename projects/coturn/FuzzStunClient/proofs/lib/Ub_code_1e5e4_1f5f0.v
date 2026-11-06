(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_1e808 : bv 32 := 0xff010113.
Lemma F_1e808 : fetch_word Ubsan.M.loaded_segments (0x1e808 : word) = Some W_1e808.
Proof. vm_refl. Qed.
Lemma D_1e808 : decode_any W_1e808 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e80c : bv 32 := 0x00113423.
Lemma F_1e80c : fetch_word Ubsan.M.loaded_segments (0x1e80c : word) = Some W_1e80c.
Proof. vm_refl. Qed.
Lemma D_1e80c : decode_any W_1e80c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e810 : bv 32 := 0x00813023.
Lemma F_1e810 : fetch_word Ubsan.M.loaded_segments (0x1e810 : word) = Some W_1e810.
Proof. vm_refl. Qed.
Lemma D_1e810 : decode_any W_1e810 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e814 : bv 32 := 0x00039517.
Lemma F_1e814 : fetch_word Ubsan.M.loaded_segments (0x1e814 : word) = Some W_1e814.
Proof. vm_refl. Qed.
Lemma D_1e814 : decode_any W_1e814 = Some (Auipc 10 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e818 : bv 32 := 0xaf450413.
Lemma F_1e818 : fetch_word Ubsan.M.loaded_segments (0x1e818 : word) = Some W_1e818.
Proof. vm_refl. Qed.
Lemma D_1e818 : decode_any W_1e818 = Some (OpImm ALU_ADD 8 10 2804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e81c : bv 32 := 0x00040513.
Lemma F_1e81c : fetch_word Ubsan.M.loaded_segments (0x1e81c : word) = Some W_1e81c.
Proof. vm_refl. Qed.
Lemma D_1e81c : decode_any W_1e81c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e820 : bv 32 := 0x209050ef.
Lemma F_1e820 : fetch_word Ubsan.M.loaded_segments (0x1e820 : word) = Some W_1e820.
Proof. vm_refl. Qed.
Lemma D_1e820 : decode_any W_1e820 = Some (Jal 1 23048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e824 : bv 32 := 0x00840513.
Lemma F_1e824 : fetch_word Ubsan.M.loaded_segments (0x1e824 : word) = Some W_1e824.
Proof. vm_refl. Qed.
Lemma D_1e824 : decode_any W_1e824 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e828 : bv 32 := 0x00813083.
Lemma F_1e828 : fetch_word Ubsan.M.loaded_segments (0x1e828 : word) = Some W_1e828.
Proof. vm_refl. Qed.
Lemma D_1e828 : decode_any W_1e828 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e82c : bv 32 := 0x00013403.
Lemma F_1e82c : fetch_word Ubsan.M.loaded_segments (0x1e82c : word) = Some W_1e82c.
Proof. vm_refl. Qed.
Lemma D_1e82c : decode_any W_1e82c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e830 : bv 32 := 0x01010113.
Lemma F_1e830 : fetch_word Ubsan.M.loaded_segments (0x1e830 : word) = Some W_1e830.
Proof. vm_refl. Qed.
Lemma D_1e830 : decode_any W_1e830 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e834 : bv 32 := 0x00008067.
Lemma F_1e834 : fetch_word Ubsan.M.loaded_segments (0x1e834 : word) = Some W_1e834.
Proof. vm_refl. Qed.
Lemma D_1e834 : decode_any W_1e834 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
