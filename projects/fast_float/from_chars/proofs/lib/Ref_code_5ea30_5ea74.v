(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

Require OSSVerify.Proofs.fast_float.from_chars.lib.Ox.F112_005.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5ea30 : bv 32 := 0xfe010113.
Lemma F_5ea30 : fetch_word Plain.M.loaded_segments (0x5ea30 : word) = Some W_5ea30.
Proof. vm_refl. Qed.
Lemma D_5ea30 : decode_any W_5ea30 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea34 : bv 32 := 0x00113c23.
Lemma F_5ea34 : fetch_word Plain.M.loaded_segments (0x5ea34 : word) = Some W_5ea34.
Proof. vm_refl. Qed.
Lemma D_5ea34 : decode_any W_5ea34 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea38 : bv 32 := 0x00813823.
Lemma F_5ea38 : fetch_word Plain.M.loaded_segments (0x5ea38 : word) = Some W_5ea38.
Proof. vm_refl. Qed.
Lemma D_5ea38 : decode_any W_5ea38 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea3c : bv 32 := 0x00913423.
Lemma F_5ea3c : fetch_word Plain.M.loaded_segments (0x5ea3c : word) = Some W_5ea3c.
Proof. vm_refl. Qed.
Lemma D_5ea3c : decode_any W_5ea3c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea40 : bv 32 := 0x00058413.
Lemma F_5ea40 : fetch_word Plain.M.loaded_segments (0x5ea40 : word) = Some W_5ea40.
Proof. vm_refl. Qed.
Lemma D_5ea40 : decode_any W_5ea40 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea44 : bv 32 := 0x00050493.
Lemma F_5ea44 : fetch_word Plain.M.loaded_segments (0x5ea44 : word) = Some W_5ea44.
Proof. vm_refl. Qed.
Lemma D_5ea44 : decode_any W_5ea44 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea48 : bv 32 := 0x00000593.
Lemma F_5ea48 : fetch_word Plain.M.loaded_segments (0x5ea48 : word) = Some W_5ea48.
Proof. vm_refl. Qed.
Lemma D_5ea48 : decode_any W_5ea48 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea4c : bv 32 := 0x00040613.
Lemma F_5ea4c : fetch_word Plain.M.loaded_segments (0x5ea4c : word) = Some W_5ea4c.
Proof. vm_refl. Qed.
Lemma D_5ea4c : decode_any W_5ea4c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea50 : bv 32 := 0xfa4ff0ef.
Lemma F_5ea50 : fetch_word Plain.M.loaded_segments (0x5ea50 : word) = Some W_5ea50.
Proof. vm_refl. Qed.
Lemma D_5ea50 : decode_any W_5ea50 = Some (Jal 1 2095012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea54 : bv 32 := 0x00050463.
Lemma F_5ea54 : fetch_word Plain.M.loaded_segments (0x5ea54 : word) = Some W_5ea54.
Proof. vm_refl. Qed.
Lemma D_5ea54 : decode_any W_5ea54 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea58 : bv 32 := 0x40950433.
Lemma F_5ea58 : fetch_word Plain.M.loaded_segments (0x5ea58 : word) = Some W_5ea58.
Proof. vm_refl. Qed.
Lemma D_5ea58 : decode_any W_5ea58 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea5c : bv 32 := 0x00040513.
Lemma F_5ea5c : fetch_word Plain.M.loaded_segments (0x5ea5c : word) = Some W_5ea5c.
Proof. vm_refl. Qed.
Lemma D_5ea5c : decode_any W_5ea5c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea60 : bv 32 := 0x01813083.
Lemma F_5ea60 : fetch_word Plain.M.loaded_segments (0x5ea60 : word) = Some W_5ea60.
Proof. vm_refl. Qed.
Lemma D_5ea60 : decode_any W_5ea60 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea64 : bv 32 := 0x01013403.
Lemma F_5ea64 : fetch_word Plain.M.loaded_segments (0x5ea64 : word) = Some W_5ea64.
Proof. vm_refl. Qed.
Lemma D_5ea64 : decode_any W_5ea64 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea68 : bv 32 := 0x00813483.
Lemma F_5ea68 : fetch_word Plain.M.loaded_segments (0x5ea68 : word) = Some W_5ea68.
Proof. vm_refl. Qed.
Lemma D_5ea68 : decode_any W_5ea68 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea6c : bv 32 := 0x02010113.
Lemma F_5ea6c : fetch_word Plain.M.loaded_segments (0x5ea6c : word) = Some W_5ea6c.
Proof. vm_refl. Qed.
Lemma D_5ea6c : decode_any W_5ea6c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ea70 : bv 32 := 0x00008067.
Lemma F_5ea70 : fetch_word Plain.M.loaded_segments (0x5ea70 : word) = Some W_5ea70.
Proof. vm_refl. Qed.
Lemma D_5ea70 : decode_any W_5ea70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
