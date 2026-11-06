(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6cae4 : bv 32 := 0xfe010113.
Lemma F_6cae4 : fetch_word Plain.M.loaded_segments (0x6cb3c : word) = Some W_6cae4.
Proof. vm_refl. Qed.
Lemma D_6cae4 : decode_any W_6cae4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cae8 : bv 32 := 0x00113c23.
Lemma F_6cae8 : fetch_word Plain.M.loaded_segments (0x6cb40 : word) = Some W_6cae8.
Proof. vm_refl. Qed.
Lemma D_6cae8 : decode_any W_6cae8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caec : bv 32 := 0x00813823.
Lemma F_6caec : fetch_word Plain.M.loaded_segments (0x6cb44 : word) = Some W_6caec.
Proof. vm_refl. Qed.
Lemma D_6caec : decode_any W_6caec = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caf0 : bv 32 := 0x00913423.
Lemma F_6caf0 : fetch_word Plain.M.loaded_segments (0x6cb48 : word) = Some W_6caf0.
Proof. vm_refl. Qed.
Lemma D_6caf0 : decode_any W_6caf0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caf4 : bv 32 := 0x06050863.
Lemma F_6caf4 : fetch_word Plain.M.loaded_segments (0x6cb4c : word) = Some W_6caf4.
Proof. vm_refl. Qed.
Lemma D_6caf4 : decode_any W_6caf4 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caf8 : bv 32 := 0x00053403.
Lemma F_6caf8 : fetch_word Plain.M.loaded_segments (0x6cb50 : word) = Some W_6caf8.
Proof. vm_refl. Qed.
Lemma D_6caf8 : decode_any W_6caf8 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cafc : bv 32 := 0x0a040063.
Lemma F_6cafc : fetch_word Plain.M.loaded_segments (0x6cb54 : word) = Some W_6cafc.
Proof. vm_refl. Qed.
Lemma D_6cafc : decode_any W_6cafc = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb00 : bv 32 := 0x01440593.
Lemma F_6cb00 : fetch_word Plain.M.loaded_segments (0x6cb58 : word) = Some W_6cb00.
Proof. vm_refl. Qed.
Lemma D_6cb00 : decode_any W_6cb00 = Some (OpImm ALU_ADD 11 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb04 : bv 32 := 0xfff00613.
Lemma F_6cb04 : fetch_word Plain.M.loaded_segments (0x6cb5c : word) = Some W_6cb04.
Proof. vm_refl. Qed.
Lemma D_6cb04 : decode_any W_6cb04 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb08 : bv 32 := 0x06c5a5af.
Lemma F_6cb08 : fetch_word Plain.M.loaded_segments (0x6cb60 : word) = Some W_6cb08.
Proof. vm_refl. Qed.
Lemma D_6cb08 : decode_any W_6cb08 = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb0c : bv 32 := 0x00100613.
Lemma F_6cb0c : fetch_word Plain.M.loaded_segments (0x6cb64 : word) = Some W_6cb0c.
Proof. vm_refl. Qed.
Lemma D_6cb0c : decode_any W_6cb0c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb10 : bv 32 := 0x04c59663.
Lemma F_6cb10 : fetch_word Plain.M.loaded_segments (0x6cb68 : word) = Some W_6cb10.
Proof. vm_refl. Qed.
Lemma D_6cb10 : decode_any W_6cb10 = Some (Branch BC_NE 11 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb5c : bv 32 := 0x00053023.
Lemma F_6cb5c : fetch_word Plain.M.loaded_segments (0x6cbb4 : word) = Some W_6cb5c.
Proof. vm_refl. Qed.
Lemma D_6cb5c : decode_any W_6cb5c = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb60 : bv 32 := 0x03c0006f.
Lemma F_6cb60 : fetch_word Plain.M.loaded_segments (0x6cbb8 : word) = Some W_6cb60.
Proof. vm_refl. Qed.
Lemma D_6cb60 : decode_any W_6cb60 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb9c : bv 32 := 0x01813083.
Lemma F_6cb9c : fetch_word Plain.M.loaded_segments (0x6cbf4 : word) = Some W_6cb9c.
Proof. vm_refl. Qed.
Lemma D_6cb9c : decode_any W_6cb9c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cba0 : bv 32 := 0x01013403.
Lemma F_6cba0 : fetch_word Plain.M.loaded_segments (0x6cbf8 : word) = Some W_6cba0.
Proof. vm_refl. Qed.
Lemma D_6cba0 : decode_any W_6cba0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cba4 : bv 32 := 0x00813483.
Lemma F_6cba4 : fetch_word Plain.M.loaded_segments (0x6cbfc : word) = Some W_6cba4.
Proof. vm_refl. Qed.
Lemma D_6cba4 : decode_any W_6cba4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cba8 : bv 32 := 0x02010113.
Lemma F_6cba8 : fetch_word Plain.M.loaded_segments (0x6cc00 : word) = Some W_6cba8.
Proof. vm_refl. Qed.
Lemma D_6cba8 : decode_any W_6cba8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbac : bv 32 := 0x00008067.
Lemma F_6cbac : fetch_word Plain.M.loaded_segments (0x6cc04 : word) = Some W_6cbac.
Proof. vm_refl. Qed.
Lemma D_6cbac : decode_any W_6cbac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
