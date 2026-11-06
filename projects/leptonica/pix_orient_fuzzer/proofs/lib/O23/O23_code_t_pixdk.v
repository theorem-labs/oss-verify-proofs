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
Definition W_6cb14 : bv 32 := 0x00050493.
Lemma F_6cb14 : fetch_word Plain.M.loaded_segments (0x6cb6c : word) = Some W_6cb14.
Proof. vm_refl. Qed.
Lemma D_6cb14 : decode_any W_6cb14 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb18 : bv 32 := 0x03843503.
Lemma F_6cb18 : fetch_word Plain.M.loaded_segments (0x6cb70 : word) = Some W_6cb18.
Proof. vm_refl. Qed.
Lemma D_6cb18 : decode_any W_6cb18 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb1c : bv 32 := 0x00050863.
Lemma F_6cb1c : fetch_word Plain.M.loaded_segments (0x6cb74 : word) = Some W_6cb1c.
Proof. vm_refl. Qed.
Lemma D_6cb1c : decode_any W_6cb1c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb20 : bv 32 := 0x000a7597.
Lemma F_6cb20 : fetch_word Plain.M.loaded_segments (0x6cb78 : word) = Some W_6cb20.
Proof. vm_refl. Qed.
Lemma D_6cb20 : decode_any W_6cb20 = Some (Auipc 11 167, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb24 : bv 32 := 0xc605b583.
Lemma F_6cb24 : fetch_word Plain.M.loaded_segments (0x6cb7c : word) = Some W_6cb24.
Proof. vm_refl. Qed.
Lemma D_6cb24 : decode_any W_6cb24 = Some (Load SZ8 true 11 11 3168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb28 : bv 32 := 0x000580e7.
Lemma F_6cb28 : fetch_word Plain.M.loaded_segments (0x6cb80 : word) = Some W_6cb28.
Proof. vm_refl. Qed.
Lemma D_6cb28 : decode_any W_6cb28 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb2c : bv 32 := 0x02843503.
Lemma F_6cb2c : fetch_word Plain.M.loaded_segments (0x6cb84 : word) = Some W_6cb2c.
Proof. vm_refl. Qed.
Lemma D_6cb2c : decode_any W_6cb2c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb30 : bv 32 := 0x00050463.
Lemma F_6cb30 : fetch_word Plain.M.loaded_segments (0x6cb88 : word) = Some W_6cb30.
Proof. vm_refl. Qed.
Lemma D_6cb30 : decode_any W_6cb30 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb38 : bv 32 := 0x03043503.
Lemma F_6cb38 : fetch_word Plain.M.loaded_segments (0x6cb90 : word) = Some W_6cb38.
Proof. vm_refl. Qed.
Lemma D_6cb38 : decode_any W_6cb38 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb3c : bv 32 := 0x00a13023.
Lemma F_6cb3c : fetch_word Plain.M.loaded_segments (0x6cb94 : word) = Some W_6cb3c.
Proof. vm_refl. Qed.
Lemma D_6cb3c : decode_any W_6cb3c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb40 : bv 32 := 0x00050863.
Lemma F_6cb40 : fetch_word Plain.M.loaded_segments (0x6cb98 : word) = Some W_6cb40.
Proof. vm_refl. Qed.
Lemma D_6cb40 : decode_any W_6cb40 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb44 : bv 32 := 0x00010513.
Lemma F_6cb44 : fetch_word Plain.M.loaded_segments (0x6cb9c : word) = Some W_6cb44.
Proof. vm_refl. Qed.
Lemma D_6cb44 : decode_any W_6cb44 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb48 : bv 32 := 0x63c040ef.
Lemma F_6cb48 : fetch_word Plain.M.loaded_segments (0x6cba0 : word) = Some W_6cb48.
Proof. vm_refl. Qed.
Lemma D_6cb48 : decode_any W_6cb48 = Some (Jal 1 17980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb4c : bv 32 := 0x02043823.
Lemma F_6cb4c : fetch_word Plain.M.loaded_segments (0x6cba4 : word) = Some W_6cb4c.
Proof. vm_refl. Qed.
Lemma D_6cb4c : decode_any W_6cb4c = Some (Store SZ8 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb50 : bv 32 := 0x00040513.
Lemma F_6cb50 : fetch_word Plain.M.loaded_segments (0x6cba8 : word) = Some W_6cb50.
Proof. vm_refl. Qed.
Lemma D_6cb50 : decode_any W_6cb50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb54 : bv 32 := 0x7c88d0ef.
Lemma F_6cb54 : fetch_word Plain.M.loaded_segments (0x6cbac : word) = Some W_6cb54.
Proof. vm_refl. Qed.
Lemma D_6cb54 : decode_any W_6cb54 = Some (Jal 1 579528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cb58 : bv 32 := 0x00048513.
Lemma F_6cb58 : fetch_word Plain.M.loaded_segments (0x6cbb0 : word) = Some W_6cb58.
Proof. vm_refl. Qed.
Lemma D_6cb58 : decode_any W_6cb58 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
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
