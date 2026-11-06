(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

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
Definition W_5eb5c : bv 32 := 0x00037597.
Lemma F_5eb5c : fetch_word Plain.M.loaded_segments (0x5eb5c : word) = Some W_5eb5c.
Proof. vm_refl. Qed.
Lemma D_5eb5c : decode_any W_5eb5c = Some (Auipc 11 55, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb60 : bv 32 := 0x30758683.
Lemma F_5eb60 : fetch_word Plain.M.loaded_segments (0x5eb60 : word) = Some W_5eb60.
Proof. vm_refl. Qed.
Lemma D_5eb60 : decode_any W_5eb60 = Some (Load SZ1 true 13 11 775, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb64 : bv 32 := 0x1e068863.
Lemma F_5eb64 : fetch_word Plain.M.loaded_segments (0x5eb64 : word) = Some W_5eb64.
Proof. vm_refl. Qed.
Lemma D_5eb64 : decode_any W_5eb64 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb68 : bv 32 := 0x00000613.
Lemma F_5eb68 : fetch_word Plain.M.loaded_segments (0x5eb68 : word) = Some W_5eb68.
Proof. vm_refl. Qed.
Lemma D_5eb68 : decode_any W_5eb68 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb6c : bv 32 := 0x80000737.
Lemma F_5eb6c : fetch_word Plain.M.loaded_segments (0x5eb6c : word) = Some W_5eb6c.
Proof. vm_refl. Qed.
Lemma D_5eb6c : decode_any W_5eb6c = Some (Lui 14 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb70 : bv 32 := 0x0017071b.
Lemma F_5eb70 : fetch_word Plain.M.loaded_segments (0x5eb70 : word) = Some W_5eb70.
Proof. vm_refl. Qed.
Lemma D_5eb70 : decode_any W_5eb70 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb74 : bv 32 := 0x160527af.
Lemma F_5eb74 : fetch_word Plain.M.loaded_segments (0x5eb74 : word) = Some W_5eb74.
Proof. vm_refl. Qed.
Lemma D_5eb74 : decode_any W_5eb74 = Some (Lr AW true true 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb78 : bv 32 := 0x00c79663.
Lemma F_5eb78 : fetch_word Plain.M.loaded_segments (0x5eb78 : word) = Some W_5eb78.
Proof. vm_refl. Qed.
Lemma D_5eb78 : decode_any W_5eb78 = Some (Branch BC_NE 15 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb7c : bv 32 := 0x1ee5282f.
Lemma F_5eb7c : fetch_word Plain.M.loaded_segments (0x5eb7c : word) = Some W_5eb7c.
Proof. vm_refl. Qed.
Lemma D_5eb7c : decode_any W_5eb7c = Some (Sc AW true true 16 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb80 : bv 32 := 0xfe081ae3.
Lemma F_5eb80 : fetch_word Plain.M.loaded_segments (0x5eb80 : word) = Some W_5eb80.
Proof. vm_refl. Qed.
Lemma D_5eb80 : decode_any W_5eb80 = Some (Branch BC_NE 16 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb84 : bv 32 := 0x0007861b.
Lemma F_5eb84 : fetch_word Plain.M.loaded_segments (0x5eb84 : word) = Some W_5eb84.
Proof. vm_refl. Qed.
Lemma D_5eb84 : decode_any W_5eb84 = Some (OpImm32 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb88 : bv 32 := 0x0006d463.
Lemma F_5eb88 : fetch_word Plain.M.loaded_segments (0x5eb88 : word) = Some W_5eb88.
Proof. vm_refl. Qed.
Lemma D_5eb88 : decode_any W_5eb88 = Some (Branch BC_GE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb8c : bv 32 := 0x300583a3.
Lemma F_5eb8c : fetch_word Plain.M.loaded_segments (0x5eb8c : word) = Some W_5eb8c.
Proof. vm_refl. Qed.
Lemma D_5eb8c : decode_any W_5eb8c = Some (Store SZ1 11 0 775, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb90 : bv 32 := 0x1c060263.
Lemma F_5eb90 : fetch_word Plain.M.loaded_segments (0x5eb90 : word) = Some W_5eb90.
Proof. vm_refl. Qed.
Lemma D_5eb90 : decode_any W_5eb90 = Some (Branch BC_EQ 12 0 452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb94 : bv 32 := 0x800007b7.
Lemma F_5eb94 : fetch_word Plain.M.loaded_segments (0x5eb94 : word) = Some W_5eb94.
Proof. vm_refl. Qed.
Lemma D_5eb94 : decode_any W_5eb94 = Some (Lui 15 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb98 : bv 32 := 0x00261593.
Lemma F_5eb98 : fetch_word Plain.M.loaded_segments (0x5eb98 : word) = Some W_5eb98.
Proof. vm_refl. Qed.
Lemma D_5eb98 : decode_any W_5eb98 = Some (ShiftImm ALU_SLL 11 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eb9c : bv 32 := 0xfff78793.
Lemma F_5eb9c : fetch_word Plain.M.loaded_segments (0x5eb9c : word) = Some W_5eb9c.
Proof. vm_refl. Qed.
Lemma D_5eb9c : decode_any W_5eb9c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eba0 : bv 32 := 0x0215d593.
Lemma F_5eba0 : fetch_word Plain.M.loaded_segments (0x5eba0 : word) = Some W_5eba0.
Proof. vm_refl. Qed.
Lemma D_5eba0 : decode_any W_5eba0 = Some (ShiftImm ALU_SRL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eba4 : bv 32 := 0x00b6063b.
Lemma F_5eba4 : fetch_word Plain.M.loaded_segments (0x5eba4 : word) = Some W_5eba4.
Proof. vm_refl. Qed.
Lemma D_5eba4 : decode_any W_5eba4 = Some (Op32 ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eba8 : bv 32 := 0x00f605b3.
Lemma F_5eba8 : fetch_word Plain.M.loaded_segments (0x5eba8 : word) = Some W_5eba8.
Proof. vm_refl. Qed.
Lemma D_5eba8 : decode_any W_5eba8 = Some (Op ALU_ADD 11 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebac : bv 32 := 0x0025859b.
Lemma F_5ebac : fetch_word Plain.M.loaded_segments (0x5ebac : word) = Some W_5ebac.
Proof. vm_refl. Qed.
Lemma D_5ebac : decode_any W_5ebac = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebb0 : bv 32 := 0x160526af.
Lemma F_5ebb0 : fetch_word Plain.M.loaded_segments (0x5ebb0 : word) = Some W_5ebb0.
Proof. vm_refl. Qed.
Lemma D_5ebb0 : decode_any W_5ebb0 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebb4 : bv 32 := 0x00c69663.
Lemma F_5ebb4 : fetch_word Plain.M.loaded_segments (0x5ebb4 : word) = Some W_5ebb4.
Proof. vm_refl. Qed.
Lemma D_5ebb4 : decode_any W_5ebb4 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebb8 : bv 32 := 0x1eb5272f.
Lemma F_5ebb8 : fetch_word Plain.M.loaded_segments (0x5ebb8 : word) = Some W_5ebb8.
Proof. vm_refl. Qed.
Lemma D_5ebb8 : decode_any W_5ebb8 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebbc : bv 32 := 0xfe071ae3.
Lemma F_5ebbc : fetch_word Plain.M.loaded_segments (0x5ebbc : word) = Some W_5ebbc.
Proof. vm_refl. Qed.
Lemma D_5ebbc : decode_any W_5ebbc = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebc0 : bv 32 := 0x0006859b.
Lemma F_5ebc0 : fetch_word Plain.M.loaded_segments (0x5ebc0 : word) = Some W_5ebc0.
Proof. vm_refl. Qed.
Lemma D_5ebc0 : decode_any W_5ebc0 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebc4 : bv 32 := 0x18c58863.
Lemma F_5ebc4 : fetch_word Plain.M.loaded_segments (0x5ebc4 : word) = Some W_5ebc4.
Proof. vm_refl. Qed.
Lemma D_5ebc4 : decode_any W_5ebc4 = Some (Branch BC_EQ 11 12 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebc8 : bv 32 := 0x01f5d613.
Lemma F_5ebc8 : fetch_word Plain.M.loaded_segments (0x5ebc8 : word) = Some W_5ebc8.
Proof. vm_refl. Qed.
Lemma D_5ebc8 : decode_any W_5ebc8 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebcc : bv 32 := 0x00f67633.
Lemma F_5ebcc : fetch_word Plain.M.loaded_segments (0x5ebcc : word) = Some W_5ebcc.
Proof. vm_refl. Qed.
Lemma D_5ebcc : decode_any W_5ebcc = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebd0 : bv 32 := 0x00c5863b.
Lemma F_5ebd0 : fetch_word Plain.M.loaded_segments (0x5ebd0 : word) = Some W_5ebd0.
Proof. vm_refl. Qed.
Lemma D_5ebd0 : decode_any W_5ebd0 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebd4 : bv 32 := 0x00c785b3.
Lemma F_5ebd4 : fetch_word Plain.M.loaded_segments (0x5ebd4 : word) = Some W_5ebd4.
Proof. vm_refl. Qed.
Lemma D_5ebd4 : decode_any W_5ebd4 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebd8 : bv 32 := 0x0025859b.
Lemma F_5ebd8 : fetch_word Plain.M.loaded_segments (0x5ebd8 : word) = Some W_5ebd8.
Proof. vm_refl. Qed.
Lemma D_5ebd8 : decode_any W_5ebd8 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebdc : bv 32 := 0x160526af.
Lemma F_5ebdc : fetch_word Plain.M.loaded_segments (0x5ebdc : word) = Some W_5ebdc.
Proof. vm_refl. Qed.
Lemma D_5ebdc : decode_any W_5ebdc = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebe0 : bv 32 := 0x00c69663.
Lemma F_5ebe0 : fetch_word Plain.M.loaded_segments (0x5ebe0 : word) = Some W_5ebe0.
Proof. vm_refl. Qed.
Lemma D_5ebe0 : decode_any W_5ebe0 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebe4 : bv 32 := 0x1eb5272f.
Lemma F_5ebe4 : fetch_word Plain.M.loaded_segments (0x5ebe4 : word) = Some W_5ebe4.
Proof. vm_refl. Qed.
Lemma D_5ebe4 : decode_any W_5ebe4 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebe8 : bv 32 := 0xfe071ae3.
Lemma F_5ebe8 : fetch_word Plain.M.loaded_segments (0x5ebe8 : word) = Some W_5ebe8.
Proof. vm_refl. Qed.
Lemma D_5ebe8 : decode_any W_5ebe8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebec : bv 32 := 0x0006859b.
Lemma F_5ebec : fetch_word Plain.M.loaded_segments (0x5ebec : word) = Some W_5ebec.
Proof. vm_refl. Qed.
Lemma D_5ebec : decode_any W_5ebec = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebf0 : bv 32 := 0x16c58263.
Lemma F_5ebf0 : fetch_word Plain.M.loaded_segments (0x5ebf0 : word) = Some W_5ebf0.
Proof. vm_refl. Qed.
Lemma D_5ebf0 : decode_any W_5ebf0 = Some (Branch BC_EQ 11 12 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebf4 : bv 32 := 0x01f5d613.
Lemma F_5ebf4 : fetch_word Plain.M.loaded_segments (0x5ebf4 : word) = Some W_5ebf4.
Proof. vm_refl. Qed.
Lemma D_5ebf4 : decode_any W_5ebf4 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebf8 : bv 32 := 0x00f67633.
Lemma F_5ebf8 : fetch_word Plain.M.loaded_segments (0x5ebf8 : word) = Some W_5ebf8.
Proof. vm_refl. Qed.
Lemma D_5ebf8 : decode_any W_5ebf8 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ebfc : bv 32 := 0x00c5863b.
Lemma F_5ebfc : fetch_word Plain.M.loaded_segments (0x5ebfc : word) = Some W_5ebfc.
Proof. vm_refl. Qed.
Lemma D_5ebfc : decode_any W_5ebfc = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec00 : bv 32 := 0x00c785b3.
Lemma F_5ec00 : fetch_word Plain.M.loaded_segments (0x5ec00 : word) = Some W_5ec00.
Proof. vm_refl. Qed.
Lemma D_5ec00 : decode_any W_5ec00 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec04 : bv 32 := 0x0025859b.
Lemma F_5ec04 : fetch_word Plain.M.loaded_segments (0x5ec04 : word) = Some W_5ec04.
Proof. vm_refl. Qed.
Lemma D_5ec04 : decode_any W_5ec04 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec08 : bv 32 := 0x160526af.
Lemma F_5ec08 : fetch_word Plain.M.loaded_segments (0x5ec08 : word) = Some W_5ec08.
Proof. vm_refl. Qed.
Lemma D_5ec08 : decode_any W_5ec08 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec0c : bv 32 := 0x00c69663.
Lemma F_5ec0c : fetch_word Plain.M.loaded_segments (0x5ec0c : word) = Some W_5ec0c.
Proof. vm_refl. Qed.
Lemma D_5ec0c : decode_any W_5ec0c = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec10 : bv 32 := 0x1eb5272f.
Lemma F_5ec10 : fetch_word Plain.M.loaded_segments (0x5ec10 : word) = Some W_5ec10.
Proof. vm_refl. Qed.
Lemma D_5ec10 : decode_any W_5ec10 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec14 : bv 32 := 0xfe071ae3.
Lemma F_5ec14 : fetch_word Plain.M.loaded_segments (0x5ec14 : word) = Some W_5ec14.
Proof. vm_refl. Qed.
Lemma D_5ec14 : decode_any W_5ec14 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec18 : bv 32 := 0x0006859b.
Lemma F_5ec18 : fetch_word Plain.M.loaded_segments (0x5ec18 : word) = Some W_5ec18.
Proof. vm_refl. Qed.
Lemma D_5ec18 : decode_any W_5ec18 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec1c : bv 32 := 0x12c58c63.
Lemma F_5ec1c : fetch_word Plain.M.loaded_segments (0x5ec1c : word) = Some W_5ec1c.
Proof. vm_refl. Qed.
Lemma D_5ec1c : decode_any W_5ec1c = Some (Branch BC_EQ 11 12 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec20 : bv 32 := 0x01f5d613.
Lemma F_5ec20 : fetch_word Plain.M.loaded_segments (0x5ec20 : word) = Some W_5ec20.
Proof. vm_refl. Qed.
Lemma D_5ec20 : decode_any W_5ec20 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec24 : bv 32 := 0x00f67633.
Lemma F_5ec24 : fetch_word Plain.M.loaded_segments (0x5ec24 : word) = Some W_5ec24.
Proof. vm_refl. Qed.
Lemma D_5ec24 : decode_any W_5ec24 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec28 : bv 32 := 0x00c5863b.
Lemma F_5ec28 : fetch_word Plain.M.loaded_segments (0x5ec28 : word) = Some W_5ec28.
Proof. vm_refl. Qed.
Lemma D_5ec28 : decode_any W_5ec28 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec2c : bv 32 := 0x00c785b3.
Lemma F_5ec2c : fetch_word Plain.M.loaded_segments (0x5ec2c : word) = Some W_5ec2c.
Proof. vm_refl. Qed.
Lemma D_5ec2c : decode_any W_5ec2c = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec30 : bv 32 := 0x0025859b.
Lemma F_5ec30 : fetch_word Plain.M.loaded_segments (0x5ec30 : word) = Some W_5ec30.
Proof. vm_refl. Qed.
Lemma D_5ec30 : decode_any W_5ec30 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec34 : bv 32 := 0x160526af.
Lemma F_5ec34 : fetch_word Plain.M.loaded_segments (0x5ec34 : word) = Some W_5ec34.
Proof. vm_refl. Qed.
Lemma D_5ec34 : decode_any W_5ec34 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec38 : bv 32 := 0x00c69663.
Lemma F_5ec38 : fetch_word Plain.M.loaded_segments (0x5ec38 : word) = Some W_5ec38.
Proof. vm_refl. Qed.
Lemma D_5ec38 : decode_any W_5ec38 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec3c : bv 32 := 0x1eb5272f.
Lemma F_5ec3c : fetch_word Plain.M.loaded_segments (0x5ec3c : word) = Some W_5ec3c.
Proof. vm_refl. Qed.
Lemma D_5ec3c : decode_any W_5ec3c = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec40 : bv 32 := 0xfe071ae3.
Lemma F_5ec40 : fetch_word Plain.M.loaded_segments (0x5ec40 : word) = Some W_5ec40.
Proof. vm_refl. Qed.
Lemma D_5ec40 : decode_any W_5ec40 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec44 : bv 32 := 0x0006859b.
Lemma F_5ec44 : fetch_word Plain.M.loaded_segments (0x5ec44 : word) = Some W_5ec44.
Proof. vm_refl. Qed.
Lemma D_5ec44 : decode_any W_5ec44 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec48 : bv 32 := 0x10c58663.
Lemma F_5ec48 : fetch_word Plain.M.loaded_segments (0x5ec48 : word) = Some W_5ec48.
Proof. vm_refl. Qed.
Lemma D_5ec48 : decode_any W_5ec48 = Some (Branch BC_EQ 11 12 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec4c : bv 32 := 0x01f5d613.
Lemma F_5ec4c : fetch_word Plain.M.loaded_segments (0x5ec4c : word) = Some W_5ec4c.
Proof. vm_refl. Qed.
Lemma D_5ec4c : decode_any W_5ec4c = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec50 : bv 32 := 0x00f67633.
Lemma F_5ec50 : fetch_word Plain.M.loaded_segments (0x5ec50 : word) = Some W_5ec50.
Proof. vm_refl. Qed.
Lemma D_5ec50 : decode_any W_5ec50 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec54 : bv 32 := 0x00c5863b.
Lemma F_5ec54 : fetch_word Plain.M.loaded_segments (0x5ec54 : word) = Some W_5ec54.
Proof. vm_refl. Qed.
Lemma D_5ec54 : decode_any W_5ec54 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec58 : bv 32 := 0x00c785b3.
Lemma F_5ec58 : fetch_word Plain.M.loaded_segments (0x5ec58 : word) = Some W_5ec58.
Proof. vm_refl. Qed.
Lemma D_5ec58 : decode_any W_5ec58 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec5c : bv 32 := 0x0025859b.
Lemma F_5ec5c : fetch_word Plain.M.loaded_segments (0x5ec5c : word) = Some W_5ec5c.
Proof. vm_refl. Qed.
Lemma D_5ec5c : decode_any W_5ec5c = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec60 : bv 32 := 0x160526af.
Lemma F_5ec60 : fetch_word Plain.M.loaded_segments (0x5ec60 : word) = Some W_5ec60.
Proof. vm_refl. Qed.
Lemma D_5ec60 : decode_any W_5ec60 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec64 : bv 32 := 0x00c69663.
Lemma F_5ec64 : fetch_word Plain.M.loaded_segments (0x5ec64 : word) = Some W_5ec64.
Proof. vm_refl. Qed.
Lemma D_5ec64 : decode_any W_5ec64 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec68 : bv 32 := 0x1eb5272f.
Lemma F_5ec68 : fetch_word Plain.M.loaded_segments (0x5ec68 : word) = Some W_5ec68.
Proof. vm_refl. Qed.
Lemma D_5ec68 : decode_any W_5ec68 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec6c : bv 32 := 0xfe071ae3.
Lemma F_5ec6c : fetch_word Plain.M.loaded_segments (0x5ec6c : word) = Some W_5ec6c.
Proof. vm_refl. Qed.
Lemma D_5ec6c : decode_any W_5ec6c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec70 : bv 32 := 0x0006859b.
Lemma F_5ec70 : fetch_word Plain.M.loaded_segments (0x5ec70 : word) = Some W_5ec70.
Proof. vm_refl. Qed.
Lemma D_5ec70 : decode_any W_5ec70 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec74 : bv 32 := 0x0ec58063.
Lemma F_5ec74 : fetch_word Plain.M.loaded_segments (0x5ec74 : word) = Some W_5ec74.
Proof. vm_refl. Qed.
Lemma D_5ec74 : decode_any W_5ec74 = Some (Branch BC_EQ 11 12 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec78 : bv 32 := 0x01f5d613.
Lemma F_5ec78 : fetch_word Plain.M.loaded_segments (0x5ec78 : word) = Some W_5ec78.
Proof. vm_refl. Qed.
Lemma D_5ec78 : decode_any W_5ec78 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec7c : bv 32 := 0x00f67633.
Lemma F_5ec7c : fetch_word Plain.M.loaded_segments (0x5ec7c : word) = Some W_5ec7c.
Proof. vm_refl. Qed.
Lemma D_5ec7c : decode_any W_5ec7c = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec80 : bv 32 := 0x00c5863b.
Lemma F_5ec80 : fetch_word Plain.M.loaded_segments (0x5ec80 : word) = Some W_5ec80.
Proof. vm_refl. Qed.
Lemma D_5ec80 : decode_any W_5ec80 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec84 : bv 32 := 0x00c785b3.
Lemma F_5ec84 : fetch_word Plain.M.loaded_segments (0x5ec84 : word) = Some W_5ec84.
Proof. vm_refl. Qed.
Lemma D_5ec84 : decode_any W_5ec84 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec88 : bv 32 := 0x0025859b.
Lemma F_5ec88 : fetch_word Plain.M.loaded_segments (0x5ec88 : word) = Some W_5ec88.
Proof. vm_refl. Qed.
Lemma D_5ec88 : decode_any W_5ec88 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec8c : bv 32 := 0x160526af.
Lemma F_5ec8c : fetch_word Plain.M.loaded_segments (0x5ec8c : word) = Some W_5ec8c.
Proof. vm_refl. Qed.
Lemma D_5ec8c : decode_any W_5ec8c = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec90 : bv 32 := 0x00c69663.
Lemma F_5ec90 : fetch_word Plain.M.loaded_segments (0x5ec90 : word) = Some W_5ec90.
Proof. vm_refl. Qed.
Lemma D_5ec90 : decode_any W_5ec90 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec94 : bv 32 := 0x1eb5272f.
Lemma F_5ec94 : fetch_word Plain.M.loaded_segments (0x5ec94 : word) = Some W_5ec94.
Proof. vm_refl. Qed.
Lemma D_5ec94 : decode_any W_5ec94 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec98 : bv 32 := 0xfe071ae3.
Lemma F_5ec98 : fetch_word Plain.M.loaded_segments (0x5ec98 : word) = Some W_5ec98.
Proof. vm_refl. Qed.
Lemma D_5ec98 : decode_any W_5ec98 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ec9c : bv 32 := 0x0006859b.
Lemma F_5ec9c : fetch_word Plain.M.loaded_segments (0x5ec9c : word) = Some W_5ec9c.
Proof. vm_refl. Qed.
Lemma D_5ec9c : decode_any W_5ec9c = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eca0 : bv 32 := 0x0ac58a63.
Lemma F_5eca0 : fetch_word Plain.M.loaded_segments (0x5eca0 : word) = Some W_5eca0.
Proof. vm_refl. Qed.
Lemma D_5eca0 : decode_any W_5eca0 = Some (Branch BC_EQ 11 12 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eca4 : bv 32 := 0x01f5d613.
Lemma F_5eca4 : fetch_word Plain.M.loaded_segments (0x5eca4 : word) = Some W_5eca4.
Proof. vm_refl. Qed.
Lemma D_5eca4 : decode_any W_5eca4 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eca8 : bv 32 := 0x00f67633.
Lemma F_5eca8 : fetch_word Plain.M.loaded_segments (0x5eca8 : word) = Some W_5eca8.
Proof. vm_refl. Qed.
Lemma D_5eca8 : decode_any W_5eca8 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecac : bv 32 := 0x00c5863b.
Lemma F_5ecac : fetch_word Plain.M.loaded_segments (0x5ecac : word) = Some W_5ecac.
Proof. vm_refl. Qed.
Lemma D_5ecac : decode_any W_5ecac = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecb0 : bv 32 := 0x00c785b3.
Lemma F_5ecb0 : fetch_word Plain.M.loaded_segments (0x5ecb0 : word) = Some W_5ecb0.
Proof. vm_refl. Qed.
Lemma D_5ecb0 : decode_any W_5ecb0 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecb4 : bv 32 := 0x0025859b.
Lemma F_5ecb4 : fetch_word Plain.M.loaded_segments (0x5ecb4 : word) = Some W_5ecb4.
Proof. vm_refl. Qed.
Lemma D_5ecb4 : decode_any W_5ecb4 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecb8 : bv 32 := 0x160526af.
Lemma F_5ecb8 : fetch_word Plain.M.loaded_segments (0x5ecb8 : word) = Some W_5ecb8.
Proof. vm_refl. Qed.
Lemma D_5ecb8 : decode_any W_5ecb8 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecbc : bv 32 := 0x00c69663.
Lemma F_5ecbc : fetch_word Plain.M.loaded_segments (0x5ecbc : word) = Some W_5ecbc.
Proof. vm_refl. Qed.
Lemma D_5ecbc : decode_any W_5ecbc = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecc0 : bv 32 := 0x1eb5272f.
Lemma F_5ecc0 : fetch_word Plain.M.loaded_segments (0x5ecc0 : word) = Some W_5ecc0.
Proof. vm_refl. Qed.
Lemma D_5ecc0 : decode_any W_5ecc0 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecc4 : bv 32 := 0xfe071ae3.
Lemma F_5ecc4 : fetch_word Plain.M.loaded_segments (0x5ecc4 : word) = Some W_5ecc4.
Proof. vm_refl. Qed.
Lemma D_5ecc4 : decode_any W_5ecc4 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecc8 : bv 32 := 0x0006859b.
Lemma F_5ecc8 : fetch_word Plain.M.loaded_segments (0x5ecc8 : word) = Some W_5ecc8.
Proof. vm_refl. Qed.
Lemma D_5ecc8 : decode_any W_5ecc8 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eccc : bv 32 := 0x08c58463.
Lemma F_5eccc : fetch_word Plain.M.loaded_segments (0x5eccc : word) = Some W_5eccc.
Proof. vm_refl. Qed.
Lemma D_5eccc : decode_any W_5eccc = Some (Branch BC_EQ 11 12 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecd0 : bv 32 := 0x01f5d613.
Lemma F_5ecd0 : fetch_word Plain.M.loaded_segments (0x5ecd0 : word) = Some W_5ecd0.
Proof. vm_refl. Qed.
Lemma D_5ecd0 : decode_any W_5ecd0 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecd4 : bv 32 := 0x00f67633.
Lemma F_5ecd4 : fetch_word Plain.M.loaded_segments (0x5ecd4 : word) = Some W_5ecd4.
Proof. vm_refl. Qed.
Lemma D_5ecd4 : decode_any W_5ecd4 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecd8 : bv 32 := 0x00c5863b.
Lemma F_5ecd8 : fetch_word Plain.M.loaded_segments (0x5ecd8 : word) = Some W_5ecd8.
Proof. vm_refl. Qed.
Lemma D_5ecd8 : decode_any W_5ecd8 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecdc : bv 32 := 0x00c785b3.
Lemma F_5ecdc : fetch_word Plain.M.loaded_segments (0x5ecdc : word) = Some W_5ecdc.
Proof. vm_refl. Qed.
Lemma D_5ecdc : decode_any W_5ecdc = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ece0 : bv 32 := 0x0025859b.
Lemma F_5ece0 : fetch_word Plain.M.loaded_segments (0x5ece0 : word) = Some W_5ece0.
Proof. vm_refl. Qed.
Lemma D_5ece0 : decode_any W_5ece0 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ece4 : bv 32 := 0x160526af.
Lemma F_5ece4 : fetch_word Plain.M.loaded_segments (0x5ece4 : word) = Some W_5ece4.
Proof. vm_refl. Qed.
Lemma D_5ece4 : decode_any W_5ece4 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ece8 : bv 32 := 0x00c69663.
Lemma F_5ece8 : fetch_word Plain.M.loaded_segments (0x5ece8 : word) = Some W_5ece8.
Proof. vm_refl. Qed.
Lemma D_5ece8 : decode_any W_5ece8 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecec : bv 32 := 0x1eb5272f.
Lemma F_5ecec : fetch_word Plain.M.loaded_segments (0x5ecec : word) = Some W_5ecec.
Proof. vm_refl. Qed.
Lemma D_5ecec : decode_any W_5ecec = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecf0 : bv 32 := 0xfe071ae3.
Lemma F_5ecf0 : fetch_word Plain.M.loaded_segments (0x5ecf0 : word) = Some W_5ecf0.
Proof. vm_refl. Qed.
Lemma D_5ecf0 : decode_any W_5ecf0 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecf4 : bv 32 := 0x0006859b.
Lemma F_5ecf4 : fetch_word Plain.M.loaded_segments (0x5ecf4 : word) = Some W_5ecf4.
Proof. vm_refl. Qed.
Lemma D_5ecf4 : decode_any W_5ecf4 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecf8 : bv 32 := 0x04c58e63.
Lemma F_5ecf8 : fetch_word Plain.M.loaded_segments (0x5ecf8 : word) = Some W_5ecf8.
Proof. vm_refl. Qed.
Lemma D_5ecf8 : decode_any W_5ecf8 = Some (Branch BC_EQ 11 12 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ecfc : bv 32 := 0x01f5d613.
Lemma F_5ecfc : fetch_word Plain.M.loaded_segments (0x5ecfc : word) = Some W_5ecfc.
Proof. vm_refl. Qed.
Lemma D_5ecfc : decode_any W_5ecfc = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed00 : bv 32 := 0x00f67633.
Lemma F_5ed00 : fetch_word Plain.M.loaded_segments (0x5ed00 : word) = Some W_5ed00.
Proof. vm_refl. Qed.
Lemma D_5ed00 : decode_any W_5ed00 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed04 : bv 32 := 0x00c5863b.
Lemma F_5ed04 : fetch_word Plain.M.loaded_segments (0x5ed04 : word) = Some W_5ed04.
Proof. vm_refl. Qed.
Lemma D_5ed04 : decode_any W_5ed04 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed08 : bv 32 := 0x00c785b3.
Lemma F_5ed08 : fetch_word Plain.M.loaded_segments (0x5ed08 : word) = Some W_5ed08.
Proof. vm_refl. Qed.
Lemma D_5ed08 : decode_any W_5ed08 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed0c : bv 32 := 0x0025859b.
Lemma F_5ed0c : fetch_word Plain.M.loaded_segments (0x5ed0c : word) = Some W_5ed0c.
Proof. vm_refl. Qed.
Lemma D_5ed0c : decode_any W_5ed0c = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed10 : bv 32 := 0x160526af.
Lemma F_5ed10 : fetch_word Plain.M.loaded_segments (0x5ed10 : word) = Some W_5ed10.
Proof. vm_refl. Qed.
Lemma D_5ed10 : decode_any W_5ed10 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed14 : bv 32 := 0x00c69663.
Lemma F_5ed14 : fetch_word Plain.M.loaded_segments (0x5ed14 : word) = Some W_5ed14.
Proof. vm_refl. Qed.
Lemma D_5ed14 : decode_any W_5ed14 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed18 : bv 32 := 0x1eb5272f.
Lemma F_5ed18 : fetch_word Plain.M.loaded_segments (0x5ed18 : word) = Some W_5ed18.
Proof. vm_refl. Qed.
Lemma D_5ed18 : decode_any W_5ed18 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed1c : bv 32 := 0xfe071ae3.
Lemma F_5ed1c : fetch_word Plain.M.loaded_segments (0x5ed1c : word) = Some W_5ed1c.
Proof. vm_refl. Qed.
Lemma D_5ed1c : decode_any W_5ed1c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed20 : bv 32 := 0x0006859b.
Lemma F_5ed20 : fetch_word Plain.M.loaded_segments (0x5ed20 : word) = Some W_5ed20.
Proof. vm_refl. Qed.
Lemma D_5ed20 : decode_any W_5ed20 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed24 : bv 32 := 0x02c58863.
Lemma F_5ed24 : fetch_word Plain.M.loaded_segments (0x5ed24 : word) = Some W_5ed24.
Proof. vm_refl. Qed.
Lemma D_5ed24 : decode_any W_5ed24 = Some (Branch BC_EQ 11 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed28 : bv 32 := 0x01f5d613.
Lemma F_5ed28 : fetch_word Plain.M.loaded_segments (0x5ed28 : word) = Some W_5ed28.
Proof. vm_refl. Qed.
Lemma D_5ed28 : decode_any W_5ed28 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed2c : bv 32 := 0x00f67633.
Lemma F_5ed2c : fetch_word Plain.M.loaded_segments (0x5ed2c : word) = Some W_5ed2c.
Proof. vm_refl. Qed.
Lemma D_5ed2c : decode_any W_5ed2c = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed30 : bv 32 := 0x00c585bb.
Lemma F_5ed30 : fetch_word Plain.M.loaded_segments (0x5ed30 : word) = Some W_5ed30.
Proof. vm_refl. Qed.
Lemma D_5ed30 : decode_any W_5ed30 = Some (Op32 ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed34 : bv 32 := 0x00b78633.
Lemma F_5ed34 : fetch_word Plain.M.loaded_segments (0x5ed34 : word) = Some W_5ed34.
Proof. vm_refl. Qed.
Lemma D_5ed34 : decode_any W_5ed34 = Some (Op ALU_ADD 12 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed38 : bv 32 := 0x0026061b.
Lemma F_5ed38 : fetch_word Plain.M.loaded_segments (0x5ed38 : word) = Some W_5ed38.
Proof. vm_refl. Qed.
Lemma D_5ed38 : decode_any W_5ed38 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed3c : bv 32 := 0x160526af.
Lemma F_5ed3c : fetch_word Plain.M.loaded_segments (0x5ed3c : word) = Some W_5ed3c.
Proof. vm_refl. Qed.
Lemma D_5ed3c : decode_any W_5ed3c = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed40 : bv 32 := 0x00b69663.
Lemma F_5ed40 : fetch_word Plain.M.loaded_segments (0x5ed40 : word) = Some W_5ed40.
Proof. vm_refl. Qed.
Lemma D_5ed40 : decode_any W_5ed40 = Some (Branch BC_NE 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed44 : bv 32 := 0x1ec5272f.
Lemma F_5ed44 : fetch_word Plain.M.loaded_segments (0x5ed44 : word) = Some W_5ed44.
Proof. vm_refl. Qed.
Lemma D_5ed44 : decode_any W_5ed44 = Some (Sc AW true true 14 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed48 : bv 32 := 0xfe071ae3.
Lemma F_5ed48 : fetch_word Plain.M.loaded_segments (0x5ed48 : word) = Some W_5ed48.
Proof. vm_refl. Qed.
Lemma D_5ed48 : decode_any W_5ed48 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed4c : bv 32 := 0x0006869b.
Lemma F_5ed4c : fetch_word Plain.M.loaded_segments (0x5ed4c : word) = Some W_5ed4c.
Proof. vm_refl. Qed.
Lemma D_5ed4c : decode_any W_5ed4c = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed50 : bv 32 := 0x00b69463.
Lemma F_5ed50 : fetch_word Plain.M.loaded_segments (0x5ed50 : word) = Some W_5ed50.
Proof. vm_refl. Qed.
Lemma D_5ed50 : decode_any W_5ed50 = Some (Branch BC_NE 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed54 : bv 32 := 0x00008067.
Lemma F_5ed54 : fetch_word Plain.M.loaded_segments (0x5ed54 : word) = Some W_5ed54.
Proof. vm_refl. Qed.
Lemma D_5ed54 : decode_any W_5ed54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed58 : bv 32 := 0x00052583.
Lemma F_5ed58 : fetch_word Plain.M.loaded_segments (0x5ed58 : word) = Some W_5ed58.
Proof. vm_refl. Qed.
Lemma D_5ed58 : decode_any W_5ed58 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed5c : bv 32 := 0x0015881b.
Lemma F_5ed5c : fetch_word Plain.M.loaded_segments (0x5ed5c : word) = Some W_5ed5c.
Proof. vm_refl. Qed.
Lemma D_5ed5c : decode_any W_5ed5c = Some (OpImm32 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed60 : bv 32 := 0x1605262f.
Lemma F_5ed60 : fetch_word Plain.M.loaded_segments (0x5ed60 : word) = Some W_5ed60.
Proof. vm_refl. Qed.
Lemma D_5ed60 : decode_any W_5ed60 = Some (Lr AW true true 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed64 : bv 32 := 0x00b61663.
Lemma F_5ed64 : fetch_word Plain.M.loaded_segments (0x5ed64 : word) = Some W_5ed64.
Proof. vm_refl. Qed.
Lemma D_5ed64 : decode_any W_5ed64 = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed68 : bv 32 := 0x1f0526af.
Lemma F_5ed68 : fetch_word Plain.M.loaded_segments (0x5ed68 : word) = Some W_5ed68.
Proof. vm_refl. Qed.
Lemma D_5ed68 : decode_any W_5ed68 = Some (Sc AW true true 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed6c : bv 32 := 0xfe069ae3.
Lemma F_5ed6c : fetch_word Plain.M.loaded_segments (0x5ed6c : word) = Some W_5ed6c.
Proof. vm_refl. Qed.
Lemma D_5ed6c : decode_any W_5ed6c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed70 : bv 32 := 0x0006061b.
Lemma F_5ed70 : fetch_word Plain.M.loaded_segments (0x5ed70 : word) = Some W_5ed70.
Proof. vm_refl. Qed.
Lemma D_5ed70 : decode_any W_5ed70 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed74 : bv 32 := 0xfeb612e3.
Lemma F_5ed74 : fetch_word Plain.M.loaded_segments (0x5ed74 : word) = Some W_5ed74.
Proof. vm_refl. Qed.
Lemma D_5ed74 : decode_any W_5ed74 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed78 : bv 32 := 0xfda00293.
Lemma F_5ed78 : fetch_word Plain.M.loaded_segments (0x5ed78 : word) = Some W_5ed78.
Proof. vm_refl. Qed.
Lemma D_5ed78 : decode_any W_5ed78 = Some (OpImm ALU_ADD 5 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed7c : bv 32 := 0x80000337.
Lemma F_5ed7c : fetch_word Plain.M.loaded_segments (0x5ed7c : word) = Some W_5ed7c.
Proof. vm_refl. Qed.
Lemma D_5ed7c : decode_any W_5ed7c = Some (Lui 6 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed80 : bv 32 := 0x02c0006f.
Lemma F_5ed80 : fetch_word Plain.M.loaded_segments (0x5ed80 : word) = Some W_5ed80.
Proof. vm_refl. Qed.
Lemma D_5ed80 : decode_any W_5ed80 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed84 : bv 32 := 0x00f8083b.
Lemma F_5ed84 : fetch_word Plain.M.loaded_segments (0x5ed84 : word) = Some W_5ed84.
Proof. vm_refl. Qed.
Lemma D_5ed84 : decode_any W_5ed84 = Some (Op32 ALU_ADD 16 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed88 : bv 32 := 0x00070513.
Lemma F_5ed88 : fetch_word Plain.M.loaded_segments (0x5ed88 : word) = Some W_5ed88.
Proof. vm_refl. Qed.
Lemma D_5ed88 : decode_any W_5ed88 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed8c : bv 32 := 0x006865b3.
Lemma F_5ed8c : fetch_word Plain.M.loaded_segments (0x5ed8c : word) = Some W_5ed8c.
Proof. vm_refl. Qed.
Lemma D_5ed8c : decode_any W_5ed8c = Some (Op ALU_OR 11 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed90 : bv 32 := 0x0008061b.
Lemma F_5ed90 : fetch_word Plain.M.loaded_segments (0x5ed90 : word) = Some W_5ed90.
Proof. vm_refl. Qed.
Lemma D_5ed90 : decode_any W_5ed90 = Some (OpImm32 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed94 : bv 32 := 0x1605282f.
Lemma F_5ed94 : fetch_word Plain.M.loaded_segments (0x5ed94 : word) = Some W_5ed94.
Proof. vm_refl. Qed.
Lemma D_5ed94 : decode_any W_5ed94 = Some (Lr AW true true 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed98 : bv 32 := 0x00c81663.
Lemma F_5ed98 : fetch_word Plain.M.loaded_segments (0x5ed98 : word) = Some W_5ed98.
Proof. vm_refl. Qed.
Lemma D_5ed98 : decode_any W_5ed98 = Some (Branch BC_NE 16 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ed9c : bv 32 := 0x1eb526af.
Lemma F_5ed9c : fetch_word Plain.M.loaded_segments (0x5ed9c : word) = Some W_5ed9c.
Proof. vm_refl. Qed.
Lemma D_5ed9c : decode_any W_5ed9c = Some (Sc AW true true 13 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eda0 : bv 32 := 0xfe069ae3.
Lemma F_5eda0 : fetch_word Plain.M.loaded_segments (0x5eda0 : word) = Some W_5eda0.
Proof. vm_refl. Qed.
Lemma D_5eda0 : decode_any W_5eda0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eda4 : bv 32 := 0x0008059b.
Lemma F_5eda4 : fetch_word Plain.M.loaded_segments (0x5eda4 : word) = Some W_5eda4.
Proof. vm_refl. Qed.
Lemma D_5eda4 : decode_any W_5eda4 = Some (OpImm32 11 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eda8 : bv 32 := 0xfac586e3.
Lemma F_5eda8 : fetch_word Plain.M.loaded_segments (0x5eda8 : word) = Some W_5eda8.
Proof. vm_refl. Qed.
Lemma D_5eda8 : decode_any W_5eda8 = Some (Branch BC_EQ 11 12 8108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edac : bv 32 := 0x0008061b.
Lemma F_5edac : fetch_word Plain.M.loaded_segments (0x5edac : word) = Some W_5edac.
Proof. vm_refl. Qed.
Lemma D_5edac : decode_any W_5edac = Some (OpImm32 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edb0 : bv 32 := 0xfc065ee3.
Lemma F_5edb0 : fetch_word Plain.M.loaded_segments (0x5edb0 : word) = Some W_5edb0.
Proof. vm_refl. Qed.
Lemma D_5edb0 : decode_any W_5edb0 = Some (Branch BC_GE 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edb4 : bv 32 := 0x06200893.
Lemma F_5edb4 : fetch_word Plain.M.loaded_segments (0x5edb4 : word) = Some W_5edb4.
Proof. vm_refl. Qed.
Lemma D_5edb4 : decode_any W_5edb4 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edb8 : bv 32 := 0x08000593.
Lemma F_5edb8 : fetch_word Plain.M.loaded_segments (0x5edb8 : word) = Some W_5edb8.
Proof. vm_refl. Qed.
Lemma D_5edb8 : decode_any W_5edb8 = Some (OpImm ALU_ADD 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edbc : bv 32 := 0x00050713.
Lemma F_5edbc : fetch_word Plain.M.loaded_segments (0x5edbc : word) = Some W_5edbc.
Proof. vm_refl. Qed.
Lemma D_5edbc : decode_any W_5edbc = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edc0 : bv 32 := 0x00000693.
Lemma F_5edc0 : fetch_word Plain.M.loaded_segments (0x5edc0 : word) = Some W_5edc0.
Proof. vm_refl. Qed.
Lemma D_5edc0 : decode_any W_5edc0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edc4 : bv 32 := 0x00000073.
Lemma F_5edc4 : fetch_word Plain.M.loaded_segments (0x5edc4 : word) = Some W_5edc4.
Proof. vm_refl. Qed.
Lemma D_5edc4 : decode_any W_5edc4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_5edc4 : is_ecall W_5edc4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_5edc8 : bv 32 := 0xfa551ee3.
Lemma F_5edc8 : fetch_word Plain.M.loaded_segments (0x5edc8 : word) = Some W_5edc8.
Proof. vm_refl. Qed.
Lemma D_5edc8 : decode_any W_5edc8 = Some (Branch BC_NE 10 5 8124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edcc : bv 32 := 0x06200893.
Lemma F_5edcc : fetch_word Plain.M.loaded_segments (0x5edcc : word) = Some W_5edcc.
Proof. vm_refl. Qed.
Lemma D_5edcc : decode_any W_5edcc = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edd0 : bv 32 := 0x00070513.
Lemma F_5edd0 : fetch_word Plain.M.loaded_segments (0x5edd0 : word) = Some W_5edd0.
Proof. vm_refl. Qed.
Lemma D_5edd0 : decode_any W_5edd0 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edd4 : bv 32 := 0x00000593.
Lemma F_5edd4 : fetch_word Plain.M.loaded_segments (0x5edd4 : word) = Some W_5edd4.
Proof. vm_refl. Qed.
Lemma D_5edd4 : decode_any W_5edd4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edd8 : bv 32 := 0x00000693.
Lemma F_5edd8 : fetch_word Plain.M.loaded_segments (0x5edd8 : word) = Some W_5edd8.
Proof. vm_refl. Qed.
Lemma D_5edd8 : decode_any W_5edd8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5eddc : bv 32 := 0x00000073.
Lemma F_5eddc : fetch_word Plain.M.loaded_segments (0x5eddc : word) = Some W_5eddc.
Proof. vm_refl. Qed.
Lemma D_5eddc : decode_any W_5eddc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_5eddc : is_ecall W_5eddc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_5ede0 : bv 32 := 0xfa5ff06f.
Lemma F_5ede0 : fetch_word Plain.M.loaded_segments (0x5ede0 : word) = Some W_5ede0.
Proof. vm_refl. Qed.
Lemma D_5ede0 : decode_any W_5ede0 = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ede4 : bv 32 := 0x00052583.
Lemma F_5ede4 : fetch_word Plain.M.loaded_segments (0x5ede4 : word) = Some W_5ede4.
Proof. vm_refl. Qed.
Lemma D_5ede4 : decode_any W_5ede4 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ede8 : bv 32 := 0x0005c463.
Lemma F_5ede8 : fetch_word Plain.M.loaded_segments (0x5ede8 : word) = Some W_5ede8.
Proof. vm_refl. Qed.
Lemma D_5ede8 : decode_any W_5ede8 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edec : bv 32 := 0x00008067.
Lemma F_5edec : fetch_word Plain.M.loaded_segments (0x5edec : word) = Some W_5edec.
Proof. vm_refl. Qed.
Lemma D_5edec : decode_any W_5edec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edf0 : bv 32 := 0x80000637.
Lemma F_5edf0 : fetch_word Plain.M.loaded_segments (0x5edf0 : word) = Some W_5edf0.
Proof. vm_refl. Qed.
Lemma D_5edf0 : decode_any W_5edf0 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edf4 : bv 32 := 0xfff60613.
Lemma F_5edf4 : fetch_word Plain.M.loaded_segments (0x5edf4 : word) = Some W_5edf4.
Proof. vm_refl. Qed.
Lemma D_5edf4 : decode_any W_5edf4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edf8 : bv 32 := 0x00052583.
Lemma F_5edf8 : fetch_word Plain.M.loaded_segments (0x5edf8 : word) = Some W_5edf8.
Proof. vm_refl. Qed.
Lemma D_5edf8 : decode_any W_5edf8 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5edfc : bv 32 := 0x00c586bb.
Lemma F_5edfc : fetch_word Plain.M.loaded_segments (0x5edfc : word) = Some W_5edfc.
Proof. vm_refl. Qed.
Lemma D_5edfc : decode_any W_5edfc = Some (Op32 ALU_ADD 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee00 : bv 32 := 0x1605272f.
Lemma F_5ee00 : fetch_word Plain.M.loaded_segments (0x5ee00 : word) = Some W_5ee00.
Proof. vm_refl. Qed.
Lemma D_5ee00 : decode_any W_5ee00 = Some (Lr AW true true 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee04 : bv 32 := 0x00b71663.
Lemma F_5ee04 : fetch_word Plain.M.loaded_segments (0x5ee04 : word) = Some W_5ee04.
Proof. vm_refl. Qed.
Lemma D_5ee04 : decode_any W_5ee04 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee08 : bv 32 := 0x1ed527af.
Lemma F_5ee08 : fetch_word Plain.M.loaded_segments (0x5ee08 : word) = Some W_5ee08.
Proof. vm_refl. Qed.
Lemma D_5ee08 : decode_any W_5ee08 = Some (Sc AW true true 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee0c : bv 32 := 0xfe079ae3.
Lemma F_5ee0c : fetch_word Plain.M.loaded_segments (0x5ee0c : word) = Some W_5ee0c.
Proof. vm_refl. Qed.
Lemma D_5ee0c : decode_any W_5ee0c = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee10 : bv 32 := 0x0007071b.
Lemma F_5ee10 : fetch_word Plain.M.loaded_segments (0x5ee10 : word) = Some W_5ee10.
Proof. vm_refl. Qed.
Lemma D_5ee10 : decode_any W_5ee10 = Some (OpImm32 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee14 : bv 32 := 0xfeb712e3.
Lemma F_5ee14 : fetch_word Plain.M.loaded_segments (0x5ee14 : word) = Some W_5ee14.
Proof. vm_refl. Qed.
Lemma D_5ee14 : decode_any W_5ee14 = Some (Branch BC_NE 14 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee18 : bv 32 := 0x80000637.
Lemma F_5ee18 : fetch_word Plain.M.loaded_segments (0x5ee18 : word) = Some W_5ee18.
Proof. vm_refl. Qed.
Lemma D_5ee18 : decode_any W_5ee18 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee1c : bv 32 := 0x0016061b.
Lemma F_5ee1c : fetch_word Plain.M.loaded_segments (0x5ee1c : word) = Some W_5ee1c.
Proof. vm_refl. Qed.
Lemma D_5ee1c : decode_any W_5ee1c = Some (OpImm32 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee20 : bv 32 := 0xfcc586e3.
Lemma F_5ee20 : fetch_word Plain.M.loaded_segments (0x5ee20 : word) = Some W_5ee20.
Proof. vm_refl. Qed.
Lemma D_5ee20 : decode_any W_5ee20 = Some (Branch BC_EQ 11 12 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee24 : bv 32 := 0x06200893.
Lemma F_5ee24 : fetch_word Plain.M.loaded_segments (0x5ee24 : word) = Some W_5ee24.
Proof. vm_refl. Qed.
Lemma D_5ee24 : decode_any W_5ee24 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee28 : bv 32 := 0x08100593.
Lemma F_5ee28 : fetch_word Plain.M.loaded_segments (0x5ee28 : word) = Some W_5ee28.
Proof. vm_refl. Qed.
Lemma D_5ee28 : decode_any W_5ee28 = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee2c : bv 32 := 0x00100613.
Lemma F_5ee2c : fetch_word Plain.M.loaded_segments (0x5ee2c : word) = Some W_5ee2c.
Proof. vm_refl. Qed.
Lemma D_5ee2c : decode_any W_5ee2c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee30 : bv 32 := 0xfda00713.
Lemma F_5ee30 : fetch_word Plain.M.loaded_segments (0x5ee30 : word) = Some W_5ee30.
Proof. vm_refl. Qed.
Lemma D_5ee30 : decode_any W_5ee30 = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee34 : bv 32 := 0x00050693.
Lemma F_5ee34 : fetch_word Plain.M.loaded_segments (0x5ee34 : word) = Some W_5ee34.
Proof. vm_refl. Qed.
Lemma D_5ee34 : decode_any W_5ee34 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee38 : bv 32 := 0x00000073.
Lemma F_5ee38 : fetch_word Plain.M.loaded_segments (0x5ee38 : word) = Some W_5ee38.
Proof. vm_refl. Qed.
Lemma D_5ee38 : decode_any W_5ee38 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_5ee38 : is_ecall W_5ee38 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_5ee3c : bv 32 := 0xfae518e3.
Lemma F_5ee3c : fetch_word Plain.M.loaded_segments (0x5ee3c : word) = Some W_5ee3c.
Proof. vm_refl. Qed.
Lemma D_5ee3c : decode_any W_5ee3c = Some (Branch BC_NE 10 14 8112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee40 : bv 32 := 0x06200893.
Lemma F_5ee40 : fetch_word Plain.M.loaded_segments (0x5ee40 : word) = Some W_5ee40.
Proof. vm_refl. Qed.
Lemma D_5ee40 : decode_any W_5ee40 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee44 : bv 32 := 0x00100593.
Lemma F_5ee44 : fetch_word Plain.M.loaded_segments (0x5ee44 : word) = Some W_5ee44.
Proof. vm_refl. Qed.
Lemma D_5ee44 : decode_any W_5ee44 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee48 : bv 32 := 0x00100613.
Lemma F_5ee48 : fetch_word Plain.M.loaded_segments (0x5ee48 : word) = Some W_5ee48.
Proof. vm_refl. Qed.
Lemma D_5ee48 : decode_any W_5ee48 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee4c : bv 32 := 0x00068513.
Lemma F_5ee4c : fetch_word Plain.M.loaded_segments (0x5ee4c : word) = Some W_5ee4c.
Proof. vm_refl. Qed.
Lemma D_5ee4c : decode_any W_5ee4c = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee50 : bv 32 := 0x00000073.
Lemma F_5ee50 : fetch_word Plain.M.loaded_segments (0x5ee50 : word) = Some W_5ee50.
Proof. vm_refl. Qed.
Lemma D_5ee50 : decode_any W_5ee50 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_5ee50 : is_ecall W_5ee50 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_5ee54 : bv 32 := 0x00008067.
Lemma F_5ee54 : fetch_word Plain.M.loaded_segments (0x5ee54 : word) = Some W_5ee54.
Proof. vm_refl. Qed.
Lemma D_5ee54 : decode_any W_5ee54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee58 : bv 32 := 0x00050893.
Lemma F_5ee58 : fetch_word Plain.M.loaded_segments (0x5ee58 : word) = Some W_5ee58.
Proof. vm_refl. Qed.
Lemma D_5ee58 : decode_any W_5ee58 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee5c : bv 32 := 0x00058513.
Lemma F_5ee5c : fetch_word Plain.M.loaded_segments (0x5ee5c : word) = Some W_5ee5c.
Proof. vm_refl. Qed.
Lemma D_5ee5c : decode_any W_5ee5c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee60 : bv 32 := 0x00060593.
Lemma F_5ee60 : fetch_word Plain.M.loaded_segments (0x5ee60 : word) = Some W_5ee60.
Proof. vm_refl. Qed.
Lemma D_5ee60 : decode_any W_5ee60 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee64 : bv 32 := 0x00068613.
Lemma F_5ee64 : fetch_word Plain.M.loaded_segments (0x5ee64 : word) = Some W_5ee64.
Proof. vm_refl. Qed.
Lemma D_5ee64 : decode_any W_5ee64 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee68 : bv 32 := 0x00070693.
Lemma F_5ee68 : fetch_word Plain.M.loaded_segments (0x5ee68 : word) = Some W_5ee68.
Proof. vm_refl. Qed.
Lemma D_5ee68 : decode_any W_5ee68 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee6c : bv 32 := 0x00078713.
Lemma F_5ee6c : fetch_word Plain.M.loaded_segments (0x5ee6c : word) = Some W_5ee6c.
Proof. vm_refl. Qed.
Lemma D_5ee6c : decode_any W_5ee6c = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee70 : bv 32 := 0x00080793.
Lemma F_5ee70 : fetch_word Plain.M.loaded_segments (0x5ee70 : word) = Some W_5ee70.
Proof. vm_refl. Qed.
Lemma D_5ee70 : decode_any W_5ee70 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee74 : bv 32 := 0x00000073.
Lemma F_5ee74 : fetch_word Plain.M.loaded_segments (0x5ee74 : word) = Some W_5ee74.
Proof. vm_refl. Qed.
Lemma D_5ee74 : decode_any W_5ee74 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_5ee74 : is_ecall W_5ee74 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_5ee78 : bv 32 := 0x00008067.
Lemma F_5ee78 : fetch_word Plain.M.loaded_segments (0x5ee78 : word) = Some W_5ee78.
Proof. vm_refl. Qed.
Lemma D_5ee78 : decode_any W_5ee78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ee7c : bv 32 := 0xfddff06f.
Lemma F_5ee7c : fetch_word Plain.M.loaded_segments (0x5ee7c : word) = Some W_5ee7c.
Proof. vm_refl. Qed.
Lemma D_5ee7c : decode_any W_5ee7c = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.
