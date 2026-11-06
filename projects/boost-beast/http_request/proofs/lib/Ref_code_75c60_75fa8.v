(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_75c60 : bv 32 := 0x0003d597.
Lemma F_75c60 : fetch_word Plain.M.loaded_segments (0x75c60 : word) = Some W_75c60.
Proof. vm_refl. Qed.
Lemma D_75c60 : decode_any W_75c60 = Some (Auipc 11 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c64 : bv 32 := 0xc8358683.
Lemma F_75c64 : fetch_word Plain.M.loaded_segments (0x75c64 : word) = Some W_75c64.
Proof. vm_refl. Qed.
Lemma D_75c64 : decode_any W_75c64 = Some (Load SZ1 true 13 11 3203, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c68 : bv 32 := 0x1e068863.
Lemma F_75c68 : fetch_word Plain.M.loaded_segments (0x75c68 : word) = Some W_75c68.
Proof. vm_refl. Qed.
Lemma D_75c68 : decode_any W_75c68 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c6c : bv 32 := 0x00000613.
Lemma F_75c6c : fetch_word Plain.M.loaded_segments (0x75c6c : word) = Some W_75c6c.
Proof. vm_refl. Qed.
Lemma D_75c6c : decode_any W_75c6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c70 : bv 32 := 0x80000737.
Lemma F_75c70 : fetch_word Plain.M.loaded_segments (0x75c70 : word) = Some W_75c70.
Proof. vm_refl. Qed.
Lemma D_75c70 : decode_any W_75c70 = Some (Lui 14 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c74 : bv 32 := 0x0017071b.
Lemma F_75c74 : fetch_word Plain.M.loaded_segments (0x75c74 : word) = Some W_75c74.
Proof. vm_refl. Qed.
Lemma D_75c74 : decode_any W_75c74 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c78 : bv 32 := 0x160527af.
Lemma F_75c78 : fetch_word Plain.M.loaded_segments (0x75c78 : word) = Some W_75c78.
Proof. vm_refl. Qed.
Lemma D_75c78 : decode_any W_75c78 = Some (Lr AW true true 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c7c : bv 32 := 0x00c79663.
Lemma F_75c7c : fetch_word Plain.M.loaded_segments (0x75c7c : word) = Some W_75c7c.
Proof. vm_refl. Qed.
Lemma D_75c7c : decode_any W_75c7c = Some (Branch BC_NE 15 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c80 : bv 32 := 0x1ee5282f.
Lemma F_75c80 : fetch_word Plain.M.loaded_segments (0x75c80 : word) = Some W_75c80.
Proof. vm_refl. Qed.
Lemma D_75c80 : decode_any W_75c80 = Some (Sc AW true true 16 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c84 : bv 32 := 0xfe081ae3.
Lemma F_75c84 : fetch_word Plain.M.loaded_segments (0x75c84 : word) = Some W_75c84.
Proof. vm_refl. Qed.
Lemma D_75c84 : decode_any W_75c84 = Some (Branch BC_NE 16 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c88 : bv 32 := 0x0007861b.
Lemma F_75c88 : fetch_word Plain.M.loaded_segments (0x75c88 : word) = Some W_75c88.
Proof. vm_refl. Qed.
Lemma D_75c88 : decode_any W_75c88 = Some (OpImm32 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c8c : bv 32 := 0x0006d463.
Lemma F_75c8c : fetch_word Plain.M.loaded_segments (0x75c8c : word) = Some W_75c8c.
Proof. vm_refl. Qed.
Lemma D_75c8c : decode_any W_75c8c = Some (Branch BC_GE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c90 : bv 32 := 0xc80581a3.
Lemma F_75c90 : fetch_word Plain.M.loaded_segments (0x75c90 : word) = Some W_75c90.
Proof. vm_refl. Qed.
Lemma D_75c90 : decode_any W_75c90 = Some (Store SZ1 11 0 3203, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c94 : bv 32 := 0x1c060263.
Lemma F_75c94 : fetch_word Plain.M.loaded_segments (0x75c94 : word) = Some W_75c94.
Proof. vm_refl. Qed.
Lemma D_75c94 : decode_any W_75c94 = Some (Branch BC_EQ 12 0 452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c98 : bv 32 := 0x800007b7.
Lemma F_75c98 : fetch_word Plain.M.loaded_segments (0x75c98 : word) = Some W_75c98.
Proof. vm_refl. Qed.
Lemma D_75c98 : decode_any W_75c98 = Some (Lui 15 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75c9c : bv 32 := 0x00261593.
Lemma F_75c9c : fetch_word Plain.M.loaded_segments (0x75c9c : word) = Some W_75c9c.
Proof. vm_refl. Qed.
Lemma D_75c9c : decode_any W_75c9c = Some (ShiftImm ALU_SLL 11 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ca0 : bv 32 := 0xfff78793.
Lemma F_75ca0 : fetch_word Plain.M.loaded_segments (0x75ca0 : word) = Some W_75ca0.
Proof. vm_refl. Qed.
Lemma D_75ca0 : decode_any W_75ca0 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ca4 : bv 32 := 0x0215d593.
Lemma F_75ca4 : fetch_word Plain.M.loaded_segments (0x75ca4 : word) = Some W_75ca4.
Proof. vm_refl. Qed.
Lemma D_75ca4 : decode_any W_75ca4 = Some (ShiftImm ALU_SRL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ca8 : bv 32 := 0x00b6063b.
Lemma F_75ca8 : fetch_word Plain.M.loaded_segments (0x75ca8 : word) = Some W_75ca8.
Proof. vm_refl. Qed.
Lemma D_75ca8 : decode_any W_75ca8 = Some (Op32 ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cac : bv 32 := 0x00f605b3.
Lemma F_75cac : fetch_word Plain.M.loaded_segments (0x75cac : word) = Some W_75cac.
Proof. vm_refl. Qed.
Lemma D_75cac : decode_any W_75cac = Some (Op ALU_ADD 11 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cb0 : bv 32 := 0x0025859b.
Lemma F_75cb0 : fetch_word Plain.M.loaded_segments (0x75cb0 : word) = Some W_75cb0.
Proof. vm_refl. Qed.
Lemma D_75cb0 : decode_any W_75cb0 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cb4 : bv 32 := 0x160526af.
Lemma F_75cb4 : fetch_word Plain.M.loaded_segments (0x75cb4 : word) = Some W_75cb4.
Proof. vm_refl. Qed.
Lemma D_75cb4 : decode_any W_75cb4 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cb8 : bv 32 := 0x00c69663.
Lemma F_75cb8 : fetch_word Plain.M.loaded_segments (0x75cb8 : word) = Some W_75cb8.
Proof. vm_refl. Qed.
Lemma D_75cb8 : decode_any W_75cb8 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cbc : bv 32 := 0x1eb5272f.
Lemma F_75cbc : fetch_word Plain.M.loaded_segments (0x75cbc : word) = Some W_75cbc.
Proof. vm_refl. Qed.
Lemma D_75cbc : decode_any W_75cbc = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cc0 : bv 32 := 0xfe071ae3.
Lemma F_75cc0 : fetch_word Plain.M.loaded_segments (0x75cc0 : word) = Some W_75cc0.
Proof. vm_refl. Qed.
Lemma D_75cc0 : decode_any W_75cc0 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cc4 : bv 32 := 0x0006859b.
Lemma F_75cc4 : fetch_word Plain.M.loaded_segments (0x75cc4 : word) = Some W_75cc4.
Proof. vm_refl. Qed.
Lemma D_75cc4 : decode_any W_75cc4 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cc8 : bv 32 := 0x18c58863.
Lemma F_75cc8 : fetch_word Plain.M.loaded_segments (0x75cc8 : word) = Some W_75cc8.
Proof. vm_refl. Qed.
Lemma D_75cc8 : decode_any W_75cc8 = Some (Branch BC_EQ 11 12 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ccc : bv 32 := 0x01f5d613.
Lemma F_75ccc : fetch_word Plain.M.loaded_segments (0x75ccc : word) = Some W_75ccc.
Proof. vm_refl. Qed.
Lemma D_75ccc : decode_any W_75ccc = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cd0 : bv 32 := 0x00f67633.
Lemma F_75cd0 : fetch_word Plain.M.loaded_segments (0x75cd0 : word) = Some W_75cd0.
Proof. vm_refl. Qed.
Lemma D_75cd0 : decode_any W_75cd0 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cd4 : bv 32 := 0x00c5863b.
Lemma F_75cd4 : fetch_word Plain.M.loaded_segments (0x75cd4 : word) = Some W_75cd4.
Proof. vm_refl. Qed.
Lemma D_75cd4 : decode_any W_75cd4 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cd8 : bv 32 := 0x00c785b3.
Lemma F_75cd8 : fetch_word Plain.M.loaded_segments (0x75cd8 : word) = Some W_75cd8.
Proof. vm_refl. Qed.
Lemma D_75cd8 : decode_any W_75cd8 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cdc : bv 32 := 0x0025859b.
Lemma F_75cdc : fetch_word Plain.M.loaded_segments (0x75cdc : word) = Some W_75cdc.
Proof. vm_refl. Qed.
Lemma D_75cdc : decode_any W_75cdc = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ce0 : bv 32 := 0x160526af.
Lemma F_75ce0 : fetch_word Plain.M.loaded_segments (0x75ce0 : word) = Some W_75ce0.
Proof. vm_refl. Qed.
Lemma D_75ce0 : decode_any W_75ce0 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ce4 : bv 32 := 0x00c69663.
Lemma F_75ce4 : fetch_word Plain.M.loaded_segments (0x75ce4 : word) = Some W_75ce4.
Proof. vm_refl. Qed.
Lemma D_75ce4 : decode_any W_75ce4 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ce8 : bv 32 := 0x1eb5272f.
Lemma F_75ce8 : fetch_word Plain.M.loaded_segments (0x75ce8 : word) = Some W_75ce8.
Proof. vm_refl. Qed.
Lemma D_75ce8 : decode_any W_75ce8 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cec : bv 32 := 0xfe071ae3.
Lemma F_75cec : fetch_word Plain.M.loaded_segments (0x75cec : word) = Some W_75cec.
Proof. vm_refl. Qed.
Lemma D_75cec : decode_any W_75cec = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cf0 : bv 32 := 0x0006859b.
Lemma F_75cf0 : fetch_word Plain.M.loaded_segments (0x75cf0 : word) = Some W_75cf0.
Proof. vm_refl. Qed.
Lemma D_75cf0 : decode_any W_75cf0 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cf4 : bv 32 := 0x16c58263.
Lemma F_75cf4 : fetch_word Plain.M.loaded_segments (0x75cf4 : word) = Some W_75cf4.
Proof. vm_refl. Qed.
Lemma D_75cf4 : decode_any W_75cf4 = Some (Branch BC_EQ 11 12 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cf8 : bv 32 := 0x01f5d613.
Lemma F_75cf8 : fetch_word Plain.M.loaded_segments (0x75cf8 : word) = Some W_75cf8.
Proof. vm_refl. Qed.
Lemma D_75cf8 : decode_any W_75cf8 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75cfc : bv 32 := 0x00f67633.
Lemma F_75cfc : fetch_word Plain.M.loaded_segments (0x75cfc : word) = Some W_75cfc.
Proof. vm_refl. Qed.
Lemma D_75cfc : decode_any W_75cfc = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d00 : bv 32 := 0x00c5863b.
Lemma F_75d00 : fetch_word Plain.M.loaded_segments (0x75d00 : word) = Some W_75d00.
Proof. vm_refl. Qed.
Lemma D_75d00 : decode_any W_75d00 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d04 : bv 32 := 0x00c785b3.
Lemma F_75d04 : fetch_word Plain.M.loaded_segments (0x75d04 : word) = Some W_75d04.
Proof. vm_refl. Qed.
Lemma D_75d04 : decode_any W_75d04 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d08 : bv 32 := 0x0025859b.
Lemma F_75d08 : fetch_word Plain.M.loaded_segments (0x75d08 : word) = Some W_75d08.
Proof. vm_refl. Qed.
Lemma D_75d08 : decode_any W_75d08 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d0c : bv 32 := 0x160526af.
Lemma F_75d0c : fetch_word Plain.M.loaded_segments (0x75d0c : word) = Some W_75d0c.
Proof. vm_refl. Qed.
Lemma D_75d0c : decode_any W_75d0c = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d10 : bv 32 := 0x00c69663.
Lemma F_75d10 : fetch_word Plain.M.loaded_segments (0x75d10 : word) = Some W_75d10.
Proof. vm_refl. Qed.
Lemma D_75d10 : decode_any W_75d10 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d14 : bv 32 := 0x1eb5272f.
Lemma F_75d14 : fetch_word Plain.M.loaded_segments (0x75d14 : word) = Some W_75d14.
Proof. vm_refl. Qed.
Lemma D_75d14 : decode_any W_75d14 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d18 : bv 32 := 0xfe071ae3.
Lemma F_75d18 : fetch_word Plain.M.loaded_segments (0x75d18 : word) = Some W_75d18.
Proof. vm_refl. Qed.
Lemma D_75d18 : decode_any W_75d18 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d1c : bv 32 := 0x0006859b.
Lemma F_75d1c : fetch_word Plain.M.loaded_segments (0x75d1c : word) = Some W_75d1c.
Proof. vm_refl. Qed.
Lemma D_75d1c : decode_any W_75d1c = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d20 : bv 32 := 0x12c58c63.
Lemma F_75d20 : fetch_word Plain.M.loaded_segments (0x75d20 : word) = Some W_75d20.
Proof. vm_refl. Qed.
Lemma D_75d20 : decode_any W_75d20 = Some (Branch BC_EQ 11 12 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d24 : bv 32 := 0x01f5d613.
Lemma F_75d24 : fetch_word Plain.M.loaded_segments (0x75d24 : word) = Some W_75d24.
Proof. vm_refl. Qed.
Lemma D_75d24 : decode_any W_75d24 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d28 : bv 32 := 0x00f67633.
Lemma F_75d28 : fetch_word Plain.M.loaded_segments (0x75d28 : word) = Some W_75d28.
Proof. vm_refl. Qed.
Lemma D_75d28 : decode_any W_75d28 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d2c : bv 32 := 0x00c5863b.
Lemma F_75d2c : fetch_word Plain.M.loaded_segments (0x75d2c : word) = Some W_75d2c.
Proof. vm_refl. Qed.
Lemma D_75d2c : decode_any W_75d2c = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d30 : bv 32 := 0x00c785b3.
Lemma F_75d30 : fetch_word Plain.M.loaded_segments (0x75d30 : word) = Some W_75d30.
Proof. vm_refl. Qed.
Lemma D_75d30 : decode_any W_75d30 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d34 : bv 32 := 0x0025859b.
Lemma F_75d34 : fetch_word Plain.M.loaded_segments (0x75d34 : word) = Some W_75d34.
Proof. vm_refl. Qed.
Lemma D_75d34 : decode_any W_75d34 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d38 : bv 32 := 0x160526af.
Lemma F_75d38 : fetch_word Plain.M.loaded_segments (0x75d38 : word) = Some W_75d38.
Proof. vm_refl. Qed.
Lemma D_75d38 : decode_any W_75d38 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d3c : bv 32 := 0x00c69663.
Lemma F_75d3c : fetch_word Plain.M.loaded_segments (0x75d3c : word) = Some W_75d3c.
Proof. vm_refl. Qed.
Lemma D_75d3c : decode_any W_75d3c = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d40 : bv 32 := 0x1eb5272f.
Lemma F_75d40 : fetch_word Plain.M.loaded_segments (0x75d40 : word) = Some W_75d40.
Proof. vm_refl. Qed.
Lemma D_75d40 : decode_any W_75d40 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d44 : bv 32 := 0xfe071ae3.
Lemma F_75d44 : fetch_word Plain.M.loaded_segments (0x75d44 : word) = Some W_75d44.
Proof. vm_refl. Qed.
Lemma D_75d44 : decode_any W_75d44 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d48 : bv 32 := 0x0006859b.
Lemma F_75d48 : fetch_word Plain.M.loaded_segments (0x75d48 : word) = Some W_75d48.
Proof. vm_refl. Qed.
Lemma D_75d48 : decode_any W_75d48 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d4c : bv 32 := 0x10c58663.
Lemma F_75d4c : fetch_word Plain.M.loaded_segments (0x75d4c : word) = Some W_75d4c.
Proof. vm_refl. Qed.
Lemma D_75d4c : decode_any W_75d4c = Some (Branch BC_EQ 11 12 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d50 : bv 32 := 0x01f5d613.
Lemma F_75d50 : fetch_word Plain.M.loaded_segments (0x75d50 : word) = Some W_75d50.
Proof. vm_refl. Qed.
Lemma D_75d50 : decode_any W_75d50 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d54 : bv 32 := 0x00f67633.
Lemma F_75d54 : fetch_word Plain.M.loaded_segments (0x75d54 : word) = Some W_75d54.
Proof. vm_refl. Qed.
Lemma D_75d54 : decode_any W_75d54 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d58 : bv 32 := 0x00c5863b.
Lemma F_75d58 : fetch_word Plain.M.loaded_segments (0x75d58 : word) = Some W_75d58.
Proof. vm_refl. Qed.
Lemma D_75d58 : decode_any W_75d58 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d5c : bv 32 := 0x00c785b3.
Lemma F_75d5c : fetch_word Plain.M.loaded_segments (0x75d5c : word) = Some W_75d5c.
Proof. vm_refl. Qed.
Lemma D_75d5c : decode_any W_75d5c = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d60 : bv 32 := 0x0025859b.
Lemma F_75d60 : fetch_word Plain.M.loaded_segments (0x75d60 : word) = Some W_75d60.
Proof. vm_refl. Qed.
Lemma D_75d60 : decode_any W_75d60 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d64 : bv 32 := 0x160526af.
Lemma F_75d64 : fetch_word Plain.M.loaded_segments (0x75d64 : word) = Some W_75d64.
Proof. vm_refl. Qed.
Lemma D_75d64 : decode_any W_75d64 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d68 : bv 32 := 0x00c69663.
Lemma F_75d68 : fetch_word Plain.M.loaded_segments (0x75d68 : word) = Some W_75d68.
Proof. vm_refl. Qed.
Lemma D_75d68 : decode_any W_75d68 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d6c : bv 32 := 0x1eb5272f.
Lemma F_75d6c : fetch_word Plain.M.loaded_segments (0x75d6c : word) = Some W_75d6c.
Proof. vm_refl. Qed.
Lemma D_75d6c : decode_any W_75d6c = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d70 : bv 32 := 0xfe071ae3.
Lemma F_75d70 : fetch_word Plain.M.loaded_segments (0x75d70 : word) = Some W_75d70.
Proof. vm_refl. Qed.
Lemma D_75d70 : decode_any W_75d70 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d74 : bv 32 := 0x0006859b.
Lemma F_75d74 : fetch_word Plain.M.loaded_segments (0x75d74 : word) = Some W_75d74.
Proof. vm_refl. Qed.
Lemma D_75d74 : decode_any W_75d74 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d78 : bv 32 := 0x0ec58063.
Lemma F_75d78 : fetch_word Plain.M.loaded_segments (0x75d78 : word) = Some W_75d78.
Proof. vm_refl. Qed.
Lemma D_75d78 : decode_any W_75d78 = Some (Branch BC_EQ 11 12 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d7c : bv 32 := 0x01f5d613.
Lemma F_75d7c : fetch_word Plain.M.loaded_segments (0x75d7c : word) = Some W_75d7c.
Proof. vm_refl. Qed.
Lemma D_75d7c : decode_any W_75d7c = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d80 : bv 32 := 0x00f67633.
Lemma F_75d80 : fetch_word Plain.M.loaded_segments (0x75d80 : word) = Some W_75d80.
Proof. vm_refl. Qed.
Lemma D_75d80 : decode_any W_75d80 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d84 : bv 32 := 0x00c5863b.
Lemma F_75d84 : fetch_word Plain.M.loaded_segments (0x75d84 : word) = Some W_75d84.
Proof. vm_refl. Qed.
Lemma D_75d84 : decode_any W_75d84 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d88 : bv 32 := 0x00c785b3.
Lemma F_75d88 : fetch_word Plain.M.loaded_segments (0x75d88 : word) = Some W_75d88.
Proof. vm_refl. Qed.
Lemma D_75d88 : decode_any W_75d88 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d8c : bv 32 := 0x0025859b.
Lemma F_75d8c : fetch_word Plain.M.loaded_segments (0x75d8c : word) = Some W_75d8c.
Proof. vm_refl. Qed.
Lemma D_75d8c : decode_any W_75d8c = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d90 : bv 32 := 0x160526af.
Lemma F_75d90 : fetch_word Plain.M.loaded_segments (0x75d90 : word) = Some W_75d90.
Proof. vm_refl. Qed.
Lemma D_75d90 : decode_any W_75d90 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d94 : bv 32 := 0x00c69663.
Lemma F_75d94 : fetch_word Plain.M.loaded_segments (0x75d94 : word) = Some W_75d94.
Proof. vm_refl. Qed.
Lemma D_75d94 : decode_any W_75d94 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d98 : bv 32 := 0x1eb5272f.
Lemma F_75d98 : fetch_word Plain.M.loaded_segments (0x75d98 : word) = Some W_75d98.
Proof. vm_refl. Qed.
Lemma D_75d98 : decode_any W_75d98 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d9c : bv 32 := 0xfe071ae3.
Lemma F_75d9c : fetch_word Plain.M.loaded_segments (0x75d9c : word) = Some W_75d9c.
Proof. vm_refl. Qed.
Lemma D_75d9c : decode_any W_75d9c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75da0 : bv 32 := 0x0006859b.
Lemma F_75da0 : fetch_word Plain.M.loaded_segments (0x75da0 : word) = Some W_75da0.
Proof. vm_refl. Qed.
Lemma D_75da0 : decode_any W_75da0 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75da4 : bv 32 := 0x0ac58a63.
Lemma F_75da4 : fetch_word Plain.M.loaded_segments (0x75da4 : word) = Some W_75da4.
Proof. vm_refl. Qed.
Lemma D_75da4 : decode_any W_75da4 = Some (Branch BC_EQ 11 12 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75da8 : bv 32 := 0x01f5d613.
Lemma F_75da8 : fetch_word Plain.M.loaded_segments (0x75da8 : word) = Some W_75da8.
Proof. vm_refl. Qed.
Lemma D_75da8 : decode_any W_75da8 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dac : bv 32 := 0x00f67633.
Lemma F_75dac : fetch_word Plain.M.loaded_segments (0x75dac : word) = Some W_75dac.
Proof. vm_refl. Qed.
Lemma D_75dac : decode_any W_75dac = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75db0 : bv 32 := 0x00c5863b.
Lemma F_75db0 : fetch_word Plain.M.loaded_segments (0x75db0 : word) = Some W_75db0.
Proof. vm_refl. Qed.
Lemma D_75db0 : decode_any W_75db0 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75db4 : bv 32 := 0x00c785b3.
Lemma F_75db4 : fetch_word Plain.M.loaded_segments (0x75db4 : word) = Some W_75db4.
Proof. vm_refl. Qed.
Lemma D_75db4 : decode_any W_75db4 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75db8 : bv 32 := 0x0025859b.
Lemma F_75db8 : fetch_word Plain.M.loaded_segments (0x75db8 : word) = Some W_75db8.
Proof. vm_refl. Qed.
Lemma D_75db8 : decode_any W_75db8 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dbc : bv 32 := 0x160526af.
Lemma F_75dbc : fetch_word Plain.M.loaded_segments (0x75dbc : word) = Some W_75dbc.
Proof. vm_refl. Qed.
Lemma D_75dbc : decode_any W_75dbc = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dc0 : bv 32 := 0x00c69663.
Lemma F_75dc0 : fetch_word Plain.M.loaded_segments (0x75dc0 : word) = Some W_75dc0.
Proof. vm_refl. Qed.
Lemma D_75dc0 : decode_any W_75dc0 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dc4 : bv 32 := 0x1eb5272f.
Lemma F_75dc4 : fetch_word Plain.M.loaded_segments (0x75dc4 : word) = Some W_75dc4.
Proof. vm_refl. Qed.
Lemma D_75dc4 : decode_any W_75dc4 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dc8 : bv 32 := 0xfe071ae3.
Lemma F_75dc8 : fetch_word Plain.M.loaded_segments (0x75dc8 : word) = Some W_75dc8.
Proof. vm_refl. Qed.
Lemma D_75dc8 : decode_any W_75dc8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dcc : bv 32 := 0x0006859b.
Lemma F_75dcc : fetch_word Plain.M.loaded_segments (0x75dcc : word) = Some W_75dcc.
Proof. vm_refl. Qed.
Lemma D_75dcc : decode_any W_75dcc = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dd0 : bv 32 := 0x08c58463.
Lemma F_75dd0 : fetch_word Plain.M.loaded_segments (0x75dd0 : word) = Some W_75dd0.
Proof. vm_refl. Qed.
Lemma D_75dd0 : decode_any W_75dd0 = Some (Branch BC_EQ 11 12 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dd4 : bv 32 := 0x01f5d613.
Lemma F_75dd4 : fetch_word Plain.M.loaded_segments (0x75dd4 : word) = Some W_75dd4.
Proof. vm_refl. Qed.
Lemma D_75dd4 : decode_any W_75dd4 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dd8 : bv 32 := 0x00f67633.
Lemma F_75dd8 : fetch_word Plain.M.loaded_segments (0x75dd8 : word) = Some W_75dd8.
Proof. vm_refl. Qed.
Lemma D_75dd8 : decode_any W_75dd8 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ddc : bv 32 := 0x00c5863b.
Lemma F_75ddc : fetch_word Plain.M.loaded_segments (0x75ddc : word) = Some W_75ddc.
Proof. vm_refl. Qed.
Lemma D_75ddc : decode_any W_75ddc = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75de0 : bv 32 := 0x00c785b3.
Lemma F_75de0 : fetch_word Plain.M.loaded_segments (0x75de0 : word) = Some W_75de0.
Proof. vm_refl. Qed.
Lemma D_75de0 : decode_any W_75de0 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75de4 : bv 32 := 0x0025859b.
Lemma F_75de4 : fetch_word Plain.M.loaded_segments (0x75de4 : word) = Some W_75de4.
Proof. vm_refl. Qed.
Lemma D_75de4 : decode_any W_75de4 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75de8 : bv 32 := 0x160526af.
Lemma F_75de8 : fetch_word Plain.M.loaded_segments (0x75de8 : word) = Some W_75de8.
Proof. vm_refl. Qed.
Lemma D_75de8 : decode_any W_75de8 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dec : bv 32 := 0x00c69663.
Lemma F_75dec : fetch_word Plain.M.loaded_segments (0x75dec : word) = Some W_75dec.
Proof. vm_refl. Qed.
Lemma D_75dec : decode_any W_75dec = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75df0 : bv 32 := 0x1eb5272f.
Lemma F_75df0 : fetch_word Plain.M.loaded_segments (0x75df0 : word) = Some W_75df0.
Proof. vm_refl. Qed.
Lemma D_75df0 : decode_any W_75df0 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75df4 : bv 32 := 0xfe071ae3.
Lemma F_75df4 : fetch_word Plain.M.loaded_segments (0x75df4 : word) = Some W_75df4.
Proof. vm_refl. Qed.
Lemma D_75df4 : decode_any W_75df4 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75df8 : bv 32 := 0x0006859b.
Lemma F_75df8 : fetch_word Plain.M.loaded_segments (0x75df8 : word) = Some W_75df8.
Proof. vm_refl. Qed.
Lemma D_75df8 : decode_any W_75df8 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75dfc : bv 32 := 0x04c58e63.
Lemma F_75dfc : fetch_word Plain.M.loaded_segments (0x75dfc : word) = Some W_75dfc.
Proof. vm_refl. Qed.
Lemma D_75dfc : decode_any W_75dfc = Some (Branch BC_EQ 11 12 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e00 : bv 32 := 0x01f5d613.
Lemma F_75e00 : fetch_word Plain.M.loaded_segments (0x75e00 : word) = Some W_75e00.
Proof. vm_refl. Qed.
Lemma D_75e00 : decode_any W_75e00 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e04 : bv 32 := 0x00f67633.
Lemma F_75e04 : fetch_word Plain.M.loaded_segments (0x75e04 : word) = Some W_75e04.
Proof. vm_refl. Qed.
Lemma D_75e04 : decode_any W_75e04 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e08 : bv 32 := 0x00c5863b.
Lemma F_75e08 : fetch_word Plain.M.loaded_segments (0x75e08 : word) = Some W_75e08.
Proof. vm_refl. Qed.
Lemma D_75e08 : decode_any W_75e08 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e0c : bv 32 := 0x00c785b3.
Lemma F_75e0c : fetch_word Plain.M.loaded_segments (0x75e0c : word) = Some W_75e0c.
Proof. vm_refl. Qed.
Lemma D_75e0c : decode_any W_75e0c = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e10 : bv 32 := 0x0025859b.
Lemma F_75e10 : fetch_word Plain.M.loaded_segments (0x75e10 : word) = Some W_75e10.
Proof. vm_refl. Qed.
Lemma D_75e10 : decode_any W_75e10 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e14 : bv 32 := 0x160526af.
Lemma F_75e14 : fetch_word Plain.M.loaded_segments (0x75e14 : word) = Some W_75e14.
Proof. vm_refl. Qed.
Lemma D_75e14 : decode_any W_75e14 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e18 : bv 32 := 0x00c69663.
Lemma F_75e18 : fetch_word Plain.M.loaded_segments (0x75e18 : word) = Some W_75e18.
Proof. vm_refl. Qed.
Lemma D_75e18 : decode_any W_75e18 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e1c : bv 32 := 0x1eb5272f.
Lemma F_75e1c : fetch_word Plain.M.loaded_segments (0x75e1c : word) = Some W_75e1c.
Proof. vm_refl. Qed.
Lemma D_75e1c : decode_any W_75e1c = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e20 : bv 32 := 0xfe071ae3.
Lemma F_75e20 : fetch_word Plain.M.loaded_segments (0x75e20 : word) = Some W_75e20.
Proof. vm_refl. Qed.
Lemma D_75e20 : decode_any W_75e20 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e24 : bv 32 := 0x0006859b.
Lemma F_75e24 : fetch_word Plain.M.loaded_segments (0x75e24 : word) = Some W_75e24.
Proof. vm_refl. Qed.
Lemma D_75e24 : decode_any W_75e24 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e28 : bv 32 := 0x02c58863.
Lemma F_75e28 : fetch_word Plain.M.loaded_segments (0x75e28 : word) = Some W_75e28.
Proof. vm_refl. Qed.
Lemma D_75e28 : decode_any W_75e28 = Some (Branch BC_EQ 11 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e2c : bv 32 := 0x01f5d613.
Lemma F_75e2c : fetch_word Plain.M.loaded_segments (0x75e2c : word) = Some W_75e2c.
Proof. vm_refl. Qed.
Lemma D_75e2c : decode_any W_75e2c = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e30 : bv 32 := 0x00f67633.
Lemma F_75e30 : fetch_word Plain.M.loaded_segments (0x75e30 : word) = Some W_75e30.
Proof. vm_refl. Qed.
Lemma D_75e30 : decode_any W_75e30 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e34 : bv 32 := 0x00c585bb.
Lemma F_75e34 : fetch_word Plain.M.loaded_segments (0x75e34 : word) = Some W_75e34.
Proof. vm_refl. Qed.
Lemma D_75e34 : decode_any W_75e34 = Some (Op32 ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e38 : bv 32 := 0x00b78633.
Lemma F_75e38 : fetch_word Plain.M.loaded_segments (0x75e38 : word) = Some W_75e38.
Proof. vm_refl. Qed.
Lemma D_75e38 : decode_any W_75e38 = Some (Op ALU_ADD 12 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e3c : bv 32 := 0x0026061b.
Lemma F_75e3c : fetch_word Plain.M.loaded_segments (0x75e3c : word) = Some W_75e3c.
Proof. vm_refl. Qed.
Lemma D_75e3c : decode_any W_75e3c = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e40 : bv 32 := 0x160526af.
Lemma F_75e40 : fetch_word Plain.M.loaded_segments (0x75e40 : word) = Some W_75e40.
Proof. vm_refl. Qed.
Lemma D_75e40 : decode_any W_75e40 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e44 : bv 32 := 0x00b69663.
Lemma F_75e44 : fetch_word Plain.M.loaded_segments (0x75e44 : word) = Some W_75e44.
Proof. vm_refl. Qed.
Lemma D_75e44 : decode_any W_75e44 = Some (Branch BC_NE 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e48 : bv 32 := 0x1ec5272f.
Lemma F_75e48 : fetch_word Plain.M.loaded_segments (0x75e48 : word) = Some W_75e48.
Proof. vm_refl. Qed.
Lemma D_75e48 : decode_any W_75e48 = Some (Sc AW true true 14 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e4c : bv 32 := 0xfe071ae3.
Lemma F_75e4c : fetch_word Plain.M.loaded_segments (0x75e4c : word) = Some W_75e4c.
Proof. vm_refl. Qed.
Lemma D_75e4c : decode_any W_75e4c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e50 : bv 32 := 0x0006869b.
Lemma F_75e50 : fetch_word Plain.M.loaded_segments (0x75e50 : word) = Some W_75e50.
Proof. vm_refl. Qed.
Lemma D_75e50 : decode_any W_75e50 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e54 : bv 32 := 0x00b69463.
Lemma F_75e54 : fetch_word Plain.M.loaded_segments (0x75e54 : word) = Some W_75e54.
Proof. vm_refl. Qed.
Lemma D_75e54 : decode_any W_75e54 = Some (Branch BC_NE 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e58 : bv 32 := 0x00008067.
Lemma F_75e58 : fetch_word Plain.M.loaded_segments (0x75e58 : word) = Some W_75e58.
Proof. vm_refl. Qed.
Lemma D_75e58 : decode_any W_75e58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e5c : bv 32 := 0x00052583.
Lemma F_75e5c : fetch_word Plain.M.loaded_segments (0x75e5c : word) = Some W_75e5c.
Proof. vm_refl. Qed.
Lemma D_75e5c : decode_any W_75e5c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e60 : bv 32 := 0x0015881b.
Lemma F_75e60 : fetch_word Plain.M.loaded_segments (0x75e60 : word) = Some W_75e60.
Proof. vm_refl. Qed.
Lemma D_75e60 : decode_any W_75e60 = Some (OpImm32 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e64 : bv 32 := 0x1605262f.
Lemma F_75e64 : fetch_word Plain.M.loaded_segments (0x75e64 : word) = Some W_75e64.
Proof. vm_refl. Qed.
Lemma D_75e64 : decode_any W_75e64 = Some (Lr AW true true 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e68 : bv 32 := 0x00b61663.
Lemma F_75e68 : fetch_word Plain.M.loaded_segments (0x75e68 : word) = Some W_75e68.
Proof. vm_refl. Qed.
Lemma D_75e68 : decode_any W_75e68 = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e6c : bv 32 := 0x1f0526af.
Lemma F_75e6c : fetch_word Plain.M.loaded_segments (0x75e6c : word) = Some W_75e6c.
Proof. vm_refl. Qed.
Lemma D_75e6c : decode_any W_75e6c = Some (Sc AW true true 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e70 : bv 32 := 0xfe069ae3.
Lemma F_75e70 : fetch_word Plain.M.loaded_segments (0x75e70 : word) = Some W_75e70.
Proof. vm_refl. Qed.
Lemma D_75e70 : decode_any W_75e70 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e74 : bv 32 := 0x0006061b.
Lemma F_75e74 : fetch_word Plain.M.loaded_segments (0x75e74 : word) = Some W_75e74.
Proof. vm_refl. Qed.
Lemma D_75e74 : decode_any W_75e74 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e78 : bv 32 := 0xfeb612e3.
Lemma F_75e78 : fetch_word Plain.M.loaded_segments (0x75e78 : word) = Some W_75e78.
Proof. vm_refl. Qed.
Lemma D_75e78 : decode_any W_75e78 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e7c : bv 32 := 0xfda00293.
Lemma F_75e7c : fetch_word Plain.M.loaded_segments (0x75e7c : word) = Some W_75e7c.
Proof. vm_refl. Qed.
Lemma D_75e7c : decode_any W_75e7c = Some (OpImm ALU_ADD 5 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e80 : bv 32 := 0x80000337.
Lemma F_75e80 : fetch_word Plain.M.loaded_segments (0x75e80 : word) = Some W_75e80.
Proof. vm_refl. Qed.
Lemma D_75e80 : decode_any W_75e80 = Some (Lui 6 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e84 : bv 32 := 0x02c0006f.
Lemma F_75e84 : fetch_word Plain.M.loaded_segments (0x75e84 : word) = Some W_75e84.
Proof. vm_refl. Qed.
Lemma D_75e84 : decode_any W_75e84 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e88 : bv 32 := 0x00f8083b.
Lemma F_75e88 : fetch_word Plain.M.loaded_segments (0x75e88 : word) = Some W_75e88.
Proof. vm_refl. Qed.
Lemma D_75e88 : decode_any W_75e88 = Some (Op32 ALU_ADD 16 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e8c : bv 32 := 0x00070513.
Lemma F_75e8c : fetch_word Plain.M.loaded_segments (0x75e8c : word) = Some W_75e8c.
Proof. vm_refl. Qed.
Lemma D_75e8c : decode_any W_75e8c = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e90 : bv 32 := 0x006865b3.
Lemma F_75e90 : fetch_word Plain.M.loaded_segments (0x75e90 : word) = Some W_75e90.
Proof. vm_refl. Qed.
Lemma D_75e90 : decode_any W_75e90 = Some (Op ALU_OR 11 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e94 : bv 32 := 0x0008061b.
Lemma F_75e94 : fetch_word Plain.M.loaded_segments (0x75e94 : word) = Some W_75e94.
Proof. vm_refl. Qed.
Lemma D_75e94 : decode_any W_75e94 = Some (OpImm32 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e98 : bv 32 := 0x1605282f.
Lemma F_75e98 : fetch_word Plain.M.loaded_segments (0x75e98 : word) = Some W_75e98.
Proof. vm_refl. Qed.
Lemma D_75e98 : decode_any W_75e98 = Some (Lr AW true true 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e9c : bv 32 := 0x00c81663.
Lemma F_75e9c : fetch_word Plain.M.loaded_segments (0x75e9c : word) = Some W_75e9c.
Proof. vm_refl. Qed.
Lemma D_75e9c : decode_any W_75e9c = Some (Branch BC_NE 16 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ea0 : bv 32 := 0x1eb526af.
Lemma F_75ea0 : fetch_word Plain.M.loaded_segments (0x75ea0 : word) = Some W_75ea0.
Proof. vm_refl. Qed.
Lemma D_75ea0 : decode_any W_75ea0 = Some (Sc AW true true 13 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ea4 : bv 32 := 0xfe069ae3.
Lemma F_75ea4 : fetch_word Plain.M.loaded_segments (0x75ea4 : word) = Some W_75ea4.
Proof. vm_refl. Qed.
Lemma D_75ea4 : decode_any W_75ea4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ea8 : bv 32 := 0x0008059b.
Lemma F_75ea8 : fetch_word Plain.M.loaded_segments (0x75ea8 : word) = Some W_75ea8.
Proof. vm_refl. Qed.
Lemma D_75ea8 : decode_any W_75ea8 = Some (OpImm32 11 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75eac : bv 32 := 0xfac586e3.
Lemma F_75eac : fetch_word Plain.M.loaded_segments (0x75eac : word) = Some W_75eac.
Proof. vm_refl. Qed.
Lemma D_75eac : decode_any W_75eac = Some (Branch BC_EQ 11 12 8108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75eb0 : bv 32 := 0x0008061b.
Lemma F_75eb0 : fetch_word Plain.M.loaded_segments (0x75eb0 : word) = Some W_75eb0.
Proof. vm_refl. Qed.
Lemma D_75eb0 : decode_any W_75eb0 = Some (OpImm32 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75eb4 : bv 32 := 0xfc065ee3.
Lemma F_75eb4 : fetch_word Plain.M.loaded_segments (0x75eb4 : word) = Some W_75eb4.
Proof. vm_refl. Qed.
Lemma D_75eb4 : decode_any W_75eb4 = Some (Branch BC_GE 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75eb8 : bv 32 := 0x06200893.
Lemma F_75eb8 : fetch_word Plain.M.loaded_segments (0x75eb8 : word) = Some W_75eb8.
Proof. vm_refl. Qed.
Lemma D_75eb8 : decode_any W_75eb8 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ebc : bv 32 := 0x08000593.
Lemma F_75ebc : fetch_word Plain.M.loaded_segments (0x75ebc : word) = Some W_75ebc.
Proof. vm_refl. Qed.
Lemma D_75ebc : decode_any W_75ebc = Some (OpImm ALU_ADD 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ec0 : bv 32 := 0x00050713.
Lemma F_75ec0 : fetch_word Plain.M.loaded_segments (0x75ec0 : word) = Some W_75ec0.
Proof. vm_refl. Qed.
Lemma D_75ec0 : decode_any W_75ec0 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ec4 : bv 32 := 0x00000693.
Lemma F_75ec4 : fetch_word Plain.M.loaded_segments (0x75ec4 : word) = Some W_75ec4.
Proof. vm_refl. Qed.
Lemma D_75ec4 : decode_any W_75ec4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ec8 : bv 32 := 0x00000073.
Lemma F_75ec8 : fetch_word Plain.M.loaded_segments (0x75ec8 : word) = Some W_75ec8.
Proof. vm_refl. Qed.
Lemma D_75ec8 : decode_any W_75ec8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_75ec8 : is_ecall W_75ec8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_75ecc : bv 32 := 0xfa551ee3.
Lemma F_75ecc : fetch_word Plain.M.loaded_segments (0x75ecc : word) = Some W_75ecc.
Proof. vm_refl. Qed.
Lemma D_75ecc : decode_any W_75ecc = Some (Branch BC_NE 10 5 8124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ed0 : bv 32 := 0x06200893.
Lemma F_75ed0 : fetch_word Plain.M.loaded_segments (0x75ed0 : word) = Some W_75ed0.
Proof. vm_refl. Qed.
Lemma D_75ed0 : decode_any W_75ed0 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ed4 : bv 32 := 0x00070513.
Lemma F_75ed4 : fetch_word Plain.M.loaded_segments (0x75ed4 : word) = Some W_75ed4.
Proof. vm_refl. Qed.
Lemma D_75ed4 : decode_any W_75ed4 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ed8 : bv 32 := 0x00000593.
Lemma F_75ed8 : fetch_word Plain.M.loaded_segments (0x75ed8 : word) = Some W_75ed8.
Proof. vm_refl. Qed.
Lemma D_75ed8 : decode_any W_75ed8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75edc : bv 32 := 0x00000693.
Lemma F_75edc : fetch_word Plain.M.loaded_segments (0x75edc : word) = Some W_75edc.
Proof. vm_refl. Qed.
Lemma D_75edc : decode_any W_75edc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ee0 : bv 32 := 0x00000073.
Lemma F_75ee0 : fetch_word Plain.M.loaded_segments (0x75ee0 : word) = Some W_75ee0.
Proof. vm_refl. Qed.
Lemma D_75ee0 : decode_any W_75ee0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_75ee0 : is_ecall W_75ee0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_75ee4 : bv 32 := 0xfa5ff06f.
Lemma F_75ee4 : fetch_word Plain.M.loaded_segments (0x75ee4 : word) = Some W_75ee4.
Proof. vm_refl. Qed.
Lemma D_75ee4 : decode_any W_75ee4 = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ee8 : bv 32 := 0x00052583.
Lemma F_75ee8 : fetch_word Plain.M.loaded_segments (0x75ee8 : word) = Some W_75ee8.
Proof. vm_refl. Qed.
Lemma D_75ee8 : decode_any W_75ee8 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75eec : bv 32 := 0x0005c463.
Lemma F_75eec : fetch_word Plain.M.loaded_segments (0x75eec : word) = Some W_75eec.
Proof. vm_refl. Qed.
Lemma D_75eec : decode_any W_75eec = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ef0 : bv 32 := 0x00008067.
Lemma F_75ef0 : fetch_word Plain.M.loaded_segments (0x75ef0 : word) = Some W_75ef0.
Proof. vm_refl. Qed.
Lemma D_75ef0 : decode_any W_75ef0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ef4 : bv 32 := 0x80000637.
Lemma F_75ef4 : fetch_word Plain.M.loaded_segments (0x75ef4 : word) = Some W_75ef4.
Proof. vm_refl. Qed.
Lemma D_75ef4 : decode_any W_75ef4 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ef8 : bv 32 := 0xfff60613.
Lemma F_75ef8 : fetch_word Plain.M.loaded_segments (0x75ef8 : word) = Some W_75ef8.
Proof. vm_refl. Qed.
Lemma D_75ef8 : decode_any W_75ef8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75efc : bv 32 := 0x00052583.
Lemma F_75efc : fetch_word Plain.M.loaded_segments (0x75efc : word) = Some W_75efc.
Proof. vm_refl. Qed.
Lemma D_75efc : decode_any W_75efc = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f00 : bv 32 := 0x00c586bb.
Lemma F_75f00 : fetch_word Plain.M.loaded_segments (0x75f00 : word) = Some W_75f00.
Proof. vm_refl. Qed.
Lemma D_75f00 : decode_any W_75f00 = Some (Op32 ALU_ADD 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f04 : bv 32 := 0x1605272f.
Lemma F_75f04 : fetch_word Plain.M.loaded_segments (0x75f04 : word) = Some W_75f04.
Proof. vm_refl. Qed.
Lemma D_75f04 : decode_any W_75f04 = Some (Lr AW true true 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f08 : bv 32 := 0x00b71663.
Lemma F_75f08 : fetch_word Plain.M.loaded_segments (0x75f08 : word) = Some W_75f08.
Proof. vm_refl. Qed.
Lemma D_75f08 : decode_any W_75f08 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f0c : bv 32 := 0x1ed527af.
Lemma F_75f0c : fetch_word Plain.M.loaded_segments (0x75f0c : word) = Some W_75f0c.
Proof. vm_refl. Qed.
Lemma D_75f0c : decode_any W_75f0c = Some (Sc AW true true 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f10 : bv 32 := 0xfe079ae3.
Lemma F_75f10 : fetch_word Plain.M.loaded_segments (0x75f10 : word) = Some W_75f10.
Proof. vm_refl. Qed.
Lemma D_75f10 : decode_any W_75f10 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f14 : bv 32 := 0x0007071b.
Lemma F_75f14 : fetch_word Plain.M.loaded_segments (0x75f14 : word) = Some W_75f14.
Proof. vm_refl. Qed.
Lemma D_75f14 : decode_any W_75f14 = Some (OpImm32 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f18 : bv 32 := 0xfeb712e3.
Lemma F_75f18 : fetch_word Plain.M.loaded_segments (0x75f18 : word) = Some W_75f18.
Proof. vm_refl. Qed.
Lemma D_75f18 : decode_any W_75f18 = Some (Branch BC_NE 14 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f1c : bv 32 := 0x80000637.
Lemma F_75f1c : fetch_word Plain.M.loaded_segments (0x75f1c : word) = Some W_75f1c.
Proof. vm_refl. Qed.
Lemma D_75f1c : decode_any W_75f1c = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f20 : bv 32 := 0x0016061b.
Lemma F_75f20 : fetch_word Plain.M.loaded_segments (0x75f20 : word) = Some W_75f20.
Proof. vm_refl. Qed.
Lemma D_75f20 : decode_any W_75f20 = Some (OpImm32 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f24 : bv 32 := 0xfcc586e3.
Lemma F_75f24 : fetch_word Plain.M.loaded_segments (0x75f24 : word) = Some W_75f24.
Proof. vm_refl. Qed.
Lemma D_75f24 : decode_any W_75f24 = Some (Branch BC_EQ 11 12 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f28 : bv 32 := 0x06200893.
Lemma F_75f28 : fetch_word Plain.M.loaded_segments (0x75f28 : word) = Some W_75f28.
Proof. vm_refl. Qed.
Lemma D_75f28 : decode_any W_75f28 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f2c : bv 32 := 0x08100593.
Lemma F_75f2c : fetch_word Plain.M.loaded_segments (0x75f2c : word) = Some W_75f2c.
Proof. vm_refl. Qed.
Lemma D_75f2c : decode_any W_75f2c = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f30 : bv 32 := 0x00100613.
Lemma F_75f30 : fetch_word Plain.M.loaded_segments (0x75f30 : word) = Some W_75f30.
Proof. vm_refl. Qed.
Lemma D_75f30 : decode_any W_75f30 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f34 : bv 32 := 0xfda00713.
Lemma F_75f34 : fetch_word Plain.M.loaded_segments (0x75f34 : word) = Some W_75f34.
Proof. vm_refl. Qed.
Lemma D_75f34 : decode_any W_75f34 = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f38 : bv 32 := 0x00050693.
Lemma F_75f38 : fetch_word Plain.M.loaded_segments (0x75f38 : word) = Some W_75f38.
Proof. vm_refl. Qed.
Lemma D_75f38 : decode_any W_75f38 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f3c : bv 32 := 0x00000073.
Lemma F_75f3c : fetch_word Plain.M.loaded_segments (0x75f3c : word) = Some W_75f3c.
Proof. vm_refl. Qed.
Lemma D_75f3c : decode_any W_75f3c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_75f3c : is_ecall W_75f3c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_75f40 : bv 32 := 0xfae518e3.
Lemma F_75f40 : fetch_word Plain.M.loaded_segments (0x75f40 : word) = Some W_75f40.
Proof. vm_refl. Qed.
Lemma D_75f40 : decode_any W_75f40 = Some (Branch BC_NE 10 14 8112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f44 : bv 32 := 0x06200893.
Lemma F_75f44 : fetch_word Plain.M.loaded_segments (0x75f44 : word) = Some W_75f44.
Proof. vm_refl. Qed.
Lemma D_75f44 : decode_any W_75f44 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f48 : bv 32 := 0x00100593.
Lemma F_75f48 : fetch_word Plain.M.loaded_segments (0x75f48 : word) = Some W_75f48.
Proof. vm_refl. Qed.
Lemma D_75f48 : decode_any W_75f48 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f4c : bv 32 := 0x00100613.
Lemma F_75f4c : fetch_word Plain.M.loaded_segments (0x75f4c : word) = Some W_75f4c.
Proof. vm_refl. Qed.
Lemma D_75f4c : decode_any W_75f4c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f50 : bv 32 := 0x00068513.
Lemma F_75f50 : fetch_word Plain.M.loaded_segments (0x75f50 : word) = Some W_75f50.
Proof. vm_refl. Qed.
Lemma D_75f50 : decode_any W_75f50 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f54 : bv 32 := 0x00000073.
Lemma F_75f54 : fetch_word Plain.M.loaded_segments (0x75f54 : word) = Some W_75f54.
Proof. vm_refl. Qed.
Lemma D_75f54 : decode_any W_75f54 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_75f54 : is_ecall W_75f54 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_75f58 : bv 32 := 0x00008067.
Lemma F_75f58 : fetch_word Plain.M.loaded_segments (0x75f58 : word) = Some W_75f58.
Proof. vm_refl. Qed.
Lemma D_75f58 : decode_any W_75f58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f5c : bv 32 := 0x00050893.
Lemma F_75f5c : fetch_word Plain.M.loaded_segments (0x75f5c : word) = Some W_75f5c.
Proof. vm_refl. Qed.
Lemma D_75f5c : decode_any W_75f5c = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f60 : bv 32 := 0x00058513.
Lemma F_75f60 : fetch_word Plain.M.loaded_segments (0x75f60 : word) = Some W_75f60.
Proof. vm_refl. Qed.
Lemma D_75f60 : decode_any W_75f60 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f64 : bv 32 := 0x00060593.
Lemma F_75f64 : fetch_word Plain.M.loaded_segments (0x75f64 : word) = Some W_75f64.
Proof. vm_refl. Qed.
Lemma D_75f64 : decode_any W_75f64 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f68 : bv 32 := 0x00068613.
Lemma F_75f68 : fetch_word Plain.M.loaded_segments (0x75f68 : word) = Some W_75f68.
Proof. vm_refl. Qed.
Lemma D_75f68 : decode_any W_75f68 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f6c : bv 32 := 0x00070693.
Lemma F_75f6c : fetch_word Plain.M.loaded_segments (0x75f6c : word) = Some W_75f6c.
Proof. vm_refl. Qed.
Lemma D_75f6c : decode_any W_75f6c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f70 : bv 32 := 0x00078713.
Lemma F_75f70 : fetch_word Plain.M.loaded_segments (0x75f70 : word) = Some W_75f70.
Proof. vm_refl. Qed.
Lemma D_75f70 : decode_any W_75f70 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f74 : bv 32 := 0x00080793.
Lemma F_75f74 : fetch_word Plain.M.loaded_segments (0x75f74 : word) = Some W_75f74.
Proof. vm_refl. Qed.
Lemma D_75f74 : decode_any W_75f74 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f78 : bv 32 := 0x00000073.
Lemma F_75f78 : fetch_word Plain.M.loaded_segments (0x75f78 : word) = Some W_75f78.
Proof. vm_refl. Qed.
Lemma D_75f78 : decode_any W_75f78 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_75f78 : is_ecall W_75f78 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_75f7c : bv 32 := 0x00008067.
Lemma F_75f7c : fetch_word Plain.M.loaded_segments (0x75f7c : word) = Some W_75f7c.
Proof. vm_refl. Qed.
Lemma D_75f7c : decode_any W_75f7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f80 : bv 32 := 0xfddff06f.
Lemma F_75f80 : fetch_word Plain.M.loaded_segments (0x75f80 : word) = Some W_75f80.
Proof. vm_refl. Qed.
Lemma D_75f80 : decode_any W_75f80 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f84 : bv 32 := 0x00020593.
Lemma F_75f84 : fetch_word Plain.M.loaded_segments (0x75f84 : word) = Some W_75f84.
Proof. vm_refl. Qed.
Lemma D_75f84 : decode_any W_75f84 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f88 : bv 32 := 0x00053603.
Lemma F_75f88 : fetch_word Plain.M.loaded_segments (0x75f88 : word) = Some W_75f88.
Proof. vm_refl. Qed.
Lemma D_75f88 : decode_any W_75f88 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f8c : bv 32 := 0xff85b583.
Lemma F_75f8c : fetch_word Plain.M.loaded_segments (0x75f8c : word) = Some W_75f8c.
Proof. vm_refl. Qed.
Lemma D_75f8c : decode_any W_75f8c = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f90 : bv 32 := 0x00853503.
Lemma F_75f90 : fetch_word Plain.M.loaded_segments (0x75f90 : word) = Some W_75f90.
Proof. vm_refl. Qed.
Lemma D_75f90 : decode_any W_75f90 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f94 : bv 32 := 0x00361613.
Lemma F_75f94 : fetch_word Plain.M.loaded_segments (0x75f94 : word) = Some W_75f94.
Proof. vm_refl. Qed.
Lemma D_75f94 : decode_any W_75f94 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f98 : bv 32 := 0x00c585b3.
Lemma F_75f98 : fetch_word Plain.M.loaded_segments (0x75f98 : word) = Some W_75f98.
Proof. vm_refl. Qed.
Lemma D_75f98 : decode_any W_75f98 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f9c : bv 32 := 0x0005b583.
Lemma F_75f9c : fetch_word Plain.M.loaded_segments (0x75f9c : word) = Some W_75f9c.
Proof. vm_refl. Qed.
Lemma D_75f9c : decode_any W_75f9c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75fa0 : bv 32 := 0x00b50533.
Lemma F_75fa0 : fetch_word Plain.M.loaded_segments (0x75fa0 : word) = Some W_75fa0.
Proof. vm_refl. Qed.
Lemma D_75fa0 : decode_any W_75fa0 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75fa4 : bv 32 := 0x00008067.
Lemma F_75fa4 : fetch_word Plain.M.loaded_segments (0x75fa4 : word) = Some W_75fa4.
Proof. vm_refl. Qed.
Lemma D_75fa4 : decode_any W_75fa4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
