(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_79f8c : bv 32 := 0x0003d597.
Lemma F_79f8c : fetch_word Ubsan.M.loaded_segments (0x79f8c : word) = Some W_79f8c.
Proof. vm_refl. Qed.
Lemma D_79f8c : decode_any W_79f8c = Some (Auipc 11 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f90 : bv 32 := 0xc7758683.
Lemma F_79f90 : fetch_word Ubsan.M.loaded_segments (0x79f90 : word) = Some W_79f90.
Proof. vm_refl. Qed.
Lemma D_79f90 : decode_any W_79f90 = Some (Load SZ1 true 13 11 3191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f94 : bv 32 := 0x1e068863.
Lemma F_79f94 : fetch_word Ubsan.M.loaded_segments (0x79f94 : word) = Some W_79f94.
Proof. vm_refl. Qed.
Lemma D_79f94 : decode_any W_79f94 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f98 : bv 32 := 0x00000613.
Lemma F_79f98 : fetch_word Ubsan.M.loaded_segments (0x79f98 : word) = Some W_79f98.
Proof. vm_refl. Qed.
Lemma D_79f98 : decode_any W_79f98 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f9c : bv 32 := 0x80000737.
Lemma F_79f9c : fetch_word Ubsan.M.loaded_segments (0x79f9c : word) = Some W_79f9c.
Proof. vm_refl. Qed.
Lemma D_79f9c : decode_any W_79f9c = Some (Lui 14 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fa0 : bv 32 := 0x0017071b.
Lemma F_79fa0 : fetch_word Ubsan.M.loaded_segments (0x79fa0 : word) = Some W_79fa0.
Proof. vm_refl. Qed.
Lemma D_79fa0 : decode_any W_79fa0 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fa4 : bv 32 := 0x160527af.
Lemma F_79fa4 : fetch_word Ubsan.M.loaded_segments (0x79fa4 : word) = Some W_79fa4.
Proof. vm_refl. Qed.
Lemma D_79fa4 : decode_any W_79fa4 = Some (Lr AW true true 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fa8 : bv 32 := 0x00c79663.
Lemma F_79fa8 : fetch_word Ubsan.M.loaded_segments (0x79fa8 : word) = Some W_79fa8.
Proof. vm_refl. Qed.
Lemma D_79fa8 : decode_any W_79fa8 = Some (Branch BC_NE 15 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fac : bv 32 := 0x1ee5282f.
Lemma F_79fac : fetch_word Ubsan.M.loaded_segments (0x79fac : word) = Some W_79fac.
Proof. vm_refl. Qed.
Lemma D_79fac : decode_any W_79fac = Some (Sc AW true true 16 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fb0 : bv 32 := 0xfe081ae3.
Lemma F_79fb0 : fetch_word Ubsan.M.loaded_segments (0x79fb0 : word) = Some W_79fb0.
Proof. vm_refl. Qed.
Lemma D_79fb0 : decode_any W_79fb0 = Some (Branch BC_NE 16 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fb4 : bv 32 := 0x0007861b.
Lemma F_79fb4 : fetch_word Ubsan.M.loaded_segments (0x79fb4 : word) = Some W_79fb4.
Proof. vm_refl. Qed.
Lemma D_79fb4 : decode_any W_79fb4 = Some (OpImm32 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fb8 : bv 32 := 0x0006d463.
Lemma F_79fb8 : fetch_word Ubsan.M.loaded_segments (0x79fb8 : word) = Some W_79fb8.
Proof. vm_refl. Qed.
Lemma D_79fb8 : decode_any W_79fb8 = Some (Branch BC_GE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fbc : bv 32 := 0xc6058ba3.
Lemma F_79fbc : fetch_word Ubsan.M.loaded_segments (0x79fbc : word) = Some W_79fbc.
Proof. vm_refl. Qed.
Lemma D_79fbc : decode_any W_79fbc = Some (Store SZ1 11 0 3191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fc0 : bv 32 := 0x1c060263.
Lemma F_79fc0 : fetch_word Ubsan.M.loaded_segments (0x79fc0 : word) = Some W_79fc0.
Proof. vm_refl. Qed.
Lemma D_79fc0 : decode_any W_79fc0 = Some (Branch BC_EQ 12 0 452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fc4 : bv 32 := 0x800007b7.
Lemma F_79fc4 : fetch_word Ubsan.M.loaded_segments (0x79fc4 : word) = Some W_79fc4.
Proof. vm_refl. Qed.
Lemma D_79fc4 : decode_any W_79fc4 = Some (Lui 15 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fc8 : bv 32 := 0x00261593.
Lemma F_79fc8 : fetch_word Ubsan.M.loaded_segments (0x79fc8 : word) = Some W_79fc8.
Proof. vm_refl. Qed.
Lemma D_79fc8 : decode_any W_79fc8 = Some (ShiftImm ALU_SLL 11 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fcc : bv 32 := 0xfff78793.
Lemma F_79fcc : fetch_word Ubsan.M.loaded_segments (0x79fcc : word) = Some W_79fcc.
Proof. vm_refl. Qed.
Lemma D_79fcc : decode_any W_79fcc = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fd0 : bv 32 := 0x0215d593.
Lemma F_79fd0 : fetch_word Ubsan.M.loaded_segments (0x79fd0 : word) = Some W_79fd0.
Proof. vm_refl. Qed.
Lemma D_79fd0 : decode_any W_79fd0 = Some (ShiftImm ALU_SRL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fd4 : bv 32 := 0x00b6063b.
Lemma F_79fd4 : fetch_word Ubsan.M.loaded_segments (0x79fd4 : word) = Some W_79fd4.
Proof. vm_refl. Qed.
Lemma D_79fd4 : decode_any W_79fd4 = Some (Op32 ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fd8 : bv 32 := 0x00f605b3.
Lemma F_79fd8 : fetch_word Ubsan.M.loaded_segments (0x79fd8 : word) = Some W_79fd8.
Proof. vm_refl. Qed.
Lemma D_79fd8 : decode_any W_79fd8 = Some (Op ALU_ADD 11 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fdc : bv 32 := 0x0025859b.
Lemma F_79fdc : fetch_word Ubsan.M.loaded_segments (0x79fdc : word) = Some W_79fdc.
Proof. vm_refl. Qed.
Lemma D_79fdc : decode_any W_79fdc = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fe0 : bv 32 := 0x160526af.
Lemma F_79fe0 : fetch_word Ubsan.M.loaded_segments (0x79fe0 : word) = Some W_79fe0.
Proof. vm_refl. Qed.
Lemma D_79fe0 : decode_any W_79fe0 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fe4 : bv 32 := 0x00c69663.
Lemma F_79fe4 : fetch_word Ubsan.M.loaded_segments (0x79fe4 : word) = Some W_79fe4.
Proof. vm_refl. Qed.
Lemma D_79fe4 : decode_any W_79fe4 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fe8 : bv 32 := 0x1eb5272f.
Lemma F_79fe8 : fetch_word Ubsan.M.loaded_segments (0x79fe8 : word) = Some W_79fe8.
Proof. vm_refl. Qed.
Lemma D_79fe8 : decode_any W_79fe8 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fec : bv 32 := 0xfe071ae3.
Lemma F_79fec : fetch_word Ubsan.M.loaded_segments (0x79fec : word) = Some W_79fec.
Proof. vm_refl. Qed.
Lemma D_79fec : decode_any W_79fec = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ff0 : bv 32 := 0x0006859b.
Lemma F_79ff0 : fetch_word Ubsan.M.loaded_segments (0x79ff0 : word) = Some W_79ff0.
Proof. vm_refl. Qed.
Lemma D_79ff0 : decode_any W_79ff0 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ff4 : bv 32 := 0x18c58863.
Lemma F_79ff4 : fetch_word Ubsan.M.loaded_segments (0x79ff4 : word) = Some W_79ff4.
Proof. vm_refl. Qed.
Lemma D_79ff4 : decode_any W_79ff4 = Some (Branch BC_EQ 11 12 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ff8 : bv 32 := 0x01f5d613.
Lemma F_79ff8 : fetch_word Ubsan.M.loaded_segments (0x79ff8 : word) = Some W_79ff8.
Proof. vm_refl. Qed.
Lemma D_79ff8 : decode_any W_79ff8 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ffc : bv 32 := 0x00f67633.
Lemma F_79ffc : fetch_word Ubsan.M.loaded_segments (0x79ffc : word) = Some W_79ffc.
Proof. vm_refl. Qed.
Lemma D_79ffc : decode_any W_79ffc = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a000 : bv 32 := 0x00c5863b.
Lemma F_7a000 : fetch_word Ubsan.M.loaded_segments (0x7a000 : word) = Some W_7a000.
Proof. vm_refl. Qed.
Lemma D_7a000 : decode_any W_7a000 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a004 : bv 32 := 0x00c785b3.
Lemma F_7a004 : fetch_word Ubsan.M.loaded_segments (0x7a004 : word) = Some W_7a004.
Proof. vm_refl. Qed.
Lemma D_7a004 : decode_any W_7a004 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a008 : bv 32 := 0x0025859b.
Lemma F_7a008 : fetch_word Ubsan.M.loaded_segments (0x7a008 : word) = Some W_7a008.
Proof. vm_refl. Qed.
Lemma D_7a008 : decode_any W_7a008 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a00c : bv 32 := 0x160526af.
Lemma F_7a00c : fetch_word Ubsan.M.loaded_segments (0x7a00c : word) = Some W_7a00c.
Proof. vm_refl. Qed.
Lemma D_7a00c : decode_any W_7a00c = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a010 : bv 32 := 0x00c69663.
Lemma F_7a010 : fetch_word Ubsan.M.loaded_segments (0x7a010 : word) = Some W_7a010.
Proof. vm_refl. Qed.
Lemma D_7a010 : decode_any W_7a010 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a014 : bv 32 := 0x1eb5272f.
Lemma F_7a014 : fetch_word Ubsan.M.loaded_segments (0x7a014 : word) = Some W_7a014.
Proof. vm_refl. Qed.
Lemma D_7a014 : decode_any W_7a014 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a018 : bv 32 := 0xfe071ae3.
Lemma F_7a018 : fetch_word Ubsan.M.loaded_segments (0x7a018 : word) = Some W_7a018.
Proof. vm_refl. Qed.
Lemma D_7a018 : decode_any W_7a018 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a01c : bv 32 := 0x0006859b.
Lemma F_7a01c : fetch_word Ubsan.M.loaded_segments (0x7a01c : word) = Some W_7a01c.
Proof. vm_refl. Qed.
Lemma D_7a01c : decode_any W_7a01c = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a020 : bv 32 := 0x16c58263.
Lemma F_7a020 : fetch_word Ubsan.M.loaded_segments (0x7a020 : word) = Some W_7a020.
Proof. vm_refl. Qed.
Lemma D_7a020 : decode_any W_7a020 = Some (Branch BC_EQ 11 12 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a024 : bv 32 := 0x01f5d613.
Lemma F_7a024 : fetch_word Ubsan.M.loaded_segments (0x7a024 : word) = Some W_7a024.
Proof. vm_refl. Qed.
Lemma D_7a024 : decode_any W_7a024 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a028 : bv 32 := 0x00f67633.
Lemma F_7a028 : fetch_word Ubsan.M.loaded_segments (0x7a028 : word) = Some W_7a028.
Proof. vm_refl. Qed.
Lemma D_7a028 : decode_any W_7a028 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a02c : bv 32 := 0x00c5863b.
Lemma F_7a02c : fetch_word Ubsan.M.loaded_segments (0x7a02c : word) = Some W_7a02c.
Proof. vm_refl. Qed.
Lemma D_7a02c : decode_any W_7a02c = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a030 : bv 32 := 0x00c785b3.
Lemma F_7a030 : fetch_word Ubsan.M.loaded_segments (0x7a030 : word) = Some W_7a030.
Proof. vm_refl. Qed.
Lemma D_7a030 : decode_any W_7a030 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a034 : bv 32 := 0x0025859b.
Lemma F_7a034 : fetch_word Ubsan.M.loaded_segments (0x7a034 : word) = Some W_7a034.
Proof. vm_refl. Qed.
Lemma D_7a034 : decode_any W_7a034 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a038 : bv 32 := 0x160526af.
Lemma F_7a038 : fetch_word Ubsan.M.loaded_segments (0x7a038 : word) = Some W_7a038.
Proof. vm_refl. Qed.
Lemma D_7a038 : decode_any W_7a038 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a03c : bv 32 := 0x00c69663.
Lemma F_7a03c : fetch_word Ubsan.M.loaded_segments (0x7a03c : word) = Some W_7a03c.
Proof. vm_refl. Qed.
Lemma D_7a03c : decode_any W_7a03c = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a040 : bv 32 := 0x1eb5272f.
Lemma F_7a040 : fetch_word Ubsan.M.loaded_segments (0x7a040 : word) = Some W_7a040.
Proof. vm_refl. Qed.
Lemma D_7a040 : decode_any W_7a040 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a044 : bv 32 := 0xfe071ae3.
Lemma F_7a044 : fetch_word Ubsan.M.loaded_segments (0x7a044 : word) = Some W_7a044.
Proof. vm_refl. Qed.
Lemma D_7a044 : decode_any W_7a044 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a048 : bv 32 := 0x0006859b.
Lemma F_7a048 : fetch_word Ubsan.M.loaded_segments (0x7a048 : word) = Some W_7a048.
Proof. vm_refl. Qed.
Lemma D_7a048 : decode_any W_7a048 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a04c : bv 32 := 0x12c58c63.
Lemma F_7a04c : fetch_word Ubsan.M.loaded_segments (0x7a04c : word) = Some W_7a04c.
Proof. vm_refl. Qed.
Lemma D_7a04c : decode_any W_7a04c = Some (Branch BC_EQ 11 12 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a050 : bv 32 := 0x01f5d613.
Lemma F_7a050 : fetch_word Ubsan.M.loaded_segments (0x7a050 : word) = Some W_7a050.
Proof. vm_refl. Qed.
Lemma D_7a050 : decode_any W_7a050 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a054 : bv 32 := 0x00f67633.
Lemma F_7a054 : fetch_word Ubsan.M.loaded_segments (0x7a054 : word) = Some W_7a054.
Proof. vm_refl. Qed.
Lemma D_7a054 : decode_any W_7a054 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a058 : bv 32 := 0x00c5863b.
Lemma F_7a058 : fetch_word Ubsan.M.loaded_segments (0x7a058 : word) = Some W_7a058.
Proof. vm_refl. Qed.
Lemma D_7a058 : decode_any W_7a058 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a05c : bv 32 := 0x00c785b3.
Lemma F_7a05c : fetch_word Ubsan.M.loaded_segments (0x7a05c : word) = Some W_7a05c.
Proof. vm_refl. Qed.
Lemma D_7a05c : decode_any W_7a05c = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a060 : bv 32 := 0x0025859b.
Lemma F_7a060 : fetch_word Ubsan.M.loaded_segments (0x7a060 : word) = Some W_7a060.
Proof. vm_refl. Qed.
Lemma D_7a060 : decode_any W_7a060 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a064 : bv 32 := 0x160526af.
Lemma F_7a064 : fetch_word Ubsan.M.loaded_segments (0x7a064 : word) = Some W_7a064.
Proof. vm_refl. Qed.
Lemma D_7a064 : decode_any W_7a064 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a068 : bv 32 := 0x00c69663.
Lemma F_7a068 : fetch_word Ubsan.M.loaded_segments (0x7a068 : word) = Some W_7a068.
Proof. vm_refl. Qed.
Lemma D_7a068 : decode_any W_7a068 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a06c : bv 32 := 0x1eb5272f.
Lemma F_7a06c : fetch_word Ubsan.M.loaded_segments (0x7a06c : word) = Some W_7a06c.
Proof. vm_refl. Qed.
Lemma D_7a06c : decode_any W_7a06c = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a070 : bv 32 := 0xfe071ae3.
Lemma F_7a070 : fetch_word Ubsan.M.loaded_segments (0x7a070 : word) = Some W_7a070.
Proof. vm_refl. Qed.
Lemma D_7a070 : decode_any W_7a070 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a074 : bv 32 := 0x0006859b.
Lemma F_7a074 : fetch_word Ubsan.M.loaded_segments (0x7a074 : word) = Some W_7a074.
Proof. vm_refl. Qed.
Lemma D_7a074 : decode_any W_7a074 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a078 : bv 32 := 0x10c58663.
Lemma F_7a078 : fetch_word Ubsan.M.loaded_segments (0x7a078 : word) = Some W_7a078.
Proof. vm_refl. Qed.
Lemma D_7a078 : decode_any W_7a078 = Some (Branch BC_EQ 11 12 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a07c : bv 32 := 0x01f5d613.
Lemma F_7a07c : fetch_word Ubsan.M.loaded_segments (0x7a07c : word) = Some W_7a07c.
Proof. vm_refl. Qed.
Lemma D_7a07c : decode_any W_7a07c = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a080 : bv 32 := 0x00f67633.
Lemma F_7a080 : fetch_word Ubsan.M.loaded_segments (0x7a080 : word) = Some W_7a080.
Proof. vm_refl. Qed.
Lemma D_7a080 : decode_any W_7a080 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a084 : bv 32 := 0x00c5863b.
Lemma F_7a084 : fetch_word Ubsan.M.loaded_segments (0x7a084 : word) = Some W_7a084.
Proof. vm_refl. Qed.
Lemma D_7a084 : decode_any W_7a084 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a088 : bv 32 := 0x00c785b3.
Lemma F_7a088 : fetch_word Ubsan.M.loaded_segments (0x7a088 : word) = Some W_7a088.
Proof. vm_refl. Qed.
Lemma D_7a088 : decode_any W_7a088 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a08c : bv 32 := 0x0025859b.
Lemma F_7a08c : fetch_word Ubsan.M.loaded_segments (0x7a08c : word) = Some W_7a08c.
Proof. vm_refl. Qed.
Lemma D_7a08c : decode_any W_7a08c = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a090 : bv 32 := 0x160526af.
Lemma F_7a090 : fetch_word Ubsan.M.loaded_segments (0x7a090 : word) = Some W_7a090.
Proof. vm_refl. Qed.
Lemma D_7a090 : decode_any W_7a090 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a094 : bv 32 := 0x00c69663.
Lemma F_7a094 : fetch_word Ubsan.M.loaded_segments (0x7a094 : word) = Some W_7a094.
Proof. vm_refl. Qed.
Lemma D_7a094 : decode_any W_7a094 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a098 : bv 32 := 0x1eb5272f.
Lemma F_7a098 : fetch_word Ubsan.M.loaded_segments (0x7a098 : word) = Some W_7a098.
Proof. vm_refl. Qed.
Lemma D_7a098 : decode_any W_7a098 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a09c : bv 32 := 0xfe071ae3.
Lemma F_7a09c : fetch_word Ubsan.M.loaded_segments (0x7a09c : word) = Some W_7a09c.
Proof. vm_refl. Qed.
Lemma D_7a09c : decode_any W_7a09c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0a0 : bv 32 := 0x0006859b.
Lemma F_7a0a0 : fetch_word Ubsan.M.loaded_segments (0x7a0a0 : word) = Some W_7a0a0.
Proof. vm_refl. Qed.
Lemma D_7a0a0 : decode_any W_7a0a0 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0a4 : bv 32 := 0x0ec58063.
Lemma F_7a0a4 : fetch_word Ubsan.M.loaded_segments (0x7a0a4 : word) = Some W_7a0a4.
Proof. vm_refl. Qed.
Lemma D_7a0a4 : decode_any W_7a0a4 = Some (Branch BC_EQ 11 12 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0a8 : bv 32 := 0x01f5d613.
Lemma F_7a0a8 : fetch_word Ubsan.M.loaded_segments (0x7a0a8 : word) = Some W_7a0a8.
Proof. vm_refl. Qed.
Lemma D_7a0a8 : decode_any W_7a0a8 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0ac : bv 32 := 0x00f67633.
Lemma F_7a0ac : fetch_word Ubsan.M.loaded_segments (0x7a0ac : word) = Some W_7a0ac.
Proof. vm_refl. Qed.
Lemma D_7a0ac : decode_any W_7a0ac = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b0 : bv 32 := 0x00c5863b.
Lemma F_7a0b0 : fetch_word Ubsan.M.loaded_segments (0x7a0b0 : word) = Some W_7a0b0.
Proof. vm_refl. Qed.
Lemma D_7a0b0 : decode_any W_7a0b0 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b4 : bv 32 := 0x00c785b3.
Lemma F_7a0b4 : fetch_word Ubsan.M.loaded_segments (0x7a0b4 : word) = Some W_7a0b4.
Proof. vm_refl. Qed.
Lemma D_7a0b4 : decode_any W_7a0b4 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b8 : bv 32 := 0x0025859b.
Lemma F_7a0b8 : fetch_word Ubsan.M.loaded_segments (0x7a0b8 : word) = Some W_7a0b8.
Proof. vm_refl. Qed.
Lemma D_7a0b8 : decode_any W_7a0b8 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0bc : bv 32 := 0x160526af.
Lemma F_7a0bc : fetch_word Ubsan.M.loaded_segments (0x7a0bc : word) = Some W_7a0bc.
Proof. vm_refl. Qed.
Lemma D_7a0bc : decode_any W_7a0bc = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0c0 : bv 32 := 0x00c69663.
Lemma F_7a0c0 : fetch_word Ubsan.M.loaded_segments (0x7a0c0 : word) = Some W_7a0c0.
Proof. vm_refl. Qed.
Lemma D_7a0c0 : decode_any W_7a0c0 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0c4 : bv 32 := 0x1eb5272f.
Lemma F_7a0c4 : fetch_word Ubsan.M.loaded_segments (0x7a0c4 : word) = Some W_7a0c4.
Proof. vm_refl. Qed.
Lemma D_7a0c4 : decode_any W_7a0c4 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0c8 : bv 32 := 0xfe071ae3.
Lemma F_7a0c8 : fetch_word Ubsan.M.loaded_segments (0x7a0c8 : word) = Some W_7a0c8.
Proof. vm_refl. Qed.
Lemma D_7a0c8 : decode_any W_7a0c8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0cc : bv 32 := 0x0006859b.
Lemma F_7a0cc : fetch_word Ubsan.M.loaded_segments (0x7a0cc : word) = Some W_7a0cc.
Proof. vm_refl. Qed.
Lemma D_7a0cc : decode_any W_7a0cc = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0d0 : bv 32 := 0x0ac58a63.
Lemma F_7a0d0 : fetch_word Ubsan.M.loaded_segments (0x7a0d0 : word) = Some W_7a0d0.
Proof. vm_refl. Qed.
Lemma D_7a0d0 : decode_any W_7a0d0 = Some (Branch BC_EQ 11 12 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0d4 : bv 32 := 0x01f5d613.
Lemma F_7a0d4 : fetch_word Ubsan.M.loaded_segments (0x7a0d4 : word) = Some W_7a0d4.
Proof. vm_refl. Qed.
Lemma D_7a0d4 : decode_any W_7a0d4 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0d8 : bv 32 := 0x00f67633.
Lemma F_7a0d8 : fetch_word Ubsan.M.loaded_segments (0x7a0d8 : word) = Some W_7a0d8.
Proof. vm_refl. Qed.
Lemma D_7a0d8 : decode_any W_7a0d8 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0dc : bv 32 := 0x00c5863b.
Lemma F_7a0dc : fetch_word Ubsan.M.loaded_segments (0x7a0dc : word) = Some W_7a0dc.
Proof. vm_refl. Qed.
Lemma D_7a0dc : decode_any W_7a0dc = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0e0 : bv 32 := 0x00c785b3.
Lemma F_7a0e0 : fetch_word Ubsan.M.loaded_segments (0x7a0e0 : word) = Some W_7a0e0.
Proof. vm_refl. Qed.
Lemma D_7a0e0 : decode_any W_7a0e0 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0e4 : bv 32 := 0x0025859b.
Lemma F_7a0e4 : fetch_word Ubsan.M.loaded_segments (0x7a0e4 : word) = Some W_7a0e4.
Proof. vm_refl. Qed.
Lemma D_7a0e4 : decode_any W_7a0e4 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0e8 : bv 32 := 0x160526af.
Lemma F_7a0e8 : fetch_word Ubsan.M.loaded_segments (0x7a0e8 : word) = Some W_7a0e8.
Proof. vm_refl. Qed.
Lemma D_7a0e8 : decode_any W_7a0e8 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0ec : bv 32 := 0x00c69663.
Lemma F_7a0ec : fetch_word Ubsan.M.loaded_segments (0x7a0ec : word) = Some W_7a0ec.
Proof. vm_refl. Qed.
Lemma D_7a0ec : decode_any W_7a0ec = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0f0 : bv 32 := 0x1eb5272f.
Lemma F_7a0f0 : fetch_word Ubsan.M.loaded_segments (0x7a0f0 : word) = Some W_7a0f0.
Proof. vm_refl. Qed.
Lemma D_7a0f0 : decode_any W_7a0f0 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0f4 : bv 32 := 0xfe071ae3.
Lemma F_7a0f4 : fetch_word Ubsan.M.loaded_segments (0x7a0f4 : word) = Some W_7a0f4.
Proof. vm_refl. Qed.
Lemma D_7a0f4 : decode_any W_7a0f4 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0f8 : bv 32 := 0x0006859b.
Lemma F_7a0f8 : fetch_word Ubsan.M.loaded_segments (0x7a0f8 : word) = Some W_7a0f8.
Proof. vm_refl. Qed.
Lemma D_7a0f8 : decode_any W_7a0f8 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0fc : bv 32 := 0x08c58463.
Lemma F_7a0fc : fetch_word Ubsan.M.loaded_segments (0x7a0fc : word) = Some W_7a0fc.
Proof. vm_refl. Qed.
Lemma D_7a0fc : decode_any W_7a0fc = Some (Branch BC_EQ 11 12 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a100 : bv 32 := 0x01f5d613.
Lemma F_7a100 : fetch_word Ubsan.M.loaded_segments (0x7a100 : word) = Some W_7a100.
Proof. vm_refl. Qed.
Lemma D_7a100 : decode_any W_7a100 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a104 : bv 32 := 0x00f67633.
Lemma F_7a104 : fetch_word Ubsan.M.loaded_segments (0x7a104 : word) = Some W_7a104.
Proof. vm_refl. Qed.
Lemma D_7a104 : decode_any W_7a104 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a108 : bv 32 := 0x00c5863b.
Lemma F_7a108 : fetch_word Ubsan.M.loaded_segments (0x7a108 : word) = Some W_7a108.
Proof. vm_refl. Qed.
Lemma D_7a108 : decode_any W_7a108 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a10c : bv 32 := 0x00c785b3.
Lemma F_7a10c : fetch_word Ubsan.M.loaded_segments (0x7a10c : word) = Some W_7a10c.
Proof. vm_refl. Qed.
Lemma D_7a10c : decode_any W_7a10c = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a110 : bv 32 := 0x0025859b.
Lemma F_7a110 : fetch_word Ubsan.M.loaded_segments (0x7a110 : word) = Some W_7a110.
Proof. vm_refl. Qed.
Lemma D_7a110 : decode_any W_7a110 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a114 : bv 32 := 0x160526af.
Lemma F_7a114 : fetch_word Ubsan.M.loaded_segments (0x7a114 : word) = Some W_7a114.
Proof. vm_refl. Qed.
Lemma D_7a114 : decode_any W_7a114 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a118 : bv 32 := 0x00c69663.
Lemma F_7a118 : fetch_word Ubsan.M.loaded_segments (0x7a118 : word) = Some W_7a118.
Proof. vm_refl. Qed.
Lemma D_7a118 : decode_any W_7a118 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a11c : bv 32 := 0x1eb5272f.
Lemma F_7a11c : fetch_word Ubsan.M.loaded_segments (0x7a11c : word) = Some W_7a11c.
Proof. vm_refl. Qed.
Lemma D_7a11c : decode_any W_7a11c = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a120 : bv 32 := 0xfe071ae3.
Lemma F_7a120 : fetch_word Ubsan.M.loaded_segments (0x7a120 : word) = Some W_7a120.
Proof. vm_refl. Qed.
Lemma D_7a120 : decode_any W_7a120 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a124 : bv 32 := 0x0006859b.
Lemma F_7a124 : fetch_word Ubsan.M.loaded_segments (0x7a124 : word) = Some W_7a124.
Proof. vm_refl. Qed.
Lemma D_7a124 : decode_any W_7a124 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a128 : bv 32 := 0x04c58e63.
Lemma F_7a128 : fetch_word Ubsan.M.loaded_segments (0x7a128 : word) = Some W_7a128.
Proof. vm_refl. Qed.
Lemma D_7a128 : decode_any W_7a128 = Some (Branch BC_EQ 11 12 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a12c : bv 32 := 0x01f5d613.
Lemma F_7a12c : fetch_word Ubsan.M.loaded_segments (0x7a12c : word) = Some W_7a12c.
Proof. vm_refl. Qed.
Lemma D_7a12c : decode_any W_7a12c = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a130 : bv 32 := 0x00f67633.
Lemma F_7a130 : fetch_word Ubsan.M.loaded_segments (0x7a130 : word) = Some W_7a130.
Proof. vm_refl. Qed.
Lemma D_7a130 : decode_any W_7a130 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a134 : bv 32 := 0x00c5863b.
Lemma F_7a134 : fetch_word Ubsan.M.loaded_segments (0x7a134 : word) = Some W_7a134.
Proof. vm_refl. Qed.
Lemma D_7a134 : decode_any W_7a134 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a138 : bv 32 := 0x00c785b3.
Lemma F_7a138 : fetch_word Ubsan.M.loaded_segments (0x7a138 : word) = Some W_7a138.
Proof. vm_refl. Qed.
Lemma D_7a138 : decode_any W_7a138 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a13c : bv 32 := 0x0025859b.
Lemma F_7a13c : fetch_word Ubsan.M.loaded_segments (0x7a13c : word) = Some W_7a13c.
Proof. vm_refl. Qed.
Lemma D_7a13c : decode_any W_7a13c = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a140 : bv 32 := 0x160526af.
Lemma F_7a140 : fetch_word Ubsan.M.loaded_segments (0x7a140 : word) = Some W_7a140.
Proof. vm_refl. Qed.
Lemma D_7a140 : decode_any W_7a140 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a144 : bv 32 := 0x00c69663.
Lemma F_7a144 : fetch_word Ubsan.M.loaded_segments (0x7a144 : word) = Some W_7a144.
Proof. vm_refl. Qed.
Lemma D_7a144 : decode_any W_7a144 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a148 : bv 32 := 0x1eb5272f.
Lemma F_7a148 : fetch_word Ubsan.M.loaded_segments (0x7a148 : word) = Some W_7a148.
Proof. vm_refl. Qed.
Lemma D_7a148 : decode_any W_7a148 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a14c : bv 32 := 0xfe071ae3.
Lemma F_7a14c : fetch_word Ubsan.M.loaded_segments (0x7a14c : word) = Some W_7a14c.
Proof. vm_refl. Qed.
Lemma D_7a14c : decode_any W_7a14c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a150 : bv 32 := 0x0006859b.
Lemma F_7a150 : fetch_word Ubsan.M.loaded_segments (0x7a150 : word) = Some W_7a150.
Proof. vm_refl. Qed.
Lemma D_7a150 : decode_any W_7a150 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a154 : bv 32 := 0x02c58863.
Lemma F_7a154 : fetch_word Ubsan.M.loaded_segments (0x7a154 : word) = Some W_7a154.
Proof. vm_refl. Qed.
Lemma D_7a154 : decode_any W_7a154 = Some (Branch BC_EQ 11 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a158 : bv 32 := 0x01f5d613.
Lemma F_7a158 : fetch_word Ubsan.M.loaded_segments (0x7a158 : word) = Some W_7a158.
Proof. vm_refl. Qed.
Lemma D_7a158 : decode_any W_7a158 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a15c : bv 32 := 0x00f67633.
Lemma F_7a15c : fetch_word Ubsan.M.loaded_segments (0x7a15c : word) = Some W_7a15c.
Proof. vm_refl. Qed.
Lemma D_7a15c : decode_any W_7a15c = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a160 : bv 32 := 0x00c585bb.
Lemma F_7a160 : fetch_word Ubsan.M.loaded_segments (0x7a160 : word) = Some W_7a160.
Proof. vm_refl. Qed.
Lemma D_7a160 : decode_any W_7a160 = Some (Op32 ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a164 : bv 32 := 0x00b78633.
Lemma F_7a164 : fetch_word Ubsan.M.loaded_segments (0x7a164 : word) = Some W_7a164.
Proof. vm_refl. Qed.
Lemma D_7a164 : decode_any W_7a164 = Some (Op ALU_ADD 12 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a168 : bv 32 := 0x0026061b.
Lemma F_7a168 : fetch_word Ubsan.M.loaded_segments (0x7a168 : word) = Some W_7a168.
Proof. vm_refl. Qed.
Lemma D_7a168 : decode_any W_7a168 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a16c : bv 32 := 0x160526af.
Lemma F_7a16c : fetch_word Ubsan.M.loaded_segments (0x7a16c : word) = Some W_7a16c.
Proof. vm_refl. Qed.
Lemma D_7a16c : decode_any W_7a16c = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a170 : bv 32 := 0x00b69663.
Lemma F_7a170 : fetch_word Ubsan.M.loaded_segments (0x7a170 : word) = Some W_7a170.
Proof. vm_refl. Qed.
Lemma D_7a170 : decode_any W_7a170 = Some (Branch BC_NE 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a174 : bv 32 := 0x1ec5272f.
Lemma F_7a174 : fetch_word Ubsan.M.loaded_segments (0x7a174 : word) = Some W_7a174.
Proof. vm_refl. Qed.
Lemma D_7a174 : decode_any W_7a174 = Some (Sc AW true true 14 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a178 : bv 32 := 0xfe071ae3.
Lemma F_7a178 : fetch_word Ubsan.M.loaded_segments (0x7a178 : word) = Some W_7a178.
Proof. vm_refl. Qed.
Lemma D_7a178 : decode_any W_7a178 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a17c : bv 32 := 0x0006869b.
Lemma F_7a17c : fetch_word Ubsan.M.loaded_segments (0x7a17c : word) = Some W_7a17c.
Proof. vm_refl. Qed.
Lemma D_7a17c : decode_any W_7a17c = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a180 : bv 32 := 0x00b69463.
Lemma F_7a180 : fetch_word Ubsan.M.loaded_segments (0x7a180 : word) = Some W_7a180.
Proof. vm_refl. Qed.
Lemma D_7a180 : decode_any W_7a180 = Some (Branch BC_NE 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a184 : bv 32 := 0x00008067.
Lemma F_7a184 : fetch_word Ubsan.M.loaded_segments (0x7a184 : word) = Some W_7a184.
Proof. vm_refl. Qed.
Lemma D_7a184 : decode_any W_7a184 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a188 : bv 32 := 0x00052583.
Lemma F_7a188 : fetch_word Ubsan.M.loaded_segments (0x7a188 : word) = Some W_7a188.
Proof. vm_refl. Qed.
Lemma D_7a188 : decode_any W_7a188 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a18c : bv 32 := 0x0015881b.
Lemma F_7a18c : fetch_word Ubsan.M.loaded_segments (0x7a18c : word) = Some W_7a18c.
Proof. vm_refl. Qed.
Lemma D_7a18c : decode_any W_7a18c = Some (OpImm32 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a190 : bv 32 := 0x1605262f.
Lemma F_7a190 : fetch_word Ubsan.M.loaded_segments (0x7a190 : word) = Some W_7a190.
Proof. vm_refl. Qed.
Lemma D_7a190 : decode_any W_7a190 = Some (Lr AW true true 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a194 : bv 32 := 0x00b61663.
Lemma F_7a194 : fetch_word Ubsan.M.loaded_segments (0x7a194 : word) = Some W_7a194.
Proof. vm_refl. Qed.
Lemma D_7a194 : decode_any W_7a194 = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a198 : bv 32 := 0x1f0526af.
Lemma F_7a198 : fetch_word Ubsan.M.loaded_segments (0x7a198 : word) = Some W_7a198.
Proof. vm_refl. Qed.
Lemma D_7a198 : decode_any W_7a198 = Some (Sc AW true true 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a19c : bv 32 := 0xfe069ae3.
Lemma F_7a19c : fetch_word Ubsan.M.loaded_segments (0x7a19c : word) = Some W_7a19c.
Proof. vm_refl. Qed.
Lemma D_7a19c : decode_any W_7a19c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1a0 : bv 32 := 0x0006061b.
Lemma F_7a1a0 : fetch_word Ubsan.M.loaded_segments (0x7a1a0 : word) = Some W_7a1a0.
Proof. vm_refl. Qed.
Lemma D_7a1a0 : decode_any W_7a1a0 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1a4 : bv 32 := 0xfeb612e3.
Lemma F_7a1a4 : fetch_word Ubsan.M.loaded_segments (0x7a1a4 : word) = Some W_7a1a4.
Proof. vm_refl. Qed.
Lemma D_7a1a4 : decode_any W_7a1a4 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1a8 : bv 32 := 0xfda00293.
Lemma F_7a1a8 : fetch_word Ubsan.M.loaded_segments (0x7a1a8 : word) = Some W_7a1a8.
Proof. vm_refl. Qed.
Lemma D_7a1a8 : decode_any W_7a1a8 = Some (OpImm ALU_ADD 5 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1ac : bv 32 := 0x80000337.
Lemma F_7a1ac : fetch_word Ubsan.M.loaded_segments (0x7a1ac : word) = Some W_7a1ac.
Proof. vm_refl. Qed.
Lemma D_7a1ac : decode_any W_7a1ac = Some (Lui 6 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1b0 : bv 32 := 0x02c0006f.
Lemma F_7a1b0 : fetch_word Ubsan.M.loaded_segments (0x7a1b0 : word) = Some W_7a1b0.
Proof. vm_refl. Qed.
Lemma D_7a1b0 : decode_any W_7a1b0 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1b4 : bv 32 := 0x00f8083b.
Lemma F_7a1b4 : fetch_word Ubsan.M.loaded_segments (0x7a1b4 : word) = Some W_7a1b4.
Proof. vm_refl. Qed.
Lemma D_7a1b4 : decode_any W_7a1b4 = Some (Op32 ALU_ADD 16 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1b8 : bv 32 := 0x00070513.
Lemma F_7a1b8 : fetch_word Ubsan.M.loaded_segments (0x7a1b8 : word) = Some W_7a1b8.
Proof. vm_refl. Qed.
Lemma D_7a1b8 : decode_any W_7a1b8 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1bc : bv 32 := 0x006865b3.
Lemma F_7a1bc : fetch_word Ubsan.M.loaded_segments (0x7a1bc : word) = Some W_7a1bc.
Proof. vm_refl. Qed.
Lemma D_7a1bc : decode_any W_7a1bc = Some (Op ALU_OR 11 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1c0 : bv 32 := 0x0008061b.
Lemma F_7a1c0 : fetch_word Ubsan.M.loaded_segments (0x7a1c0 : word) = Some W_7a1c0.
Proof. vm_refl. Qed.
Lemma D_7a1c0 : decode_any W_7a1c0 = Some (OpImm32 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1c4 : bv 32 := 0x1605282f.
Lemma F_7a1c4 : fetch_word Ubsan.M.loaded_segments (0x7a1c4 : word) = Some W_7a1c4.
Proof. vm_refl. Qed.
Lemma D_7a1c4 : decode_any W_7a1c4 = Some (Lr AW true true 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1c8 : bv 32 := 0x00c81663.
Lemma F_7a1c8 : fetch_word Ubsan.M.loaded_segments (0x7a1c8 : word) = Some W_7a1c8.
Proof. vm_refl. Qed.
Lemma D_7a1c8 : decode_any W_7a1c8 = Some (Branch BC_NE 16 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1cc : bv 32 := 0x1eb526af.
Lemma F_7a1cc : fetch_word Ubsan.M.loaded_segments (0x7a1cc : word) = Some W_7a1cc.
Proof. vm_refl. Qed.
Lemma D_7a1cc : decode_any W_7a1cc = Some (Sc AW true true 13 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1d0 : bv 32 := 0xfe069ae3.
Lemma F_7a1d0 : fetch_word Ubsan.M.loaded_segments (0x7a1d0 : word) = Some W_7a1d0.
Proof. vm_refl. Qed.
Lemma D_7a1d0 : decode_any W_7a1d0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1d4 : bv 32 := 0x0008059b.
Lemma F_7a1d4 : fetch_word Ubsan.M.loaded_segments (0x7a1d4 : word) = Some W_7a1d4.
Proof. vm_refl. Qed.
Lemma D_7a1d4 : decode_any W_7a1d4 = Some (OpImm32 11 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1d8 : bv 32 := 0xfac586e3.
Lemma F_7a1d8 : fetch_word Ubsan.M.loaded_segments (0x7a1d8 : word) = Some W_7a1d8.
Proof. vm_refl. Qed.
Lemma D_7a1d8 : decode_any W_7a1d8 = Some (Branch BC_EQ 11 12 8108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1dc : bv 32 := 0x0008061b.
Lemma F_7a1dc : fetch_word Ubsan.M.loaded_segments (0x7a1dc : word) = Some W_7a1dc.
Proof. vm_refl. Qed.
Lemma D_7a1dc : decode_any W_7a1dc = Some (OpImm32 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1e0 : bv 32 := 0xfc065ee3.
Lemma F_7a1e0 : fetch_word Ubsan.M.loaded_segments (0x7a1e0 : word) = Some W_7a1e0.
Proof. vm_refl. Qed.
Lemma D_7a1e0 : decode_any W_7a1e0 = Some (Branch BC_GE 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1e4 : bv 32 := 0x06200893.
Lemma F_7a1e4 : fetch_word Ubsan.M.loaded_segments (0x7a1e4 : word) = Some W_7a1e4.
Proof. vm_refl. Qed.
Lemma D_7a1e4 : decode_any W_7a1e4 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1e8 : bv 32 := 0x08000593.
Lemma F_7a1e8 : fetch_word Ubsan.M.loaded_segments (0x7a1e8 : word) = Some W_7a1e8.
Proof. vm_refl. Qed.
Lemma D_7a1e8 : decode_any W_7a1e8 = Some (OpImm ALU_ADD 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1ec : bv 32 := 0x00050713.
Lemma F_7a1ec : fetch_word Ubsan.M.loaded_segments (0x7a1ec : word) = Some W_7a1ec.
Proof. vm_refl. Qed.
Lemma D_7a1ec : decode_any W_7a1ec = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1f0 : bv 32 := 0x00000693.
Lemma F_7a1f0 : fetch_word Ubsan.M.loaded_segments (0x7a1f0 : word) = Some W_7a1f0.
Proof. vm_refl. Qed.
Lemma D_7a1f0 : decode_any W_7a1f0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1f4 : bv 32 := 0x00000073.
Lemma F_7a1f4 : fetch_word Ubsan.M.loaded_segments (0x7a1f4 : word) = Some W_7a1f4.
Proof. vm_refl. Qed.
Lemma D_7a1f4 : decode_any W_7a1f4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7a1f4 : is_ecall W_7a1f4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7a1f8 : bv 32 := 0xfa551ee3.
Lemma F_7a1f8 : fetch_word Ubsan.M.loaded_segments (0x7a1f8 : word) = Some W_7a1f8.
Proof. vm_refl. Qed.
Lemma D_7a1f8 : decode_any W_7a1f8 = Some (Branch BC_NE 10 5 8124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1fc : bv 32 := 0x06200893.
Lemma F_7a1fc : fetch_word Ubsan.M.loaded_segments (0x7a1fc : word) = Some W_7a1fc.
Proof. vm_refl. Qed.
Lemma D_7a1fc : decode_any W_7a1fc = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a200 : bv 32 := 0x00070513.
Lemma F_7a200 : fetch_word Ubsan.M.loaded_segments (0x7a200 : word) = Some W_7a200.
Proof. vm_refl. Qed.
Lemma D_7a200 : decode_any W_7a200 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a204 : bv 32 := 0x00000593.
Lemma F_7a204 : fetch_word Ubsan.M.loaded_segments (0x7a204 : word) = Some W_7a204.
Proof. vm_refl. Qed.
Lemma D_7a204 : decode_any W_7a204 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a208 : bv 32 := 0x00000693.
Lemma F_7a208 : fetch_word Ubsan.M.loaded_segments (0x7a208 : word) = Some W_7a208.
Proof. vm_refl. Qed.
Lemma D_7a208 : decode_any W_7a208 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a20c : bv 32 := 0x00000073.
Lemma F_7a20c : fetch_word Ubsan.M.loaded_segments (0x7a20c : word) = Some W_7a20c.
Proof. vm_refl. Qed.
Lemma D_7a20c : decode_any W_7a20c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7a20c : is_ecall W_7a20c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7a210 : bv 32 := 0xfa5ff06f.
Lemma F_7a210 : fetch_word Ubsan.M.loaded_segments (0x7a210 : word) = Some W_7a210.
Proof. vm_refl. Qed.
Lemma D_7a210 : decode_any W_7a210 = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a214 : bv 32 := 0x00052583.
Lemma F_7a214 : fetch_word Ubsan.M.loaded_segments (0x7a214 : word) = Some W_7a214.
Proof. vm_refl. Qed.
Lemma D_7a214 : decode_any W_7a214 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a218 : bv 32 := 0x0005c463.
Lemma F_7a218 : fetch_word Ubsan.M.loaded_segments (0x7a218 : word) = Some W_7a218.
Proof. vm_refl. Qed.
Lemma D_7a218 : decode_any W_7a218 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a21c : bv 32 := 0x00008067.
Lemma F_7a21c : fetch_word Ubsan.M.loaded_segments (0x7a21c : word) = Some W_7a21c.
Proof. vm_refl. Qed.
Lemma D_7a21c : decode_any W_7a21c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a220 : bv 32 := 0x80000637.
Lemma F_7a220 : fetch_word Ubsan.M.loaded_segments (0x7a220 : word) = Some W_7a220.
Proof. vm_refl. Qed.
Lemma D_7a220 : decode_any W_7a220 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a224 : bv 32 := 0xfff60613.
Lemma F_7a224 : fetch_word Ubsan.M.loaded_segments (0x7a224 : word) = Some W_7a224.
Proof. vm_refl. Qed.
Lemma D_7a224 : decode_any W_7a224 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a228 : bv 32 := 0x00052583.
Lemma F_7a228 : fetch_word Ubsan.M.loaded_segments (0x7a228 : word) = Some W_7a228.
Proof. vm_refl. Qed.
Lemma D_7a228 : decode_any W_7a228 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a22c : bv 32 := 0x00c586bb.
Lemma F_7a22c : fetch_word Ubsan.M.loaded_segments (0x7a22c : word) = Some W_7a22c.
Proof. vm_refl. Qed.
Lemma D_7a22c : decode_any W_7a22c = Some (Op32 ALU_ADD 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a230 : bv 32 := 0x1605272f.
Lemma F_7a230 : fetch_word Ubsan.M.loaded_segments (0x7a230 : word) = Some W_7a230.
Proof. vm_refl. Qed.
Lemma D_7a230 : decode_any W_7a230 = Some (Lr AW true true 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a234 : bv 32 := 0x00b71663.
Lemma F_7a234 : fetch_word Ubsan.M.loaded_segments (0x7a234 : word) = Some W_7a234.
Proof. vm_refl. Qed.
Lemma D_7a234 : decode_any W_7a234 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a238 : bv 32 := 0x1ed527af.
Lemma F_7a238 : fetch_word Ubsan.M.loaded_segments (0x7a238 : word) = Some W_7a238.
Proof. vm_refl. Qed.
Lemma D_7a238 : decode_any W_7a238 = Some (Sc AW true true 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a23c : bv 32 := 0xfe079ae3.
Lemma F_7a23c : fetch_word Ubsan.M.loaded_segments (0x7a23c : word) = Some W_7a23c.
Proof. vm_refl. Qed.
Lemma D_7a23c : decode_any W_7a23c = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a240 : bv 32 := 0x0007071b.
Lemma F_7a240 : fetch_word Ubsan.M.loaded_segments (0x7a240 : word) = Some W_7a240.
Proof. vm_refl. Qed.
Lemma D_7a240 : decode_any W_7a240 = Some (OpImm32 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a244 : bv 32 := 0xfeb712e3.
Lemma F_7a244 : fetch_word Ubsan.M.loaded_segments (0x7a244 : word) = Some W_7a244.
Proof. vm_refl. Qed.
Lemma D_7a244 : decode_any W_7a244 = Some (Branch BC_NE 14 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a248 : bv 32 := 0x80000637.
Lemma F_7a248 : fetch_word Ubsan.M.loaded_segments (0x7a248 : word) = Some W_7a248.
Proof. vm_refl. Qed.
Lemma D_7a248 : decode_any W_7a248 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a24c : bv 32 := 0x0016061b.
Lemma F_7a24c : fetch_word Ubsan.M.loaded_segments (0x7a24c : word) = Some W_7a24c.
Proof. vm_refl. Qed.
Lemma D_7a24c : decode_any W_7a24c = Some (OpImm32 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a250 : bv 32 := 0xfcc586e3.
Lemma F_7a250 : fetch_word Ubsan.M.loaded_segments (0x7a250 : word) = Some W_7a250.
Proof. vm_refl. Qed.
Lemma D_7a250 : decode_any W_7a250 = Some (Branch BC_EQ 11 12 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a254 : bv 32 := 0x06200893.
Lemma F_7a254 : fetch_word Ubsan.M.loaded_segments (0x7a254 : word) = Some W_7a254.
Proof. vm_refl. Qed.
Lemma D_7a254 : decode_any W_7a254 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a258 : bv 32 := 0x08100593.
Lemma F_7a258 : fetch_word Ubsan.M.loaded_segments (0x7a258 : word) = Some W_7a258.
Proof. vm_refl. Qed.
Lemma D_7a258 : decode_any W_7a258 = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a25c : bv 32 := 0x00100613.
Lemma F_7a25c : fetch_word Ubsan.M.loaded_segments (0x7a25c : word) = Some W_7a25c.
Proof. vm_refl. Qed.
Lemma D_7a25c : decode_any W_7a25c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a260 : bv 32 := 0xfda00713.
Lemma F_7a260 : fetch_word Ubsan.M.loaded_segments (0x7a260 : word) = Some W_7a260.
Proof. vm_refl. Qed.
Lemma D_7a260 : decode_any W_7a260 = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a264 : bv 32 := 0x00050693.
Lemma F_7a264 : fetch_word Ubsan.M.loaded_segments (0x7a264 : word) = Some W_7a264.
Proof. vm_refl. Qed.
Lemma D_7a264 : decode_any W_7a264 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a268 : bv 32 := 0x00000073.
Lemma F_7a268 : fetch_word Ubsan.M.loaded_segments (0x7a268 : word) = Some W_7a268.
Proof. vm_refl. Qed.
Lemma D_7a268 : decode_any W_7a268 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7a268 : is_ecall W_7a268 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7a26c : bv 32 := 0xfae518e3.
Lemma F_7a26c : fetch_word Ubsan.M.loaded_segments (0x7a26c : word) = Some W_7a26c.
Proof. vm_refl. Qed.
Lemma D_7a26c : decode_any W_7a26c = Some (Branch BC_NE 10 14 8112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a270 : bv 32 := 0x06200893.
Lemma F_7a270 : fetch_word Ubsan.M.loaded_segments (0x7a270 : word) = Some W_7a270.
Proof. vm_refl. Qed.
Lemma D_7a270 : decode_any W_7a270 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a274 : bv 32 := 0x00100593.
Lemma F_7a274 : fetch_word Ubsan.M.loaded_segments (0x7a274 : word) = Some W_7a274.
Proof. vm_refl. Qed.
Lemma D_7a274 : decode_any W_7a274 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a278 : bv 32 := 0x00100613.
Lemma F_7a278 : fetch_word Ubsan.M.loaded_segments (0x7a278 : word) = Some W_7a278.
Proof. vm_refl. Qed.
Lemma D_7a278 : decode_any W_7a278 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a27c : bv 32 := 0x00068513.
Lemma F_7a27c : fetch_word Ubsan.M.loaded_segments (0x7a27c : word) = Some W_7a27c.
Proof. vm_refl. Qed.
Lemma D_7a27c : decode_any W_7a27c = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a280 : bv 32 := 0x00000073.
Lemma F_7a280 : fetch_word Ubsan.M.loaded_segments (0x7a280 : word) = Some W_7a280.
Proof. vm_refl. Qed.
Lemma D_7a280 : decode_any W_7a280 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7a280 : is_ecall W_7a280 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7a284 : bv 32 := 0x00008067.
Lemma F_7a284 : fetch_word Ubsan.M.loaded_segments (0x7a284 : word) = Some W_7a284.
Proof. vm_refl. Qed.
Lemma D_7a284 : decode_any W_7a284 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a288 : bv 32 := 0x00050893.
Lemma F_7a288 : fetch_word Ubsan.M.loaded_segments (0x7a288 : word) = Some W_7a288.
Proof. vm_refl. Qed.
Lemma D_7a288 : decode_any W_7a288 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a28c : bv 32 := 0x00058513.
Lemma F_7a28c : fetch_word Ubsan.M.loaded_segments (0x7a28c : word) = Some W_7a28c.
Proof. vm_refl. Qed.
Lemma D_7a28c : decode_any W_7a28c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a290 : bv 32 := 0x00060593.
Lemma F_7a290 : fetch_word Ubsan.M.loaded_segments (0x7a290 : word) = Some W_7a290.
Proof. vm_refl. Qed.
Lemma D_7a290 : decode_any W_7a290 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a294 : bv 32 := 0x00068613.
Lemma F_7a294 : fetch_word Ubsan.M.loaded_segments (0x7a294 : word) = Some W_7a294.
Proof. vm_refl. Qed.
Lemma D_7a294 : decode_any W_7a294 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a298 : bv 32 := 0x00070693.
Lemma F_7a298 : fetch_word Ubsan.M.loaded_segments (0x7a298 : word) = Some W_7a298.
Proof. vm_refl. Qed.
Lemma D_7a298 : decode_any W_7a298 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a29c : bv 32 := 0x00078713.
Lemma F_7a29c : fetch_word Ubsan.M.loaded_segments (0x7a29c : word) = Some W_7a29c.
Proof. vm_refl. Qed.
Lemma D_7a29c : decode_any W_7a29c = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2a0 : bv 32 := 0x00080793.
Lemma F_7a2a0 : fetch_word Ubsan.M.loaded_segments (0x7a2a0 : word) = Some W_7a2a0.
Proof. vm_refl. Qed.
Lemma D_7a2a0 : decode_any W_7a2a0 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2a4 : bv 32 := 0x00000073.
Lemma F_7a2a4 : fetch_word Ubsan.M.loaded_segments (0x7a2a4 : word) = Some W_7a2a4.
Proof. vm_refl. Qed.
Lemma D_7a2a4 : decode_any W_7a2a4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_7a2a4 : is_ecall W_7a2a4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_7a2a8 : bv 32 := 0x00008067.
Lemma F_7a2a8 : fetch_word Ubsan.M.loaded_segments (0x7a2a8 : word) = Some W_7a2a8.
Proof. vm_refl. Qed.
Lemma D_7a2a8 : decode_any W_7a2a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2ac : bv 32 := 0xfddff06f.
Lemma F_7a2ac : fetch_word Ubsan.M.loaded_segments (0x7a2ac : word) = Some W_7a2ac.
Proof. vm_refl. Qed.
Lemma D_7a2ac : decode_any W_7a2ac = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2b0 : bv 32 := 0x00020593.
Lemma F_7a2b0 : fetch_word Ubsan.M.loaded_segments (0x7a2b0 : word) = Some W_7a2b0.
Proof. vm_refl. Qed.
Lemma D_7a2b0 : decode_any W_7a2b0 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2b4 : bv 32 := 0x00053603.
Lemma F_7a2b4 : fetch_word Ubsan.M.loaded_segments (0x7a2b4 : word) = Some W_7a2b4.
Proof. vm_refl. Qed.
Lemma D_7a2b4 : decode_any W_7a2b4 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2b8 : bv 32 := 0xff85b583.
Lemma F_7a2b8 : fetch_word Ubsan.M.loaded_segments (0x7a2b8 : word) = Some W_7a2b8.
Proof. vm_refl. Qed.
Lemma D_7a2b8 : decode_any W_7a2b8 = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2bc : bv 32 := 0x00853503.
Lemma F_7a2bc : fetch_word Ubsan.M.loaded_segments (0x7a2bc : word) = Some W_7a2bc.
Proof. vm_refl. Qed.
Lemma D_7a2bc : decode_any W_7a2bc = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2c0 : bv 32 := 0x00361613.
Lemma F_7a2c0 : fetch_word Ubsan.M.loaded_segments (0x7a2c0 : word) = Some W_7a2c0.
Proof. vm_refl. Qed.
Lemma D_7a2c0 : decode_any W_7a2c0 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2c4 : bv 32 := 0x00c585b3.
Lemma F_7a2c4 : fetch_word Ubsan.M.loaded_segments (0x7a2c4 : word) = Some W_7a2c4.
Proof. vm_refl. Qed.
Lemma D_7a2c4 : decode_any W_7a2c4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2c8 : bv 32 := 0x0005b583.
Lemma F_7a2c8 : fetch_word Ubsan.M.loaded_segments (0x7a2c8 : word) = Some W_7a2c8.
Proof. vm_refl. Qed.
Lemma D_7a2c8 : decode_any W_7a2c8 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2cc : bv 32 := 0x00b50533.
Lemma F_7a2cc : fetch_word Ubsan.M.loaded_segments (0x7a2cc : word) = Some W_7a2cc.
Proof. vm_refl. Qed.
Lemma D_7a2cc : decode_any W_7a2cc = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2d0 : bv 32 := 0x00008067.
Lemma F_7a2d0 : fetch_word Ubsan.M.loaded_segments (0x7a2d0 : word) = Some W_7a2d0.
Proof. vm_refl. Qed.
Lemma D_7a2d0 : decode_any W_7a2d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
