(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8b594 : bv 32 := 0xff010113.
Lemma F_8b594 : fetch_word AsanUbsan.M.loaded_segments (0x8b9ac : word) = Some W_8b594.
Proof. vm_refl. Qed.
Lemma D_8b594 : decode_any W_8b594 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b598 : bv 32 := 0x00113423.
Lemma F_8b598 : fetch_word AsanUbsan.M.loaded_segments (0x8b9b0 : word) = Some W_8b598.
Proof. vm_refl. Qed.
Lemma D_8b598 : decode_any W_8b598 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b59c : bv 32 := 0x00058693.
Lemma F_8b59c : fetch_word AsanUbsan.M.loaded_segments (0x8b9b4 : word) = Some W_8b59c.
Proof. vm_refl. Qed.
Lemma D_8b59c : decode_any W_8b59c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5a0 : bv 32 := 0x00100713.
Lemma F_8b5a0 : fetch_word AsanUbsan.M.loaded_segments (0x8b9b8 : word) = Some W_8b5a0.
Proof. vm_refl. Qed.
Lemma D_8b5a0 : decode_any W_8b5a0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5a4 : bv 32 := 0x02871713.
Lemma F_8b5a4 : fetch_word AsanUbsan.M.loaded_segments (0x8b9bc : word) = Some W_8b5a4.
Proof. vm_refl. Qed.
Lemma D_8b5a4 : decode_any W_8b5a4 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5a8 : bv 32 := 0x00170593.
Lemma F_8b5a8 : fetch_word AsanUbsan.M.loaded_segments (0x8b9c0 : word) = Some W_8b5a8.
Proof. vm_refl. Qed.
Lemma D_8b5a8 : decode_any W_8b5a8 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5ac : bv 32 := 0x08b6f263.
Lemma F_8b5ac : fetch_word AsanUbsan.M.loaded_segments (0x8b9c4 : word) = Some W_8b5ac.
Proof. vm_refl. Qed.
Lemma D_8b5ac : decode_any W_8b5ac = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5b0 : bv 32 := 0x00000593.
Lemma F_8b5b0 : fetch_word AsanUbsan.M.loaded_segments (0x8b9c8 : word) = Some W_8b5b0.
Proof. vm_refl. Qed.
Lemma D_8b5b0 : decode_any W_8b5b0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5b4 : bv 32 := 0x00d50733.
Lemma F_8b5b4 : fetch_word AsanUbsan.M.loaded_segments (0x8b9cc : word) = Some W_8b5b4.
Proof. vm_refl. Qed.
Lemma D_8b5b4 : decode_any W_8b5b4 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5b8 : bv 32 := 0x00750793.
Lemma F_8b5b8 : fetch_word AsanUbsan.M.loaded_segments (0x8b9d0 : word) = Some W_8b5b8.
Proof. vm_refl. Qed.
Lemma D_8b5b8 : decode_any W_8b5b8 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5bc : bv 32 := 0xff87f793.
Lemma F_8b5bc : fetch_word AsanUbsan.M.loaded_segments (0x8b9d4 : word) = Some W_8b5bc.
Proof. vm_refl. Qed.
Lemma D_8b5bc : decode_any W_8b5bc = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5c0 : bv 32 := 0xff877613.
Lemma F_8b5c0 : fetch_word AsanUbsan.M.loaded_segments (0x8b9d8 : word) = Some W_8b5c0.
Proof. vm_refl. Qed.
Lemma D_8b5c0 : decode_any W_8b5c0 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5c4 : bv 32 := 0x02f57463.
Lemma F_8b5c4 : fetch_word AsanUbsan.M.loaded_segments (0x8b9dc : word) = Some W_8b5c4.
Proof. vm_refl. Qed.
Lemma D_8b5c4 : decode_any W_8b5c4 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5c8 : bv 32 := 0x02068263.
Lemma F_8b5c8 : fetch_word AsanUbsan.M.loaded_segments (0x8b9e0 : word) = Some W_8b5c8.
Proof. vm_refl. Qed.
Lemma D_8b5c8 : decode_any W_8b5c8 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5cc : bv 32 := 0x00000593.
Lemma F_8b5cc : fetch_word AsanUbsan.M.loaded_segments (0x8b9e4 : word) = Some W_8b5cc.
Proof. vm_refl. Qed.
Lemma D_8b5cc : decode_any W_8b5cc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5d0 : bv 32 := 0x00150693.
Lemma F_8b5d0 : fetch_word AsanUbsan.M.loaded_segments (0x8b9e8 : word) = Some W_8b5d0.
Proof. vm_refl. Qed.
Lemma D_8b5d0 : decode_any W_8b5d0 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5d4 : bv 32 := 0x00068813.
Lemma F_8b5d4 : fetch_word AsanUbsan.M.loaded_segments (0x8b9ec : word) = Some W_8b5d4.
Proof. vm_refl. Qed.
Lemma D_8b5d4 : decode_any W_8b5d4 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5d8 : bv 32 := 0xfff6c683.
Lemma F_8b5d8 : fetch_word AsanUbsan.M.loaded_segments (0x8b9f0 : word) = Some W_8b5d8.
Proof. vm_refl. Qed.
Lemma D_8b5d8 : decode_any W_8b5d8 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5dc : bv 32 := 0x00d5e5b3.
Lemma F_8b5dc : fetch_word AsanUbsan.M.loaded_segments (0x8b9f4 : word) = Some W_8b5dc.
Proof. vm_refl. Qed.
Lemma D_8b5dc : decode_any W_8b5dc = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5e0 : bv 32 := 0x00f87663.
Lemma F_8b5e0 : fetch_word AsanUbsan.M.loaded_segments (0x8b9f8 : word) = Some W_8b5e0.
Proof. vm_refl. Qed.
Lemma D_8b5e0 : decode_any W_8b5e0 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5e4 : bv 32 := 0x00180693.
Lemma F_8b5e4 : fetch_word AsanUbsan.M.loaded_segments (0x8b9fc : word) = Some W_8b5e4.
Proof. vm_refl. Qed.
Lemma D_8b5e4 : decode_any W_8b5e4 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5e8 : bv 32 := 0xfee866e3.
Lemma F_8b5e8 : fetch_word AsanUbsan.M.loaded_segments (0x8ba00 : word) = Some W_8b5e8.
Proof. vm_refl. Qed.
Lemma D_8b5e8 : decode_any W_8b5e8 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5ec : bv 32 := 0x00c7fa63.
Lemma F_8b5ec : fetch_word AsanUbsan.M.loaded_segments (0x8ba04 : word) = Some W_8b5ec.
Proof. vm_refl. Qed.
Lemma D_8b5ec : decode_any W_8b5ec = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5f0 : bv 32 := 0x0007b683.
Lemma F_8b5f0 : fetch_word AsanUbsan.M.loaded_segments (0x8ba08 : word) = Some W_8b5f0.
Proof. vm_refl. Qed.
Lemma D_8b5f0 : decode_any W_8b5f0 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5f4 : bv 32 := 0x00878793.
Lemma F_8b5f4 : fetch_word AsanUbsan.M.loaded_segments (0x8ba0c : word) = Some W_8b5f4.
Proof. vm_refl. Qed.
Lemma D_8b5f4 : decode_any W_8b5f4 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5f8 : bv 32 := 0x00b6e5b3.
Lemma F_8b5f8 : fetch_word AsanUbsan.M.loaded_segments (0x8ba10 : word) = Some W_8b5f8.
Proof. vm_refl. Qed.
Lemma D_8b5f8 : decode_any W_8b5f8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b5fc : bv 32 := 0xfec7eae3.
Lemma F_8b5fc : fetch_word AsanUbsan.M.loaded_segments (0x8ba14 : word) = Some W_8b5fc.
Proof. vm_refl. Qed.
Lemma D_8b5fc : decode_any W_8b5fc = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b600 : bv 32 := 0x02a66063.
Lemma F_8b600 : fetch_word AsanUbsan.M.loaded_segments (0x8ba18 : word) = Some W_8b600.
Proof. vm_refl. Qed.
Lemma D_8b600 : decode_any W_8b600 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b604 : bv 32 := 0x00e67e63.
Lemma F_8b604 : fetch_word AsanUbsan.M.loaded_segments (0x8ba1c : word) = Some W_8b604.
Proof. vm_refl. Qed.
Lemma D_8b604 : decode_any W_8b604 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b608 : bv 32 := 0x40c70733.
Lemma F_8b608 : fetch_word AsanUbsan.M.loaded_segments (0x8ba20 : word) = Some W_8b608.
Proof. vm_refl. Qed.
Lemma D_8b608 : decode_any W_8b608 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b60c : bv 32 := 0x00064503.
Lemma F_8b60c : fetch_word AsanUbsan.M.loaded_segments (0x8ba24 : word) = Some W_8b60c.
Proof. vm_refl. Qed.
Lemma D_8b60c : decode_any W_8b60c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b610 : bv 32 := 0xfff70713.
Lemma F_8b610 : fetch_word AsanUbsan.M.loaded_segments (0x8ba28 : word) = Some W_8b610.
Proof. vm_refl. Qed.
Lemma D_8b610 : decode_any W_8b610 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b614 : bv 32 := 0x00a5e5b3.
Lemma F_8b614 : fetch_word AsanUbsan.M.loaded_segments (0x8ba2c : word) = Some W_8b614.
Proof. vm_refl. Qed.
Lemma D_8b614 : decode_any W_8b614 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b618 : bv 32 := 0x00160613.
Lemma F_8b618 : fetch_word AsanUbsan.M.loaded_segments (0x8ba30 : word) = Some W_8b618.
Proof. vm_refl. Qed.
Lemma D_8b618 : decode_any W_8b618 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b61c : bv 32 := 0xfe0718e3.
Lemma F_8b61c : fetch_word AsanUbsan.M.loaded_segments (0x8ba34 : word) = Some W_8b61c.
Proof. vm_refl. Qed.
Lemma D_8b61c : decode_any W_8b61c = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b620 : bv 32 := 0x0015b513.
Lemma F_8b620 : fetch_word AsanUbsan.M.loaded_segments (0x8ba38 : word) = Some W_8b620.
Proof. vm_refl. Qed.
Lemma D_8b620 : decode_any W_8b620 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b624 : bv 32 := 0x00813083.
Lemma F_8b624 : fetch_word AsanUbsan.M.loaded_segments (0x8ba3c : word) = Some W_8b624.
Proof. vm_refl. Qed.
Lemma D_8b624 : decode_any W_8b624 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b628 : bv 32 := 0x01010113.
Lemma F_8b628 : fetch_word AsanUbsan.M.loaded_segments (0x8ba40 : word) = Some W_8b628.
Proof. vm_refl. Qed.
Lemma D_8b628 : decode_any W_8b628 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b62c : bv 32 := 0x00008067.
Lemma F_8b62c : fetch_word AsanUbsan.M.loaded_segments (0x8ba44 : word) = Some W_8b62c.
Proof. vm_refl. Qed.
Lemma D_8b62c : decode_any W_8b62c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
