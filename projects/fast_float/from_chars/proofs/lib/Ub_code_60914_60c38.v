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
Definition W_60914 : bv 32 := 0x00037597.
Lemma F_60914 : fetch_word Ubsan.M.loaded_segments (0x60914 : word) = Some W_60914.
Proof. vm_refl. Qed.
Lemma D_60914 : decode_any W_60914 = Some (Auipc 11 55, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60918 : bv 32 := 0x30f58683.
Lemma F_60918 : fetch_word Ubsan.M.loaded_segments (0x60918 : word) = Some W_60918.
Proof. vm_refl. Qed.
Lemma D_60918 : decode_any W_60918 = Some (Load SZ1 true 13 11 783, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6091c : bv 32 := 0x1e068863.
Lemma F_6091c : fetch_word Ubsan.M.loaded_segments (0x6091c : word) = Some W_6091c.
Proof. vm_refl. Qed.
Lemma D_6091c : decode_any W_6091c = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60920 : bv 32 := 0x00000613.
Lemma F_60920 : fetch_word Ubsan.M.loaded_segments (0x60920 : word) = Some W_60920.
Proof. vm_refl. Qed.
Lemma D_60920 : decode_any W_60920 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60924 : bv 32 := 0x80000737.
Lemma F_60924 : fetch_word Ubsan.M.loaded_segments (0x60924 : word) = Some W_60924.
Proof. vm_refl. Qed.
Lemma D_60924 : decode_any W_60924 = Some (Lui 14 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60928 : bv 32 := 0x0017071b.
Lemma F_60928 : fetch_word Ubsan.M.loaded_segments (0x60928 : word) = Some W_60928.
Proof. vm_refl. Qed.
Lemma D_60928 : decode_any W_60928 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6092c : bv 32 := 0x160527af.
Lemma F_6092c : fetch_word Ubsan.M.loaded_segments (0x6092c : word) = Some W_6092c.
Proof. vm_refl. Qed.
Lemma D_6092c : decode_any W_6092c = Some (Lr AW true true 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60930 : bv 32 := 0x00c79663.
Lemma F_60930 : fetch_word Ubsan.M.loaded_segments (0x60930 : word) = Some W_60930.
Proof. vm_refl. Qed.
Lemma D_60930 : decode_any W_60930 = Some (Branch BC_NE 15 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60934 : bv 32 := 0x1ee5282f.
Lemma F_60934 : fetch_word Ubsan.M.loaded_segments (0x60934 : word) = Some W_60934.
Proof. vm_refl. Qed.
Lemma D_60934 : decode_any W_60934 = Some (Sc AW true true 16 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60938 : bv 32 := 0xfe081ae3.
Lemma F_60938 : fetch_word Ubsan.M.loaded_segments (0x60938 : word) = Some W_60938.
Proof. vm_refl. Qed.
Lemma D_60938 : decode_any W_60938 = Some (Branch BC_NE 16 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6093c : bv 32 := 0x0007861b.
Lemma F_6093c : fetch_word Ubsan.M.loaded_segments (0x6093c : word) = Some W_6093c.
Proof. vm_refl. Qed.
Lemma D_6093c : decode_any W_6093c = Some (OpImm32 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60940 : bv 32 := 0x0006d463.
Lemma F_60940 : fetch_word Ubsan.M.loaded_segments (0x60940 : word) = Some W_60940.
Proof. vm_refl. Qed.
Lemma D_60940 : decode_any W_60940 = Some (Branch BC_GE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60944 : bv 32 := 0x300587a3.
Lemma F_60944 : fetch_word Ubsan.M.loaded_segments (0x60944 : word) = Some W_60944.
Proof. vm_refl. Qed.
Lemma D_60944 : decode_any W_60944 = Some (Store SZ1 11 0 783, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60948 : bv 32 := 0x1c060263.
Lemma F_60948 : fetch_word Ubsan.M.loaded_segments (0x60948 : word) = Some W_60948.
Proof. vm_refl. Qed.
Lemma D_60948 : decode_any W_60948 = Some (Branch BC_EQ 12 0 452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6094c : bv 32 := 0x800007b7.
Lemma F_6094c : fetch_word Ubsan.M.loaded_segments (0x6094c : word) = Some W_6094c.
Proof. vm_refl. Qed.
Lemma D_6094c : decode_any W_6094c = Some (Lui 15 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60950 : bv 32 := 0x00261593.
Lemma F_60950 : fetch_word Ubsan.M.loaded_segments (0x60950 : word) = Some W_60950.
Proof. vm_refl. Qed.
Lemma D_60950 : decode_any W_60950 = Some (ShiftImm ALU_SLL 11 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60954 : bv 32 := 0xfff78793.
Lemma F_60954 : fetch_word Ubsan.M.loaded_segments (0x60954 : word) = Some W_60954.
Proof. vm_refl. Qed.
Lemma D_60954 : decode_any W_60954 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60958 : bv 32 := 0x0215d593.
Lemma F_60958 : fetch_word Ubsan.M.loaded_segments (0x60958 : word) = Some W_60958.
Proof. vm_refl. Qed.
Lemma D_60958 : decode_any W_60958 = Some (ShiftImm ALU_SRL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6095c : bv 32 := 0x00b6063b.
Lemma F_6095c : fetch_word Ubsan.M.loaded_segments (0x6095c : word) = Some W_6095c.
Proof. vm_refl. Qed.
Lemma D_6095c : decode_any W_6095c = Some (Op32 ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60960 : bv 32 := 0x00f605b3.
Lemma F_60960 : fetch_word Ubsan.M.loaded_segments (0x60960 : word) = Some W_60960.
Proof. vm_refl. Qed.
Lemma D_60960 : decode_any W_60960 = Some (Op ALU_ADD 11 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60964 : bv 32 := 0x0025859b.
Lemma F_60964 : fetch_word Ubsan.M.loaded_segments (0x60964 : word) = Some W_60964.
Proof. vm_refl. Qed.
Lemma D_60964 : decode_any W_60964 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60968 : bv 32 := 0x160526af.
Lemma F_60968 : fetch_word Ubsan.M.loaded_segments (0x60968 : word) = Some W_60968.
Proof. vm_refl. Qed.
Lemma D_60968 : decode_any W_60968 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6096c : bv 32 := 0x00c69663.
Lemma F_6096c : fetch_word Ubsan.M.loaded_segments (0x6096c : word) = Some W_6096c.
Proof. vm_refl. Qed.
Lemma D_6096c : decode_any W_6096c = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60970 : bv 32 := 0x1eb5272f.
Lemma F_60970 : fetch_word Ubsan.M.loaded_segments (0x60970 : word) = Some W_60970.
Proof. vm_refl. Qed.
Lemma D_60970 : decode_any W_60970 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60974 : bv 32 := 0xfe071ae3.
Lemma F_60974 : fetch_word Ubsan.M.loaded_segments (0x60974 : word) = Some W_60974.
Proof. vm_refl. Qed.
Lemma D_60974 : decode_any W_60974 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60978 : bv 32 := 0x0006859b.
Lemma F_60978 : fetch_word Ubsan.M.loaded_segments (0x60978 : word) = Some W_60978.
Proof. vm_refl. Qed.
Lemma D_60978 : decode_any W_60978 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6097c : bv 32 := 0x18c58863.
Lemma F_6097c : fetch_word Ubsan.M.loaded_segments (0x6097c : word) = Some W_6097c.
Proof. vm_refl. Qed.
Lemma D_6097c : decode_any W_6097c = Some (Branch BC_EQ 11 12 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60980 : bv 32 := 0x01f5d613.
Lemma F_60980 : fetch_word Ubsan.M.loaded_segments (0x60980 : word) = Some W_60980.
Proof. vm_refl. Qed.
Lemma D_60980 : decode_any W_60980 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60984 : bv 32 := 0x00f67633.
Lemma F_60984 : fetch_word Ubsan.M.loaded_segments (0x60984 : word) = Some W_60984.
Proof. vm_refl. Qed.
Lemma D_60984 : decode_any W_60984 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60988 : bv 32 := 0x00c5863b.
Lemma F_60988 : fetch_word Ubsan.M.loaded_segments (0x60988 : word) = Some W_60988.
Proof. vm_refl. Qed.
Lemma D_60988 : decode_any W_60988 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6098c : bv 32 := 0x00c785b3.
Lemma F_6098c : fetch_word Ubsan.M.loaded_segments (0x6098c : word) = Some W_6098c.
Proof. vm_refl. Qed.
Lemma D_6098c : decode_any W_6098c = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60990 : bv 32 := 0x0025859b.
Lemma F_60990 : fetch_word Ubsan.M.loaded_segments (0x60990 : word) = Some W_60990.
Proof. vm_refl. Qed.
Lemma D_60990 : decode_any W_60990 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60994 : bv 32 := 0x160526af.
Lemma F_60994 : fetch_word Ubsan.M.loaded_segments (0x60994 : word) = Some W_60994.
Proof. vm_refl. Qed.
Lemma D_60994 : decode_any W_60994 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60998 : bv 32 := 0x00c69663.
Lemma F_60998 : fetch_word Ubsan.M.loaded_segments (0x60998 : word) = Some W_60998.
Proof. vm_refl. Qed.
Lemma D_60998 : decode_any W_60998 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6099c : bv 32 := 0x1eb5272f.
Lemma F_6099c : fetch_word Ubsan.M.loaded_segments (0x6099c : word) = Some W_6099c.
Proof. vm_refl. Qed.
Lemma D_6099c : decode_any W_6099c = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609a0 : bv 32 := 0xfe071ae3.
Lemma F_609a0 : fetch_word Ubsan.M.loaded_segments (0x609a0 : word) = Some W_609a0.
Proof. vm_refl. Qed.
Lemma D_609a0 : decode_any W_609a0 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609a4 : bv 32 := 0x0006859b.
Lemma F_609a4 : fetch_word Ubsan.M.loaded_segments (0x609a4 : word) = Some W_609a4.
Proof. vm_refl. Qed.
Lemma D_609a4 : decode_any W_609a4 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609a8 : bv 32 := 0x16c58263.
Lemma F_609a8 : fetch_word Ubsan.M.loaded_segments (0x609a8 : word) = Some W_609a8.
Proof. vm_refl. Qed.
Lemma D_609a8 : decode_any W_609a8 = Some (Branch BC_EQ 11 12 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609ac : bv 32 := 0x01f5d613.
Lemma F_609ac : fetch_word Ubsan.M.loaded_segments (0x609ac : word) = Some W_609ac.
Proof. vm_refl. Qed.
Lemma D_609ac : decode_any W_609ac = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609b0 : bv 32 := 0x00f67633.
Lemma F_609b0 : fetch_word Ubsan.M.loaded_segments (0x609b0 : word) = Some W_609b0.
Proof. vm_refl. Qed.
Lemma D_609b0 : decode_any W_609b0 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609b4 : bv 32 := 0x00c5863b.
Lemma F_609b4 : fetch_word Ubsan.M.loaded_segments (0x609b4 : word) = Some W_609b4.
Proof. vm_refl. Qed.
Lemma D_609b4 : decode_any W_609b4 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609b8 : bv 32 := 0x00c785b3.
Lemma F_609b8 : fetch_word Ubsan.M.loaded_segments (0x609b8 : word) = Some W_609b8.
Proof. vm_refl. Qed.
Lemma D_609b8 : decode_any W_609b8 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609bc : bv 32 := 0x0025859b.
Lemma F_609bc : fetch_word Ubsan.M.loaded_segments (0x609bc : word) = Some W_609bc.
Proof. vm_refl. Qed.
Lemma D_609bc : decode_any W_609bc = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609c0 : bv 32 := 0x160526af.
Lemma F_609c0 : fetch_word Ubsan.M.loaded_segments (0x609c0 : word) = Some W_609c0.
Proof. vm_refl. Qed.
Lemma D_609c0 : decode_any W_609c0 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609c4 : bv 32 := 0x00c69663.
Lemma F_609c4 : fetch_word Ubsan.M.loaded_segments (0x609c4 : word) = Some W_609c4.
Proof. vm_refl. Qed.
Lemma D_609c4 : decode_any W_609c4 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609c8 : bv 32 := 0x1eb5272f.
Lemma F_609c8 : fetch_word Ubsan.M.loaded_segments (0x609c8 : word) = Some W_609c8.
Proof. vm_refl. Qed.
Lemma D_609c8 : decode_any W_609c8 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609cc : bv 32 := 0xfe071ae3.
Lemma F_609cc : fetch_word Ubsan.M.loaded_segments (0x609cc : word) = Some W_609cc.
Proof. vm_refl. Qed.
Lemma D_609cc : decode_any W_609cc = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609d0 : bv 32 := 0x0006859b.
Lemma F_609d0 : fetch_word Ubsan.M.loaded_segments (0x609d0 : word) = Some W_609d0.
Proof. vm_refl. Qed.
Lemma D_609d0 : decode_any W_609d0 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609d4 : bv 32 := 0x12c58c63.
Lemma F_609d4 : fetch_word Ubsan.M.loaded_segments (0x609d4 : word) = Some W_609d4.
Proof. vm_refl. Qed.
Lemma D_609d4 : decode_any W_609d4 = Some (Branch BC_EQ 11 12 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609d8 : bv 32 := 0x01f5d613.
Lemma F_609d8 : fetch_word Ubsan.M.loaded_segments (0x609d8 : word) = Some W_609d8.
Proof. vm_refl. Qed.
Lemma D_609d8 : decode_any W_609d8 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609dc : bv 32 := 0x00f67633.
Lemma F_609dc : fetch_word Ubsan.M.loaded_segments (0x609dc : word) = Some W_609dc.
Proof. vm_refl. Qed.
Lemma D_609dc : decode_any W_609dc = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609e0 : bv 32 := 0x00c5863b.
Lemma F_609e0 : fetch_word Ubsan.M.loaded_segments (0x609e0 : word) = Some W_609e0.
Proof. vm_refl. Qed.
Lemma D_609e0 : decode_any W_609e0 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609e4 : bv 32 := 0x00c785b3.
Lemma F_609e4 : fetch_word Ubsan.M.loaded_segments (0x609e4 : word) = Some W_609e4.
Proof. vm_refl. Qed.
Lemma D_609e4 : decode_any W_609e4 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609e8 : bv 32 := 0x0025859b.
Lemma F_609e8 : fetch_word Ubsan.M.loaded_segments (0x609e8 : word) = Some W_609e8.
Proof. vm_refl. Qed.
Lemma D_609e8 : decode_any W_609e8 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609ec : bv 32 := 0x160526af.
Lemma F_609ec : fetch_word Ubsan.M.loaded_segments (0x609ec : word) = Some W_609ec.
Proof. vm_refl. Qed.
Lemma D_609ec : decode_any W_609ec = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609f0 : bv 32 := 0x00c69663.
Lemma F_609f0 : fetch_word Ubsan.M.loaded_segments (0x609f0 : word) = Some W_609f0.
Proof. vm_refl. Qed.
Lemma D_609f0 : decode_any W_609f0 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609f4 : bv 32 := 0x1eb5272f.
Lemma F_609f4 : fetch_word Ubsan.M.loaded_segments (0x609f4 : word) = Some W_609f4.
Proof. vm_refl. Qed.
Lemma D_609f4 : decode_any W_609f4 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609f8 : bv 32 := 0xfe071ae3.
Lemma F_609f8 : fetch_word Ubsan.M.loaded_segments (0x609f8 : word) = Some W_609f8.
Proof. vm_refl. Qed.
Lemma D_609f8 : decode_any W_609f8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_609fc : bv 32 := 0x0006859b.
Lemma F_609fc : fetch_word Ubsan.M.loaded_segments (0x609fc : word) = Some W_609fc.
Proof. vm_refl. Qed.
Lemma D_609fc : decode_any W_609fc = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a00 : bv 32 := 0x10c58663.
Lemma F_60a00 : fetch_word Ubsan.M.loaded_segments (0x60a00 : word) = Some W_60a00.
Proof. vm_refl. Qed.
Lemma D_60a00 : decode_any W_60a00 = Some (Branch BC_EQ 11 12 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a04 : bv 32 := 0x01f5d613.
Lemma F_60a04 : fetch_word Ubsan.M.loaded_segments (0x60a04 : word) = Some W_60a04.
Proof. vm_refl. Qed.
Lemma D_60a04 : decode_any W_60a04 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a08 : bv 32 := 0x00f67633.
Lemma F_60a08 : fetch_word Ubsan.M.loaded_segments (0x60a08 : word) = Some W_60a08.
Proof. vm_refl. Qed.
Lemma D_60a08 : decode_any W_60a08 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a0c : bv 32 := 0x00c5863b.
Lemma F_60a0c : fetch_word Ubsan.M.loaded_segments (0x60a0c : word) = Some W_60a0c.
Proof. vm_refl. Qed.
Lemma D_60a0c : decode_any W_60a0c = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a10 : bv 32 := 0x00c785b3.
Lemma F_60a10 : fetch_word Ubsan.M.loaded_segments (0x60a10 : word) = Some W_60a10.
Proof. vm_refl. Qed.
Lemma D_60a10 : decode_any W_60a10 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a14 : bv 32 := 0x0025859b.
Lemma F_60a14 : fetch_word Ubsan.M.loaded_segments (0x60a14 : word) = Some W_60a14.
Proof. vm_refl. Qed.
Lemma D_60a14 : decode_any W_60a14 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a18 : bv 32 := 0x160526af.
Lemma F_60a18 : fetch_word Ubsan.M.loaded_segments (0x60a18 : word) = Some W_60a18.
Proof. vm_refl. Qed.
Lemma D_60a18 : decode_any W_60a18 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a1c : bv 32 := 0x00c69663.
Lemma F_60a1c : fetch_word Ubsan.M.loaded_segments (0x60a1c : word) = Some W_60a1c.
Proof. vm_refl. Qed.
Lemma D_60a1c : decode_any W_60a1c = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a20 : bv 32 := 0x1eb5272f.
Lemma F_60a20 : fetch_word Ubsan.M.loaded_segments (0x60a20 : word) = Some W_60a20.
Proof. vm_refl. Qed.
Lemma D_60a20 : decode_any W_60a20 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a24 : bv 32 := 0xfe071ae3.
Lemma F_60a24 : fetch_word Ubsan.M.loaded_segments (0x60a24 : word) = Some W_60a24.
Proof. vm_refl. Qed.
Lemma D_60a24 : decode_any W_60a24 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a28 : bv 32 := 0x0006859b.
Lemma F_60a28 : fetch_word Ubsan.M.loaded_segments (0x60a28 : word) = Some W_60a28.
Proof. vm_refl. Qed.
Lemma D_60a28 : decode_any W_60a28 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a2c : bv 32 := 0x0ec58063.
Lemma F_60a2c : fetch_word Ubsan.M.loaded_segments (0x60a2c : word) = Some W_60a2c.
Proof. vm_refl. Qed.
Lemma D_60a2c : decode_any W_60a2c = Some (Branch BC_EQ 11 12 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a30 : bv 32 := 0x01f5d613.
Lemma F_60a30 : fetch_word Ubsan.M.loaded_segments (0x60a30 : word) = Some W_60a30.
Proof. vm_refl. Qed.
Lemma D_60a30 : decode_any W_60a30 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a34 : bv 32 := 0x00f67633.
Lemma F_60a34 : fetch_word Ubsan.M.loaded_segments (0x60a34 : word) = Some W_60a34.
Proof. vm_refl. Qed.
Lemma D_60a34 : decode_any W_60a34 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a38 : bv 32 := 0x00c5863b.
Lemma F_60a38 : fetch_word Ubsan.M.loaded_segments (0x60a38 : word) = Some W_60a38.
Proof. vm_refl. Qed.
Lemma D_60a38 : decode_any W_60a38 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a3c : bv 32 := 0x00c785b3.
Lemma F_60a3c : fetch_word Ubsan.M.loaded_segments (0x60a3c : word) = Some W_60a3c.
Proof. vm_refl. Qed.
Lemma D_60a3c : decode_any W_60a3c = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a40 : bv 32 := 0x0025859b.
Lemma F_60a40 : fetch_word Ubsan.M.loaded_segments (0x60a40 : word) = Some W_60a40.
Proof. vm_refl. Qed.
Lemma D_60a40 : decode_any W_60a40 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a44 : bv 32 := 0x160526af.
Lemma F_60a44 : fetch_word Ubsan.M.loaded_segments (0x60a44 : word) = Some W_60a44.
Proof. vm_refl. Qed.
Lemma D_60a44 : decode_any W_60a44 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a48 : bv 32 := 0x00c69663.
Lemma F_60a48 : fetch_word Ubsan.M.loaded_segments (0x60a48 : word) = Some W_60a48.
Proof. vm_refl. Qed.
Lemma D_60a48 : decode_any W_60a48 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a4c : bv 32 := 0x1eb5272f.
Lemma F_60a4c : fetch_word Ubsan.M.loaded_segments (0x60a4c : word) = Some W_60a4c.
Proof. vm_refl. Qed.
Lemma D_60a4c : decode_any W_60a4c = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a50 : bv 32 := 0xfe071ae3.
Lemma F_60a50 : fetch_word Ubsan.M.loaded_segments (0x60a50 : word) = Some W_60a50.
Proof. vm_refl. Qed.
Lemma D_60a50 : decode_any W_60a50 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a54 : bv 32 := 0x0006859b.
Lemma F_60a54 : fetch_word Ubsan.M.loaded_segments (0x60a54 : word) = Some W_60a54.
Proof. vm_refl. Qed.
Lemma D_60a54 : decode_any W_60a54 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a58 : bv 32 := 0x0ac58a63.
Lemma F_60a58 : fetch_word Ubsan.M.loaded_segments (0x60a58 : word) = Some W_60a58.
Proof. vm_refl. Qed.
Lemma D_60a58 : decode_any W_60a58 = Some (Branch BC_EQ 11 12 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a5c : bv 32 := 0x01f5d613.
Lemma F_60a5c : fetch_word Ubsan.M.loaded_segments (0x60a5c : word) = Some W_60a5c.
Proof. vm_refl. Qed.
Lemma D_60a5c : decode_any W_60a5c = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a60 : bv 32 := 0x00f67633.
Lemma F_60a60 : fetch_word Ubsan.M.loaded_segments (0x60a60 : word) = Some W_60a60.
Proof. vm_refl. Qed.
Lemma D_60a60 : decode_any W_60a60 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a64 : bv 32 := 0x00c5863b.
Lemma F_60a64 : fetch_word Ubsan.M.loaded_segments (0x60a64 : word) = Some W_60a64.
Proof. vm_refl. Qed.
Lemma D_60a64 : decode_any W_60a64 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a68 : bv 32 := 0x00c785b3.
Lemma F_60a68 : fetch_word Ubsan.M.loaded_segments (0x60a68 : word) = Some W_60a68.
Proof. vm_refl. Qed.
Lemma D_60a68 : decode_any W_60a68 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a6c : bv 32 := 0x0025859b.
Lemma F_60a6c : fetch_word Ubsan.M.loaded_segments (0x60a6c : word) = Some W_60a6c.
Proof. vm_refl. Qed.
Lemma D_60a6c : decode_any W_60a6c = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a70 : bv 32 := 0x160526af.
Lemma F_60a70 : fetch_word Ubsan.M.loaded_segments (0x60a70 : word) = Some W_60a70.
Proof. vm_refl. Qed.
Lemma D_60a70 : decode_any W_60a70 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a74 : bv 32 := 0x00c69663.
Lemma F_60a74 : fetch_word Ubsan.M.loaded_segments (0x60a74 : word) = Some W_60a74.
Proof. vm_refl. Qed.
Lemma D_60a74 : decode_any W_60a74 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a78 : bv 32 := 0x1eb5272f.
Lemma F_60a78 : fetch_word Ubsan.M.loaded_segments (0x60a78 : word) = Some W_60a78.
Proof. vm_refl. Qed.
Lemma D_60a78 : decode_any W_60a78 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a7c : bv 32 := 0xfe071ae3.
Lemma F_60a7c : fetch_word Ubsan.M.loaded_segments (0x60a7c : word) = Some W_60a7c.
Proof. vm_refl. Qed.
Lemma D_60a7c : decode_any W_60a7c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a80 : bv 32 := 0x0006859b.
Lemma F_60a80 : fetch_word Ubsan.M.loaded_segments (0x60a80 : word) = Some W_60a80.
Proof. vm_refl. Qed.
Lemma D_60a80 : decode_any W_60a80 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a84 : bv 32 := 0x08c58463.
Lemma F_60a84 : fetch_word Ubsan.M.loaded_segments (0x60a84 : word) = Some W_60a84.
Proof. vm_refl. Qed.
Lemma D_60a84 : decode_any W_60a84 = Some (Branch BC_EQ 11 12 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a88 : bv 32 := 0x01f5d613.
Lemma F_60a88 : fetch_word Ubsan.M.loaded_segments (0x60a88 : word) = Some W_60a88.
Proof. vm_refl. Qed.
Lemma D_60a88 : decode_any W_60a88 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a8c : bv 32 := 0x00f67633.
Lemma F_60a8c : fetch_word Ubsan.M.loaded_segments (0x60a8c : word) = Some W_60a8c.
Proof. vm_refl. Qed.
Lemma D_60a8c : decode_any W_60a8c = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a90 : bv 32 := 0x00c5863b.
Lemma F_60a90 : fetch_word Ubsan.M.loaded_segments (0x60a90 : word) = Some W_60a90.
Proof. vm_refl. Qed.
Lemma D_60a90 : decode_any W_60a90 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a94 : bv 32 := 0x00c785b3.
Lemma F_60a94 : fetch_word Ubsan.M.loaded_segments (0x60a94 : word) = Some W_60a94.
Proof. vm_refl. Qed.
Lemma D_60a94 : decode_any W_60a94 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a98 : bv 32 := 0x0025859b.
Lemma F_60a98 : fetch_word Ubsan.M.loaded_segments (0x60a98 : word) = Some W_60a98.
Proof. vm_refl. Qed.
Lemma D_60a98 : decode_any W_60a98 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60a9c : bv 32 := 0x160526af.
Lemma F_60a9c : fetch_word Ubsan.M.loaded_segments (0x60a9c : word) = Some W_60a9c.
Proof. vm_refl. Qed.
Lemma D_60a9c : decode_any W_60a9c = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60aa0 : bv 32 := 0x00c69663.
Lemma F_60aa0 : fetch_word Ubsan.M.loaded_segments (0x60aa0 : word) = Some W_60aa0.
Proof. vm_refl. Qed.
Lemma D_60aa0 : decode_any W_60aa0 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60aa4 : bv 32 := 0x1eb5272f.
Lemma F_60aa4 : fetch_word Ubsan.M.loaded_segments (0x60aa4 : word) = Some W_60aa4.
Proof. vm_refl. Qed.
Lemma D_60aa4 : decode_any W_60aa4 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60aa8 : bv 32 := 0xfe071ae3.
Lemma F_60aa8 : fetch_word Ubsan.M.loaded_segments (0x60aa8 : word) = Some W_60aa8.
Proof. vm_refl. Qed.
Lemma D_60aa8 : decode_any W_60aa8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60aac : bv 32 := 0x0006859b.
Lemma F_60aac : fetch_word Ubsan.M.loaded_segments (0x60aac : word) = Some W_60aac.
Proof. vm_refl. Qed.
Lemma D_60aac : decode_any W_60aac = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ab0 : bv 32 := 0x04c58e63.
Lemma F_60ab0 : fetch_word Ubsan.M.loaded_segments (0x60ab0 : word) = Some W_60ab0.
Proof. vm_refl. Qed.
Lemma D_60ab0 : decode_any W_60ab0 = Some (Branch BC_EQ 11 12 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ab4 : bv 32 := 0x01f5d613.
Lemma F_60ab4 : fetch_word Ubsan.M.loaded_segments (0x60ab4 : word) = Some W_60ab4.
Proof. vm_refl. Qed.
Lemma D_60ab4 : decode_any W_60ab4 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ab8 : bv 32 := 0x00f67633.
Lemma F_60ab8 : fetch_word Ubsan.M.loaded_segments (0x60ab8 : word) = Some W_60ab8.
Proof. vm_refl. Qed.
Lemma D_60ab8 : decode_any W_60ab8 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60abc : bv 32 := 0x00c5863b.
Lemma F_60abc : fetch_word Ubsan.M.loaded_segments (0x60abc : word) = Some W_60abc.
Proof. vm_refl. Qed.
Lemma D_60abc : decode_any W_60abc = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ac0 : bv 32 := 0x00c785b3.
Lemma F_60ac0 : fetch_word Ubsan.M.loaded_segments (0x60ac0 : word) = Some W_60ac0.
Proof. vm_refl. Qed.
Lemma D_60ac0 : decode_any W_60ac0 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ac4 : bv 32 := 0x0025859b.
Lemma F_60ac4 : fetch_word Ubsan.M.loaded_segments (0x60ac4 : word) = Some W_60ac4.
Proof. vm_refl. Qed.
Lemma D_60ac4 : decode_any W_60ac4 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ac8 : bv 32 := 0x160526af.
Lemma F_60ac8 : fetch_word Ubsan.M.loaded_segments (0x60ac8 : word) = Some W_60ac8.
Proof. vm_refl. Qed.
Lemma D_60ac8 : decode_any W_60ac8 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60acc : bv 32 := 0x00c69663.
Lemma F_60acc : fetch_word Ubsan.M.loaded_segments (0x60acc : word) = Some W_60acc.
Proof. vm_refl. Qed.
Lemma D_60acc : decode_any W_60acc = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ad0 : bv 32 := 0x1eb5272f.
Lemma F_60ad0 : fetch_word Ubsan.M.loaded_segments (0x60ad0 : word) = Some W_60ad0.
Proof. vm_refl. Qed.
Lemma D_60ad0 : decode_any W_60ad0 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ad4 : bv 32 := 0xfe071ae3.
Lemma F_60ad4 : fetch_word Ubsan.M.loaded_segments (0x60ad4 : word) = Some W_60ad4.
Proof. vm_refl. Qed.
Lemma D_60ad4 : decode_any W_60ad4 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ad8 : bv 32 := 0x0006859b.
Lemma F_60ad8 : fetch_word Ubsan.M.loaded_segments (0x60ad8 : word) = Some W_60ad8.
Proof. vm_refl. Qed.
Lemma D_60ad8 : decode_any W_60ad8 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60adc : bv 32 := 0x02c58863.
Lemma F_60adc : fetch_word Ubsan.M.loaded_segments (0x60adc : word) = Some W_60adc.
Proof. vm_refl. Qed.
Lemma D_60adc : decode_any W_60adc = Some (Branch BC_EQ 11 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ae0 : bv 32 := 0x01f5d613.
Lemma F_60ae0 : fetch_word Ubsan.M.loaded_segments (0x60ae0 : word) = Some W_60ae0.
Proof. vm_refl. Qed.
Lemma D_60ae0 : decode_any W_60ae0 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ae4 : bv 32 := 0x00f67633.
Lemma F_60ae4 : fetch_word Ubsan.M.loaded_segments (0x60ae4 : word) = Some W_60ae4.
Proof. vm_refl. Qed.
Lemma D_60ae4 : decode_any W_60ae4 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ae8 : bv 32 := 0x00c585bb.
Lemma F_60ae8 : fetch_word Ubsan.M.loaded_segments (0x60ae8 : word) = Some W_60ae8.
Proof. vm_refl. Qed.
Lemma D_60ae8 : decode_any W_60ae8 = Some (Op32 ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60aec : bv 32 := 0x00b78633.
Lemma F_60aec : fetch_word Ubsan.M.loaded_segments (0x60aec : word) = Some W_60aec.
Proof. vm_refl. Qed.
Lemma D_60aec : decode_any W_60aec = Some (Op ALU_ADD 12 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60af0 : bv 32 := 0x0026061b.
Lemma F_60af0 : fetch_word Ubsan.M.loaded_segments (0x60af0 : word) = Some W_60af0.
Proof. vm_refl. Qed.
Lemma D_60af0 : decode_any W_60af0 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60af4 : bv 32 := 0x160526af.
Lemma F_60af4 : fetch_word Ubsan.M.loaded_segments (0x60af4 : word) = Some W_60af4.
Proof. vm_refl. Qed.
Lemma D_60af4 : decode_any W_60af4 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60af8 : bv 32 := 0x00b69663.
Lemma F_60af8 : fetch_word Ubsan.M.loaded_segments (0x60af8 : word) = Some W_60af8.
Proof. vm_refl. Qed.
Lemma D_60af8 : decode_any W_60af8 = Some (Branch BC_NE 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60afc : bv 32 := 0x1ec5272f.
Lemma F_60afc : fetch_word Ubsan.M.loaded_segments (0x60afc : word) = Some W_60afc.
Proof. vm_refl. Qed.
Lemma D_60afc : decode_any W_60afc = Some (Sc AW true true 14 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b00 : bv 32 := 0xfe071ae3.
Lemma F_60b00 : fetch_word Ubsan.M.loaded_segments (0x60b00 : word) = Some W_60b00.
Proof. vm_refl. Qed.
Lemma D_60b00 : decode_any W_60b00 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b04 : bv 32 := 0x0006869b.
Lemma F_60b04 : fetch_word Ubsan.M.loaded_segments (0x60b04 : word) = Some W_60b04.
Proof. vm_refl. Qed.
Lemma D_60b04 : decode_any W_60b04 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b08 : bv 32 := 0x00b69463.
Lemma F_60b08 : fetch_word Ubsan.M.loaded_segments (0x60b08 : word) = Some W_60b08.
Proof. vm_refl. Qed.
Lemma D_60b08 : decode_any W_60b08 = Some (Branch BC_NE 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b0c : bv 32 := 0x00008067.
Lemma F_60b0c : fetch_word Ubsan.M.loaded_segments (0x60b0c : word) = Some W_60b0c.
Proof. vm_refl. Qed.
Lemma D_60b0c : decode_any W_60b0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b10 : bv 32 := 0x00052583.
Lemma F_60b10 : fetch_word Ubsan.M.loaded_segments (0x60b10 : word) = Some W_60b10.
Proof. vm_refl. Qed.
Lemma D_60b10 : decode_any W_60b10 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b14 : bv 32 := 0x0015881b.
Lemma F_60b14 : fetch_word Ubsan.M.loaded_segments (0x60b14 : word) = Some W_60b14.
Proof. vm_refl. Qed.
Lemma D_60b14 : decode_any W_60b14 = Some (OpImm32 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b18 : bv 32 := 0x1605262f.
Lemma F_60b18 : fetch_word Ubsan.M.loaded_segments (0x60b18 : word) = Some W_60b18.
Proof. vm_refl. Qed.
Lemma D_60b18 : decode_any W_60b18 = Some (Lr AW true true 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b1c : bv 32 := 0x00b61663.
Lemma F_60b1c : fetch_word Ubsan.M.loaded_segments (0x60b1c : word) = Some W_60b1c.
Proof. vm_refl. Qed.
Lemma D_60b1c : decode_any W_60b1c = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b20 : bv 32 := 0x1f0526af.
Lemma F_60b20 : fetch_word Ubsan.M.loaded_segments (0x60b20 : word) = Some W_60b20.
Proof. vm_refl. Qed.
Lemma D_60b20 : decode_any W_60b20 = Some (Sc AW true true 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b24 : bv 32 := 0xfe069ae3.
Lemma F_60b24 : fetch_word Ubsan.M.loaded_segments (0x60b24 : word) = Some W_60b24.
Proof. vm_refl. Qed.
Lemma D_60b24 : decode_any W_60b24 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b28 : bv 32 := 0x0006061b.
Lemma F_60b28 : fetch_word Ubsan.M.loaded_segments (0x60b28 : word) = Some W_60b28.
Proof. vm_refl. Qed.
Lemma D_60b28 : decode_any W_60b28 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b2c : bv 32 := 0xfeb612e3.
Lemma F_60b2c : fetch_word Ubsan.M.loaded_segments (0x60b2c : word) = Some W_60b2c.
Proof. vm_refl. Qed.
Lemma D_60b2c : decode_any W_60b2c = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b30 : bv 32 := 0xfda00293.
Lemma F_60b30 : fetch_word Ubsan.M.loaded_segments (0x60b30 : word) = Some W_60b30.
Proof. vm_refl. Qed.
Lemma D_60b30 : decode_any W_60b30 = Some (OpImm ALU_ADD 5 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b34 : bv 32 := 0x80000337.
Lemma F_60b34 : fetch_word Ubsan.M.loaded_segments (0x60b34 : word) = Some W_60b34.
Proof. vm_refl. Qed.
Lemma D_60b34 : decode_any W_60b34 = Some (Lui 6 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b38 : bv 32 := 0x02c0006f.
Lemma F_60b38 : fetch_word Ubsan.M.loaded_segments (0x60b38 : word) = Some W_60b38.
Proof. vm_refl. Qed.
Lemma D_60b38 : decode_any W_60b38 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b3c : bv 32 := 0x00f8083b.
Lemma F_60b3c : fetch_word Ubsan.M.loaded_segments (0x60b3c : word) = Some W_60b3c.
Proof. vm_refl. Qed.
Lemma D_60b3c : decode_any W_60b3c = Some (Op32 ALU_ADD 16 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b40 : bv 32 := 0x00070513.
Lemma F_60b40 : fetch_word Ubsan.M.loaded_segments (0x60b40 : word) = Some W_60b40.
Proof. vm_refl. Qed.
Lemma D_60b40 : decode_any W_60b40 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b44 : bv 32 := 0x006865b3.
Lemma F_60b44 : fetch_word Ubsan.M.loaded_segments (0x60b44 : word) = Some W_60b44.
Proof. vm_refl. Qed.
Lemma D_60b44 : decode_any W_60b44 = Some (Op ALU_OR 11 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b48 : bv 32 := 0x0008061b.
Lemma F_60b48 : fetch_word Ubsan.M.loaded_segments (0x60b48 : word) = Some W_60b48.
Proof. vm_refl. Qed.
Lemma D_60b48 : decode_any W_60b48 = Some (OpImm32 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b4c : bv 32 := 0x1605282f.
Lemma F_60b4c : fetch_word Ubsan.M.loaded_segments (0x60b4c : word) = Some W_60b4c.
Proof. vm_refl. Qed.
Lemma D_60b4c : decode_any W_60b4c = Some (Lr AW true true 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b50 : bv 32 := 0x00c81663.
Lemma F_60b50 : fetch_word Ubsan.M.loaded_segments (0x60b50 : word) = Some W_60b50.
Proof. vm_refl. Qed.
Lemma D_60b50 : decode_any W_60b50 = Some (Branch BC_NE 16 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b54 : bv 32 := 0x1eb526af.
Lemma F_60b54 : fetch_word Ubsan.M.loaded_segments (0x60b54 : word) = Some W_60b54.
Proof. vm_refl. Qed.
Lemma D_60b54 : decode_any W_60b54 = Some (Sc AW true true 13 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b58 : bv 32 := 0xfe069ae3.
Lemma F_60b58 : fetch_word Ubsan.M.loaded_segments (0x60b58 : word) = Some W_60b58.
Proof. vm_refl. Qed.
Lemma D_60b58 : decode_any W_60b58 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b5c : bv 32 := 0x0008059b.
Lemma F_60b5c : fetch_word Ubsan.M.loaded_segments (0x60b5c : word) = Some W_60b5c.
Proof. vm_refl. Qed.
Lemma D_60b5c : decode_any W_60b5c = Some (OpImm32 11 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b60 : bv 32 := 0xfac586e3.
Lemma F_60b60 : fetch_word Ubsan.M.loaded_segments (0x60b60 : word) = Some W_60b60.
Proof. vm_refl. Qed.
Lemma D_60b60 : decode_any W_60b60 = Some (Branch BC_EQ 11 12 8108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b64 : bv 32 := 0x0008061b.
Lemma F_60b64 : fetch_word Ubsan.M.loaded_segments (0x60b64 : word) = Some W_60b64.
Proof. vm_refl. Qed.
Lemma D_60b64 : decode_any W_60b64 = Some (OpImm32 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b68 : bv 32 := 0xfc065ee3.
Lemma F_60b68 : fetch_word Ubsan.M.loaded_segments (0x60b68 : word) = Some W_60b68.
Proof. vm_refl. Qed.
Lemma D_60b68 : decode_any W_60b68 = Some (Branch BC_GE 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b6c : bv 32 := 0x06200893.
Lemma F_60b6c : fetch_word Ubsan.M.loaded_segments (0x60b6c : word) = Some W_60b6c.
Proof. vm_refl. Qed.
Lemma D_60b6c : decode_any W_60b6c = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b70 : bv 32 := 0x08000593.
Lemma F_60b70 : fetch_word Ubsan.M.loaded_segments (0x60b70 : word) = Some W_60b70.
Proof. vm_refl. Qed.
Lemma D_60b70 : decode_any W_60b70 = Some (OpImm ALU_ADD 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b74 : bv 32 := 0x00050713.
Lemma F_60b74 : fetch_word Ubsan.M.loaded_segments (0x60b74 : word) = Some W_60b74.
Proof. vm_refl. Qed.
Lemma D_60b74 : decode_any W_60b74 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b78 : bv 32 := 0x00000693.
Lemma F_60b78 : fetch_word Ubsan.M.loaded_segments (0x60b78 : word) = Some W_60b78.
Proof. vm_refl. Qed.
Lemma D_60b78 : decode_any W_60b78 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b7c : bv 32 := 0x00000073.
Lemma F_60b7c : fetch_word Ubsan.M.loaded_segments (0x60b7c : word) = Some W_60b7c.
Proof. vm_refl. Qed.
Lemma D_60b7c : decode_any W_60b7c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_60b7c : is_ecall W_60b7c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_60b80 : bv 32 := 0xfa551ee3.
Lemma F_60b80 : fetch_word Ubsan.M.loaded_segments (0x60b80 : word) = Some W_60b80.
Proof. vm_refl. Qed.
Lemma D_60b80 : decode_any W_60b80 = Some (Branch BC_NE 10 5 8124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b84 : bv 32 := 0x06200893.
Lemma F_60b84 : fetch_word Ubsan.M.loaded_segments (0x60b84 : word) = Some W_60b84.
Proof. vm_refl. Qed.
Lemma D_60b84 : decode_any W_60b84 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b88 : bv 32 := 0x00070513.
Lemma F_60b88 : fetch_word Ubsan.M.loaded_segments (0x60b88 : word) = Some W_60b88.
Proof. vm_refl. Qed.
Lemma D_60b88 : decode_any W_60b88 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b8c : bv 32 := 0x00000593.
Lemma F_60b8c : fetch_word Ubsan.M.loaded_segments (0x60b8c : word) = Some W_60b8c.
Proof. vm_refl. Qed.
Lemma D_60b8c : decode_any W_60b8c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b90 : bv 32 := 0x00000693.
Lemma F_60b90 : fetch_word Ubsan.M.loaded_segments (0x60b90 : word) = Some W_60b90.
Proof. vm_refl. Qed.
Lemma D_60b90 : decode_any W_60b90 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b94 : bv 32 := 0x00000073.
Lemma F_60b94 : fetch_word Ubsan.M.loaded_segments (0x60b94 : word) = Some W_60b94.
Proof. vm_refl. Qed.
Lemma D_60b94 : decode_any W_60b94 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_60b94 : is_ecall W_60b94 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_60b98 : bv 32 := 0xfa5ff06f.
Lemma F_60b98 : fetch_word Ubsan.M.loaded_segments (0x60b98 : word) = Some W_60b98.
Proof. vm_refl. Qed.
Lemma D_60b98 : decode_any W_60b98 = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60b9c : bv 32 := 0x00052583.
Lemma F_60b9c : fetch_word Ubsan.M.loaded_segments (0x60b9c : word) = Some W_60b9c.
Proof. vm_refl. Qed.
Lemma D_60b9c : decode_any W_60b9c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ba0 : bv 32 := 0x0005c463.
Lemma F_60ba0 : fetch_word Ubsan.M.loaded_segments (0x60ba0 : word) = Some W_60ba0.
Proof. vm_refl. Qed.
Lemma D_60ba0 : decode_any W_60ba0 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ba4 : bv 32 := 0x00008067.
Lemma F_60ba4 : fetch_word Ubsan.M.loaded_segments (0x60ba4 : word) = Some W_60ba4.
Proof. vm_refl. Qed.
Lemma D_60ba4 : decode_any W_60ba4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ba8 : bv 32 := 0x80000637.
Lemma F_60ba8 : fetch_word Ubsan.M.loaded_segments (0x60ba8 : word) = Some W_60ba8.
Proof. vm_refl. Qed.
Lemma D_60ba8 : decode_any W_60ba8 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bac : bv 32 := 0xfff60613.
Lemma F_60bac : fetch_word Ubsan.M.loaded_segments (0x60bac : word) = Some W_60bac.
Proof. vm_refl. Qed.
Lemma D_60bac : decode_any W_60bac = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bb0 : bv 32 := 0x00052583.
Lemma F_60bb0 : fetch_word Ubsan.M.loaded_segments (0x60bb0 : word) = Some W_60bb0.
Proof. vm_refl. Qed.
Lemma D_60bb0 : decode_any W_60bb0 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bb4 : bv 32 := 0x00c586bb.
Lemma F_60bb4 : fetch_word Ubsan.M.loaded_segments (0x60bb4 : word) = Some W_60bb4.
Proof. vm_refl. Qed.
Lemma D_60bb4 : decode_any W_60bb4 = Some (Op32 ALU_ADD 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bb8 : bv 32 := 0x1605272f.
Lemma F_60bb8 : fetch_word Ubsan.M.loaded_segments (0x60bb8 : word) = Some W_60bb8.
Proof. vm_refl. Qed.
Lemma D_60bb8 : decode_any W_60bb8 = Some (Lr AW true true 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bbc : bv 32 := 0x00b71663.
Lemma F_60bbc : fetch_word Ubsan.M.loaded_segments (0x60bbc : word) = Some W_60bbc.
Proof. vm_refl. Qed.
Lemma D_60bbc : decode_any W_60bbc = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bc0 : bv 32 := 0x1ed527af.
Lemma F_60bc0 : fetch_word Ubsan.M.loaded_segments (0x60bc0 : word) = Some W_60bc0.
Proof. vm_refl. Qed.
Lemma D_60bc0 : decode_any W_60bc0 = Some (Sc AW true true 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bc4 : bv 32 := 0xfe079ae3.
Lemma F_60bc4 : fetch_word Ubsan.M.loaded_segments (0x60bc4 : word) = Some W_60bc4.
Proof. vm_refl. Qed.
Lemma D_60bc4 : decode_any W_60bc4 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bc8 : bv 32 := 0x0007071b.
Lemma F_60bc8 : fetch_word Ubsan.M.loaded_segments (0x60bc8 : word) = Some W_60bc8.
Proof. vm_refl. Qed.
Lemma D_60bc8 : decode_any W_60bc8 = Some (OpImm32 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bcc : bv 32 := 0xfeb712e3.
Lemma F_60bcc : fetch_word Ubsan.M.loaded_segments (0x60bcc : word) = Some W_60bcc.
Proof. vm_refl. Qed.
Lemma D_60bcc : decode_any W_60bcc = Some (Branch BC_NE 14 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bd0 : bv 32 := 0x80000637.
Lemma F_60bd0 : fetch_word Ubsan.M.loaded_segments (0x60bd0 : word) = Some W_60bd0.
Proof. vm_refl. Qed.
Lemma D_60bd0 : decode_any W_60bd0 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bd4 : bv 32 := 0x0016061b.
Lemma F_60bd4 : fetch_word Ubsan.M.loaded_segments (0x60bd4 : word) = Some W_60bd4.
Proof. vm_refl. Qed.
Lemma D_60bd4 : decode_any W_60bd4 = Some (OpImm32 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bd8 : bv 32 := 0xfcc586e3.
Lemma F_60bd8 : fetch_word Ubsan.M.loaded_segments (0x60bd8 : word) = Some W_60bd8.
Proof. vm_refl. Qed.
Lemma D_60bd8 : decode_any W_60bd8 = Some (Branch BC_EQ 11 12 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bdc : bv 32 := 0x06200893.
Lemma F_60bdc : fetch_word Ubsan.M.loaded_segments (0x60bdc : word) = Some W_60bdc.
Proof. vm_refl. Qed.
Lemma D_60bdc : decode_any W_60bdc = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60be0 : bv 32 := 0x08100593.
Lemma F_60be0 : fetch_word Ubsan.M.loaded_segments (0x60be0 : word) = Some W_60be0.
Proof. vm_refl. Qed.
Lemma D_60be0 : decode_any W_60be0 = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60be4 : bv 32 := 0x00100613.
Lemma F_60be4 : fetch_word Ubsan.M.loaded_segments (0x60be4 : word) = Some W_60be4.
Proof. vm_refl. Qed.
Lemma D_60be4 : decode_any W_60be4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60be8 : bv 32 := 0xfda00713.
Lemma F_60be8 : fetch_word Ubsan.M.loaded_segments (0x60be8 : word) = Some W_60be8.
Proof. vm_refl. Qed.
Lemma D_60be8 : decode_any W_60be8 = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bec : bv 32 := 0x00050693.
Lemma F_60bec : fetch_word Ubsan.M.loaded_segments (0x60bec : word) = Some W_60bec.
Proof. vm_refl. Qed.
Lemma D_60bec : decode_any W_60bec = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bf0 : bv 32 := 0x00000073.
Lemma F_60bf0 : fetch_word Ubsan.M.loaded_segments (0x60bf0 : word) = Some W_60bf0.
Proof. vm_refl. Qed.
Lemma D_60bf0 : decode_any W_60bf0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_60bf0 : is_ecall W_60bf0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_60bf4 : bv 32 := 0xfae518e3.
Lemma F_60bf4 : fetch_word Ubsan.M.loaded_segments (0x60bf4 : word) = Some W_60bf4.
Proof. vm_refl. Qed.
Lemma D_60bf4 : decode_any W_60bf4 = Some (Branch BC_NE 10 14 8112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bf8 : bv 32 := 0x06200893.
Lemma F_60bf8 : fetch_word Ubsan.M.loaded_segments (0x60bf8 : word) = Some W_60bf8.
Proof. vm_refl. Qed.
Lemma D_60bf8 : decode_any W_60bf8 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60bfc : bv 32 := 0x00100593.
Lemma F_60bfc : fetch_word Ubsan.M.loaded_segments (0x60bfc : word) = Some W_60bfc.
Proof. vm_refl. Qed.
Lemma D_60bfc : decode_any W_60bfc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c00 : bv 32 := 0x00100613.
Lemma F_60c00 : fetch_word Ubsan.M.loaded_segments (0x60c00 : word) = Some W_60c00.
Proof. vm_refl. Qed.
Lemma D_60c00 : decode_any W_60c00 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c04 : bv 32 := 0x00068513.
Lemma F_60c04 : fetch_word Ubsan.M.loaded_segments (0x60c04 : word) = Some W_60c04.
Proof. vm_refl. Qed.
Lemma D_60c04 : decode_any W_60c04 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c08 : bv 32 := 0x00000073.
Lemma F_60c08 : fetch_word Ubsan.M.loaded_segments (0x60c08 : word) = Some W_60c08.
Proof. vm_refl. Qed.
Lemma D_60c08 : decode_any W_60c08 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_60c08 : is_ecall W_60c08 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_60c0c : bv 32 := 0x00008067.
Lemma F_60c0c : fetch_word Ubsan.M.loaded_segments (0x60c0c : word) = Some W_60c0c.
Proof. vm_refl. Qed.
Lemma D_60c0c : decode_any W_60c0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c10 : bv 32 := 0x00050893.
Lemma F_60c10 : fetch_word Ubsan.M.loaded_segments (0x60c10 : word) = Some W_60c10.
Proof. vm_refl. Qed.
Lemma D_60c10 : decode_any W_60c10 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c14 : bv 32 := 0x00058513.
Lemma F_60c14 : fetch_word Ubsan.M.loaded_segments (0x60c14 : word) = Some W_60c14.
Proof. vm_refl. Qed.
Lemma D_60c14 : decode_any W_60c14 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c18 : bv 32 := 0x00060593.
Lemma F_60c18 : fetch_word Ubsan.M.loaded_segments (0x60c18 : word) = Some W_60c18.
Proof. vm_refl. Qed.
Lemma D_60c18 : decode_any W_60c18 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c1c : bv 32 := 0x00068613.
Lemma F_60c1c : fetch_word Ubsan.M.loaded_segments (0x60c1c : word) = Some W_60c1c.
Proof. vm_refl. Qed.
Lemma D_60c1c : decode_any W_60c1c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c20 : bv 32 := 0x00070693.
Lemma F_60c20 : fetch_word Ubsan.M.loaded_segments (0x60c20 : word) = Some W_60c20.
Proof. vm_refl. Qed.
Lemma D_60c20 : decode_any W_60c20 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c24 : bv 32 := 0x00078713.
Lemma F_60c24 : fetch_word Ubsan.M.loaded_segments (0x60c24 : word) = Some W_60c24.
Proof. vm_refl. Qed.
Lemma D_60c24 : decode_any W_60c24 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c28 : bv 32 := 0x00080793.
Lemma F_60c28 : fetch_word Ubsan.M.loaded_segments (0x60c28 : word) = Some W_60c28.
Proof. vm_refl. Qed.
Lemma D_60c28 : decode_any W_60c28 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c2c : bv 32 := 0x00000073.
Lemma F_60c2c : fetch_word Ubsan.M.loaded_segments (0x60c2c : word) = Some W_60c2c.
Proof. vm_refl. Qed.
Lemma D_60c2c : decode_any W_60c2c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_60c2c : is_ecall W_60c2c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_60c30 : bv 32 := 0x00008067.
Lemma F_60c30 : fetch_word Ubsan.M.loaded_segments (0x60c30 : word) = Some W_60c30.
Proof. vm_refl. Qed.
Lemma D_60c30 : decode_any W_60c30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c34 : bv 32 := 0xfddff06f.
Lemma F_60c34 : fetch_word Ubsan.M.loaded_segments (0x60c34 : word) = Some W_60c34.
Proof. vm_refl. Qed.
Lemma D_60c34 : decode_any W_60c34 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.
