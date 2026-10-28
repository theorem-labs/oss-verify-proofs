(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_3a58c : bv 32 := 0xf6010113.
Lemma F_3a58c : fetch_word Ubsan.M.loaded_segments (0x3a58c : word) = Some W_3a58c.
Proof. vm_refl. Qed.
Lemma D_3a58c : decode_any W_3a58c = Some (OpImm ALU_ADD 2 2 3936, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a590 : bv 32 := 0x08113c23.
Lemma F_3a590 : fetch_word Ubsan.M.loaded_segments (0x3a590 : word) = Some W_3a590.
Proof. vm_refl. Qed.
Lemma D_3a590 : decode_any W_3a590 = Some (Store SZ8 2 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a594 : bv 32 := 0x08813823.
Lemma F_3a594 : fetch_word Ubsan.M.loaded_segments (0x3a594 : word) = Some W_3a594.
Proof. vm_refl. Qed.
Lemma D_3a594 : decode_any W_3a594 = Some (Store SZ8 2 8 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a598 : bv 32 := 0x08913423.
Lemma F_3a598 : fetch_word Ubsan.M.loaded_segments (0x3a598 : word) = Some W_3a598.
Proof. vm_refl. Qed.
Lemma D_3a598 : decode_any W_3a598 = Some (Store SZ8 2 9 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a59c : bv 32 := 0x09213023.
Lemma F_3a59c : fetch_word Ubsan.M.loaded_segments (0x3a59c : word) = Some W_3a59c.
Proof. vm_refl. Qed.
Lemma D_3a59c : decode_any W_3a59c = Some (Store SZ8 2 18 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5a0 : bv 32 := 0x07313c23.
Lemma F_3a5a0 : fetch_word Ubsan.M.loaded_segments (0x3a5a0 : word) = Some W_3a5a0.
Proof. vm_refl. Qed.
Lemma D_3a5a0 : decode_any W_3a5a0 = Some (Store SZ8 2 19 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5a4 : bv 32 := 0x07413823.
Lemma F_3a5a4 : fetch_word Ubsan.M.loaded_segments (0x3a5a4 : word) = Some W_3a5a4.
Proof. vm_refl. Qed.
Lemma D_3a5a4 : decode_any W_3a5a4 = Some (Store SZ8 2 20 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5a8 : bv 32 := 0x07513423.
Lemma F_3a5a8 : fetch_word Ubsan.M.loaded_segments (0x3a5a8 : word) = Some W_3a5a8.
Proof. vm_refl. Qed.
Lemma D_3a5a8 : decode_any W_3a5a8 = Some (Store SZ8 2 21 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5ac : bv 32 := 0x07613023.
Lemma F_3a5ac : fetch_word Ubsan.M.loaded_segments (0x3a5ac : word) = Some W_3a5ac.
Proof. vm_refl. Qed.
Lemma D_3a5ac : decode_any W_3a5ac = Some (Store SZ8 2 22 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5b0 : bv 32 := 0x05713c23.
Lemma F_3a5b0 : fetch_word Ubsan.M.loaded_segments (0x3a5b0 : word) = Some W_3a5b0.
Proof. vm_refl. Qed.
Lemma D_3a5b0 : decode_any W_3a5b0 = Some (Store SZ8 2 23 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5b4 : bv 32 := 0x05813823.
Lemma F_3a5b4 : fetch_word Ubsan.M.loaded_segments (0x3a5b4 : word) = Some W_3a5b4.
Proof. vm_refl. Qed.
Lemma D_3a5b4 : decode_any W_3a5b4 = Some (Store SZ8 2 24 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5b8 : bv 32 := 0x05913423.
Lemma F_3a5b8 : fetch_word Ubsan.M.loaded_segments (0x3a5b8 : word) = Some W_3a5b8.
Proof. vm_refl. Qed.
Lemma D_3a5b8 : decode_any W_3a5b8 = Some (Store SZ8 2 25 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5bc : bv 32 := 0x05a13023.
Lemma F_3a5bc : fetch_word Ubsan.M.loaded_segments (0x3a5bc : word) = Some W_3a5bc.
Proof. vm_refl. Qed.
Lemma D_3a5bc : decode_any W_3a5bc = Some (Store SZ8 2 26 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5c0 : bv 32 := 0x03b13c23.
Lemma F_3a5c0 : fetch_word Ubsan.M.loaded_segments (0x3a5c0 : word) = Some W_3a5c0.
Proof. vm_refl. Qed.
Lemma D_3a5c0 : decode_any W_3a5c0 = Some (Store SZ8 2 27 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5c4 : bv 32 := 0x00757593.
Lemma F_3a5c4 : fetch_word Ubsan.M.loaded_segments (0x3a5c4 : word) = Some W_3a5c4.
Proof. vm_refl. Qed.
Lemma D_3a5c4 : decode_any W_3a5c4 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5c8 : bv 32 := 0x48059863.
Lemma F_3a5c8 : fetch_word Ubsan.M.loaded_segments (0x3a5c8 : word) = Some W_3a5c8.
Proof. vm_refl. Qed.
Lemma D_3a5c8 : decode_any W_3a5c8 = Some (Branch BC_NE 11 0 1168, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5cc : bv 32 := 0x00053a83.
Lemma F_3a5cc : fetch_word Ubsan.M.loaded_segments (0x3a5cc : word) = Some W_3a5cc.
Proof. vm_refl. Qed.
Lemma D_3a5cc : decode_any W_3a5cc = Some (Load SZ8 true 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5d0 : bv 32 := 0x01052b03.
Lemma F_3a5d0 : fetch_word Ubsan.M.loaded_segments (0x3a5d0 : word) = Some W_3a5d0.
Proof. vm_refl. Qed.
Lemma D_3a5d0 : decode_any W_3a5d0 = Some (Load SZ4 true 22 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5d4 : bv 32 := 0x03852403.
Lemma F_3a5d4 : fetch_word Ubsan.M.loaded_segments (0x3a5d4 : word) = Some W_3a5d4.
Proof. vm_refl. Qed.
Lemma D_3a5d4 : decode_any W_3a5d4 = Some (Load SZ4 true 8 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5d8 : bv 32 := 0x04853b83.
Lemma F_3a5d8 : fetch_word Ubsan.M.loaded_segments (0x3a5d8 : word) = Some W_3a5d8.
Proof. vm_refl. Qed.
Lemma D_3a5d8 : decode_any W_3a5d8 = Some (Load SZ8 true 23 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5dc : bv 32 := 0x05053c03.
Lemma F_3a5dc : fetch_word Ubsan.M.loaded_segments (0x3a5dc : word) = Some W_3a5dc.
Proof. vm_refl. Qed.
Lemma D_3a5dc : decode_any W_3a5dc = Some (Load SZ8 true 24 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5e0 : bv 32 := 0x05853583.
Lemma F_3a5e0 : fetch_word Ubsan.M.loaded_segments (0x3a5e0 : word) = Some W_3a5e0.
Proof. vm_refl. Qed.
Lemma D_3a5e0 : decode_any W_3a5e0 = Some (Load SZ8 true 11 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5e4 : bv 32 := 0x06053c83.
Lemma F_3a5e4 : fetch_word Ubsan.M.loaded_segments (0x3a5e4 : word) = Some W_3a5e4.
Proof. vm_refl. Qed.
Lemma D_3a5e4 : decode_any W_3a5e4 = Some (Load SZ8 true 25 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5e8 : bv 32 := 0x00058513.
Lemma F_3a5e8 : fetch_word Ubsan.M.loaded_segments (0x3a5e8 : word) = Some W_3a5e8.
Proof. vm_refl. Qed.
Lemma D_3a5e8 : decode_any W_3a5e8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5ec : bv 32 := 0xa20de0ef.
Lemma F_3a5ec : fetch_word Ubsan.M.loaded_segments (0x3a5ec : word) = Some W_3a5ec.
Proof. vm_refl. Qed.
Lemma D_3a5ec : decode_any W_3a5ec = Some (Jal 1 1958432, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5f0 : bv 32 := 0x38851c63.
Lemma F_3a5f0 : fetch_word Ubsan.M.loaded_segments (0x3a5f0 : word) = Some W_3a5f0.
Proof. vm_refl. Qed.
Lemma D_3a5f0 : decode_any W_3a5f0 = Some (Branch BC_NE 10 8 920, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5f4 : bv 32 := 0x000a8513.
Lemma F_3a5f4 : fetch_word Ubsan.M.loaded_segments (0x3a5f4 : word) = Some W_3a5f4.
Proof. vm_refl. Qed.
Lemma D_3a5f4 : decode_any W_3a5f4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5f8 : bv 32 := 0xb14df0ef.
Lemma F_3a5f8 : fetch_word Ubsan.M.loaded_segments (0x3a5f8 : word) = Some W_3a5f8.
Proof. vm_refl. Qed.
Lemma D_3a5f8 : decode_any W_3a5f8 = Some (Jal 1 1962772, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a5fc : bv 32 := 0x3a050a63.
Lemma F_3a5fc : fetch_word Ubsan.M.loaded_segments (0x3a5fc : word) = Some W_3a5fc.
Proof. vm_refl. Qed.
Lemma D_3a5fc : decode_any W_3a5fc = Some (Branch BC_EQ 10 0 948, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a600 : bv 32 := 0x00050413.
Lemma F_3a600 : fetch_word Ubsan.M.loaded_segments (0x3a600 : word) = Some W_3a600.
Proof. vm_refl. Qed.
Lemma D_3a600 : decode_any W_3a600 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a604 : bv 32 := 0x000a8513.
Lemma F_3a604 : fetch_word Ubsan.M.loaded_segments (0x3a604 : word) = Some W_3a604.
Proof. vm_refl. Qed.
Lemma D_3a604 : decode_any W_3a604 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a608 : bv 32 := 0xb9ce00ef.
Lemma F_3a608 : fetch_word Ubsan.M.loaded_segments (0x3a608 : word) = Some W_3a608.
Proof. vm_refl. Qed.
Lemma D_3a608 : decode_any W_3a608 = Some (Jal 1 1967004, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a60c : bv 32 := 0x00050493.
Lemma F_3a60c : fetch_word Ubsan.M.loaded_segments (0x3a60c : word) = Some W_3a60c.
Proof. vm_refl. Qed.
Lemma D_3a60c : decode_any W_3a60c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a610 : bv 32 := 0x000a8513.
Lemma F_3a610 : fetch_word Ubsan.M.loaded_segments (0x3a610 : word) = Some W_3a610.
Proof. vm_refl. Qed.
Lemma D_3a610 : decode_any W_3a610 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a614 : bv 32 := 0x9ccdf0ef.
Lemma F_3a614 : fetch_word Ubsan.M.loaded_segments (0x3a614 : word) = Some W_3a614.
Proof. vm_refl. Qed.
Lemma D_3a614 : decode_any W_3a614 = Some (Jal 1 1962444, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a618 : bv 32 := 0x00050913.
Lemma F_3a618 : fetch_word Ubsan.M.loaded_segments (0x3a618 : word) = Some W_3a618.
Proof. vm_refl. Qed.
Lemma D_3a618 : decode_any W_3a618 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a61c : bv 32 := 0x00040513.
Lemma F_3a61c : fetch_word Ubsan.M.loaded_segments (0x3a61c : word) = Some W_3a61c.
Proof. vm_refl. Qed.
Lemma D_3a61c : decode_any W_3a61c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a620 : bv 32 := 0xb84e00ef.
Lemma F_3a620 : fetch_word Ubsan.M.loaded_segments (0x3a620 : word) = Some W_3a620.
Proof. vm_refl. Qed.
Lemma D_3a620 : decode_any W_3a620 = Some (Jal 1 1966980, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a624 : bv 32 := 0x00050993.
Lemma F_3a624 : fetch_word Ubsan.M.loaded_segments (0x3a624 : word) = Some W_3a624.
Proof. vm_refl. Qed.
Lemma D_3a624 : decode_any W_3a624 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a628 : bv 32 := 0x00040513.
Lemma F_3a628 : fetch_word Ubsan.M.loaded_segments (0x3a628 : word) = Some W_3a628.
Proof. vm_refl. Qed.
Lemma D_3a628 : decode_any W_3a628 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a62c : bv 32 := 0x9b4df0ef.
Lemma F_3a62c : fetch_word Ubsan.M.loaded_segments (0x3a62c : word) = Some W_3a62c.
Proof. vm_refl. Qed.
Lemma D_3a62c : decode_any W_3a62c = Some (Jal 1 1962420, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a630 : bv 32 := 0x00a13823.
Lemma F_3a630 : fetch_word Ubsan.M.loaded_segments (0x3a630 : word) = Some W_3a630.
Proof. vm_refl. Qed.
Lemma D_3a630 : decode_any W_3a630 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a634 : bv 32 := 0x03410593.
Lemma F_3a634 : fetch_word Ubsan.M.loaded_segments (0x3a634 : word) = Some W_3a634.
Proof. vm_refl. Qed.
Lemma D_3a634 : decode_any W_3a634 = Some (OpImm ALU_ADD 11 2 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a638 : bv 32 := 0x03010613.
Lemma F_3a638 : fetch_word Ubsan.M.loaded_segments (0x3a638 : word) = Some W_3a638.
Proof. vm_refl. Qed.
Lemma D_3a638 : decode_any W_3a638 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a63c : bv 32 := 0x000a8513.
Lemma F_3a63c : fetch_word Ubsan.M.loaded_segments (0x3a63c : word) = Some W_3a63c.
Proof. vm_refl. Qed.
Lemma D_3a63c : decode_any W_3a63c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a640 : bv 32 := 0x00000693.
Lemma F_3a640 : fetch_word Ubsan.M.loaded_segments (0x3a640 : word) = Some W_3a640.
Proof. vm_refl. Qed.
Lemma D_3a640 : decode_any W_3a640 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a644 : bv 32 := 0xcf4df0ef.
Lemma F_3a644 : fetch_word Ubsan.M.loaded_segments (0x3a644 : word) = Some W_3a644.
Proof. vm_refl. Qed.
Lemma D_3a644 : decode_any W_3a644 = Some (Jal 1 1963252, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a648 : bv 32 := 0x03012503.
Lemma F_3a648 : fetch_word Ubsan.M.loaded_segments (0x3a648 : word) = Some W_3a648.
Proof. vm_refl. Qed.
Lemma D_3a648 : decode_any W_3a648 = Some (Load SZ4 true 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a64c : bv 32 := 0x3ca05663.
Lemma F_3a64c : fetch_word Ubsan.M.loaded_segments (0x3a64c : word) = Some W_3a64c.
Proof. vm_refl. Qed.
Lemma D_3a64c : decode_any W_3a64c = Some (Branch BC_GE 0 10 972, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a650 : bv 32 := 0x00813023.
Lemma F_3a650 : fetch_word Ubsan.M.loaded_segments (0x3a650 : word) = Some W_3a650.
Proof. vm_refl. Qed.
Lemma D_3a650 : decode_any W_3a650 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a654 : bv 32 := 0x00013c23.
Lemma F_3a654 : fetch_word Ubsan.M.loaded_segments (0x3a654 : word) = Some W_3a654.
Proof. vm_refl. Qed.
Lemma D_3a654 : decode_any W_3a654 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a658 : bv 32 := 0x00000593.
Lemma F_3a658 : fetch_word Ubsan.M.loaded_segments (0x3a658 : word) = Some W_3a658.
Proof. vm_refl. Qed.
Lemma D_3a658 : decode_any W_3a658 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a65c : bv 32 := 0x00000613.
Lemma F_3a65c : fetch_word Ubsan.M.loaded_segments (0x3a65c : word) = Some W_3a65c.
Proof. vm_refl. Qed.
Lemma D_3a65c : decode_any W_3a65c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a660 : bv 32 := 0x02913423.
Lemma F_3a660 : fetch_word Ubsan.M.loaded_segments (0x3a660 : word) = Some W_3a660.
Proof. vm_refl. Qed.
Lemma D_3a660 : decode_any W_3a660 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a664 : bv 32 := 0x009036b3.
Lemma F_3a664 : fetch_word Ubsan.M.loaded_segments (0x3a664 : word) = Some W_3a664.
Proof. vm_refl. Qed.
Lemma D_3a664 : decode_any W_3a664 = Some (Op ALU_SLTU 13 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a668 : bv 32 := 0x03313023.
Lemma F_3a668 : fetch_word Ubsan.M.loaded_segments (0x3a668 : word) = Some W_3a668.
Proof. vm_refl. Qed.
Lemma D_3a668 : decode_any W_3a668 = Some (Store SZ8 2 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a66c : bv 32 := 0x01303733.
Lemma F_3a66c : fetch_word Ubsan.M.loaded_segments (0x3a66c : word) = Some W_3a66c.
Proof. vm_refl. Qed.
Lemma D_3a66c : decode_any W_3a66c = Some (Op ALU_SLTU 14 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a670 : bv 32 := 0x00300793.
Lemma F_3a670 : fetch_word Ubsan.M.loaded_segments (0x3a670 : word) = Some W_3a670.
Proof. vm_refl. Qed.
Lemma D_3a670 : decode_any W_3a670 = Some (OpImm ALU_ADD 15 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a674 : bv 32 := 0x01213423.
Lemma F_3a674 : fetch_word Ubsan.M.loaded_segments (0x3a674 : word) = Some W_3a674.
Proof. vm_refl. Qed.
Lemma D_3a674 : decode_any W_3a674 = Some (Store SZ8 2 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a678 : bv 32 := 0x0280006f.
Lemma F_3a678 : fetch_word Ubsan.M.loaded_segments (0x3a678 : word) = Some W_3a678.
Proof. vm_refl. Qed.
Lemma D_3a678 : decode_any W_3a678 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a67c : bv 32 := 0x03012503.
Lemma F_3a67c : fetch_word Ubsan.M.loaded_segments (0x3a67c : word) = Some W_3a67c.
Proof. vm_refl. Qed.
Lemma D_3a67c : decode_any W_3a67c = Some (Load SZ4 true 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a680 : bv 32 := 0x0016061b.
Lemma F_3a680 : fetch_word Ubsan.M.loaded_segments (0x3a680 : word) = Some W_3a680.
Proof. vm_refl. Qed.
Lemma D_3a680 : decode_any W_3a680 = Some (OpImm32 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a684 : bv 32 := 0x00813903.
Lemma F_3a684 : fetch_word Ubsan.M.loaded_segments (0x3a684 : word) = Some W_3a684.
Proof. vm_refl. Qed.
Lemma D_3a684 : decode_any W_3a684 = Some (Load SZ8 true 18 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a688 : bv 32 := 0x012585bb.
Lemma F_3a688 : fetch_word Ubsan.M.loaded_segments (0x3a688 : word) = Some W_3a688.
Proof. vm_refl. Qed.
Lemma D_3a688 : decode_any W_3a688 = Some (Op32 ALU_ADD 11 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a68c : bv 32 := 0x01013803.
Lemma F_3a68c : fetch_word Ubsan.M.loaded_segments (0x3a68c : word) = Some W_3a68c.
Proof. vm_refl. Qed.
Lemma D_3a68c : decode_any W_3a68c = Some (Load SZ8 true 16 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a690 : bv 32 := 0x01813883.
Lemma F_3a690 : fetch_word Ubsan.M.loaded_segments (0x3a690 : word) = Some W_3a690.
Proof. vm_refl. Qed.
Lemma D_3a690 : decode_any W_3a690 = Some (Load SZ8 true 17 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a694 : bv 32 := 0x010888bb.
Lemma F_3a694 : fetch_word Ubsan.M.loaded_segments (0x3a694 : word) = Some W_3a694.
Proof. vm_refl. Qed.
Lemma D_3a694 : decode_any W_3a694 = Some (Op32 ALU_ADD 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a698 : bv 32 := 0x01113c23.
Lemma F_3a698 : fetch_word Ubsan.M.loaded_segments (0x3a698 : word) = Some W_3a698.
Proof. vm_refl. Qed.
Lemma D_3a698 : decode_any W_3a698 = Some (Store SZ8 2 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a69c : bv 32 := 0x30a65663.
Lemma F_3a69c : fetch_word Ubsan.M.loaded_segments (0x3a69c : word) = Some W_3a69c.
Proof. vm_refl. Qed.
Lemma D_3a69c : decode_any W_3a69c = Some (Branch BC_GE 12 10 780, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6a0 : bv 32 := 0x032608b3.
Lemma F_3a6a0 : fetch_word Ubsan.M.loaded_segments (0x3a6a0 : word) = Some W_3a6a0.
Proof. vm_refl. Qed.
Lemma D_3a6a0 : decode_any W_3a6a0 = Some (Mul M_MUL 17 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6a4 : bv 32 := 0x0326083b.
Lemma F_3a6a4 : fetch_word Ubsan.M.loaded_segments (0x3a6a4 : word) = Some W_3a6a4.
Proof. vm_refl. Qed.
Lemma D_3a6a4 : decode_any W_3a6a4 = Some (Mul32 M_MUL 16 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6a8 : bv 32 := 0x3b181863.
Lemma F_3a6a8 : fetch_word Ubsan.M.loaded_segments (0x3a6a8 : word) = Some W_3a6a8.
Proof. vm_refl. Qed.
Lemma D_3a6a8 : decode_any W_3a6a8 = Some (Branch BC_NE 16 17 944, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6ac : bv 32 := 0x0008889b.
Lemma F_3a6ac : fetch_word Ubsan.M.loaded_segments (0x3a6ac : word) = Some W_3a6ac.
Proof. vm_refl. Qed.
Lemma D_3a6ac : decode_any W_3a6ac = Some (OpImm32 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6b0 : bv 32 := 0x00289813.
Lemma F_3a6b0 : fetch_word Ubsan.M.loaded_segments (0x3a6b0 : word) = Some W_3a6b0.
Proof. vm_refl. Qed.
Lemma D_3a6b0 : decode_any W_3a6b0 = Some (ShiftImm ALU_SLL 16 17 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6b4 : bv 32 := 0x02813503.
Lemma F_3a6b4 : fetch_word Ubsan.M.loaded_segments (0x3a6b4 : word) = Some W_3a6b4.
Proof. vm_refl. Qed.
Lemma D_3a6b4 : decode_any W_3a6b4 = Some (Load SZ8 true 10 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6b8 : bv 32 := 0x01050833.
Lemma F_3a6b8 : fetch_word Ubsan.M.loaded_segments (0x3a6b8 : word) = Some W_3a6b8.
Proof. vm_refl. Qed.
Lemma D_3a6b8 : decode_any W_3a6b8 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6bc : bv 32 := 0x00183293.
Lemma F_3a6bc : fetch_word Ubsan.M.loaded_segments (0x3a6bc : word) = Some W_3a6bc.
Proof. vm_refl. Qed.
Lemma D_3a6bc : decode_any W_3a6bc = Some (OpImm ALU_SLTU 5 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6c0 : bv 32 := 0x38568c63.
Lemma F_3a6c0 : fetch_word Ubsan.M.loaded_segments (0x3a6c0 : word) = Some W_3a6c0.
Proof. vm_refl. Qed.
Lemma D_3a6c0 : decode_any W_3a6c0 = Some (Branch BC_EQ 13 5 920, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6c4 : bv 32 := 0x02813503.
Lemma F_3a6c4 : fetch_word Ubsan.M.loaded_segments (0x3a6c4 : word) = Some W_3a6c4.
Proof. vm_refl. Qed.
Lemma D_3a6c4 : decode_any W_3a6c4 = Some (Load SZ8 true 10 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6c8 : bv 32 := 0x00a832b3.
Lemma F_3a6c8 : fetch_word Ubsan.M.loaded_segments (0x3a6c8 : word) = Some W_3a6c8.
Proof. vm_refl. Qed.
Lemma D_3a6c8 : decode_any W_3a6c8 = Some (Op ALU_SLTU 5 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6cc : bv 32 := 0x0008a893.
Lemma F_3a6cc : fetch_word Ubsan.M.loaded_segments (0x3a6cc : word) = Some W_3a6cc.
Proof. vm_refl. Qed.
Lemma D_3a6cc : decode_any W_3a6cc = Some (OpImm ALU_SLT 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6d0 : bv 32 := 0x0112c8b3.
Lemma F_3a6d0 : fetch_word Ubsan.M.loaded_segments (0x3a6d0 : word) = Some W_3a6d0.
Proof. vm_refl. Qed.
Lemma D_3a6d0 : decode_any W_3a6d0 = Some (Op ALU_XOR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6d4 : bv 32 := 0x0018c893.
Lemma F_3a6d4 : fetch_word Ubsan.M.loaded_segments (0x3a6d4 : word) = Some W_3a6d4.
Proof. vm_refl. Qed.
Lemma D_3a6d4 : decode_any W_3a6d4 = Some (OpImm ALU_XOR 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6d8 : bv 32 := 0x38088063.
Lemma F_3a6d8 : fetch_word Ubsan.M.loaded_segments (0x3a6d8 : word) = Some W_3a6d8.
Proof. vm_refl. Qed.
Lemma D_3a6d8 : decode_any W_3a6d8 = Some (Branch BC_EQ 17 0 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6dc : bv 32 := 0x01013503.
Lemma F_3a6dc : fetch_word Ubsan.M.loaded_segments (0x3a6dc : word) = Some W_3a6dc.
Proof. vm_refl. Qed.
Lemma D_3a6dc : decode_any W_3a6dc = Some (Load SZ8 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6e0 : bv 32 := 0x02a602b3.
Lemma F_3a6e0 : fetch_word Ubsan.M.loaded_segments (0x3a6e0 : word) = Some W_3a6e0.
Proof. vm_refl. Qed.
Lemma D_3a6e0 : decode_any W_3a6e0 = Some (Mul M_MUL 5 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6e4 : bv 32 := 0x02a608bb.
Lemma F_3a6e4 : fetch_word Ubsan.M.loaded_segments (0x3a6e4 : word) = Some W_3a6e4.
Proof. vm_refl. Qed.
Lemma D_3a6e4 : decode_any W_3a6e4 = Some (Mul32 M_MUL 17 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6e8 : bv 32 := 0x36589863.
Lemma F_3a6e8 : fetch_word Ubsan.M.loaded_segments (0x3a6e8 : word) = Some W_3a6e8.
Proof. vm_refl. Qed.
Lemma D_3a6e8 : decode_any W_3a6e8 = Some (Branch BC_NE 17 5 880, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6ec : bv 32 := 0x0002829b.
Lemma F_3a6ec : fetch_word Ubsan.M.loaded_segments (0x3a6ec : word) = Some W_3a6ec.
Proof. vm_refl. Qed.
Lemma D_3a6ec : decode_any W_3a6ec = Some (OpImm32 5 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6f0 : bv 32 := 0x00229893.
Lemma F_3a6f0 : fetch_word Ubsan.M.loaded_segments (0x3a6f0 : word) = Some W_3a6f0.
Proof. vm_refl. Qed.
Lemma D_3a6f0 : decode_any W_3a6f0 = Some (ShiftImm ALU_SLL 17 5 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6f4 : bv 32 := 0x02013503.
Lemma F_3a6f4 : fetch_word Ubsan.M.loaded_segments (0x3a6f4 : word) = Some W_3a6f4.
Proof. vm_refl. Qed.
Lemma D_3a6f4 : decode_any W_3a6f4 = Some (Load SZ8 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6f8 : bv 32 := 0x011508b3.
Lemma F_3a6f8 : fetch_word Ubsan.M.loaded_segments (0x3a6f8 : word) = Some W_3a6f8.
Proof. vm_refl. Qed.
Lemma D_3a6f8 : decode_any W_3a6f8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a6fc : bv 32 := 0x0018b313.
Lemma F_3a6fc : fetch_word Ubsan.M.loaded_segments (0x3a6fc : word) = Some W_3a6fc.
Proof. vm_refl. Qed.
Lemma D_3a6fc : decode_any W_3a6fc = Some (OpImm ALU_SLTU 6 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a700 : bv 32 := 0x34670c63.
Lemma F_3a700 : fetch_word Ubsan.M.loaded_segments (0x3a700 : word) = Some W_3a700.
Proof. vm_refl. Qed.
Lemma D_3a700 : decode_any W_3a700 = Some (Branch BC_EQ 14 6 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a704 : bv 32 := 0x02013503.
Lemma F_3a704 : fetch_word Ubsan.M.loaded_segments (0x3a704 : word) = Some W_3a704.
Proof. vm_refl. Qed.
Lemma D_3a704 : decode_any W_3a704 = Some (Load SZ8 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a708 : bv 32 := 0x00a8b333.
Lemma F_3a708 : fetch_word Ubsan.M.loaded_segments (0x3a708 : word) = Some W_3a708.
Proof. vm_refl. Qed.
Lemma D_3a708 : decode_any W_3a708 = Some (Op ALU_SLTU 6 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a70c : bv 32 := 0x0002a293.
Lemma F_3a70c : fetch_word Ubsan.M.loaded_segments (0x3a70c : word) = Some W_3a70c.
Proof. vm_refl. Qed.
Lemma D_3a70c : decode_any W_3a70c = Some (OpImm ALU_SLT 5 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a710 : bv 32 := 0x005342b3.
Lemma F_3a710 : fetch_word Ubsan.M.loaded_segments (0x3a710 : word) = Some W_3a710.
Proof. vm_refl. Qed.
Lemma D_3a710 : decode_any W_3a710 = Some (Op ALU_XOR 5 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a714 : bv 32 := 0x0012c293.
Lemma F_3a714 : fetch_word Ubsan.M.loaded_segments (0x3a714 : word) = Some W_3a714.
Proof. vm_refl. Qed.
Lemma D_3a714 : decode_any W_3a714 = Some (OpImm ALU_XOR 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a718 : bv 32 := 0x34028063.
Lemma F_3a718 : fetch_word Ubsan.M.loaded_segments (0x3a718 : word) = Some W_3a718.
Proof. vm_refl. Qed.
Lemma D_3a718 : decode_any W_3a718 = Some (Branch BC_EQ 5 0 832, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a71c : bv 32 := 0x320b0e63.
Lemma F_3a71c : fetch_word Ubsan.M.loaded_segments (0x3a71c : word) = Some W_3a71c.
Proof. vm_refl. Qed.
Lemma D_3a71c : decode_any W_3a71c = Some (Branch BC_EQ 22 0 828, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a720 : bv 32 := 0x03412283.
Lemma F_3a720 : fetch_word Ubsan.M.loaded_segments (0x3a720 : word) = Some W_3a720.
Proof. vm_refl. Qed.
Lemma D_3a720 : decode_any W_3a720 = Some (Load SZ4 true 5 2 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a724 : bv 32 := 0xf4505ce3.
Lemma F_3a724 : fetch_word Ubsan.M.loaded_segments (0x3a724 : word) = Some W_3a724.
Proof. vm_refl. Qed.
Lemma D_3a724 : decode_any W_3a724 = Some (Branch BC_GE 0 5 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a728 : bv 32 := 0x00000293.
Lemma F_3a728 : fetch_word Ubsan.M.loaded_segments (0x3a728 : word) = Some W_3a728.
Proof. vm_refl. Qed.
Lemma D_3a728 : decode_any W_3a728 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a72c : bv 32 := 0x00000313.
Lemma F_3a72c : fetch_word Ubsan.M.loaded_segments (0x3a72c : word) = Some W_3a72c.
Proof. vm_refl. Qed.
Lemma D_3a72c : decode_any W_3a72c = Some (OpImm ALU_ADD 6 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a730 : bv 32 := 0x00259393.
Lemma F_3a730 : fetch_word Ubsan.M.loaded_segments (0x3a730 : word) = Some W_3a730.
Proof. vm_refl. Qed.
Lemma D_3a730 : decode_any W_3a730 = Some (ShiftImm ALU_SLL 7 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a734 : bv 32 := 0x01813e03.
Lemma F_3a734 : fetch_word Ubsan.M.loaded_segments (0x3a734 : word) = Some W_3a734.
Proof. vm_refl. Qed.
Lemma D_3a734 : decode_any W_3a734 = Some (Load SZ8 true 28 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a738 : bv 32 := 0x002e1e13.
Lemma F_3a738 : fetch_word Ubsan.M.loaded_segments (0x3a738 : word) = Some W_3a738.
Proof. vm_refl. Qed.
Lemma D_3a738 : decode_any W_3a738 = Some (ShiftImm ALU_SLL 28 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a73c : bv 32 := 0x02813503.
Lemma F_3a73c : fetch_word Ubsan.M.loaded_segments (0x3a73c : word) = Some W_3a73c.
Proof. vm_refl. Qed.
Lemma D_3a73c : decode_any W_3a73c = Some (Load SZ8 true 10 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a740 : bv 32 := 0x007503b3.
Lemma F_3a740 : fetch_word Ubsan.M.loaded_segments (0x3a740 : word) = Some W_3a740.
Proof. vm_refl. Qed.
Lemma D_3a740 : decode_any W_3a740 = Some (Op ALU_ADD 7 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a744 : bv 32 := 0x02013503.
Lemma F_3a744 : fetch_word Ubsan.M.loaded_segments (0x3a744 : word) = Some W_3a744.
Proof. vm_refl. Qed.
Lemma D_3a744 : decode_any W_3a744 = Some (Load SZ8 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a748 : bv 32 := 0x01c50e33.
Lemma F_3a748 : fetch_word Ubsan.M.loaded_segments (0x3a748 : word) = Some W_3a748.
Proof. vm_refl. Qed.
Lemma D_3a748 : decode_any W_3a748 = Some (Op ALU_ADD 28 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a74c : bv 32 := 0x03664ebb.
Lemma F_3a74c : fetch_word Ubsan.M.loaded_segments (0x3a74c : word) = Some W_3a74c.
Proof. vm_refl. Qed.
Lemma D_3a74c : decode_any W_3a74c = Some (Mul32 M_DIV 29 12 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a750 : bv 32 := 0x003e9f13.
Lemma F_3a750 : fetch_word Ubsan.M.loaded_segments (0x3a750 : word) = Some W_3a750.
Proof. vm_refl. Qed.
Lemma D_3a750 : decode_any W_3a750 = Some (ShiftImm ALU_SLL 30 29 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a754 : bv 32 := 0x000e0f93.
Lemma F_3a754 : fetch_word Ubsan.M.loaded_segments (0x3a754 : word) = Some W_3a754.
Proof. vm_refl. Qed.
Lemma D_3a754 : decode_any W_3a754 = Some (OpImm ALU_ADD 31 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a758 : bv 32 := 0x00038a93.
Lemma F_3a758 : fetch_word Ubsan.M.loaded_segments (0x3a758 : word) = Some W_3a758.
Proof. vm_refl. Qed.
Lemma D_3a758 : decode_any W_3a758 = Some (OpImm ALU_ADD 21 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a75c : bv 32 := 0x2f0aee63.
Lemma F_3a75c : fetch_word Ubsan.M.loaded_segments (0x3a75c : word) = Some W_3a75c.
Proof. vm_refl. Qed.
Lemma D_3a75c : decode_any W_3a75c = Some (Branch BC_LTU 21 16 764, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a760 : bv 32 := 0x001ab413.
Lemma F_3a760 : fetch_word Ubsan.M.loaded_segments (0x3a760 : word) = Some W_3a760.
Proof. vm_refl. Qed.
Lemma D_3a760 : decode_any W_3a760 = Some (OpImm ALU_SLTU 8 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a764 : bv 32 := 0x0086c433.
Lemma F_3a764 : fetch_word Ubsan.M.loaded_segments (0x3a764 : word) = Some W_3a764.
Proof. vm_refl. Qed.
Lemma D_3a764 : decode_any W_3a764 = Some (Op ALU_XOR 8 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a768 : bv 32 := 0x2e040863.
Lemma F_3a768 : fetch_word Ubsan.M.loaded_segments (0x3a768 : word) = Some W_3a768.
Proof. vm_refl. Qed.
Lemma D_3a768 : decode_any W_3a768 = Some (Branch BC_EQ 8 0 752, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a76c : bv 32 := 0x2ef38663.
Lemma F_3a76c : fetch_word Ubsan.M.loaded_segments (0x3a76c : word) = Some W_3a76c.
Proof. vm_refl. Qed.
Lemma D_3a76c : decode_any W_3a76c = Some (Branch BC_EQ 7 15 748, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a770 : bv 32 := 0x003ac413.
Lemma F_3a770 : fetch_word Ubsan.M.loaded_segments (0x3a770 : word) = Some W_3a770.
Proof. vm_refl. Qed.
Lemma D_3a770 : decode_any W_3a770 = Some (OpImm ALU_XOR 8 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a774 : bv 32 := 0x00044d03.
Lemma F_3a774 : fetch_word Ubsan.M.loaded_segments (0x3a774 : word) = Some W_3a774.
Proof. vm_refl. Qed.
Lemma D_3a774 : decode_any W_3a774 = Some (Load SZ1 false 26 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a778 : bv 32 := 0x002d1d13.
Lemma F_3a778 : fetch_word Ubsan.M.loaded_segments (0x3a778 : word) = Some W_3a778.
Proof. vm_refl. Qed.
Lemma D_3a778 : decode_any W_3a778 = Some (ShiftImm ALU_SLL 26 26 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a77c : bv 32 := 0x01ab8433.
Lemma F_3a77c : fetch_word Ubsan.M.loaded_segments (0x3a77c : word) = Some W_3a77c.
Proof. vm_refl. Qed.
Lemma D_3a77c : decode_any W_3a77c = Some (Op ALU_ADD 8 23 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a780 : bv 32 := 0x2d746c63.
Lemma F_3a780 : fetch_word Ubsan.M.loaded_segments (0x3a780 : word) = Some W_3a780.
Proof. vm_refl. Qed.
Lemma D_3a780 : decode_any W_3a780 = Some (Branch BC_LTU 8 23 728, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a784 : bv 32 := 0x017034b3.
Lemma F_3a784 : fetch_word Ubsan.M.loaded_segments (0x3a784 : word) = Some W_3a784.
Proof. vm_refl. Qed.
Lemma D_3a784 : decode_any W_3a784 = Some (Op ALU_SLTU 9 0 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a788 : bv 32 := 0x00143913.
Lemma F_3a788 : fetch_word Ubsan.M.loaded_segments (0x3a788 : word) = Some W_3a788.
Proof. vm_refl. Qed.
Lemma D_3a788 : decode_any W_3a788 = Some (OpImm ALU_SLTU 18 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a78c : bv 32 := 0x0124c4b3.
Lemma F_3a78c : fetch_word Ubsan.M.loaded_segments (0x3a78c : word) = Some W_3a78c.
Proof. vm_refl. Qed.
Lemma D_3a78c : decode_any W_3a78c = Some (Op ALU_XOR 9 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a790 : bv 32 := 0x2c048463.
Lemma F_3a790 : fetch_word Ubsan.M.loaded_segments (0x3a790 : word) = Some W_3a790.
Proof. vm_refl. Qed.
Lemma D_3a790 : decode_any W_3a790 = Some (Branch BC_EQ 9 0 712, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a794 : bv 32 := 0x2c0b8263.
Lemma F_3a794 : fetch_word Ubsan.M.loaded_segments (0x3a794 : word) = Some W_3a794.
Proof. vm_refl. Qed.
Lemma D_3a794 : decode_any W_3a794 = Some (Branch BC_EQ 23 0 708, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a798 : bv 32 := 0x00347493.
Lemma F_3a798 : fetch_word Ubsan.M.loaded_segments (0x3a798 : word) = Some W_3a798.
Proof. vm_refl. Qed.
Lemma D_3a798 : decode_any W_3a798 = Some (OpImm ALU_AND 9 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a79c : bv 32 := 0x2a049e63.
Lemma F_3a79c : fetch_word Ubsan.M.loaded_segments (0x3a79c : word) = Some W_3a79c.
Proof. vm_refl. Qed.
Lemma D_3a79c : decode_any W_3a79c = Some (Branch BC_NE 9 0 700, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7a0 : bv 32 := 0x00042903.
Lemma F_3a7a0 : fetch_word Ubsan.M.loaded_segments (0x3a7a0 : word) = Some W_3a7a0.
Proof. vm_refl. Qed.
Lemma D_3a7a0 : decode_any W_3a7a0 = Some (Load SZ4 true 18 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7a4 : bv 32 := 0x019034b3.
Lemma F_3a7a4 : fetch_word Ubsan.M.loaded_segments (0x3a7a4 : word) = Some W_3a7a4.
Proof. vm_refl. Qed.
Lemma D_3a7a4 : decode_any W_3a7a4 = Some (Op ALU_SLTU 9 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7a8 : bv 32 := 0x00391413.
Lemma F_3a7a8 : fetch_word Ubsan.M.loaded_segments (0x3a7a8 : word) = Some W_3a7a8.
Proof. vm_refl. Qed.
Lemma D_3a7a8 : decode_any W_3a7a8 = Some (ShiftImm ALU_SLL 8 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7ac : bv 32 := 0x008c8433.
Lemma F_3a7ac : fetch_word Ubsan.M.loaded_segments (0x3a7ac : word) = Some W_3a7ac.
Proof. vm_refl. Qed.
Lemma D_3a7ac : decode_any W_3a7ac = Some (Op ALU_ADD 8 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7b0 : bv 32 := 0x00143993.
Lemma F_3a7b0 : fetch_word Ubsan.M.loaded_segments (0x3a7b0 : word) = Some W_3a7b0.
Proof. vm_refl. Qed.
Lemma D_3a7b0 : decode_any W_3a7b0 = Some (OpImm ALU_SLTU 19 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7b4 : bv 32 := 0x2b348263.
Lemma F_3a7b4 : fetch_word Ubsan.M.loaded_segments (0x3a7b4 : word) = Some W_3a7b4.
Proof. vm_refl. Qed.
Lemma D_3a7b4 : decode_any W_3a7b4 = Some (Branch BC_EQ 9 19 676, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7b8 : bv 32 := 0x00092493.
Lemma F_3a7b8 : fetch_word Ubsan.M.loaded_segments (0x3a7b8 : word) = Some W_3a7b8.
Proof. vm_refl. Qed.
Lemma D_3a7b8 : decode_any W_3a7b8 = Some (OpImm ALU_SLT 9 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7bc : bv 32 := 0x019439b3.
Lemma F_3a7bc : fetch_word Ubsan.M.loaded_segments (0x3a7bc : word) = Some W_3a7bc.
Proof. vm_refl. Qed.
Lemma D_3a7bc : decode_any W_3a7bc = Some (Op ALU_SLTU 19 8 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7c0 : bv 32 := 0x0099c4b3.
Lemma F_3a7c0 : fetch_word Ubsan.M.loaded_segments (0x3a7c0 : word) = Some W_3a7c0.
Proof. vm_refl. Qed.
Lemma D_3a7c0 : decode_any W_3a7c0 = Some (Op ALU_XOR 9 19 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7c4 : bv 32 := 0x0014c493.
Lemma F_3a7c4 : fetch_word Ubsan.M.loaded_segments (0x3a7c4 : word) = Some W_3a7c4.
Proof. vm_refl. Qed.
Lemma D_3a7c4 : decode_any W_3a7c4 = Some (OpImm ALU_XOR 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7c8 : bv 32 := 0x28048863.
Lemma F_3a7c8 : fetch_word Ubsan.M.loaded_segments (0x3a7c8 : word) = Some W_3a7c8.
Proof. vm_refl. Qed.
Lemma D_3a7c8 : decode_any W_3a7c8 = Some (Branch BC_EQ 9 0 656, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7cc : bv 32 := 0x280c8663.
Lemma F_3a7cc : fetch_word Ubsan.M.loaded_segments (0x3a7cc : word) = Some W_3a7cc.
Proof. vm_refl. Qed.
Lemma D_3a7cc : decode_any W_3a7cc = Some (Branch BC_EQ 25 0 652, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7d0 : bv 32 := 0x00747493.
Lemma F_3a7d0 : fetch_word Ubsan.M.loaded_segments (0x3a7d0 : word) = Some W_3a7d0.
Proof. vm_refl. Qed.
Lemma D_3a7d0 : decode_any W_3a7d0 = Some (OpImm ALU_AND 9 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7d4 : bv 32 := 0x28049263.
Lemma F_3a7d4 : fetch_word Ubsan.M.loaded_segments (0x3a7d4 : word) = Some W_3a7d4.
Proof. vm_refl. Qed.
Lemma D_3a7d4 : decode_any W_3a7d4 = Some (Branch BC_NE 9 0 644, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7d8 : bv 32 := 0x00043983.
Lemma F_3a7d8 : fetch_word Ubsan.M.loaded_segments (0x3a7d8 : word) = Some W_3a7d8.
Proof. vm_refl. Qed.
Lemma D_3a7d8 : decode_any W_3a7d8 = Some (Load SZ8 true 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7dc : bv 32 := 0x013f04b3.
Lemma F_3a7dc : fetch_word Ubsan.M.loaded_segments (0x3a7dc : word) = Some W_3a7dc.
Proof. vm_refl. Qed.
Lemma D_3a7dc : decode_any W_3a7dc = Some (Op ALU_ADD 9 30 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7e0 : bv 32 := 0x01303433.
Lemma F_3a7e0 : fetch_word Ubsan.M.loaded_segments (0x3a7e0 : word) = Some W_3a7e0.
Proof. vm_refl. Qed.
Lemma D_3a7e0 : decode_any W_3a7e0 = Some (Op ALU_SLTU 8 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7e4 : bv 32 := 0x0014bd93.
Lemma F_3a7e4 : fetch_word Ubsan.M.loaded_segments (0x3a7e4 : word) = Some W_3a7e4.
Proof. vm_refl. Qed.
Lemma D_3a7e4 : decode_any W_3a7e4 = Some (OpImm ALU_SLTU 27 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7e8 : bv 32 := 0x27b40863.
Lemma F_3a7e8 : fetch_word Ubsan.M.loaded_segments (0x3a7e8 : word) = Some W_3a7e8.
Proof. vm_refl. Qed.
Lemma D_3a7e8 : decode_any W_3a7e8 = Some (Branch BC_EQ 8 27 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7ec : bv 32 := 0x000ea413.
Lemma F_3a7ec : fetch_word Ubsan.M.loaded_segments (0x3a7ec : word) = Some W_3a7ec.
Proof. vm_refl. Qed.
Lemma D_3a7ec : decode_any W_3a7ec = Some (OpImm ALU_SLT 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7f0 : bv 32 := 0x01e4bdb3.
Lemma F_3a7f0 : fetch_word Ubsan.M.loaded_segments (0x3a7f0 : word) = Some W_3a7f0.
Proof. vm_refl. Qed.
Lemma D_3a7f0 : decode_any W_3a7f0 = Some (Op ALU_SLTU 27 9 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7f4 : bv 32 := 0x01b44db3.
Lemma F_3a7f4 : fetch_word Ubsan.M.loaded_segments (0x3a7f4 : word) = Some W_3a7f4.
Proof. vm_refl. Qed.
Lemma D_3a7f4 : decode_any W_3a7f4 = Some (Op ALU_XOR 27 8 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7f8 : bv 32 := 0x001dcd93.
Lemma F_3a7f8 : fetch_word Ubsan.M.loaded_segments (0x3a7f8 : word) = Some W_3a7f8.
Proof. vm_refl. Qed.
Lemma D_3a7f8 : decode_any W_3a7f8 = Some (OpImm ALU_XOR 27 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a7fc : bv 32 := 0x240d8e63.
Lemma F_3a7fc : fetch_word Ubsan.M.loaded_segments (0x3a7fc : word) = Some W_3a7fc.
Proof. vm_refl. Qed.
Lemma D_3a7fc : decode_any W_3a7fc = Some (Branch BC_EQ 27 0 604, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a800 : bv 32 := 0x24098c63.
Lemma F_3a800 : fetch_word Ubsan.M.loaded_segments (0x3a800 : word) = Some W_3a800.
Proof. vm_refl. Qed.
Lemma D_3a800 : decode_any W_3a800 = Some (Branch BC_EQ 19 0 600, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a804 : bv 32 := 0x0074f993.
Lemma F_3a804 : fetch_word Ubsan.M.loaded_segments (0x3a804 : word) = Some W_3a804.
Proof. vm_refl. Qed.
Lemma D_3a804 : decode_any W_3a804 = Some (OpImm ALU_AND 19 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a808 : bv 32 := 0x24099863.
Lemma F_3a808 : fetch_word Ubsan.M.loaded_segments (0x3a808 : word) = Some W_3a808.
Proof. vm_refl. Qed.
Lemma D_3a808 : decode_any W_3a808 = Some (Branch BC_NE 19 0 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a80c : bv 32 := 0x0004b983.
Lemma F_3a80c : fetch_word Ubsan.M.loaded_segments (0x3a80c : word) = Some W_3a80c.
Proof. vm_refl. Qed.
Lemma D_3a80c : decode_any W_3a80c = Some (Load SZ8 true 19 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a810 : bv 32 := 0x0362cdbb.
Lemma F_3a810 : fetch_word Ubsan.M.loaded_segments (0x3a810 : word) = Some W_3a810.
Proof. vm_refl. Qed.
Lemma D_3a810 : decode_any W_3a810 = Some (Mul32 M_DIV 27 5 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a814 : bv 32 := 0x01b984b3.
Lemma F_3a814 : fetch_word Ubsan.M.loaded_segments (0x3a814 : word) = Some W_3a814.
Proof. vm_refl. Qed.
Lemma D_3a814 : decode_any W_3a814 = Some (Op ALU_ADD 9 19 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a818 : bv 32 := 0x013030b3.
Lemma F_3a818 : fetch_word Ubsan.M.loaded_segments (0x3a818 : word) = Some W_3a818.
Proof. vm_refl. Qed.
Lemma D_3a818 : decode_any W_3a818 = Some (Op ALU_SLTU 1 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a81c : bv 32 := 0x0014ba13.
Lemma F_3a81c : fetch_word Ubsan.M.loaded_segments (0x3a81c : word) = Some W_3a81c.
Proof. vm_refl. Qed.
Lemma D_3a81c : decode_any W_3a81c = Some (OpImm ALU_SLTU 20 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a820 : bv 32 := 0x23408c63.
Lemma F_3a820 : fetch_word Ubsan.M.loaded_segments (0x3a820 : word) = Some W_3a820.
Proof. vm_refl. Qed.
Lemma D_3a820 : decode_any W_3a820 = Some (Branch BC_EQ 1 20 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a824 : bv 32 := 0x0134ba33.
Lemma F_3a824 : fetch_word Ubsan.M.loaded_segments (0x3a824 : word) = Some W_3a824.
Proof. vm_refl. Qed.
Lemma D_3a824 : decode_any W_3a824 = Some (Op ALU_SLTU 20 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a828 : bv 32 := 0x000da993.
Lemma F_3a828 : fetch_word Ubsan.M.loaded_segments (0x3a828 : word) = Some W_3a828.
Proof. vm_refl. Qed.
Lemma D_3a828 : decode_any W_3a828 = Some (OpImm ALU_SLT 19 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a82c : bv 32 := 0x0149ca33.
Lemma F_3a82c : fetch_word Ubsan.M.loaded_segments (0x3a82c : word) = Some W_3a82c.
Proof. vm_refl. Qed.
Lemma D_3a82c : decode_any W_3a82c = Some (Op ALU_XOR 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a830 : bv 32 := 0x001a4a13.
Lemma F_3a830 : fetch_word Ubsan.M.loaded_segments (0x3a830 : word) = Some W_3a830.
Proof. vm_refl. Qed.
Lemma D_3a830 : decode_any W_3a830 = Some (OpImm ALU_XOR 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a834 : bv 32 := 0x220a0263.
Lemma F_3a834 : fetch_word Ubsan.M.loaded_segments (0x3a834 : word) = Some W_3a834.
Proof. vm_refl. Qed.
Lemma D_3a834 : decode_any W_3a834 = Some (Branch BC_EQ 20 0 548, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a838 : bv 32 := 0x22f48063.
Lemma F_3a838 : fetch_word Ubsan.M.loaded_segments (0x3a838 : word) = Some W_3a838.
Proof. vm_refl. Qed.
Lemma D_3a838 : decode_any W_3a838 = Some (Branch BC_EQ 9 15 544, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a83c : bv 32 := 0x0019009b.
Lemma F_3a83c : fetch_word Ubsan.M.loaded_segments (0x3a83c : word) = Some W_3a83c.
Proof. vm_refl. Qed.
Lemma D_3a83c : decode_any W_3a83c = Some (OpImm32 1 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a840 : bv 32 := 0x2120cc63.
Lemma F_3a840 : fetch_word Ubsan.M.loaded_segments (0x3a840 : word) = Some W_3a840.
Proof. vm_refl. Qed.
Lemma D_3a840 : decode_any W_3a840 = Some (Branch BC_LT 1 18 536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a844 : bv 32 := 0x00309913.
Lemma F_3a844 : fetch_word Ubsan.M.loaded_segments (0x3a844 : word) = Some W_3a844.
Proof. vm_refl. Qed.
Lemma D_3a844 : decode_any W_3a844 = Some (ShiftImm ALU_SLL 18 1 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a848 : bv 32 := 0x01990933.
Lemma F_3a848 : fetch_word Ubsan.M.loaded_segments (0x3a848 : word) = Some W_3a848.
Proof. vm_refl. Qed.
Lemma D_3a848 : decode_any W_3a848 = Some (Op ALU_ADD 18 18 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a84c : bv 32 := 0x20090663.
Lemma F_3a84c : fetch_word Ubsan.M.loaded_segments (0x3a84c : word) = Some W_3a84c.
Proof. vm_refl. Qed.
Lemma D_3a84c : decode_any W_3a84c = Some (Branch BC_EQ 18 0 524, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a850 : bv 32 := 0x01993a33.
Lemma F_3a850 : fetch_word Ubsan.M.loaded_segments (0x3a850 : word) = Some W_3a850.
Proof. vm_refl. Qed.
Lemma D_3a850 : decode_any W_3a850 = Some (Op ALU_SLTU 20 18 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a854 : bv 32 := 0x0000a093.
Lemma F_3a854 : fetch_word Ubsan.M.loaded_segments (0x3a854 : word) = Some W_3a854.
Proof. vm_refl. Qed.
Lemma D_3a854 : decode_any W_3a854 = Some (OpImm ALU_SLT 1 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a858 : bv 32 := 0x001a4a33.
Lemma F_3a858 : fetch_word Ubsan.M.loaded_segments (0x3a858 : word) = Some W_3a858.
Proof. vm_refl. Qed.
Lemma D_3a858 : decode_any W_3a858 = Some (Op ALU_XOR 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a85c : bv 32 := 0x001a4a13.
Lemma F_3a85c : fetch_word Ubsan.M.loaded_segments (0x3a85c : word) = Some W_3a85c.
Proof. vm_refl. Qed.
Lemma D_3a85c : decode_any W_3a85c = Some (OpImm ALU_XOR 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a860 : bv 32 := 0x1e0a0c63.
Lemma F_3a860 : fetch_word Ubsan.M.loaded_segments (0x3a860 : word) = Some W_3a860.
Proof. vm_refl. Qed.
Lemma D_3a860 : decode_any W_3a860 = Some (Branch BC_EQ 20 0 504, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a864 : bv 32 := 0x00093903.
Lemma F_3a864 : fetch_word Ubsan.M.loaded_segments (0x3a864 : word) = Some W_3a864.
Proof. vm_refl. Qed.
Lemma D_3a864 : decode_any W_3a864 = Some (Load SZ8 true 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a868 : bv 32 := 0x012f00b3.
Lemma F_3a868 : fetch_word Ubsan.M.loaded_segments (0x3a868 : word) = Some W_3a868.
Proof. vm_refl. Qed.
Lemma D_3a868 : decode_any W_3a868 = Some (Op ALU_ADD 1 30 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a86c : bv 32 := 0x01203a33.
Lemma F_3a86c : fetch_word Ubsan.M.loaded_segments (0x3a86c : word) = Some W_3a86c.
Proof. vm_refl. Qed.
Lemma D_3a86c : decode_any W_3a86c = Some (Op ALU_SLTU 20 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a870 : bv 32 := 0x0010b513.
Lemma F_3a870 : fetch_word Ubsan.M.loaded_segments (0x3a870 : word) = Some W_3a870.
Proof. vm_refl. Qed.
Lemma D_3a870 : decode_any W_3a870 = Some (OpImm ALU_SLTU 10 1 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a874 : bv 32 := 0x1eaa0263.
Lemma F_3a874 : fetch_word Ubsan.M.loaded_segments (0x3a874 : word) = Some W_3a874.
Proof. vm_refl. Qed.
Lemma D_3a874 : decode_any W_3a874 = Some (Branch BC_EQ 20 10 484, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a878 : bv 32 := 0x01e0b533.
Lemma F_3a878 : fetch_word Ubsan.M.loaded_segments (0x3a878 : word) = Some W_3a878.
Proof. vm_refl. Qed.
Lemma D_3a878 : decode_any W_3a878 = Some (Op ALU_SLTU 10 1 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a87c : bv 32 := 0x00a44533.
Lemma F_3a87c : fetch_word Ubsan.M.loaded_segments (0x3a87c : word) = Some W_3a87c.
Proof. vm_refl. Qed.
Lemma D_3a87c : decode_any W_3a87c = Some (Op ALU_XOR 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a880 : bv 32 := 0x00154513.
Lemma F_3a880 : fetch_word Ubsan.M.loaded_segments (0x3a880 : word) = Some W_3a880.
Proof. vm_refl. Qed.
Lemma D_3a880 : decode_any W_3a880 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a884 : bv 32 := 0x1c050a63.
Lemma F_3a884 : fetch_word Ubsan.M.loaded_segments (0x3a884 : word) = Some W_3a884.
Proof. vm_refl. Qed.
Lemma D_3a884 : decode_any W_3a884 = Some (Branch BC_EQ 10 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a888 : bv 32 := 0x1c090863.
Lemma F_3a888 : fetch_word Ubsan.M.loaded_segments (0x3a888 : word) = Some W_3a888.
Proof. vm_refl. Qed.
Lemma D_3a888 : decode_any W_3a888 = Some (Branch BC_EQ 18 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a88c : bv 32 := 0x0070f513.
Lemma F_3a88c : fetch_word Ubsan.M.loaded_segments (0x3a88c : word) = Some W_3a88c.
Proof. vm_refl. Qed.
Lemma D_3a88c : decode_any W_3a88c = Some (OpImm ALU_AND 10 1 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a890 : bv 32 := 0x1c051463.
Lemma F_3a890 : fetch_word Ubsan.M.loaded_segments (0x3a890 : word) = Some W_3a890.
Proof. vm_refl. Qed.
Lemma D_3a890 : decode_any W_3a890 = Some (Branch BC_NE 10 0 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a894 : bv 32 := 0x0000b403.
Lemma F_3a894 : fetch_word Ubsan.M.loaded_segments (0x3a894 : word) = Some W_3a894.
Proof. vm_refl. Qed.
Lemma D_3a894 : decode_any W_3a894 = Some (Load SZ8 true 8 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a898 : bv 32 := 0x01b40db3.
Lemma F_3a898 : fetch_word Ubsan.M.loaded_segments (0x3a898 : word) = Some W_3a898.
Proof. vm_refl. Qed.
Lemma D_3a898 : decode_any W_3a898 = Some (Op ALU_ADD 27 8 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a89c : bv 32 := 0x00803533.
Lemma F_3a89c : fetch_word Ubsan.M.loaded_segments (0x3a89c : word) = Some W_3a89c.
Proof. vm_refl. Qed.
Lemma D_3a89c : decode_any W_3a89c = Some (Op ALU_SLTU 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8a0 : bv 32 := 0x001db913.
Lemma F_3a8a0 : fetch_word Ubsan.M.loaded_segments (0x3a8a0 : word) = Some W_3a8a0.
Proof. vm_refl. Qed.
Lemma D_3a8a0 : decode_any W_3a8a0 = Some (OpImm ALU_SLTU 18 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8a4 : bv 32 := 0x1b250a63.
Lemma F_3a8a4 : fetch_word Ubsan.M.loaded_segments (0x3a8a4 : word) = Some W_3a8a4.
Proof. vm_refl. Qed.
Lemma D_3a8a4 : decode_any W_3a8a4 = Some (Branch BC_EQ 10 18 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8a8 : bv 32 := 0x008db533.
Lemma F_3a8a8 : fetch_word Ubsan.M.loaded_segments (0x3a8a8 : word) = Some W_3a8a8.
Proof. vm_refl. Qed.
Lemma D_3a8a8 : decode_any W_3a8a8 = Some (Op ALU_SLTU 10 27 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8ac : bv 32 := 0x00a9c533.
Lemma F_3a8ac : fetch_word Ubsan.M.loaded_segments (0x3a8ac : word) = Some W_3a8ac.
Proof. vm_refl. Qed.
Lemma D_3a8ac : decode_any W_3a8ac = Some (Op ALU_XOR 10 19 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8b0 : bv 32 := 0x00154513.
Lemma F_3a8b0 : fetch_word Ubsan.M.loaded_segments (0x3a8b0 : word) = Some W_3a8b0.
Proof. vm_refl. Qed.
Lemma D_3a8b0 : decode_any W_3a8b0 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8b4 : bv 32 := 0x1a050263.
Lemma F_3a8b4 : fetch_word Ubsan.M.loaded_segments (0x3a8b4 : word) = Some W_3a8b4.
Proof. vm_refl. Qed.
Lemma D_3a8b4 : decode_any W_3a8b4 = Some (Branch BC_EQ 10 0 420, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8b8 : bv 32 := 0x1afd8063.
Lemma F_3a8b8 : fetch_word Ubsan.M.loaded_segments (0x3a8b8 : word) = Some W_3a8b8.
Proof. vm_refl. Qed.
Lemma D_3a8b8 : decode_any W_3a8b8 = Some (Branch BC_EQ 27 15 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8bc : bv 32 := 0x01ac0d33.
Lemma F_3a8bc : fetch_word Ubsan.M.loaded_segments (0x3a8bc : word) = Some W_3a8bc.
Proof. vm_refl. Qed.
Lemma D_3a8bc : decode_any W_3a8bc = Some (Op ALU_ADD 26 24 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8c0 : bv 32 := 0x198d6c63.
Lemma F_3a8c0 : fetch_word Ubsan.M.loaded_segments (0x3a8c0 : word) = Some W_3a8c0.
Proof. vm_refl. Qed.
Lemma D_3a8c0 : decode_any W_3a8c0 = Some (Branch BC_LTU 26 24 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8c4 : bv 32 := 0x01803533.
Lemma F_3a8c4 : fetch_word Ubsan.M.loaded_segments (0x3a8c4 : word) = Some W_3a8c4.
Proof. vm_refl. Qed.
Lemma D_3a8c4 : decode_any W_3a8c4 = Some (Op ALU_SLTU 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8c8 : bv 32 := 0x001d3413.
Lemma F_3a8c8 : fetch_word Ubsan.M.loaded_segments (0x3a8c8 : word) = Some W_3a8c8.
Proof. vm_refl. Qed.
Lemma D_3a8c8 : decode_any W_3a8c8 = Some (OpImm ALU_SLTU 8 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8cc : bv 32 := 0x00854533.
Lemma F_3a8cc : fetch_word Ubsan.M.loaded_segments (0x3a8cc : word) = Some W_3a8cc.
Proof. vm_refl. Qed.
Lemma D_3a8cc : decode_any W_3a8cc = Some (Op ALU_XOR 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8d0 : bv 32 := 0x18050463.
Lemma F_3a8d0 : fetch_word Ubsan.M.loaded_segments (0x3a8d0 : word) = Some W_3a8d0.
Proof. vm_refl. Qed.
Lemma D_3a8d0 : decode_any W_3a8d0 = Some (Branch BC_EQ 10 0 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8d4 : bv 32 := 0x180c0263.
Lemma F_3a8d4 : fetch_word Ubsan.M.loaded_segments (0x3a8d4 : word) = Some W_3a8d4.
Proof. vm_refl. Qed.
Lemma D_3a8d4 : decode_any W_3a8d4 = Some (Branch BC_EQ 24 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8d8 : bv 32 := 0x003d7513.
Lemma F_3a8d8 : fetch_word Ubsan.M.loaded_segments (0x3a8d8 : word) = Some W_3a8d8.
Proof. vm_refl. Qed.
Lemma D_3a8d8 : decode_any W_3a8d8 = Some (OpImm ALU_AND 10 26 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8dc : bv 32 := 0x16051e63.
Lemma F_3a8dc : fetch_word Ubsan.M.loaded_segments (0x3a8dc : word) = Some W_3a8dc.
Proof. vm_refl. Qed.
Lemma D_3a8dc : decode_any W_3a8dc = Some (Branch BC_NE 10 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8e0 : bv 32 := 0x0034c513.
Lemma F_3a8e0 : fetch_word Ubsan.M.loaded_segments (0x3a8e0 : word) = Some W_3a8e0.
Proof. vm_refl. Qed.
Lemma D_3a8e0 : decode_any W_3a8e0 = Some (OpImm ALU_XOR 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8e4 : bv 32 := 0x003dc413.
Lemma F_3a8e4 : fetch_word Ubsan.M.loaded_segments (0x3a8e4 : word) = Some W_3a8e4.
Proof. vm_refl. Qed.
Lemma D_3a8e4 : decode_any W_3a8e4 = Some (OpImm ALU_XOR 8 27 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8e8 : bv 32 := 0x000d2787.
Lemma F_3a8e8 : fetch_word Ubsan.M.loaded_segments (0x3a8e8 : word) = Some W_3a8e8.
Proof. vm_refl. Qed.
Lemma D_3a8e8 : decode_any W_3a8e8 = Some (FLoad FMT_S 15 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8ec : bv 32 := 0xfffd8497.
Lemma F_3a8ec : fetch_word Ubsan.M.loaded_segments (0x3a8ec : word) = Some W_3a8ec.
Proof. vm_refl. Qed.
Lemma D_3a8ec : decode_any W_3a8ec = Some (Auipc 9 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8f0 : bv 32 := 0xca44b707.
Lemma F_3a8f0 : fetch_word Ubsan.M.loaded_segments (0x3a8f0 : word) = Some W_3a8f0.
Proof. vm_refl. Qed.
Lemma D_3a8f0 : decode_any W_3a8f0 = Some (FLoad FMT_D 14 9 3236, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8f4 : bv 32 := 0xfffd8497.
Lemma F_3a8f4 : fetch_word Ubsan.M.loaded_segments (0x3a8f4 : word) = Some W_3a8f4.
Proof. vm_refl. Qed.
Lemma D_3a8f4 : decode_any W_3a8f4 = Some (Auipc 9 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8f8 : bv 32 := 0xcc44b687.
Lemma F_3a8f8 : fetch_word Ubsan.M.loaded_segments (0x3a8f8 : word) = Some W_3a8f8.
Proof. vm_refl. Qed.
Lemma D_3a8f8 : decode_any W_3a8f8 = Some (FLoad FMT_D 13 9 3268, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a8fc : bv 32 := 0xfffd8497.
Lemma F_3a8fc : fetch_word Ubsan.M.loaded_segments (0x3a8fc : word) = Some W_3a8fc.
Proof. vm_refl. Qed.
Lemma D_3a8fc : decode_any W_3a8fc = Some (Auipc 9 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a900 : bv 32 := 0x00054503.
Lemma F_3a900 : fetch_word Ubsan.M.loaded_segments (0x3a900 : word) = Some W_3a900.
Proof. vm_refl. Qed.
Lemma D_3a900 : decode_any W_3a900 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a904 : bv 32 := 0x00044403.
Lemma F_3a904 : fetch_word Ubsan.M.loaded_segments (0x3a904 : word) = Some W_3a904.
Proof. vm_refl. Qed.
Lemma D_3a904 : decode_any W_3a904 = Some (Load SZ1 false 8 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a908 : bv 32 := 0x42078653.
Lemma F_3a908 : fetch_word Ubsan.M.loaded_segments (0x3a908 : word) = Some W_3a908.
Proof. vm_refl. Qed.
Lemma D_3a908 : decode_any W_3a908 = Some (Fcvt FC_D FC_S 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a90c : bv 32 := 0x0ac77753.
Lemma F_3a90c : fetch_word Ubsan.M.loaded_segments (0x3a90c : word) = Some W_3a90c.
Proof. vm_refl. Qed.
Lemma D_3a90c : decode_any W_3a90c = Some (Fari F_SUB FMT_D 14 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a910 : bv 32 := 0xd2150653.
Lemma F_3a910 : fetch_word Ubsan.M.loaded_segments (0x3a910 : word) = Some W_3a910.
Proof. vm_refl. Qed.
Lemma D_3a910 : decode_any W_3a910 = Some (Fcvt FC_D FC_WU 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a914 : bv 32 := 0xd01475d3.
Lemma F_3a914 : fetch_word Ubsan.M.loaded_segments (0x3a914 : word) = Some W_3a914.
Proof. vm_refl. Qed.
Lemma D_3a914 : decode_any W_3a914 = Some (Fcvt FC_S FC_WU 11 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a918 : bv 32 := 0x10b7f7d3.
Lemma F_3a918 : fetch_word Ubsan.M.loaded_segments (0x3a918 : word) = Some W_3a918.
Proof. vm_refl. Qed.
Lemma D_3a918 : decode_any W_3a918 = Some (Fari F_MUL FMT_S 15 15 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a91c : bv 32 := 0xcd44b587.
Lemma F_3a91c : fetch_word Ubsan.M.loaded_segments (0x3a91c : word) = Some W_3a91c.
Proof. vm_refl. Qed.
Lemma D_3a91c : decode_any W_3a91c = Some (FLoad FMT_D 11 9 3284, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a920 : bv 32 := 0x420787d3.
Lemma F_3a920 : fetch_word Ubsan.M.loaded_segments (0x3a920 : word) = Some W_3a920.
Proof. vm_refl. Qed.
Lemma D_3a920 : decode_any W_3a920 = Some (Fcvt FC_D FC_S 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a924 : bv 32 := 0x7ac777c3.
Lemma F_3a924 : fetch_word Ubsan.M.loaded_segments (0x3a924 : word) = Some W_3a924.
Proof. vm_refl. Qed.
Lemma D_3a924 : decode_any W_3a924 = Some (Fma F_MADD FMT_D 15 14 12 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a928 : bv 32 := 0x02d7f7d3.
Lemma F_3a928 : fetch_word Ubsan.M.loaded_segments (0x3a928 : word) = Some W_3a928.
Proof. vm_refl. Qed.
Lemma D_3a928 : decode_any W_3a928 = Some (Fari F_ADD FMT_D 15 15 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a92c : bv 32 := 0xa2f59553.
Lemma F_3a92c : fetch_word Ubsan.M.loaded_segments (0x3a92c : word) = Some W_3a92c.
Proof. vm_refl. Qed.
Lemma D_3a92c : decode_any W_3a92c = Some (Fcmp F_LT FMT_D 10 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a930 : bv 32 := 0x12050463.
Lemma F_3a930 : fetch_word Ubsan.M.loaded_segments (0x3a930 : word) = Some W_3a930.
Proof. vm_refl. Qed.
Lemma D_3a930 : decode_any W_3a930 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a934 : bv 32 := 0xfffd8517.
Lemma F_3a934 : fetch_word Ubsan.M.loaded_segments (0x3a934 : word) = Some W_3a934.
Proof. vm_refl. Qed.
Lemma D_3a934 : decode_any W_3a934 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a938 : bv 32 := 0xc5453707.
Lemma F_3a938 : fetch_word Ubsan.M.loaded_segments (0x3a938 : word) = Some W_3a938.
Proof. vm_refl. Qed.
Lemma D_3a938 : decode_any W_3a938 = Some (FLoad FMT_D 14 10 3156, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a93c : bv 32 := 0xa2e79553.
Lemma F_3a93c : fetch_word Ubsan.M.loaded_segments (0x3a93c : word) = Some W_3a93c.
Proof. vm_refl. Qed.
Lemma D_3a93c : decode_any W_3a93c = Some (Fcmp F_LT FMT_D 10 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a940 : bv 32 := 0x10050c63.
Lemma F_3a940 : fetch_word Ubsan.M.loaded_segments (0x3a940 : word) = Some W_3a940.
Proof. vm_refl. Qed.
Lemma D_3a940 : decode_any W_3a940 = Some (Branch BC_EQ 10 0 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a944 : bv 32 := 0x111fea63.
Lemma F_3a944 : fetch_word Ubsan.M.loaded_segments (0x3a944 : word) = Some W_3a944.
Proof. vm_refl. Qed.
Lemma D_3a944 : decode_any W_3a944 = Some (Branch BC_LTU 31 17 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a948 : bv 32 := 0x001fb513.
Lemma F_3a948 : fetch_word Ubsan.M.loaded_segments (0x3a948 : word) = Some W_3a948.
Proof. vm_refl. Qed.
Lemma D_3a948 : decode_any W_3a948 = Some (OpImm ALU_SLTU 10 31 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a94c : bv 32 := 0x00a74533.
Lemma F_3a94c : fetch_word Ubsan.M.loaded_segments (0x3a94c : word) = Some W_3a94c.
Proof. vm_refl. Qed.
Lemma D_3a94c : decode_any W_3a94c = Some (Op ALU_XOR 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a950 : bv 32 := 0x10050463.
Lemma F_3a950 : fetch_word Ubsan.M.loaded_segments (0x3a950 : word) = Some W_3a950.
Proof. vm_refl. Qed.
Lemma D_3a950 : decode_any W_3a950 = Some (Branch BC_EQ 10 0 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a954 : bv 32 := 0x10fe0263.
Lemma F_3a954 : fetch_word Ubsan.M.loaded_segments (0x3a954 : word) = Some W_3a954.
Proof. vm_refl. Qed.
Lemma D_3a954 : decode_any W_3a954 = Some (Branch BC_EQ 28 15 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a958 : bv 32 := 0xc2079553.
Lemma F_3a958 : fetch_word Ubsan.M.loaded_segments (0x3a958 : word) = Some W_3a958.
Proof. vm_refl. Qed.
Lemma D_3a958 : decode_any W_3a958 = Some (Fcvt FC_W FC_D 10 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a95c : bv 32 := 0x003fc413.
Lemma F_3a95c : fetch_word Ubsan.M.loaded_segments (0x3a95c : word) = Some W_3a95c.
Proof. vm_refl. Qed.
Lemma D_3a95c : decode_any W_3a95c = Some (OpImm ALU_XOR 8 31 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a960 : bv 32 := 0x00130313.
Lemma F_3a960 : fetch_word Ubsan.M.loaded_segments (0x3a960 : word) = Some W_3a960.
Proof. vm_refl. Qed.
Lemma D_3a960 : decode_any W_3a960 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a964 : bv 32 := 0x00a40023.
Lemma F_3a964 : fetch_word Ubsan.M.loaded_segments (0x3a964 : word) = Some W_3a964.
Proof. vm_refl. Qed.
Lemma D_3a964 : decode_any W_3a964 = Some (Store SZ1 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a968 : bv 32 := 0x03412503.
Lemma F_3a968 : fetch_word Ubsan.M.loaded_segments (0x3a968 : word) = Some W_3a968.
Proof. vm_refl. Qed.
Lemma D_3a968 : decode_any W_3a968 = Some (Load SZ4 true 10 2 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a96c : bv 32 := 0x00128293.
Lemma F_3a96c : fetch_word Ubsan.M.loaded_segments (0x3a96c : word) = Some W_3a96c.
Proof. vm_refl. Qed.
Lemma D_3a96c : decode_any W_3a96c = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a970 : bv 32 := 0x001a8a93.
Lemma F_3a970 : fetch_word Ubsan.M.loaded_segments (0x3a970 : word) = Some W_3a970.
Proof. vm_refl. Qed.
Lemma D_3a970 : decode_any W_3a970 = Some (OpImm ALU_ADD 21 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a974 : bv 32 := 0x001f8f93.
Lemma F_3a974 : fetch_word Ubsan.M.loaded_segments (0x3a974 : word) = Some W_3a974.
Proof. vm_refl. Qed.
Lemma D_3a974 : decode_any W_3a974 = Some (OpImm ALU_ADD 31 31 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a978 : bv 32 := 0x001e0e13.
Lemma F_3a978 : fetch_word Ubsan.M.loaded_segments (0x3a978 : word) = Some W_3a978.
Proof. vm_refl. Qed.
Lemma D_3a978 : decode_any W_3a978 = Some (OpImm ALU_ADD 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a97c : bv 32 := 0x00138393.
Lemma F_3a97c : fetch_word Ubsan.M.loaded_segments (0x3a97c : word) = Some W_3a97c.
Proof. vm_refl. Qed.
Lemma D_3a97c : decode_any W_3a97c = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a980 : bv 32 := 0xdca34ee3.
Lemma F_3a980 : fetch_word Ubsan.M.loaded_segments (0x3a980 : word) = Some W_3a980.
Proof. vm_refl. Qed.
Lemma D_3a980 : decode_any W_3a980 = Some (Branch BC_LT 6 10 7644, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a984 : bv 32 := 0xcf9ff06f.
Lemma F_3a984 : fetch_word Ubsan.M.loaded_segments (0x3a984 : word) = Some W_3a984.
Proof. vm_refl. Qed.
Lemma D_3a984 : decode_any W_3a984 = Some (Jal 0 2096376, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a988 : bv 32 := 0x0000a517.
Lemma F_3a988 : fetch_word Ubsan.M.loaded_segments (0x3a988 : word) = Some W_3a988.
Proof. vm_refl. Qed.
Lemma D_3a988 : decode_any W_3a988 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a98c : bv 32 := 0x51053503.
Lemma F_3a98c : fetch_word Ubsan.M.loaded_segments (0x3a98c : word) = Some W_3a98c.
Proof. vm_refl. Qed.
Lemma D_3a98c : decode_any W_3a98c = Some (Load SZ8 true 10 10 1296, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a990 : bv 32 := 0x00052503.
Lemma F_3a990 : fetch_word Ubsan.M.loaded_segments (0x3a990 : word) = Some W_3a990.
Proof. vm_refl. Qed.
Lemma D_3a990 : decode_any W_3a990 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a994 : bv 32 := 0x00600593.
Lemma F_3a994 : fetch_word Ubsan.M.loaded_segments (0x3a994 : word) = Some W_3a994.
Proof. vm_refl. Qed.
Lemma D_3a994 : decode_any W_3a994 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a998 : bv 32 := 0x06b55e63.
Lemma F_3a998 : fetch_word Ubsan.M.loaded_segments (0x3a998 : word) = Some W_3a998.
Proof. vm_refl. Qed.
Lemma D_3a998 : decode_any W_3a998 = Some (Branch BC_GE 10 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a99c : bv 32 := 0xfffd6517.
Lemma F_3a99c : fetch_word Ubsan.M.loaded_segments (0x3a99c : word) = Some W_3a99c.
Proof. vm_refl. Qed.
Lemma D_3a99c : decode_any W_3a99c = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9a0 : bv 32 := 0xab150513.
Lemma F_3a9a0 : fetch_word Ubsan.M.loaded_segments (0x3a9a0 : word) = Some W_3a9a0.
Proof. vm_refl. Qed.
Lemma D_3a9a0 : decode_any W_3a9a0 = Some (OpImm ALU_ADD 10 10 2737, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9a4 : bv 32 := 0x0280006f.
Lemma F_3a9a4 : fetch_word Ubsan.M.loaded_segments (0x3a9a4 : word) = Some W_3a9a4.
Proof. vm_refl. Qed.
Lemma D_3a9a4 : decode_any W_3a9a4 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9a8 : bv 32 := 0x00013403.
Lemma F_3a9a8 : fetch_word Ubsan.M.loaded_segments (0x3a9a8 : word) = Some W_3a9a8.
Proof. vm_refl. Qed.
Lemma D_3a9a8 : decode_any W_3a9a8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9ac : bv 32 := 0x06c0006f.
Lemma F_3a9ac : fetch_word Ubsan.M.loaded_segments (0x3a9ac : word) = Some W_3a9ac.
Proof. vm_refl. Qed.
Lemma D_3a9ac : decode_any W_3a9ac = Some (Jal 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9b0 : bv 32 := 0x0000a517.
Lemma F_3a9b0 : fetch_word Ubsan.M.loaded_segments (0x3a9b0 : word) = Some W_3a9b0.
Proof. vm_refl. Qed.
Lemma D_3a9b0 : decode_any W_3a9b0 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9b4 : bv 32 := 0x4e853503.
Lemma F_3a9b4 : fetch_word Ubsan.M.loaded_segments (0x3a9b4 : word) = Some W_3a9b4.
Proof. vm_refl. Qed.
Lemma D_3a9b4 : decode_any W_3a9b4 = Some (Load SZ8 true 10 10 1256, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9b8 : bv 32 := 0x00052503.
Lemma F_3a9b8 : fetch_word Ubsan.M.loaded_segments (0x3a9b8 : word) = Some W_3a9b8.
Proof. vm_refl. Qed.
Lemma D_3a9b8 : decode_any W_3a9b8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9bc : bv 32 := 0x00600593.
Lemma F_3a9bc : fetch_word Ubsan.M.loaded_segments (0x3a9bc : word) = Some W_3a9bc.
Proof. vm_refl. Qed.
Lemma D_3a9bc : decode_any W_3a9bc = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9c0 : bv 32 := 0x04b55a63.
Lemma F_3a9c0 : fetch_word Ubsan.M.loaded_segments (0x3a9c0 : word) = Some W_3a9c0.
Proof. vm_refl. Qed.
Lemma D_3a9c0 : decode_any W_3a9c0 = Some (Branch BC_GE 10 11 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9c4 : bv 32 := 0xfffd6517.
Lemma F_3a9c4 : fetch_word Ubsan.M.loaded_segments (0x3a9c4 : word) = Some W_3a9c4.
Proof. vm_refl. Qed.
Lemma D_3a9c4 : decode_any W_3a9c4 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9c8 : bv 32 := 0xda150513.
Lemma F_3a9c8 : fetch_word Ubsan.M.loaded_segments (0x3a9c8 : word) = Some W_3a9c8.
Proof. vm_refl. Qed.
Lemma D_3a9c8 : decode_any W_3a9c8 = Some (OpImm ALU_ADD 10 10 3489, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9cc : bv 32 := 0xfffd7597.
Lemma F_3a9cc : fetch_word Ubsan.M.loaded_segments (0x3a9cc : word) = Some W_3a9cc.
Proof. vm_refl. Qed.
Lemma D_3a9cc : decode_any W_3a9cc = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9d0 : bv 32 := 0xad358593.
Lemma F_3a9d0 : fetch_word Ubsan.M.loaded_segments (0x3a9d0 : word) = Some W_3a9d0.
Proof. vm_refl. Qed.
Lemma D_3a9d0 : decode_any W_3a9d0 = Some (OpImm ALU_ADD 11 11 2771, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9d4 : bv 32 := 0x00000613.
Lemma F_3a9d4 : fetch_word Ubsan.M.loaded_segments (0x3a9d4 : word) = Some W_3a9d4.
Proof. vm_refl. Qed.
Lemma D_3a9d4 : decode_any W_3a9d4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9d8 : bv 32 := 0x09813083.
Lemma F_3a9d8 : fetch_word Ubsan.M.loaded_segments (0x3a9d8 : word) = Some W_3a9d8.
Proof. vm_refl. Qed.
Lemma D_3a9d8 : decode_any W_3a9d8 = Some (Load SZ8 true 1 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9dc : bv 32 := 0x09013403.
Lemma F_3a9dc : fetch_word Ubsan.M.loaded_segments (0x3a9dc : word) = Some W_3a9dc.
Proof. vm_refl. Qed.
Lemma D_3a9dc : decode_any W_3a9dc = Some (Load SZ8 true 8 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9e0 : bv 32 := 0x08813483.
Lemma F_3a9e0 : fetch_word Ubsan.M.loaded_segments (0x3a9e0 : word) = Some W_3a9e0.
Proof. vm_refl. Qed.
Lemma D_3a9e0 : decode_any W_3a9e0 = Some (Load SZ8 true 9 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9e4 : bv 32 := 0x08013903.
Lemma F_3a9e4 : fetch_word Ubsan.M.loaded_segments (0x3a9e4 : word) = Some W_3a9e4.
Proof. vm_refl. Qed.
Lemma D_3a9e4 : decode_any W_3a9e4 = Some (Load SZ8 true 18 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9e8 : bv 32 := 0x07813983.
Lemma F_3a9e8 : fetch_word Ubsan.M.loaded_segments (0x3a9e8 : word) = Some W_3a9e8.
Proof. vm_refl. Qed.
Lemma D_3a9e8 : decode_any W_3a9e8 = Some (Load SZ8 true 19 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9ec : bv 32 := 0x07013a03.
Lemma F_3a9ec : fetch_word Ubsan.M.loaded_segments (0x3a9ec : word) = Some W_3a9ec.
Proof. vm_refl. Qed.
Lemma D_3a9ec : decode_any W_3a9ec = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9f0 : bv 32 := 0x06813a83.
Lemma F_3a9f0 : fetch_word Ubsan.M.loaded_segments (0x3a9f0 : word) = Some W_3a9f0.
Proof. vm_refl. Qed.
Lemma D_3a9f0 : decode_any W_3a9f0 = Some (Load SZ8 true 21 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9f4 : bv 32 := 0x06013b03.
Lemma F_3a9f4 : fetch_word Ubsan.M.loaded_segments (0x3a9f4 : word) = Some W_3a9f4.
Proof. vm_refl. Qed.
Lemma D_3a9f4 : decode_any W_3a9f4 = Some (Load SZ8 true 22 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9f8 : bv 32 := 0x05813b83.
Lemma F_3a9f8 : fetch_word Ubsan.M.loaded_segments (0x3a9f8 : word) = Some W_3a9f8.
Proof. vm_refl. Qed.
Lemma D_3a9f8 : decode_any W_3a9f8 = Some (Load SZ8 true 23 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a9fc : bv 32 := 0x05013c03.
Lemma F_3a9fc : fetch_word Ubsan.M.loaded_segments (0x3a9fc : word) = Some W_3a9fc.
Proof. vm_refl. Qed.
Lemma D_3a9fc : decode_any W_3a9fc = Some (Load SZ8 true 24 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa00 : bv 32 := 0x04813c83.
Lemma F_3aa00 : fetch_word Ubsan.M.loaded_segments (0x3aa00 : word) = Some W_3aa00.
Proof. vm_refl. Qed.
Lemma D_3aa00 : decode_any W_3aa00 = Some (Load SZ8 true 25 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa04 : bv 32 := 0x04013d03.
Lemma F_3aa04 : fetch_word Ubsan.M.loaded_segments (0x3aa04 : word) = Some W_3aa04.
Proof. vm_refl. Qed.
Lemma D_3aa04 : decode_any W_3aa04 = Some (Load SZ8 true 26 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa08 : bv 32 := 0x03813d83.
Lemma F_3aa08 : fetch_word Ubsan.M.loaded_segments (0x3aa08 : word) = Some W_3aa08.
Proof. vm_refl. Qed.
Lemma D_3aa08 : decode_any W_3aa08 = Some (Load SZ8 true 27 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa0c : bv 32 := 0x0a010113.
Lemma F_3aa0c : fetch_word Ubsan.M.loaded_segments (0x3aa0c : word) = Some W_3aa0c.
Proof. vm_refl. Qed.
Lemma D_3aa0c : decode_any W_3aa0c = Some (OpImm ALU_ADD 2 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa10 : bv 32 := 0xcb4dd06f.
Lemma F_3aa10 : fetch_word Ubsan.M.loaded_segments (0x3aa10 : word) = Some W_3aa10.
Proof. vm_refl. Qed.
Lemma D_3aa10 : decode_any W_3aa10 = Some (Jal 0 1954996, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa14 : bv 32 := 0x00000413.
Lemma F_3aa14 : fetch_word Ubsan.M.loaded_segments (0x3aa14 : word) = Some W_3aa14.
Proof. vm_refl. Qed.
Lemma D_3aa14 : decode_any W_3aa14 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa18 : bv 32 := 0x00040513.
Lemma F_3aa18 : fetch_word Ubsan.M.loaded_segments (0x3aa18 : word) = Some W_3aa18.
Proof. vm_refl. Qed.
Lemma D_3aa18 : decode_any W_3aa18 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa1c : bv 32 := 0x09813083.
Lemma F_3aa1c : fetch_word Ubsan.M.loaded_segments (0x3aa1c : word) = Some W_3aa1c.
Proof. vm_refl. Qed.
Lemma D_3aa1c : decode_any W_3aa1c = Some (Load SZ8 true 1 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa20 : bv 32 := 0x09013403.
Lemma F_3aa20 : fetch_word Ubsan.M.loaded_segments (0x3aa20 : word) = Some W_3aa20.
Proof. vm_refl. Qed.
Lemma D_3aa20 : decode_any W_3aa20 = Some (Load SZ8 true 8 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa24 : bv 32 := 0x08813483.
Lemma F_3aa24 : fetch_word Ubsan.M.loaded_segments (0x3aa24 : word) = Some W_3aa24.
Proof. vm_refl. Qed.
Lemma D_3aa24 : decode_any W_3aa24 = Some (Load SZ8 true 9 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa28 : bv 32 := 0x08013903.
Lemma F_3aa28 : fetch_word Ubsan.M.loaded_segments (0x3aa28 : word) = Some W_3aa28.
Proof. vm_refl. Qed.
Lemma D_3aa28 : decode_any W_3aa28 = Some (Load SZ8 true 18 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa2c : bv 32 := 0x07813983.
Lemma F_3aa2c : fetch_word Ubsan.M.loaded_segments (0x3aa2c : word) = Some W_3aa2c.
Proof. vm_refl. Qed.
Lemma D_3aa2c : decode_any W_3aa2c = Some (Load SZ8 true 19 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa30 : bv 32 := 0x07013a03.
Lemma F_3aa30 : fetch_word Ubsan.M.loaded_segments (0x3aa30 : word) = Some W_3aa30.
Proof. vm_refl. Qed.
Lemma D_3aa30 : decode_any W_3aa30 = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa34 : bv 32 := 0x06813a83.
Lemma F_3aa34 : fetch_word Ubsan.M.loaded_segments (0x3aa34 : word) = Some W_3aa34.
Proof. vm_refl. Qed.
Lemma D_3aa34 : decode_any W_3aa34 = Some (Load SZ8 true 21 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa38 : bv 32 := 0x06013b03.
Lemma F_3aa38 : fetch_word Ubsan.M.loaded_segments (0x3aa38 : word) = Some W_3aa38.
Proof. vm_refl. Qed.
Lemma D_3aa38 : decode_any W_3aa38 = Some (Load SZ8 true 22 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa3c : bv 32 := 0x05813b83.
Lemma F_3aa3c : fetch_word Ubsan.M.loaded_segments (0x3aa3c : word) = Some W_3aa3c.
Proof. vm_refl. Qed.
Lemma D_3aa3c : decode_any W_3aa3c = Some (Load SZ8 true 23 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa40 : bv 32 := 0x05013c03.
Lemma F_3aa40 : fetch_word Ubsan.M.loaded_segments (0x3aa40 : word) = Some W_3aa40.
Proof. vm_refl. Qed.
Lemma D_3aa40 : decode_any W_3aa40 = Some (Load SZ8 true 24 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa44 : bv 32 := 0x04813c83.
Lemma F_3aa44 : fetch_word Ubsan.M.loaded_segments (0x3aa44 : word) = Some W_3aa44.
Proof. vm_refl. Qed.
Lemma D_3aa44 : decode_any W_3aa44 = Some (Load SZ8 true 25 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa48 : bv 32 := 0x04013d03.
Lemma F_3aa48 : fetch_word Ubsan.M.loaded_segments (0x3aa48 : word) = Some W_3aa48.
Proof. vm_refl. Qed.
Lemma D_3aa48 : decode_any W_3aa48 = Some (Load SZ8 true 26 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa4c : bv 32 := 0x03813d83.
Lemma F_3aa4c : fetch_word Ubsan.M.loaded_segments (0x3aa4c : word) = Some W_3aa4c.
Proof. vm_refl. Qed.
Lemma D_3aa4c : decode_any W_3aa4c = Some (Load SZ8 true 27 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa50 : bv 32 := 0x0a010113.
Lemma F_3aa50 : fetch_word Ubsan.M.loaded_segments (0x3aa50 : word) = Some W_3aa50.
Proof. vm_refl. Qed.
Lemma D_3aa50 : decode_any W_3aa50 = Some (OpImm ALU_ADD 2 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa54 : bv 32 := 0x00008067.
Lemma F_3aa54 : fetch_word Ubsan.M.loaded_segments (0x3aa54 : word) = Some W_3aa54.
Proof. vm_refl. Qed.
Lemma D_3aa54 : decode_any W_3aa54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa58 : bv 32 := 0xc0001073.
Lemma F_3aa58 : fetch_word Ubsan.M.loaded_segments (0x3aa58 : word) = Some W_3aa58.
Proof. vm_refl. Qed.
Lemma D_3aa58 : decode_any W_3aa58 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
