(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a5590 : bv 32 := 0xf8010113.
Lemma F_a5590 : fetch_word Ubsan.M.loaded_segments (0xa5590 : word) = Some W_a5590.
Proof. vm_refl. Qed.
Lemma D_a5590 : decode_any W_a5590 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5594 : bv 32 := 0x06113c23.
Lemma F_a5594 : fetch_word Ubsan.M.loaded_segments (0xa5594 : word) = Some W_a5594.
Proof. vm_refl. Qed.
Lemma D_a5594 : decode_any W_a5594 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5598 : bv 32 := 0x06813823.
Lemma F_a5598 : fetch_word Ubsan.M.loaded_segments (0xa5598 : word) = Some W_a5598.
Proof. vm_refl. Qed.
Lemma D_a5598 : decode_any W_a5598 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a559c : bv 32 := 0x06913423.
Lemma F_a559c : fetch_word Ubsan.M.loaded_segments (0xa559c : word) = Some W_a559c.
Proof. vm_refl. Qed.
Lemma D_a559c : decode_any W_a559c = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55a0 : bv 32 := 0x07213023.
Lemma F_a55a0 : fetch_word Ubsan.M.loaded_segments (0xa55a0 : word) = Some W_a55a0.
Proof. vm_refl. Qed.
Lemma D_a55a0 : decode_any W_a55a0 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55a4 : bv 32 := 0x05313c23.
Lemma F_a55a4 : fetch_word Ubsan.M.loaded_segments (0xa55a4 : word) = Some W_a55a4.
Proof. vm_refl. Qed.
Lemma D_a55a4 : decode_any W_a55a4 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55a8 : bv 32 := 0x05413823.
Lemma F_a55a8 : fetch_word Ubsan.M.loaded_segments (0xa55a8 : word) = Some W_a55a8.
Proof. vm_refl. Qed.
Lemma D_a55a8 : decode_any W_a55a8 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55ac : bv 32 := 0x05513423.
Lemma F_a55ac : fetch_word Ubsan.M.loaded_segments (0xa55ac : word) = Some W_a55ac.
Proof. vm_refl. Qed.
Lemma D_a55ac : decode_any W_a55ac = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55b0 : bv 32 := 0x05613023.
Lemma F_a55b0 : fetch_word Ubsan.M.loaded_segments (0xa55b0 : word) = Some W_a55b0.
Proof. vm_refl. Qed.
Lemma D_a55b0 : decode_any W_a55b0 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55b4 : bv 32 := 0x03713c23.
Lemma F_a55b4 : fetch_word Ubsan.M.loaded_segments (0xa55b4 : word) = Some W_a55b4.
Proof. vm_refl. Qed.
Lemma D_a55b4 : decode_any W_a55b4 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55b8 : bv 32 := 0x03813823.
Lemma F_a55b8 : fetch_word Ubsan.M.loaded_segments (0xa55b8 : word) = Some W_a55b8.
Proof. vm_refl. Qed.
Lemma D_a55b8 : decode_any W_a55b8 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55bc : bv 32 := 0x03913423.
Lemma F_a55bc : fetch_word Ubsan.M.loaded_segments (0xa55bc : word) = Some W_a55bc.
Proof. vm_refl. Qed.
Lemma D_a55bc : decode_any W_a55bc = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55c0 : bv 32 := 0x03a13023.
Lemma F_a55c0 : fetch_word Ubsan.M.loaded_segments (0xa55c0 : word) = Some W_a55c0.
Proof. vm_refl. Qed.
Lemma D_a55c0 : decode_any W_a55c0 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55c4 : bv 32 := 0x01b13c23.
Lemma F_a55c4 : fetch_word Ubsan.M.loaded_segments (0xa55c4 : word) = Some W_a55c4.
Proof. vm_refl. Qed.
Lemma D_a55c4 : decode_any W_a55c4 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55c8 : bv 32 := 0x1c058663.
Lemma F_a55c8 : fetch_word Ubsan.M.loaded_segments (0xa55c8 : word) = Some W_a55c8.
Proof. vm_refl. Qed.
Lemma D_a55c8 : decode_any W_a55c8 = Some (Branch BC_EQ 11 0 460, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55cc : bv 32 := 0x1c060463.
Lemma F_a55cc : fetch_word Ubsan.M.loaded_segments (0xa55cc : word) = Some W_a55cc.
Proof. vm_refl. Qed.
Lemma D_a55cc : decode_any W_a55cc = Some (Branch BC_EQ 12 0 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55d0 : bv 32 := 0x1c068263.
Lemma F_a55d0 : fetch_word Ubsan.M.loaded_segments (0xa55d0 : word) = Some W_a55d0.
Proof. vm_refl. Qed.
Lemma D_a55d0 : decode_any W_a55d0 = Some (Branch BC_EQ 13 0 452, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55d4 : bv 32 := 0x1c070063.
Lemma F_a55d4 : fetch_word Ubsan.M.loaded_segments (0xa55d4 : word) = Some W_a55d4.
Proof. vm_refl. Qed.
Lemma D_a55d4 : decode_any W_a55d4 = Some (Branch BC_EQ 14 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55d8 : bv 32 := 0x00d13823.
Lemma F_a55d8 : fetch_word Ubsan.M.loaded_segments (0xa55d8 : word) = Some W_a55d8.
Proof. vm_refl. Qed.
Lemma D_a55d8 : decode_any W_a55d8 = Some (Store SZ8 2 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55dc : bv 32 := 0x00e13423.
Lemma F_a55dc : fetch_word Ubsan.M.loaded_segments (0xa55dc : word) = Some W_a55dc.
Proof. vm_refl. Qed.
Lemma D_a55dc : decode_any W_a55dc = Some (Store SZ8 2 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55e0 : bv 32 := 0x00377693.
Lemma F_a55e0 : fetch_word Ubsan.M.loaded_segments (0xa55e0 : word) = Some W_a55e0.
Proof. vm_refl. Qed.
Lemma D_a55e0 : decode_any W_a55e0 = Some (OpImm ALU_AND 13 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55e4 : bv 32 := 0x2a069663.
Lemma F_a55e4 : fetch_word Ubsan.M.loaded_segments (0xa55e4 : word) = Some W_a55e4.
Proof. vm_refl. Qed.
Lemma D_a55e4 : decode_any W_a55e4 = Some (Branch BC_NE 13 0 684, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55e8 : bv 32 := 0x01013683.
Lemma F_a55e8 : fetch_word Ubsan.M.loaded_segments (0xa55e8 : word) = Some W_a55e8.
Proof. vm_refl. Qed.
Lemma D_a55e8 : decode_any W_a55e8 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55ec : bv 32 := 0x0036f693.
Lemma F_a55ec : fetch_word Ubsan.M.loaded_segments (0xa55ec : word) = Some W_a55ec.
Proof. vm_refl. Qed.
Lemma D_a55ec : decode_any W_a55ec = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55f0 : bv 32 := 0x00813703.
Lemma F_a55f0 : fetch_word Ubsan.M.loaded_segments (0xa55f0 : word) = Some W_a55f0.
Proof. vm_refl. Qed.
Lemma D_a55f0 : decode_any W_a55f0 = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55f4 : bv 32 := 0x00072023.
Lemma F_a55f4 : fetch_word Ubsan.M.loaded_segments (0xa55f4 : word) = Some W_a55f4.
Proof. vm_refl. Qed.
Lemma D_a55f4 : decode_any W_a55f4 = Some (Store SZ4 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55f8 : bv 32 := 0x28069c63.
Lemma F_a55f8 : fetch_word Ubsan.M.loaded_segments (0xa55f8 : word) = Some W_a55f8.
Proof. vm_refl. Qed.
Lemma D_a55f8 : decode_any W_a55f8 = Some (Branch BC_NE 13 0 664, 4%Z).
Proof. vm_refl. Qed.

Definition W_a55fc : bv 32 := 0x00367693.
Lemma F_a55fc : fetch_word Ubsan.M.loaded_segments (0xa55fc : word) = Some W_a55fc.
Proof. vm_refl. Qed.
Lemma D_a55fc : decode_any W_a55fc = Some (OpImm ALU_AND 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5600 : bv 32 := 0x01013703.
Lemma F_a5600 : fetch_word Ubsan.M.loaded_segments (0xa5600 : word) = Some W_a5600.
Proof. vm_refl. Qed.
Lemma D_a5600 : decode_any W_a5600 = Some (Load SZ8 true 14 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5604 : bv 32 := 0x00072023.
Lemma F_a5604 : fetch_word Ubsan.M.loaded_segments (0xa5604 : word) = Some W_a5604.
Proof. vm_refl. Qed.
Lemma D_a5604 : decode_any W_a5604 = Some (Store SZ4 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5608 : bv 32 := 0x28069463.
Lemma F_a5608 : fetch_word Ubsan.M.loaded_segments (0xa5608 : word) = Some W_a5608.
Proof. vm_refl. Qed.
Lemma D_a5608 : decode_any W_a5608 = Some (Branch BC_NE 13 0 648, 4%Z).
Proof. vm_refl. Qed.

Definition W_a560c : bv 32 := 0x0035f693.
Lemma F_a560c : fetch_word Ubsan.M.loaded_segments (0xa560c : word) = Some W_a560c.
Proof. vm_refl. Qed.
Lemma D_a560c : decode_any W_a560c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5610 : bv 32 := 0x00062023.
Lemma F_a5610 : fetch_word Ubsan.M.loaded_segments (0xa5610 : word) = Some W_a5610.
Proof. vm_refl. Qed.
Lemma D_a5610 : decode_any W_a5610 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5614 : bv 32 := 0x26069e63.
Lemma F_a5614 : fetch_word Ubsan.M.loaded_segments (0xa5614 : word) = Some W_a5614.
Proof. vm_refl. Qed.
Lemma D_a5614 : decode_any W_a5614 = Some (Branch BC_NE 13 0 636, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5618 : bv 32 := 0x0005a023.
Lemma F_a5618 : fetch_word Ubsan.M.loaded_segments (0xa5618 : word) = Some W_a5618.
Proof. vm_refl. Qed.
Lemma D_a5618 : decode_any W_a5618 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a561c : bv 32 := 0x1a050063.
Lemma F_a561c : fetch_word Ubsan.M.loaded_segments (0xa561c : word) = Some W_a561c.
Proof. vm_refl. Qed.
Lemma D_a561c : decode_any W_a561c = Some (Branch BC_EQ 10 0 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5620 : bv 32 := 0x00757693.
Lemma F_a5620 : fetch_word Ubsan.M.loaded_segments (0xa5620 : word) = Some W_a5620.
Proof. vm_refl. Qed.
Lemma D_a5620 : decode_any W_a5620 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5624 : bv 32 := 0x26069663.
Lemma F_a5624 : fetch_word Ubsan.M.loaded_segments (0xa5624 : word) = Some W_a5624.
Proof. vm_refl. Qed.
Lemma D_a5624 : decode_any W_a5624 = Some (Branch BC_NE 13 0 620, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5628 : bv 32 := 0x00052f83.
Lemma F_a5628 : fetch_word Ubsan.M.loaded_segments (0xa5628 : word) = Some W_a5628.
Proof. vm_refl. Qed.
Lemma D_a5628 : decode_any W_a5628 = Some (Load SZ4 true 31 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a562c : bv 32 := 0x1ff05e63.
Lemma F_a562c : fetch_word Ubsan.M.loaded_segments (0xa562c : word) = Some W_a562c.
Proof. vm_refl. Qed.
Lemma D_a562c : decode_any W_a562c = Some (Branch BC_GE 0 31 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5630 : bv 32 := 0x00000793.
Lemma F_a5630 : fetch_word Ubsan.M.loaded_segments (0xa5630 : word) = Some W_a5630.
Proof. vm_refl. Qed.
Lemma D_a5630 : decode_any W_a5630 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5634 : bv 32 := 0x00000813.
Lemma F_a5634 : fetch_word Ubsan.M.loaded_segments (0xa5634 : word) = Some W_a5634.
Proof. vm_refl. Qed.
Lemma D_a5634 : decode_any W_a5634 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5638 : bv 32 := 0x00000713.
Lemma F_a5638 : fetch_word Ubsan.M.loaded_segments (0xa5638 : word) = Some W_a5638.
Proof. vm_refl. Qed.
Lemma D_a5638 : decode_any W_a5638 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a563c : bv 32 := 0x00000293.
Lemma F_a563c : fetch_word Ubsan.M.loaded_segments (0xa563c : word) = Some W_a563c.
Proof. vm_refl. Qed.
Lemma D_a563c : decode_any W_a563c = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5640 : bv 32 := 0x00000313.
Lemma F_a5640 : fetch_word Ubsan.M.loaded_segments (0xa5640 : word) = Some W_a5640.
Proof. vm_refl. Qed.
Lemma D_a5640 : decode_any W_a5640 = Some (OpImm ALU_ADD 6 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5644 : bv 32 := 0x00456683.
Lemma F_a5644 : fetch_word Ubsan.M.loaded_segments (0xa5644 : word) = Some W_a5644.
Proof. vm_refl. Qed.
Lemma D_a5644 : decode_any W_a5644 = Some (Load SZ4 false 13 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5648 : bv 32 := 0x00852e03.
Lemma F_a5648 : fetch_word Ubsan.M.loaded_segments (0xa5648 : word) = Some W_a5648.
Proof. vm_refl. Qed.
Lemma D_a5648 : decode_any W_a5648 = Some (Load SZ4 true 28 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a564c : bv 32 := 0x00c52e83.
Lemma F_a564c : fetch_word Ubsan.M.loaded_segments (0xa564c : word) = Some W_a564c.
Proof. vm_refl. Qed.
Lemma D_a564c : decode_any W_a564c = Some (Load SZ4 true 29 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5650 : bv 32 := 0x01f028b3.
Lemma F_a5650 : fetch_word Ubsan.M.loaded_segments (0xa5650 : word) = Some W_a5650.
Proof. vm_refl. Qed.
Lemma D_a5650 : decode_any W_a5650 = Some (Op ALU_SLT 17 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5654 : bv 32 := 0x00100f13.
Lemma F_a5654 : fetch_word Ubsan.M.loaded_segments (0xa5654 : word) = Some W_a5654.
Proof. vm_refl. Qed.
Lemma D_a5654 : decode_any W_a5654 = Some (OpImm ALU_ADD 30 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5658 : bv 32 := 0x800004b7.
Lemma F_a5658 : fetch_word Ubsan.M.loaded_segments (0xa5658 : word) = Some W_a5658.
Proof. vm_refl. Qed.
Lemma D_a5658 : decode_any W_a5658 = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_a565c : bv 32 := 0x411008b3.
Lemma F_a565c : fetch_word Ubsan.M.loaded_segments (0xa565c : word) = Some W_a565c.
Proof. vm_refl. Qed.
Lemma D_a565c : decode_any W_a565c = Some (Op ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5660 : bv 32 := 0x01f8ffb3.
Lemma F_a5660 : fetch_word Ubsan.M.loaded_segments (0xa5660 : word) = Some W_a5660.
Proof. vm_refl. Qed.
Lemma D_a5660 : decode_any W_a5660 = Some (Op ALU_AND 31 17 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5664 : bv 32 := 0x0006841b.
Lemma F_a5664 : fetch_word Ubsan.M.loaded_segments (0xa5664 : word) = Some W_a5664.
Proof. vm_refl. Qed.
Lemma D_a5664 : decode_any W_a5664 = Some (OpImm32 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5668 : bv 32 := 0xfff4849b.
Lemma F_a5668 : fetch_word Ubsan.M.loaded_segments (0xa5668 : word) = Some W_a5668.
Proof. vm_refl. Qed.
Lemma D_a5668 : decode_any W_a5668 = Some (OpImm32 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a566c : bv 32 := 0x10805c63.
Lemma F_a566c : fetch_word Ubsan.M.loaded_segments (0xa566c : word) = Some W_a566c.
Proof. vm_refl. Qed.
Lemma D_a566c : decode_any W_a566c = Some (Branch BC_GE 0 8 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5670 : bv 32 := 0x01053383.
Lemma F_a5670 : fetch_word Ubsan.M.loaded_segments (0xa5670 : word) = Some W_a5670.
Proof. vm_refl. Qed.
Lemma D_a5670 : decode_any W_a5670 = Some (Load SZ8 true 7 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5674 : bv 32 := 0x00331993.
Lemma F_a5674 : fetch_word Ubsan.M.loaded_segments (0xa5674 : word) = Some W_a5674.
Proof. vm_refl. Qed.
Lemma D_a5674 : decode_any W_a5674 = Some (ShiftImm ALU_SLL 19 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5678 : bv 32 := 0x013389b3.
Lemma F_a5678 : fetch_word Ubsan.M.loaded_segments (0xa5678 : word) = Some W_a5678.
Proof. vm_refl. Qed.
Lemma D_a5678 : decode_any W_a5678 = Some (Op ALU_ADD 19 7 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_a567c : bv 32 := 0x007038b3.
Lemma F_a567c : fetch_word Ubsan.M.loaded_segments (0xa567c : word) = Some W_a567c.
Proof. vm_refl. Qed.
Lemma D_a567c : decode_any W_a567c = Some (Op ALU_SLTU 17 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5680 : bv 32 := 0x0019b913.
Lemma F_a5680 : fetch_word Ubsan.M.loaded_segments (0xa5680 : word) = Some W_a5680.
Proof. vm_refl. Qed.
Lemma D_a5680 : decode_any W_a5680 = Some (OpImm ALU_SLTU 18 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5684 : bv 32 := 0x21288663.
Lemma F_a5684 : fetch_word Ubsan.M.loaded_segments (0xa5684 : word) = Some W_a5684.
Proof. vm_refl. Qed.
Lemma D_a5684 : decode_any W_a5684 = Some (Branch BC_EQ 17 18 524, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5688 : bv 32 := 0x2079e463.
Lemma F_a5688 : fetch_word Ubsan.M.loaded_segments (0xa5688 : word) = Some W_a5688.
Proof. vm_refl. Qed.
Lemma D_a5688 : decode_any W_a5688 = Some (Branch BC_LTU 19 7 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_a568c : bv 32 := 0x20038263.
Lemma F_a568c : fetch_word Ubsan.M.loaded_segments (0xa568c : word) = Some W_a568c.
Proof. vm_refl. Qed.
Lemma D_a568c : decode_any W_a568c = Some (Branch BC_EQ 7 0 516, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5690 : bv 32 := 0x0079f893.
Lemma F_a5690 : fetch_word Ubsan.M.loaded_segments (0xa5690 : word) = Some W_a5690.
Proof. vm_refl. Qed.
Lemma D_a5690 : decode_any W_a5690 = Some (OpImm ALU_AND 17 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5694 : bv 32 := 0x1e089e63.
Lemma F_a5694 : fetch_word Ubsan.M.loaded_segments (0xa5694 : word) = Some W_a5694.
Proof. vm_refl. Qed.
Lemma D_a5694 : decode_any W_a5694 = Some (Branch BC_NE 17 0 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5698 : bv 32 := 0x00000913.
Lemma F_a5698 : fetch_word Ubsan.M.loaded_segments (0xa5698 : word) = Some W_a5698.
Proof. vm_refl. Qed.
Lemma D_a5698 : decode_any W_a5698 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a569c : bv 32 := 0x0003089b.
Lemma F_a569c : fetch_word Ubsan.M.loaded_segments (0xa569c : word) = Some W_a569c.
Proof. vm_refl. Qed.
Lemma D_a569c : decode_any W_a569c = Some (OpImm32 17 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56a0 : bv 32 := 0x0009b983.
Lemma F_a56a0 : fetch_word Ubsan.M.loaded_segments (0xa56a0 : word) = Some W_a56a0.
Proof. vm_refl. Qed.
Lemma D_a56a0 : decode_any W_a56a0 = Some (Load SZ8 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56a4 : bv 32 := 0x411e0a33.
Lemma F_a56a4 : fetch_word Ubsan.M.loaded_segments (0xa56a4 : word) = Some W_a56a4.
Proof. vm_refl. Qed.
Lemma D_a56a4 : decode_any W_a56a4 = Some (Op ALU_SUB 20 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56a8 : bv 32 := 0x411e03bb.
Lemma F_a56a8 : fetch_word Ubsan.M.loaded_segments (0xa56a8 : word) = Some W_a56a8.
Proof. vm_refl. Qed.
Lemma D_a56a8 : decode_any W_a56a8 = Some (Op32 ALU_SUB 7 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56ac : bv 32 := 0x41c88ab3.
Lemma F_a56ac : fetch_word Ubsan.M.loaded_segments (0xa56ac : word) = Some W_a56ac.
Proof. vm_refl. Qed.
Lemma D_a56ac : decode_any W_a56ac = Some (Op ALU_SUB 21 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56b0 : bv 32 := 0x41c888bb.
Lemma F_a56b0 : fetch_word Ubsan.M.loaded_segments (0xa56b0 : word) = Some W_a56b0.
Proof. vm_refl. Qed.
Lemma D_a56b0 : decode_any W_a56b0 = Some (Op32 ALU_SUB 17 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56b4 : bv 32 := 0x0143c3b3.
Lemma F_a56b4 : fetch_word Ubsan.M.loaded_segments (0xa56b4 : word) = Some W_a56b4.
Proof. vm_refl. Qed.
Lemma D_a56b4 : decode_any W_a56b4 = Some (Op ALU_XOR 7 7 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56b8 : bv 32 := 0x0158c8b3.
Lemma F_a56b8 : fetch_word Ubsan.M.loaded_segments (0xa56b8 : word) = Some W_a56b8.
Proof. vm_refl. Qed.
Lemma D_a56b8 : decode_any W_a56b8 = Some (Op ALU_XOR 17 17 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56bc : bv 32 := 0x00703b33.
Lemma F_a56bc : fetch_word Ubsan.M.loaded_segments (0xa56bc : word) = Some W_a56bc.
Proof. vm_refl. Qed.
Lemma D_a56bc : decode_any W_a56bc = Some (Op ALU_SLTU 22 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56c0 : bv 32 := 0x01103bb3.
Lemma F_a56c0 : fetch_word Ubsan.M.loaded_segments (0xa56c0 : word) = Some W_a56c0.
Proof. vm_refl. Qed.
Lemma D_a56c0 : decode_any W_a56c0 = Some (Op ALU_SLTU 23 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56c4 : bv 32 := 0x01303c33.
Lemma F_a56c4 : fetch_word Ubsan.M.loaded_segments (0xa56c4 : word) = Some W_a56c4.
Proof. vm_refl. Qed.
Lemma D_a56c4 : decode_any W_a56c4 = Some (Op ALU_SLTU 24 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56c8 : bv 32 := 0x0039f893.
Lemma F_a56c8 : fetch_word Ubsan.M.loaded_segments (0xa56c8 : word) = Some W_a56c8.
Proof. vm_refl. Qed.
Lemma D_a56c8 : decode_any W_a56c8 = Some (OpImm ALU_AND 17 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56cc : bv 32 := 0x0018b893.
Lemma F_a56cc : fetch_word Ubsan.M.loaded_segments (0xa56cc : word) = Some W_a56cc.
Proof. vm_refl. Qed.
Lemma D_a56cc : decode_any W_a56cc = Some (OpImm ALU_SLTU 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56d0 : bv 32 := 0x0188fcb3.
Lemma F_a56d0 : fetch_word Ubsan.M.loaded_segments (0xa56d0 : word) = Some W_a56d0.
Proof. vm_refl. Qed.
Lemma D_a56d0 : decode_any W_a56d0 = Some (Op ALU_AND 25 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56d4 : bv 32 := 0x00068d13.
Lemma F_a56d4 : fetch_word Ubsan.M.loaded_segments (0xa56d4 : word) = Some W_a56d4.
Proof. vm_refl. Qed.
Lemma D_a56d4 : decode_any W_a56d4 = Some (OpImm ALU_ADD 26 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56d8 : bv 32 := 0x00098d93.
Lemma F_a56d8 : fetch_word Ubsan.M.loaded_segments (0xa56d8 : word) = Some W_a56d8.
Proof. vm_refl. Qed.
Lemma D_a56d8 : decode_any W_a56d8 = Some (OpImm ALU_ADD 27 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56dc : bv 32 := 0x00098093.
Lemma F_a56dc : fetch_word Ubsan.M.loaded_segments (0xa56dc : word) = Some W_a56dc.
Proof. vm_refl. Qed.
Lemma D_a56dc : decode_any W_a56dc = Some (OpImm ALU_ADD 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56e0 : bv 32 := 0x0180006f.
Lemma F_a56e0 : fetch_word Ubsan.M.loaded_segments (0xa56e0 : word) = Some W_a56e0.
Proof. vm_refl. Qed.
Lemma D_a56e0 : decode_any W_a56e0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56e4 : bv 32 := 0x0019091b.
Lemma F_a56e4 : fetch_word Ubsan.M.loaded_segments (0xa56e4 : word) = Some W_a56e4.
Proof. vm_refl. Qed.
Lemma D_a56e4 : decode_any W_a56e4 = Some (OpImm32 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56e8 : bv 32 := 0x00408093.
Lemma F_a56e8 : fetch_word Ubsan.M.loaded_segments (0xa56e8 : word) = Some W_a56e8.
Proof. vm_refl. Qed.
Lemma D_a56e8 : decode_any W_a56e8 = Some (OpImm ALU_ADD 1 1 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56ec : bv 32 := 0xfffd0d13.
Lemma F_a56ec : fetch_word Ubsan.M.loaded_segments (0xa56ec : word) = Some W_a56ec.
Proof. vm_refl. Qed.
Lemma D_a56ec : decode_any W_a56ec = Some (OpImm ALU_ADD 26 26 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56f0 : bv 32 := 0x004d8d93.
Lemma F_a56f0 : fetch_word Ubsan.M.loaded_segments (0xa56f0 : word) = Some W_a56f0.
Proof. vm_refl. Qed.
Lemma D_a56f0 : decode_any W_a56f0 = Some (OpImm ALU_ADD 27 27 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56f4 : bv 32 := 0x080d0863.
Lemma F_a56f4 : fetch_word Ubsan.M.loaded_segments (0xa56f4 : word) = Some W_a56f4.
Proof. vm_refl. Qed.
Lemma D_a56f4 : decode_any W_a56f4 = Some (Branch BC_EQ 26 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56f8 : bv 32 := 0x001db893.
Lemma F_a56f8 : fetch_word Ubsan.M.loaded_segments (0xa56f8 : word) = Some W_a56f8.
Proof. vm_refl. Qed.
Lemma D_a56f8 : decode_any W_a56f8 = Some (OpImm ALU_SLTU 17 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a56fc : bv 32 := 0x191c0a63.
Lemma F_a56fc : fetch_word Ubsan.M.loaded_segments (0xa56fc : word) = Some W_a56fc.
Proof. vm_refl. Qed.
Lemma D_a56fc : decode_any W_a56fc = Some (Branch BC_EQ 24 17 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5700 : bv 32 := 0x193de863.
Lemma F_a5700 : fetch_word Ubsan.M.loaded_segments (0xa5700 : word) = Some W_a5700.
Proof. vm_refl. Qed.
Lemma D_a5700 : decode_any W_a5700 = Some (Branch BC_LTU 27 19 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5704 : bv 32 := 0x180c8663.
Lemma F_a5704 : fetch_word Ubsan.M.loaded_segments (0xa5704 : word) = Some W_a5704.
Proof. vm_refl. Qed.
Lemma D_a5704 : decode_any W_a5704 = Some (Branch BC_EQ 25 0 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5708 : bv 32 := 0x0000a883.
Lemma F_a5708 : fetch_word Ubsan.M.loaded_segments (0xa5708 : word) = Some W_a5708.
Proof. vm_refl. Qed.
Lemma D_a5708 : decode_any W_a5708 = Some (Load SZ4 true 17 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a570c : bv 32 := 0xfde89ce3.
Lemma F_a570c : fetch_word Ubsan.M.loaded_segments (0xa570c : word) = Some W_a570c.
Proof. vm_refl. Qed.
Lemma D_a570c : decode_any W_a570c = Some (Branch BC_NE 17 30 8152, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5710 : bv 32 := 0x412e83b3.
Lemma F_a5710 : fetch_word Ubsan.M.loaded_segments (0xa5710 : word) = Some W_a5710.
Proof. vm_refl. Qed.
Lemma D_a5710 : decode_any W_a5710 = Some (Op ALU_SUB 7 29 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5714 : bv 32 := 0x412e88bb.
Lemma F_a5714 : fetch_word Ubsan.M.loaded_segments (0xa5714 : word) = Some W_a5714.
Proof. vm_refl. Qed.
Lemma D_a5714 : decode_any W_a5714 = Some (Op32 ALU_SUB 17 29 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5718 : bv 32 := 0x16789c63.
Lemma F_a5718 : fetch_word Ubsan.M.loaded_segments (0xa5718 : word) = Some W_a5718.
Proof. vm_refl. Qed.
Lemma D_a5718 : decode_any W_a5718 = Some (Branch BC_NE 17 7 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_a571c : bv 32 := 0x0003839b.
Lemma F_a571c : fetch_word Ubsan.M.loaded_segments (0xa571c : word) = Some W_a571c.
Proof. vm_refl. Qed.
Lemma D_a571c : decode_any W_a571c = Some (OpImm32 7 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5720 : bv 32 := 0x0053c463.
Lemma F_a5720 : fetch_word Ubsan.M.loaded_segments (0xa5720 : word) = Some W_a5720.
Proof. vm_refl. Qed.
Lemma D_a5720 : decode_any W_a5720 = Some (Branch BC_LT 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5724 : bv 32 := 0x00038293.
Lemma F_a5724 : fetch_word Ubsan.M.loaded_segments (0xa5724 : word) = Some W_a5724.
Proof. vm_refl. Qed.
Lemma D_a5724 : decode_any W_a5724 = Some (OpImm ALU_ADD 5 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5728 : bv 32 := 0x160b1463.
Lemma F_a5728 : fetch_word Ubsan.M.loaded_segments (0xa5728 : word) = Some W_a5728.
Proof. vm_refl. Qed.
Lemma D_a5728 : decode_any W_a5728 = Some (Branch BC_NE 22 0 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_a572c : bv 32 := 0x41d903b3.
Lemma F_a572c : fetch_word Ubsan.M.loaded_segments (0xa572c : word) = Some W_a572c.
Proof. vm_refl. Qed.
Lemma D_a572c : decode_any W_a572c = Some (Op ALU_SUB 7 18 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5730 : bv 32 := 0x41d908bb.
Lemma F_a5730 : fetch_word Ubsan.M.loaded_segments (0xa5730 : word) = Some W_a5730.
Proof. vm_refl. Qed.
Lemma D_a5730 : decode_any W_a5730 = Some (Op32 ALU_SUB 17 18 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5734 : bv 32 := 0x0078c8b3.
Lemma F_a5734 : fetch_word Ubsan.M.loaded_segments (0xa5734 : word) = Some W_a5734.
Proof. vm_refl. Qed.
Lemma D_a5734 : decode_any W_a5734 = Some (Op ALU_XOR 17 17 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5738 : bv 32 := 0x011038b3.
Lemma F_a5738 : fetch_word Ubsan.M.loaded_segments (0xa5738 : word) = Some W_a5738.
Proof. vm_refl. Qed.
Lemma D_a5738 : decode_any W_a5738 = Some (Op ALU_SLTU 17 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a573c : bv 32 := 0x0178e8b3.
Lemma F_a573c : fetch_word Ubsan.M.loaded_segments (0xa573c : word) = Some W_a573c.
Proof. vm_refl. Qed.
Lemma D_a573c : decode_any W_a573c = Some (Op ALU_OR 17 17 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5740 : bv 32 := 0x0018f893.
Lemma F_a5740 : fetch_word Ubsan.M.loaded_segments (0xa5740 : word) = Some W_a5740.
Proof. vm_refl. Qed.
Lemma D_a5740 : decode_any W_a5740 = Some (OpImm ALU_AND 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5744 : bv 32 := 0x14089663.
Lemma F_a5744 : fetch_word Ubsan.M.loaded_segments (0xa5744 : word) = Some W_a5744.
Proof. vm_refl. Qed.
Lemma D_a5744 : decode_any W_a5744 = Some (Branch BC_NE 17 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5748 : bv 32 := 0x000a089b.
Lemma F_a5748 : fetch_word Ubsan.M.loaded_segments (0xa5748 : word) = Some W_a5748.
Proof. vm_refl. Qed.
Lemma D_a5748 : decode_any W_a5748 = Some (OpImm32 17 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a574c : bv 32 := 0x00e8ce63.
Lemma F_a574c : fetch_word Ubsan.M.loaded_segments (0xa574c : word) = Some W_a574c.
Proof. vm_refl. Qed.
Lemma D_a574c : decode_any W_a574c = Some (Branch BC_LT 17 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5750 : bv 32 := 0x00088713.
Lemma F_a5750 : fetch_word Ubsan.M.loaded_segments (0xa5750 : word) = Some W_a5750.
Proof. vm_refl. Qed.
Lemma D_a5750 : decode_any W_a5750 = Some (OpImm ALU_ADD 14 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5754 : bv 32 := 0x0003839b.
Lemma F_a5754 : fetch_word Ubsan.M.loaded_segments (0xa5754 : word) = Some W_a5754.
Proof. vm_refl. Qed.
Lemma D_a5754 : decode_any W_a5754 = Some (OpImm32 7 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5758 : bv 32 := 0x0103dc63.
Lemma F_a5758 : fetch_word Ubsan.M.loaded_segments (0xa5758 : word) = Some W_a5758.
Proof. vm_refl. Qed.
Lemma D_a5758 : decode_any W_a5758 = Some (Branch BC_GE 7 16 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a575c : bv 32 := 0x000a889b.
Lemma F_a575c : fetch_word Ubsan.M.loaded_segments (0xa575c : word) = Some W_a575c.
Proof. vm_refl. Qed.
Lemma D_a575c : decode_any W_a575c = Some (OpImm32 17 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5760 : bv 32 := 0xf8f8c2e3.
Lemma F_a5760 : fetch_word Ubsan.M.loaded_segments (0xa5760 : word) = Some W_a5760.
Proof. vm_refl. Qed.
Lemma D_a5760 : decode_any W_a5760 = Some (Branch BC_LT 17 15 8068, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5764 : bv 32 := 0x0180006f.
Lemma F_a5764 : fetch_word Ubsan.M.loaded_segments (0xa5764 : word) = Some W_a5764.
Proof. vm_refl. Qed.
Lemma D_a5764 : decode_any W_a5764 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5768 : bv 32 := 0x0003839b.
Lemma F_a5768 : fetch_word Ubsan.M.loaded_segments (0xa5768 : word) = Some W_a5768.
Proof. vm_refl. Qed.
Lemma D_a5768 : decode_any W_a5768 = Some (OpImm32 7 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a576c : bv 32 := 0xff03c8e3.
Lemma F_a576c : fetch_word Ubsan.M.loaded_segments (0xa576c : word) = Some W_a576c.
Proof. vm_refl. Qed.
Lemma D_a576c : decode_any W_a576c = Some (Branch BC_LT 7 16 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5770 : bv 32 := 0x00038813.
Lemma F_a5770 : fetch_word Ubsan.M.loaded_segments (0xa5770 : word) = Some W_a5770.
Proof. vm_refl. Qed.
Lemma D_a5770 : decode_any W_a5770 = Some (OpImm ALU_ADD 16 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5774 : bv 32 := 0x000a889b.
Lemma F_a5774 : fetch_word Ubsan.M.loaded_segments (0xa5774 : word) = Some W_a5774.
Proof. vm_refl. Qed.
Lemma D_a5774 : decode_any W_a5774 = Some (OpImm32 17 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5778 : bv 32 := 0xf6f8c6e3.
Lemma F_a5778 : fetch_word Ubsan.M.loaded_segments (0xa5778 : word) = Some W_a5778.
Proof. vm_refl. Qed.
Lemma D_a5778 : decode_any W_a5778 = Some (Branch BC_LT 17 15 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_a577c : bv 32 := 0x00088793.
Lemma F_a577c : fetch_word Ubsan.M.loaded_segments (0xa577c : word) = Some W_a577c.
Proof. vm_refl. Qed.
Lemma D_a577c : decode_any W_a577c = Some (OpImm ALU_ADD 15 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5780 : bv 32 := 0xf65ff06f.
Lemma F_a5780 : fetch_word Ubsan.M.loaded_segments (0xa5780 : word) = Some W_a5780.
Proof. vm_refl. Qed.
Lemma D_a5780 : decode_any W_a5780 = Some (Jal 0 2096996, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5784 : bv 32 := 0x10930663.
Lemma F_a5784 : fetch_word Ubsan.M.loaded_segments (0xa5784 : word) = Some W_a5784.
Proof. vm_refl. Qed.
Lemma D_a5784 : decode_any W_a5784 = Some (Branch BC_EQ 6 9 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5788 : bv 32 := 0x00130313.
Lemma F_a5788 : fetch_word Ubsan.M.loaded_segments (0xa5788 : word) = Some W_a5788.
Proof. vm_refl. Qed.
Lemma D_a5788 : decode_any W_a5788 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a578c : bv 32 := 0xeff310e3.
Lemma F_a578c : fetch_word Ubsan.M.loaded_segments (0xa578c : word) = Some W_a578c.
Proof. vm_refl. Qed.
Lemma D_a578c : decode_any W_a578c = Some (Branch BC_NE 6 31 7904, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5790 : bv 32 := 0x0a80006f.
Lemma F_a5790 : fetch_word Ubsan.M.loaded_segments (0xa5790 : word) = Some W_a5790.
Proof. vm_refl. Qed.
Lemma D_a5790 : decode_any W_a5790 = Some (Jal 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5794 : bv 32 := 0x00081517.
Lemma F_a5794 : fetch_word Ubsan.M.loaded_segments (0xa5794 : word) = Some W_a5794.
Proof. vm_refl. Qed.
Lemma D_a5794 : decode_any W_a5794 = Some (Auipc 10 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5798 : bv 32 := 0x2dc53503.
Lemma F_a5798 : fetch_word Ubsan.M.loaded_segments (0xa5798 : word) = Some W_a5798.
Proof. vm_refl. Qed.
Lemma D_a5798 : decode_any W_a5798 = Some (Load SZ8 true 10 10 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_a579c : bv 32 := 0x00052503.
Lemma F_a579c : fetch_word Ubsan.M.loaded_segments (0xa579c : word) = Some W_a579c.
Proof. vm_refl. Qed.
Lemma D_a579c : decode_any W_a579c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57a0 : bv 32 := 0x00500593.
Lemma F_a57a0 : fetch_word Ubsan.M.loaded_segments (0xa57a0 : word) = Some W_a57a0.
Proof. vm_refl. Qed.
Lemma D_a57a0 : decode_any W_a57a0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57a4 : bv 32 := 0x06a5ce63.
Lemma F_a57a4 : fetch_word Ubsan.M.loaded_segments (0xa57a4 : word) = Some W_a57a4.
Proof. vm_refl. Qed.
Lemma D_a57a4 : decode_any W_a57a4 = Some (Branch BC_LT 11 10 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57a8 : bv 32 := 0xfff77517.
Lemma F_a57a8 : fetch_word Ubsan.M.loaded_segments (0xa57a8 : word) = Some W_a57a8.
Proof. vm_refl. Qed.
Lemma D_a57a8 : decode_any W_a57a8 = Some (Auipc 10 1048439, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57ac : bv 32 := 0xfff6d597.
Lemma F_a57ac : fetch_word Ubsan.M.loaded_segments (0xa57ac : word) = Some W_a57ac.
Proof. vm_refl. Qed.
Lemma D_a57ac : decode_any W_a57ac = Some (Auipc 11 1048429, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57b0 : bv 32 := 0x26650513.
Lemma F_a57b0 : fetch_word Ubsan.M.loaded_segments (0xa57b0 : word) = Some W_a57b0.
Proof. vm_refl. Qed.
Lemma D_a57b0 : decode_any W_a57b0 = Some (OpImm ALU_ADD 10 10 614, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57b4 : bv 32 := 0x7ff58593.
Lemma F_a57b4 : fetch_word Ubsan.M.loaded_segments (0xa57b4 : word) = Some W_a57b4.
Proof. vm_refl. Qed.
Lemma D_a57b4 : decode_any W_a57b4 = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57b8 : bv 32 := 0x0280006f.
Lemma F_a57b8 : fetch_word Ubsan.M.loaded_segments (0xa57b8 : word) = Some W_a57b8.
Proof. vm_refl. Qed.
Lemma D_a57b8 : decode_any W_a57b8 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57bc : bv 32 := 0x00081517.
Lemma F_a57bc : fetch_word Ubsan.M.loaded_segments (0xa57bc : word) = Some W_a57bc.
Proof. vm_refl. Qed.
Lemma D_a57bc : decode_any W_a57bc = Some (Auipc 10 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57c0 : bv 32 := 0x2b453503.
Lemma F_a57c0 : fetch_word Ubsan.M.loaded_segments (0xa57c0 : word) = Some W_a57c0.
Proof. vm_refl. Qed.
Lemma D_a57c0 : decode_any W_a57c0 = Some (Load SZ8 true 10 10 692, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57c4 : bv 32 := 0x00052503.
Lemma F_a57c4 : fetch_word Ubsan.M.loaded_segments (0xa57c4 : word) = Some W_a57c4.
Proof. vm_refl. Qed.
Lemma D_a57c4 : decode_any W_a57c4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57c8 : bv 32 := 0x00500593.
Lemma F_a57c8 : fetch_word Ubsan.M.loaded_segments (0xa57c8 : word) = Some W_a57c8.
Proof. vm_refl. Qed.
Lemma D_a57c8 : decode_any W_a57c8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57cc : bv 32 := 0x04a5ca63.
Lemma F_a57cc : fetch_word Ubsan.M.loaded_segments (0xa57cc : word) = Some W_a57cc.
Proof. vm_refl. Qed.
Lemma D_a57cc : decode_any W_a57cc = Some (Branch BC_LT 11 10 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57d0 : bv 32 := 0xfff72517.
Lemma F_a57d0 : fetch_word Ubsan.M.loaded_segments (0xa57d0 : word) = Some W_a57d0.
Proof. vm_refl. Qed.
Lemma D_a57d0 : decode_any W_a57d0 = Some (Auipc 10 1048434, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57d4 : bv 32 := 0xfff6d597.
Lemma F_a57d4 : fetch_word Ubsan.M.loaded_segments (0xa57d4 : word) = Some W_a57d4.
Proof. vm_refl. Qed.
Lemma D_a57d4 : decode_any W_a57d4 = Some (Auipc 11 1048429, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57d8 : bv 32 := 0xa3550513.
Lemma F_a57d8 : fetch_word Ubsan.M.loaded_segments (0xa57d8 : word) = Some W_a57d8.
Proof. vm_refl. Qed.
Lemma D_a57d8 : decode_any W_a57d8 = Some (OpImm ALU_ADD 10 10 2613, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57dc : bv 32 := 0x7d758593.
Lemma F_a57dc : fetch_word Ubsan.M.loaded_segments (0xa57dc : word) = Some W_a57dc.
Proof. vm_refl. Qed.
Lemma D_a57dc : decode_any W_a57dc = Some (OpImm ALU_ADD 11 11 2007, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57e0 : bv 32 := 0x00100613.
Lemma F_a57e0 : fetch_word Ubsan.M.loaded_segments (0xa57e0 : word) = Some W_a57e0.
Proof. vm_refl. Qed.
Lemma D_a57e0 : decode_any W_a57e0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57e4 : bv 32 := 0x07813083.
Lemma F_a57e4 : fetch_word Ubsan.M.loaded_segments (0xa57e4 : word) = Some W_a57e4.
Proof. vm_refl. Qed.
Lemma D_a57e4 : decode_any W_a57e4 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57e8 : bv 32 := 0x07013403.
Lemma F_a57e8 : fetch_word Ubsan.M.loaded_segments (0xa57e8 : word) = Some W_a57e8.
Proof. vm_refl. Qed.
Lemma D_a57e8 : decode_any W_a57e8 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57ec : bv 32 := 0x06813483.
Lemma F_a57ec : fetch_word Ubsan.M.loaded_segments (0xa57ec : word) = Some W_a57ec.
Proof. vm_refl. Qed.
Lemma D_a57ec : decode_any W_a57ec = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57f0 : bv 32 := 0x06013903.
Lemma F_a57f0 : fetch_word Ubsan.M.loaded_segments (0xa57f0 : word) = Some W_a57f0.
Proof. vm_refl. Qed.
Lemma D_a57f0 : decode_any W_a57f0 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57f4 : bv 32 := 0x05813983.
Lemma F_a57f4 : fetch_word Ubsan.M.loaded_segments (0xa57f4 : word) = Some W_a57f4.
Proof. vm_refl. Qed.
Lemma D_a57f4 : decode_any W_a57f4 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57f8 : bv 32 := 0x05013a03.
Lemma F_a57f8 : fetch_word Ubsan.M.loaded_segments (0xa57f8 : word) = Some W_a57f8.
Proof. vm_refl. Qed.
Lemma D_a57f8 : decode_any W_a57f8 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a57fc : bv 32 := 0x04813a83.
Lemma F_a57fc : fetch_word Ubsan.M.loaded_segments (0xa57fc : word) = Some W_a57fc.
Proof. vm_refl. Qed.
Lemma D_a57fc : decode_any W_a57fc = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5800 : bv 32 := 0x04013b03.
Lemma F_a5800 : fetch_word Ubsan.M.loaded_segments (0xa5800 : word) = Some W_a5800.
Proof. vm_refl. Qed.
Lemma D_a5800 : decode_any W_a5800 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5804 : bv 32 := 0x03813b83.
Lemma F_a5804 : fetch_word Ubsan.M.loaded_segments (0xa5804 : word) = Some W_a5804.
Proof. vm_refl. Qed.
Lemma D_a5804 : decode_any W_a5804 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5808 : bv 32 := 0x03013c03.
Lemma F_a5808 : fetch_word Ubsan.M.loaded_segments (0xa5808 : word) = Some W_a5808.
Proof. vm_refl. Qed.
Lemma D_a5808 : decode_any W_a5808 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a580c : bv 32 := 0x02813c83.
Lemma F_a580c : fetch_word Ubsan.M.loaded_segments (0xa580c : word) = Some W_a580c.
Proof. vm_refl. Qed.
Lemma D_a580c : decode_any W_a580c = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5810 : bv 32 := 0x02013d03.
Lemma F_a5810 : fetch_word Ubsan.M.loaded_segments (0xa5810 : word) = Some W_a5810.
Proof. vm_refl. Qed.
Lemma D_a5810 : decode_any W_a5810 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5814 : bv 32 := 0x01813d83.
Lemma F_a5814 : fetch_word Ubsan.M.loaded_segments (0xa5814 : word) = Some W_a5814.
Proof. vm_refl. Qed.
Lemma D_a5814 : decode_any W_a5814 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5818 : bv 32 := 0x08010113.
Lemma F_a5818 : fetch_word Ubsan.M.loaded_segments (0xa5818 : word) = Some W_a5818.
Proof. vm_refl. Qed.
Lemma D_a5818 : decode_any W_a5818 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a581c : bv 32 := 0xe55bd06f.
Lemma F_a581c : fetch_word Ubsan.M.loaded_segments (0xa581c : word) = Some W_a581c.
Proof. vm_refl. Qed.
Lemma D_a581c : decode_any W_a581c = Some (Jal 0 1826388, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5820 : bv 32 := 0x00100513.
Lemma F_a5820 : fetch_word Ubsan.M.loaded_segments (0xa5820 : word) = Some W_a5820.
Proof. vm_refl. Qed.
Lemma D_a5820 : decode_any W_a5820 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5824 : bv 32 := 0x0300006f.
Lemma F_a5824 : fetch_word Ubsan.M.loaded_segments (0xa5824 : word) = Some W_a5824.
Proof. vm_refl. Qed.
Lemma D_a5824 : decode_any W_a5824 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5828 : bv 32 := 0x00000293.
Lemma F_a5828 : fetch_word Ubsan.M.loaded_segments (0xa5828 : word) = Some W_a5828.
Proof. vm_refl. Qed.
Lemma D_a5828 : decode_any W_a5828 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a582c : bv 32 := 0x00000713.
Lemma F_a582c : fetch_word Ubsan.M.loaded_segments (0xa582c : word) = Some W_a582c.
Proof. vm_refl. Qed.
Lemma D_a582c : decode_any W_a582c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5830 : bv 32 := 0x00000813.
Lemma F_a5830 : fetch_word Ubsan.M.loaded_segments (0xa5830 : word) = Some W_a5830.
Proof. vm_refl. Qed.
Lemma D_a5830 : decode_any W_a5830 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5834 : bv 32 := 0x00000793.
Lemma F_a5834 : fetch_word Ubsan.M.loaded_segments (0xa5834 : word) = Some W_a5834.
Proof. vm_refl. Qed.
Lemma D_a5834 : decode_any W_a5834 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5838 : bv 32 := 0x00000513.
Lemma F_a5838 : fetch_word Ubsan.M.loaded_segments (0xa5838 : word) = Some W_a5838.
Proof. vm_refl. Qed.
Lemma D_a5838 : decode_any W_a5838 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a583c : bv 32 := 0x0055a023.
Lemma F_a583c : fetch_word Ubsan.M.loaded_segments (0xa583c : word) = Some W_a583c.
Proof. vm_refl. Qed.
Lemma D_a583c : decode_any W_a583c = Some (Store SZ4 11 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5840 : bv 32 := 0x00e62023.
Lemma F_a5840 : fetch_word Ubsan.M.loaded_segments (0xa5840 : word) = Some W_a5840.
Proof. vm_refl. Qed.
Lemma D_a5840 : decode_any W_a5840 = Some (Store SZ4 12 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5844 : bv 32 := 0x01013583.
Lemma F_a5844 : fetch_word Ubsan.M.loaded_segments (0xa5844 : word) = Some W_a5844.
Proof. vm_refl. Qed.
Lemma D_a5844 : decode_any W_a5844 = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5848 : bv 32 := 0x0105a023.
Lemma F_a5848 : fetch_word Ubsan.M.loaded_segments (0xa5848 : word) = Some W_a5848.
Proof. vm_refl. Qed.
Lemma D_a5848 : decode_any W_a5848 = Some (Store SZ4 11 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a584c : bv 32 := 0x00813583.
Lemma F_a584c : fetch_word Ubsan.M.loaded_segments (0xa584c : word) = Some W_a584c.
Proof. vm_refl. Qed.
Lemma D_a584c : decode_any W_a584c = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5850 : bv 32 := 0x00f5a023.
Lemma F_a5850 : fetch_word Ubsan.M.loaded_segments (0xa5850 : word) = Some W_a5850.
Proof. vm_refl. Qed.
Lemma D_a5850 : decode_any W_a5850 = Some (Store SZ4 11 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5854 : bv 32 := 0x07813083.
Lemma F_a5854 : fetch_word Ubsan.M.loaded_segments (0xa5854 : word) = Some W_a5854.
Proof. vm_refl. Qed.
Lemma D_a5854 : decode_any W_a5854 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5858 : bv 32 := 0x07013403.
Lemma F_a5858 : fetch_word Ubsan.M.loaded_segments (0xa5858 : word) = Some W_a5858.
Proof. vm_refl. Qed.
Lemma D_a5858 : decode_any W_a5858 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a585c : bv 32 := 0x06813483.
Lemma F_a585c : fetch_word Ubsan.M.loaded_segments (0xa585c : word) = Some W_a585c.
Proof. vm_refl. Qed.
Lemma D_a585c : decode_any W_a585c = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5860 : bv 32 := 0x06013903.
Lemma F_a5860 : fetch_word Ubsan.M.loaded_segments (0xa5860 : word) = Some W_a5860.
Proof. vm_refl. Qed.
Lemma D_a5860 : decode_any W_a5860 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5864 : bv 32 := 0x05813983.
Lemma F_a5864 : fetch_word Ubsan.M.loaded_segments (0xa5864 : word) = Some W_a5864.
Proof. vm_refl. Qed.
Lemma D_a5864 : decode_any W_a5864 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5868 : bv 32 := 0x05013a03.
Lemma F_a5868 : fetch_word Ubsan.M.loaded_segments (0xa5868 : word) = Some W_a5868.
Proof. vm_refl. Qed.
Lemma D_a5868 : decode_any W_a5868 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a586c : bv 32 := 0x04813a83.
Lemma F_a586c : fetch_word Ubsan.M.loaded_segments (0xa586c : word) = Some W_a586c.
Proof. vm_refl. Qed.
Lemma D_a586c : decode_any W_a586c = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5870 : bv 32 := 0x04013b03.
Lemma F_a5870 : fetch_word Ubsan.M.loaded_segments (0xa5870 : word) = Some W_a5870.
Proof. vm_refl. Qed.
Lemma D_a5870 : decode_any W_a5870 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5874 : bv 32 := 0x03813b83.
Lemma F_a5874 : fetch_word Ubsan.M.loaded_segments (0xa5874 : word) = Some W_a5874.
Proof. vm_refl. Qed.
Lemma D_a5874 : decode_any W_a5874 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5878 : bv 32 := 0x03013c03.
Lemma F_a5878 : fetch_word Ubsan.M.loaded_segments (0xa5878 : word) = Some W_a5878.
Proof. vm_refl. Qed.
Lemma D_a5878 : decode_any W_a5878 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a587c : bv 32 := 0x02813c83.
Lemma F_a587c : fetch_word Ubsan.M.loaded_segments (0xa587c : word) = Some W_a587c.
Proof. vm_refl. Qed.
Lemma D_a587c : decode_any W_a587c = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5880 : bv 32 := 0x02013d03.
Lemma F_a5880 : fetch_word Ubsan.M.loaded_segments (0xa5880 : word) = Some W_a5880.
Proof. vm_refl. Qed.
Lemma D_a5880 : decode_any W_a5880 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5884 : bv 32 := 0x01813d83.
Lemma F_a5884 : fetch_word Ubsan.M.loaded_segments (0xa5884 : word) = Some W_a5884.
Proof. vm_refl. Qed.
Lemma D_a5884 : decode_any W_a5884 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5888 : bv 32 := 0x08010113.
Lemma F_a5888 : fetch_word Ubsan.M.loaded_segments (0xa5888 : word) = Some W_a5888.
Proof. vm_refl. Qed.
Lemma D_a5888 : decode_any W_a5888 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a588c : bv 32 := 0x00008067.
Lemma F_a588c : fetch_word Ubsan.M.loaded_segments (0xa588c : word) = Some W_a588c.
Proof. vm_refl. Qed.
Lemma D_a588c : decode_any W_a588c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a5890 : bv 32 := 0xc0001073.
Lemma F_a5890 : fetch_word Ubsan.M.loaded_segments (0xa5890 : word) = Some W_a5890.
Proof. vm_refl. Qed.
Lemma D_a5890 : decode_any W_a5890 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
