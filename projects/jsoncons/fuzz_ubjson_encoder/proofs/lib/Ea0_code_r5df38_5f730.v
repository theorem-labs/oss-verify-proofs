(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_785bc : bv 32 := 0x2590006f.
Lemma F_785bc : fetch_word Asan.M.loaded_segments (0x7860c : word) = Some W_785bc.
Proof. vm_refl. Qed.
Lemma D_785bc : decode_any W_785bc = Some (Jal 0 2648, 4%Z).
Proof. vm_refl. Qed.

Definition W_785c0 : bv 32 := 0x5450006f.
Lemma F_785c0 : fetch_word Asan.M.loaded_segments (0x78610 : word) = Some W_785c0.
Proof. vm_refl. Qed.
Lemma D_785c0 : decode_any W_785c0 = Some (Jal 0 3396, 4%Z).
Proof. vm_refl. Qed.

Definition W_785c4 : bv 32 := 0x2000106f.
Lemma F_785c4 : fetch_word Asan.M.loaded_segments (0x78614 : word) = Some W_785c4.
Proof. vm_refl. Qed.
Lemma D_785c4 : decode_any W_785c4 = Some (Jal 0 4608, 4%Z).
Proof. vm_refl. Qed.

Definition W_785c8 : bv 32 := 0x81010113.
Lemma F_785c8 : fetch_word Asan.M.loaded_segments (0x78618 : word) = Some W_785c8.
Proof. vm_refl. Qed.
Lemma D_785c8 : decode_any W_785c8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_785cc : bv 32 := 0x7e113423.
Lemma F_785cc : fetch_word Asan.M.loaded_segments (0x7861c : word) = Some W_785cc.
Proof. vm_refl. Qed.
Lemma D_785cc : decode_any W_785cc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_785d0 : bv 32 := 0x7e813023.
Lemma F_785d0 : fetch_word Asan.M.loaded_segments (0x78620 : word) = Some W_785d0.
Proof. vm_refl. Qed.
Lemma D_785d0 : decode_any W_785d0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_785d4 : bv 32 := 0x7c913c23.
Lemma F_785d4 : fetch_word Asan.M.loaded_segments (0x78624 : word) = Some W_785d4.
Proof. vm_refl. Qed.
Lemma D_785d4 : decode_any W_785d4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_785d8 : bv 32 := 0x7d213823.
Lemma F_785d8 : fetch_word Asan.M.loaded_segments (0x78628 : word) = Some W_785d8.
Proof. vm_refl. Qed.
Lemma D_785d8 : decode_any W_785d8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_785dc : bv 32 := 0x7d313423.
Lemma F_785dc : fetch_word Asan.M.loaded_segments (0x7862c : word) = Some W_785dc.
Proof. vm_refl. Qed.
Lemma D_785dc : decode_any W_785dc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_785e0 : bv 32 := 0x7d413023.
Lemma F_785e0 : fetch_word Asan.M.loaded_segments (0x78630 : word) = Some W_785e0.
Proof. vm_refl. Qed.
Lemma D_785e0 : decode_any W_785e0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_785e4 : bv 32 := 0x7b513c23.
Lemma F_785e4 : fetch_word Asan.M.loaded_segments (0x78634 : word) = Some W_785e4.
Proof. vm_refl. Qed.
Lemma D_785e4 : decode_any W_785e4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_785e8 : bv 32 := 0x7b613823.
Lemma F_785e8 : fetch_word Asan.M.loaded_segments (0x78638 : word) = Some W_785e8.
Proof. vm_refl. Qed.
Lemma D_785e8 : decode_any W_785e8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_785ec : bv 32 := 0x7b713423.
Lemma F_785ec : fetch_word Asan.M.loaded_segments (0x7863c : word) = Some W_785ec.
Proof. vm_refl. Qed.
Lemma D_785ec : decode_any W_785ec = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_785f0 : bv 32 := 0x7f010413.
Lemma F_785f0 : fetch_word Asan.M.loaded_segments (0x78640 : word) = Some W_785f0.
Proof. vm_refl. Qed.
Lemma D_785f0 : decode_any W_785f0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_785f4 : bv 32 := 0xf9010113.
Lemma F_785f4 : fetch_word Asan.M.loaded_segments (0x78644 : word) = Some W_785f4.
Proof. vm_refl. Qed.
Lemma D_785f4 : decode_any W_785f4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_785f8 : bv 32 := 0x000c1697.
Lemma F_785f8 : fetch_word Asan.M.loaded_segments (0x78648 : word) = Some W_785f8.
Proof. vm_refl. Qed.
Lemma D_785f8 : decode_any W_785f8 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_785fc : bv 32 := 0x6d86b683.
Lemma F_785fc : fetch_word Asan.M.loaded_segments (0x7864c : word) = Some W_785fc.
Proof. vm_refl. Qed.
Lemma D_785fc : decode_any W_785fc = Some (Load SZ8 true 13 13 1752, 4%Z).
Proof. vm_refl. Qed.

Definition W_78600 : bv 32 := 0x0006c683.
Lemma F_78600 : fetch_word Asan.M.loaded_segments (0x78650 : word) = Some W_78600.
Proof. vm_refl. Qed.
Lemma D_78600 : decode_any W_78600 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78604 : bv 32 := 0x0e068863.
Lemma F_78604 : fetch_word Asan.M.loaded_segments (0x78654 : word) = Some W_78604.
Proof. vm_refl. Qed.
Lemma D_78604 : decode_any W_78604 = Some (Branch BC_EQ 13 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_78608 : bv 32 := 0x80040a13.
Lemma F_78608 : fetch_word Asan.M.loaded_segments (0x78658 : word) = Some W_78608.
Proof. vm_refl. Qed.
Lemma D_78608 : decode_any W_78608 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7860c : bv 32 := 0xfa0a0a13.
Lemma F_7860c : fetch_word Asan.M.loaded_segments (0x7865c : word) = Some W_7860c.
Proof. vm_refl. Qed.
Lemma D_7860c : decode_any W_7860c = Some (OpImm ALU_ADD 20 20 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_78610 : bv 32 := 0x00c58ab3.
Lemma F_78610 : fetch_word Asan.M.loaded_segments (0x78660 : word) = Some W_78610.
Proof. vm_refl. Qed.
Lemma D_78610 : decode_any W_78610 = Some (Op ALU_ADD 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_78614 : bv 32 := 0x00c509b3.
Lemma F_78614 : fetch_word Asan.M.loaded_segments (0x78664 : word) = Some W_78614.
Proof. vm_refl. Qed.
Lemma D_78614 : decode_any W_78614 = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_78618 : bv 32 := 0x00b50663.
Lemma F_78618 : fetch_word Asan.M.loaded_segments (0x78668 : word) = Some W_78618.
Proof. vm_refl. Qed.
Lemma D_78618 : decode_any W_78618 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7861c : bv 32 := 0x0135f463.
Lemma F_7861c : fetch_word Asan.M.loaded_segments (0x7866c : word) = Some W_7861c.
Proof. vm_refl. Qed.
Lemma D_7861c : decode_any W_7861c = Some (Branch BC_GEU 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_78620 : bv 32 := 0x1b556a63.
Lemma F_78620 : fetch_word Asan.M.loaded_segments (0x78670 : word) = Some W_78620.
Proof. vm_refl. Qed.
Lemma D_78620 : decode_any W_78620 = Some (Branch BC_LTU 10 21 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_78624 : bv 32 := 0xfff5c693.
Lemma F_78624 : fetch_word Asan.M.loaded_segments (0x78674 : word) = Some W_78624.
Proof. vm_refl. Qed.
Lemma D_78624 : decode_any W_78624 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78628 : bv 32 := 0x26c6e463.
Lemma F_78628 : fetch_word Asan.M.loaded_segments (0x78678 : word) = Some W_78628.
Proof. vm_refl. Qed.
Lemma D_78628 : decode_any W_78628 = Some (Branch BC_LTU 13 12 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_7862c : bv 32 := 0xfbf60b13.
Lemma F_7862c : fetch_word Asan.M.loaded_segments (0x7867c : word) = Some W_7862c.
Proof. vm_refl. Qed.
Lemma D_7862c : decode_any W_7862c = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_78630 : bv 32 := 0xfbf00693.
Lemma F_78630 : fetch_word Asan.M.loaded_segments (0x78680 : word) = Some W_78630.
Proof. vm_refl. Qed.
Lemma D_78630 : decode_any W_78630 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_78634 : bv 32 := 0x2f66f263.
Lemma F_78634 : fetch_word Asan.M.loaded_segments (0x78684 : word) = Some W_78634.
Proof. vm_refl. Qed.
Lemma D_78634 : decode_any W_78634 = Some (Branch BC_GEU 13 22 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_78638 : bv 32 := 0x000c1697.
Lemma F_78638 : fetch_word Asan.M.loaded_segments (0x78688 : word) = Some W_78638.
Proof. vm_refl. Qed.
Lemma D_78638 : decode_any W_78638 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7863c : bv 32 := 0xb306b683.
Lemma F_7863c : fetch_word Asan.M.loaded_segments (0x7868c : word) = Some W_7863c.
Proof. vm_refl. Qed.
Lemma D_7863c : decode_any W_7863c = Some (Load SZ8 true 13 13 2864, 4%Z).
Proof. vm_refl. Qed.

Definition W_78640 : bv 32 := 0x0006b703.
Lemma F_78640 : fetch_word Asan.M.loaded_segments (0x78690 : word) = Some W_78640.
Proof. vm_refl. Qed.
Lemma D_78640 : decode_any W_78640 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78644 : bv 32 := 0xfffa8a93.
Lemma F_78644 : fetch_word Asan.M.loaded_segments (0x78694 : word) = Some W_78644.
Proof. vm_refl. Qed.
Lemma D_78644 : decode_any W_78644 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78648 : bv 32 := 0x0035d693.
Lemma F_78648 : fetch_word Asan.M.loaded_segments (0x78698 : word) = Some W_78648.
Proof. vm_refl. Qed.
Lemma D_78648 : decode_any W_78648 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7864c : bv 32 := 0x003ad793.
Lemma F_7864c : fetch_word Asan.M.loaded_segments (0x7869c : word) = Some W_7864c.
Proof. vm_refl. Qed.
Lemma D_7864c : decode_any W_7864c = Some (ShiftImm ALU_SRL 15 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78650 : bv 32 := 0x00d706b3.
Lemma F_78650 : fetch_word Asan.M.loaded_segments (0x786a0 : word) = Some W_78650.
Proof. vm_refl. Qed.
Lemma D_78650 : decode_any W_78650 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_78654 : bv 32 := 0x00f70733.
Lemma F_78654 : fetch_word Asan.M.loaded_segments (0x786a4 : word) = Some W_78654.
Proof. vm_refl. Qed.
Lemma D_78654 : decode_any W_78654 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78658 : bv 32 := 0xff86f793.
Lemma F_78658 : fetch_word Asan.M.loaded_segments (0x786a8 : word) = Some W_78658.
Proof. vm_refl. Qed.
Lemma D_78658 : decode_any W_78658 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7865c : bv 32 := 0xff877813.
Lemma F_7865c : fetch_word Asan.M.loaded_segments (0x786ac : word) = Some W_7865c.
Proof. vm_refl. Qed.
Lemma D_7865c : decode_any W_7865c = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78660 : bv 32 := 0x0007b783.
Lemma F_78660 : fetch_word Asan.M.loaded_segments (0x786b0 : word) = Some W_78660.
Proof. vm_refl. Qed.
Lemma D_78660 : decode_any W_78660 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78664 : bv 32 := 0x00083803.
Lemma F_78664 : fetch_word Asan.M.loaded_segments (0x786b4 : word) = Some W_78664.
Proof. vm_refl. Qed.
Lemma D_78664 : decode_any W_78664 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78668 : bv 32 := 0x00f867b3.
Lemma F_78668 : fetch_word Asan.M.loaded_segments (0x786b8 : word) = Some W_78668.
Proof. vm_refl. Qed.
Lemma D_78668 : decode_any W_78668 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7866c : bv 32 := 0x2a079a63.
Lemma F_7866c : fetch_word Asan.M.loaded_segments (0x786bc : word) = Some W_7866c.
Proof. vm_refl. Qed.
Lemma D_7866c : decode_any W_7866c = Some (Branch BC_NE 15 0 692, 4%Z).
Proof. vm_refl. Qed.

Definition W_78670 : bv 32 := 0xfff54693.
Lemma F_78670 : fetch_word Asan.M.loaded_segments (0x786c0 : word) = Some W_78670.
Proof. vm_refl. Qed.
Lemma D_78670 : decode_any W_78670 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78674 : bv 32 := 0x0cc6ea63.
Lemma F_78674 : fetch_word Asan.M.loaded_segments (0x786c4 : word) = Some W_78674.
Proof. vm_refl. Qed.
Lemma D_78674 : decode_any W_78674 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_78678 : bv 32 := 0xfbf00693.
Lemma F_78678 : fetch_word Asan.M.loaded_segments (0x786c8 : word) = Some W_78678.
Proof. vm_refl. Qed.
Lemma D_78678 : decode_any W_78678 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7867c : bv 32 := 0x1566f863.
Lemma F_7867c : fetch_word Asan.M.loaded_segments (0x786cc : word) = Some W_7867c.
Proof. vm_refl. Qed.
Lemma D_7867c : decode_any W_7867c = Some (Branch BC_GEU 13 22 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_78680 : bv 32 := 0x000c1697.
Lemma F_78680 : fetch_word Asan.M.loaded_segments (0x786d0 : word) = Some W_78680.
Proof. vm_refl. Qed.
Lemma D_78680 : decode_any W_78680 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_78684 : bv 32 := 0xae86b683.
Lemma F_78684 : fetch_word Asan.M.loaded_segments (0x786d4 : word) = Some W_78684.
Proof. vm_refl. Qed.
Lemma D_78684 : decode_any W_78684 = Some (Load SZ8 true 13 13 2792, 4%Z).
Proof. vm_refl. Qed.

Definition W_78688 : bv 32 := 0x0006b703.
Lemma F_78688 : fetch_word Asan.M.loaded_segments (0x786d8 : word) = Some W_78688.
Proof. vm_refl. Qed.
Lemma D_78688 : decode_any W_78688 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7868c : bv 32 := 0xfff98993.
Lemma F_7868c : fetch_word Asan.M.loaded_segments (0x786dc : word) = Some W_7868c.
Proof. vm_refl. Qed.
Lemma D_7868c : decode_any W_7868c = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78690 : bv 32 := 0x00355693.
Lemma F_78690 : fetch_word Asan.M.loaded_segments (0x786e0 : word) = Some W_78690.
Proof. vm_refl. Qed.
Lemma D_78690 : decode_any W_78690 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78694 : bv 32 := 0x0039d793.
Lemma F_78694 : fetch_word Asan.M.loaded_segments (0x786e4 : word) = Some W_78694.
Proof. vm_refl. Qed.
Lemma D_78694 : decode_any W_78694 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78698 : bv 32 := 0x00d706b3.
Lemma F_78698 : fetch_word Asan.M.loaded_segments (0x786e8 : word) = Some W_78698.
Proof. vm_refl. Qed.
Lemma D_78698 : decode_any W_78698 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7869c : bv 32 := 0x00f70733.
Lemma F_7869c : fetch_word Asan.M.loaded_segments (0x786ec : word) = Some W_7869c.
Proof. vm_refl. Qed.
Lemma D_7869c : decode_any W_7869c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_786a0 : bv 32 := 0xff86f793.
Lemma F_786a0 : fetch_word Asan.M.loaded_segments (0x786f0 : word) = Some W_786a0.
Proof. vm_refl. Qed.
Lemma D_786a0 : decode_any W_786a0 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_786a4 : bv 32 := 0xff877813.
Lemma F_786a4 : fetch_word Asan.M.loaded_segments (0x786f4 : word) = Some W_786a4.
Proof. vm_refl. Qed.
Lemma D_786a4 : decode_any W_786a4 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_786a8 : bv 32 := 0x0007b783.
Lemma F_786a8 : fetch_word Asan.M.loaded_segments (0x786f8 : word) = Some W_786a8.
Proof. vm_refl. Qed.
Lemma D_786a8 : decode_any W_786a8 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_786ac : bv 32 := 0x00083803.
Lemma F_786ac : fetch_word Asan.M.loaded_segments (0x786fc : word) = Some W_786ac.
Proof. vm_refl. Qed.
Lemma D_786ac : decode_any W_786ac = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_786b0 : bv 32 := 0x00f867b3.
Lemma F_786b0 : fetch_word Asan.M.loaded_segments (0x78700 : word) = Some W_786b0.
Proof. vm_refl. Qed.
Lemma D_786b0 : decode_any W_786b0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_786b4 : bv 32 := 0x30079863.
Lemma F_786b4 : fetch_word Asan.M.loaded_segments (0x78704 : word) = Some W_786b4.
Proof. vm_refl. Qed.
Lemma D_786b4 : decode_any W_786b4 = Some (Branch BC_NE 15 0 784, 4%Z).
Proof. vm_refl. Qed.

Definition W_786b8 : bv 32 := 0x000c3697.
Lemma F_786b8 : fetch_word Asan.M.loaded_segments (0x78708 : word) = Some W_786b8.
Proof. vm_refl. Qed.
Lemma D_786b8 : decode_any W_786b8 = Some (Auipc 13 195, 4%Z).
Proof. vm_refl. Qed.

Definition W_786bc : bv 32 := 0xab86b683.
Lemma F_786bc : fetch_word Asan.M.loaded_segments (0x7870c : word) = Some W_786bc.
Proof. vm_refl. Qed.
Lemma D_786bc : decode_any W_786bc = Some (Load SZ8 true 13 13 2744, 4%Z).
Proof. vm_refl. Qed.

Definition W_786c0 : bv 32 := 0x000680e7.
Lemma F_786c0 : fetch_word Asan.M.loaded_segments (0x78710 : word) = Some W_786c0.
Proof. vm_refl. Qed.
Lemma D_786c0 : decode_any W_786c0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_786c4 : bv 32 := 0x07010113.
Lemma F_786c4 : fetch_word Asan.M.loaded_segments (0x78714 : word) = Some W_786c4.
Proof. vm_refl. Qed.
Lemma D_786c4 : decode_any W_786c4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_786c8 : bv 32 := 0x7e813083.
Lemma F_786c8 : fetch_word Asan.M.loaded_segments (0x78718 : word) = Some W_786c8.
Proof. vm_refl. Qed.
Lemma D_786c8 : decode_any W_786c8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_786cc : bv 32 := 0x7e013403.
Lemma F_786cc : fetch_word Asan.M.loaded_segments (0x7871c : word) = Some W_786cc.
Proof. vm_refl. Qed.
Lemma D_786cc : decode_any W_786cc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_786d0 : bv 32 := 0x7d813483.
Lemma F_786d0 : fetch_word Asan.M.loaded_segments (0x78720 : word) = Some W_786d0.
Proof. vm_refl. Qed.
Lemma D_786d0 : decode_any W_786d0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_786d4 : bv 32 := 0x7d013903.
Lemma F_786d4 : fetch_word Asan.M.loaded_segments (0x78724 : word) = Some W_786d4.
Proof. vm_refl. Qed.
Lemma D_786d4 : decode_any W_786d4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_786d8 : bv 32 := 0x7c813983.
Lemma F_786d8 : fetch_word Asan.M.loaded_segments (0x78728 : word) = Some W_786d8.
Proof. vm_refl. Qed.
Lemma D_786d8 : decode_any W_786d8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_786dc : bv 32 := 0x7c013a03.
Lemma F_786dc : fetch_word Asan.M.loaded_segments (0x7872c : word) = Some W_786dc.
Proof. vm_refl. Qed.
Lemma D_786dc : decode_any W_786dc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_786e0 : bv 32 := 0x7b813a83.
Lemma F_786e0 : fetch_word Asan.M.loaded_segments (0x78730 : word) = Some W_786e0.
Proof. vm_refl. Qed.
Lemma D_786e0 : decode_any W_786e0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_786e4 : bv 32 := 0x7b013b03.
Lemma F_786e4 : fetch_word Asan.M.loaded_segments (0x78734 : word) = Some W_786e4.
Proof. vm_refl. Qed.
Lemma D_786e4 : decode_any W_786e4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_786e8 : bv 32 := 0x7a813b83.
Lemma F_786e8 : fetch_word Asan.M.loaded_segments (0x78738 : word) = Some W_786e8.
Proof. vm_refl. Qed.
Lemma D_786e8 : decode_any W_786e8 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_786ec : bv 32 := 0x7f010113.
Lemma F_786ec : fetch_word Asan.M.loaded_segments (0x7873c : word) = Some W_786ec.
Proof. vm_refl. Qed.
Lemma D_786ec : decode_any W_786ec = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_786f0 : bv 32 := 0x00008067.
Lemma F_786f0 : fetch_word Asan.M.loaded_segments (0x78740 : word) = Some W_786f0.
Proof. vm_refl. Qed.
Lemma D_786f0 : decode_any W_786f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_787cc : bv 32 := 0x22061663.
Lemma F_787cc : fetch_word Asan.M.loaded_segments (0x7881c : word) = Some W_787cc.
Proof. vm_refl. Qed.
Lemma D_787cc : decode_any W_787cc = Some (Branch BC_NE 12 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_787d0 : bv 32 := 0xee9ff06f.
Lemma F_787d0 : fetch_word Asan.M.loaded_segments (0x78820 : word) = Some W_787d0.
Proof. vm_refl. Qed.
Lemma D_787d0 : decode_any W_787d0 = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

Definition W_78918 : bv 32 := 0x02061e63.
Lemma F_78918 : fetch_word Asan.M.loaded_segments (0x78968 : word) = Some W_78918.
Proof. vm_refl. Qed.
Lemma D_78918 : decode_any W_78918 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7891c : bv 32 := 0xd55ff06f.
Lemma F_7891c : fetch_word Asan.M.loaded_segments (0x7896c : word) = Some W_7891c.
Proof. vm_refl. Qed.
Lemma D_7891c : decode_any W_7891c = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

Definition W_78920 : bv 32 := 0x00070783.
Lemma F_78920 : fetch_word Asan.M.loaded_segments (0x78970 : word) = Some W_78920.
Proof. vm_refl. Qed.
Lemma D_78920 : decode_any W_78920 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78924 : bv 32 := 0x007af813.
Lemma F_78924 : fetch_word Asan.M.loaded_segments (0x78974 : word) = Some W_78924.
Proof. vm_refl. Qed.
Lemma D_78924 : decode_any W_78924 = Some (OpImm ALU_AND 16 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_78928 : bv 32 := 0x00f038b3.
Lemma F_78928 : fetch_word Asan.M.loaded_segments (0x78978 : word) = Some W_78928.
Proof. vm_refl. Qed.
Lemma D_78928 : decode_any W_78928 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7892c : bv 32 := 0x00f827b3.
Lemma F_7892c : fetch_word Asan.M.loaded_segments (0x7897c : word) = Some W_7892c.
Proof. vm_refl. Qed.
Lemma D_7892c : decode_any W_7892c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78930 : bv 32 := 0x0017c793.
Lemma F_78930 : fetch_word Asan.M.loaded_segments (0x78980 : word) = Some W_78930.
Proof. vm_refl. Qed.
Lemma D_78930 : decode_any W_78930 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_78934 : bv 32 := 0x00f8f7b3.
Lemma F_78934 : fetch_word Asan.M.loaded_segments (0x78984 : word) = Some W_78934.
Proof. vm_refl. Qed.
Lemma D_78934 : decode_any W_78934 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78938 : bv 32 := 0x00e6fa63.
Lemma F_78938 : fetch_word Asan.M.loaded_segments (0x78988 : word) = Some W_78938.
Proof. vm_refl. Qed.
Lemma D_78938 : decode_any W_78938 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7893c : bv 32 := 0x0006c803.
Lemma F_7893c : fetch_word Asan.M.loaded_segments (0x7898c : word) = Some W_7893c.
Proof. vm_refl. Qed.
Lemma D_7893c : decode_any W_7893c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78940 : bv 32 := 0x00168693.
Lemma F_78940 : fetch_word Asan.M.loaded_segments (0x78990 : word) = Some W_78940.
Proof. vm_refl. Qed.
Lemma D_78940 : decode_any W_78940 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_78944 : bv 32 := 0x00f867b3.
Lemma F_78944 : fetch_word Asan.M.loaded_segments (0x78994 : word) = Some W_78944.
Proof. vm_refl. Qed.
Lemma D_78944 : decode_any W_78944 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78948 : bv 32 := 0xfee69ae3.
Lemma F_78948 : fetch_word Asan.M.loaded_segments (0x78998 : word) = Some W_78948.
Proof. vm_refl. Qed.
Lemma D_78948 : decode_any W_78948 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7894c : bv 32 := 0x0ff7f693.
Lemma F_7894c : fetch_word Asan.M.loaded_segments (0x7899c : word) = Some W_7894c.
Proof. vm_refl. Qed.
Lemma D_7894c : decode_any W_7894c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_78950 : bv 32 := 0xd20680e3.
Lemma F_78950 : fetch_word Asan.M.loaded_segments (0x789a0 : word) = Some W_78950.
Proof. vm_refl. Qed.
Lemma D_78950 : decode_any W_78950 = Some (Branch BC_EQ 13 0 7456, 4%Z).
Proof. vm_refl. Qed.

Definition W_78954 : bv 32 := 0x00050a93.
Lemma F_78954 : fetch_word Asan.M.loaded_segments (0x789a4 : word) = Some W_78954.
Proof. vm_refl. Qed.
Lemma D_78954 : decode_any W_78954 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78958 : bv 32 := 0x00058513.
Lemma F_78958 : fetch_word Asan.M.loaded_segments (0x789a8 : word) = Some W_78958.
Proof. vm_refl. Qed.
Lemma D_78958 : decode_any W_78958 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7895c : bv 32 := 0x00058b93.
Lemma F_7895c : fetch_word Asan.M.loaded_segments (0x789ac : word) = Some W_7895c.
Proof. vm_refl. Qed.
Lemma D_7895c : decode_any W_7895c = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78960 : bv 32 := 0x00060593.
Lemma F_78960 : fetch_word Asan.M.loaded_segments (0x789b0 : word) = Some W_78960.
Proof. vm_refl. Qed.
Lemma D_78960 : decode_any W_78960 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78964 : bv 32 := 0x00060493.
Lemma F_78964 : fetch_word Asan.M.loaded_segments (0x789b4 : word) = Some W_78964.
Proof. vm_refl. Qed.
Lemma D_78964 : decode_any W_78964 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78968 : bv 32 := 0x48c030ef.
Lemma F_78968 : fetch_word Asan.M.loaded_segments (0x789b8 : word) = Some W_78968.
Proof. vm_refl. Qed.
Lemma D_78968 : decode_any W_78968 = Some (Jal 1 13452, 4%Z).
Proof. vm_refl. Qed.

Definition W_7896c : bv 32 := 0x000b8593.
Lemma F_7896c : fetch_word Asan.M.loaded_segments (0x789bc : word) = Some W_7896c.
Proof. vm_refl. Qed.
Lemma D_7896c : decode_any W_7896c = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78970 : bv 32 := 0x00048613.
Lemma F_78970 : fetch_word Asan.M.loaded_segments (0x789c0 : word) = Some W_78970.
Proof. vm_refl. Qed.
Lemma D_78970 : decode_any W_78970 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78974 : bv 32 := 0x00050913.
Lemma F_78974 : fetch_word Asan.M.loaded_segments (0x789c4 : word) = Some W_78974.
Proof. vm_refl. Qed.
Lemma D_78974 : decode_any W_78974 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78978 : bv 32 := 0x000a8513.
Lemma F_78978 : fetch_word Asan.M.loaded_segments (0x789c8 : word) = Some W_78978.
Proof. vm_refl. Qed.
Lemma D_78978 : decode_any W_78978 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7897c : bv 32 := 0xce090ae3.
Lemma F_7897c : fetch_word Asan.M.loaded_segments (0x789cc : word) = Some W_7897c.
Proof. vm_refl. Qed.
Lemma D_7897c : decode_any W_7897c = Some (Branch BC_EQ 18 0 7412, 4%Z).
Proof. vm_refl. Qed.

Definition W_789c4 : bv 32 := 0x00070783.
Lemma F_789c4 : fetch_word Asan.M.loaded_segments (0x78a14 : word) = Some W_789c4.
Proof. vm_refl. Qed.
Lemma D_789c4 : decode_any W_789c4 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_789c8 : bv 32 := 0x0079f813.
Lemma F_789c8 : fetch_word Asan.M.loaded_segments (0x78a18 : word) = Some W_789c8.
Proof. vm_refl. Qed.
Lemma D_789c8 : decode_any W_789c8 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_789cc : bv 32 := 0x00f038b3.
Lemma F_789cc : fetch_word Asan.M.loaded_segments (0x78a1c : word) = Some W_789cc.
Proof. vm_refl. Qed.
Lemma D_789cc : decode_any W_789cc = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_789d0 : bv 32 := 0x00f827b3.
Lemma F_789d0 : fetch_word Asan.M.loaded_segments (0x78a20 : word) = Some W_789d0.
Proof. vm_refl. Qed.
Lemma D_789d0 : decode_any W_789d0 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_789d4 : bv 32 := 0x0017c793.
Lemma F_789d4 : fetch_word Asan.M.loaded_segments (0x78a24 : word) = Some W_789d4.
Proof. vm_refl. Qed.
Lemma D_789d4 : decode_any W_789d4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_789d8 : bv 32 := 0x00f8f7b3.
Lemma F_789d8 : fetch_word Asan.M.loaded_segments (0x78a28 : word) = Some W_789d8.
Proof. vm_refl. Qed.
Lemma D_789d8 : decode_any W_789d8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_789dc : bv 32 := 0x00e6fa63.
Lemma F_789dc : fetch_word Asan.M.loaded_segments (0x78a2c : word) = Some W_789dc.
Proof. vm_refl. Qed.
Lemma D_789dc : decode_any W_789dc = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_789e0 : bv 32 := 0x0006c803.
Lemma F_789e0 : fetch_word Asan.M.loaded_segments (0x78a30 : word) = Some W_789e0.
Proof. vm_refl. Qed.
Lemma D_789e0 : decode_any W_789e0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_789e4 : bv 32 := 0x00168693.
Lemma F_789e4 : fetch_word Asan.M.loaded_segments (0x78a34 : word) = Some W_789e4.
Proof. vm_refl. Qed.
Lemma D_789e4 : decode_any W_789e4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_789e8 : bv 32 := 0x00f867b3.
Lemma F_789e8 : fetch_word Asan.M.loaded_segments (0x78a38 : word) = Some W_789e8.
Proof. vm_refl. Qed.
Lemma D_789e8 : decode_any W_789e8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_789ec : bv 32 := 0xfee69ae3.
Lemma F_789ec : fetch_word Asan.M.loaded_segments (0x78a3c : word) = Some W_789ec.
Proof. vm_refl. Qed.
Lemma D_789ec : decode_any W_789ec = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_789f0 : bv 32 := 0x0ff7f693.
Lemma F_789f0 : fetch_word Asan.M.loaded_segments (0x78a40 : word) = Some W_789f0.
Proof. vm_refl. Qed.
Lemma D_789f0 : decode_any W_789f0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_789f4 : bv 32 := 0xcc0682e3.
Lemma F_789f4 : fetch_word Asan.M.loaded_segments (0x78a44 : word) = Some W_789f4.
Proof. vm_refl. Qed.
Lemma D_789f4 : decode_any W_789f4 = Some (Branch BC_EQ 13 0 7364, 4%Z).
Proof. vm_refl. Qed.

Definition W_789f8 : bv 32 := 0x00050493.
Lemma F_789f8 : fetch_word Asan.M.loaded_segments (0x78a48 : word) = Some W_789f8.
Proof. vm_refl. Qed.
Lemma D_789f8 : decode_any W_789f8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_789fc : bv 32 := 0x00058a93.
Lemma F_789fc : fetch_word Asan.M.loaded_segments (0x78a4c : word) = Some W_789fc.
Proof. vm_refl. Qed.
Lemma D_789fc : decode_any W_789fc = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a00 : bv 32 := 0x00060593.
Lemma F_78a00 : fetch_word Asan.M.loaded_segments (0x78a50 : word) = Some W_78a00.
Proof. vm_refl. Qed.
Lemma D_78a00 : decode_any W_78a00 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a04 : bv 32 := 0x00060913.
Lemma F_78a04 : fetch_word Asan.M.loaded_segments (0x78a54 : word) = Some W_78a04.
Proof. vm_refl. Qed.
Lemma D_78a04 : decode_any W_78a04 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a08 : bv 32 := 0x3ec030ef.
Lemma F_78a08 : fetch_word Asan.M.loaded_segments (0x78a58 : word) = Some W_78a08.
Proof. vm_refl. Qed.
Lemma D_78a08 : decode_any W_78a08 = Some (Jal 1 13292, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a0c : bv 32 := 0x000a8593.
Lemma F_78a0c : fetch_word Asan.M.loaded_segments (0x78a5c : word) = Some W_78a0c.
Proof. vm_refl. Qed.
Lemma D_78a0c : decode_any W_78a0c = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a10 : bv 32 := 0x00090613.
Lemma F_78a10 : fetch_word Asan.M.loaded_segments (0x78a60 : word) = Some W_78a10.
Proof. vm_refl. Qed.
Lemma D_78a10 : decode_any W_78a10 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a14 : bv 32 := 0x00050993.
Lemma F_78a14 : fetch_word Asan.M.loaded_segments (0x78a64 : word) = Some W_78a14.
Proof. vm_refl. Qed.
Lemma D_78a14 : decode_any W_78a14 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a18 : bv 32 := 0x00048513.
Lemma F_78a18 : fetch_word Asan.M.loaded_segments (0x78a68 : word) = Some W_78a18.
Proof. vm_refl. Qed.
Lemma D_78a18 : decode_any W_78a18 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a1c : bv 32 := 0xc8098ee3.
Lemma F_78a1c : fetch_word Asan.M.loaded_segments (0x78a6c : word) = Some W_78a1c.
Proof. vm_refl. Qed.
Lemma D_78a1c : decode_any W_78a1c = Some (Branch BC_EQ 19 0 7324, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a64 : bv 32 := 0x81010113.
Lemma F_78a64 : fetch_word Asan.M.loaded_segments (0x78ab4 : word) = Some W_78a64.
Proof. vm_refl. Qed.
Lemma D_78a64 : decode_any W_78a64 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a68 : bv 32 := 0x7e113423.
Lemma F_78a68 : fetch_word Asan.M.loaded_segments (0x78ab8 : word) = Some W_78a68.
Proof. vm_refl. Qed.
Lemma D_78a68 : decode_any W_78a68 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a6c : bv 32 := 0x7e813023.
Lemma F_78a6c : fetch_word Asan.M.loaded_segments (0x78abc : word) = Some W_78a6c.
Proof. vm_refl. Qed.
Lemma D_78a6c : decode_any W_78a6c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a70 : bv 32 := 0x7c913c23.
Lemma F_78a70 : fetch_word Asan.M.loaded_segments (0x78ac0 : word) = Some W_78a70.
Proof. vm_refl. Qed.
Lemma D_78a70 : decode_any W_78a70 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a74 : bv 32 := 0x7d213823.
Lemma F_78a74 : fetch_word Asan.M.loaded_segments (0x78ac4 : word) = Some W_78a74.
Proof. vm_refl. Qed.
Lemma D_78a74 : decode_any W_78a74 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a78 : bv 32 := 0x7d313423.
Lemma F_78a78 : fetch_word Asan.M.loaded_segments (0x78ac8 : word) = Some W_78a78.
Proof. vm_refl. Qed.
Lemma D_78a78 : decode_any W_78a78 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a7c : bv 32 := 0x7d413023.
Lemma F_78a7c : fetch_word Asan.M.loaded_segments (0x78acc : word) = Some W_78a7c.
Proof. vm_refl. Qed.
Lemma D_78a7c : decode_any W_78a7c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a80 : bv 32 := 0x7b513c23.
Lemma F_78a80 : fetch_word Asan.M.loaded_segments (0x78ad0 : word) = Some W_78a80.
Proof. vm_refl. Qed.
Lemma D_78a80 : decode_any W_78a80 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a84 : bv 32 := 0x7f010413.
Lemma F_78a84 : fetch_word Asan.M.loaded_segments (0x78ad4 : word) = Some W_78a84.
Proof. vm_refl. Qed.
Lemma D_78a84 : decode_any W_78a84 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a88 : bv 32 := 0xfa010113.
Lemma F_78a88 : fetch_word Asan.M.loaded_segments (0x78ad8 : word) = Some W_78a88.
Proof. vm_refl. Qed.
Lemma D_78a88 : decode_any W_78a88 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a8c : bv 32 := 0x000c1697.
Lemma F_78a8c : fetch_word Asan.M.loaded_segments (0x78adc : word) = Some W_78a8c.
Proof. vm_refl. Qed.
Lemma D_78a8c : decode_any W_78a8c = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a90 : bv 32 := 0x2446b683.
Lemma F_78a90 : fetch_word Asan.M.loaded_segments (0x78ae0 : word) = Some W_78a90.
Proof. vm_refl. Qed.
Lemma D_78a90 : decode_any W_78a90 = Some (Load SZ8 true 13 13 580, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a94 : bv 32 := 0x0006c683.
Lemma F_78a94 : fetch_word Asan.M.loaded_segments (0x78ae4 : word) = Some W_78a94.
Proof. vm_refl. Qed.
Lemma D_78a94 : decode_any W_78a94 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a98 : bv 32 := 0x08068863.
Lemma F_78a98 : fetch_word Asan.M.loaded_segments (0x78ae8 : word) = Some W_78a98.
Proof. vm_refl. Qed.
Lemma D_78a98 : decode_any W_78a98 = Some (Branch BC_EQ 13 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_78a9c : bv 32 := 0xfff54693.
Lemma F_78a9c : fetch_word Asan.M.loaded_segments (0x78aec : word) = Some W_78a9c.
Proof. vm_refl. Qed.
Lemma D_78a9c : decode_any W_78a9c = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78aa0 : bv 32 := 0x80040a13.
Lemma F_78aa0 : fetch_word Asan.M.loaded_segments (0x78af0 : word) = Some W_78aa0.
Proof. vm_refl. Qed.
Lemma D_78aa0 : decode_any W_78aa0 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_78aa4 : bv 32 := 0xfb0a0a13.
Lemma F_78aa4 : fetch_word Asan.M.loaded_segments (0x78af4 : word) = Some W_78aa4.
Proof. vm_refl. Qed.
Lemma D_78aa4 : decode_any W_78aa4 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_78aa8 : bv 32 := 0x0cc6e663.
Lemma F_78aa8 : fetch_word Asan.M.loaded_segments (0x78af8 : word) = Some W_78aa8.
Proof. vm_refl. Qed.
Lemma D_78aa8 : decode_any W_78aa8 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_78aac : bv 32 := 0xfbf60693.
Lemma F_78aac : fetch_word Asan.M.loaded_segments (0x78afc : word) = Some W_78aac.
Proof. vm_refl. Qed.
Lemma D_78aac : decode_any W_78aac = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ab0 : bv 32 := 0xfbf00713.
Lemma F_78ab0 : fetch_word Asan.M.loaded_segments (0x78b00 : word) = Some W_78ab0.
Proof. vm_refl. Qed.
Lemma D_78ab0 : decode_any W_78ab0 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ab4 : bv 32 := 0x14d77463.
Lemma F_78ab4 : fetch_word Asan.M.loaded_segments (0x78b04 : word) = Some W_78ab4.
Proof. vm_refl. Qed.
Lemma D_78ab4 : decode_any W_78ab4 = Some (Branch BC_GEU 14 13 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ab8 : bv 32 := 0x000c0697.
Lemma F_78ab8 : fetch_word Asan.M.loaded_segments (0x78b08 : word) = Some W_78ab8.
Proof. vm_refl. Qed.
Lemma D_78ab8 : decode_any W_78ab8 = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_78abc : bv 32 := 0x6b06b683.
Lemma F_78abc : fetch_word Asan.M.loaded_segments (0x78b0c : word) = Some W_78abc.
Proof. vm_refl. Qed.
Lemma D_78abc : decode_any W_78abc = Some (Load SZ8 true 13 13 1712, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ac0 : bv 32 := 0x00c507b3.
Lemma F_78ac0 : fetch_word Asan.M.loaded_segments (0x78b10 : word) = Some W_78ac0.
Proof. vm_refl. Qed.
Lemma D_78ac0 : decode_any W_78ac0 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ac4 : bv 32 := 0x0006b703.
Lemma F_78ac4 : fetch_word Asan.M.loaded_segments (0x78b14 : word) = Some W_78ac4.
Proof. vm_refl. Qed.
Lemma D_78ac4 : decode_any W_78ac4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ac8 : bv 32 := 0x00355693.
Lemma F_78ac8 : fetch_word Asan.M.loaded_segments (0x78b18 : word) = Some W_78ac8.
Proof. vm_refl. Qed.
Lemma D_78ac8 : decode_any W_78ac8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78acc : bv 32 := 0xfff78793.
Lemma F_78acc : fetch_word Asan.M.loaded_segments (0x78b1c : word) = Some W_78acc.
Proof. vm_refl. Qed.
Lemma D_78acc : decode_any W_78acc = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ad0 : bv 32 := 0x0037d813.
Lemma F_78ad0 : fetch_word Asan.M.loaded_segments (0x78b20 : word) = Some W_78ad0.
Proof. vm_refl. Qed.
Lemma D_78ad0 : decode_any W_78ad0 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ad4 : bv 32 := 0x00d706b3.
Lemma F_78ad4 : fetch_word Asan.M.loaded_segments (0x78b24 : word) = Some W_78ad4.
Proof. vm_refl. Qed.
Lemma D_78ad4 : decode_any W_78ad4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ad8 : bv 32 := 0x01070733.
Lemma F_78ad8 : fetch_word Asan.M.loaded_segments (0x78b28 : word) = Some W_78ad8.
Proof. vm_refl. Qed.
Lemma D_78ad8 : decode_any W_78ad8 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78adc : bv 32 := 0xff86f813.
Lemma F_78adc : fetch_word Asan.M.loaded_segments (0x78b2c : word) = Some W_78adc.
Proof. vm_refl. Qed.
Lemma D_78adc : decode_any W_78adc = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ae0 : bv 32 := 0xff877893.
Lemma F_78ae0 : fetch_word Asan.M.loaded_segments (0x78b30 : word) = Some W_78ae0.
Proof. vm_refl. Qed.
Lemma D_78ae0 : decode_any W_78ae0 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ae4 : bv 32 := 0x00083803.
Lemma F_78ae4 : fetch_word Asan.M.loaded_segments (0x78b34 : word) = Some W_78ae4.
Proof. vm_refl. Qed.
Lemma D_78ae4 : decode_any W_78ae4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ae8 : bv 32 := 0x0008b883.
Lemma F_78ae8 : fetch_word Asan.M.loaded_segments (0x78b38 : word) = Some W_78ae8.
Proof. vm_refl. Qed.
Lemma D_78ae8 : decode_any W_78ae8 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78aec : bv 32 := 0x0108e833.
Lemma F_78aec : fetch_word Asan.M.loaded_segments (0x78b3c : word) = Some W_78aec.
Proof. vm_refl. Qed.
Lemma D_78aec : decode_any W_78aec = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78af0 : bv 32 := 0x10081a63.
Lemma F_78af0 : fetch_word Asan.M.loaded_segments (0x78b40 : word) = Some W_78af0.
Proof. vm_refl. Qed.
Lemma D_78af0 : decode_any W_78af0 = Some (Branch BC_NE 16 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_78af4 : bv 32 := 0x000c2697.
Lemma F_78af4 : fetch_word Asan.M.loaded_segments (0x78b44 : word) = Some W_78af4.
Proof. vm_refl. Qed.
Lemma D_78af4 : decode_any W_78af4 = Some (Auipc 13 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_78af8 : bv 32 := 0x6846b683.
Lemma F_78af8 : fetch_word Asan.M.loaded_segments (0x78b48 : word) = Some W_78af8.
Proof. vm_refl. Qed.
Lemma D_78af8 : decode_any W_78af8 = Some (Load SZ8 true 13 13 1668, 4%Z).
Proof. vm_refl. Qed.

Definition W_78afc : bv 32 := 0x000680e7.
Lemma F_78afc : fetch_word Asan.M.loaded_segments (0x78b4c : word) = Some W_78afc.
Proof. vm_refl. Qed.
Lemma D_78afc : decode_any W_78afc = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78b00 : bv 32 := 0x06010113.
Lemma F_78b00 : fetch_word Asan.M.loaded_segments (0x78b50 : word) = Some W_78b00.
Proof. vm_refl. Qed.
Lemma D_78b00 : decode_any W_78b00 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_78b04 : bv 32 := 0x7e813083.
Lemma F_78b04 : fetch_word Asan.M.loaded_segments (0x78b54 : word) = Some W_78b04.
Proof. vm_refl. Qed.
Lemma D_78b04 : decode_any W_78b04 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_78b08 : bv 32 := 0x7e013403.
Lemma F_78b08 : fetch_word Asan.M.loaded_segments (0x78b58 : word) = Some W_78b08.
Proof. vm_refl. Qed.
Lemma D_78b08 : decode_any W_78b08 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_78b0c : bv 32 := 0x7d813483.
Lemma F_78b0c : fetch_word Asan.M.loaded_segments (0x78b5c : word) = Some W_78b0c.
Proof. vm_refl. Qed.
Lemma D_78b0c : decode_any W_78b0c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_78b10 : bv 32 := 0x7d013903.
Lemma F_78b10 : fetch_word Asan.M.loaded_segments (0x78b60 : word) = Some W_78b10.
Proof. vm_refl. Qed.
Lemma D_78b10 : decode_any W_78b10 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_78b14 : bv 32 := 0x7c813983.
Lemma F_78b14 : fetch_word Asan.M.loaded_segments (0x78b64 : word) = Some W_78b14.
Proof. vm_refl. Qed.
Lemma D_78b14 : decode_any W_78b14 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_78b18 : bv 32 := 0x7c013a03.
Lemma F_78b18 : fetch_word Asan.M.loaded_segments (0x78b68 : word) = Some W_78b18.
Proof. vm_refl. Qed.
Lemma D_78b18 : decode_any W_78b18 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_78b1c : bv 32 := 0x7b813a83.
Lemma F_78b1c : fetch_word Asan.M.loaded_segments (0x78b6c : word) = Some W_78b1c.
Proof. vm_refl. Qed.
Lemma D_78b1c : decode_any W_78b1c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_78b20 : bv 32 := 0x7f010113.
Lemma F_78b20 : fetch_word Asan.M.loaded_segments (0x78b70 : word) = Some W_78b20.
Proof. vm_refl. Qed.
Lemma D_78b20 : decode_any W_78b20 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_78b24 : bv 32 := 0x00008067.
Lemma F_78b24 : fetch_word Asan.M.loaded_segments (0x78b74 : word) = Some W_78b24.
Proof. vm_refl. Qed.
Lemma D_78b24 : decode_any W_78b24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78bfc : bv 32 := 0x02061e63.
Lemma F_78bfc : fetch_word Asan.M.loaded_segments (0x78c4c : word) = Some W_78bfc.
Proof. vm_refl. Qed.
Lemma D_78bfc : decode_any W_78bfc = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c00 : bv 32 := 0xef5ff06f.
Lemma F_78c00 : fetch_word Asan.M.loaded_segments (0x78c50 : word) = Some W_78c00.
Proof. vm_refl. Qed.
Lemma D_78c00 : decode_any W_78c00 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c04 : bv 32 := 0x00070803.
Lemma F_78c04 : fetch_word Asan.M.loaded_segments (0x78c54 : word) = Some W_78c04.
Proof. vm_refl. Qed.
Lemma D_78c04 : decode_any W_78c04 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c08 : bv 32 := 0x0077f793.
Lemma F_78c08 : fetch_word Asan.M.loaded_segments (0x78c58 : word) = Some W_78c08.
Proof. vm_refl. Qed.
Lemma D_78c08 : decode_any W_78c08 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c0c : bv 32 := 0x010038b3.
Lemma F_78c0c : fetch_word Asan.M.loaded_segments (0x78c5c : word) = Some W_78c0c.
Proof. vm_refl. Qed.
Lemma D_78c0c : decode_any W_78c0c = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c10 : bv 32 := 0x0107a7b3.
Lemma F_78c10 : fetch_word Asan.M.loaded_segments (0x78c60 : word) = Some W_78c10.
Proof. vm_refl. Qed.
Lemma D_78c10 : decode_any W_78c10 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c14 : bv 32 := 0x0017c793.
Lemma F_78c14 : fetch_word Asan.M.loaded_segments (0x78c64 : word) = Some W_78c14.
Proof. vm_refl. Qed.
Lemma D_78c14 : decode_any W_78c14 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c18 : bv 32 := 0x00f8f7b3.
Lemma F_78c18 : fetch_word Asan.M.loaded_segments (0x78c68 : word) = Some W_78c18.
Proof. vm_refl. Qed.
Lemma D_78c18 : decode_any W_78c18 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c1c : bv 32 := 0x00e6fa63.
Lemma F_78c1c : fetch_word Asan.M.loaded_segments (0x78c6c : word) = Some W_78c1c.
Proof. vm_refl. Qed.
Lemma D_78c1c : decode_any W_78c1c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c20 : bv 32 := 0x0006c803.
Lemma F_78c20 : fetch_word Asan.M.loaded_segments (0x78c70 : word) = Some W_78c20.
Proof. vm_refl. Qed.
Lemma D_78c20 : decode_any W_78c20 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c24 : bv 32 := 0x00168693.
Lemma F_78c24 : fetch_word Asan.M.loaded_segments (0x78c74 : word) = Some W_78c24.
Proof. vm_refl. Qed.
Lemma D_78c24 : decode_any W_78c24 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c28 : bv 32 := 0x00f867b3.
Lemma F_78c28 : fetch_word Asan.M.loaded_segments (0x78c78 : word) = Some W_78c28.
Proof. vm_refl. Qed.
Lemma D_78c28 : decode_any W_78c28 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c2c : bv 32 := 0xfee69ae3.
Lemma F_78c2c : fetch_word Asan.M.loaded_segments (0x78c7c : word) = Some W_78c2c.
Proof. vm_refl. Qed.
Lemma D_78c2c : decode_any W_78c2c = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c30 : bv 32 := 0x0ff7f693.
Lemma F_78c30 : fetch_word Asan.M.loaded_segments (0x78c80 : word) = Some W_78c30.
Proof. vm_refl. Qed.
Lemma D_78c30 : decode_any W_78c30 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c34 : bv 32 := 0xec0680e3.
Lemma F_78c34 : fetch_word Asan.M.loaded_segments (0x78c84 : word) = Some W_78c34.
Proof. vm_refl. Qed.
Lemma D_78c34 : decode_any W_78c34 = Some (Branch BC_EQ 13 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c38 : bv 32 := 0x00050493.
Lemma F_78c38 : fetch_word Asan.M.loaded_segments (0x78c88 : word) = Some W_78c38.
Proof. vm_refl. Qed.
Lemma D_78c38 : decode_any W_78c38 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c3c : bv 32 := 0x00058a93.
Lemma F_78c3c : fetch_word Asan.M.loaded_segments (0x78c8c : word) = Some W_78c3c.
Proof. vm_refl. Qed.
Lemma D_78c3c : decode_any W_78c3c = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c40 : bv 32 := 0x00060593.
Lemma F_78c40 : fetch_word Asan.M.loaded_segments (0x78c90 : word) = Some W_78c40.
Proof. vm_refl. Qed.
Lemma D_78c40 : decode_any W_78c40 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c44 : bv 32 := 0x00060913.
Lemma F_78c44 : fetch_word Asan.M.loaded_segments (0x78c94 : word) = Some W_78c44.
Proof. vm_refl. Qed.
Lemma D_78c44 : decode_any W_78c44 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c48 : bv 32 := 0x1ac030ef.
Lemma F_78c48 : fetch_word Asan.M.loaded_segments (0x78c98 : word) = Some W_78c48.
Proof. vm_refl. Qed.
Lemma D_78c48 : decode_any W_78c48 = Some (Jal 1 12716, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c4c : bv 32 := 0x000a8593.
Lemma F_78c4c : fetch_word Asan.M.loaded_segments (0x78c9c : word) = Some W_78c4c.
Proof. vm_refl. Qed.
Lemma D_78c4c : decode_any W_78c4c = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c50 : bv 32 := 0x00090613.
Lemma F_78c50 : fetch_word Asan.M.loaded_segments (0x78ca0 : word) = Some W_78c50.
Proof. vm_refl. Qed.
Lemma D_78c50 : decode_any W_78c50 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c54 : bv 32 := 0x00050993.
Lemma F_78c54 : fetch_word Asan.M.loaded_segments (0x78ca4 : word) = Some W_78c54.
Proof. vm_refl. Qed.
Lemma D_78c54 : decode_any W_78c54 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c58 : bv 32 := 0x00048513.
Lemma F_78c58 : fetch_word Asan.M.loaded_segments (0x78ca8 : word) = Some W_78c58.
Proof. vm_refl. Qed.
Lemma D_78c58 : decode_any W_78c58 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78c5c : bv 32 := 0xe8098ce3.
Lemma F_78c5c : fetch_word Asan.M.loaded_segments (0x78cac : word) = Some W_78c5c.
Proof. vm_refl. Qed.
Lemma D_78c5c : decode_any W_78c5c = Some (Branch BC_EQ 19 0 7832, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ca4 : bv 32 := 0x81010113.
Lemma F_78ca4 : fetch_word Asan.M.loaded_segments (0x78cf4 : word) = Some W_78ca4.
Proof. vm_refl. Qed.
Lemma D_78ca4 : decode_any W_78ca4 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ca8 : bv 32 := 0x7e113423.
Lemma F_78ca8 : fetch_word Asan.M.loaded_segments (0x78cf8 : word) = Some W_78ca8.
Proof. vm_refl. Qed.
Lemma D_78ca8 : decode_any W_78ca8 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cac : bv 32 := 0x7e813023.
Lemma F_78cac : fetch_word Asan.M.loaded_segments (0x78cfc : word) = Some W_78cac.
Proof. vm_refl. Qed.
Lemma D_78cac : decode_any W_78cac = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cb0 : bv 32 := 0x7c913c23.
Lemma F_78cb0 : fetch_word Asan.M.loaded_segments (0x78d00 : word) = Some W_78cb0.
Proof. vm_refl. Qed.
Lemma D_78cb0 : decode_any W_78cb0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cb4 : bv 32 := 0x7d213823.
Lemma F_78cb4 : fetch_word Asan.M.loaded_segments (0x78d04 : word) = Some W_78cb4.
Proof. vm_refl. Qed.
Lemma D_78cb4 : decode_any W_78cb4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cb8 : bv 32 := 0x7d313423.
Lemma F_78cb8 : fetch_word Asan.M.loaded_segments (0x78d08 : word) = Some W_78cb8.
Proof. vm_refl. Qed.
Lemma D_78cb8 : decode_any W_78cb8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cbc : bv 32 := 0x7d413023.
Lemma F_78cbc : fetch_word Asan.M.loaded_segments (0x78d0c : word) = Some W_78cbc.
Proof. vm_refl. Qed.
Lemma D_78cbc : decode_any W_78cbc = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cc0 : bv 32 := 0x7b513c23.
Lemma F_78cc0 : fetch_word Asan.M.loaded_segments (0x78d10 : word) = Some W_78cc0.
Proof. vm_refl. Qed.
Lemma D_78cc0 : decode_any W_78cc0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cc4 : bv 32 := 0x7b613823.
Lemma F_78cc4 : fetch_word Asan.M.loaded_segments (0x78d14 : word) = Some W_78cc4.
Proof. vm_refl. Qed.
Lemma D_78cc4 : decode_any W_78cc4 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cc8 : bv 32 := 0x7f010413.
Lemma F_78cc8 : fetch_word Asan.M.loaded_segments (0x78d18 : word) = Some W_78cc8.
Proof. vm_refl. Qed.
Lemma D_78cc8 : decode_any W_78cc8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ccc : bv 32 := 0xf9010113.
Lemma F_78ccc : fetch_word Asan.M.loaded_segments (0x78d1c : word) = Some W_78ccc.
Proof. vm_refl. Qed.
Lemma D_78ccc : decode_any W_78ccc = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cd0 : bv 32 := 0x000c1697.
Lemma F_78cd0 : fetch_word Asan.M.loaded_segments (0x78d20 : word) = Some W_78cd0.
Proof. vm_refl. Qed.
Lemma D_78cd0 : decode_any W_78cd0 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cd4 : bv 32 := 0x0006b683.
Lemma F_78cd4 : fetch_word Asan.M.loaded_segments (0x78d24 : word) = Some W_78cd4.
Proof. vm_refl. Qed.
Lemma D_78cd4 : decode_any W_78cd4 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cd8 : bv 32 := 0x0006c683.
Lemma F_78cd8 : fetch_word Asan.M.loaded_segments (0x78d28 : word) = Some W_78cd8.
Proof. vm_refl. Qed.
Lemma D_78cd8 : decode_any W_78cd8 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cdc : bv 32 := 0x0a068463.
Lemma F_78cdc : fetch_word Asan.M.loaded_segments (0x78d2c : word) = Some W_78cdc.
Proof. vm_refl. Qed.
Lemma D_78cdc : decode_any W_78cdc = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ce0 : bv 32 := 0xfff5c693.
Lemma F_78ce0 : fetch_word Asan.M.loaded_segments (0x78d30 : word) = Some W_78ce0.
Proof. vm_refl. Qed.
Lemma D_78ce0 : decode_any W_78ce0 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ce4 : bv 32 := 0x80040a13.
Lemma F_78ce4 : fetch_word Asan.M.loaded_segments (0x78d34 : word) = Some W_78ce4.
Proof. vm_refl. Qed.
Lemma D_78ce4 : decode_any W_78ce4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ce8 : bv 32 := 0xfa8a0a13.
Lemma F_78ce8 : fetch_word Asan.M.loaded_segments (0x78d38 : word) = Some W_78ce8.
Proof. vm_refl. Qed.
Lemma D_78ce8 : decode_any W_78ce8 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cec : bv 32 := 0x0cc6e463.
Lemma F_78cec : fetch_word Asan.M.loaded_segments (0x78d3c : word) = Some W_78cec.
Proof. vm_refl. Qed.
Lemma D_78cec : decode_any W_78cec = Some (Branch BC_LTU 13 12 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cf0 : bv 32 := 0xfbf60993.
Lemma F_78cf0 : fetch_word Asan.M.loaded_segments (0x78d40 : word) = Some W_78cf0.
Proof. vm_refl. Qed.
Lemma D_78cf0 : decode_any W_78cf0 = Some (OpImm ALU_ADD 19 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cf4 : bv 32 := 0xfbf00693.
Lemma F_78cf4 : fetch_word Asan.M.loaded_segments (0x78d44 : word) = Some W_78cf4.
Proof. vm_refl. Qed.
Lemma D_78cf4 : decode_any W_78cf4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cf8 : bv 32 := 0x1536f263.
Lemma F_78cf8 : fetch_word Asan.M.loaded_segments (0x78d48 : word) = Some W_78cf8.
Proof. vm_refl. Qed.
Lemma D_78cf8 : decode_any W_78cf8 = Some (Branch BC_GEU 13 19 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_78cfc : bv 32 := 0x000c0697.
Lemma F_78cfc : fetch_word Asan.M.loaded_segments (0x78d4c : word) = Some W_78cfc.
Proof. vm_refl. Qed.
Lemma D_78cfc : decode_any W_78cfc = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d00 : bv 32 := 0x46c6b683.
Lemma F_78d00 : fetch_word Asan.M.loaded_segments (0x78d50 : word) = Some W_78d00.
Proof. vm_refl. Qed.
Lemma D_78d00 : decode_any W_78d00 = Some (Load SZ8 true 13 13 1132, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d04 : bv 32 := 0x00c587b3.
Lemma F_78d04 : fetch_word Asan.M.loaded_segments (0x78d54 : word) = Some W_78d04.
Proof. vm_refl. Qed.
Lemma D_78d04 : decode_any W_78d04 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d08 : bv 32 := 0x0006b703.
Lemma F_78d08 : fetch_word Asan.M.loaded_segments (0x78d58 : word) = Some W_78d08.
Proof. vm_refl. Qed.
Lemma D_78d08 : decode_any W_78d08 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d0c : bv 32 := 0x0035d693.
Lemma F_78d0c : fetch_word Asan.M.loaded_segments (0x78d5c : word) = Some W_78d0c.
Proof. vm_refl. Qed.
Lemma D_78d0c : decode_any W_78d0c = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d10 : bv 32 := 0xfff78793.
Lemma F_78d10 : fetch_word Asan.M.loaded_segments (0x78d60 : word) = Some W_78d10.
Proof. vm_refl. Qed.
Lemma D_78d10 : decode_any W_78d10 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d14 : bv 32 := 0x0037d813.
Lemma F_78d14 : fetch_word Asan.M.loaded_segments (0x78d64 : word) = Some W_78d14.
Proof. vm_refl. Qed.
Lemma D_78d14 : decode_any W_78d14 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d18 : bv 32 := 0x00d706b3.
Lemma F_78d18 : fetch_word Asan.M.loaded_segments (0x78d68 : word) = Some W_78d18.
Proof. vm_refl. Qed.
Lemma D_78d18 : decode_any W_78d18 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d1c : bv 32 := 0x01070733.
Lemma F_78d1c : fetch_word Asan.M.loaded_segments (0x78d6c : word) = Some W_78d1c.
Proof. vm_refl. Qed.
Lemma D_78d1c : decode_any W_78d1c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d20 : bv 32 := 0xff86f813.
Lemma F_78d20 : fetch_word Asan.M.loaded_segments (0x78d70 : word) = Some W_78d20.
Proof. vm_refl. Qed.
Lemma D_78d20 : decode_any W_78d20 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d24 : bv 32 := 0xff877893.
Lemma F_78d24 : fetch_word Asan.M.loaded_segments (0x78d74 : word) = Some W_78d24.
Proof. vm_refl. Qed.
Lemma D_78d24 : decode_any W_78d24 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d28 : bv 32 := 0x00083803.
Lemma F_78d28 : fetch_word Asan.M.loaded_segments (0x78d78 : word) = Some W_78d28.
Proof. vm_refl. Qed.
Lemma D_78d28 : decode_any W_78d28 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d2c : bv 32 := 0x0008b883.
Lemma F_78d2c : fetch_word Asan.M.loaded_segments (0x78d7c : word) = Some W_78d2c.
Proof. vm_refl. Qed.
Lemma D_78d2c : decode_any W_78d2c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d30 : bv 32 := 0x0108e833.
Lemma F_78d30 : fetch_word Asan.M.loaded_segments (0x78d80 : word) = Some W_78d30.
Proof. vm_refl. Qed.
Lemma D_78d30 : decode_any W_78d30 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d34 : bv 32 := 0x18081e63.
Lemma F_78d34 : fetch_word Asan.M.loaded_segments (0x78d84 : word) = Some W_78d34.
Proof. vm_refl. Qed.
Lemma D_78d34 : decode_any W_78d34 = Some (Branch BC_NE 16 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d38 : bv 32 := 0xfff54693.
Lemma F_78d38 : fetch_word Asan.M.loaded_segments (0x78d88 : word) = Some W_78d38.
Proof. vm_refl. Qed.
Lemma D_78d38 : decode_any W_78d38 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d3c : bv 32 := 0x10c6e463.
Lemma F_78d3c : fetch_word Asan.M.loaded_segments (0x78d8c : word) = Some W_78d3c.
Proof. vm_refl. Qed.
Lemma D_78d3c : decode_any W_78d3c = Some (Branch BC_LTU 13 12 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d40 : bv 32 := 0xfbf00693.
Lemma F_78d40 : fetch_word Asan.M.loaded_segments (0x78d90 : word) = Some W_78d40.
Proof. vm_refl. Qed.
Lemma D_78d40 : decode_any W_78d40 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d44 : bv 32 := 0x1936f263.
Lemma F_78d44 : fetch_word Asan.M.loaded_segments (0x78d94 : word) = Some W_78d44.
Proof. vm_refl. Qed.
Lemma D_78d44 : decode_any W_78d44 = Some (Branch BC_GEU 13 19 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d48 : bv 32 := 0x000c0697.
Lemma F_78d48 : fetch_word Asan.M.loaded_segments (0x78d98 : word) = Some W_78d48.
Proof. vm_refl. Qed.
Lemma D_78d48 : decode_any W_78d48 = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d4c : bv 32 := 0x4206b683.
Lemma F_78d4c : fetch_word Asan.M.loaded_segments (0x78d9c : word) = Some W_78d4c.
Proof. vm_refl. Qed.
Lemma D_78d4c : decode_any W_78d4c = Some (Load SZ8 true 13 13 1056, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d50 : bv 32 := 0x00c507b3.
Lemma F_78d50 : fetch_word Asan.M.loaded_segments (0x78da0 : word) = Some W_78d50.
Proof. vm_refl. Qed.
Lemma D_78d50 : decode_any W_78d50 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d54 : bv 32 := 0x0006b703.
Lemma F_78d54 : fetch_word Asan.M.loaded_segments (0x78da4 : word) = Some W_78d54.
Proof. vm_refl. Qed.
Lemma D_78d54 : decode_any W_78d54 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d58 : bv 32 := 0x00355693.
Lemma F_78d58 : fetch_word Asan.M.loaded_segments (0x78da8 : word) = Some W_78d58.
Proof. vm_refl. Qed.
Lemma D_78d58 : decode_any W_78d58 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d5c : bv 32 := 0xfff78793.
Lemma F_78d5c : fetch_word Asan.M.loaded_segments (0x78dac : word) = Some W_78d5c.
Proof. vm_refl. Qed.
Lemma D_78d5c : decode_any W_78d5c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d60 : bv 32 := 0x0037d813.
Lemma F_78d60 : fetch_word Asan.M.loaded_segments (0x78db0 : word) = Some W_78d60.
Proof. vm_refl. Qed.
Lemma D_78d60 : decode_any W_78d60 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d64 : bv 32 := 0x00d706b3.
Lemma F_78d64 : fetch_word Asan.M.loaded_segments (0x78db4 : word) = Some W_78d64.
Proof. vm_refl. Qed.
Lemma D_78d64 : decode_any W_78d64 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d68 : bv 32 := 0x01070733.
Lemma F_78d68 : fetch_word Asan.M.loaded_segments (0x78db8 : word) = Some W_78d68.
Proof. vm_refl. Qed.
Lemma D_78d68 : decode_any W_78d68 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d6c : bv 32 := 0xff86f813.
Lemma F_78d6c : fetch_word Asan.M.loaded_segments (0x78dbc : word) = Some W_78d6c.
Proof. vm_refl. Qed.
Lemma D_78d6c : decode_any W_78d6c = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d70 : bv 32 := 0xff877893.
Lemma F_78d70 : fetch_word Asan.M.loaded_segments (0x78dc0 : word) = Some W_78d70.
Proof. vm_refl. Qed.
Lemma D_78d70 : decode_any W_78d70 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d74 : bv 32 := 0x00083803.
Lemma F_78d74 : fetch_word Asan.M.loaded_segments (0x78dc4 : word) = Some W_78d74.
Proof. vm_refl. Qed.
Lemma D_78d74 : decode_any W_78d74 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d78 : bv 32 := 0x0008b883.
Lemma F_78d78 : fetch_word Asan.M.loaded_segments (0x78dc8 : word) = Some W_78d78.
Proof. vm_refl. Qed.
Lemma D_78d78 : decode_any W_78d78 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d7c : bv 32 := 0x0108e833.
Lemma F_78d7c : fetch_word Asan.M.loaded_segments (0x78dcc : word) = Some W_78d7c.
Proof. vm_refl. Qed.
Lemma D_78d7c : decode_any W_78d7c = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d80 : bv 32 := 0x1e081a63.
Lemma F_78d80 : fetch_word Asan.M.loaded_segments (0x78dd0 : word) = Some W_78d80.
Proof. vm_refl. Qed.
Lemma D_78d80 : decode_any W_78d80 = Some (Branch BC_NE 16 0 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d84 : bv 32 := 0x7b9120ef.
Lemma F_78d84 : fetch_word Asan.M.loaded_segments (0x78dd4 : word) = Some W_78d84.
Proof. vm_refl. Qed.
Lemma D_78d84 : decode_any W_78d84 = Some (Jal 1 77752, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d88 : bv 32 := 0x07010113.
Lemma F_78d88 : fetch_word Asan.M.loaded_segments (0x78dd8 : word) = Some W_78d88.
Proof. vm_refl. Qed.
Lemma D_78d88 : decode_any W_78d88 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d8c : bv 32 := 0x7e813083.
Lemma F_78d8c : fetch_word Asan.M.loaded_segments (0x78ddc : word) = Some W_78d8c.
Proof. vm_refl. Qed.
Lemma D_78d8c : decode_any W_78d8c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d90 : bv 32 := 0x7e013403.
Lemma F_78d90 : fetch_word Asan.M.loaded_segments (0x78de0 : word) = Some W_78d90.
Proof. vm_refl. Qed.
Lemma D_78d90 : decode_any W_78d90 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d94 : bv 32 := 0x7d813483.
Lemma F_78d94 : fetch_word Asan.M.loaded_segments (0x78de4 : word) = Some W_78d94.
Proof. vm_refl. Qed.
Lemma D_78d94 : decode_any W_78d94 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d98 : bv 32 := 0x7d013903.
Lemma F_78d98 : fetch_word Asan.M.loaded_segments (0x78de8 : word) = Some W_78d98.
Proof. vm_refl. Qed.
Lemma D_78d98 : decode_any W_78d98 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_78d9c : bv 32 := 0x7c813983.
Lemma F_78d9c : fetch_word Asan.M.loaded_segments (0x78dec : word) = Some W_78d9c.
Proof. vm_refl. Qed.
Lemma D_78d9c : decode_any W_78d9c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_78da0 : bv 32 := 0x7c013a03.
Lemma F_78da0 : fetch_word Asan.M.loaded_segments (0x78df0 : word) = Some W_78da0.
Proof. vm_refl. Qed.
Lemma D_78da0 : decode_any W_78da0 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_78da4 : bv 32 := 0x7b813a83.
Lemma F_78da4 : fetch_word Asan.M.loaded_segments (0x78df4 : word) = Some W_78da4.
Proof. vm_refl. Qed.
Lemma D_78da4 : decode_any W_78da4 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_78da8 : bv 32 := 0x7b013b03.
Lemma F_78da8 : fetch_word Asan.M.loaded_segments (0x78df8 : word) = Some W_78da8.
Proof. vm_refl. Qed.
Lemma D_78da8 : decode_any W_78da8 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_78dac : bv 32 := 0x7f010113.
Lemma F_78dac : fetch_word Asan.M.loaded_segments (0x78dfc : word) = Some W_78dac.
Proof. vm_refl. Qed.
Lemma D_78dac : decode_any W_78dac = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_78db0 : bv 32 := 0x00008067.
Lemma F_78db0 : fetch_word Asan.M.loaded_segments (0x78e00 : word) = Some W_78db0.
Proof. vm_refl. Qed.
Lemma D_78db0 : decode_any W_78db0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e3c : bv 32 := 0x0c061463.
Lemma F_78e3c : fetch_word Asan.M.loaded_segments (0x78e8c : word) = Some W_78e3c.
Proof. vm_refl. Qed.
Lemma D_78e3c : decode_any W_78e3c = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e40 : bv 32 := 0xef9ff06f.
Lemma F_78e40 : fetch_word Asan.M.loaded_segments (0x78e90 : word) = Some W_78e40.
Proof. vm_refl. Qed.
Lemma D_78e40 : decode_any W_78e40 = Some (Jal 0 2096888, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ec8 : bv 32 := 0x0e061063.
Lemma F_78ec8 : fetch_word Asan.M.loaded_segments (0x78f18 : word) = Some W_78ec8.
Proof. vm_refl. Qed.
Lemma D_78ec8 : decode_any W_78ec8 = Some (Branch BC_NE 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ecc : bv 32 := 0xeb9ff06f.
Lemma F_78ecc : fetch_word Asan.M.loaded_segments (0x78f1c : word) = Some W_78ecc.
Proof. vm_refl. Qed.
Lemma D_78ecc : decode_any W_78ecc = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ed0 : bv 32 := 0x00070803.
Lemma F_78ed0 : fetch_word Asan.M.loaded_segments (0x78f20 : word) = Some W_78ed0.
Proof. vm_refl. Qed.
Lemma D_78ed0 : decode_any W_78ed0 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ed4 : bv 32 := 0x0077f793.
Lemma F_78ed4 : fetch_word Asan.M.loaded_segments (0x78f24 : word) = Some W_78ed4.
Proof. vm_refl. Qed.
Lemma D_78ed4 : decode_any W_78ed4 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ed8 : bv 32 := 0x010038b3.
Lemma F_78ed8 : fetch_word Asan.M.loaded_segments (0x78f28 : word) = Some W_78ed8.
Proof. vm_refl. Qed.
Lemma D_78ed8 : decode_any W_78ed8 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78edc : bv 32 := 0x0107a7b3.
Lemma F_78edc : fetch_word Asan.M.loaded_segments (0x78f2c : word) = Some W_78edc.
Proof. vm_refl. Qed.
Lemma D_78edc : decode_any W_78edc = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ee0 : bv 32 := 0x0017c793.
Lemma F_78ee0 : fetch_word Asan.M.loaded_segments (0x78f30 : word) = Some W_78ee0.
Proof. vm_refl. Qed.
Lemma D_78ee0 : decode_any W_78ee0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ee4 : bv 32 := 0x00f8f7b3.
Lemma F_78ee4 : fetch_word Asan.M.loaded_segments (0x78f34 : word) = Some W_78ee4.
Proof. vm_refl. Qed.
Lemma D_78ee4 : decode_any W_78ee4 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ee8 : bv 32 := 0x00e6fa63.
Lemma F_78ee8 : fetch_word Asan.M.loaded_segments (0x78f38 : word) = Some W_78ee8.
Proof. vm_refl. Qed.
Lemma D_78ee8 : decode_any W_78ee8 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_78eec : bv 32 := 0x0006c803.
Lemma F_78eec : fetch_word Asan.M.loaded_segments (0x78f3c : word) = Some W_78eec.
Proof. vm_refl. Qed.
Lemma D_78eec : decode_any W_78eec = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ef0 : bv 32 := 0x00168693.
Lemma F_78ef0 : fetch_word Asan.M.loaded_segments (0x78f40 : word) = Some W_78ef0.
Proof. vm_refl. Qed.
Lemma D_78ef0 : decode_any W_78ef0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ef4 : bv 32 := 0x00f867b3.
Lemma F_78ef4 : fetch_word Asan.M.loaded_segments (0x78f44 : word) = Some W_78ef4.
Proof. vm_refl. Qed.
Lemma D_78ef4 : decode_any W_78ef4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ef8 : bv 32 := 0xfee69ae3.
Lemma F_78ef8 : fetch_word Asan.M.loaded_segments (0x78f48 : word) = Some W_78ef8.
Proof. vm_refl. Qed.
Lemma D_78ef8 : decode_any W_78ef8 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_78efc : bv 32 := 0x0ff7f693.
Lemma F_78efc : fetch_word Asan.M.loaded_segments (0x78f4c : word) = Some W_78efc.
Proof. vm_refl. Qed.
Lemma D_78efc : decode_any W_78efc = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f00 : bv 32 := 0xe2068ce3.
Lemma F_78f00 : fetch_word Asan.M.loaded_segments (0x78f50 : word) = Some W_78f00.
Proof. vm_refl. Qed.
Lemma D_78f00 : decode_any W_78f00 = Some (Branch BC_EQ 13 0 7736, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f04 : bv 32 := 0x00050a93.
Lemma F_78f04 : fetch_word Asan.M.loaded_segments (0x78f54 : word) = Some W_78f04.
Proof. vm_refl. Qed.
Lemma D_78f04 : decode_any W_78f04 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f08 : bv 32 := 0x00058513.
Lemma F_78f08 : fetch_word Asan.M.loaded_segments (0x78f58 : word) = Some W_78f08.
Proof. vm_refl. Qed.
Lemma D_78f08 : decode_any W_78f08 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f0c : bv 32 := 0x00058b13.
Lemma F_78f0c : fetch_word Asan.M.loaded_segments (0x78f5c : word) = Some W_78f0c.
Proof. vm_refl. Qed.
Lemma D_78f0c : decode_any W_78f0c = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f10 : bv 32 := 0x00060593.
Lemma F_78f10 : fetch_word Asan.M.loaded_segments (0x78f60 : word) = Some W_78f10.
Proof. vm_refl. Qed.
Lemma D_78f10 : decode_any W_78f10 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f14 : bv 32 := 0x00060493.
Lemma F_78f14 : fetch_word Asan.M.loaded_segments (0x78f64 : word) = Some W_78f14.
Proof. vm_refl. Qed.
Lemma D_78f14 : decode_any W_78f14 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f18 : bv 32 := 0x6dd020ef.
Lemma F_78f18 : fetch_word Asan.M.loaded_segments (0x78f68 : word) = Some W_78f18.
Proof. vm_refl. Qed.
Lemma D_78f18 : decode_any W_78f18 = Some (Jal 1 11996, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f1c : bv 32 := 0x000b0593.
Lemma F_78f1c : fetch_word Asan.M.loaded_segments (0x78f6c : word) = Some W_78f1c.
Proof. vm_refl. Qed.
Lemma D_78f1c : decode_any W_78f1c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f20 : bv 32 := 0x00048613.
Lemma F_78f20 : fetch_word Asan.M.loaded_segments (0x78f70 : word) = Some W_78f20.
Proof. vm_refl. Qed.
Lemma D_78f20 : decode_any W_78f20 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f24 : bv 32 := 0x00050913.
Lemma F_78f24 : fetch_word Asan.M.loaded_segments (0x78f74 : word) = Some W_78f24.
Proof. vm_refl. Qed.
Lemma D_78f24 : decode_any W_78f24 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f28 : bv 32 := 0x000a8513.
Lemma F_78f28 : fetch_word Asan.M.loaded_segments (0x78f78 : word) = Some W_78f28.
Proof. vm_refl. Qed.
Lemma D_78f28 : decode_any W_78f28 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f2c : bv 32 := 0xe00906e3.
Lemma F_78f2c : fetch_word Asan.M.loaded_segments (0x78f7c : word) = Some W_78f2c.
Proof. vm_refl. Qed.
Lemma D_78f2c : decode_any W_78f2c = Some (Branch BC_EQ 18 0 7692, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f74 : bv 32 := 0x00070803.
Lemma F_78f74 : fetch_word Asan.M.loaded_segments (0x78fc4 : word) = Some W_78f74.
Proof. vm_refl. Qed.
Lemma D_78f74 : decode_any W_78f74 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f78 : bv 32 := 0x0077f793.
Lemma F_78f78 : fetch_word Asan.M.loaded_segments (0x78fc8 : word) = Some W_78f78.
Proof. vm_refl. Qed.
Lemma D_78f78 : decode_any W_78f78 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f7c : bv 32 := 0x010038b3.
Lemma F_78f7c : fetch_word Asan.M.loaded_segments (0x78fcc : word) = Some W_78f7c.
Proof. vm_refl. Qed.
Lemma D_78f7c : decode_any W_78f7c = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f80 : bv 32 := 0x0107a7b3.
Lemma F_78f80 : fetch_word Asan.M.loaded_segments (0x78fd0 : word) = Some W_78f80.
Proof. vm_refl. Qed.
Lemma D_78f80 : decode_any W_78f80 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f84 : bv 32 := 0x0017c793.
Lemma F_78f84 : fetch_word Asan.M.loaded_segments (0x78fd4 : word) = Some W_78f84.
Proof. vm_refl. Qed.
Lemma D_78f84 : decode_any W_78f84 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f88 : bv 32 := 0x00f8f7b3.
Lemma F_78f88 : fetch_word Asan.M.loaded_segments (0x78fd8 : word) = Some W_78f88.
Proof. vm_refl. Qed.
Lemma D_78f88 : decode_any W_78f88 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f8c : bv 32 := 0x00e6fa63.
Lemma F_78f8c : fetch_word Asan.M.loaded_segments (0x78fdc : word) = Some W_78f8c.
Proof. vm_refl. Qed.
Lemma D_78f8c : decode_any W_78f8c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f90 : bv 32 := 0x0006c803.
Lemma F_78f90 : fetch_word Asan.M.loaded_segments (0x78fe0 : word) = Some W_78f90.
Proof. vm_refl. Qed.
Lemma D_78f90 : decode_any W_78f90 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f94 : bv 32 := 0x00168693.
Lemma F_78f94 : fetch_word Asan.M.loaded_segments (0x78fe4 : word) = Some W_78f94.
Proof. vm_refl. Qed.
Lemma D_78f94 : decode_any W_78f94 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f98 : bv 32 := 0x00f867b3.
Lemma F_78f98 : fetch_word Asan.M.loaded_segments (0x78fe8 : word) = Some W_78f98.
Proof. vm_refl. Qed.
Lemma D_78f98 : decode_any W_78f98 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f9c : bv 32 := 0xfee69ae3.
Lemma F_78f9c : fetch_word Asan.M.loaded_segments (0x78fec : word) = Some W_78f9c.
Proof. vm_refl. Qed.
Lemma D_78f9c : decode_any W_78f9c = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fa0 : bv 32 := 0x0ff7f693.
Lemma F_78fa0 : fetch_word Asan.M.loaded_segments (0x78ff0 : word) = Some W_78fa0.
Proof. vm_refl. Qed.
Lemma D_78fa0 : decode_any W_78fa0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fa4 : bv 32 := 0xde0680e3.
Lemma F_78fa4 : fetch_word Asan.M.loaded_segments (0x78ff4 : word) = Some W_78fa4.
Proof. vm_refl. Qed.
Lemma D_78fa4 : decode_any W_78fa4 = Some (Branch BC_EQ 13 0 7648, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fa8 : bv 32 := 0x00050493.
Lemma F_78fa8 : fetch_word Asan.M.loaded_segments (0x78ff8 : word) = Some W_78fa8.
Proof. vm_refl. Qed.
Lemma D_78fa8 : decode_any W_78fa8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fac : bv 32 := 0x00058a93.
Lemma F_78fac : fetch_word Asan.M.loaded_segments (0x78ffc : word) = Some W_78fac.
Proof. vm_refl. Qed.
Lemma D_78fac : decode_any W_78fac = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fb0 : bv 32 := 0x00060593.
Lemma F_78fb0 : fetch_word Asan.M.loaded_segments (0x79000 : word) = Some W_78fb0.
Proof. vm_refl. Qed.
Lemma D_78fb0 : decode_any W_78fb0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fb4 : bv 32 := 0x00060913.
Lemma F_78fb4 : fetch_word Asan.M.loaded_segments (0x79004 : word) = Some W_78fb4.
Proof. vm_refl. Qed.
Lemma D_78fb4 : decode_any W_78fb4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fb8 : bv 32 := 0x63d020ef.
Lemma F_78fb8 : fetch_word Asan.M.loaded_segments (0x79008 : word) = Some W_78fb8.
Proof. vm_refl. Qed.
Lemma D_78fb8 : decode_any W_78fb8 = Some (Jal 1 11836, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fbc : bv 32 := 0x000a8593.
Lemma F_78fbc : fetch_word Asan.M.loaded_segments (0x7900c : word) = Some W_78fbc.
Proof. vm_refl. Qed.
Lemma D_78fbc : decode_any W_78fbc = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fc0 : bv 32 := 0x00090613.
Lemma F_78fc0 : fetch_word Asan.M.loaded_segments (0x79010 : word) = Some W_78fc0.
Proof. vm_refl. Qed.
Lemma D_78fc0 : decode_any W_78fc0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fc4 : bv 32 := 0x00050993.
Lemma F_78fc4 : fetch_word Asan.M.loaded_segments (0x79014 : word) = Some W_78fc4.
Proof. vm_refl. Qed.
Lemma D_78fc4 : decode_any W_78fc4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fc8 : bv 32 := 0x00048513.
Lemma F_78fc8 : fetch_word Asan.M.loaded_segments (0x79018 : word) = Some W_78fc8.
Proof. vm_refl. Qed.
Lemma D_78fc8 : decode_any W_78fc8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78fcc : bv 32 := 0xda098ce3.
Lemma F_78fcc : fetch_word Asan.M.loaded_segments (0x7901c : word) = Some W_78fcc.
Proof. vm_refl. Qed.
Lemma D_78fcc : decode_any W_78fcc = Some (Branch BC_EQ 19 0 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_79014 : bv 32 := 0x81010113.
Lemma F_79014 : fetch_word Asan.M.loaded_segments (0x79064 : word) = Some W_79014.
Proof. vm_refl. Qed.
Lemma D_79014 : decode_any W_79014 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_79018 : bv 32 := 0x7e113423.
Lemma F_79018 : fetch_word Asan.M.loaded_segments (0x79068 : word) = Some W_79018.
Proof. vm_refl. Qed.
Lemma D_79018 : decode_any W_79018 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7901c : bv 32 := 0x7e813023.
Lemma F_7901c : fetch_word Asan.M.loaded_segments (0x7906c : word) = Some W_7901c.
Proof. vm_refl. Qed.
Lemma D_7901c : decode_any W_7901c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_79020 : bv 32 := 0x7c913c23.
Lemma F_79020 : fetch_word Asan.M.loaded_segments (0x79070 : word) = Some W_79020.
Proof. vm_refl. Qed.
Lemma D_79020 : decode_any W_79020 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_79024 : bv 32 := 0x7d213823.
Lemma F_79024 : fetch_word Asan.M.loaded_segments (0x79074 : word) = Some W_79024.
Proof. vm_refl. Qed.
Lemma D_79024 : decode_any W_79024 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_79028 : bv 32 := 0x7d313423.
Lemma F_79028 : fetch_word Asan.M.loaded_segments (0x79078 : word) = Some W_79028.
Proof. vm_refl. Qed.
Lemma D_79028 : decode_any W_79028 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7902c : bv 32 := 0x7d413023.
Lemma F_7902c : fetch_word Asan.M.loaded_segments (0x7907c : word) = Some W_7902c.
Proof. vm_refl. Qed.
Lemma D_7902c : decode_any W_7902c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79030 : bv 32 := 0x7b513c23.
Lemma F_79030 : fetch_word Asan.M.loaded_segments (0x79080 : word) = Some W_79030.
Proof. vm_refl. Qed.
Lemma D_79030 : decode_any W_79030 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_79034 : bv 32 := 0x7b613823.
Lemma F_79034 : fetch_word Asan.M.loaded_segments (0x79084 : word) = Some W_79034.
Proof. vm_refl. Qed.
Lemma D_79034 : decode_any W_79034 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_79038 : bv 32 := 0x7f010413.
Lemma F_79038 : fetch_word Asan.M.loaded_segments (0x79088 : word) = Some W_79038.
Proof. vm_refl. Qed.
Lemma D_79038 : decode_any W_79038 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7903c : bv 32 := 0xf9010113.
Lemma F_7903c : fetch_word Asan.M.loaded_segments (0x7908c : word) = Some W_7903c.
Proof. vm_refl. Qed.
Lemma D_7903c : decode_any W_7903c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79040 : bv 32 := 0x000c1697.
Lemma F_79040 : fetch_word Asan.M.loaded_segments (0x79090 : word) = Some W_79040.
Proof. vm_refl. Qed.
Lemma D_79040 : decode_any W_79040 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_79044 : bv 32 := 0xc906b683.
Lemma F_79044 : fetch_word Asan.M.loaded_segments (0x79094 : word) = Some W_79044.
Proof. vm_refl. Qed.
Lemma D_79044 : decode_any W_79044 = Some (Load SZ8 true 13 13 3216, 4%Z).
Proof. vm_refl. Qed.

Definition W_79048 : bv 32 := 0x0006c683.
Lemma F_79048 : fetch_word Asan.M.loaded_segments (0x79098 : word) = Some W_79048.
Proof. vm_refl. Qed.
Lemma D_79048 : decode_any W_79048 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7904c : bv 32 := 0x08068a63.
Lemma F_7904c : fetch_word Asan.M.loaded_segments (0x7909c : word) = Some W_7904c.
Proof. vm_refl. Qed.
Lemma D_7904c : decode_any W_7904c = Some (Branch BC_EQ 13 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_79050 : bv 32 := 0xfff54693.
Lemma F_79050 : fetch_word Asan.M.loaded_segments (0x790a0 : word) = Some W_79050.
Proof. vm_refl. Qed.
Lemma D_79050 : decode_any W_79050 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79054 : bv 32 := 0x80040a93.
Lemma F_79054 : fetch_word Asan.M.loaded_segments (0x790a4 : word) = Some W_79054.
Proof. vm_refl. Qed.
Lemma D_79054 : decode_any W_79054 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_79058 : bv 32 := 0xfa8a8a93.
Lemma F_79058 : fetch_word Asan.M.loaded_segments (0x790a8 : word) = Some W_79058.
Proof. vm_refl. Qed.
Lemma D_79058 : decode_any W_79058 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7905c : bv 32 := 0x0cc6ea63.
Lemma F_7905c : fetch_word Asan.M.loaded_segments (0x790ac : word) = Some W_7905c.
Proof. vm_refl. Qed.
Lemma D_7905c : decode_any W_7905c = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_79060 : bv 32 := 0xfbf60693.
Lemma F_79060 : fetch_word Asan.M.loaded_segments (0x790b0 : word) = Some W_79060.
Proof. vm_refl. Qed.
Lemma D_79060 : decode_any W_79060 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_79064 : bv 32 := 0xfbf00713.
Lemma F_79064 : fetch_word Asan.M.loaded_segments (0x790b4 : word) = Some W_79064.
Proof. vm_refl. Qed.
Lemma D_79064 : decode_any W_79064 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_79068 : bv 32 := 0x14d77863.
Lemma F_79068 : fetch_word Asan.M.loaded_segments (0x790b8 : word) = Some W_79068.
Proof. vm_refl. Qed.
Lemma D_79068 : decode_any W_79068 = Some (Branch BC_GEU 14 13 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_7906c : bv 32 := 0x000c0697.
Lemma F_7906c : fetch_word Asan.M.loaded_segments (0x790bc : word) = Some W_7906c.
Proof. vm_refl. Qed.
Lemma D_7906c : decode_any W_7906c = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_79070 : bv 32 := 0x0fc6b683.
Lemma F_79070 : fetch_word Asan.M.loaded_segments (0x790c0 : word) = Some W_79070.
Proof. vm_refl. Qed.
Lemma D_79070 : decode_any W_79070 = Some (Load SZ8 true 13 13 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_79074 : bv 32 := 0x00c507b3.
Lemma F_79074 : fetch_word Asan.M.loaded_segments (0x790c4 : word) = Some W_79074.
Proof. vm_refl. Qed.
Lemma D_79074 : decode_any W_79074 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_79078 : bv 32 := 0x0006b703.
Lemma F_79078 : fetch_word Asan.M.loaded_segments (0x790c8 : word) = Some W_79078.
Proof. vm_refl. Qed.
Lemma D_79078 : decode_any W_79078 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7907c : bv 32 := 0x00355693.
Lemma F_7907c : fetch_word Asan.M.loaded_segments (0x790cc : word) = Some W_7907c.
Proof. vm_refl. Qed.
Lemma D_7907c : decode_any W_7907c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79080 : bv 32 := 0xfff78793.
Lemma F_79080 : fetch_word Asan.M.loaded_segments (0x790d0 : word) = Some W_79080.
Proof. vm_refl. Qed.
Lemma D_79080 : decode_any W_79080 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79084 : bv 32 := 0x0037d813.
Lemma F_79084 : fetch_word Asan.M.loaded_segments (0x790d4 : word) = Some W_79084.
Proof. vm_refl. Qed.
Lemma D_79084 : decode_any W_79084 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79088 : bv 32 := 0x00d706b3.
Lemma F_79088 : fetch_word Asan.M.loaded_segments (0x790d8 : word) = Some W_79088.
Proof. vm_refl. Qed.
Lemma D_79088 : decode_any W_79088 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7908c : bv 32 := 0x01070733.
Lemma F_7908c : fetch_word Asan.M.loaded_segments (0x790dc : word) = Some W_7908c.
Proof. vm_refl. Qed.
Lemma D_7908c : decode_any W_7908c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79090 : bv 32 := 0xff86f813.
Lemma F_79090 : fetch_word Asan.M.loaded_segments (0x790e0 : word) = Some W_79090.
Proof. vm_refl. Qed.
Lemma D_79090 : decode_any W_79090 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79094 : bv 32 := 0xff877893.
Lemma F_79094 : fetch_word Asan.M.loaded_segments (0x790e4 : word) = Some W_79094.
Proof. vm_refl. Qed.
Lemma D_79094 : decode_any W_79094 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79098 : bv 32 := 0x00083803.
Lemma F_79098 : fetch_word Asan.M.loaded_segments (0x790e8 : word) = Some W_79098.
Proof. vm_refl. Qed.
Lemma D_79098 : decode_any W_79098 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7909c : bv 32 := 0x0008b883.
Lemma F_7909c : fetch_word Asan.M.loaded_segments (0x790ec : word) = Some W_7909c.
Proof. vm_refl. Qed.
Lemma D_7909c : decode_any W_7909c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_790a0 : bv 32 := 0x0108e833.
Lemma F_790a0 : fetch_word Asan.M.loaded_segments (0x790f0 : word) = Some W_790a0.
Proof. vm_refl. Qed.
Lemma D_790a0 : decode_any W_790a0 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_790a4 : bv 32 := 0x10081e63.
Lemma F_790a4 : fetch_word Asan.M.loaded_segments (0x790f4 : word) = Some W_790a4.
Proof. vm_refl. Qed.
Lemma D_790a4 : decode_any W_790a4 = Some (Branch BC_NE 16 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_790a8 : bv 32 := 0x000c2697.
Lemma F_790a8 : fetch_word Asan.M.loaded_segments (0x790f8 : word) = Some W_790a8.
Proof. vm_refl. Qed.
Lemma D_790a8 : decode_any W_790a8 = Some (Auipc 13 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_790ac : bv 32 := 0x0d06b683.
Lemma F_790ac : fetch_word Asan.M.loaded_segments (0x790fc : word) = Some W_790ac.
Proof. vm_refl. Qed.
Lemma D_790ac : decode_any W_790ac = Some (Load SZ8 true 13 13 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_790b0 : bv 32 := 0x000680e7.
Lemma F_790b0 : fetch_word Asan.M.loaded_segments (0x79100 : word) = Some W_790b0.
Proof. vm_refl. Qed.
Lemma D_790b0 : decode_any W_790b0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_790b4 : bv 32 := 0x07010113.
Lemma F_790b4 : fetch_word Asan.M.loaded_segments (0x79104 : word) = Some W_790b4.
Proof. vm_refl. Qed.
Lemma D_790b4 : decode_any W_790b4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_790b8 : bv 32 := 0x7e813083.
Lemma F_790b8 : fetch_word Asan.M.loaded_segments (0x79108 : word) = Some W_790b8.
Proof. vm_refl. Qed.
Lemma D_790b8 : decode_any W_790b8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_790bc : bv 32 := 0x7e013403.
Lemma F_790bc : fetch_word Asan.M.loaded_segments (0x7910c : word) = Some W_790bc.
Proof. vm_refl. Qed.
Lemma D_790bc : decode_any W_790bc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_790c0 : bv 32 := 0x7d813483.
Lemma F_790c0 : fetch_word Asan.M.loaded_segments (0x79110 : word) = Some W_790c0.
Proof. vm_refl. Qed.
Lemma D_790c0 : decode_any W_790c0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_790c4 : bv 32 := 0x7d013903.
Lemma F_790c4 : fetch_word Asan.M.loaded_segments (0x79114 : word) = Some W_790c4.
Proof. vm_refl. Qed.
Lemma D_790c4 : decode_any W_790c4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_790c8 : bv 32 := 0x7c813983.
Lemma F_790c8 : fetch_word Asan.M.loaded_segments (0x79118 : word) = Some W_790c8.
Proof. vm_refl. Qed.
Lemma D_790c8 : decode_any W_790c8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_790cc : bv 32 := 0x7c013a03.
Lemma F_790cc : fetch_word Asan.M.loaded_segments (0x7911c : word) = Some W_790cc.
Proof. vm_refl. Qed.
Lemma D_790cc : decode_any W_790cc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_790d0 : bv 32 := 0x7b813a83.
Lemma F_790d0 : fetch_word Asan.M.loaded_segments (0x79120 : word) = Some W_790d0.
Proof. vm_refl. Qed.
Lemma D_790d0 : decode_any W_790d0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_790d4 : bv 32 := 0x7b013b03.
Lemma F_790d4 : fetch_word Asan.M.loaded_segments (0x79124 : word) = Some W_790d4.
Proof. vm_refl. Qed.
Lemma D_790d4 : decode_any W_790d4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_790d8 : bv 32 := 0x7f010113.
Lemma F_790d8 : fetch_word Asan.M.loaded_segments (0x79128 : word) = Some W_790d8.
Proof. vm_refl. Qed.
Lemma D_790d8 : decode_any W_790d8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_790dc : bv 32 := 0x00008067.
Lemma F_790dc : fetch_word Asan.M.loaded_segments (0x7912c : word) = Some W_790dc.
Proof. vm_refl. Qed.
Lemma D_790dc : decode_any W_790dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_791b8 : bv 32 := 0x02061e63.
Lemma F_791b8 : fetch_word Asan.M.loaded_segments (0x79208 : word) = Some W_791b8.
Proof. vm_refl. Qed.
Lemma D_791b8 : decode_any W_791b8 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_791bc : bv 32 := 0xeedff06f.
Lemma F_791bc : fetch_word Asan.M.loaded_segments (0x7920c : word) = Some W_791bc.
Proof. vm_refl. Qed.
Lemma D_791bc : decode_any W_791bc = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

Definition W_791c0 : bv 32 := 0x00070803.
Lemma F_791c0 : fetch_word Asan.M.loaded_segments (0x79210 : word) = Some W_791c0.
Proof. vm_refl. Qed.
Lemma D_791c0 : decode_any W_791c0 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_791c4 : bv 32 := 0x0077f793.
Lemma F_791c4 : fetch_word Asan.M.loaded_segments (0x79214 : word) = Some W_791c4.
Proof. vm_refl. Qed.
Lemma D_791c4 : decode_any W_791c4 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_791c8 : bv 32 := 0x010038b3.
Lemma F_791c8 : fetch_word Asan.M.loaded_segments (0x79218 : word) = Some W_791c8.
Proof. vm_refl. Qed.
Lemma D_791c8 : decode_any W_791c8 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_791cc : bv 32 := 0x0107a7b3.
Lemma F_791cc : fetch_word Asan.M.loaded_segments (0x7921c : word) = Some W_791cc.
Proof. vm_refl. Qed.
Lemma D_791cc : decode_any W_791cc = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_791d0 : bv 32 := 0x0017c793.
Lemma F_791d0 : fetch_word Asan.M.loaded_segments (0x79220 : word) = Some W_791d0.
Proof. vm_refl. Qed.
Lemma D_791d0 : decode_any W_791d0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_791d4 : bv 32 := 0x00f8f7b3.
Lemma F_791d4 : fetch_word Asan.M.loaded_segments (0x79224 : word) = Some W_791d4.
Proof. vm_refl. Qed.
Lemma D_791d4 : decode_any W_791d4 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_791d8 : bv 32 := 0x00e6fa63.
Lemma F_791d8 : fetch_word Asan.M.loaded_segments (0x79228 : word) = Some W_791d8.
Proof. vm_refl. Qed.
Lemma D_791d8 : decode_any W_791d8 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_791dc : bv 32 := 0x0006c803.
Lemma F_791dc : fetch_word Asan.M.loaded_segments (0x7922c : word) = Some W_791dc.
Proof. vm_refl. Qed.
Lemma D_791dc : decode_any W_791dc = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_791e0 : bv 32 := 0x00168693.
Lemma F_791e0 : fetch_word Asan.M.loaded_segments (0x79230 : word) = Some W_791e0.
Proof. vm_refl. Qed.
Lemma D_791e0 : decode_any W_791e0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_791e4 : bv 32 := 0x00f867b3.
Lemma F_791e4 : fetch_word Asan.M.loaded_segments (0x79234 : word) = Some W_791e4.
Proof. vm_refl. Qed.
Lemma D_791e4 : decode_any W_791e4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_791e8 : bv 32 := 0xfee69ae3.
Lemma F_791e8 : fetch_word Asan.M.loaded_segments (0x79238 : word) = Some W_791e8.
Proof. vm_refl. Qed.
Lemma D_791e8 : decode_any W_791e8 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_791ec : bv 32 := 0x0ff7f693.
Lemma F_791ec : fetch_word Asan.M.loaded_segments (0x7923c : word) = Some W_791ec.
Proof. vm_refl. Qed.
Lemma D_791ec : decode_any W_791ec = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_791f0 : bv 32 := 0xea068ce3.
Lemma F_791f0 : fetch_word Asan.M.loaded_segments (0x79240 : word) = Some W_791f0.
Proof. vm_refl. Qed.
Lemma D_791f0 : decode_any W_791f0 = Some (Branch BC_EQ 13 0 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_791f4 : bv 32 := 0x00050493.
Lemma F_791f4 : fetch_word Asan.M.loaded_segments (0x79244 : word) = Some W_791f4.
Proof. vm_refl. Qed.
Lemma D_791f4 : decode_any W_791f4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_791f8 : bv 32 := 0x00058b13.
Lemma F_791f8 : fetch_word Asan.M.loaded_segments (0x79248 : word) = Some W_791f8.
Proof. vm_refl. Qed.
Lemma D_791f8 : decode_any W_791f8 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_791fc : bv 32 := 0x00060593.
Lemma F_791fc : fetch_word Asan.M.loaded_segments (0x7924c : word) = Some W_791fc.
Proof. vm_refl. Qed.
Lemma D_791fc : decode_any W_791fc = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79200 : bv 32 := 0x00060913.
Lemma F_79200 : fetch_word Asan.M.loaded_segments (0x79250 : word) = Some W_79200.
Proof. vm_refl. Qed.
Lemma D_79200 : decode_any W_79200 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79204 : bv 32 := 0x3f1020ef.
Lemma F_79204 : fetch_word Asan.M.loaded_segments (0x79254 : word) = Some W_79204.
Proof. vm_refl. Qed.
Lemma D_79204 : decode_any W_79204 = Some (Jal 1 11248, 4%Z).
Proof. vm_refl. Qed.

Definition W_79208 : bv 32 := 0x000b0593.
Lemma F_79208 : fetch_word Asan.M.loaded_segments (0x79258 : word) = Some W_79208.
Proof. vm_refl. Qed.
Lemma D_79208 : decode_any W_79208 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7920c : bv 32 := 0x00090613.
Lemma F_7920c : fetch_word Asan.M.loaded_segments (0x7925c : word) = Some W_7920c.
Proof. vm_refl. Qed.
Lemma D_7920c : decode_any W_7920c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79210 : bv 32 := 0x00050993.
Lemma F_79210 : fetch_word Asan.M.loaded_segments (0x79260 : word) = Some W_79210.
Proof. vm_refl. Qed.
Lemma D_79210 : decode_any W_79210 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79214 : bv 32 := 0x00048513.
Lemma F_79214 : fetch_word Asan.M.loaded_segments (0x79264 : word) = Some W_79214.
Proof. vm_refl. Qed.
Lemma D_79214 : decode_any W_79214 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79218 : bv 32 := 0xe80988e3.
Lemma F_79218 : fetch_word Asan.M.loaded_segments (0x79268 : word) = Some W_79218.
Proof. vm_refl. Qed.
Lemma D_79218 : decode_any W_79218 = Some (Branch BC_EQ 19 0 7824, 4%Z).
Proof. vm_refl. Qed.

Definition W_79304 : bv 32 := 0x81010113.
Lemma F_79304 : fetch_word Asan.M.loaded_segments (0x79354 : word) = Some W_79304.
Proof. vm_refl. Qed.
Lemma D_79304 : decode_any W_79304 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_79308 : bv 32 := 0x7e113423.
Lemma F_79308 : fetch_word Asan.M.loaded_segments (0x79358 : word) = Some W_79308.
Proof. vm_refl. Qed.
Lemma D_79308 : decode_any W_79308 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7930c : bv 32 := 0x7e813023.
Lemma F_7930c : fetch_word Asan.M.loaded_segments (0x7935c : word) = Some W_7930c.
Proof. vm_refl. Qed.
Lemma D_7930c : decode_any W_7930c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_79310 : bv 32 := 0x7c913c23.
Lemma F_79310 : fetch_word Asan.M.loaded_segments (0x79360 : word) = Some W_79310.
Proof. vm_refl. Qed.
Lemma D_79310 : decode_any W_79310 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_79314 : bv 32 := 0x7d213823.
Lemma F_79314 : fetch_word Asan.M.loaded_segments (0x79364 : word) = Some W_79314.
Proof. vm_refl. Qed.
Lemma D_79314 : decode_any W_79314 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_79318 : bv 32 := 0x7d313423.
Lemma F_79318 : fetch_word Asan.M.loaded_segments (0x79368 : word) = Some W_79318.
Proof. vm_refl. Qed.
Lemma D_79318 : decode_any W_79318 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7931c : bv 32 := 0x7d413023.
Lemma F_7931c : fetch_word Asan.M.loaded_segments (0x7936c : word) = Some W_7931c.
Proof. vm_refl. Qed.
Lemma D_7931c : decode_any W_7931c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79320 : bv 32 := 0x7b513c23.
Lemma F_79320 : fetch_word Asan.M.loaded_segments (0x79370 : word) = Some W_79320.
Proof. vm_refl. Qed.
Lemma D_79320 : decode_any W_79320 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_79324 : bv 32 := 0x7b613823.
Lemma F_79324 : fetch_word Asan.M.loaded_segments (0x79374 : word) = Some W_79324.
Proof. vm_refl. Qed.
Lemma D_79324 : decode_any W_79324 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_79328 : bv 32 := 0x7b713423.
Lemma F_79328 : fetch_word Asan.M.loaded_segments (0x79378 : word) = Some W_79328.
Proof. vm_refl. Qed.
Lemma D_79328 : decode_any W_79328 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7932c : bv 32 := 0x7f010413.
Lemma F_7932c : fetch_word Asan.M.loaded_segments (0x7937c : word) = Some W_7932c.
Proof. vm_refl. Qed.
Lemma D_7932c : decode_any W_7932c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_79330 : bv 32 := 0xf9010113.
Lemma F_79330 : fetch_word Asan.M.loaded_segments (0x79380 : word) = Some W_79330.
Proof. vm_refl. Qed.
Lemma D_79330 : decode_any W_79330 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79334 : bv 32 := 0x000c1697.
Lemma F_79334 : fetch_word Asan.M.loaded_segments (0x79384 : word) = Some W_79334.
Proof. vm_refl. Qed.
Lemma D_79334 : decode_any W_79334 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_79338 : bv 32 := 0x99c6b683.
Lemma F_79338 : fetch_word Asan.M.loaded_segments (0x79388 : word) = Some W_79338.
Proof. vm_refl. Qed.
Lemma D_79338 : decode_any W_79338 = Some (Load SZ8 true 13 13 2460, 4%Z).
Proof. vm_refl. Qed.

Definition W_7933c : bv 32 := 0x0006c683.
Lemma F_7933c : fetch_word Asan.M.loaded_segments (0x7938c : word) = Some W_7933c.
Proof. vm_refl. Qed.
Lemma D_7933c : decode_any W_7933c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79340 : bv 32 := 0x0a068463.
Lemma F_79340 : fetch_word Asan.M.loaded_segments (0x79390 : word) = Some W_79340.
Proof. vm_refl. Qed.
Lemma D_79340 : decode_any W_79340 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_79344 : bv 32 := 0xfff5c693.
Lemma F_79344 : fetch_word Asan.M.loaded_segments (0x79394 : word) = Some W_79344.
Proof. vm_refl. Qed.
Lemma D_79344 : decode_any W_79344 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79348 : bv 32 := 0x80040a93.
Lemma F_79348 : fetch_word Asan.M.loaded_segments (0x79398 : word) = Some W_79348.
Proof. vm_refl. Qed.
Lemma D_79348 : decode_any W_79348 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7934c : bv 32 := 0xfa0a8a93.
Lemma F_7934c : fetch_word Asan.M.loaded_segments (0x7939c : word) = Some W_7934c.
Proof. vm_refl. Qed.
Lemma D_7934c : decode_any W_7934c = Some (OpImm ALU_ADD 21 21 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_79350 : bv 32 := 0x0cc6e663.
Lemma F_79350 : fetch_word Asan.M.loaded_segments (0x793a0 : word) = Some W_79350.
Proof. vm_refl. Qed.
Lemma D_79350 : decode_any W_79350 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_79354 : bv 32 := 0xfbf60a13.
Lemma F_79354 : fetch_word Asan.M.loaded_segments (0x793a4 : word) = Some W_79354.
Proof. vm_refl. Qed.
Lemma D_79354 : decode_any W_79354 = Some (OpImm ALU_ADD 20 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_79358 : bv 32 := 0xfbf00693.
Lemma F_79358 : fetch_word Asan.M.loaded_segments (0x793a8 : word) = Some W_79358.
Proof. vm_refl. Qed.
Lemma D_79358 : decode_any W_79358 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7935c : bv 32 := 0x1546f463.
Lemma F_7935c : fetch_word Asan.M.loaded_segments (0x793ac : word) = Some W_7935c.
Proof. vm_refl. Qed.
Lemma D_7935c : decode_any W_7935c = Some (Branch BC_GEU 13 20 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_79360 : bv 32 := 0x000c0697.
Lemma F_79360 : fetch_word Asan.M.loaded_segments (0x793b0 : word) = Some W_79360.
Proof. vm_refl. Qed.
Lemma D_79360 : decode_any W_79360 = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_79364 : bv 32 := 0xe086b683.
Lemma F_79364 : fetch_word Asan.M.loaded_segments (0x793b4 : word) = Some W_79364.
Proof. vm_refl. Qed.
Lemma D_79364 : decode_any W_79364 = Some (Load SZ8 true 13 13 3592, 4%Z).
Proof. vm_refl. Qed.

Definition W_79368 : bv 32 := 0x00c587b3.
Lemma F_79368 : fetch_word Asan.M.loaded_segments (0x793b8 : word) = Some W_79368.
Proof. vm_refl. Qed.
Lemma D_79368 : decode_any W_79368 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7936c : bv 32 := 0x0006b703.
Lemma F_7936c : fetch_word Asan.M.loaded_segments (0x793bc : word) = Some W_7936c.
Proof. vm_refl. Qed.
Lemma D_7936c : decode_any W_7936c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79370 : bv 32 := 0x0035d693.
Lemma F_79370 : fetch_word Asan.M.loaded_segments (0x793c0 : word) = Some W_79370.
Proof. vm_refl. Qed.
Lemma D_79370 : decode_any W_79370 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79374 : bv 32 := 0xfff78793.
Lemma F_79374 : fetch_word Asan.M.loaded_segments (0x793c4 : word) = Some W_79374.
Proof. vm_refl. Qed.
Lemma D_79374 : decode_any W_79374 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79378 : bv 32 := 0x0037d813.
Lemma F_79378 : fetch_word Asan.M.loaded_segments (0x793c8 : word) = Some W_79378.
Proof. vm_refl. Qed.
Lemma D_79378 : decode_any W_79378 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7937c : bv 32 := 0x00d706b3.
Lemma F_7937c : fetch_word Asan.M.loaded_segments (0x793cc : word) = Some W_7937c.
Proof. vm_refl. Qed.
Lemma D_7937c : decode_any W_7937c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_79380 : bv 32 := 0x01070733.
Lemma F_79380 : fetch_word Asan.M.loaded_segments (0x793d0 : word) = Some W_79380.
Proof. vm_refl. Qed.
Lemma D_79380 : decode_any W_79380 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79384 : bv 32 := 0xff86f813.
Lemma F_79384 : fetch_word Asan.M.loaded_segments (0x793d4 : word) = Some W_79384.
Proof. vm_refl. Qed.
Lemma D_79384 : decode_any W_79384 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79388 : bv 32 := 0xff877893.
Lemma F_79388 : fetch_word Asan.M.loaded_segments (0x793d8 : word) = Some W_79388.
Proof. vm_refl. Qed.
Lemma D_79388 : decode_any W_79388 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7938c : bv 32 := 0x00083803.
Lemma F_7938c : fetch_word Asan.M.loaded_segments (0x793dc : word) = Some W_7938c.
Proof. vm_refl. Qed.
Lemma D_7938c : decode_any W_7938c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79390 : bv 32 := 0x0008b883.
Lemma F_79390 : fetch_word Asan.M.loaded_segments (0x793e0 : word) = Some W_79390.
Proof. vm_refl. Qed.
Lemma D_79390 : decode_any W_79390 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79394 : bv 32 := 0x0108e833.
Lemma F_79394 : fetch_word Asan.M.loaded_segments (0x793e4 : word) = Some W_79394.
Proof. vm_refl. Qed.
Lemma D_79394 : decode_any W_79394 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79398 : bv 32 := 0x1a081063.
Lemma F_79398 : fetch_word Asan.M.loaded_segments (0x793e8 : word) = Some W_79398.
Proof. vm_refl. Qed.
Lemma D_79398 : decode_any W_79398 = Some (Branch BC_NE 16 0 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_7939c : bv 32 := 0xfff54693.
Lemma F_7939c : fetch_word Asan.M.loaded_segments (0x793ec : word) = Some W_7939c.
Proof. vm_refl. Qed.
Lemma D_7939c : decode_any W_7939c = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_793a0 : bv 32 := 0x10c6e663.
Lemma F_793a0 : fetch_word Asan.M.loaded_segments (0x793f0 : word) = Some W_793a0.
Proof. vm_refl. Qed.
Lemma D_793a0 : decode_any W_793a0 = Some (Branch BC_LTU 13 12 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_793a4 : bv 32 := 0xfbf00693.
Lemma F_793a4 : fetch_word Asan.M.loaded_segments (0x793f4 : word) = Some W_793a4.
Proof. vm_refl. Qed.
Lemma D_793a4 : decode_any W_793a4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_793a8 : bv 32 := 0x1946f463.
Lemma F_793a8 : fetch_word Asan.M.loaded_segments (0x793f8 : word) = Some W_793a8.
Proof. vm_refl. Qed.
Lemma D_793a8 : decode_any W_793a8 = Some (Branch BC_GEU 13 20 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_793ac : bv 32 := 0x000c0697.
Lemma F_793ac : fetch_word Asan.M.loaded_segments (0x793fc : word) = Some W_793ac.
Proof. vm_refl. Qed.
Lemma D_793ac : decode_any W_793ac = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_793b0 : bv 32 := 0xdbc6b683.
Lemma F_793b0 : fetch_word Asan.M.loaded_segments (0x79400 : word) = Some W_793b0.
Proof. vm_refl. Qed.
Lemma D_793b0 : decode_any W_793b0 = Some (Load SZ8 true 13 13 3516, 4%Z).
Proof. vm_refl. Qed.

Definition W_793b4 : bv 32 := 0x00c507b3.
Lemma F_793b4 : fetch_word Asan.M.loaded_segments (0x79404 : word) = Some W_793b4.
Proof. vm_refl. Qed.
Lemma D_793b4 : decode_any W_793b4 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_793b8 : bv 32 := 0x0006b703.
Lemma F_793b8 : fetch_word Asan.M.loaded_segments (0x79408 : word) = Some W_793b8.
Proof. vm_refl. Qed.
Lemma D_793b8 : decode_any W_793b8 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_793bc : bv 32 := 0x00355693.
Lemma F_793bc : fetch_word Asan.M.loaded_segments (0x7940c : word) = Some W_793bc.
Proof. vm_refl. Qed.
Lemma D_793bc : decode_any W_793bc = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_793c0 : bv 32 := 0xfff78793.
Lemma F_793c0 : fetch_word Asan.M.loaded_segments (0x79410 : word) = Some W_793c0.
Proof. vm_refl. Qed.
Lemma D_793c0 : decode_any W_793c0 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_793c4 : bv 32 := 0x0037d813.
Lemma F_793c4 : fetch_word Asan.M.loaded_segments (0x79414 : word) = Some W_793c4.
Proof. vm_refl. Qed.
Lemma D_793c4 : decode_any W_793c4 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_793c8 : bv 32 := 0x00d706b3.
Lemma F_793c8 : fetch_word Asan.M.loaded_segments (0x79418 : word) = Some W_793c8.
Proof. vm_refl. Qed.
Lemma D_793c8 : decode_any W_793c8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_793cc : bv 32 := 0x01070733.
Lemma F_793cc : fetch_word Asan.M.loaded_segments (0x7941c : word) = Some W_793cc.
Proof. vm_refl. Qed.
Lemma D_793cc : decode_any W_793cc = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_793d0 : bv 32 := 0xff86f813.
Lemma F_793d0 : fetch_word Asan.M.loaded_segments (0x79420 : word) = Some W_793d0.
Proof. vm_refl. Qed.
Lemma D_793d0 : decode_any W_793d0 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_793d4 : bv 32 := 0xff877893.
Lemma F_793d4 : fetch_word Asan.M.loaded_segments (0x79424 : word) = Some W_793d4.
Proof. vm_refl. Qed.
Lemma D_793d4 : decode_any W_793d4 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_793d8 : bv 32 := 0x00083803.
Lemma F_793d8 : fetch_word Asan.M.loaded_segments (0x79428 : word) = Some W_793d8.
Proof. vm_refl. Qed.
Lemma D_793d8 : decode_any W_793d8 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_793dc : bv 32 := 0x0008b883.
Lemma F_793dc : fetch_word Asan.M.loaded_segments (0x7942c : word) = Some W_793dc.
Proof. vm_refl. Qed.
Lemma D_793dc : decode_any W_793dc = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_793e0 : bv 32 := 0x0108e833.
Lemma F_793e0 : fetch_word Asan.M.loaded_segments (0x79430 : word) = Some W_793e0.
Proof. vm_refl. Qed.
Lemma D_793e0 : decode_any W_793e0 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_793e4 : bv 32 := 0x24081a63.
Lemma F_793e4 : fetch_word Asan.M.loaded_segments (0x79434 : word) = Some W_793e4.
Proof. vm_refl. Qed.
Lemma D_793e4 : decode_any W_793e4 = Some (Branch BC_NE 16 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_793e8 : bv 32 := 0x155120ef.
Lemma F_793e8 : fetch_word Asan.M.loaded_segments (0x79438 : word) = Some W_793e8.
Proof. vm_refl. Qed.
Lemma D_793e8 : decode_any W_793e8 = Some (Jal 1 76116, 4%Z).
Proof. vm_refl. Qed.

Definition W_793ec : bv 32 := 0x07010113.
Lemma F_793ec : fetch_word Asan.M.loaded_segments (0x7943c : word) = Some W_793ec.
Proof. vm_refl. Qed.
Lemma D_793ec : decode_any W_793ec = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_793f0 : bv 32 := 0x7e813083.
Lemma F_793f0 : fetch_word Asan.M.loaded_segments (0x79440 : word) = Some W_793f0.
Proof. vm_refl. Qed.
Lemma D_793f0 : decode_any W_793f0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_793f4 : bv 32 := 0x7e013403.
Lemma F_793f4 : fetch_word Asan.M.loaded_segments (0x79444 : word) = Some W_793f4.
Proof. vm_refl. Qed.
Lemma D_793f4 : decode_any W_793f4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_793f8 : bv 32 := 0x7d813483.
Lemma F_793f8 : fetch_word Asan.M.loaded_segments (0x79448 : word) = Some W_793f8.
Proof. vm_refl. Qed.
Lemma D_793f8 : decode_any W_793f8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_793fc : bv 32 := 0x7d013903.
Lemma F_793fc : fetch_word Asan.M.loaded_segments (0x7944c : word) = Some W_793fc.
Proof. vm_refl. Qed.
Lemma D_793fc : decode_any W_793fc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_79400 : bv 32 := 0x7c813983.
Lemma F_79400 : fetch_word Asan.M.loaded_segments (0x79450 : word) = Some W_79400.
Proof. vm_refl. Qed.
Lemma D_79400 : decode_any W_79400 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_79404 : bv 32 := 0x7c013a03.
Lemma F_79404 : fetch_word Asan.M.loaded_segments (0x79454 : word) = Some W_79404.
Proof. vm_refl. Qed.
Lemma D_79404 : decode_any W_79404 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79408 : bv 32 := 0x7b813a83.
Lemma F_79408 : fetch_word Asan.M.loaded_segments (0x79458 : word) = Some W_79408.
Proof. vm_refl. Qed.
Lemma D_79408 : decode_any W_79408 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7940c : bv 32 := 0x7b013b03.
Lemma F_7940c : fetch_word Asan.M.loaded_segments (0x7945c : word) = Some W_7940c.
Proof. vm_refl. Qed.
Lemma D_7940c : decode_any W_7940c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_79410 : bv 32 := 0x7a813b83.
Lemma F_79410 : fetch_word Asan.M.loaded_segments (0x79460 : word) = Some W_79410.
Proof. vm_refl. Qed.
Lemma D_79410 : decode_any W_79410 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_79414 : bv 32 := 0x7f010113.
Lemma F_79414 : fetch_word Asan.M.loaded_segments (0x79464 : word) = Some W_79414.
Proof. vm_refl. Qed.
Lemma D_79414 : decode_any W_79414 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_79418 : bv 32 := 0x00008067.
Lemma F_79418 : fetch_word Asan.M.loaded_segments (0x79468 : word) = Some W_79418.
Proof. vm_refl. Qed.
Lemma D_79418 : decode_any W_79418 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_794a4 : bv 32 := 0x0c061463.
Lemma F_794a4 : fetch_word Asan.M.loaded_segments (0x794f4 : word) = Some W_794a4.
Proof. vm_refl. Qed.
Lemma D_794a4 : decode_any W_794a4 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_794a8 : bv 32 := 0xef5ff06f.
Lemma F_794a8 : fetch_word Asan.M.loaded_segments (0x794f8 : word) = Some W_794a8.
Proof. vm_refl. Qed.
Lemma D_794a8 : decode_any W_794a8 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_79530 : bv 32 := 0x12061e63.
Lemma F_79530 : fetch_word Asan.M.loaded_segments (0x79580 : word) = Some W_79530.
Proof. vm_refl. Qed.
Lemma D_79530 : decode_any W_79530 = Some (Branch BC_NE 12 0 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_79534 : bv 32 := 0xeb5ff06f.
Lemma F_79534 : fetch_word Asan.M.loaded_segments (0x79584 : word) = Some W_79534.
Proof. vm_refl. Qed.
Lemma D_79534 : decode_any W_79534 = Some (Jal 0 2096820, 4%Z).
Proof. vm_refl. Qed.

Definition W_79538 : bv 32 := 0x00070803.
Lemma F_79538 : fetch_word Asan.M.loaded_segments (0x79588 : word) = Some W_79538.
Proof. vm_refl. Qed.
Lemma D_79538 : decode_any W_79538 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7953c : bv 32 := 0x0077f793.
Lemma F_7953c : fetch_word Asan.M.loaded_segments (0x7958c : word) = Some W_7953c.
Proof. vm_refl. Qed.
Lemma D_7953c : decode_any W_7953c = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_79540 : bv 32 := 0x010038b3.
Lemma F_79540 : fetch_word Asan.M.loaded_segments (0x79590 : word) = Some W_79540.
Proof. vm_refl. Qed.
Lemma D_79540 : decode_any W_79540 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79544 : bv 32 := 0x0107a7b3.
Lemma F_79544 : fetch_word Asan.M.loaded_segments (0x79594 : word) = Some W_79544.
Proof. vm_refl. Qed.
Lemma D_79544 : decode_any W_79544 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79548 : bv 32 := 0x0017c793.
Lemma F_79548 : fetch_word Asan.M.loaded_segments (0x79598 : word) = Some W_79548.
Proof. vm_refl. Qed.
Lemma D_79548 : decode_any W_79548 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7954c : bv 32 := 0x00f8f7b3.
Lemma F_7954c : fetch_word Asan.M.loaded_segments (0x7959c : word) = Some W_7954c.
Proof. vm_refl. Qed.
Lemma D_7954c : decode_any W_7954c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79550 : bv 32 := 0x00e6fa63.
Lemma F_79550 : fetch_word Asan.M.loaded_segments (0x795a0 : word) = Some W_79550.
Proof. vm_refl. Qed.
Lemma D_79550 : decode_any W_79550 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79554 : bv 32 := 0x0006c803.
Lemma F_79554 : fetch_word Asan.M.loaded_segments (0x795a4 : word) = Some W_79554.
Proof. vm_refl. Qed.
Lemma D_79554 : decode_any W_79554 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79558 : bv 32 := 0x00168693.
Lemma F_79558 : fetch_word Asan.M.loaded_segments (0x795a8 : word) = Some W_79558.
Proof. vm_refl. Qed.
Lemma D_79558 : decode_any W_79558 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7955c : bv 32 := 0x00f867b3.
Lemma F_7955c : fetch_word Asan.M.loaded_segments (0x795ac : word) = Some W_7955c.
Proof. vm_refl. Qed.
Lemma D_7955c : decode_any W_7955c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79560 : bv 32 := 0xfee69ae3.
Lemma F_79560 : fetch_word Asan.M.loaded_segments (0x795b0 : word) = Some W_79560.
Proof. vm_refl. Qed.
Lemma D_79560 : decode_any W_79560 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79564 : bv 32 := 0x0ff7f693.
Lemma F_79564 : fetch_word Asan.M.loaded_segments (0x795b4 : word) = Some W_79564.
Proof. vm_refl. Qed.
Lemma D_79564 : decode_any W_79564 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_79568 : bv 32 := 0xe2068ae3.
Lemma F_79568 : fetch_word Asan.M.loaded_segments (0x795b8 : word) = Some W_79568.
Proof. vm_refl. Qed.
Lemma D_79568 : decode_any W_79568 = Some (Branch BC_EQ 13 0 7732, 4%Z).
Proof. vm_refl. Qed.

Definition W_7956c : bv 32 := 0x00050b13.
Lemma F_7956c : fetch_word Asan.M.loaded_segments (0x795bc : word) = Some W_7956c.
Proof. vm_refl. Qed.
Lemma D_7956c : decode_any W_7956c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79570 : bv 32 := 0x00058513.
Lemma F_79570 : fetch_word Asan.M.loaded_segments (0x795c0 : word) = Some W_79570.
Proof. vm_refl. Qed.
Lemma D_79570 : decode_any W_79570 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79574 : bv 32 := 0x00058b93.
Lemma F_79574 : fetch_word Asan.M.loaded_segments (0x795c4 : word) = Some W_79574.
Proof. vm_refl. Qed.
Lemma D_79574 : decode_any W_79574 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79578 : bv 32 := 0x00060593.
Lemma F_79578 : fetch_word Asan.M.loaded_segments (0x795c8 : word) = Some W_79578.
Proof. vm_refl. Qed.
Lemma D_79578 : decode_any W_79578 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7957c : bv 32 := 0x00060493.
Lemma F_7957c : fetch_word Asan.M.loaded_segments (0x795cc : word) = Some W_7957c.
Proof. vm_refl. Qed.
Lemma D_7957c : decode_any W_7957c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79580 : bv 32 := 0x075020ef.
Lemma F_79580 : fetch_word Asan.M.loaded_segments (0x795d0 : word) = Some W_79580.
Proof. vm_refl. Qed.
Lemma D_79580 : decode_any W_79580 = Some (Jal 1 10356, 4%Z).
Proof. vm_refl. Qed.

Definition W_79584 : bv 32 := 0x000b8593.
Lemma F_79584 : fetch_word Asan.M.loaded_segments (0x795d4 : word) = Some W_79584.
Proof. vm_refl. Qed.
Lemma D_79584 : decode_any W_79584 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79588 : bv 32 := 0x00048613.
Lemma F_79588 : fetch_word Asan.M.loaded_segments (0x795d8 : word) = Some W_79588.
Proof. vm_refl. Qed.
Lemma D_79588 : decode_any W_79588 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7958c : bv 32 := 0x00050913.
Lemma F_7958c : fetch_word Asan.M.loaded_segments (0x795dc : word) = Some W_7958c.
Proof. vm_refl. Qed.
Lemma D_7958c : decode_any W_7958c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79590 : bv 32 := 0x000b0513.
Lemma F_79590 : fetch_word Asan.M.loaded_segments (0x795e0 : word) = Some W_79590.
Proof. vm_refl. Qed.
Lemma D_79590 : decode_any W_79590 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79594 : bv 32 := 0xe00904e3.
Lemma F_79594 : fetch_word Asan.M.loaded_segments (0x795e4 : word) = Some W_79594.
Proof. vm_refl. Qed.
Lemma D_79594 : decode_any W_79594 = Some (Branch BC_EQ 18 0 7688, 4%Z).
Proof. vm_refl. Qed.

Definition W_79638 : bv 32 := 0x00070803.
Lemma F_79638 : fetch_word Asan.M.loaded_segments (0x79688 : word) = Some W_79638.
Proof. vm_refl. Qed.
Lemma D_79638 : decode_any W_79638 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7963c : bv 32 := 0x0077f793.
Lemma F_7963c : fetch_word Asan.M.loaded_segments (0x7968c : word) = Some W_7963c.
Proof. vm_refl. Qed.
Lemma D_7963c : decode_any W_7963c = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_79640 : bv 32 := 0x010038b3.
Lemma F_79640 : fetch_word Asan.M.loaded_segments (0x79690 : word) = Some W_79640.
Proof. vm_refl. Qed.
Lemma D_79640 : decode_any W_79640 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79644 : bv 32 := 0x0107a7b3.
Lemma F_79644 : fetch_word Asan.M.loaded_segments (0x79694 : word) = Some W_79644.
Proof. vm_refl. Qed.
Lemma D_79644 : decode_any W_79644 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79648 : bv 32 := 0x0017c793.
Lemma F_79648 : fetch_word Asan.M.loaded_segments (0x79698 : word) = Some W_79648.
Proof. vm_refl. Qed.
Lemma D_79648 : decode_any W_79648 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7964c : bv 32 := 0x00f8f7b3.
Lemma F_7964c : fetch_word Asan.M.loaded_segments (0x7969c : word) = Some W_7964c.
Proof. vm_refl. Qed.
Lemma D_7964c : decode_any W_7964c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79650 : bv 32 := 0x00e6fa63.
Lemma F_79650 : fetch_word Asan.M.loaded_segments (0x796a0 : word) = Some W_79650.
Proof. vm_refl. Qed.
Lemma D_79650 : decode_any W_79650 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79654 : bv 32 := 0x0006c803.
Lemma F_79654 : fetch_word Asan.M.loaded_segments (0x796a4 : word) = Some W_79654.
Proof. vm_refl. Qed.
Lemma D_79654 : decode_any W_79654 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79658 : bv 32 := 0x00168693.
Lemma F_79658 : fetch_word Asan.M.loaded_segments (0x796a8 : word) = Some W_79658.
Proof. vm_refl. Qed.
Lemma D_79658 : decode_any W_79658 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7965c : bv 32 := 0x00f867b3.
Lemma F_7965c : fetch_word Asan.M.loaded_segments (0x796ac : word) = Some W_7965c.
Proof. vm_refl. Qed.
Lemma D_7965c : decode_any W_7965c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79660 : bv 32 := 0xfee69ae3.
Lemma F_79660 : fetch_word Asan.M.loaded_segments (0x796b0 : word) = Some W_79660.
Proof. vm_refl. Qed.
Lemma D_79660 : decode_any W_79660 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79664 : bv 32 := 0x0ff7f693.
Lemma F_79664 : fetch_word Asan.M.loaded_segments (0x796b4 : word) = Some W_79664.
Proof. vm_refl. Qed.
Lemma D_79664 : decode_any W_79664 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_79668 : bv 32 := 0xd80680e3.
Lemma F_79668 : fetch_word Asan.M.loaded_segments (0x796b8 : word) = Some W_79668.
Proof. vm_refl. Qed.
Lemma D_79668 : decode_any W_79668 = Some (Branch BC_EQ 13 0 7552, 4%Z).
Proof. vm_refl. Qed.

Definition W_7966c : bv 32 := 0x00050493.
Lemma F_7966c : fetch_word Asan.M.loaded_segments (0x796bc : word) = Some W_7966c.
Proof. vm_refl. Qed.
Lemma D_7966c : decode_any W_7966c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79670 : bv 32 := 0x00058b13.
Lemma F_79670 : fetch_word Asan.M.loaded_segments (0x796c0 : word) = Some W_79670.
Proof. vm_refl. Qed.
Lemma D_79670 : decode_any W_79670 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79674 : bv 32 := 0x00060593.
Lemma F_79674 : fetch_word Asan.M.loaded_segments (0x796c4 : word) = Some W_79674.
Proof. vm_refl. Qed.
Lemma D_79674 : decode_any W_79674 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79678 : bv 32 := 0x00060913.
Lemma F_79678 : fetch_word Asan.M.loaded_segments (0x796c8 : word) = Some W_79678.
Proof. vm_refl. Qed.
Lemma D_79678 : decode_any W_79678 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7967c : bv 32 := 0x778020ef.
Lemma F_7967c : fetch_word Asan.M.loaded_segments (0x796cc : word) = Some W_7967c.
Proof. vm_refl. Qed.
Lemma D_7967c : decode_any W_7967c = Some (Jal 1 10104, 4%Z).
Proof. vm_refl. Qed.

Definition W_79680 : bv 32 := 0x000b0593.
Lemma F_79680 : fetch_word Asan.M.loaded_segments (0x796d0 : word) = Some W_79680.
Proof. vm_refl. Qed.
Lemma D_79680 : decode_any W_79680 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79684 : bv 32 := 0x00090613.
Lemma F_79684 : fetch_word Asan.M.loaded_segments (0x796d4 : word) = Some W_79684.
Proof. vm_refl. Qed.
Lemma D_79684 : decode_any W_79684 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79688 : bv 32 := 0x00050993.
Lemma F_79688 : fetch_word Asan.M.loaded_segments (0x796d8 : word) = Some W_79688.
Proof. vm_refl. Qed.
Lemma D_79688 : decode_any W_79688 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7968c : bv 32 := 0x00048513.
Lemma F_7968c : fetch_word Asan.M.loaded_segments (0x796dc : word) = Some W_7968c.
Proof. vm_refl. Qed.
Lemma D_7968c : decode_any W_7968c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79690 : bv 32 := 0xd4098ce3.
Lemma F_79690 : fetch_word Asan.M.loaded_segments (0x796e0 : word) = Some W_79690.
Proof. vm_refl. Qed.
Lemma D_79690 : decode_any W_79690 = Some (Branch BC_EQ 19 0 7512, 4%Z).
Proof. vm_refl. Qed.

Definition W_797c4 : bv 32 := 0x81010113.
Lemma F_797c4 : fetch_word Asan.M.loaded_segments (0x79814 : word) = Some W_797c4.
Proof. vm_refl. Qed.
Lemma D_797c4 : decode_any W_797c4 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_797c8 : bv 32 := 0x7e113423.
Lemma F_797c8 : fetch_word Asan.M.loaded_segments (0x79818 : word) = Some W_797c8.
Proof. vm_refl. Qed.
Lemma D_797c8 : decode_any W_797c8 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_797cc : bv 32 := 0x7e813023.
Lemma F_797cc : fetch_word Asan.M.loaded_segments (0x7981c : word) = Some W_797cc.
Proof. vm_refl. Qed.
Lemma D_797cc : decode_any W_797cc = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_797d0 : bv 32 := 0x7c913c23.
Lemma F_797d0 : fetch_word Asan.M.loaded_segments (0x79820 : word) = Some W_797d0.
Proof. vm_refl. Qed.
Lemma D_797d0 : decode_any W_797d0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_797d4 : bv 32 := 0x7d213823.
Lemma F_797d4 : fetch_word Asan.M.loaded_segments (0x79824 : word) = Some W_797d4.
Proof. vm_refl. Qed.
Lemma D_797d4 : decode_any W_797d4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_797d8 : bv 32 := 0x7d313423.
Lemma F_797d8 : fetch_word Asan.M.loaded_segments (0x79828 : word) = Some W_797d8.
Proof. vm_refl. Qed.
Lemma D_797d8 : decode_any W_797d8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_797dc : bv 32 := 0x7d413023.
Lemma F_797dc : fetch_word Asan.M.loaded_segments (0x7982c : word) = Some W_797dc.
Proof. vm_refl. Qed.
Lemma D_797dc : decode_any W_797dc = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_797e0 : bv 32 := 0x7b513c23.
Lemma F_797e0 : fetch_word Asan.M.loaded_segments (0x79830 : word) = Some W_797e0.
Proof. vm_refl. Qed.
Lemma D_797e0 : decode_any W_797e0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_797e4 : bv 32 := 0x7b613823.
Lemma F_797e4 : fetch_word Asan.M.loaded_segments (0x79834 : word) = Some W_797e4.
Proof. vm_refl. Qed.
Lemma D_797e4 : decode_any W_797e4 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_797e8 : bv 32 := 0x7b713423.
Lemma F_797e8 : fetch_word Asan.M.loaded_segments (0x79838 : word) = Some W_797e8.
Proof. vm_refl. Qed.
Lemma D_797e8 : decode_any W_797e8 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_797ec : bv 32 := 0x7b813023.
Lemma F_797ec : fetch_word Asan.M.loaded_segments (0x7983c : word) = Some W_797ec.
Proof. vm_refl. Qed.
Lemma D_797ec : decode_any W_797ec = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_797f0 : bv 32 := 0x7f010413.
Lemma F_797f0 : fetch_word Asan.M.loaded_segments (0x79840 : word) = Some W_797f0.
Proof. vm_refl. Qed.
Lemma D_797f0 : decode_any W_797f0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_797f4 : bv 32 := 0xf8010113.
Lemma F_797f4 : fetch_word Asan.M.loaded_segments (0x79844 : word) = Some W_797f4.
Proof. vm_refl. Qed.
Lemma D_797f4 : decode_any W_797f4 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_797f8 : bv 32 := 0x000c0697.
Lemma F_797f8 : fetch_word Asan.M.loaded_segments (0x79848 : word) = Some W_797f8.
Proof. vm_refl. Qed.
Lemma D_797f8 : decode_any W_797f8 = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_797fc : bv 32 := 0x4d86b683.
Lemma F_797fc : fetch_word Asan.M.loaded_segments (0x7984c : word) = Some W_797fc.
Proof. vm_refl. Qed.
Lemma D_797fc : decode_any W_797fc = Some (Load SZ8 true 13 13 1240, 4%Z).
Proof. vm_refl. Qed.

Definition W_79800 : bv 32 := 0x0006c683.
Lemma F_79800 : fetch_word Asan.M.loaded_segments (0x79850 : word) = Some W_79800.
Proof. vm_refl. Qed.
Lemma D_79800 : decode_any W_79800 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79804 : bv 32 := 0x0e068a63.
Lemma F_79804 : fetch_word Asan.M.loaded_segments (0x79854 : word) = Some W_79804.
Proof. vm_refl. Qed.
Lemma D_79804 : decode_any W_79804 = Some (Branch BC_EQ 13 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_79808 : bv 32 := 0x80040a93.
Lemma F_79808 : fetch_word Asan.M.loaded_segments (0x79858 : word) = Some W_79808.
Proof. vm_refl. Qed.
Lemma D_79808 : decode_any W_79808 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7980c : bv 32 := 0xf98a8a93.
Lemma F_7980c : fetch_word Asan.M.loaded_segments (0x7985c : word) = Some W_7980c.
Proof. vm_refl. Qed.
Lemma D_7980c : decode_any W_7980c = Some (OpImm ALU_ADD 21 21 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_79810 : bv 32 := 0x00c589b3.
Lemma F_79810 : fetch_word Asan.M.loaded_segments (0x79860 : word) = Some W_79810.
Proof. vm_refl. Qed.
Lemma D_79810 : decode_any W_79810 = Some (Op ALU_ADD 19 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_79814 : bv 32 := 0x00c50a33.
Lemma F_79814 : fetch_word Asan.M.loaded_segments (0x79864 : word) = Some W_79814.
Proof. vm_refl. Qed.
Lemma D_79814 : decode_any W_79814 = Some (Op ALU_ADD 20 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_79818 : bv 32 := 0x00b50663.
Lemma F_79818 : fetch_word Asan.M.loaded_segments (0x79868 : word) = Some W_79818.
Proof. vm_refl. Qed.
Lemma D_79818 : decode_any W_79818 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7981c : bv 32 := 0x0145f463.
Lemma F_7981c : fetch_word Asan.M.loaded_segments (0x7986c : word) = Some W_7981c.
Proof. vm_refl. Qed.
Lemma D_7981c : decode_any W_7981c = Some (Branch BC_GEU 11 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_79820 : bv 32 := 0x1b356e63.
Lemma F_79820 : fetch_word Asan.M.loaded_segments (0x79870 : word) = Some W_79820.
Proof. vm_refl. Qed.
Lemma D_79820 : decode_any W_79820 = Some (Branch BC_LTU 10 19 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_79824 : bv 32 := 0xfff5c693.
Lemma F_79824 : fetch_word Asan.M.loaded_segments (0x79874 : word) = Some W_79824.
Proof. vm_refl. Qed.
Lemma D_79824 : decode_any W_79824 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79828 : bv 32 := 0x26c6e863.
Lemma F_79828 : fetch_word Asan.M.loaded_segments (0x79878 : word) = Some W_79828.
Proof. vm_refl. Qed.
Lemma D_79828 : decode_any W_79828 = Some (Branch BC_LTU 13 12 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_7982c : bv 32 := 0xfbf60b13.
Lemma F_7982c : fetch_word Asan.M.loaded_segments (0x7987c : word) = Some W_7982c.
Proof. vm_refl. Qed.
Lemma D_7982c : decode_any W_7982c = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_79830 : bv 32 := 0xfbf00693.
Lemma F_79830 : fetch_word Asan.M.loaded_segments (0x79880 : word) = Some W_79830.
Proof. vm_refl. Qed.
Lemma D_79830 : decode_any W_79830 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_79834 : bv 32 := 0x2f66f663.
Lemma F_79834 : fetch_word Asan.M.loaded_segments (0x79884 : word) = Some W_79834.
Proof. vm_refl. Qed.
Lemma D_79834 : decode_any W_79834 = Some (Branch BC_GEU 13 22 748, 4%Z).
Proof. vm_refl. Qed.

Definition W_79838 : bv 32 := 0x000c0697.
Lemma F_79838 : fetch_word Asan.M.loaded_segments (0x79888 : word) = Some W_79838.
Proof. vm_refl. Qed.
Lemma D_79838 : decode_any W_79838 = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7983c : bv 32 := 0x9306b683.
Lemma F_7983c : fetch_word Asan.M.loaded_segments (0x7988c : word) = Some W_7983c.
Proof. vm_refl. Qed.
Lemma D_7983c : decode_any W_7983c = Some (Load SZ8 true 13 13 2352, 4%Z).
Proof. vm_refl. Qed.

Definition W_79840 : bv 32 := 0x0006b703.
Lemma F_79840 : fetch_word Asan.M.loaded_segments (0x79890 : word) = Some W_79840.
Proof. vm_refl. Qed.
Lemma D_79840 : decode_any W_79840 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79844 : bv 32 := 0xfff98993.
Lemma F_79844 : fetch_word Asan.M.loaded_segments (0x79894 : word) = Some W_79844.
Proof. vm_refl. Qed.
Lemma D_79844 : decode_any W_79844 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79848 : bv 32 := 0x0035d693.
Lemma F_79848 : fetch_word Asan.M.loaded_segments (0x79898 : word) = Some W_79848.
Proof. vm_refl. Qed.
Lemma D_79848 : decode_any W_79848 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7984c : bv 32 := 0x0039d793.
Lemma F_7984c : fetch_word Asan.M.loaded_segments (0x7989c : word) = Some W_7984c.
Proof. vm_refl. Qed.
Lemma D_7984c : decode_any W_7984c = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79850 : bv 32 := 0x00d706b3.
Lemma F_79850 : fetch_word Asan.M.loaded_segments (0x798a0 : word) = Some W_79850.
Proof. vm_refl. Qed.
Lemma D_79850 : decode_any W_79850 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_79854 : bv 32 := 0x00f70733.
Lemma F_79854 : fetch_word Asan.M.loaded_segments (0x798a4 : word) = Some W_79854.
Proof. vm_refl. Qed.
Lemma D_79854 : decode_any W_79854 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79858 : bv 32 := 0xff86f793.
Lemma F_79858 : fetch_word Asan.M.loaded_segments (0x798a8 : word) = Some W_79858.
Proof. vm_refl. Qed.
Lemma D_79858 : decode_any W_79858 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7985c : bv 32 := 0xff877813.
Lemma F_7985c : fetch_word Asan.M.loaded_segments (0x798ac : word) = Some W_7985c.
Proof. vm_refl. Qed.
Lemma D_7985c : decode_any W_7985c = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79860 : bv 32 := 0x0007b783.
Lemma F_79860 : fetch_word Asan.M.loaded_segments (0x798b0 : word) = Some W_79860.
Proof. vm_refl. Qed.
Lemma D_79860 : decode_any W_79860 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79864 : bv 32 := 0x00083803.
Lemma F_79864 : fetch_word Asan.M.loaded_segments (0x798b4 : word) = Some W_79864.
Proof. vm_refl. Qed.
Lemma D_79864 : decode_any W_79864 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79868 : bv 32 := 0x00f867b3.
Lemma F_79868 : fetch_word Asan.M.loaded_segments (0x798b8 : word) = Some W_79868.
Proof. vm_refl. Qed.
Lemma D_79868 : decode_any W_79868 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7986c : bv 32 := 0x2a079e63.
Lemma F_7986c : fetch_word Asan.M.loaded_segments (0x798bc : word) = Some W_7986c.
Proof. vm_refl. Qed.
Lemma D_7986c : decode_any W_7986c = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

Definition W_79870 : bv 32 := 0xfff54693.
Lemma F_79870 : fetch_word Asan.M.loaded_segments (0x798c0 : word) = Some W_79870.
Proof. vm_refl. Qed.
Lemma D_79870 : decode_any W_79870 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79874 : bv 32 := 0x0cc6ee63.
Lemma F_79874 : fetch_word Asan.M.loaded_segments (0x798c4 : word) = Some W_79874.
Proof. vm_refl. Qed.
Lemma D_79874 : decode_any W_79874 = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_79878 : bv 32 := 0xfbf00693.
Lemma F_79878 : fetch_word Asan.M.loaded_segments (0x798c8 : word) = Some W_79878.
Proof. vm_refl. Qed.
Lemma D_79878 : decode_any W_79878 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7987c : bv 32 := 0x1566fc63.
Lemma F_7987c : fetch_word Asan.M.loaded_segments (0x798cc : word) = Some W_7987c.
Proof. vm_refl. Qed.
Lemma D_7987c : decode_any W_7987c = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_79880 : bv 32 := 0x000c0697.
Lemma F_79880 : fetch_word Asan.M.loaded_segments (0x798d0 : word) = Some W_79880.
Proof. vm_refl. Qed.
Lemma D_79880 : decode_any W_79880 = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_79884 : bv 32 := 0x8e86b683.
Lemma F_79884 : fetch_word Asan.M.loaded_segments (0x798d4 : word) = Some W_79884.
Proof. vm_refl. Qed.
Lemma D_79884 : decode_any W_79884 = Some (Load SZ8 true 13 13 2280, 4%Z).
Proof. vm_refl. Qed.

Definition W_79888 : bv 32 := 0x0006b703.
Lemma F_79888 : fetch_word Asan.M.loaded_segments (0x798d8 : word) = Some W_79888.
Proof. vm_refl. Qed.
Lemma D_79888 : decode_any W_79888 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7988c : bv 32 := 0xfffa0a13.
Lemma F_7988c : fetch_word Asan.M.loaded_segments (0x798dc : word) = Some W_7988c.
Proof. vm_refl. Qed.
Lemma D_7988c : decode_any W_7988c = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79890 : bv 32 := 0x00355693.
Lemma F_79890 : fetch_word Asan.M.loaded_segments (0x798e0 : word) = Some W_79890.
Proof. vm_refl. Qed.
Lemma D_79890 : decode_any W_79890 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79894 : bv 32 := 0x003a5793.
Lemma F_79894 : fetch_word Asan.M.loaded_segments (0x798e4 : word) = Some W_79894.
Proof. vm_refl. Qed.
Lemma D_79894 : decode_any W_79894 = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79898 : bv 32 := 0x00d706b3.
Lemma F_79898 : fetch_word Asan.M.loaded_segments (0x798e8 : word) = Some W_79898.
Proof. vm_refl. Qed.
Lemma D_79898 : decode_any W_79898 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7989c : bv 32 := 0x00f70733.
Lemma F_7989c : fetch_word Asan.M.loaded_segments (0x798ec : word) = Some W_7989c.
Proof. vm_refl. Qed.
Lemma D_7989c : decode_any W_7989c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_798a0 : bv 32 := 0xff86f793.
Lemma F_798a0 : fetch_word Asan.M.loaded_segments (0x798f0 : word) = Some W_798a0.
Proof. vm_refl. Qed.
Lemma D_798a0 : decode_any W_798a0 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_798a4 : bv 32 := 0xff877813.
Lemma F_798a4 : fetch_word Asan.M.loaded_segments (0x798f4 : word) = Some W_798a4.
Proof. vm_refl. Qed.
Lemma D_798a4 : decode_any W_798a4 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_798a8 : bv 32 := 0x0007b783.
Lemma F_798a8 : fetch_word Asan.M.loaded_segments (0x798f8 : word) = Some W_798a8.
Proof. vm_refl. Qed.
Lemma D_798a8 : decode_any W_798a8 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_798ac : bv 32 := 0x00083803.
Lemma F_798ac : fetch_word Asan.M.loaded_segments (0x798fc : word) = Some W_798ac.
Proof. vm_refl. Qed.
Lemma D_798ac : decode_any W_798ac = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_798b0 : bv 32 := 0x00f867b3.
Lemma F_798b0 : fetch_word Asan.M.loaded_segments (0x79900 : word) = Some W_798b0.
Proof. vm_refl. Qed.
Lemma D_798b0 : decode_any W_798b0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_798b4 : bv 32 := 0x36079a63.
Lemma F_798b4 : fetch_word Asan.M.loaded_segments (0x79904 : word) = Some W_798b4.
Proof. vm_refl. Qed.
Lemma D_798b4 : decode_any W_798b4 = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

Definition W_798b8 : bv 32 := 0x000c2697.
Lemma F_798b8 : fetch_word Asan.M.loaded_segments (0x79908 : word) = Some W_798b8.
Proof. vm_refl. Qed.
Lemma D_798b8 : decode_any W_798b8 = Some (Auipc 13 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_798bc : bv 32 := 0x8b86b683.
Lemma F_798bc : fetch_word Asan.M.loaded_segments (0x7990c : word) = Some W_798bc.
Proof. vm_refl. Qed.
Lemma D_798bc : decode_any W_798bc = Some (Load SZ8 true 13 13 2232, 4%Z).
Proof. vm_refl. Qed.

Definition W_798c0 : bv 32 := 0x000680e7.
Lemma F_798c0 : fetch_word Asan.M.loaded_segments (0x79910 : word) = Some W_798c0.
Proof. vm_refl. Qed.
Lemma D_798c0 : decode_any W_798c0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_798c4 : bv 32 := 0x08010113.
Lemma F_798c4 : fetch_word Asan.M.loaded_segments (0x79914 : word) = Some W_798c4.
Proof. vm_refl. Qed.
Lemma D_798c4 : decode_any W_798c4 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_798c8 : bv 32 := 0x7e813083.
Lemma F_798c8 : fetch_word Asan.M.loaded_segments (0x79918 : word) = Some W_798c8.
Proof. vm_refl. Qed.
Lemma D_798c8 : decode_any W_798c8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_798cc : bv 32 := 0x7e013403.
Lemma F_798cc : fetch_word Asan.M.loaded_segments (0x7991c : word) = Some W_798cc.
Proof. vm_refl. Qed.
Lemma D_798cc : decode_any W_798cc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_798d0 : bv 32 := 0x7d813483.
Lemma F_798d0 : fetch_word Asan.M.loaded_segments (0x79920 : word) = Some W_798d0.
Proof. vm_refl. Qed.
Lemma D_798d0 : decode_any W_798d0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_798d4 : bv 32 := 0x7d013903.
Lemma F_798d4 : fetch_word Asan.M.loaded_segments (0x79924 : word) = Some W_798d4.
Proof. vm_refl. Qed.
Lemma D_798d4 : decode_any W_798d4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_798d8 : bv 32 := 0x7c813983.
Lemma F_798d8 : fetch_word Asan.M.loaded_segments (0x79928 : word) = Some W_798d8.
Proof. vm_refl. Qed.
Lemma D_798d8 : decode_any W_798d8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_798dc : bv 32 := 0x7c013a03.
Lemma F_798dc : fetch_word Asan.M.loaded_segments (0x7992c : word) = Some W_798dc.
Proof. vm_refl. Qed.
Lemma D_798dc : decode_any W_798dc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_798e0 : bv 32 := 0x7b813a83.
Lemma F_798e0 : fetch_word Asan.M.loaded_segments (0x79930 : word) = Some W_798e0.
Proof. vm_refl. Qed.
Lemma D_798e0 : decode_any W_798e0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_798e4 : bv 32 := 0x7b013b03.
Lemma F_798e4 : fetch_word Asan.M.loaded_segments (0x79934 : word) = Some W_798e4.
Proof. vm_refl. Qed.
Lemma D_798e4 : decode_any W_798e4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_798e8 : bv 32 := 0x7a813b83.
Lemma F_798e8 : fetch_word Asan.M.loaded_segments (0x79938 : word) = Some W_798e8.
Proof. vm_refl. Qed.
Lemma D_798e8 : decode_any W_798e8 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_798ec : bv 32 := 0x7a013c03.
Lemma F_798ec : fetch_word Asan.M.loaded_segments (0x7993c : word) = Some W_798ec.
Proof. vm_refl. Qed.
Lemma D_798ec : decode_any W_798ec = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_798f0 : bv 32 := 0x7f010113.
Lemma F_798f0 : fetch_word Asan.M.loaded_segments (0x79940 : word) = Some W_798f0.
Proof. vm_refl. Qed.
Lemma D_798f0 : decode_any W_798f0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_798f4 : bv 32 := 0x00008067.
Lemma F_798f4 : fetch_word Asan.M.loaded_segments (0x79944 : word) = Some W_798f4.
Proof. vm_refl. Qed.
Lemma D_798f4 : decode_any W_798f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_799d4 : bv 32 := 0x28061463.
Lemma F_799d4 : fetch_word Asan.M.loaded_segments (0x79a24 : word) = Some W_799d4.
Proof. vm_refl. Qed.
Lemma D_799d4 : decode_any W_799d4 = Some (Branch BC_NE 12 0 648, 4%Z).
Proof. vm_refl. Qed.

Definition W_799d8 : bv 32 := 0xee1ff06f.
Lemma F_799d8 : fetch_word Asan.M.loaded_segments (0x79a28 : word) = Some W_799d8.
Proof. vm_refl. Qed.
Lemma D_799d8 : decode_any W_799d8 = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b20 : bv 32 := 0x02061e63.
Lemma F_79b20 : fetch_word Asan.M.loaded_segments (0x79b70 : word) = Some W_79b20.
Proof. vm_refl. Qed.
Lemma D_79b20 : decode_any W_79b20 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b24 : bv 32 := 0xd4dff06f.
Lemma F_79b24 : fetch_word Asan.M.loaded_segments (0x79b74 : word) = Some W_79b24.
Proof. vm_refl. Qed.
Lemma D_79b24 : decode_any W_79b24 = Some (Jal 0 2096460, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b28 : bv 32 := 0x00070783.
Lemma F_79b28 : fetch_word Asan.M.loaded_segments (0x79b78 : word) = Some W_79b28.
Proof. vm_refl. Qed.
Lemma D_79b28 : decode_any W_79b28 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b2c : bv 32 := 0x0079f813.
Lemma F_79b2c : fetch_word Asan.M.loaded_segments (0x79b7c : word) = Some W_79b2c.
Proof. vm_refl. Qed.
Lemma D_79b2c : decode_any W_79b2c = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b30 : bv 32 := 0x00f038b3.
Lemma F_79b30 : fetch_word Asan.M.loaded_segments (0x79b80 : word) = Some W_79b30.
Proof. vm_refl. Qed.
Lemma D_79b30 : decode_any W_79b30 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b34 : bv 32 := 0x00f827b3.
Lemma F_79b34 : fetch_word Asan.M.loaded_segments (0x79b84 : word) = Some W_79b34.
Proof. vm_refl. Qed.
Lemma D_79b34 : decode_any W_79b34 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b38 : bv 32 := 0x0017c793.
Lemma F_79b38 : fetch_word Asan.M.loaded_segments (0x79b88 : word) = Some W_79b38.
Proof. vm_refl. Qed.
Lemma D_79b38 : decode_any W_79b38 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b3c : bv 32 := 0x00f8f7b3.
Lemma F_79b3c : fetch_word Asan.M.loaded_segments (0x79b8c : word) = Some W_79b3c.
Proof. vm_refl. Qed.
Lemma D_79b3c : decode_any W_79b3c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b40 : bv 32 := 0x00e6fa63.
Lemma F_79b40 : fetch_word Asan.M.loaded_segments (0x79b90 : word) = Some W_79b40.
Proof. vm_refl. Qed.
Lemma D_79b40 : decode_any W_79b40 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b44 : bv 32 := 0x0006c803.
Lemma F_79b44 : fetch_word Asan.M.loaded_segments (0x79b94 : word) = Some W_79b44.
Proof. vm_refl. Qed.
Lemma D_79b44 : decode_any W_79b44 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b48 : bv 32 := 0x00168693.
Lemma F_79b48 : fetch_word Asan.M.loaded_segments (0x79b98 : word) = Some W_79b48.
Proof. vm_refl. Qed.
Lemma D_79b48 : decode_any W_79b48 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b4c : bv 32 := 0x00f867b3.
Lemma F_79b4c : fetch_word Asan.M.loaded_segments (0x79b9c : word) = Some W_79b4c.
Proof. vm_refl. Qed.
Lemma D_79b4c : decode_any W_79b4c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b50 : bv 32 := 0xfee69ae3.
Lemma F_79b50 : fetch_word Asan.M.loaded_segments (0x79ba0 : word) = Some W_79b50.
Proof. vm_refl. Qed.
Lemma D_79b50 : decode_any W_79b50 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b54 : bv 32 := 0x0ff7f693.
Lemma F_79b54 : fetch_word Asan.M.loaded_segments (0x79ba4 : word) = Some W_79b54.
Proof. vm_refl. Qed.
Lemma D_79b54 : decode_any W_79b54 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b58 : bv 32 := 0xd0068ce3.
Lemma F_79b58 : fetch_word Asan.M.loaded_segments (0x79ba8 : word) = Some W_79b58.
Proof. vm_refl. Qed.
Lemma D_79b58 : decode_any W_79b58 = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b5c : bv 32 := 0x00050b93.
Lemma F_79b5c : fetch_word Asan.M.loaded_segments (0x79bac : word) = Some W_79b5c.
Proof. vm_refl. Qed.
Lemma D_79b5c : decode_any W_79b5c = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b60 : bv 32 := 0x00058513.
Lemma F_79b60 : fetch_word Asan.M.loaded_segments (0x79bb0 : word) = Some W_79b60.
Proof. vm_refl. Qed.
Lemma D_79b60 : decode_any W_79b60 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b64 : bv 32 := 0x00058c13.
Lemma F_79b64 : fetch_word Asan.M.loaded_segments (0x79bb4 : word) = Some W_79b64.
Proof. vm_refl. Qed.
Lemma D_79b64 : decode_any W_79b64 = Some (OpImm ALU_ADD 24 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b68 : bv 32 := 0x00060593.
Lemma F_79b68 : fetch_word Asan.M.loaded_segments (0x79bb8 : word) = Some W_79b68.
Proof. vm_refl. Qed.
Lemma D_79b68 : decode_any W_79b68 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b6c : bv 32 := 0x00060493.
Lemma F_79b6c : fetch_word Asan.M.loaded_segments (0x79bbc : word) = Some W_79b6c.
Proof. vm_refl. Qed.
Lemma D_79b6c : decode_any W_79b6c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b70 : bv 32 := 0x284020ef.
Lemma F_79b70 : fetch_word Asan.M.loaded_segments (0x79bc0 : word) = Some W_79b70.
Proof. vm_refl. Qed.
Lemma D_79b70 : decode_any W_79b70 = Some (Jal 1 8836, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b74 : bv 32 := 0x000c0593.
Lemma F_79b74 : fetch_word Asan.M.loaded_segments (0x79bc4 : word) = Some W_79b74.
Proof. vm_refl. Qed.
Lemma D_79b74 : decode_any W_79b74 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b78 : bv 32 := 0x00048613.
Lemma F_79b78 : fetch_word Asan.M.loaded_segments (0x79bc8 : word) = Some W_79b78.
Proof. vm_refl. Qed.
Lemma D_79b78 : decode_any W_79b78 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b7c : bv 32 := 0x00050913.
Lemma F_79b7c : fetch_word Asan.M.loaded_segments (0x79bcc : word) = Some W_79b7c.
Proof. vm_refl. Qed.
Lemma D_79b7c : decode_any W_79b7c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b80 : bv 32 := 0x000b8513.
Lemma F_79b80 : fetch_word Asan.M.loaded_segments (0x79bd0 : word) = Some W_79b80.
Proof. vm_refl. Qed.
Lemma D_79b80 : decode_any W_79b80 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b84 : bv 32 := 0xce0906e3.
Lemma F_79b84 : fetch_word Asan.M.loaded_segments (0x79bd4 : word) = Some W_79b84.
Proof. vm_refl. Qed.
Lemma D_79b84 : decode_any W_79b84 = Some (Branch BC_EQ 18 0 7404, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c28 : bv 32 := 0x00070783.
Lemma F_79c28 : fetch_word Asan.M.loaded_segments (0x79c78 : word) = Some W_79c28.
Proof. vm_refl. Qed.
Lemma D_79c28 : decode_any W_79c28 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c2c : bv 32 := 0x007a7813.
Lemma F_79c2c : fetch_word Asan.M.loaded_segments (0x79c7c : word) = Some W_79c2c.
Proof. vm_refl. Qed.
Lemma D_79c2c : decode_any W_79c2c = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c30 : bv 32 := 0x00f038b3.
Lemma F_79c30 : fetch_word Asan.M.loaded_segments (0x79c80 : word) = Some W_79c30.
Proof. vm_refl. Qed.
Lemma D_79c30 : decode_any W_79c30 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c34 : bv 32 := 0x00f827b3.
Lemma F_79c34 : fetch_word Asan.M.loaded_segments (0x79c84 : word) = Some W_79c34.
Proof. vm_refl. Qed.
Lemma D_79c34 : decode_any W_79c34 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c38 : bv 32 := 0x0017c793.
Lemma F_79c38 : fetch_word Asan.M.loaded_segments (0x79c88 : word) = Some W_79c38.
Proof. vm_refl. Qed.
Lemma D_79c38 : decode_any W_79c38 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c3c : bv 32 := 0x00f8f7b3.
Lemma F_79c3c : fetch_word Asan.M.loaded_segments (0x79c8c : word) = Some W_79c3c.
Proof. vm_refl. Qed.
Lemma D_79c3c : decode_any W_79c3c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c40 : bv 32 := 0x00e6fa63.
Lemma F_79c40 : fetch_word Asan.M.loaded_segments (0x79c90 : word) = Some W_79c40.
Proof. vm_refl. Qed.
Lemma D_79c40 : decode_any W_79c40 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c44 : bv 32 := 0x0006c803.
Lemma F_79c44 : fetch_word Asan.M.loaded_segments (0x79c94 : word) = Some W_79c44.
Proof. vm_refl. Qed.
Lemma D_79c44 : decode_any W_79c44 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c48 : bv 32 := 0x00168693.
Lemma F_79c48 : fetch_word Asan.M.loaded_segments (0x79c98 : word) = Some W_79c48.
Proof. vm_refl. Qed.
Lemma D_79c48 : decode_any W_79c48 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c4c : bv 32 := 0x00f867b3.
Lemma F_79c4c : fetch_word Asan.M.loaded_segments (0x79c9c : word) = Some W_79c4c.
Proof. vm_refl. Qed.
Lemma D_79c4c : decode_any W_79c4c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c50 : bv 32 := 0xfee69ae3.
Lemma F_79c50 : fetch_word Asan.M.loaded_segments (0x79ca0 : word) = Some W_79c50.
Proof. vm_refl. Qed.
Lemma D_79c50 : decode_any W_79c50 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c54 : bv 32 := 0x0ff7f693.
Lemma F_79c54 : fetch_word Asan.M.loaded_segments (0x79ca4 : word) = Some W_79c54.
Proof. vm_refl. Qed.
Lemma D_79c54 : decode_any W_79c54 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c58 : bv 32 := 0xc60680e3.
Lemma F_79c58 : fetch_word Asan.M.loaded_segments (0x79ca8 : word) = Some W_79c58.
Proof. vm_refl. Qed.
Lemma D_79c58 : decode_any W_79c58 = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c5c : bv 32 := 0x00050493.
Lemma F_79c5c : fetch_word Asan.M.loaded_segments (0x79cac : word) = Some W_79c5c.
Proof. vm_refl. Qed.
Lemma D_79c5c : decode_any W_79c5c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c60 : bv 32 := 0x00058b13.
Lemma F_79c60 : fetch_word Asan.M.loaded_segments (0x79cb0 : word) = Some W_79c60.
Proof. vm_refl. Qed.
Lemma D_79c60 : decode_any W_79c60 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c64 : bv 32 := 0x00060593.
Lemma F_79c64 : fetch_word Asan.M.loaded_segments (0x79cb4 : word) = Some W_79c64.
Proof. vm_refl. Qed.
Lemma D_79c64 : decode_any W_79c64 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c68 : bv 32 := 0x00060913.
Lemma F_79c68 : fetch_word Asan.M.loaded_segments (0x79cb8 : word) = Some W_79c68.
Proof. vm_refl. Qed.
Lemma D_79c68 : decode_any W_79c68 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c6c : bv 32 := 0x188020ef.
Lemma F_79c6c : fetch_word Asan.M.loaded_segments (0x79cbc : word) = Some W_79c6c.
Proof. vm_refl. Qed.
Lemma D_79c6c : decode_any W_79c6c = Some (Jal 1 8584, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c70 : bv 32 := 0x000b0593.
Lemma F_79c70 : fetch_word Asan.M.loaded_segments (0x79cc0 : word) = Some W_79c70.
Proof. vm_refl. Qed.
Lemma D_79c70 : decode_any W_79c70 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c74 : bv 32 := 0x00090613.
Lemma F_79c74 : fetch_word Asan.M.loaded_segments (0x79cc4 : word) = Some W_79c74.
Proof. vm_refl. Qed.
Lemma D_79c74 : decode_any W_79c74 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c78 : bv 32 := 0x00050993.
Lemma F_79c78 : fetch_word Asan.M.loaded_segments (0x79cc8 : word) = Some W_79c78.
Proof. vm_refl. Qed.
Lemma D_79c78 : decode_any W_79c78 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c7c : bv 32 := 0x00048513.
Lemma F_79c7c : fetch_word Asan.M.loaded_segments (0x79ccc : word) = Some W_79c7c.
Proof. vm_refl. Qed.
Lemma D_79c7c : decode_any W_79c7c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c80 : bv 32 := 0xc2098ce3.
Lemma F_79c80 : fetch_word Asan.M.loaded_segments (0x79cd0 : word) = Some W_79c80.
Proof. vm_refl. Qed.
Lemma D_79c80 : decode_any W_79c80 = Some (Branch BC_EQ 19 0 7224, 4%Z).
Proof. vm_refl. Qed.
