(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_80588 : bv 32 := 0xfd010113.
Lemma F_80588 : fetch_word Asan.M.loaded_segments (0x80588 : word) = Some W_80588.
Proof. vm_refl. Qed.
Lemma D_80588 : decode_any W_80588 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_8058c : bv 32 := 0x02113423.
Lemma F_8058c : fetch_word Asan.M.loaded_segments (0x8058c : word) = Some W_8058c.
Proof. vm_refl. Qed.
Lemma D_8058c : decode_any W_8058c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80590 : bv 32 := 0x02813023.
Lemma F_80590 : fetch_word Asan.M.loaded_segments (0x80590 : word) = Some W_80590.
Proof. vm_refl. Qed.
Lemma D_80590 : decode_any W_80590 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80594 : bv 32 := 0x00913c23.
Lemma F_80594 : fetch_word Asan.M.loaded_segments (0x80594 : word) = Some W_80594.
Proof. vm_refl. Qed.
Lemma D_80594 : decode_any W_80594 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80598 : bv 32 := 0x01213823.
Lemma F_80598 : fetch_word Asan.M.loaded_segments (0x80598 : word) = Some W_80598.
Proof. vm_refl. Qed.
Lemma D_80598 : decode_any W_80598 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8059c : bv 32 := 0x01313423.
Lemma F_8059c : fetch_word Asan.M.loaded_segments (0x8059c : word) = Some W_8059c.
Proof. vm_refl. Qed.
Lemma D_8059c : decode_any W_8059c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_805a0 : bv 32 := 0x02059593.
Lemma F_805a0 : fetch_word Asan.M.loaded_segments (0x805a0 : word) = Some W_805a0.
Proof. vm_refl. Qed.
Lemma D_805a0 : decode_any W_805a0 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_805a4 : bv 32 := 0x00400637.
Lemma F_805a4 : fetch_word Asan.M.loaded_segments (0x805a4 : word) = Some W_805a4.
Proof. vm_refl. Qed.
Lemma D_805a4 : decode_any W_805a4 = Some (Lui 12 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_805a8 : bv 32 := 0x0205d593.
Lemma F_805a8 : fetch_word Asan.M.loaded_segments (0x805a8 : word) = Some W_805a8.
Proof. vm_refl. Qed.
Lemma D_805a8 : decode_any W_805a8 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_805ac : bv 32 := 0x0106049b.
Lemma F_805ac : fetch_word Asan.M.loaded_segments (0x805ac : word) = Some W_805ac.
Proof. vm_refl. Qed.
Lemma D_805ac : decode_any W_805ac = Some (OpImm32 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_805b0 : bv 32 := 0x0086061b.
Lemma F_805b0 : fetch_word Asan.M.loaded_segments (0x805b0 : word) = Some W_805b0.
Proof. vm_refl. Qed.
Lemma D_805b0 : decode_any W_805b0 = Some (OpImm32 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_805b4 : bv 32 := 0x009504b3.
Lemma F_805b4 : fetch_word Asan.M.loaded_segments (0x805b4 : word) = Some W_805b4.
Proof. vm_refl. Qed.
Lemma D_805b4 : decode_any W_805b4 = Some (Op ALU_ADD 9 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_805b8 : bv 32 := 0x00c50433.
Lemma F_805b8 : fetch_word Asan.M.loaded_segments (0x805b8 : word) = Some W_805b8.
Proof. vm_refl. Qed.
Lemma D_805b8 : decode_any W_805b8 = Some (Op ALU_ADD 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_805bc : bv 32 := 0x00058913.
Lemma F_805bc : fetch_word Asan.M.loaded_segments (0x805bc : word) = Some W_805bc.
Proof. vm_refl. Qed.
Lemma D_805bc : decode_any W_805bc = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_805c0 : bv 32 := 0x04058e63.
Lemma F_805c0 : fetch_word Asan.M.loaded_segments (0x805c0 : word) = Some W_805c0.
Proof. vm_refl. Qed.
Lemma D_805c0 : decode_any W_805c0 = Some (Branch BC_EQ 11 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_805c4 : bv 32 := 0x01095593.
Lemma F_805c4 : fetch_word Asan.M.loaded_segments (0x805c4 : word) = Some W_805c4.
Proof. vm_refl. Qed.
Lemma D_805c4 : decode_any W_805c4 = Some (ShiftImm ALU_SRL 11 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_805c8 : bv 32 := 0x00359513.
Lemma F_805c8 : fetch_word Asan.M.loaded_segments (0x805c8 : word) = Some W_805c8.
Proof. vm_refl. Qed.
Lemma D_805c8 : decode_any W_805c8 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_805cc : bv 32 := 0x00a48533.
Lemma F_805cc : fetch_word Asan.M.loaded_segments (0x805cc : word) = Some W_805cc.
Proof. vm_refl. Qed.
Lemma D_805cc : decode_any W_805cc = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_805d0 : bv 32 := 0x00053503.
Lemma F_805d0 : fetch_word Asan.M.loaded_segments (0x805d0 : word) = Some W_805d0.
Proof. vm_refl. Qed.
Lemma D_805d0 : decode_any W_805d0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_805d4 : bv 32 := 0x02050063.
Lemma F_805d4 : fetch_word Asan.M.loaded_segments (0x805d4 : word) = Some W_805d4.
Proof. vm_refl. Qed.
Lemma D_805d4 : decode_any W_805d4 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_805d8 : bv 32 := 0x03091593.
Lemma F_805d8 : fetch_word Asan.M.loaded_segments (0x805d8 : word) = Some W_805d8.
Proof. vm_refl. Qed.
Lemma D_805d8 : decode_any W_805d8 = Some (ShiftImm ALU_SLL 11 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_805dc : bv 32 := 0x02c5d593.
Lemma F_805dc : fetch_word Asan.M.loaded_segments (0x805dc : word) = Some W_805dc.
Proof. vm_refl. Qed.
Lemma D_805dc : decode_any W_805dc = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_805e0 : bv 32 := 0x00b50533.
Lemma F_805e0 : fetch_word Asan.M.loaded_segments (0x805e0 : word) = Some W_805e0.
Proof. vm_refl. Qed.
Lemma D_805e0 : decode_any W_805e0 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_805e4 : bv 32 := 0x00053603.
Lemma F_805e4 : fetch_word Asan.M.loaded_segments (0x805e4 : word) = Some W_805e4.
Proof. vm_refl. Qed.
Lemma D_805e4 : decode_any W_805e4 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_805e8 : bv 32 := 0x00856583.
Lemma F_805e8 : fetch_word Asan.M.loaded_segments (0x805e8 : word) = Some W_805e8.
Proof. vm_refl. Qed.
Lemma D_805e8 : decode_any W_805e8 = Some (Load SZ4 false 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_805ec : bv 32 := 0xfcc718e3.
Lemma F_805ec : fetch_word Asan.M.loaded_segments (0x805ec : word) = Some W_805ec.
Proof. vm_refl. Qed.
Lemma D_805ec : decode_any W_805ec = Some (Branch BC_NE 14 12 8144, 4%Z).
Proof. vm_refl. Qed.

Definition W_805f0 : bv 32 := 0x02c0006f.
Lemma F_805f0 : fetch_word Asan.M.loaded_segments (0x805f0 : word) = Some W_805f0.
Proof. vm_refl. Qed.
Lemma D_805f0 : decode_any W_805f0 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_805f4 : bv 32 := 0x00040513.
Lemma F_805f4 : fetch_word Asan.M.loaded_segments (0x805f4 : word) = Some W_805f4.
Proof. vm_refl. Qed.
Lemma D_805f4 : decode_any W_805f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_805f8 : bv 32 := 0x00070993.
Lemma F_805f8 : fetch_word Asan.M.loaded_segments (0x805f8 : word) = Some W_805f8.
Proof. vm_refl. Qed.
Lemma D_805f8 : decode_any W_805f8 = Some (OpImm ALU_ADD 19 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_805fc : bv 32 := 0x0d0000ef.
Lemma F_805fc : fetch_word Asan.M.loaded_segments (0x805fc : word) = Some W_805fc.
Proof. vm_refl. Qed.
Lemma D_805fc : decode_any W_805fc = Some (Jal 1 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_80600 : bv 32 := 0x00098713.
Lemma F_80600 : fetch_word Asan.M.loaded_segments (0x80600 : word) = Some W_80600.
Proof. vm_refl. Qed.
Lemma D_80600 : decode_any W_80600 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80604 : bv 32 := 0x03091593.
Lemma F_80604 : fetch_word Asan.M.loaded_segments (0x80604 : word) = Some W_80604.
Proof. vm_refl. Qed.
Lemma D_80604 : decode_any W_80604 = Some (ShiftImm ALU_SLL 11 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80608 : bv 32 := 0x02c5d593.
Lemma F_80608 : fetch_word Asan.M.loaded_segments (0x80608 : word) = Some W_80608.
Proof. vm_refl. Qed.
Lemma D_80608 : decode_any W_80608 = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8060c : bv 32 := 0x00b50533.
Lemma F_8060c : fetch_word Asan.M.loaded_segments (0x8060c : word) = Some W_8060c.
Proof. vm_refl. Qed.
Lemma D_8060c : decode_any W_8060c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80610 : bv 32 := 0x00053603.
Lemma F_80610 : fetch_word Asan.M.loaded_segments (0x80610 : word) = Some W_80610.
Proof. vm_refl. Qed.
Lemma D_80610 : decode_any W_80610 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80614 : bv 32 := 0x00856583.
Lemma F_80614 : fetch_word Asan.M.loaded_segments (0x80614 : word) = Some W_80614.
Proof. vm_refl. Qed.
Lemma D_80614 : decode_any W_80614 = Some (Load SZ4 false 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80618 : bv 32 := 0xfac992e3.
Lemma F_80618 : fetch_word Asan.M.loaded_segments (0x80618 : word) = Some W_80618.
Proof. vm_refl. Qed.
Lemma D_80618 : decode_any W_80618 = Some (Branch BC_NE 19 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_8061c : bv 32 := 0x0009051b.
Lemma F_8061c : fetch_word Asan.M.loaded_segments (0x8061c : word) = Some W_8061c.
Proof. vm_refl. Qed.
Lemma D_8061c : decode_any W_8061c = Some (OpImm32 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80620 : bv 32 := 0x02813083.
Lemma F_80620 : fetch_word Asan.M.loaded_segments (0x80620 : word) = Some W_80620.
Proof. vm_refl. Qed.
Lemma D_80620 : decode_any W_80620 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80624 : bv 32 := 0x02013403.
Lemma F_80624 : fetch_word Asan.M.loaded_segments (0x80624 : word) = Some W_80624.
Proof. vm_refl. Qed.
Lemma D_80624 : decode_any W_80624 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80628 : bv 32 := 0x01813483.
Lemma F_80628 : fetch_word Asan.M.loaded_segments (0x80628 : word) = Some W_80628.
Proof. vm_refl. Qed.
Lemma D_80628 : decode_any W_80628 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8062c : bv 32 := 0x01013903.
Lemma F_8062c : fetch_word Asan.M.loaded_segments (0x8062c : word) = Some W_8062c.
Proof. vm_refl. Qed.
Lemma D_8062c : decode_any W_8062c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80630 : bv 32 := 0x00813983.
Lemma F_80630 : fetch_word Asan.M.loaded_segments (0x80630 : word) = Some W_80630.
Proof. vm_refl. Qed.
Lemma D_80630 : decode_any W_80630 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80634 : bv 32 := 0x03010113.
Lemma F_80634 : fetch_word Asan.M.loaded_segments (0x80634 : word) = Some W_80634.
Proof. vm_refl. Qed.
Lemma D_80634 : decode_any W_80634 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80638 : bv 32 := 0x00008067.
Lemma F_80638 : fetch_word Asan.M.loaded_segments (0x80638 : word) = Some W_80638.
Proof. vm_refl. Qed.
Lemma D_80638 : decode_any W_80638 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8063c : bv 32 := 0xfd010113.
Lemma F_8063c : fetch_word Asan.M.loaded_segments (0x8063c : word) = Some W_8063c.
Proof. vm_refl. Qed.
Lemma D_8063c : decode_any W_8063c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80640 : bv 32 := 0x02113423.
Lemma F_80640 : fetch_word Asan.M.loaded_segments (0x80640 : word) = Some W_80640.
Proof. vm_refl. Qed.
Lemma D_80640 : decode_any W_80640 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80644 : bv 32 := 0x02813023.
Lemma F_80644 : fetch_word Asan.M.loaded_segments (0x80644 : word) = Some W_80644.
Proof. vm_refl. Qed.
Lemma D_80644 : decode_any W_80644 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80648 : bv 32 := 0x00913c23.
Lemma F_80648 : fetch_word Asan.M.loaded_segments (0x80648 : word) = Some W_80648.
Proof. vm_refl. Qed.
Lemma D_80648 : decode_any W_80648 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8064c : bv 32 := 0x01213823.
Lemma F_8064c : fetch_word Asan.M.loaded_segments (0x8064c : word) = Some W_8064c.
Proof. vm_refl. Qed.
Lemma D_8064c : decode_any W_8064c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80650 : bv 32 := 0x01313423.
Lemma F_80650 : fetch_word Asan.M.loaded_segments (0x80650 : word) = Some W_80650.
Proof. vm_refl. Qed.
Lemma D_80650 : decode_any W_80650 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80654 : bv 32 := 0x00050413.
Lemma F_80654 : fetch_word Asan.M.loaded_segments (0x80654 : word) = Some W_80654.
Proof. vm_refl. Qed.
Lemma D_80654 : decode_any W_80654 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80658 : bv 32 := 0x00000593.
Lemma F_80658 : fetch_word Asan.M.loaded_segments (0x80658 : word) = Some W_80658.
Proof. vm_refl. Qed.
Lemma D_80658 : decode_any W_80658 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8065c : bv 32 := 0x800004b7.
Lemma F_8065c : fetch_word Asan.M.loaded_segments (0x8065c : word) = Some W_8065c.
Proof. vm_refl. Qed.
Lemma D_8065c : decode_any W_8065c = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_80660 : bv 32 := 0x00900913.
Lemma F_80660 : fetch_word Asan.M.loaded_segments (0x80660 : word) = Some W_80660.
Proof. vm_refl. Qed.
Lemma D_80660 : decode_any W_80660 = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80664 : bv 32 := 0x00052503.
Lemma F_80664 : fetch_word Asan.M.loaded_segments (0x80664 : word) = Some W_80664.
Proof. vm_refl. Qed.
Lemma D_80664 : decode_any W_80664 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80668 : bv 32 := 0x00055a63.
Lemma F_80668 : fetch_word Asan.M.loaded_segments (0x80668 : word) = Some W_80668.
Proof. vm_refl. Qed.
Lemma D_80668 : decode_any W_80668 = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8066c : bv 32 := 0x0280006f.
Lemma F_8066c : fetch_word Asan.M.loaded_segments (0x8066c : word) = Some W_8066c.
Proof. vm_refl. Qed.
Lemma D_8066c : decode_any W_8066c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80670 : bv 32 := 0x00098593.
Lemma F_80670 : fetch_word Asan.M.loaded_segments (0x80670 : word) = Some W_80670.
Proof. vm_refl. Qed.
Lemma D_80670 : decode_any W_80670 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80674 : bv 32 := 0x00042503.
Lemma F_80674 : fetch_word Asan.M.loaded_segments (0x80674 : word) = Some W_80674.
Proof. vm_refl. Qed.
Lemma D_80674 : decode_any W_80674 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80678 : bv 32 := 0x00054e63.
Lemma F_80678 : fetch_word Asan.M.loaded_segments (0x80678 : word) = Some W_80678.
Proof. vm_refl. Qed.
Lemma D_80678 : decode_any W_80678 = Some (Branch BC_LT 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8067c : bv 32 := 0x00956633.
Lemma F_8067c : fetch_word Asan.M.loaded_segments (0x8067c : word) = Some W_8067c.
Proof. vm_refl. Qed.
Lemma D_8067c : decode_any W_8067c = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80680 : bv 32 := 0x160426af.
Lemma F_80680 : fetch_word Asan.M.loaded_segments (0x80680 : word) = Some W_80680.
Proof. vm_refl. Qed.
Lemma D_80680 : decode_any W_80680 = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80684 : bv 32 := 0x00a69663.
Lemma F_80684 : fetch_word Asan.M.loaded_segments (0x80684 : word) = Some W_80684.
Proof. vm_refl. Qed.
Lemma D_80684 : decode_any W_80684 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80688 : bv 32 := 0x1ac4272f.
Lemma F_80688 : fetch_word Asan.M.loaded_segments (0x80688 : word) = Some W_80688.
Proof. vm_refl. Qed.
Lemma D_80688 : decode_any W_80688 = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8068c : bv 32 := 0xfe071ae3.
Lemma F_8068c : fetch_word Asan.M.loaded_segments (0x8068c : word) = Some W_8068c.
Proof. vm_refl. Qed.
Lemma D_8068c : decode_any W_8068c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_80690 : bv 32 := 0x02a68063.
Lemma F_80690 : fetch_word Asan.M.loaded_segments (0x80690 : word) = Some W_80690.
Proof. vm_refl. Qed.
Lemma D_80690 : decode_any W_80690 = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80694 : bv 32 := 0x0015899b.
Lemma F_80694 : fetch_word Asan.M.loaded_segments (0x80694 : word) = Some W_80694.
Proof. vm_refl. Qed.
Lemma D_80694 : decode_any W_80694 = Some (OpImm32 19 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80698 : bv 32 := 0xfcb97ce3.
Lemma F_80698 : fetch_word Asan.M.loaded_segments (0x80698 : word) = Some W_80698.
Proof. vm_refl. Qed.
Lemma D_80698 : decode_any W_80698 = Some (Branch BC_GEU 18 11 8152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8069c : bv 32 := 0xe24f10ef.
Lemma F_8069c : fetch_word Asan.M.loaded_segments (0x8069c : word) = Some W_8069c.
Proof. vm_refl. Qed.
Lemma D_8069c : decode_any W_8069c = Some (Jal 1 2037284, 4%Z).
Proof. vm_refl. Qed.

Definition W_806a0 : bv 32 := 0x00098593.
Lemma F_806a0 : fetch_word Asan.M.loaded_segments (0x806a0 : word) = Some W_806a0.
Proof. vm_refl. Qed.
Lemma D_806a0 : decode_any W_806a0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806a4 : bv 32 := 0x00042503.
Lemma F_806a4 : fetch_word Asan.M.loaded_segments (0x806a4 : word) = Some W_806a4.
Proof. vm_refl. Qed.
Lemma D_806a4 : decode_any W_806a4 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806a8 : bv 32 := 0xfc055ae3.
Lemma F_806a8 : fetch_word Asan.M.loaded_segments (0x806a8 : word) = Some W_806a8.
Proof. vm_refl. Qed.
Lemma D_806a8 : decode_any W_806a8 = Some (Branch BC_GE 10 0 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_806ac : bv 32 := 0xfe9ff06f.
Lemma F_806ac : fetch_word Asan.M.loaded_segments (0x806ac : word) = Some W_806ac.
Proof. vm_refl. Qed.
Lemma D_806ac : decode_any W_806ac = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

Definition W_806b0 : bv 32 := 0x02813083.
Lemma F_806b0 : fetch_word Asan.M.loaded_segments (0x806b0 : word) = Some W_806b0.
Proof. vm_refl. Qed.
Lemma D_806b0 : decode_any W_806b0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_806b4 : bv 32 := 0x02013403.
Lemma F_806b4 : fetch_word Asan.M.loaded_segments (0x806b4 : word) = Some W_806b4.
Proof. vm_refl. Qed.
Lemma D_806b4 : decode_any W_806b4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_806b8 : bv 32 := 0x01813483.
Lemma F_806b8 : fetch_word Asan.M.loaded_segments (0x806b8 : word) = Some W_806b8.
Proof. vm_refl. Qed.
Lemma D_806b8 : decode_any W_806b8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_806bc : bv 32 := 0x01013903.
Lemma F_806bc : fetch_word Asan.M.loaded_segments (0x806bc : word) = Some W_806bc.
Proof. vm_refl. Qed.
Lemma D_806bc : decode_any W_806bc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_806c0 : bv 32 := 0x00813983.
Lemma F_806c0 : fetch_word Asan.M.loaded_segments (0x806c0 : word) = Some W_806c0.
Proof. vm_refl. Qed.
Lemma D_806c0 : decode_any W_806c0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_806c4 : bv 32 := 0x03010113.
Lemma F_806c4 : fetch_word Asan.M.loaded_segments (0x806c4 : word) = Some W_806c4.
Proof. vm_refl. Qed.
Lemma D_806c4 : decode_any W_806c4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_806c8 : bv 32 := 0x00008067.
Lemma F_806c8 : fetch_word Asan.M.loaded_segments (0x806c8 : word) = Some W_806c8.
Proof. vm_refl. Qed.
Lemma D_806c8 : decode_any W_806c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
