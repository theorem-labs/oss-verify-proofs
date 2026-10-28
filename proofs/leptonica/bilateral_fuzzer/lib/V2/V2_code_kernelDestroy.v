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

Definition W_38570 : bv 32 := 0xfd010113.
Lemma F_38570 : fetch_word Ubsan.M.loaded_segments (0x38570 : word) = Some W_38570.
Proof. vm_refl. Qed.
Lemma D_38570 : decode_any W_38570 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_38574 : bv 32 := 0x02113423.
Lemma F_38574 : fetch_word Ubsan.M.loaded_segments (0x38574 : word) = Some W_38574.
Proof. vm_refl. Qed.
Lemma D_38574 : decode_any W_38574 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_38578 : bv 32 := 0x02813023.
Lemma F_38578 : fetch_word Ubsan.M.loaded_segments (0x38578 : word) = Some W_38578.
Proof. vm_refl. Qed.
Lemma D_38578 : decode_any W_38578 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3857c : bv 32 := 0x00913c23.
Lemma F_3857c : fetch_word Ubsan.M.loaded_segments (0x3857c : word) = Some W_3857c.
Proof. vm_refl. Qed.
Lemma D_3857c : decode_any W_3857c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38580 : bv 32 := 0x01213823.
Lemma F_38580 : fetch_word Ubsan.M.loaded_segments (0x38580 : word) = Some W_38580.
Proof. vm_refl. Qed.
Lemma D_38580 : decode_any W_38580 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38584 : bv 32 := 0x01313423.
Lemma F_38584 : fetch_word Ubsan.M.loaded_segments (0x38584 : word) = Some W_38584.
Proof. vm_refl. Qed.
Lemma D_38584 : decode_any W_38584 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38588 : bv 32 := 0x08050663.
Lemma F_38588 : fetch_word Ubsan.M.loaded_segments (0x38588 : word) = Some W_38588.
Proof. vm_refl. Qed.
Lemma D_38588 : decode_any W_38588 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_3858c : bv 32 := 0x00050413.
Lemma F_3858c : fetch_word Ubsan.M.loaded_segments (0x3858c : word) = Some W_3858c.
Proof. vm_refl. Qed.
Lemma D_3858c : decode_any W_3858c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38590 : bv 32 := 0x00757513.
Lemma F_38590 : fetch_word Ubsan.M.loaded_segments (0x38590 : word) = Some W_38590.
Proof. vm_refl. Qed.
Lemma D_38590 : decode_any W_38590 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_38594 : bv 32 := 0x0c051e63.
Lemma F_38594 : fetch_word Ubsan.M.loaded_segments (0x38594 : word) = Some W_38594.
Proof. vm_refl. Qed.
Lemma D_38594 : decode_any W_38594 = Some (Branch BC_NE 10 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_38598 : bv 32 := 0x00043483.
Lemma F_38598 : fetch_word Ubsan.M.loaded_segments (0x38598 : word) = Some W_38598.
Proof. vm_refl. Qed.
Lemma D_38598 : decode_any W_38598 = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3859c : bv 32 := 0x0a048c63.
Lemma F_3859c : fetch_word Ubsan.M.loaded_segments (0x3859c : word) = Some W_3859c.
Proof. vm_refl. Qed.
Lemma D_3859c : decode_any W_3859c = Some (Branch BC_EQ 9 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_385a0 : bv 32 := 0x0074f513.
Lemma F_385a0 : fetch_word Ubsan.M.loaded_segments (0x385a0 : word) = Some W_385a0.
Proof. vm_refl. Qed.
Lemma D_385a0 : decode_any W_385a0 = Some (OpImm ALU_AND 10 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_385a4 : bv 32 := 0x0c051663.
Lemma F_385a4 : fetch_word Ubsan.M.loaded_segments (0x385a4 : word) = Some W_385a4.
Proof. vm_refl. Qed.
Lemma D_385a4 : decode_any W_385a4 = Some (Branch BC_NE 10 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_385a8 : bv 32 := 0x0004a503.
Lemma F_385a8 : fetch_word Ubsan.M.loaded_segments (0x385a8 : word) = Some W_385a8.
Proof. vm_refl. Qed.
Lemma D_385a8 : decode_any W_385a8 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_385ac : bv 32 := 0x04a05863.
Lemma F_385ac : fetch_word Ubsan.M.loaded_segments (0x385ac : word) = Some W_385ac.
Proof. vm_refl. Qed.
Lemma D_385ac : decode_any W_385ac = Some (Branch BC_GE 0 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_385b0 : bv 32 := 0x00000913.
Lemma F_385b0 : fetch_word Ubsan.M.loaded_segments (0x385b0 : word) = Some W_385b0.
Proof. vm_refl. Qed.
Lemma D_385b0 : decode_any W_385b0 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_385b4 : bv 32 := 0x00000993.
Lemma F_385b4 : fetch_word Ubsan.M.loaded_segments (0x385b4 : word) = Some W_385b4.
Proof. vm_refl. Qed.
Lemma D_385b4 : decode_any W_385b4 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_385b8 : bv 32 := 0x0104b583.
Lemma F_385b8 : fetch_word Ubsan.M.loaded_segments (0x385b8 : word) = Some W_385b8.
Proof. vm_refl. Qed.
Lemma D_385b8 : decode_any W_385b8 = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_385bc : bv 32 := 0x01258533.
Lemma F_385bc : fetch_word Ubsan.M.loaded_segments (0x385bc : word) = Some W_385bc.
Proof. vm_refl. Qed.
Lemma D_385bc : decode_any W_385bc = Some (Op ALU_ADD 10 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_385c0 : bv 32 := 0x0ab56863.
Lemma F_385c0 : fetch_word Ubsan.M.loaded_segments (0x385c0 : word) = Some W_385c0.
Proof. vm_refl. Qed.
Lemma D_385c0 : decode_any W_385c0 = Some (Branch BC_LTU 10 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_385c4 : bv 32 := 0x00b03633.
Lemma F_385c4 : fetch_word Ubsan.M.loaded_segments (0x385c4 : word) = Some W_385c4.
Proof. vm_refl. Qed.
Lemma D_385c4 : decode_any W_385c4 = Some (Op ALU_SLTU 12 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_385c8 : bv 32 := 0x00153693.
Lemma F_385c8 : fetch_word Ubsan.M.loaded_segments (0x385c8 : word) = Some W_385c8.
Proof. vm_refl. Qed.
Lemma D_385c8 : decode_any W_385c8 = Some (OpImm ALU_SLTU 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_385cc : bv 32 := 0x00d64633.
Lemma F_385cc : fetch_word Ubsan.M.loaded_segments (0x385cc : word) = Some W_385cc.
Proof. vm_refl. Qed.
Lemma D_385cc : decode_any W_385cc = Some (Op ALU_XOR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_385d0 : bv 32 := 0x0a060063.
Lemma F_385d0 : fetch_word Ubsan.M.loaded_segments (0x385d0 : word) = Some W_385d0.
Proof. vm_refl. Qed.
Lemma D_385d0 : decode_any W_385d0 = Some (Branch BC_EQ 12 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_385d4 : bv 32 := 0x08058e63.
Lemma F_385d4 : fetch_word Ubsan.M.loaded_segments (0x385d4 : word) = Some W_385d4.
Proof. vm_refl. Qed.
Lemma D_385d4 : decode_any W_385d4 = Some (Branch BC_EQ 11 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_385d8 : bv 32 := 0x00b905b3.
Lemma F_385d8 : fetch_word Ubsan.M.loaded_segments (0x385d8 : word) = Some W_385d8.
Proof. vm_refl. Qed.
Lemma D_385d8 : decode_any W_385d8 = Some (Op ALU_ADD 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_385dc : bv 32 := 0x0075f593.
Lemma F_385dc : fetch_word Ubsan.M.loaded_segments (0x385dc : word) = Some W_385dc.
Proof. vm_refl. Qed.
Lemma D_385dc : decode_any W_385dc = Some (OpImm ALU_AND 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_385e0 : bv 32 := 0x08059863.
Lemma F_385e0 : fetch_word Ubsan.M.loaded_segments (0x385e0 : word) = Some W_385e0.
Proof. vm_refl. Qed.
Lemma D_385e0 : decode_any W_385e0 = Some (Branch BC_NE 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_385e4 : bv 32 := 0x00053503.
Lemma F_385e4 : fetch_word Ubsan.M.loaded_segments (0x385e4 : word) = Some W_385e4.
Proof. vm_refl. Qed.
Lemma D_385e4 : decode_any W_385e4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_385e8 : bv 32 := 0x449030ef.
Lemma F_385e8 : fetch_word Ubsan.M.loaded_segments (0x385e8 : word) = Some W_385e8.
Proof. vm_refl. Qed.
Lemma D_385e8 : decode_any W_385e8 = Some (Jal 1 15432, 4%Z).
Proof. vm_refl. Qed.

Definition W_385ec : bv 32 := 0x0004a503.
Lemma F_385ec : fetch_word Ubsan.M.loaded_segments (0x385ec : word) = Some W_385ec.
Proof. vm_refl. Qed.
Lemma D_385ec : decode_any W_385ec = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_385f0 : bv 32 := 0x00198993.
Lemma F_385f0 : fetch_word Ubsan.M.loaded_segments (0x385f0 : word) = Some W_385f0.
Proof. vm_refl. Qed.
Lemma D_385f0 : decode_any W_385f0 = Some (OpImm ALU_ADD 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_385f4 : bv 32 := 0x00890913.
Lemma F_385f4 : fetch_word Ubsan.M.loaded_segments (0x385f4 : word) = Some W_385f4.
Proof. vm_refl. Qed.
Lemma D_385f4 : decode_any W_385f4 = Some (OpImm ALU_ADD 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_385f8 : bv 32 := 0xfca9c0e3.
Lemma F_385f8 : fetch_word Ubsan.M.loaded_segments (0x385f8 : word) = Some W_385f8.
Proof. vm_refl. Qed.
Lemma D_385f8 : decode_any W_385f8 = Some (Branch BC_LT 19 10 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_385fc : bv 32 := 0x0104b503.
Lemma F_385fc : fetch_word Ubsan.M.loaded_segments (0x385fc : word) = Some W_385fc.
Proof. vm_refl. Qed.
Lemma D_385fc : decode_any W_385fc = Some (Load SZ8 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38600 : bv 32 := 0x431030ef.
Lemma F_38600 : fetch_word Ubsan.M.loaded_segments (0x38600 : word) = Some W_38600.
Proof. vm_refl. Qed.
Lemma D_38600 : decode_any W_38600 = Some (Jal 1 15408, 4%Z).
Proof. vm_refl. Qed.

Definition W_38604 : bv 32 := 0x00048513.
Lemma F_38604 : fetch_word Ubsan.M.loaded_segments (0x38604 : word) = Some W_38604.
Proof. vm_refl. Qed.
Lemma D_38604 : decode_any W_38604 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38608 : bv 32 := 0x429030ef.
Lemma F_38608 : fetch_word Ubsan.M.loaded_segments (0x38608 : word) = Some W_38608.
Proof. vm_refl. Qed.
Lemma D_38608 : decode_any W_38608 = Some (Jal 1 15400, 4%Z).
Proof. vm_refl. Qed.

Definition W_3860c : bv 32 := 0x00043023.
Lemma F_3860c : fetch_word Ubsan.M.loaded_segments (0x3860c : word) = Some W_3860c.
Proof. vm_refl. Qed.
Lemma D_3860c : decode_any W_3860c = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38610 : bv 32 := 0x0440006f.
Lemma F_38610 : fetch_word Ubsan.M.loaded_segments (0x38610 : word) = Some W_38610.
Proof. vm_refl. Qed.
Lemma D_38610 : decode_any W_38610 = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_38614 : bv 32 := 0x0000d517.
Lemma F_38614 : fetch_word Ubsan.M.loaded_segments (0x38614 : word) = Some W_38614.
Proof. vm_refl. Qed.
Lemma D_38614 : decode_any W_38614 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_38618 : bv 32 := 0x88453503.
Lemma F_38618 : fetch_word Ubsan.M.loaded_segments (0x38618 : word) = Some W_38618.
Proof. vm_refl. Qed.
Lemma D_38618 : decode_any W_38618 = Some (Load SZ8 true 10 10 2180, 4%Z).
Proof. vm_refl. Qed.

Definition W_3861c : bv 32 := 0x00052503.
Lemma F_3861c : fetch_word Ubsan.M.loaded_segments (0x3861c : word) = Some W_3861c.
Proof. vm_refl. Qed.
Lemma D_3861c : decode_any W_3861c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38620 : bv 32 := 0x00400593.
Lemma F_38620 : fetch_word Ubsan.M.loaded_segments (0x38620 : word) = Some W_38620.
Proof. vm_refl. Qed.
Lemma D_38620 : decode_any W_38620 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38624 : bv 32 := 0x02a5c863.
Lemma F_38624 : fetch_word Ubsan.M.loaded_segments (0x38624 : word) = Some W_38624.
Proof. vm_refl. Qed.
Lemma D_38624 : decode_any W_38624 = Some (Branch BC_LT 11 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_38628 : bv 32 := 0xfffd8517.
Lemma F_38628 : fetch_word Ubsan.M.loaded_segments (0x38628 : word) = Some W_38628.
Proof. vm_refl. Qed.
Lemma D_38628 : decode_any W_38628 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3862c : bv 32 := 0xfffda597.
Lemma F_3862c : fetch_word Ubsan.M.loaded_segments (0x3862c : word) = Some W_3862c.
Proof. vm_refl. Qed.
Lemma D_3862c : decode_any W_3862c = Some (Auipc 11 1048538, 4%Z).
Proof. vm_refl. Qed.

Definition W_38630 : bv 32 := 0x26c50513.
Lemma F_38630 : fetch_word Ubsan.M.loaded_segments (0x38630 : word) = Some W_38630.
Proof. vm_refl. Qed.
Lemma D_38630 : decode_any W_38630 = Some (OpImm ALU_ADD 10 10 620, 4%Z).
Proof. vm_refl. Qed.

Definition W_38634 : bv 32 := 0xeee58593.
Lemma F_38634 : fetch_word Ubsan.M.loaded_segments (0x38634 : word) = Some W_38634.
Proof. vm_refl. Qed.
Lemma D_38634 : decode_any W_38634 = Some (OpImm ALU_ADD 11 11 3822, 4%Z).
Proof. vm_refl. Qed.

Definition W_38638 : bv 32 := 0x02813083.
Lemma F_38638 : fetch_word Ubsan.M.loaded_segments (0x38638 : word) = Some W_38638.
Proof. vm_refl. Qed.
Lemma D_38638 : decode_any W_38638 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3863c : bv 32 := 0x02013403.
Lemma F_3863c : fetch_word Ubsan.M.loaded_segments (0x3863c : word) = Some W_3863c.
Proof. vm_refl. Qed.
Lemma D_3863c : decode_any W_3863c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_38640 : bv 32 := 0x01813483.
Lemma F_38640 : fetch_word Ubsan.M.loaded_segments (0x38640 : word) = Some W_38640.
Proof. vm_refl. Qed.
Lemma D_38640 : decode_any W_38640 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38644 : bv 32 := 0x01013903.
Lemma F_38644 : fetch_word Ubsan.M.loaded_segments (0x38644 : word) = Some W_38644.
Proof. vm_refl. Qed.
Lemma D_38644 : decode_any W_38644 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38648 : bv 32 := 0x00813983.
Lemma F_38648 : fetch_word Ubsan.M.loaded_segments (0x38648 : word) = Some W_38648.
Proof. vm_refl. Qed.
Lemma D_38648 : decode_any W_38648 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3864c : bv 32 := 0x03010113.
Lemma F_3864c : fetch_word Ubsan.M.loaded_segments (0x3864c : word) = Some W_3864c.
Proof. vm_refl. Qed.
Lemma D_3864c : decode_any W_3864c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_38650 : bv 32 := 0xfd8df06f.
Lemma F_38650 : fetch_word Ubsan.M.loaded_segments (0x38650 : word) = Some W_38650.
Proof. vm_refl. Qed.
Lemma D_38650 : decode_any W_38650 = Some (Jal 0 1963992, 4%Z).
Proof. vm_refl. Qed.

Definition W_38654 : bv 32 := 0x02813083.
Lemma F_38654 : fetch_word Ubsan.M.loaded_segments (0x38654 : word) = Some W_38654.
Proof. vm_refl. Qed.
Lemma D_38654 : decode_any W_38654 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_38658 : bv 32 := 0x02013403.
Lemma F_38658 : fetch_word Ubsan.M.loaded_segments (0x38658 : word) = Some W_38658.
Proof. vm_refl. Qed.
Lemma D_38658 : decode_any W_38658 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3865c : bv 32 := 0x01813483.
Lemma F_3865c : fetch_word Ubsan.M.loaded_segments (0x3865c : word) = Some W_3865c.
Proof. vm_refl. Qed.
Lemma D_3865c : decode_any W_3865c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38660 : bv 32 := 0x01013903.
Lemma F_38660 : fetch_word Ubsan.M.loaded_segments (0x38660 : word) = Some W_38660.
Proof. vm_refl. Qed.
Lemma D_38660 : decode_any W_38660 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38664 : bv 32 := 0x00813983.
Lemma F_38664 : fetch_word Ubsan.M.loaded_segments (0x38664 : word) = Some W_38664.
Proof. vm_refl. Qed.
Lemma D_38664 : decode_any W_38664 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38668 : bv 32 := 0x03010113.
Lemma F_38668 : fetch_word Ubsan.M.loaded_segments (0x38668 : word) = Some W_38668.
Proof. vm_refl. Qed.
Lemma D_38668 : decode_any W_38668 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3866c : bv 32 := 0x00008067.
Lemma F_3866c : fetch_word Ubsan.M.loaded_segments (0x3866c : word) = Some W_3866c.
Proof. vm_refl. Qed.
Lemma D_3866c : decode_any W_3866c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38670 : bv 32 := 0xc0001073.
Lemma F_38670 : fetch_word Ubsan.M.loaded_segments (0x38670 : word) = Some W_38670.
Proof. vm_refl. Qed.
Lemma D_38670 : decode_any W_38670 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
