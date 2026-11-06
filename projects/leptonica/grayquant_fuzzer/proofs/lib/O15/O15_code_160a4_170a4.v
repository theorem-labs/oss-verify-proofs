(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.H Require GcFlushS15.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_16648 : bv 32 := 0xff010113.
Lemma F_16648 : fetch_word Plain.M.loaded_segments (0x166a0 : word) = Some W_16648.
Proof. vm_refl. Qed.
Lemma D_16648 : decode_any W_16648 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1664c : bv 32 := 0x00113423.
Lemma F_1664c : fetch_word Plain.M.loaded_segments (0x166a4 : word) = Some W_1664c.
Proof. vm_refl. Qed.
Lemma D_1664c : decode_any W_1664c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16650 : bv 32 := 0x00813023.
Lemma F_16650 : fetch_word Plain.M.loaded_segments (0x166a8 : word) = Some W_16650.
Proof. vm_refl. Qed.
Lemma D_16650 : decode_any W_16650 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16654 : bv 32 := 0x080000ef.
Lemma F_16654 : fetch_word Plain.M.loaded_segments (0x166ac : word) = Some W_16654.
Proof. vm_refl. Qed.
Lemma D_16654 : decode_any W_16654 = Some (Jal 1 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16658 : bv 32 := 0x02050863.
Lemma F_16658 : fetch_word Plain.M.loaded_segments (0x166b0 : word) = Some W_16658.
Proof. vm_refl. Qed.
Lemma D_16658 : decode_any W_16658 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1665c : bv 32 := 0x00456603.
Lemma F_1665c : fetch_word Plain.M.loaded_segments (0x166b4 : word) = Some W_1665c.
Proof. vm_refl. Qed.
Lemma D_1665c : decode_any W_1665c = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16660 : bv 32 := 0x01056683.
Lemma F_16660 : fetch_word Plain.M.loaded_segments (0x166b8 : word) = Some W_16660.
Proof. vm_refl. Qed.
Lemma D_16660 : decode_any W_16660 = Some (Load SZ4 false 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16664 : bv 32 := 0x03853583.
Lemma F_16664 : fetch_word Plain.M.loaded_segments (0x166bc : word) = Some W_16664.
Proof. vm_refl. Qed.
Lemma D_16664 : decode_any W_16664 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16668 : bv 32 := 0x02c68633.
Lemma F_16668 : fetch_word Plain.M.loaded_segments (0x166c0 : word) = Some W_16668.
Proof. vm_refl. Qed.
Lemma D_16668 : decode_any W_16668 = Some (Mul M_MUL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1666c : bv 32 := 0x00261613.
Lemma F_1666c : fetch_word Plain.M.loaded_segments (0x166c4 : word) = Some W_1666c.
Proof. vm_refl. Qed.
Lemma D_1666c : decode_any W_1666c = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16670 : bv 32 := 0x00050413.
Lemma F_16670 : fetch_word Plain.M.loaded_segments (0x166c8 : word) = Some W_16670.
Proof. vm_refl. Qed.
Lemma D_16670 : decode_any W_16670 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16674 : bv 32 := 0x00058513.
Lemma F_16674 : fetch_word Plain.M.loaded_segments (0x166cc : word) = Some W_16674.
Proof. vm_refl. Qed.
Lemma D_16674 : decode_any W_16674 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16678 : bv 32 := 0x00000593.
Lemma F_16678 : fetch_word Plain.M.loaded_segments (0x166d0 : word) = Some W_16678.
Proof. vm_refl. Qed.
Lemma D_16678 : decode_any W_16678 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1667c : bv 32 := 0x179140ef.
Lemma F_1667c : fetch_word Plain.M.loaded_segments (0x166d4 : word) = Some W_1667c.
Proof. vm_refl. Qed.
Lemma D_1667c : decode_any W_1667c = Some (Jal 1 84344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16680 : bv 32 := 0x00040513.
Lemma F_16680 : fetch_word Plain.M.loaded_segments (0x166d8 : word) = Some W_16680.
Proof. vm_refl. Qed.
Lemma D_16680 : decode_any W_16680 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16684 : bv 32 := 0x0400006f.
Lemma F_16684 : fetch_word Plain.M.loaded_segments (0x166dc : word) = Some W_16684.
Proof. vm_refl. Qed.
Lemma D_16684 : decode_any W_16684 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16688 : bv 32 := 0x00016517.
Lemma F_16688 : fetch_word Plain.M.loaded_segments (0x166e0 : word) = Some W_16688.
Proof. vm_refl. Qed.
Lemma D_16688 : decode_any W_16688 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1668c : bv 32 := 0x0a053503.
Lemma F_1668c : fetch_word Plain.M.loaded_segments (0x166e4 : word) = Some W_1668c.
Proof. vm_refl. Qed.
Lemma D_1668c : decode_any W_1668c = Some (Load SZ8 true 10 10 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16690 : bv 32 := 0x00052503.
Lemma F_16690 : fetch_word Plain.M.loaded_segments (0x166e8 : word) = Some W_16690.
Proof. vm_refl. Qed.
Lemma D_16690 : decode_any W_16690 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16694 : bv 32 := 0x00500593.
Lemma F_16694 : fetch_word Plain.M.loaded_segments (0x166ec : word) = Some W_16694.
Proof. vm_refl. Qed.
Lemma D_16694 : decode_any W_16694 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16698 : bv 32 := 0x02a5c463.
Lemma F_16698 : fetch_word Plain.M.loaded_segments (0x166f0 : word) = Some W_16698.
Proof. vm_refl. Qed.
Lemma D_16698 : decode_any W_16698 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1669c : bv 32 := 0xffffa517.
Lemma F_1669c : fetch_word Plain.M.loaded_segments (0x166f4 : word) = Some W_1669c.
Proof. vm_refl. Qed.
Lemma D_1669c : decode_any W_1669c = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166a0 : bv 32 := 0xffffa597.
Lemma F_166a0 : fetch_word Plain.M.loaded_segments (0x166f8 : word) = Some W_166a0.
Proof. vm_refl. Qed.
Lemma D_166a0 : decode_any W_166a0 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166a4 : bv 32 := 0xe2b50513.
Lemma F_166a4 : fetch_word Plain.M.loaded_segments (0x166fc : word) = Some W_166a4.
Proof. vm_refl. Qed.
Lemma D_166a4 : decode_any W_166a4 = Some (OpImm ALU_ADD 10 10 3627, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166a8 : bv 32 := 0x15458593.
Lemma F_166a8 : fetch_word Plain.M.loaded_segments (0x16700 : word) = Some W_166a8.
Proof. vm_refl. Qed.
Lemma D_166a8 : decode_any W_166a8 = Some (OpImm ALU_ADD 11 11 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166ac : bv 32 := 0x00000613.
Lemma F_166ac : fetch_word Plain.M.loaded_segments (0x16704 : word) = Some W_166ac.
Proof. vm_refl. Qed.
Lemma D_166ac : decode_any W_166ac = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166b0 : bv 32 := 0x00813083.
Lemma F_166b0 : fetch_word Plain.M.loaded_segments (0x16708 : word) = Some W_166b0.
Proof. vm_refl. Qed.
Lemma D_166b0 : decode_any W_166b0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166b4 : bv 32 := 0x00013403.
Lemma F_166b4 : fetch_word Plain.M.loaded_segments (0x1670c : word) = Some W_166b4.
Proof. vm_refl. Qed.
Lemma D_166b4 : decode_any W_166b4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166b8 : bv 32 := 0x01010113.
Lemma F_166b8 : fetch_word Plain.M.loaded_segments (0x16710 : word) = Some W_166b8.
Proof. vm_refl. Qed.
Lemma D_166b8 : decode_any W_166b8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166bc : bv 32 := 0xd65fe06f.
Lemma F_166bc : fetch_word Plain.M.loaded_segments (0x16714 : word) = Some W_166bc.
Proof. vm_refl. Qed.
Lemma D_166bc : decode_any W_166bc = Some (Jal 0 2092388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166c4 : bv 32 := 0x00813083.
Lemma F_166c4 : fetch_word Plain.M.loaded_segments (0x1671c : word) = Some W_166c4.
Proof. vm_refl. Qed.
Lemma D_166c4 : decode_any W_166c4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166c8 : bv 32 := 0x00013403.
Lemma F_166c8 : fetch_word Plain.M.loaded_segments (0x16720 : word) = Some W_166c8.
Proof. vm_refl. Qed.
Lemma D_166c8 : decode_any W_166c8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166cc : bv 32 := 0x01010113.
Lemma F_166cc : fetch_word Plain.M.loaded_segments (0x16724 : word) = Some W_166cc.
Proof. vm_refl. Qed.
Lemma D_166cc : decode_any W_166cc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166d0 : bv 32 := 0x00008067.
Lemma F_166d0 : fetch_word Plain.M.loaded_segments (0x16728 : word) = Some W_166d0.
Proof. vm_refl. Qed.
Lemma D_166d0 : decode_any W_166d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166d4 : bv 32 := 0xfd010113.
Lemma F_166d4 : fetch_word Plain.M.loaded_segments (0x1672c : word) = Some W_166d4.
Proof. vm_refl. Qed.
Lemma D_166d4 : decode_any W_166d4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166d8 : bv 32 := 0x02113423.
Lemma F_166d8 : fetch_word Plain.M.loaded_segments (0x16730 : word) = Some W_166d8.
Proof. vm_refl. Qed.
Lemma D_166d8 : decode_any W_166d8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166dc : bv 32 := 0x02813023.
Lemma F_166dc : fetch_word Plain.M.loaded_segments (0x16734 : word) = Some W_166dc.
Proof. vm_refl. Qed.
Lemma D_166dc : decode_any W_166dc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166e0 : bv 32 := 0x00913c23.
Lemma F_166e0 : fetch_word Plain.M.loaded_segments (0x16738 : word) = Some W_166e0.
Proof. vm_refl. Qed.
Lemma D_166e0 : decode_any W_166e0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166e4 : bv 32 := 0x01213823.
Lemma F_166e4 : fetch_word Plain.M.loaded_segments (0x1673c : word) = Some W_166e4.
Proof. vm_refl. Qed.
Lemma D_166e4 : decode_any W_166e4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166e8 : bv 32 := 0x00058493.
Lemma F_166e8 : fetch_word Plain.M.loaded_segments (0x16740 : word) = Some W_166e8.
Proof. vm_refl. Qed.
Lemma D_166e8 : decode_any W_166e8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166ec : bv 32 := 0x124000ef.
Lemma F_166ec : fetch_word Plain.M.loaded_segments (0x16744 : word) = Some W_166ec.
Proof. vm_refl. Qed.
Lemma D_166ec : decode_any W_166ec = Some (Jal 1 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166f0 : bv 32 := 0x02050e63.
Lemma F_166f0 : fetch_word Plain.M.loaded_segments (0x16748 : word) = Some W_166f0.
Proof. vm_refl. Qed.
Lemma D_166f0 : decode_any W_166f0 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166f4 : bv 32 := 0x00050413.
Lemma F_166f4 : fetch_word Plain.M.loaded_segments (0x1674c : word) = Some W_166f4.
Proof. vm_refl. Qed.
Lemma D_166f4 : decode_any W_166f4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166f8 : bv 32 := 0x01052503.
Lemma F_166f8 : fetch_word Plain.M.loaded_segments (0x16750 : word) = Some W_166f8.
Proof. vm_refl. Qed.
Lemma D_166f8 : decode_any W_166f8 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166fc : bv 32 := 0x00017597.
Lemma F_166fc : fetch_word Plain.M.loaded_segments (0x16754 : word) = Some W_166fc.
Proof. vm_refl. Qed.
Lemma D_166fc : decode_any W_166fc = Some (Auipc 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16700 : bv 32 := 0x0ac58913.
Lemma F_16700 : fetch_word Plain.M.loaded_segments (0x16758 : word) = Some W_16700.
Proof. vm_refl. Qed.
Lemma D_16700 : decode_any W_16700 = Some (OpImm ALU_ADD 18 11 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16704 : bv 32 := 0x00093583.
Lemma F_16704 : fetch_word Plain.M.loaded_segments (0x1675c : word) = Some W_16704.
Proof. vm_refl. Qed.
Lemma D_16704 : decode_any W_16704 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16708 : bv 32 := 0x02a48533.
Lemma F_16708 : fetch_word Plain.M.loaded_segments (0x16760 : word) = Some W_16708.
Proof. vm_refl. Qed.
Lemma D_16708 : decode_any W_16708 = Some (Mul M_MUL 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1670c : bv 32 := 0x00251513.
Lemma F_1670c : fetch_word Plain.M.loaded_segments (0x16764 : word) = Some W_1670c.
Proof. vm_refl. Qed.
Lemma D_1670c : decode_any W_1670c = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16710 : bv 32 := 0x000580e7.
Lemma F_16710 : fetch_word Plain.M.loaded_segments (0x16768 : word) = Some W_16710.
Proof. vm_refl. Qed.
Lemma D_16710 : decode_any W_16710 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16714 : bv 32 := 0x04050c63.
Lemma F_16714 : fetch_word Plain.M.loaded_segments (0x1676c : word) = Some W_16714.
Proof. vm_refl. Qed.
Lemma D_16714 : decode_any W_16714 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16718 : bv 32 := 0x02a43c23.
Lemma F_16718 : fetch_word Plain.M.loaded_segments (0x16770 : word) = Some W_16718.
Proof. vm_refl. Qed.
Lemma D_16718 : decode_any W_16718 = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1671c : bv 32 := 0x00040513.
Lemma F_1671c : fetch_word Plain.M.loaded_segments (0x16774 : word) = Some W_1671c.
Proof. vm_refl. Qed.
Lemma D_1671c : decode_any W_1671c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16720 : bv 32 := 0x00000593.
Lemma F_16720 : fetch_word Plain.M.loaded_segments (0x16778 : word) = Some W_16720.
Proof. vm_refl. Qed.
Lemma D_16720 : decode_any W_16720 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16724 : bv 32 := 0x1e4010ef.
Lemma F_16724 : fetch_word Plain.M.loaded_segments (0x1677c : word) = Some W_16724.
Proof. vm_refl. Qed.
Lemma D_16724 : decode_any W_16724 = Some (Jal 1 4580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16728 : bv 32 := 0x0cc0006f.
Lemma F_16728 : fetch_word Plain.M.loaded_segments (0x16780 : word) = Some W_16728.
Proof. vm_refl. Qed.
Lemma D_16728 : decode_any W_16728 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1672c : bv 32 := 0x00016517.
Lemma F_1672c : fetch_word Plain.M.loaded_segments (0x16784 : word) = Some W_1672c.
Proof. vm_refl. Qed.
Lemma D_1672c : decode_any W_1672c = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16730 : bv 32 := 0xffc53503.
Lemma F_16730 : fetch_word Plain.M.loaded_segments (0x16788 : word) = Some W_16730.
Proof. vm_refl. Qed.
Lemma D_16730 : decode_any W_16730 = Some (Load SZ8 true 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16734 : bv 32 := 0x00052503.
Lemma F_16734 : fetch_word Plain.M.loaded_segments (0x1678c : word) = Some W_16734.
Proof. vm_refl. Qed.
Lemma D_16734 : decode_any W_16734 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16738 : bv 32 := 0x00500593.
Lemma F_16738 : fetch_word Plain.M.loaded_segments (0x16790 : word) = Some W_16738.
Proof. vm_refl. Qed.
Lemma D_16738 : decode_any W_16738 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1673c : bv 32 := 0x0aa5ca63.
Lemma F_1673c : fetch_word Plain.M.loaded_segments (0x16794 : word) = Some W_1673c.
Proof. vm_refl. Qed.
Lemma D_1673c : decode_any W_1673c = Some (Branch BC_LT 11 10 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16740 : bv 32 := 0xffffa517.
Lemma F_16740 : fetch_word Plain.M.loaded_segments (0x16798 : word) = Some W_16740.
Proof. vm_refl. Qed.
Lemma D_16740 : decode_any W_16740 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16744 : bv 32 := 0xffffa597.
Lemma F_16744 : fetch_word Plain.M.loaded_segments (0x1679c : word) = Some W_16744.
Proof. vm_refl. Qed.
Lemma D_16744 : decode_any W_16744 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16748 : bv 32 := 0xd8750513.
Lemma F_16748 : fetch_word Plain.M.loaded_segments (0x167a0 : word) = Some W_16748.
Proof. vm_refl. Qed.
Lemma D_16748 : decode_any W_16748 = Some (OpImm ALU_ADD 10 10 3463, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1674c : bv 32 := 0xf3258593.
Lemma F_1674c : fetch_word Plain.M.loaded_segments (0x167a4 : word) = Some W_1674c.
Proof. vm_refl. Qed.
Lemma D_1674c : decode_any W_1674c = Some (OpImm ALU_ADD 11 11 3890, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16750 : bv 32 := 0x00000613.
Lemma F_16750 : fetch_word Plain.M.loaded_segments (0x167a8 : word) = Some W_16750.
Proof. vm_refl. Qed.
Lemma D_16750 : decode_any W_16750 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16754 : bv 32 := 0x02813083.
Lemma F_16754 : fetch_word Plain.M.loaded_segments (0x167ac : word) = Some W_16754.
Proof. vm_refl. Qed.
Lemma D_16754 : decode_any W_16754 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16758 : bv 32 := 0x02013403.
Lemma F_16758 : fetch_word Plain.M.loaded_segments (0x167b0 : word) = Some W_16758.
Proof. vm_refl. Qed.
Lemma D_16758 : decode_any W_16758 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1675c : bv 32 := 0x01813483.
Lemma F_1675c : fetch_word Plain.M.loaded_segments (0x167b4 : word) = Some W_1675c.
Proof. vm_refl. Qed.
Lemma D_1675c : decode_any W_1675c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16760 : bv 32 := 0x01013903.
Lemma F_16760 : fetch_word Plain.M.loaded_segments (0x167b8 : word) = Some W_16760.
Proof. vm_refl. Qed.
Lemma D_16760 : decode_any W_16760 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16764 : bv 32 := 0x03010113.
Lemma F_16764 : fetch_word Plain.M.loaded_segments (0x167bc : word) = Some W_16764.
Proof. vm_refl. Qed.
Lemma D_16764 : decode_any W_16764 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16768 : bv 32 := 0xcb9fe06f.
Lemma F_16768 : fetch_word Plain.M.loaded_segments (0x167c0 : word) = Some W_16768.
Proof. vm_refl. Qed.
Lemma D_16768 : decode_any W_16768 = Some (Jal 0 2092216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1676c : bv 32 := 0x01440513.
Lemma F_1676c : fetch_word Plain.M.loaded_segments (0x167c4 : word) = Some W_1676c.
Proof. vm_refl. Qed.
Lemma D_1676c : decode_any W_1676c = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16770 : bv 32 := 0xfff00593.
Lemma F_16770 : fetch_word Plain.M.loaded_segments (0x167c8 : word) = Some W_16770.
Proof. vm_refl. Qed.
Lemma D_16770 : decode_any W_16770 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16774 : bv 32 := 0x06b5252f.
Lemma F_16774 : fetch_word Plain.M.loaded_segments (0x167cc : word) = Some W_16774.
Proof. vm_refl. Qed.
Lemma D_16774 : decode_any W_16774 = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16778 : bv 32 := 0x00100593.
Lemma F_16778 : fetch_word Plain.M.loaded_segments (0x167d0 : word) = Some W_16778.
Proof. vm_refl. Qed.
Lemma D_16778 : decode_any W_16778 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1677c : bv 32 := 0x04b51063.
Lemma F_1677c : fetch_word Plain.M.loaded_segments (0x167d4 : word) = Some W_1677c.
Proof. vm_refl. Qed.
Lemma D_1677c : decode_any W_1677c = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16780 : bv 32 := 0x03843503.
Lemma F_16780 : fetch_word Plain.M.loaded_segments (0x167d8 : word) = Some W_16780.
Proof. vm_refl. Qed.
Lemma D_16780 : decode_any W_16780 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16784 : bv 32 := 0x00050663.
Lemma F_16784 : fetch_word Plain.M.loaded_segments (0x167dc : word) = Some W_16784.
Proof. vm_refl. Qed.
Lemma D_16784 : decode_any W_16784 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16790 : bv 32 := 0x02843503.
Lemma F_16790 : fetch_word Plain.M.loaded_segments (0x167e8 : word) = Some W_16790.
Proof. vm_refl. Qed.
Lemma D_16790 : decode_any W_16790 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16794 : bv 32 := 0x00050463.
Lemma F_16794 : fetch_word Plain.M.loaded_segments (0x167ec : word) = Some W_16794.
Proof. vm_refl. Qed.
Lemma D_16794 : decode_any W_16794 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1679c : bv 32 := 0x03043503.
Lemma F_1679c : fetch_word Plain.M.loaded_segments (0x167f4 : word) = Some W_1679c.
Proof. vm_refl. Qed.
Lemma D_1679c : decode_any W_1679c = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167a0 : bv 32 := 0x00a13423.
Lemma F_167a0 : fetch_word Plain.M.loaded_segments (0x167f8 : word) = Some W_167a0.
Proof. vm_refl. Qed.
Lemma D_167a0 : decode_any W_167a0 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167a4 : bv 32 := 0x00050863.
Lemma F_167a4 : fetch_word Plain.M.loaded_segments (0x167fc : word) = Some W_167a4.
Proof. vm_refl. Qed.
Lemma D_167a4 : decode_any W_167a4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167b4 : bv 32 := 0x00040513.
Lemma F_167b4 : fetch_word Plain.M.loaded_segments (0x1680c : word) = Some W_167b4.
Proof. vm_refl. Qed.
Lemma D_167b4 : decode_any W_167b4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167b8 : bv 32 := 0x7c80a0ef.
Lemma F_167b8 : fetch_word Plain.M.loaded_segments (0x16810 : word) = Some W_167b8.
Proof. vm_refl. Qed.
Lemma D_167b8 : decode_any W_167b8 = Some (Jal 1 42952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167bc : bv 32 := 0x00016517.
Lemma F_167bc : fetch_word Plain.M.loaded_segments (0x16814 : word) = Some W_167bc.
Proof. vm_refl. Qed.
Lemma D_167bc : decode_any W_167bc = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167c0 : bv 32 := 0xf6c53503.
Lemma F_167c0 : fetch_word Plain.M.loaded_segments (0x16818 : word) = Some W_167c0.
Proof. vm_refl. Qed.
Lemma D_167c0 : decode_any W_167c0 = Some (Load SZ8 true 10 10 3948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167c4 : bv 32 := 0x00052503.
Lemma F_167c4 : fetch_word Plain.M.loaded_segments (0x1681c : word) = Some W_167c4.
Proof. vm_refl. Qed.
Lemma D_167c4 : decode_any W_167c4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167c8 : bv 32 := 0x00500593.
Lemma F_167c8 : fetch_word Plain.M.loaded_segments (0x16820 : word) = Some W_167c8.
Proof. vm_refl. Qed.
Lemma D_167c8 : decode_any W_167c8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167cc : bv 32 := 0x02a5c263.
Lemma F_167cc : fetch_word Plain.M.loaded_segments (0x16824 : word) = Some W_167cc.
Proof. vm_refl. Qed.
Lemma D_167cc : decode_any W_167cc = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167d0 : bv 32 := 0xffffb517.
Lemma F_167d0 : fetch_word Plain.M.loaded_segments (0x16828 : word) = Some W_167d0.
Proof. vm_refl. Qed.
Lemma D_167d0 : decode_any W_167d0 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167d4 : bv 32 := 0xffffa597.
Lemma F_167d4 : fetch_word Plain.M.loaded_segments (0x1682c : word) = Some W_167d4.
Proof. vm_refl. Qed.
Lemma D_167d4 : decode_any W_167d4 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167d8 : bv 32 := 0x8bf50513.
Lemma F_167d8 : fetch_word Plain.M.loaded_segments (0x16830 : word) = Some W_167d8.
Proof. vm_refl. Qed.
Lemma D_167d8 : decode_any W_167d8 = Some (OpImm ALU_ADD 10 10 2239, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167dc : bv 32 := 0xea258593.
Lemma F_167dc : fetch_word Plain.M.loaded_segments (0x16834 : word) = Some W_167dc.
Proof. vm_refl. Qed.
Lemma D_167dc : decode_any W_167dc = Some (OpImm ALU_ADD 11 11 3746, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167e0 : bv 32 := 0x00000613.
Lemma F_167e0 : fetch_word Plain.M.loaded_segments (0x16838 : word) = Some W_167e0.
Proof. vm_refl. Qed.
Lemma D_167e0 : decode_any W_167e0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167e4 : bv 32 := 0xc3dfe0ef.
Lemma F_167e4 : fetch_word Plain.M.loaded_segments (0x1683c : word) = Some W_167e4.
Proof. vm_refl. Qed.
Lemma D_167e4 : decode_any W_167e4 = Some (Jal 1 2092092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167e8 : bv 32 := 0x00050413.
Lemma F_167e8 : fetch_word Plain.M.loaded_segments (0x16840 : word) = Some W_167e8.
Proof. vm_refl. Qed.
Lemma D_167e8 : decode_any W_167e8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167ec : bv 32 := 0x0080006f.
Lemma F_167ec : fetch_word Plain.M.loaded_segments (0x16844 : word) = Some W_167ec.
Proof. vm_refl. Qed.
Lemma D_167ec : decode_any W_167ec = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167f4 : bv 32 := 0x00040513.
Lemma F_167f4 : fetch_word Plain.M.loaded_segments (0x1684c : word) = Some W_167f4.
Proof. vm_refl. Qed.
Lemma D_167f4 : decode_any W_167f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167f8 : bv 32 := 0x02813083.
Lemma F_167f8 : fetch_word Plain.M.loaded_segments (0x16850 : word) = Some W_167f8.
Proof. vm_refl. Qed.
Lemma D_167f8 : decode_any W_167f8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167fc : bv 32 := 0x02013403.
Lemma F_167fc : fetch_word Plain.M.loaded_segments (0x16854 : word) = Some W_167fc.
Proof. vm_refl. Qed.
Lemma D_167fc : decode_any W_167fc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16800 : bv 32 := 0x01813483.
Lemma F_16800 : fetch_word Plain.M.loaded_segments (0x16858 : word) = Some W_16800.
Proof. vm_refl. Qed.
Lemma D_16800 : decode_any W_16800 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16804 : bv 32 := 0x01013903.
Lemma F_16804 : fetch_word Plain.M.loaded_segments (0x1685c : word) = Some W_16804.
Proof. vm_refl. Qed.
Lemma D_16804 : decode_any W_16804 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16808 : bv 32 := 0x03010113.
Lemma F_16808 : fetch_word Plain.M.loaded_segments (0x16860 : word) = Some W_16808.
Proof. vm_refl. Qed.
Lemma D_16808 : decode_any W_16808 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1680c : bv 32 := 0x00008067.
Lemma F_1680c : fetch_word Plain.M.loaded_segments (0x16864 : word) = Some W_1680c.
Proof. vm_refl. Qed.
Lemma D_1680c : decode_any W_1680c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c18 : bv 32 := 0xfe010113.
Lemma F_16c18 : fetch_word Plain.M.loaded_segments (0x16c70 : word) = Some W_16c18.
Proof. vm_refl. Qed.
Lemma D_16c18 : decode_any W_16c18 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c1c : bv 32 := 0x00113c23.
Lemma F_16c1c : fetch_word Plain.M.loaded_segments (0x16c74 : word) = Some W_16c1c.
Proof. vm_refl. Qed.
Lemma D_16c1c : decode_any W_16c1c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c20 : bv 32 := 0x00813823.
Lemma F_16c20 : fetch_word Plain.M.loaded_segments (0x16c78 : word) = Some W_16c20.
Proof. vm_refl. Qed.
Lemma D_16c20 : decode_any W_16c20 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c24 : bv 32 := 0x00913423.
Lemma F_16c24 : fetch_word Plain.M.loaded_segments (0x16c7c : word) = Some W_16c24.
Proof. vm_refl. Qed.
Lemma D_16c24 : decode_any W_16c24 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c28 : bv 32 := 0x02050a63.
Lemma F_16c28 : fetch_word Plain.M.loaded_segments (0x16c80 : word) = Some W_16c28.
Proof. vm_refl. Qed.
Lemma D_16c28 : decode_any W_16c28 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c2c : bv 32 := 0x00050493.
Lemma F_16c2c : fetch_word Plain.M.loaded_segments (0x16c84 : word) = Some W_16c2c.
Proof. vm_refl. Qed.
Lemma D_16c2c : decode_any W_16c2c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c30 : bv 32 := 0x00052503.
Lemma F_16c30 : fetch_word Plain.M.loaded_segments (0x16c88 : word) = Some W_16c30.
Proof. vm_refl. Qed.
Lemma D_16c30 : decode_any W_16c30 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c34 : bv 32 := 0x0044a583.
Lemma F_16c34 : fetch_word Plain.M.loaded_segments (0x16c8c : word) = Some W_16c34.
Proof. vm_refl. Qed.
Lemma D_16c34 : decode_any W_16c34 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c38 : bv 32 := 0x0084a603.
Lemma F_16c38 : fetch_word Plain.M.loaded_segments (0x16c90 : word) = Some W_16c38.
Proof. vm_refl. Qed.
Lemma D_16c38 : decode_any W_16c38 = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c3c : bv 32 := 0xa99ff0ef.
Lemma F_16c3c : fetch_word Plain.M.loaded_segments (0x16c94 : word) = Some W_16c3c.
Proof. vm_refl. Qed.
Lemma D_16c3c : decode_any W_16c3c = Some (Jal 1 2095768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c40 : bv 32 := 0x04050263.
Lemma F_16c40 : fetch_word Plain.M.loaded_segments (0x16c98 : word) = Some W_16c40.
Proof. vm_refl. Qed.
Lemma D_16c40 : decode_any W_16c40 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c44 : bv 32 := 0x00050413.
Lemma F_16c44 : fetch_word Plain.M.loaded_segments (0x16c9c : word) = Some W_16c44.
Proof. vm_refl. Qed.
Lemma D_16c44 : decode_any W_16c44 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c48 : bv 32 := 0x08a48063.
Lemma F_16c48 : fetch_word Plain.M.loaded_segments (0x16ca0 : word) = Some W_16c48.
Proof. vm_refl. Qed.
Lemma D_16c48 : decode_any W_16c48 = Some (Branch BC_EQ 9 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c4c : bv 32 := 0x00c4a503.
Lemma F_16c4c : fetch_word Plain.M.loaded_segments (0x16ca4 : word) = Some W_16c4c.
Proof. vm_refl. Qed.
Lemma D_16c4c : decode_any W_16c4c = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c50 : bv 32 := 0x08a05463.
Lemma F_16c50 : fetch_word Plain.M.loaded_segments (0x16ca8 : word) = Some W_16c50.
Proof. vm_refl. Qed.
Lemma D_16c50 : decode_any W_16c50 = Some (Branch BC_GE 0 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c54 : bv 32 := 0x00a42623.
Lemma F_16c54 : fetch_word Plain.M.loaded_segments (0x16cac : word) = Some W_16c54.
Proof. vm_refl. Qed.
Lemma D_16c54 : decode_any W_16c54 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c58 : bv 32 := 0x0ac0006f.
Lemma F_16c58 : fetch_word Plain.M.loaded_segments (0x16cb0 : word) = Some W_16c58.
Proof. vm_refl. Qed.
Lemma D_16c58 : decode_any W_16c58 = Some (Jal 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c84 : bv 32 := 0x00016517.
Lemma F_16c84 : fetch_word Plain.M.loaded_segments (0x16cdc : word) = Some W_16c84.
Proof. vm_refl. Qed.
Lemma D_16c84 : decode_any W_16c84 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c88 : bv 32 := 0xaa453503.
Lemma F_16c88 : fetch_word Plain.M.loaded_segments (0x16ce0 : word) = Some W_16c88.
Proof. vm_refl. Qed.
Lemma D_16c88 : decode_any W_16c88 = Some (Load SZ8 true 10 10 2724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c8c : bv 32 := 0x00052503.
Lemma F_16c8c : fetch_word Plain.M.loaded_segments (0x16ce4 : word) = Some W_16c8c.
Proof. vm_refl. Qed.
Lemma D_16c8c : decode_any W_16c8c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c90 : bv 32 := 0x00500593.
Lemma F_16c90 : fetch_word Plain.M.loaded_segments (0x16ce8 : word) = Some W_16c90.
Proof. vm_refl. Qed.
Lemma D_16c90 : decode_any W_16c90 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c94 : bv 32 := 0x02a5c663.
Lemma F_16c94 : fetch_word Plain.M.loaded_segments (0x16cec : word) = Some W_16c94.
Proof. vm_refl. Qed.
Lemma D_16c94 : decode_any W_16c94 = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c98 : bv 32 := 0xffffa517.
Lemma F_16c98 : fetch_word Plain.M.loaded_segments (0x16cf0 : word) = Some W_16c98.
Proof. vm_refl. Qed.
Lemma D_16c98 : decode_any W_16c98 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c9c : bv 32 := 0xffffa597.
Lemma F_16c9c : fetch_word Plain.M.loaded_segments (0x16cf4 : word) = Some W_16c9c.
Proof. vm_refl. Qed.
Lemma D_16c9c : decode_any W_16c9c = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ca0 : bv 32 := 0x82f50513.
Lemma F_16ca0 : fetch_word Plain.M.loaded_segments (0x16cf8 : word) = Some W_16ca0.
Proof. vm_refl. Qed.
Lemma D_16ca0 : decode_any W_16ca0 = Some (OpImm ALU_ADD 10 10 2095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ca4 : bv 32 := 0x41058593.
Lemma F_16ca4 : fetch_word Plain.M.loaded_segments (0x16cfc : word) = Some W_16ca4.
Proof. vm_refl. Qed.
Lemma D_16ca4 : decode_any W_16ca4 = Some (OpImm ALU_ADD 11 11 1040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ca8 : bv 32 := 0x00000613.
Lemma F_16ca8 : fetch_word Plain.M.loaded_segments (0x16d00 : word) = Some W_16ca8.
Proof. vm_refl. Qed.
Lemma D_16ca8 : decode_any W_16ca8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16cac : bv 32 := 0x01813083.
Lemma F_16cac : fetch_word Plain.M.loaded_segments (0x16d04 : word) = Some W_16cac.
Proof. vm_refl. Qed.
Lemma D_16cac : decode_any W_16cac = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16cb0 : bv 32 := 0x01013403.
Lemma F_16cb0 : fetch_word Plain.M.loaded_segments (0x16d08 : word) = Some W_16cb0.
Proof. vm_refl. Qed.
Lemma D_16cb0 : decode_any W_16cb0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16cb4 : bv 32 := 0x00813483.
Lemma F_16cb4 : fetch_word Plain.M.loaded_segments (0x16d0c : word) = Some W_16cb4.
Proof. vm_refl. Qed.
Lemma D_16cb4 : decode_any W_16cb4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16cb8 : bv 32 := 0x02010113.
Lemma F_16cb8 : fetch_word Plain.M.loaded_segments (0x16d10 : word) = Some W_16cb8.
Proof. vm_refl. Qed.
Lemma D_16cb8 : decode_any W_16cb8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16cbc : bv 32 := 0xf64fe06f.
Lemma F_16cbc : fetch_word Plain.M.loaded_segments (0x16d14 : word) = Some W_16cbc.
Proof. vm_refl. Qed.
Lemma D_16cbc : decode_any W_16cbc = Some (Jal 0 2090852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d04 : bv 32 := 0x0184b503.
Lemma F_16d04 : fetch_word Plain.M.loaded_segments (0x16d5c : word) = Some W_16d04.
Proof. vm_refl. Qed.
Lemma D_16d04 : decode_any W_16d04 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d08 : bv 32 := 0x00a43c23.
Lemma F_16d08 : fetch_word Plain.M.loaded_segments (0x16d60 : word) = Some W_16d08.
Proof. vm_refl. Qed.
Lemma D_16d08 : decode_any W_16d08 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d0c : bv 32 := 0x00040513.
Lemma F_16d0c : fetch_word Plain.M.loaded_segments (0x16d64 : word) = Some W_16d0c.
Proof. vm_refl. Qed.
Lemma D_16d0c : decode_any W_16d0c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d10 : bv 32 := 0x00048593.
Lemma F_16d10 : fetch_word Plain.M.loaded_segments (0x16d68 : word) = Some W_16d10.
Proof. vm_refl. Qed.
Lemma D_16d10 : decode_any W_16d10 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d14 : bv 32 := 0x144000ef.
Lemma F_16d14 : fetch_word Plain.M.loaded_segments (0x16d6c : word) = Some W_16d14.
Proof. vm_refl. Qed.
Lemma D_16d14 : decode_any W_16d14 = Some (Jal 1 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d18 : bv 32 := 0x0284b583.
Lemma F_16d18 : fetch_word Plain.M.loaded_segments (0x16d70 : word) = Some W_16d18.
Proof. vm_refl. Qed.
Lemma D_16d18 : decode_any W_16d18 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d1c : bv 32 := 0x02840513.
Lemma F_16d1c : fetch_word Plain.M.loaded_segments (0x16d74 : word) = Some W_16d1c.
Proof. vm_refl. Qed.
Lemma D_16d1c : decode_any W_16d1c = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d20 : bv 32 := 0x8a9fe0ef.
Lemma F_16d20 : fetch_word Plain.M.loaded_segments (0x16d78 : word) = Some W_16d20.
Proof. vm_refl. Qed.
Lemma D_16d20 : decode_any W_16d20 = Some (Jal 1 2091176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d24 : bv 32 := 0x0204a503.
Lemma F_16d24 : fetch_word Plain.M.loaded_segments (0x16d7c : word) = Some W_16d24.
Proof. vm_refl. Qed.
Lemma D_16d24 : decode_any W_16d24 = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d28 : bv 32 := 0x02a42023.
Lemma F_16d28 : fetch_word Plain.M.loaded_segments (0x16d80 : word) = Some W_16d28.
Proof. vm_refl. Qed.
Lemma D_16d28 : decode_any W_16d28 = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d2c : bv 32 := 0x00040513.
Lemma F_16d2c : fetch_word Plain.M.loaded_segments (0x16d84 : word) = Some W_16d2c.
Proof. vm_refl. Qed.
Lemma D_16d2c : decode_any W_16d2c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d30 : bv 32 := 0x00000593.
Lemma F_16d30 : fetch_word Plain.M.loaded_segments (0x16d88 : word) = Some W_16d30.
Proof. vm_refl. Qed.
Lemma D_16d30 : decode_any W_16d30 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d34 : bv 32 := 0x3d5000ef.
Lemma F_16d34 : fetch_word Plain.M.loaded_segments (0x16d8c : word) = Some W_16d34.
Proof. vm_refl. Qed.
Lemma D_16d34 : decode_any W_16d34 = Some (Jal 1 3028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d38 : bv 32 := 0x00040513.
Lemma F_16d38 : fetch_word Plain.M.loaded_segments (0x16d90 : word) = Some W_16d38.
Proof. vm_refl. Qed.
Lemma D_16d38 : decode_any W_16d38 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d3c : bv 32 := 0x01813083.
Lemma F_16d3c : fetch_word Plain.M.loaded_segments (0x16d94 : word) = Some W_16d3c.
Proof. vm_refl. Qed.
Lemma D_16d3c : decode_any W_16d3c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d40 : bv 32 := 0x01013403.
Lemma F_16d40 : fetch_word Plain.M.loaded_segments (0x16d98 : word) = Some W_16d40.
Proof. vm_refl. Qed.
Lemma D_16d40 : decode_any W_16d40 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d44 : bv 32 := 0x00813483.
Lemma F_16d44 : fetch_word Plain.M.loaded_segments (0x16d9c : word) = Some W_16d44.
Proof. vm_refl. Qed.
Lemma D_16d44 : decode_any W_16d44 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d48 : bv 32 := 0x02010113.
Lemma F_16d48 : fetch_word Plain.M.loaded_segments (0x16da0 : word) = Some W_16d48.
Proof. vm_refl. Qed.
Lemma D_16d48 : decode_any W_16d48 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d4c : bv 32 := 0x00008067.
Lemma F_16d4c : fetch_word Plain.M.loaded_segments (0x16da4 : word) = Some W_16d4c.
Proof. vm_refl. Qed.
Lemma D_16d4c : decode_any W_16d4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d50 : bv 32 := 0x00058463.
Lemma F_16d50 : fetch_word Plain.M.loaded_segments (0x16da8 : word) = Some W_16d50.
Proof. vm_refl. Qed.
Lemma D_16d50 : decode_any W_16d50 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d54 : bv 32 := 0x0005a023.
Lemma F_16d54 : fetch_word Plain.M.loaded_segments (0x16dac : word) = Some W_16d54.
Proof. vm_refl. Qed.
Lemma D_16d54 : decode_any W_16d54 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d58 : bv 32 := 0x00060463.
Lemma F_16d58 : fetch_word Plain.M.loaded_segments (0x16db0 : word) = Some W_16d58.
Proof. vm_refl. Qed.
Lemma D_16d58 : decode_any W_16d58 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d5c : bv 32 := 0x00062023.
Lemma F_16d5c : fetch_word Plain.M.loaded_segments (0x16db4 : word) = Some W_16d5c.
Proof. vm_refl. Qed.
Lemma D_16d5c : decode_any W_16d5c = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d60 : bv 32 := 0x00068463.
Lemma F_16d60 : fetch_word Plain.M.loaded_segments (0x16db8 : word) = Some W_16d60.
Proof. vm_refl. Qed.
Lemma D_16d60 : decode_any W_16d60 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d64 : bv 32 := 0x0006a023.
Lemma F_16d64 : fetch_word Plain.M.loaded_segments (0x16dbc : word) = Some W_16d64.
Proof. vm_refl. Qed.
Lemma D_16d64 : decode_any W_16d64 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d68 : bv 32 := 0x02050a63.
Lemma F_16d68 : fetch_word Plain.M.loaded_segments (0x16dc0 : word) = Some W_16d68.
Proof. vm_refl. Qed.
Lemma D_16d68 : decode_any W_16d68 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d6c : bv 32 := 0x00058663.
Lemma F_16d6c : fetch_word Plain.M.loaded_segments (0x16dc4 : word) = Some W_16d6c.
Proof. vm_refl. Qed.
Lemma D_16d6c : decode_any W_16d6c = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d70 : bv 32 := 0x00052703.
Lemma F_16d70 : fetch_word Plain.M.loaded_segments (0x16dc8 : word) = Some W_16d70.
Proof. vm_refl. Qed.
Lemma D_16d70 : decode_any W_16d70 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d74 : bv 32 := 0x00e5a023.
Lemma F_16d74 : fetch_word Plain.M.loaded_segments (0x16dcc : word) = Some W_16d74.
Proof. vm_refl. Qed.
Lemma D_16d74 : decode_any W_16d74 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d78 : bv 32 := 0x00060663.
Lemma F_16d78 : fetch_word Plain.M.loaded_segments (0x16dd0 : word) = Some W_16d78.
Proof. vm_refl. Qed.
Lemma D_16d78 : decode_any W_16d78 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d7c : bv 32 := 0x00452583.
Lemma F_16d7c : fetch_word Plain.M.loaded_segments (0x16dd4 : word) = Some W_16d7c.
Proof. vm_refl. Qed.
Lemma D_16d7c : decode_any W_16d7c = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d80 : bv 32 := 0x00b62023.
Lemma F_16d80 : fetch_word Plain.M.loaded_segments (0x16dd8 : word) = Some W_16d80.
Proof. vm_refl. Qed.
Lemma D_16d80 : decode_any W_16d80 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d84 : bv 32 := 0x00000593.
Lemma F_16d84 : fetch_word Plain.M.loaded_segments (0x16ddc : word) = Some W_16d84.
Proof. vm_refl. Qed.
Lemma D_16d84 : decode_any W_16d84 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d88 : bv 32 := 0x00068663.
Lemma F_16d88 : fetch_word Plain.M.loaded_segments (0x16de0 : word) = Some W_16d88.
Proof. vm_refl. Qed.
Lemma D_16d88 : decode_any W_16d88 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d8c : bv 32 := 0x00852503.
Lemma F_16d8c : fetch_word Plain.M.loaded_segments (0x16de4 : word) = Some W_16d8c.
Proof. vm_refl. Qed.
Lemma D_16d8c : decode_any W_16d8c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d90 : bv 32 := 0x00a6a023.
Lemma F_16d90 : fetch_word Plain.M.loaded_segments (0x16de8 : word) = Some W_16d90.
Proof. vm_refl. Qed.
Lemma D_16d90 : decode_any W_16d90 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d94 : bv 32 := 0x00058513.
Lemma F_16d94 : fetch_word Plain.M.loaded_segments (0x16dec : word) = Some W_16d94.
Proof. vm_refl. Qed.
Lemma D_16d94 : decode_any W_16d94 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d98 : bv 32 := 0x00008067.
Lemma F_16d98 : fetch_word Plain.M.loaded_segments (0x16df0 : word) = Some W_16d98.
Proof. vm_refl. Qed.
Lemma D_16d98 : decode_any W_16d98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e58 : bv 32 := 0xfd010113.
Lemma F_16e58 : fetch_word Plain.M.loaded_segments (0x16eb0 : word) = Some W_16e58.
Proof. vm_refl. Qed.
Lemma D_16e58 : decode_any W_16e58 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e5c : bv 32 := 0x02113423.
Lemma F_16e5c : fetch_word Plain.M.loaded_segments (0x16eb4 : word) = Some W_16e5c.
Proof. vm_refl. Qed.
Lemma D_16e5c : decode_any W_16e5c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e60 : bv 32 := 0x02813023.
Lemma F_16e60 : fetch_word Plain.M.loaded_segments (0x16eb8 : word) = Some W_16e60.
Proof. vm_refl. Qed.
Lemma D_16e60 : decode_any W_16e60 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e64 : bv 32 := 0x00913c23.
Lemma F_16e64 : fetch_word Plain.M.loaded_segments (0x16ebc : word) = Some W_16e64.
Proof. vm_refl. Qed.
Lemma D_16e64 : decode_any W_16e64 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e68 : bv 32 := 0x0e058063.
Lemma F_16e68 : fetch_word Plain.M.loaded_segments (0x16ec0 : word) = Some W_16e68.
Proof. vm_refl. Qed.
Lemma D_16e68 : decode_any W_16e68 = Some (Branch BC_EQ 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e6c : bv 32 := 0x10050263.
Lemma F_16e6c : fetch_word Plain.M.loaded_segments (0x16ec4 : word) = Some W_16e6c.
Proof. vm_refl. Qed.
Lemma D_16e6c : decode_any W_16e6c = Some (Branch BC_EQ 10 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e70 : bv 32 := 0x0ca58863.
Lemma F_16e70 : fetch_word Plain.M.loaded_segments (0x16ec8 : word) = Some W_16e70.
Proof. vm_refl. Qed.
Lemma D_16e70 : decode_any W_16e70 = Some (Branch BC_EQ 11 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e74 : bv 32 := 0x0085a603.
Lemma F_16e74 : fetch_word Plain.M.loaded_segments (0x16ecc : word) = Some W_16e74.
Proof. vm_refl. Qed.
Lemma D_16e74 : decode_any W_16e74 = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e78 : bv 32 := 0x00852683.
Lemma F_16e78 : fetch_word Plain.M.loaded_segments (0x16ed0 : word) = Some W_16e78.
Proof. vm_refl. Qed.
Lemma D_16e78 : decode_any W_16e78 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e7c : bv 32 := 0x10d61e63.
Lemma F_16e7c : fetch_word Plain.M.loaded_segments (0x16ed4 : word) = Some W_16e7c.
Proof. vm_refl. Qed.
Lemma D_16e7c : decode_any W_16e7c = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e80 : bv 32 := 0x03053603.
Lemma F_16e80 : fetch_word Plain.M.loaded_segments (0x16ed8 : word) = Some W_16e80.
Proof. vm_refl. Qed.
Lemma D_16e80 : decode_any W_16e80 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e84 : bv 32 := 0x00c13823.
Lemma F_16e84 : fetch_word Plain.M.loaded_segments (0x16edc : word) = Some W_16e84.
Proof. vm_refl. Qed.
Lemma D_16e84 : decode_any W_16e84 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e88 : bv 32 := 0x02060063.
Lemma F_16e88 : fetch_word Plain.M.loaded_segments (0x16ee0 : word) = Some W_16e88.
Proof. vm_refl. Qed.
Lemma D_16e88 : decode_any W_16e88 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ea8 : bv 32 := 0x0305b403.
Lemma F_16ea8 : fetch_word Plain.M.loaded_segments (0x16f00 : word) = Some W_16ea8.
Proof. vm_refl. Qed.
Lemma D_16ea8 : decode_any W_16ea8 = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16eac : bv 32 := 0x08040a63.
Lemma F_16eac : fetch_word Plain.M.loaded_segments (0x16f04 : word) = Some W_16eac.
Proof. vm_refl. Qed.
Lemma D_16eac : decode_any W_16eac = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16eb0 : bv 32 := 0x00050493.
Lemma F_16eb0 : fetch_word Plain.M.loaded_segments (0x16f08 : word) = Some W_16eb0.
Proof. vm_refl. Qed.
Lemma D_16eb0 : decode_any W_16eb0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16eb4 : bv 32 := 0x00c10613.
Lemma F_16eb4 : fetch_word Plain.M.loaded_segments (0x16f0c : word) = Some W_16eb4.
Proof. vm_refl. Qed.
Lemma D_16eb4 : decode_any W_16eb4 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16eb8 : bv 32 := 0x00040513.
Lemma F_16eb8 : fetch_word Plain.M.loaded_segments (0x16f10 : word) = Some W_16eb8.
Proof. vm_refl. Qed.
Lemma D_16eb8 : decode_any W_16eb8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ebc : bv 32 := 0x00000593.
Lemma F_16ebc : fetch_word Plain.M.loaded_segments (0x16f14 : word) = Some W_16ebc.
Proof. vm_refl. Qed.
Lemma D_16ebc : decode_any W_16ebc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ec0 : bv 32 := 0x0d0010ef.
Lemma F_16ec0 : fetch_word Plain.M.loaded_segments (0x16f18 : word) = Some W_16ec0.
Proof. vm_refl. Qed.
Lemma D_16ec0 : decode_any W_16ec0 = Some (Jal 1 4304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ec4 : bv 32 := 0x00c12503.
Lemma F_16ec4 : fetch_word Plain.M.loaded_segments (0x16f1c : word) = Some W_16ec4.
Proof. vm_refl. Qed.
Lemma D_16ec4 : decode_any W_16ec4 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ec8 : bv 32 := 0x10050663.
Lemma F_16ec8 : fetch_word Plain.M.loaded_segments (0x16f20 : word) = Some W_16ec8.
Proof. vm_refl. Qed.
Lemma D_16ec8 : decode_any W_16ec8 = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ecc : bv 32 := 0x00040513.
Lemma F_16ecc : fetch_word Plain.M.loaded_segments (0x16f24 : word) = Some W_16ecc.
Proof. vm_refl. Qed.
Lemma D_16ecc : decode_any W_16ecc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ed0 : bv 32 := 0x7c5000ef.
Lemma F_16ed0 : fetch_word Plain.M.loaded_segments (0x16f28 : word) = Some W_16ed0.
Proof. vm_refl. Qed.
Lemma D_16ed0 : decode_any W_16ed0 = Some (Jal 1 4036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ed4 : bv 32 := 0x12050463.
Lemma F_16ed4 : fetch_word Plain.M.loaded_segments (0x16f2c : word) = Some W_16ed4.
Proof. vm_refl. Qed.
Lemma D_16ed4 : decode_any W_16ed4 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ed8 : bv 32 := 0x00048593.
Lemma F_16ed8 : fetch_word Plain.M.loaded_segments (0x16f30 : word) = Some W_16ed8.
Proof. vm_refl. Qed.
Lemma D_16ed8 : decode_any W_16ed8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16edc : bv 32 := 0x0304b603.
Lemma F_16edc : fetch_word Plain.M.loaded_segments (0x16f34 : word) = Some W_16edc.
Proof. vm_refl. Qed.
Lemma D_16edc : decode_any W_16edc = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ee0 : bv 32 := 0x00c13823.
Lemma F_16ee0 : fetch_word Plain.M.loaded_segments (0x16f38 : word) = Some W_16ee0.
Proof. vm_refl. Qed.
Lemma D_16ee0 : decode_any W_16ee0 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ee4 : bv 32 := 0x00060c63.
Lemma F_16ee4 : fetch_word Plain.M.loaded_segments (0x16f3c : word) = Some W_16ee4.
Proof. vm_refl. Qed.
Lemma D_16ee4 : decode_any W_16ee4 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16efc : bv 32 := 0x02a5b823.
Lemma F_16efc : fetch_word Plain.M.loaded_segments (0x16f54 : word) = Some W_16efc.
Proof. vm_refl. Qed.
Lemma D_16efc : decode_any W_16efc = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f00 : bv 32 := 0x01010613.
Lemma F_16f00 : fetch_word Plain.M.loaded_segments (0x16f58 : word) = Some W_16f00.
Proof. vm_refl. Qed.
Lemma D_16f00 : decode_any W_16f00 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f04 : bv 32 := 0x00000593.
Lemma F_16f04 : fetch_word Plain.M.loaded_segments (0x16f5c : word) = Some W_16f04.
Proof. vm_refl. Qed.
Lemma D_16f04 : decode_any W_16f04 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f08 : bv 32 := 0x088010ef.
Lemma F_16f08 : fetch_word Plain.M.loaded_segments (0x16f60 : word) = Some W_16f08.
Proof. vm_refl. Qed.
Lemma D_16f08 : decode_any W_16f08 = Some (Jal 1 4232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f0c : bv 32 := 0x01012503.
Lemma F_16f0c : fetch_word Plain.M.loaded_segments (0x16f64 : word) = Some W_16f0c.
Proof. vm_refl. Qed.
Lemma D_16f0c : decode_any W_16f0c = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f10 : bv 32 := 0x02051863.
Lemma F_16f10 : fetch_word Plain.M.loaded_segments (0x16f68 : word) = Some W_16f10.
Proof. vm_refl. Qed.
Lemma D_16f10 : decode_any W_16f10 = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f40 : bv 32 := 0x00000513.
Lemma F_16f40 : fetch_word Plain.M.loaded_segments (0x16f98 : word) = Some W_16f40.
Proof. vm_refl. Qed.
Lemma D_16f40 : decode_any W_16f40 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f44 : bv 32 := 0x0ec0006f.
Lemma F_16f44 : fetch_word Plain.M.loaded_segments (0x16f9c : word) = Some W_16f44.
Proof. vm_refl. Qed.
Lemma D_16f44 : decode_any W_16f44 = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ffc : bv 32 := 0x00015517.
Lemma F_16ffc : fetch_word Plain.M.loaded_segments (0x17054 : word) = Some W_16ffc.
Proof. vm_refl. Qed.
Lemma D_16ffc : decode_any W_16ffc = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17000 : bv 32 := 0x72c53503.
Lemma F_17000 : fetch_word Plain.M.loaded_segments (0x17058 : word) = Some W_17000.
Proof. vm_refl. Qed.
Lemma D_17000 : decode_any W_17000 = Some (Load SZ8 true 10 10 1836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17004 : bv 32 := 0x00052503.
Lemma F_17004 : fetch_word Plain.M.loaded_segments (0x1705c : word) = Some W_17004.
Proof. vm_refl. Qed.
Lemma D_17004 : decode_any W_17004 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17008 : bv 32 := 0x00500593.
Lemma F_17008 : fetch_word Plain.M.loaded_segments (0x17060 : word) = Some W_17008.
Proof. vm_refl. Qed.
Lemma D_17008 : decode_any W_17008 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1700c : bv 32 := 0x02a5c063.
Lemma F_1700c : fetch_word Plain.M.loaded_segments (0x17064 : word) = Some W_1700c.
Proof. vm_refl. Qed.
Lemma D_1700c : decode_any W_1700c = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17010 : bv 32 := 0xffff9517.
Lemma F_17010 : fetch_word Plain.M.loaded_segments (0x17068 : word) = Some W_17010.
Proof. vm_refl. Qed.
Lemma D_17010 : decode_any W_17010 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17014 : bv 32 := 0xffff9597.
Lemma F_17014 : fetch_word Plain.M.loaded_segments (0x1706c : word) = Some W_17014.
Proof. vm_refl. Qed.
Lemma D_17014 : decode_any W_17014 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17018 : bv 32 := 0x4c550513.
Lemma F_17018 : fetch_word Plain.M.loaded_segments (0x17070 : word) = Some W_17018.
Proof. vm_refl. Qed.
Lemma D_17018 : decode_any W_17018 = Some (OpImm ALU_ADD 10 10 1221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1701c : bv 32 := 0x57f58593.
Lemma F_1701c : fetch_word Plain.M.loaded_segments (0x17074 : word) = Some W_1701c.
Proof. vm_refl. Qed.
Lemma D_1701c : decode_any W_1701c = Some (OpImm ALU_ADD 11 11 1407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17020 : bv 32 := 0x00100613.
Lemma F_17020 : fetch_word Plain.M.loaded_segments (0x17078 : word) = Some W_17020.
Proof. vm_refl. Qed.
Lemma D_17020 : decode_any W_17020 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17024 : bv 32 := 0xb2cfe0ef.
Lemma F_17024 : fetch_word Plain.M.loaded_segments (0x1707c : word) = Some W_17024.
Proof. vm_refl. Qed.
Lemma D_17024 : decode_any W_17024 = Some (Jal 1 2089772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17028 : bv 32 := 0x0080006f.
Lemma F_17028 : fetch_word Plain.M.loaded_segments (0x17080 : word) = Some W_17028.
Proof. vm_refl. Qed.
Lemma D_17028 : decode_any W_17028 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17030 : bv 32 := 0x02813083.
Lemma F_17030 : fetch_word Plain.M.loaded_segments (0x17088 : word) = Some W_17030.
Proof. vm_refl. Qed.
Lemma D_17030 : decode_any W_17030 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17034 : bv 32 := 0x02013403.
Lemma F_17034 : fetch_word Plain.M.loaded_segments (0x1708c : word) = Some W_17034.
Proof. vm_refl. Qed.
Lemma D_17034 : decode_any W_17034 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17038 : bv 32 := 0x01813483.
Lemma F_17038 : fetch_word Plain.M.loaded_segments (0x17090 : word) = Some W_17038.
Proof. vm_refl. Qed.
Lemma D_17038 : decode_any W_17038 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1703c : bv 32 := 0x03010113.
Lemma F_1703c : fetch_word Plain.M.loaded_segments (0x17094 : word) = Some W_1703c.
Proof. vm_refl. Qed.
Lemma D_1703c : decode_any W_1703c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17040 : bv 32 := 0x00008067.
Lemma F_17040 : fetch_word Plain.M.loaded_segments (0x17098 : word) = Some W_17040.
Proof. vm_refl. Qed.
Lemma D_17040 : decode_any W_17040 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

