(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation PSEGS := ImgP.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_95728 : bv 32 := 0x00008067.
Lemma F_95728 : fetch_word PSEGS (0x95728 : word) = Some W_95728.
Proof. vm_refl. Qed.
Lemma D_95728 : decode_any W_95728 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9572c : bv 32 := 0xe8010113.
Lemma F_9572c : fetch_word PSEGS (0x9572c : word) = Some W_9572c.
Proof. vm_refl. Qed.
Lemma D_9572c : decode_any W_9572c = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95730 : bv 32 := 0x16113c23.
Lemma F_95730 : fetch_word PSEGS (0x95730 : word) = Some W_95730.
Proof. vm_refl. Qed.
Lemma D_95730 : decode_any W_95730 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95734 : bv 32 := 0x16813823.
Lemma F_95734 : fetch_word PSEGS (0x95734 : word) = Some W_95734.
Proof. vm_refl. Qed.
Lemma D_95734 : decode_any W_95734 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95738 : bv 32 := 0x16913423.
Lemma F_95738 : fetch_word PSEGS (0x95738 : word) = Some W_95738.
Proof. vm_refl. Qed.
Lemma D_95738 : decode_any W_95738 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9573c : bv 32 := 0x17213023.
Lemma F_9573c : fetch_word PSEGS (0x9573c : word) = Some W_9573c.
Proof. vm_refl. Qed.
Lemma D_9573c : decode_any W_9573c = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95740 : bv 32 := 0x00058413.
Lemma F_95740 : fetch_word PSEGS (0x95740 : word) = Some W_95740.
Proof. vm_refl. Qed.
Lemma D_95740 : decode_any W_95740 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95744 : bv 32 := 0x00050493.
Lemma F_95744 : fetch_word PSEGS (0x95744 : word) = Some W_95744.
Proof. vm_refl. Qed.
Lemma D_95744 : decode_any W_95744 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95748 : bv 32 := 0x03010513.
Lemma F_95748 : fetch_word PSEGS (0x95748 : word) = Some W_95748.
Proof. vm_refl. Qed.
Lemma D_95748 : decode_any W_95748 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9574c : bv 32 := 0x13000613.
Lemma F_9574c : fetch_word PSEGS (0x9574c : word) = Some W_9574c.
Proof. vm_refl. Qed.
Lemma D_9574c : decode_any W_9574c = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95750 : bv 32 := 0x00000593.
Lemma F_95750 : fetch_word PSEGS (0x95750 : word) = Some W_95750.
Proof. vm_refl. Qed.
Lemma D_95750 : decode_any W_95750 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95754 : bv 32 := 0x554110ef.
Lemma F_95754 : fetch_word PSEGS (0x95754 : word) = Some W_95754.
Proof. vm_refl. Qed.
Lemma D_95754 : decode_any W_95754 = Some (Jal 1 70996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95758 : bv 32 := 0x0001c517.
Lemma F_95758 : fetch_word PSEGS (0x95758 : word) = Some W_95758.
Proof. vm_refl. Qed.
Lemma D_95758 : decode_any W_95758 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9575c : bv 32 := 0x43053503.
Lemma F_9575c : fetch_word PSEGS (0x9575c : word) = Some W_9575c.
Proof. vm_refl. Qed.
Lemma D_9575c : decode_any W_9575c = Some (Load SZ8 true 10 10 1072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95760 : bv 32 := 0x00953023.
Lemma F_95760 : fetch_word PSEGS (0x95760 : word) = Some W_95760.
Proof. vm_refl. Qed.
Lemma D_95760 : decode_any W_95760 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95764 : bv 32 := 0x0004b503.
Lemma F_95764 : fetch_word PSEGS (0x95764 : word) = Some W_95764.
Proof. vm_refl. Qed.
Lemma D_95764 : decode_any W_95764 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95768 : bv 32 := 0x00848493.
Lemma F_95768 : fetch_word PSEGS (0x95768 : word) = Some W_95768.
Proof. vm_refl. Qed.
Lemma D_95768 : decode_any W_95768 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9576c : bv 32 := 0xfe051ce3.
Lemma F_9576c : fetch_word PSEGS (0x9576c : word) = Some W_9576c.
Proof. vm_refl. Qed.
Lemma D_9576c : decode_any W_9576c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95770 : bv 32 := 0x0004f517.
Lemma F_95770 : fetch_word PSEGS (0x95770 : word) = Some W_95770.
Proof. vm_refl. Qed.
Lemma D_95770 : decode_any W_95770 = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95774 : bv 32 := 0x43850913.
Lemma F_95774 : fetch_word PSEGS (0x95774 : word) = Some W_95774.
Proof. vm_refl. Qed.
Lemma D_95774 : decode_any W_95774 = Some (OpImm ALU_ADD 18 10 1080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95778 : bv 32 := 0x00993423.
Lemma F_95778 : fetch_word PSEGS (0x95778 : word) = Some W_95778.
Proof. vm_refl. Qed.
Lemma D_95778 : decode_any W_95778 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9577c : bv 32 := 0x0004b583.
Lemma F_9577c : fetch_word PSEGS (0x9577c : word) = Some W_9577c.
Proof. vm_refl. Qed.
Lemma D_9577c : decode_any W_9577c = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95780 : bv 32 := 0x04058c63.
Lemma F_95780 : fetch_word PSEGS (0x95780 : word) = Some W_95780.
Proof. vm_refl. Qed.
Lemma D_95780 : decode_any W_95780 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95784 : bv 32 := 0x01048493.
Lemma F_95784 : fetch_word PSEGS (0x95784 : word) = Some W_95784.
Proof. vm_refl. Qed.
Lemma D_95784 : decode_any W_95784 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95788 : bv 32 := 0x02500513.
Lemma F_95788 : fetch_word PSEGS (0x95788 : word) = Some W_95788.
Proof. vm_refl. Qed.
Lemma D_95788 : decode_any W_95788 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9578c : bv 32 := 0x03010613.
Lemma F_9578c : fetch_word PSEGS (0x9578c : word) = Some W_9578c.
Proof. vm_refl. Qed.
Lemma D_9578c : decode_any W_9578c = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95790 : bv 32 := 0x0100006f.
Lemma F_95790 : fetch_word PSEGS (0x95790 : word) = Some W_95790.
Proof. vm_refl. Qed.
Lemma D_95790 : decode_any W_95790 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95794 : bv 32 := 0x0004b583.
Lemma F_95794 : fetch_word PSEGS (0x95794 : word) = Some W_95794.
Proof. vm_refl. Qed.
Lemma D_95794 : decode_any W_95794 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95798 : bv 32 := 0x01048493.
Lemma F_95798 : fetch_word PSEGS (0x95798 : word) = Some W_95798.
Proof. vm_refl. Qed.
Lemma D_95798 : decode_any W_95798 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9579c : bv 32 := 0x00058e63.
Lemma F_9579c : fetch_word PSEGS (0x9579c : word) = Some W_9579c.
Proof. vm_refl. Qed.
Lemma D_9579c : decode_any W_9579c = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957a0 : bv 32 := 0xfeb56ae3.
Lemma F_957a0 : fetch_word PSEGS (0x957a0 : word) = Some W_957a0.
Proof. vm_refl. Qed.
Lemma D_957a0 : decode_any W_957a0 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957a4 : bv 32 := 0xff84b683.
Lemma F_957a4 : fetch_word PSEGS (0x957a4 : word) = Some W_957a4.
Proof. vm_refl. Qed.
Lemma D_957a4 : decode_any W_957a4 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957a8 : bv 32 := 0x00359593.
Lemma F_957a8 : fetch_word PSEGS (0x957a8 : word) = Some W_957a8.
Proof. vm_refl. Qed.
Lemma D_957a8 : decode_any W_957a8 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957ac : bv 32 := 0x00b605b3.
Lemma F_957ac : fetch_word PSEGS (0x957ac : word) = Some W_957ac.
Proof. vm_refl. Qed.
Lemma D_957ac : decode_any W_957ac = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957b0 : bv 32 := 0x00d5b023.
Lemma F_957b0 : fetch_word PSEGS (0x957b0 : word) = Some W_957b0.
Proof. vm_refl. Qed.
Lemma D_957b0 : decode_any W_957b0 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957b4 : bv 32 := 0xfe1ff06f.
Lemma F_957b4 : fetch_word PSEGS (0x957b4 : word) = Some W_957b4.
Proof. vm_refl. Qed.
Lemma D_957b4 : decode_any W_957b4 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957b8 : bv 32 := 0x0b013583.
Lemma F_957b8 : fetch_word PSEGS (0x957b8 : word) = Some W_957b8.
Proof. vm_refl. Qed.
Lemma D_957b8 : decode_any W_957b8 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957bc : bv 32 := 0x13013503.
Lemma F_957bc : fetch_word PSEGS (0x957bc : word) = Some W_957bc.
Proof. vm_refl. Qed.
Lemma D_957bc : decode_any W_957bc = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957c0 : bv 32 := 0x0004f617.
Lemma F_957c0 : fetch_word PSEGS (0x957c0 : word) = Some W_957c0.
Proof. vm_refl. Qed.
Lemma D_957c0 : decode_any W_957c0 = Some (Auipc 12 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957c4 : bv 32 := 0x44b63823.
Lemma F_957c4 : fetch_word PSEGS (0x957c4 : word) = Some W_957c4.
Proof. vm_refl. Qed.
Lemma D_957c4 : decode_any W_957c4 = Some (Store SZ8 12 11 1104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957c8 : bv 32 := 0x00050c63.
Lemma F_957c8 : fetch_word PSEGS (0x957c8 : word) = Some W_957c8.
Proof. vm_refl. Qed.
Lemma D_957c8 : decode_any W_957c8 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957e0 : bv 32 := 0x06013503.
Lemma F_957e0 : fetch_word PSEGS (0x957e0 : word) = Some W_957e0.
Proof. vm_refl. Qed.
Lemma D_957e0 : decode_any W_957e0 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957e4 : bv 32 := 0x02a93823.
Lemma F_957e4 : fetch_word PSEGS (0x957e4 : word) = Some W_957e4.
Proof. vm_refl. Qed.
Lemma D_957e4 : decode_any W_957e4 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957e8 : bv 32 := 0x00041463.
Lemma F_957e8 : fetch_word PSEGS (0x957e8 : word) = Some W_957e8.
Proof. vm_refl. Qed.
Lemma D_957e8 : decode_any W_957e8 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957f0 : bv 32 := 0x00041663.
Lemma F_957f0 : fetch_word PSEGS (0x957f0 : word) = Some W_957f0.
Proof. vm_refl. Qed.
Lemma D_957f0 : decode_any W_957f0 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_957fc : bv 32 := 0x0001c517.
Lemma F_957fc : fetch_word PSEGS (0x957fc : word) = Some W_957fc.
Proof. vm_refl. Qed.
Lemma D_957fc : decode_any W_957fc = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95800 : bv 32 := 0x39453583.
Lemma F_95800 : fetch_word PSEGS (0x95800 : word) = Some W_95800.
Proof. vm_refl. Qed.
Lemma D_95800 : decode_any W_95800 = Some (Load SZ8 true 11 10 916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95804 : bv 32 := 0x0001c517.
Lemma F_95804 : fetch_word PSEGS (0x95804 : word) = Some W_95804.
Proof. vm_refl. Qed.
Lemma D_95804 : decode_any W_95804 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95808 : bv 32 := 0x39453503.
Lemma F_95808 : fetch_word PSEGS (0x95808 : word) = Some W_95808.
Proof. vm_refl. Qed.
Lemma D_95808 : decode_any W_95808 = Some (Load SZ8 true 10 10 916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9580c : bv 32 := 0x0085b023.
Lemma F_9580c : fetch_word PSEGS (0x9580c : word) = Some W_9580c.
Proof. vm_refl. Qed.
Lemma D_9580c : decode_any W_9580c = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95810 : bv 32 := 0x00140593.
Lemma F_95810 : fetch_word PSEGS (0x95810 : word) = Some W_95810.
Proof. vm_refl. Qed.
Lemma D_95810 : decode_any W_95810 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95814 : bv 32 := 0x00853023.
Lemma F_95814 : fetch_word PSEGS (0x95814 : word) = Some W_95814.
Proof. vm_refl. Qed.
Lemma D_95814 : decode_any W_95814 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95818 : bv 32 := 0x02f00613.
Lemma F_95818 : fetch_word PSEGS (0x95818 : word) = Some W_95818.
Proof. vm_refl. Qed.
Lemma D_95818 : decode_any W_95818 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9581c : bv 32 := 0x00c0006f.
Lemma F_9581c : fetch_word PSEGS (0x9581c : word) = Some W_9581c.
Proof. vm_refl. Qed.
Lemma D_9581c : decode_any W_9581c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95820 : bv 32 := 0x00b53023.
Lemma F_95820 : fetch_word PSEGS (0x95820 : word) = Some W_95820.
Proof. vm_refl. Qed.
Lemma D_95820 : decode_any W_95820 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95824 : bv 32 := 0x00158593.
Lemma F_95824 : fetch_word PSEGS (0x95824 : word) = Some W_95824.
Proof. vm_refl. Qed.
Lemma D_95824 : decode_any W_95824 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95828 : bv 32 := 0xfff5c683.
Lemma F_95828 : fetch_word PSEGS (0x95828 : word) = Some W_95828.
Proof. vm_refl. Qed.
Lemma D_95828 : decode_any W_95828 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9582c : bv 32 := 0xfec68ae3.
Lemma F_9582c : fetch_word PSEGS (0x9582c : word) = Some W_9582c.
Proof. vm_refl. Qed.
Lemma D_9582c : decode_any W_9582c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95830 : bv 32 := 0xfe069ae3.
Lemma F_95830 : fetch_word PSEGS (0x95830 : word) = Some W_95830.
Proof. vm_refl. Qed.
Lemma D_95830 : decode_any W_95830 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95834 : bv 32 := 0x03010513.
Lemma F_95834 : fetch_word PSEGS (0x95834 : word) = Some W_95834.
Proof. vm_refl. Qed.
Lemma D_95834 : decode_any W_95834 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95838 : bv 32 := 0x214000ef.
Lemma F_95838 : fetch_word PSEGS (0x95838 : word) = Some W_95838.
Proof. vm_refl. Qed.
Lemma D_95838 : decode_any W_95838 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9583c : bv 32 := 0x0f813503.
Lemma F_9583c : fetch_word PSEGS (0x9583c : word) = Some W_9583c.
Proof. vm_refl. Qed.
Lemma D_9583c : decode_any W_9583c = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95840 : bv 32 := 0x1ad000ef.
Lemma F_95840 : fetch_word PSEGS (0x95840 : word) = Some W_95840.
Proof. vm_refl. Qed.
Lemma D_95840 : decode_any W_95840 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95844 : bv 32 := 0x08813503.
Lemma F_95844 : fetch_word PSEGS (0x95844 : word) = Some W_95844.
Proof. vm_refl. Qed.
Lemma D_95844 : decode_any W_95844 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95848 : bv 32 := 0x09013583.
Lemma F_95848 : fetch_word PSEGS (0x95848 : word) = Some W_95848.
Proof. vm_refl. Qed.
Lemma D_95848 : decode_any W_95848 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9584c : bv 32 := 0x00b51c63.
Lemma F_9584c : fetch_word PSEGS (0x9584c : word) = Some W_9584c.
Proof. vm_refl. Qed.
Lemma D_9584c : decode_any W_9584c = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95850 : bv 32 := 0x09813503.
Lemma F_95850 : fetch_word PSEGS (0x95850 : word) = Some W_95850.
Proof. vm_refl. Qed.
Lemma D_95850 : decode_any W_95850 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95854 : bv 32 := 0x0a013583.
Lemma F_95854 : fetch_word PSEGS (0x95854 : word) = Some W_95854.
Proof. vm_refl. Qed.
Lemma D_95854 : decode_any W_95854 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95858 : bv 32 := 0x00b51663.
Lemma F_95858 : fetch_word PSEGS (0x95858 : word) = Some W_95858.
Proof. vm_refl. Qed.
Lemma D_95858 : decode_any W_95858 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9585c : bv 32 := 0x0e813503.
Lemma F_9585c : fetch_word PSEGS (0x9585c : word) = Some W_9585c.
Proof. vm_refl. Qed.
Lemma D_9585c : decode_any W_9585c = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95860 : bv 32 := 0x0e050063.
Lemma F_95860 : fetch_word PSEGS (0x95860 : word) = Some W_95860.
Proof. vm_refl. Qed.
Lemma D_95860 : decode_any W_95860 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95940 : bv 32 := 0x17813083.
Lemma F_95940 : fetch_word PSEGS (0x95940 : word) = Some W_95940.
Proof. vm_refl. Qed.
Lemma D_95940 : decode_any W_95940 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95944 : bv 32 := 0x17013403.
Lemma F_95944 : fetch_word PSEGS (0x95944 : word) = Some W_95944.
Proof. vm_refl. Qed.
Lemma D_95944 : decode_any W_95944 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95948 : bv 32 := 0x16813483.
Lemma F_95948 : fetch_word PSEGS (0x95948 : word) = Some W_95948.
Proof. vm_refl. Qed.
Lemma D_95948 : decode_any W_95948 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9594c : bv 32 := 0x16013903.
Lemma F_9594c : fetch_word PSEGS (0x9594c : word) = Some W_9594c.
Proof. vm_refl. Qed.
Lemma D_9594c : decode_any W_9594c = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95950 : bv 32 := 0x18010113.
Lemma F_95950 : fetch_word PSEGS (0x95950 : word) = Some W_95950.
Proof. vm_refl. Qed.
Lemma D_95950 : decode_any W_95950 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95954 : bv 32 := 0x00008067.
Lemma F_95954 : fetch_word PSEGS (0x95954 : word) = Some W_95954.
Proof. vm_refl. Qed.
Lemma D_95954 : decode_any W_95954 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95958 : bv 32 := 0xfe010113.
Lemma F_95958 : fetch_word PSEGS (0x95958 : word) = Some W_95958.
Proof. vm_refl. Qed.
Lemma D_95958 : decode_any W_95958 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9595c : bv 32 := 0x00113c23.
Lemma F_9595c : fetch_word PSEGS (0x9595c : word) = Some W_9595c.
Proof. vm_refl. Qed.
Lemma D_9595c : decode_any W_9595c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95960 : bv 32 := 0x00813823.
Lemma F_95960 : fetch_word PSEGS (0x95960 : word) = Some W_95960.
Proof. vm_refl. Qed.
Lemma D_95960 : decode_any W_95960 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95964 : bv 32 := 0x00913423.
Lemma F_95964 : fetch_word PSEGS (0x95964 : word) = Some W_95964.
Proof. vm_refl. Qed.
Lemma D_95964 : decode_any W_95964 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95968 : bv 32 := 0xdc1ff0ef.
Lemma F_95968 : fetch_word PSEGS (0x95968 : word) = Some W_95968.
Proof. vm_refl. Qed.
Lemma D_95968 : decode_any W_95968 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9596c : bv 32 := 0x0001c517.
Lemma F_9596c : fetch_word PSEGS (0x9596c : word) = Some W_9596c.
Proof. vm_refl. Qed.
Lemma D_9596c : decode_any W_9596c = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95970 : bv 32 := 0x0001c597.
Lemma F_95970 : fetch_word PSEGS (0x95970 : word) = Some W_95970.
Proof. vm_refl. Qed.
Lemma D_95970 : decode_any W_95970 = Some (Auipc 11 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95974 : bv 32 := 0x23453403.
Lemma F_95974 : fetch_word PSEGS (0x95974 : word) = Some W_95974.
Proof. vm_refl. Qed.
Lemma D_95974 : decode_any W_95974 = Some (Load SZ8 true 8 10 564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95978 : bv 32 := 0x2385b483.
Lemma F_95978 : fetch_word PSEGS (0x95978 : word) = Some W_95978.
Proof. vm_refl. Qed.
Lemma D_95978 : decode_any W_95978 = Some (Load SZ8 true 9 11 568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9597c : bv 32 := 0x0084fa63.
Lemma F_9597c : fetch_word PSEGS (0x9597c : word) = Some W_9597c.
Proof. vm_refl. Qed.
Lemma D_9597c : decode_any W_9597c = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95980 : bv 32 := 0x0004b503.
Lemma F_95980 : fetch_word PSEGS (0x95980 : word) = Some W_95980.
Proof. vm_refl. Qed.
Lemma D_95980 : decode_any W_95980 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95984 : bv 32 := 0x000500e7.
Lemma F_95984 : fetch_word PSEGS (0x95984 : word) = Some W_95984.
Proof. vm_refl. Qed.
Lemma D_95984 : decode_any W_95984 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95988 : bv 32 := 0x00848493.
Lemma F_95988 : fetch_word PSEGS (0x95988 : word) = Some W_95988.
Proof. vm_refl. Qed.
Lemma D_95988 : decode_any W_95988 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9598c : bv 32 := 0xfe84eae3.
Lemma F_9598c : fetch_word PSEGS (0x9598c : word) = Some W_9598c.
Proof. vm_refl. Qed.
Lemma D_9598c : decode_any W_9598c = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95990 : bv 32 := 0x01813083.
Lemma F_95990 : fetch_word PSEGS (0x95990 : word) = Some W_95990.
Proof. vm_refl. Qed.
Lemma D_95990 : decode_any W_95990 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95994 : bv 32 := 0x01013403.
Lemma F_95994 : fetch_word PSEGS (0x95994 : word) = Some W_95994.
Proof. vm_refl. Qed.
Lemma D_95994 : decode_any W_95994 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95998 : bv 32 := 0x00813483.
Lemma F_95998 : fetch_word PSEGS (0x95998 : word) = Some W_95998.
Proof. vm_refl. Qed.
Lemma D_95998 : decode_any W_95998 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9599c : bv 32 := 0x02010113.
Lemma F_9599c : fetch_word PSEGS (0x9599c : word) = Some W_9599c.
Proof. vm_refl. Qed.
Lemma D_9599c : decode_any W_9599c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959a0 : bv 32 := 0x00008067.
Lemma F_959a0 : fetch_word PSEGS (0x959a0 : word) = Some W_959a0.
Proof. vm_refl. Qed.
Lemma D_959a0 : decode_any W_959a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959a4 : bv 32 := 0xfe010113.
Lemma F_959a4 : fetch_word PSEGS (0x959a4 : word) = Some W_959a4.
Proof. vm_refl. Qed.
Lemma D_959a4 : decode_any W_959a4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959a8 : bv 32 := 0x00113c23.
Lemma F_959a8 : fetch_word PSEGS (0x959a8 : word) = Some W_959a8.
Proof. vm_refl. Qed.
Lemma D_959a8 : decode_any W_959a8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959ac : bv 32 := 0x00813823.
Lemma F_959ac : fetch_word PSEGS (0x959ac : word) = Some W_959ac.
Proof. vm_refl. Qed.
Lemma D_959ac : decode_any W_959ac = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959b0 : bv 32 := 0x00913423.
Lemma F_959b0 : fetch_word PSEGS (0x959b0 : word) = Some W_959b0.
Proof. vm_refl. Qed.
Lemma D_959b0 : decode_any W_959b0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959b4 : bv 32 := 0x01213023.
Lemma F_959b4 : fetch_word PSEGS (0x959b4 : word) = Some W_959b4.
Proof. vm_refl. Qed.
Lemma D_959b4 : decode_any W_959b4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959b8 : bv 32 := 0x00060413.
Lemma F_959b8 : fetch_word PSEGS (0x959b8 : word) = Some W_959b8.
Proof. vm_refl. Qed.
Lemma D_959b8 : decode_any W_959b8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959bc : bv 32 := 0x00058493.
Lemma F_959bc : fetch_word PSEGS (0x959bc : word) = Some W_959bc.
Proof. vm_refl. Qed.
Lemma D_959bc : decode_any W_959bc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959c0 : bv 32 := 0x00050913.
Lemma F_959c0 : fetch_word PSEGS (0x959c0 : word) = Some W_959c0.
Proof. vm_refl. Qed.
Lemma D_959c0 : decode_any W_959c0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959c4 : bv 32 := 0x00063583.
Lemma F_959c4 : fetch_word PSEGS (0x959c4 : word) = Some W_959c4.
Proof. vm_refl. Qed.
Lemma D_959c4 : decode_any W_959c4 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959c8 : bv 32 := 0x00349513.
Lemma F_959c8 : fetch_word PSEGS (0x959c8 : word) = Some W_959c8.
Proof. vm_refl. Qed.
Lemma D_959c8 : decode_any W_959c8 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959cc : bv 32 := 0x00a60533.
Lemma F_959cc : fetch_word PSEGS (0x959cc : word) = Some W_959cc.
Proof. vm_refl. Qed.
Lemma D_959cc : decode_any W_959cc = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959d0 : bv 32 := 0x00850513.
Lemma F_959d0 : fetch_word PSEGS (0x959d0 : word) = Some W_959d0.
Proof. vm_refl. Qed.
Lemma D_959d0 : decode_any W_959d0 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959d4 : bv 32 := 0xd59ff0ef.
Lemma F_959d4 : fetch_word PSEGS (0x959d4 : word) = Some W_959d4.
Proof. vm_refl. Qed.
Lemma D_959d4 : decode_any W_959d4 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959d8 : bv 32 := 0x00000517.
Lemma F_959d8 : fetch_word PSEGS (0x959d8 : word) = Some W_959d8.
Proof. vm_refl. Qed.
Lemma D_959d8 : decode_any W_959d8 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959dc : bv 32 := 0x02c50313.
Lemma F_959dc : fetch_word PSEGS (0x959dc : word) = Some W_959dc.
Proof. vm_refl. Qed.
Lemma D_959dc : decode_any W_959dc = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959e0 : bv 32 := 0x00090513.
Lemma F_959e0 : fetch_word PSEGS (0x959e0 : word) = Some W_959e0.
Proof. vm_refl. Qed.
Lemma D_959e0 : decode_any W_959e0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959e4 : bv 32 := 0x00048593.
Lemma F_959e4 : fetch_word PSEGS (0x959e4 : word) = Some W_959e4.
Proof. vm_refl. Qed.
Lemma D_959e4 : decode_any W_959e4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959e8 : bv 32 := 0x00040613.
Lemma F_959e8 : fetch_word PSEGS (0x959e8 : word) = Some W_959e8.
Proof. vm_refl. Qed.
Lemma D_959e8 : decode_any W_959e8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959ec : bv 32 := 0x01813083.
Lemma F_959ec : fetch_word PSEGS (0x959ec : word) = Some W_959ec.
Proof. vm_refl. Qed.
Lemma D_959ec : decode_any W_959ec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959f0 : bv 32 := 0x01013403.
Lemma F_959f0 : fetch_word PSEGS (0x959f0 : word) = Some W_959f0.
Proof. vm_refl. Qed.
Lemma D_959f0 : decode_any W_959f0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959f4 : bv 32 := 0x00813483.
Lemma F_959f4 : fetch_word PSEGS (0x959f4 : word) = Some W_959f4.
Proof. vm_refl. Qed.
Lemma D_959f4 : decode_any W_959f4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959f8 : bv 32 := 0x00013903.
Lemma F_959f8 : fetch_word PSEGS (0x959f8 : word) = Some W_959f8.
Proof. vm_refl. Qed.
Lemma D_959f8 : decode_any W_959f8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_959fc : bv 32 := 0x02010113.
Lemma F_959fc : fetch_word PSEGS (0x959fc : word) = Some W_959fc.
Proof. vm_refl. Qed.
Lemma D_959fc : decode_any W_959fc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a00 : bv 32 := 0x00030067.
Lemma F_95a00 : fetch_word PSEGS (0x95a00 : word) = Some W_95a00.
Proof. vm_refl. Qed.
Lemma D_95a00 : decode_any W_95a00 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a04 : bv 32 := 0xfd010113.
Lemma F_95a04 : fetch_word PSEGS (0x95a04 : word) = Some W_95a04.
Proof. vm_refl. Qed.
Lemma D_95a04 : decode_any W_95a04 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a08 : bv 32 := 0x02113423.
Lemma F_95a08 : fetch_word PSEGS (0x95a08 : word) = Some W_95a08.
Proof. vm_refl. Qed.
Lemma D_95a08 : decode_any W_95a08 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a0c : bv 32 := 0x02813023.
Lemma F_95a0c : fetch_word PSEGS (0x95a0c : word) = Some W_95a0c.
Proof. vm_refl. Qed.
Lemma D_95a0c : decode_any W_95a0c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a10 : bv 32 := 0x00913c23.
Lemma F_95a10 : fetch_word PSEGS (0x95a10 : word) = Some W_95a10.
Proof. vm_refl. Qed.
Lemma D_95a10 : decode_any W_95a10 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a14 : bv 32 := 0x01213823.
Lemma F_95a14 : fetch_word PSEGS (0x95a14 : word) = Some W_95a14.
Proof. vm_refl. Qed.
Lemma D_95a14 : decode_any W_95a14 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a18 : bv 32 := 0x01313423.
Lemma F_95a18 : fetch_word PSEGS (0x95a18 : word) = Some W_95a18.
Proof. vm_refl. Qed.
Lemma D_95a18 : decode_any W_95a18 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a1c : bv 32 := 0x00060413.
Lemma F_95a1c : fetch_word PSEGS (0x95a1c : word) = Some W_95a1c.
Proof. vm_refl. Qed.
Lemma D_95a1c : decode_any W_95a1c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a20 : bv 32 := 0x00058493.
Lemma F_95a20 : fetch_word PSEGS (0x95a20 : word) = Some W_95a20.
Proof. vm_refl. Qed.
Lemma D_95a20 : decode_any W_95a20 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a24 : bv 32 := 0x00050913.
Lemma F_95a24 : fetch_word PSEGS (0x95a24 : word) = Some W_95a24.
Proof. vm_refl. Qed.
Lemma D_95a24 : decode_any W_95a24 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a28 : bv 32 := 0x00359513.
Lemma F_95a28 : fetch_word PSEGS (0x95a28 : word) = Some W_95a28.
Proof. vm_refl. Qed.
Lemma D_95a28 : decode_any W_95a28 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a2c : bv 32 := 0x00a60533.
Lemma F_95a2c : fetch_word PSEGS (0x95a2c : word) = Some W_95a2c.
Proof. vm_refl. Qed.
Lemma D_95a2c : decode_any W_95a2c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a30 : bv 32 := 0x00850993.
Lemma F_95a30 : fetch_word PSEGS (0x95a30 : word) = Some W_95a30.
Proof. vm_refl. Qed.
Lemma D_95a30 : decode_any W_95a30 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a34 : bv 32 := 0xf25ff0ef.
Lemma F_95a34 : fetch_word PSEGS (0x95a34 : word) = Some W_95a34.
Proof. vm_refl. Qed.
Lemma D_95a34 : decode_any W_95a34 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a38 : bv 32 := 0x00048513.
Lemma F_95a38 : fetch_word PSEGS (0x95a38 : word) = Some W_95a38.
Proof. vm_refl. Qed.
Lemma D_95a38 : decode_any W_95a38 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a3c : bv 32 := 0x00040593.
Lemma F_95a3c : fetch_word PSEGS (0x95a3c : word) = Some W_95a3c.
Proof. vm_refl. Qed.
Lemma D_95a3c : decode_any W_95a3c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a40 : bv 32 := 0x00098613.
Lemma F_95a40 : fetch_word PSEGS (0x95a40 : word) = Some W_95a40.
Proof. vm_refl. Qed.
Lemma D_95a40 : decode_any W_95a40 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a44 : bv 32 := 0x000900e7.
Lemma F_95a44 : fetch_word PSEGS (0x95a44 : word) = Some W_95a44.
Proof. vm_refl. Qed.
Lemma D_95a44 : decode_any W_95a44 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a4c : bv 32 := 0xfc010113.
Lemma F_95a4c : fetch_word PSEGS (0x95a4c : word) = Some W_95a4c.
Proof. vm_refl. Qed.
Lemma D_95a4c : decode_any W_95a4c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a50 : bv 32 := 0x02113c23.
Lemma F_95a50 : fetch_word PSEGS (0x95a50 : word) = Some W_95a50.
Proof. vm_refl. Qed.
Lemma D_95a50 : decode_any W_95a50 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a54 : bv 32 := 0x02813823.
Lemma F_95a54 : fetch_word PSEGS (0x95a54 : word) = Some W_95a54.
Proof. vm_refl. Qed.
Lemma D_95a54 : decode_any W_95a54 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a58 : bv 32 := 0x02913423.
Lemma F_95a58 : fetch_word PSEGS (0x95a58 : word) = Some W_95a58.
Proof. vm_refl. Qed.
Lemma D_95a58 : decode_any W_95a58 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a5c : bv 32 := 0x03213023.
Lemma F_95a5c : fetch_word PSEGS (0x95a5c : word) = Some W_95a5c.
Proof. vm_refl. Qed.
Lemma D_95a5c : decode_any W_95a5c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a60 : bv 32 := 0x01313c23.
Lemma F_95a60 : fetch_word PSEGS (0x95a60 : word) = Some W_95a60.
Proof. vm_refl. Qed.
Lemma D_95a60 : decode_any W_95a60 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a64 : bv 32 := 0x01413823.
Lemma F_95a64 : fetch_word PSEGS (0x95a64 : word) = Some W_95a64.
Proof. vm_refl. Qed.
Lemma D_95a64 : decode_any W_95a64 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a68 : bv 32 := 0x01513423.
Lemma F_95a68 : fetch_word PSEGS (0x95a68 : word) = Some W_95a68.
Proof. vm_refl. Qed.
Lemma D_95a68 : decode_any W_95a68 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a6c : bv 32 := 0x02853683.
Lemma F_95a6c : fetch_word PSEGS (0x95a6c : word) = Some W_95a6c.
Proof. vm_refl. Qed.
Lemma D_95a6c : decode_any W_95a6c = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a70 : bv 32 := 0x0004f597.
Lemma F_95a70 : fetch_word PSEGS (0x95a70 : word) = Some W_95a70.
Proof. vm_refl. Qed.
Lemma D_95a70 : decode_any W_95a70 = Some (Auipc 11 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_95a80 : bv 32 := 0x0c068e63.
Lemma F_95a80 : fetch_word PSEGS (0x95a80 : word) = Some W_95a80.
Proof. vm_refl. Qed.
Lemma D_95a80 : decode_any W_95a80 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_95a88 : bv 32 := 0x00000893.
Lemma F_95a88 : fetch_word PSEGS (0x95a88 : word) = Some W_95a88.
Proof. vm_refl. Qed.
Lemma D_95a88 : decode_any W_95a88 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a8c : bv 32 := 0x0001d717.
Lemma F_95a8c : fetch_word PSEGS (0x95a8c : word) = Some W_95a8c.
Proof. vm_refl. Qed.
Lemma D_95a8c : decode_any W_95a8c = Some (Auipc 14 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a90 : bv 32 := 0x01853783.
Lemma F_95a90 : fetch_word PSEGS (0x95a90 : word) = Some W_95a90.
Proof. vm_refl. Qed.
Lemma D_95a90 : decode_any W_95a90 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a94 : bv 32 := 0x02053503.
Lemma F_95a94 : fetch_word PSEGS (0x95a94 : word) = Some W_95a94.
Proof. vm_refl. Qed.
Lemma D_95a94 : decode_any W_95a94 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a98 : bv 32 := 0x00600813.
Lemma F_95a98 : fetch_word PSEGS (0x95a98 : word) = Some W_95a98.
Proof. vm_refl. Qed.
Lemma D_95a98 : decode_any W_95a98 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95a9c : bv 32 := 0x0001c297.
Lemma F_95a9c : fetch_word PSEGS (0x95a9c : word) = Some W_95a9c.
Proof. vm_refl. Qed.
Lemma D_95a9c : decode_any W_95a9c = Some (Auipc 5 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95aa0 : bv 32 := 0x3f476f03.
Lemma F_95aa0 : fetch_word PSEGS (0x95aa0 : word) = Some W_95aa0.
Proof. vm_refl. Qed.
Lemma D_95aa0 : decode_any W_95aa0 = Some (Load SZ4 false 30 14 1012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95aa4 : bv 32 := 0xfac2b283.
Lemma F_95aa4 : fetch_word PSEGS (0x95aa4 : word) = Some W_95aa4.
Proof. vm_refl. Qed.
Lemma D_95aa4 : decode_any W_95aa4 = Some (Load SZ8 true 5 5 4012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95aa8 : bv 32 := 0x00200313.
Lemma F_95aa8 : fetch_word PSEGS (0x95aa8 : word) = Some W_95aa8.
Proof. vm_refl. Qed.
Lemma D_95aa8 : decode_any W_95aa8 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95aac : bv 32 := 0x00700393.
Lemma F_95aac : fetch_word PSEGS (0x95aac : word) = Some W_95aac.
Proof. vm_refl. Qed.
Lemma D_95aac : decode_any W_95aac = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ab0 : bv 32 := 0x6474ee37.
Lemma F_95ab0 : fetch_word PSEGS (0x95ab0 : word) = Some W_95ab0.
Proof. vm_refl. Qed.
Lemma D_95ab0 : decode_any W_95ab0 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ab4 : bv 32 := 0x551e0e1b.
Lemma F_95ab4 : fetch_word PSEGS (0x95ab4 : word) = Some W_95ab4.
Proof. vm_refl. Qed.
Lemma D_95ab4 : decode_any W_95ab4 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ab8 : bv 32 := 0x00078e93.
Lemma F_95ab8 : fetch_word PSEGS (0x95ab8 : word) = Some W_95ab8.
Proof. vm_refl. Qed.
Lemma D_95ab8 : decode_any W_95ab8 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95abc : bv 32 := 0x0180006f.
Lemma F_95abc : fetch_word PSEGS (0x95abc : word) = Some W_95abc.
Proof. vm_refl. Qed.
Lemma D_95abc : decode_any W_95abc = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_95ac8 : bv 32 := 0xfff68693.
Lemma F_95ac8 : fetch_word PSEGS (0x95ac8 : word) = Some W_95ac8.
Proof. vm_refl. Qed.
Lemma D_95ac8 : decode_any W_95ac8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95acc : bv 32 := 0x00ae8eb3.
Lemma F_95acc : fetch_word PSEGS (0x95acc : word) = Some W_95acc.
Proof. vm_refl. Qed.
Lemma D_95acc : decode_any W_95acc = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ad0 : bv 32 := 0x04068a63.
Lemma F_95ad0 : fetch_word PSEGS (0x95ad0 : word) = Some W_95ad0.
Proof. vm_refl. Qed.
Lemma D_95ad0 : decode_any W_95ad0 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ad4 : bv 32 := 0x000ea403.
Lemma F_95ad4 : fetch_word PSEGS (0x95ad4 : word) = Some W_95ad4.
Proof. vm_refl. Qed.
Lemma D_95ad4 : decode_any W_95ad4 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ad8 : bv 32 := 0xff0404e3.
Lemma F_95ad8 : fetch_word PSEGS (0x95ad8 : word) = Some W_95ad8.
Proof. vm_refl. Qed.
Lemma D_95ad8 : decode_any W_95ad8 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95adc : bv 32 := 0x00028a63.
Lemma F_95adc : fetch_word PSEGS (0x95adc : word) = Some W_95adc.
Proof. vm_refl. Qed.
Lemma D_95adc : decode_any W_95adc = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95af0 : bv 32 := 0x000e8f93.
Lemma F_95af0 : fetch_word PSEGS (0x95af0 : word) = Some W_95af0.
Proof. vm_refl. Qed.
Lemma D_95af0 : decode_any W_95af0 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95af4 : bv 32 := 0x00740463.
Lemma F_95af4 : fetch_word PSEGS (0x95af4 : word) = Some W_95af4.
Proof. vm_refl. Qed.
Lemma D_95af4 : decode_any W_95af4 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95af8 : bv 32 := 0x00088f93.
Lemma F_95af8 : fetch_word PSEGS (0x95af8 : word) = Some W_95af8.
Proof. vm_refl. Qed.
Lemma D_95af8 : decode_any W_95af8 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95afc : bv 32 := 0x03c41063.
Lemma F_95afc : fetch_word PSEGS (0x95afc : word) = Some W_95afc.
Proof. vm_refl. Qed.
Lemma D_95afc : decode_any W_95afc = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b00 : bv 32 := 0x028eb883.
Lemma F_95b00 : fetch_word PSEGS (0x95b00 : word) = Some W_95b00.
Proof. vm_refl. Qed.
Lemma D_95b00 : decode_any W_95b00 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b04 : bv 32 := 0x011f7c63.
Lemma F_95b04 : fetch_word PSEGS (0x95b04 : word) = Some W_95b04.
Proof. vm_refl. Qed.
Lemma D_95b04 : decode_any W_95b04 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b1c : bv 32 := 0x000f8893.
Lemma F_95b1c : fetch_word PSEGS (0x95b1c : word) = Some W_95b1c.
Proof. vm_refl. Qed.
Lemma D_95b1c : decode_any W_95b1c = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b20 : bv 32 := 0xfa9ff06f.
Lemma F_95b20 : fetch_word PSEGS (0x95b20 : word) = Some W_95b20.
Proof. vm_refl. Qed.
Lemma D_95b20 : decode_any W_95b20 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b24 : bv 32 := 0x02088c63.
Lemma F_95b24 : fetch_word PSEGS (0x95b24 : word) = Some W_95b24.
Proof. vm_refl. Qed.
Lemma D_95b24 : decode_any W_95b24 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_95b6c : bv 32 := 0xfff50793.
Lemma F_95b6c : fetch_word PSEGS (0x95b6c : word) = Some W_95b6c.
Proof. vm_refl. Qed.
Lemma D_95b6c : decode_any W_95b6c = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b70 : bv 32 := 0x40e00733.
Lemma F_95b70 : fetch_word PSEGS (0x95b70 : word) = Some W_95b70.
Proof. vm_refl. Qed.
Lemma D_95b70 : decode_any W_95b70 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_95b78 : bv 32 := 0x00e7f733.
Lemma F_95b78 : fetch_word PSEGS (0x95b78 : word) = Some W_95b78.
Proof. vm_refl. Qed.
Lemma D_95b78 : decode_any W_95b78 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b7c : bv 32 := 0x00700793.
Lemma F_95b7c : fetch_word PSEGS (0x95b7c : word) = Some W_95b7c.
Proof. vm_refl. Qed.
Lemma D_95b7c : decode_any W_95b7c = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b80 : bv 32 := 0x00d706b3.
Lemma F_95b80 : fetch_word PSEGS (0x95b80 : word) = Some W_95b80.
Proof. vm_refl. Qed.
Lemma D_95b80 : decode_any W_95b80 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_95b8c : bv 32 := 0x00a7e663.
Lemma F_95b8c : fetch_word PSEGS (0x95b8c : word) = Some W_95b8c.
Proof. vm_refl. Qed.
Lemma D_95b8c : decode_any W_95b8c = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95b90 : bv 32 := 0x00800513.
Lemma F_95b90 : fetch_word PSEGS (0x95b90 : word) = Some W_95b90.
Proof. vm_refl. Qed.
Lemma D_95b90 : decode_any W_95b90 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_95bac : bv 32 := 0xff85f593.
Lemma F_95bac : fetch_word PSEGS (0x95bac : word) = Some W_95bac.
Proof. vm_refl. Qed.
Lemma D_95bac : decode_any W_95bac = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95bb0 : bv 32 := 0x00b4bc23.
Lemma F_95bb0 : fetch_word PSEGS (0x95bb0 : word) = Some W_95bb0.
Proof. vm_refl. Qed.
Lemma D_95bb0 : decode_any W_95bb0 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95bb4 : bv 32 := 0x02a4b023.
Lemma F_95bb4 : fetch_word PSEGS (0x95bb4 : word) = Some W_95bb4.
Proof. vm_refl. Qed.
Lemma D_95bb4 : decode_any W_95bb4 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95bb8 : bv 32 := 0x02d5ea63.
Lemma F_95bb8 : fetch_word PSEGS (0x95bb8 : word) = Some W_95bb8.
Proof. vm_refl. Qed.
Lemma D_95bb8 : decode_any W_95bb8 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_95bf4 : bv 32 := 0x0284b603.
Lemma F_95bf4 : fetch_word PSEGS (0x95bf4 : word) = Some W_95bf4.
Proof. vm_refl. Qed.
Lemma D_95bf4 : decode_any W_95bf4 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_95c20 : bv 32 := 0x0c890413.
Lemma F_95c20 : fetch_word PSEGS (0x95c20 : word) = Some W_95c20.
Proof. vm_refl. Qed.
Lemma D_95c20 : decode_any W_95c20 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_95c74 : bv 32 := 0x01293023.
Lemma F_95c74 : fetch_word PSEGS (0x95c74 : word) = Some W_95c74.
Proof. vm_refl. Qed.
Lemma D_95c74 : decode_any W_95c74 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95c78 : bv 32 := 0x00040513.
Lemma F_95c78 : fetch_word PSEGS (0x95c78 : word) = Some W_95c78.
Proof. vm_refl. Qed.
Lemma D_95c78 : decode_any W_95c78 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95c7c : bv 32 := 0x0d4130ef.
Lemma F_95c7c : fetch_word PSEGS (0x95c7c : word) = Some W_95c7c.
Proof. vm_refl. Qed.
Lemma D_95c7c : decode_any W_95c7c = Some (Jal 1 78036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95c80 : bv 32 := 0x04054a63.
Lemma F_95c80 : fetch_word PSEGS (0x95c80 : word) = Some W_95c80.
Proof. vm_refl. Qed.
Lemma D_95c80 : decode_any W_95c80 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95c84 : bv 32 := 0x00051663.
Lemma F_95c84 : fetch_word PSEGS (0x95c84 : word) = Some W_95c84.
Proof. vm_refl. Qed.
Lemma D_95c84 : decode_any W_95c84 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95c88 : bv 32 := 0x00100513.
Lemma F_95c88 : fetch_word PSEGS (0x95c88 : word) = Some W_95c88.
Proof. vm_refl. Qed.
Lemma D_95c88 : decode_any W_95c88 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95c8c : bv 32 := 0x00a48023.
Lemma F_95c8c : fetch_word PSEGS (0x95c8c : word) = Some W_95c8c.
Proof. vm_refl. Qed.
Lemma D_95c8c : decode_any W_95c8c = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95c90 : bv 32 := 0x00200513.
Lemma F_95c90 : fetch_word PSEGS (0x95c90 : word) = Some W_95c90.
Proof. vm_refl. Qed.
Lemma D_95c90 : decode_any W_95c90 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95c94 : bv 32 := 0x0004f597.
Lemma F_95c94 : fetch_word PSEGS (0x95c94 : word) = Some W_95c94.
Proof. vm_refl. Qed.
Lemma D_95c94 : decode_any W_95c94 = Some (Auipc 11 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95c98 : bv 32 := 0x02a92423.
Lemma F_95c98 : fetch_word PSEGS (0x95c98 : word) = Some W_95c98.
Proof. vm_refl. Qed.
Lemma D_95c98 : decode_any W_95c98 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95c9c : bv 32 := 0x06000893.
Lemma F_95c9c : fetch_word PSEGS (0x95c9c : word) = Some W_95c9c.
Proof. vm_refl. Qed.
Lemma D_95c9c : decode_any W_95c9c = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ca0 : bv 32 := 0xc8c58513.
Lemma F_95ca0 : fetch_word PSEGS (0x95ca0 : word) = Some W_95ca0.
Proof. vm_refl. Qed.
Lemma D_95ca0 : decode_any W_95ca0 = Some (OpImm ALU_ADD 10 11 3212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ca4 : bv 32 := 0x03848593.
Lemma F_95ca4 : fetch_word PSEGS (0x95ca4 : word) = Some W_95ca4.
Proof. vm_refl. Qed.
Lemma D_95ca4 : decode_any W_95ca4 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ca8 : bv 32 := 0x00000073.
Lemma F_95ca8 : fetch_word PSEGS (0x95ca8 : word) = Some W_95ca8.
Proof. vm_refl. Qed.
Lemma D_95ca8 : decode_any W_95ca8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_95ca8 : is_ecall W_95ca8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_95cac : bv 32 := 0x07890613.
Lemma F_95cac : fetch_word PSEGS (0x95cac : word) = Some W_95cac.
Proof. vm_refl. Qed.
Lemma D_95cac : decode_any W_95cac = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cb0 : bv 32 := 0x02a92023.
Lemma F_95cb0 : fetch_word PSEGS (0x95cb0 : word) = Some W_95cb0.
Proof. vm_refl. Qed.
Lemma D_95cb0 : decode_any W_95cb0 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cb4 : bv 32 := 0x08b93c23.
Lemma F_95cb4 : fetch_word PSEGS (0x95cb4 : word) = Some W_95cb4.
Proof. vm_refl. Qed.
Lemma D_95cb4 : decode_any W_95cb4 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cb8 : bv 32 := 0x06c93c23.
Lemma F_95cb8 : fetch_word PSEGS (0x95cb8 : word) = Some W_95cb8.
Proof. vm_refl. Qed.
Lemma D_95cb8 : decode_any W_95cb8 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cbc : bv 32 := 0x0004f517.
Lemma F_95cbc : fetch_word PSEGS (0x95cbc : word) = Some W_95cbc.
Proof. vm_refl. Qed.
Lemma D_95cbc : decode_any W_95cbc = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cc0 : bv 32 := 0xed453503.
Lemma F_95cc0 : fetch_word PSEGS (0x95cc0 : word) = Some W_95cc0.
Proof. vm_refl. Qed.
Lemma D_95cc0 : decode_any W_95cc0 = Some (Load SZ8 true 10 10 3796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cc4 : bv 32 := 0x01293423.
Lemma F_95cc4 : fetch_word PSEGS (0x95cc4 : word) = Some W_95cc4.
Proof. vm_refl. Qed.
Lemma D_95cc4 : decode_any W_95cc4 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cc8 : bv 32 := 0x01293823.
Lemma F_95cc8 : fetch_word PSEGS (0x95cc8 : word) = Some W_95cc8.
Proof. vm_refl. Qed.
Lemma D_95cc8 : decode_any W_95cc8 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ccc : bv 32 := 0x00a93c23.
Lemma F_95ccc : fetch_word PSEGS (0x95ccc : word) = Some W_95ccc.
Proof. vm_refl. Qed.
Lemma D_95ccc : decode_any W_95ccc = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cd0 : bv 32 := 0x0080006f.
Lemma F_95cd0 : fetch_word PSEGS (0x95cd0 : word) = Some W_95cd0.
Proof. vm_refl. Qed.
Lemma D_95cd0 : decode_any W_95cd0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cd8 : bv 32 := 0x03813083.
Lemma F_95cd8 : fetch_word PSEGS (0x95cd8 : word) = Some W_95cd8.
Proof. vm_refl. Qed.
Lemma D_95cd8 : decode_any W_95cd8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cdc : bv 32 := 0x03013403.
Lemma F_95cdc : fetch_word PSEGS (0x95cdc : word) = Some W_95cdc.
Proof. vm_refl. Qed.
Lemma D_95cdc : decode_any W_95cdc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ce0 : bv 32 := 0x02813483.
Lemma F_95ce0 : fetch_word PSEGS (0x95ce0 : word) = Some W_95ce0.
Proof. vm_refl. Qed.
Lemma D_95ce0 : decode_any W_95ce0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ce4 : bv 32 := 0x02013903.
Lemma F_95ce4 : fetch_word PSEGS (0x95ce4 : word) = Some W_95ce4.
Proof. vm_refl. Qed.
Lemma D_95ce4 : decode_any W_95ce4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ce8 : bv 32 := 0x01813983.
Lemma F_95ce8 : fetch_word PSEGS (0x95ce8 : word) = Some W_95ce8.
Proof. vm_refl. Qed.
Lemma D_95ce8 : decode_any W_95ce8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cec : bv 32 := 0x01013a03.
Lemma F_95cec : fetch_word PSEGS (0x95cec : word) = Some W_95cec.
Proof. vm_refl. Qed.
Lemma D_95cec : decode_any W_95cec = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cf0 : bv 32 := 0x00813a83.
Lemma F_95cf0 : fetch_word PSEGS (0x95cf0 : word) = Some W_95cf0.
Proof. vm_refl. Qed.
Lemma D_95cf0 : decode_any W_95cf0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cf4 : bv 32 := 0x04010113.
Lemma F_95cf4 : fetch_word PSEGS (0x95cf4 : word) = Some W_95cf4.
Proof. vm_refl. Qed.
Lemma D_95cf4 : decode_any W_95cf4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95cf8 : bv 32 := 0x00008067.
Lemma F_95cf8 : fetch_word PSEGS (0x95cf8 : word) = Some W_95cf8.
Proof. vm_refl. Qed.
Lemma D_95cf8 : decode_any W_95cf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d9c : bv 32 := 0x00050593.
Lemma F_95d9c : fetch_word PSEGS (0x95d9c : word) = Some W_95d9c.
Proof. vm_refl. Qed.
Lemma D_95d9c : decode_any W_95d9c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95da0 : bv 32 := 0x05e00893.
Lemma F_95da0 : fetch_word PSEGS (0x95da0 : word) = Some W_95da0.
Proof. vm_refl. Qed.
Lemma D_95da0 : decode_any W_95da0 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95da4 : bv 32 := 0x00000073.
Lemma F_95da4 : fetch_word PSEGS (0x95da4 : word) = Some W_95da4.
Proof. vm_refl. Qed.
Lemma D_95da4 : decode_any W_95da4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_95da4 : is_ecall W_95da4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_95de8 : bv 32 := 0xfd010113.
Lemma F_95de8 : fetch_word PSEGS (0x95de8 : word) = Some W_95de8.
Proof. vm_refl. Qed.
Lemma D_95de8 : decode_any W_95de8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dec : bv 32 := 0x02113423.
Lemma F_95dec : fetch_word PSEGS (0x95dec : word) = Some W_95dec.
Proof. vm_refl. Qed.
Lemma D_95dec : decode_any W_95dec = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95df0 : bv 32 := 0x02813023.
Lemma F_95df0 : fetch_word PSEGS (0x95df0 : word) = Some W_95df0.
Proof. vm_refl. Qed.
Lemma D_95df0 : decode_any W_95df0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95df4 : bv 32 := 0x00913c23.
Lemma F_95df4 : fetch_word PSEGS (0x95df4 : word) = Some W_95df4.
Proof. vm_refl. Qed.
Lemma D_95df4 : decode_any W_95df4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95df8 : bv 32 := 0x01213823.
Lemma F_95df8 : fetch_word PSEGS (0x95df8 : word) = Some W_95df8.
Proof. vm_refl. Qed.
Lemma D_95df8 : decode_any W_95df8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dfc : bv 32 := 0x01313423.
Lemma F_95dfc : fetch_word PSEGS (0x95dfc : word) = Some W_95dfc.
Proof. vm_refl. Qed.
Lemma D_95dfc : decode_any W_95dfc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e00 : bv 32 := 0x0004f517.
Lemma F_95e00 : fetch_word PSEGS (0x95e00 : word) = Some W_95e00.
Proof. vm_refl. Qed.
Lemma D_95e00 : decode_any W_95e00 = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e04 : bv 32 := 0xb6050913.
Lemma F_95e04 : fetch_word PSEGS (0x95e04 : word) = Some W_95e04.
Proof. vm_refl. Qed.
Lemma D_95e04 : decode_any W_95e04 = Some (OpImm ALU_ADD 18 10 2912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e08 : bv 32 := 0x00490413.
Lemma F_95e08 : fetch_word PSEGS (0x95e08 : word) = Some W_95e08.
Proof. vm_refl. Qed.
Lemma D_95e08 : decode_any W_95e08 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e0c : bv 32 := 0x00040513.
Lemma F_95e0c : fetch_word PSEGS (0x95e0c : word) = Some W_95e0c.
Proof. vm_refl. Qed.
Lemma D_95e0c : decode_any W_95e0c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e10 : bv 32 := 0x510110ef.
Lemma F_95e10 : fetch_word PSEGS (0x95e10 : word) = Some W_95e10.
Proof. vm_refl. Qed.
Lemma D_95e10 : decode_any W_95e10 = Some (Jal 1 70928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e14 : bv 32 := 0x01093503.
Lemma F_95e14 : fetch_word PSEGS (0x95e14 : word) = Some W_95e14.
Proof. vm_refl. Qed.
Lemma D_95e14 : decode_any W_95e14 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e18 : bv 32 := 0x06050863.
Lemma F_95e18 : fetch_word PSEGS (0x95e18 : word) = Some W_95e18.
Proof. vm_refl. Qed.
Lemma D_95e18 : decode_any W_95e18 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e1c : bv 32 := 0x00892583.
Lemma F_95e1c : fetch_word PSEGS (0x95e1c : word) = Some W_95e1c.
Proof. vm_refl. Qed.
Lemma D_95e1c : decode_any W_95e1c = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e20 : bv 32 := 0x0180006f.
Lemma F_95e20 : fetch_word PSEGS (0x95e20 : word) = Some W_95e20.
Proof. vm_refl. Qed.
Lemma D_95e20 : decode_any W_95e20 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e24 : bv 32 := 0x00053503.
Lemma F_95e24 : fetch_word PSEGS (0x95e24 : word) = Some W_95e24.
Proof. vm_refl. Qed.
Lemma D_95e24 : decode_any W_95e24 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e28 : bv 32 := 0x02000593.
Lemma F_95e28 : fetch_word PSEGS (0x95e28 : word) = Some W_95e28.
Proof. vm_refl. Qed.
Lemma D_95e28 : decode_any W_95e28 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e2c : bv 32 := 0x00b92423.
Lemma F_95e2c : fetch_word PSEGS (0x95e2c : word) = Some W_95e2c.
Proof. vm_refl. Qed.
Lemma D_95e2c : decode_any W_95e2c = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e30 : bv 32 := 0x00a93823.
Lemma F_95e30 : fetch_word PSEGS (0x95e30 : word) = Some W_95e30.
Proof. vm_refl. Qed.
Lemma D_95e30 : decode_any W_95e30 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e34 : bv 32 := 0x04050a63.
Lemma F_95e34 : fetch_word PSEGS (0x95e34 : word) = Some W_95e34.
Proof. vm_refl. Qed.
Lemma D_95e34 : decode_any W_95e34 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e38 : bv 32 := 0xfff5861b.
Lemma F_95e38 : fetch_word PSEGS (0x95e38 : word) = Some W_95e38.
Proof. vm_refl. Qed.
Lemma D_95e38 : decode_any W_95e38 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e3c : bv 32 := 0x00c92423.
Lemma F_95e3c : fetch_word PSEGS (0x95e3c : word) = Some W_95e3c.
Proof. vm_refl. Qed.
Lemma D_95e3c : decode_any W_95e3c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e40 : bv 32 := 0xfeb052e3.
Lemma F_95e40 : fetch_word PSEGS (0x95e40 : word) = Some W_95e40.
Proof. vm_refl. Qed.
Lemma D_95e40 : decode_any W_95e40 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e44 : bv 32 := 0x01093503.
Lemma F_95e44 : fetch_word PSEGS (0x95e44 : word) = Some W_95e44.
Proof. vm_refl. Qed.
Lemma D_95e44 : decode_any W_95e44 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e48 : bv 32 := 0x00361613.
Lemma F_95e48 : fetch_word PSEGS (0x95e48 : word) = Some W_95e48.
Proof. vm_refl. Qed.
Lemma D_95e48 : decode_any W_95e48 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e4c : bv 32 := 0x00c50533.
Lemma F_95e4c : fetch_word PSEGS (0x95e4c : word) = Some W_95e4c.
Proof. vm_refl. Qed.
Lemma D_95e4c : decode_any W_95e4c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e50 : bv 32 := 0x00853983.
Lemma F_95e50 : fetch_word PSEGS (0x95e50 : word) = Some W_95e50.
Proof. vm_refl. Qed.
Lemma D_95e50 : decode_any W_95e50 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e54 : bv 32 := 0x10853483.
Lemma F_95e54 : fetch_word PSEGS (0x95e54 : word) = Some W_95e54.
Proof. vm_refl. Qed.
Lemma D_95e54 : decode_any W_95e54 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e58 : bv 32 := 0x00040513.
Lemma F_95e58 : fetch_word PSEGS (0x95e58 : word) = Some W_95e58.
Proof. vm_refl. Qed.
Lemma D_95e58 : decode_any W_95e58 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e5c : bv 32 := 0x74c110ef.
Lemma F_95e5c : fetch_word PSEGS (0x95e5c : word) = Some W_95e5c.
Proof. vm_refl. Qed.
Lemma D_95e5c : decode_any W_95e5c = Some (Jal 1 71500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e60 : bv 32 := 0x00048513.
Lemma F_95e60 : fetch_word PSEGS (0x95e60 : word) = Some W_95e60.
Proof. vm_refl. Qed.
Lemma D_95e60 : decode_any W_95e60 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e64 : bv 32 := 0x000980e7.
Lemma F_95e64 : fetch_word PSEGS (0x95e64 : word) = Some W_95e64.
Proof. vm_refl. Qed.
Lemma D_95e64 : decode_any W_95e64 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e68 : bv 32 := 0x00040513.
Lemma F_95e68 : fetch_word PSEGS (0x95e68 : word) = Some W_95e68.
Proof. vm_refl. Qed.
Lemma D_95e68 : decode_any W_95e68 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e6c : bv 32 := 0x4b4110ef.
Lemma F_95e6c : fetch_word PSEGS (0x95e6c : word) = Some W_95e6c.
Proof. vm_refl. Qed.
Lemma D_95e6c : decode_any W_95e6c = Some (Jal 1 70836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e70 : bv 32 := 0x00892503.
Lemma F_95e70 : fetch_word PSEGS (0x95e70 : word) = Some W_95e70.
Proof. vm_refl. Qed.
Lemma D_95e70 : decode_any W_95e70 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e74 : bv 32 := 0xfff5061b.
Lemma F_95e74 : fetch_word PSEGS (0x95e74 : word) = Some W_95e74.
Proof. vm_refl. Qed.
Lemma D_95e74 : decode_any W_95e74 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e78 : bv 32 := 0x00c92423.
Lemma F_95e78 : fetch_word PSEGS (0x95e78 : word) = Some W_95e78.
Proof. vm_refl. Qed.
Lemma D_95e78 : decode_any W_95e78 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e7c : bv 32 := 0xfca044e3.
Lemma F_95e7c : fetch_word PSEGS (0x95e7c : word) = Some W_95e7c.
Proof. vm_refl. Qed.
Lemma D_95e7c : decode_any W_95e7c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e80 : bv 32 := 0x01093503.
Lemma F_95e80 : fetch_word PSEGS (0x95e80 : word) = Some W_95e80.
Proof. vm_refl. Qed.
Lemma D_95e80 : decode_any W_95e80 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e84 : bv 32 := 0xfa1ff06f.
Lemma F_95e84 : fetch_word PSEGS (0x95e84 : word) = Some W_95e84.
Proof. vm_refl. Qed.
Lemma D_95e84 : decode_any W_95e84 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e88 : bv 32 := 0x00100513.
Lemma F_95e88 : fetch_word PSEGS (0x95e88 : word) = Some W_95e88.
Proof. vm_refl. Qed.
Lemma D_95e88 : decode_any W_95e88 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e8c : bv 32 := 0x00a90023.
Lemma F_95e8c : fetch_word PSEGS (0x95e8c : word) = Some W_95e8c.
Proof. vm_refl. Qed.
Lemma D_95e8c : decode_any W_95e8c = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e90 : bv 32 := 0x00040513.
Lemma F_95e90 : fetch_word PSEGS (0x95e90 : word) = Some W_95e90.
Proof. vm_refl. Qed.
Lemma D_95e90 : decode_any W_95e90 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e94 : bv 32 := 0x02813083.
Lemma F_95e94 : fetch_word PSEGS (0x95e94 : word) = Some W_95e94.
Proof. vm_refl. Qed.
Lemma D_95e94 : decode_any W_95e94 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e98 : bv 32 := 0x02013403.
Lemma F_95e98 : fetch_word PSEGS (0x95e98 : word) = Some W_95e98.
Proof. vm_refl. Qed.
Lemma D_95e98 : decode_any W_95e98 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e9c : bv 32 := 0x01813483.
Lemma F_95e9c : fetch_word PSEGS (0x95e9c : word) = Some W_95e9c.
Proof. vm_refl. Qed.
Lemma D_95e9c : decode_any W_95e9c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ea0 : bv 32 := 0x01013903.
Lemma F_95ea0 : fetch_word PSEGS (0x95ea0 : word) = Some W_95ea0.
Proof. vm_refl. Qed.
Lemma D_95ea0 : decode_any W_95ea0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ea4 : bv 32 := 0x00813983.
Lemma F_95ea4 : fetch_word PSEGS (0x95ea4 : word) = Some W_95ea4.
Proof. vm_refl. Qed.
Lemma D_95ea4 : decode_any W_95ea4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ea8 : bv 32 := 0x03010113.
Lemma F_95ea8 : fetch_word PSEGS (0x95ea8 : word) = Some W_95ea8.
Proof. vm_refl. Qed.
Lemma D_95ea8 : decode_any W_95ea8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95eac : bv 32 := 0x6fc1106f.
Lemma F_95eac : fetch_word PSEGS (0x95eac : word) = Some W_95eac.
Proof. vm_refl. Qed.
Lemma D_95eac : decode_any W_95eac = Some (Jal 0 71420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95eb0 : bv 32 := 0x00008067.
Lemma F_95eb0 : fetch_word PSEGS (0x95eb0 : word) = Some W_95eb0.
Proof. vm_refl. Qed.
Lemma D_95eb0 : decode_any W_95eb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95eb4 : bv 32 := 0xfd010113.
Lemma F_95eb4 : fetch_word PSEGS (0x95eb4 : word) = Some W_95eb4.
Proof. vm_refl. Qed.
Lemma D_95eb4 : decode_any W_95eb4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ecc : bv 32 := 0x01413023.
Lemma F_95ecc : fetch_word PSEGS (0x95ecc : word) = Some W_95ecc.
Proof. vm_refl. Qed.
Lemma D_95ecc : decode_any W_95ecc = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ed0 : bv 32 := 0x00058493.
Lemma F_95ed0 : fetch_word PSEGS (0x95ed0 : word) = Some W_95ed0.
Proof. vm_refl. Qed.
Lemma D_95ed0 : decode_any W_95ed0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ed4 : bv 32 := 0x00050913.
Lemma F_95ed4 : fetch_word PSEGS (0x95ed4 : word) = Some W_95ed4.
Proof. vm_refl. Qed.
Lemma D_95ed4 : decode_any W_95ed4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95edc : bv 32 := 0xa8850a13.
Lemma F_95edc : fetch_word PSEGS (0x95edc : word) = Some W_95edc.
Proof. vm_refl. Qed.
Lemma D_95edc : decode_any W_95edc = Some (OpImm ALU_ADD 20 10 2696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ee8 : bv 32 := 0x438110ef.
Lemma F_95ee8 : fetch_word PSEGS (0x95ee8 : word) = Some W_95ee8.
Proof. vm_refl. Qed.
Lemma D_95ee8 : decode_any W_95ee8 = Some (Jal 1 70712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95eec : bv 32 := 0x000a4503.
Lemma F_95eec : fetch_word PSEGS (0x95eec : word) = Some W_95eec.
Proof. vm_refl. Qed.
Lemma D_95eec : decode_any W_95eec = Some (Load SZ1 false 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ef0 : bv 32 := 0xfff00993.
Lemma F_95ef0 : fetch_word PSEGS (0x95ef0 : word) = Some W_95ef0.
Proof. vm_refl. Qed.
Lemma D_95ef0 : decode_any W_95ef0 = Some (OpImm ALU_ADD 19 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ef4 : bv 32 := 0x04051e63.
Lemma F_95ef4 : fetch_word PSEGS (0x95ef4 : word) = Some W_95ef4.
Proof. vm_refl. Qed.
Lemma D_95ef4 : decode_any W_95ef4 = Some (Branch BC_NE 10 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ef8 : bv 32 := 0x010a3503.
Lemma F_95ef8 : fetch_word PSEGS (0x95ef8 : word) = Some W_95ef8.
Proof. vm_refl. Qed.
Lemma D_95ef8 : decode_any W_95ef8 = Some (Load SZ8 true 10 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95efc : bv 32 := 0x00051663.
Lemma F_95efc : fetch_word PSEGS (0x95efc : word) = Some W_95efc.
Proof. vm_refl. Qed.
Lemma D_95efc : decode_any W_95efc = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f00 : bv 32 := 0x018a0513.
Lemma F_95f00 : fetch_word PSEGS (0x95f00 : word) = Some W_95f00.
Proof. vm_refl. Qed.
Lemma D_95f00 : decode_any W_95f00 = Some (OpImm ALU_ADD 10 20 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f04 : bv 32 := 0x00aa3823.
Lemma F_95f04 : fetch_word PSEGS (0x95f04 : word) = Some W_95f04.
Proof. vm_refl. Qed.
Lemma D_95f04 : decode_any W_95f04 = Some (Store SZ8 20 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f08 : bv 32 := 0x008a2583.
Lemma F_95f08 : fetch_word PSEGS (0x95f08 : word) = Some W_95f08.
Proof. vm_refl. Qed.
Lemma D_95f08 : decode_any W_95f08 = Some (Load SZ4 true 11 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f0c : bv 32 := 0x02000613.
Lemma F_95f0c : fetch_word PSEGS (0x95f0c : word) = Some W_95f0c.
Proof. vm_refl. Qed.
Lemma D_95f0c : decode_any W_95f0c = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f10 : bv 32 := 0x02c59263.
Lemma F_95f10 : fetch_word PSEGS (0x95f10 : word) = Some W_95f10.
Proof. vm_refl. Qed.
Lemma D_95f10 : decode_any W_95f10 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f14 : bv 32 := 0x20800513.
Lemma F_95f14 : fetch_word PSEGS (0x95f14 : word) = Some W_95f14.
Proof. vm_refl. Qed.
Lemma D_95f14 : decode_any W_95f14 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f18 : bv 32 := 0x00100593.
Lemma F_95f18 : fetch_word PSEGS (0x95f18 : word) = Some W_95f18.
Proof. vm_refl. Qed.
Lemma D_95f18 : decode_any W_95f18 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f1c : bv 32 := 0x020020ef.
Lemma F_95f1c : fetch_word PSEGS (0x95f1c : word) = Some W_95f1c.
Proof. vm_refl. Qed.
Lemma D_95f1c : decode_any W_95f1c = Some (Jal 1 8224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f20 : bv 32 := 0x02050863.
Lemma F_95f20 : fetch_word PSEGS (0x95f20 : word) = Some W_95f20.
Proof. vm_refl. Qed.
Lemma D_95f20 : decode_any W_95f20 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f24 : bv 32 := 0x00000593.
Lemma F_95f24 : fetch_word PSEGS (0x95f24 : word) = Some W_95f24.
Proof. vm_refl. Qed.
Lemma D_95f24 : decode_any W_95f24 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f28 : bv 32 := 0x010a3603.
Lemma F_95f28 : fetch_word PSEGS (0x95f28 : word) = Some W_95f28.
Proof. vm_refl. Qed.
Lemma D_95f28 : decode_any W_95f28 = Some (Load SZ8 true 12 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f2c : bv 32 := 0x00c53023.
Lemma F_95f2c : fetch_word PSEGS (0x95f2c : word) = Some W_95f2c.
Proof. vm_refl. Qed.
Lemma D_95f2c : decode_any W_95f2c = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f30 : bv 32 := 0x00aa3823.
Lemma F_95f30 : fetch_word PSEGS (0x95f30 : word) = Some W_95f30.
Proof. vm_refl. Qed.
Lemma D_95f30 : decode_any W_95f30 = Some (Store SZ8 20 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f34 : bv 32 := 0x00000993.
Lemma F_95f34 : fetch_word PSEGS (0x95f34 : word) = Some W_95f34.
Proof. vm_refl. Qed.
Lemma D_95f34 : decode_any W_95f34 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f38 : bv 32 := 0x00359613.
Lemma F_95f38 : fetch_word PSEGS (0x95f38 : word) = Some W_95f38.
Proof. vm_refl. Qed.
Lemma D_95f38 : decode_any W_95f38 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f3c : bv 32 := 0x00c50533.
Lemma F_95f3c : fetch_word PSEGS (0x95f3c : word) = Some W_95f3c.
Proof. vm_refl. Qed.
Lemma D_95f3c : decode_any W_95f3c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f40 : bv 32 := 0x00158593.
Lemma F_95f40 : fetch_word PSEGS (0x95f40 : word) = Some W_95f40.
Proof. vm_refl. Qed.
Lemma D_95f40 : decode_any W_95f40 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f44 : bv 32 := 0x01253423.
Lemma F_95f44 : fetch_word PSEGS (0x95f44 : word) = Some W_95f44.
Proof. vm_refl. Qed.
Lemma D_95f44 : decode_any W_95f44 = Some (Store SZ8 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f48 : bv 32 := 0x10953423.
Lemma F_95f48 : fetch_word PSEGS (0x95f48 : word) = Some W_95f48.
Proof. vm_refl. Qed.
Lemma D_95f48 : decode_any W_95f48 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95f4c : bv 32 := 0x00ba2423.
Lemma F_95f4c : fetch_word PSEGS (0x95f4c : word) = Some W_95f4c.
Proof. vm_refl. Qed.
Lemma D_95f4c : decode_any W_95f4c = Some (Store SZ4 20 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96044 : bv 32 := 0x00008067.
Lemma F_96044 : fetch_word PSEGS (0x96044 : word) = Some W_96044.
Proof. vm_refl. Qed.
Lemma D_96044 : decode_any W_96044 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96048 : bv 32 := 0xfe010113.
Lemma F_96048 : fetch_word PSEGS (0x96048 : word) = Some W_96048.
Proof. vm_refl. Qed.
Lemma D_96048 : decode_any W_96048 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9604c : bv 32 := 0x00113c23.
Lemma F_9604c : fetch_word PSEGS (0x9604c : word) = Some W_9604c.
Proof. vm_refl. Qed.
Lemma D_9604c : decode_any W_9604c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96050 : bv 32 := 0x00813823.
Lemma F_96050 : fetch_word PSEGS (0x96050 : word) = Some W_96050.
Proof. vm_refl. Qed.
Lemma D_96050 : decode_any W_96050 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96054 : bv 32 := 0x00913423.
Lemma F_96054 : fetch_word PSEGS (0x96054 : word) = Some W_96054.
Proof. vm_refl. Qed.
Lemma D_96054 : decode_any W_96054 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96058 : bv 32 := 0x0001c517.
Lemma F_96058 : fetch_word PSEGS (0x96058 : word) = Some W_96058.
Proof. vm_refl. Qed.
Lemma D_96058 : decode_any W_96058 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9605c : bv 32 := 0x0001c597.
Lemma F_9605c : fetch_word PSEGS (0x9605c : word) = Some W_9605c.
Proof. vm_refl. Qed.
Lemma D_9605c : decode_any W_9605c = Some (Auipc 11 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96060 : bv 32 := 0xb6053503.
Lemma F_96060 : fetch_word PSEGS (0x96060 : word) = Some W_96060.
Proof. vm_refl. Qed.
Lemma D_96060 : decode_any W_96060 = Some (Load SZ8 true 10 10 2912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96064 : bv 32 := 0xb645b403.
Lemma F_96064 : fetch_word PSEGS (0x96064 : word) = Some W_96064.
Proof. vm_refl. Qed.
Lemma D_96064 : decode_any W_96064 = Some (Load SZ8 true 8 11 2916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96068 : bv 32 := 0x00a47c63.
Lemma F_96068 : fetch_word PSEGS (0x96068 : word) = Some W_96068.
Proof. vm_refl. Qed.
Lemma D_96068 : decode_any W_96068 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9606c : bv 32 := 0xff853583.
Lemma F_9606c : fetch_word PSEGS (0x9606c : word) = Some W_9606c.
Proof. vm_refl. Qed.
Lemma D_9606c : decode_any W_9606c = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96070 : bv 32 := 0xff850493.
Lemma F_96070 : fetch_word PSEGS (0x96070 : word) = Some W_96070.
Proof. vm_refl. Qed.
Lemma D_96070 : decode_any W_96070 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96074 : bv 32 := 0x000580e7.
Lemma F_96074 : fetch_word PSEGS (0x96074 : word) = Some W_96074.
Proof. vm_refl. Qed.
Lemma D_96074 : decode_any W_96074 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96078 : bv 32 := 0x00048513.
Lemma F_96078 : fetch_word PSEGS (0x96078 : word) = Some W_96078.
Proof. vm_refl. Qed.
Lemma D_96078 : decode_any W_96078 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9607c : bv 32 := 0xfe9468e3.
Lemma F_9607c : fetch_word PSEGS (0x9607c : word) = Some W_9607c.
Proof. vm_refl. Qed.
Lemma D_9607c : decode_any W_9607c = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96080 : bv 32 := 0x01813083.
Lemma F_96080 : fetch_word PSEGS (0x96080 : word) = Some W_96080.
Proof. vm_refl. Qed.
Lemma D_96080 : decode_any W_96080 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96084 : bv 32 := 0x01013403.
Lemma F_96084 : fetch_word PSEGS (0x96084 : word) = Some W_96084.
Proof. vm_refl. Qed.
Lemma D_96084 : decode_any W_96084 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96088 : bv 32 := 0x00813483.
Lemma F_96088 : fetch_word PSEGS (0x96088 : word) = Some W_96088.
Proof. vm_refl. Qed.
Lemma D_96088 : decode_any W_96088 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9608c : bv 32 := 0x02010113.
Lemma F_9608c : fetch_word PSEGS (0x9608c : word) = Some W_9608c.
Proof. vm_refl. Qed.
Lemma D_9608c : decode_any W_9608c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96090 : bv 32 := 0xfb5ff06f.
Lemma F_96090 : fetch_word PSEGS (0x96090 : word) = Some W_96090.
Proof. vm_refl. Qed.
Lemma D_96090 : decode_any W_96090 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96094 : bv 32 := 0xff010113.
Lemma F_96094 : fetch_word PSEGS (0x96094 : word) = Some W_96094.
Proof. vm_refl. Qed.
Lemma D_96094 : decode_any W_96094 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96098 : bv 32 := 0x00113423.
Lemma F_96098 : fetch_word PSEGS (0x96098 : word) = Some W_96098.
Proof. vm_refl. Qed.
Lemma D_96098 : decode_any W_96098 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9609c : bv 32 := 0x00813023.
Lemma F_9609c : fetch_word PSEGS (0x9609c : word) = Some W_9609c.
Proof. vm_refl. Qed.
Lemma D_9609c : decode_any W_9609c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960a0 : bv 32 := 0x00000593.
Lemma F_960a0 : fetch_word PSEGS (0x960a0 : word) = Some W_960a0.
Proof. vm_refl. Qed.
Lemma D_960a0 : decode_any W_960a0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960a4 : bv 32 := 0x00020613.
Lemma F_960a4 : fetch_word PSEGS (0x960a4 : word) = Some W_960a4.
Proof. vm_refl. Qed.
Lemma D_960a4 : decode_any W_960a4 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960a8 : bv 32 := 0xf5862603.
Lemma F_960a8 : fetch_word PSEGS (0x960a8 : word) = Some W_960a8.
Proof. vm_refl. Qed.
Lemma D_960a8 : decode_any W_960a8 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960ac : bv 32 := 0x0004f697.
Lemma F_960ac : fetch_word PSEGS (0x960ac : word) = Some W_960ac.
Proof. vm_refl. Qed.
Lemma D_960ac : decode_any W_960ac = Some (Auipc 13 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960b0 : bv 32 := 0xad468693.
Lemma F_960b0 : fetch_word PSEGS (0x960b0 : word) = Some W_960b0.
Proof. vm_refl. Qed.
Lemma D_960b0 : decode_any W_960b0 = Some (OpImm ALU_ADD 13 13 2772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960b4 : bv 32 := 0x1606a72f.
Lemma F_960b4 : fetch_word PSEGS (0x960b4 : word) = Some W_960b4.
Proof. vm_refl. Qed.
Lemma D_960b4 : decode_any W_960b4 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960b8 : bv 32 := 0x00b71663.
Lemma F_960b8 : fetch_word PSEGS (0x960b8 : word) = Some W_960b8.
Proof. vm_refl. Qed.
Lemma D_960b8 : decode_any W_960b8 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960bc : bv 32 := 0x1ec6a7af.
Lemma F_960bc : fetch_word PSEGS (0x960bc : word) = Some W_960bc.
Proof. vm_refl. Qed.
Lemma D_960bc : decode_any W_960bc = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960c0 : bv 32 := 0xfe079ae3.
Lemma F_960c0 : fetch_word PSEGS (0x960c0 : word) = Some W_960c0.
Proof. vm_refl. Qed.
Lemma D_960c0 : decode_any W_960c0 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960c4 : bv 32 := 0x0007059b.
Lemma F_960c4 : fetch_word PSEGS (0x960c4 : word) = Some W_960c4.
Proof. vm_refl. Qed.
Lemma D_960c4 : decode_any W_960c4 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960c8 : bv 32 := 0x02c58263.
Lemma F_960c8 : fetch_word PSEGS (0x960c8 : word) = Some W_960c8.
Proof. vm_refl. Qed.
Lemma D_960c8 : decode_any W_960c8 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960cc : bv 32 := 0x02058263.
Lemma F_960cc : fetch_word PSEGS (0x960cc : word) = Some W_960cc.
Proof. vm_refl. Qed.
Lemma D_960cc : decode_any W_960cc = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960f0 : bv 32 := 0x00050413.
Lemma F_960f0 : fetch_word PSEGS (0x960f0 : word) = Some W_960f0.
Proof. vm_refl. Qed.
Lemma D_960f0 : decode_any W_960f0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960f4 : bv 32 := 0xcf5ff0ef.
Lemma F_960f4 : fetch_word PSEGS (0x960f4 : word) = Some W_960f4.
Proof. vm_refl. Qed.
Lemma D_960f4 : decode_any W_960f4 = Some (Jal 1 2096372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960f8 : bv 32 := 0xf51ff0ef.
Lemma F_960f8 : fetch_word PSEGS (0x960f8 : word) = Some W_960f8.
Proof. vm_refl. Qed.
Lemma D_960f8 : decode_any W_960f8 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_960fc : bv 32 := 0x474050ef.
Lemma F_960fc : fetch_word PSEGS (0x960fc : word) = Some W_960fc.
Proof. vm_refl. Qed.
Lemma D_960fc : decode_any W_960fc = Some (Jal 1 21620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96100 : bv 32 := 0x00040513.
Lemma F_96100 : fetch_word PSEGS (0x96100 : word) = Some W_96100.
Proof. vm_refl. Qed.
Lemma D_96100 : decode_any W_96100 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96104 : bv 32 := 0xc99ff0ef.
Lemma F_96104 : fetch_word PSEGS (0x96104 : word) = Some W_96104.
Proof. vm_refl. Qed.
Lemma D_96104 : decode_any W_96104 = Some (Jal 1 2096280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96108 : bv 32 := 0xfa010113.
Lemma F_96108 : fetch_word PSEGS (0x96108 : word) = Some W_96108.
Proof. vm_refl. Qed.
Lemma D_96108 : decode_any W_96108 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9610c : bv 32 := 0x02113423.
Lemma F_9610c : fetch_word PSEGS (0x9610c : word) = Some W_9610c.
Proof. vm_refl. Qed.
Lemma D_9610c : decode_any W_9610c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96110 : bv 32 := 0x02813023.
Lemma F_96110 : fetch_word PSEGS (0x96110 : word) = Some W_96110.
Proof. vm_refl. Qed.
Lemma D_96110 : decode_any W_96110 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96114 : bv 32 := 0x00913c23.
Lemma F_96114 : fetch_word PSEGS (0x96114 : word) = Some W_96114.
Proof. vm_refl. Qed.
Lemma D_96114 : decode_any W_96114 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96118 : bv 32 := 0x00058413.
Lemma F_96118 : fetch_word PSEGS (0x96118 : word) = Some W_96118.
Proof. vm_refl. Qed.
Lemma D_96118 : decode_any W_96118 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9611c : bv 32 := 0x00050293.
Lemma F_9611c : fetch_word PSEGS (0x9611c : word) = Some W_9611c.
Proof. vm_refl. Qed.
Lemma D_9611c : decode_any W_9611c = Some (OpImm ALU_ADD 5 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96120 : bv 32 := 0x05013823.
Lemma F_96120 : fetch_word PSEGS (0x96120 : word) = Some W_96120.
Proof. vm_refl. Qed.
Lemma D_96120 : decode_any W_96120 = Some (Store SZ8 2 16 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96124 : bv 32 := 0x05113c23.
Lemma F_96124 : fetch_word PSEGS (0x96124 : word) = Some W_96124.
Proof. vm_refl. Qed.
Lemma D_96124 : decode_any W_96124 = Some (Store SZ8 2 17 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96128 : bv 32 := 0x0001c517.
Lemma F_96128 : fetch_word PSEGS (0x96128 : word) = Some W_96128.
Proof. vm_refl. Qed.
Lemma D_96128 : decode_any W_96128 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9612c : bv 32 := 0xa8853483.
Lemma F_9612c : fetch_word PSEGS (0x9612c : word) = Some W_9612c.
Proof. vm_refl. Qed.
Lemma D_9612c : decode_any W_9612c = Some (Load SZ8 true 9 10 2696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96130 : bv 32 := 0x02c13823.
Lemma F_96130 : fetch_word PSEGS (0x96130 : word) = Some W_96130.
Proof. vm_refl. Qed.
Lemma D_96130 : decode_any W_96130 = Some (Store SZ8 2 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96134 : bv 32 := 0x02d13c23.
Lemma F_96134 : fetch_word PSEGS (0x96134 : word) = Some W_96134.
Proof. vm_refl. Qed.
Lemma D_96134 : decode_any W_96134 = Some (Store SZ8 2 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96138 : bv 32 := 0x04e13023.
Lemma F_96138 : fetch_word PSEGS (0x96138 : word) = Some W_96138.
Proof. vm_refl. Qed.
Lemma D_96138 : decode_any W_96138 = Some (Store SZ8 2 14 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9613c : bv 32 := 0x04f13423.
Lemma F_9613c : fetch_word PSEGS (0x9613c : word) = Some W_9613c.
Proof. vm_refl. Qed.
Lemma D_9613c : decode_any W_9613c = Some (Store SZ8 2 15 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96140 : bv 32 := 0x0004b503.
Lemma F_96140 : fetch_word PSEGS (0x96140 : word) = Some W_96140.
Proof. vm_refl. Qed.
Lemma D_96140 : decode_any W_96140 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96144 : bv 32 := 0x0405f593.
Lemma F_96144 : fetch_word PSEGS (0x96144 : word) = Some W_96144.
Proof. vm_refl. Qed.
Lemma D_96144 : decode_any W_96144 = Some (OpImm ALU_AND 11 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96148 : bv 32 := 0x00a13823.
Lemma F_96148 : fetch_word PSEGS (0x96148 : word) = Some W_96148.
Proof. vm_refl. Qed.
Lemma D_96148 : decode_any W_96148 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9614c : bv 32 := 0x00059c63.
Lemma F_9614c : fetch_word PSEGS (0x9614c : word) = Some W_9614c.
Proof. vm_refl. Qed.
Lemma D_9614c : decode_any W_9614c = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96150 : bv 32 := 0x00410537.
Lemma F_96150 : fetch_word PSEGS (0x96150 : word) = Some W_96150.
Proof. vm_refl. Qed.
Lemma D_96150 : decode_any W_96150 = Some (Lui 10 1040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96154 : bv 32 := 0x00a475b3.
Lemma F_96154 : fetch_word PSEGS (0x96154 : word) = Some W_96154.
Proof. vm_refl. Qed.
Lemma D_96154 : decode_any W_96154 = Some (Op ALU_AND 11 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96158 : bv 32 := 0x00a58663.
Lemma F_96158 : fetch_word PSEGS (0x96158 : word) = Some W_96158.
Proof. vm_refl. Qed.
Lemma D_96158 : decode_any W_96158 = Some (Branch BC_EQ 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9615c : bv 32 := 0x00000713.
Lemma F_9615c : fetch_word PSEGS (0x9615c : word) = Some W_9615c.
Proof. vm_refl. Qed.
Lemma D_9615c : decode_any W_9615c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96160 : bv 32 := 0x0080006f.
Lemma F_96160 : fetch_word PSEGS (0x96160 : word) = Some W_96160.
Proof. vm_refl. Qed.
Lemma D_96160 : decode_any W_96160 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96164 : bv 32 := 0x03016703.
Lemma F_96164 : fetch_word PSEGS (0x96164 : word) = Some W_96164.
Proof. vm_refl. Qed.
Lemma D_96164 : decode_any W_96164 = Some (Load SZ4 false 14 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96168 : bv 32 := 0x000086b7.
Lemma F_96168 : fetch_word PSEGS (0x96168 : word) = Some W_96168.
Proof. vm_refl. Qed.
Lemma D_96168 : decode_any W_96168 = Some (Lui 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9616c : bv 32 := 0x00d466b3.
Lemma F_9616c : fetch_word PSEGS (0x9616c : word) = Some W_9616c.
Proof. vm_refl. Qed.
Lemma D_9616c : decode_any W_9616c = Some (Op ALU_OR 13 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96170 : bv 32 := 0x03800513.
Lemma F_96170 : fetch_word PSEGS (0x96170 : word) = Some W_96170.
Proof. vm_refl. Qed.
Lemma D_96170 : decode_any W_96170 = Some (OpImm ALU_ADD 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96174 : bv 32 := 0xf9c00593.
Lemma F_96174 : fetch_word PSEGS (0x96174 : word) = Some W_96174.
Proof. vm_refl. Qed.
Lemma D_96174 : decode_any W_96174 = Some (OpImm ALU_ADD 11 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96178 : bv 32 := 0x00028613.
Lemma F_96178 : fetch_word PSEGS (0x96178 : word) = Some W_96178.
Proof. vm_refl. Qed.
Lemma D_96178 : decode_any W_96178 = Some (OpImm ALU_ADD 12 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9617c : bv 32 := 0x00000793.
Lemma F_9617c : fetch_word PSEGS (0x9617c : word) = Some W_9617c.
Proof. vm_refl. Qed.
Lemma D_9617c : decode_any W_9617c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96180 : bv 32 := 0x00000813.
Lemma F_96180 : fetch_word PSEGS (0x96180 : word) = Some W_96180.
Proof. vm_refl. Qed.
Lemma D_96180 : decode_any W_96180 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96184 : bv 32 := 0x4bc110ef.
Lemma F_96184 : fetch_word PSEGS (0x96184 : word) = Some W_96184.
Proof. vm_refl. Qed.
Lemma D_96184 : decode_any W_96184 = Some (Jal 1 70844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96188 : bv 32 := 0x02c41413.
Lemma F_96188 : fetch_word PSEGS (0x96188 : word) = Some W_96188.
Proof. vm_refl. Qed.
Lemma D_96188 : decode_any W_96188 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9618c : bv 32 := 0x00050693.
Lemma F_9618c : fetch_word PSEGS (0x9618c : word) = Some W_9618c.
Proof. vm_refl. Qed.
Lemma D_9618c : decode_any W_9618c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96190 : bv 32 := 0x02045663.
Lemma F_96190 : fetch_word PSEGS (0x96190 : word) = Some W_96190.
Proof. vm_refl. Qed.
Lemma D_96190 : decode_any W_96190 = Some (Branch BC_GE 8 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96194 : bv 32 := 0x80000537.
Lemma F_96194 : fetch_word PSEGS (0x96194 : word) = Some W_96194.
Proof. vm_refl. Qed.
Lemma D_96194 : decode_any W_96194 = Some (Lui 10 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96198 : bv 32 := 0xfff5051b.
Lemma F_96198 : fetch_word PSEGS (0x96198 : word) = Some W_96198.
Proof. vm_refl. Qed.
Lemma D_96198 : decode_any W_96198 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9619c : bv 32 := 0x00150593.
Lemma F_9619c : fetch_word PSEGS (0x9619c : word) = Some W_9619c.
Proof. vm_refl. Qed.
Lemma D_9619c : decode_any W_9619c = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961a0 : bv 32 := 0x00b6f5b3.
Lemma F_961a0 : fetch_word PSEGS (0x961a0 : word) = Some W_961a0.
Proof. vm_refl. Qed.
Lemma D_961a0 : decode_any W_961a0 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961a4 : bv 32 := 0x00059c63.
Lemma F_961a4 : fetch_word PSEGS (0x961a4 : word) = Some W_961a4.
Proof. vm_refl. Qed.
Lemma D_961a4 : decode_any W_961a4 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961a8 : bv 32 := 0x00a6f533.
Lemma F_961a8 : fetch_word PSEGS (0x961a8 : word) = Some W_961a8.
Proof. vm_refl. Qed.
Lemma D_961a8 : decode_any W_961a8 = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961ac : bv 32 := 0x01900893.
Lemma F_961ac : fetch_word PSEGS (0x961ac : word) = Some W_961ac.
Proof. vm_refl. Qed.
Lemma D_961ac : decode_any W_961ac = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961b0 : bv 32 := 0x00200593.
Lemma F_961b0 : fetch_word PSEGS (0x961b0 : word) = Some W_961b0.
Proof. vm_refl. Qed.
Lemma D_961b0 : decode_any W_961b0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961b4 : bv 32 := 0x00100613.
Lemma F_961b4 : fetch_word PSEGS (0x961b4 : word) = Some W_961b4.
Proof. vm_refl. Qed.
Lemma D_961b4 : decode_any W_961b4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.
