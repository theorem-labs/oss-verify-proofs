(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_72708 : bv 32 := 0xfc010113.
Lemma F_72708 : fetch_word Asan.M.loaded_segments (0x72708 : word) = Some W_72708.
Proof. vm_refl. Qed.
Lemma D_72708 : decode_any W_72708 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7270c : bv 32 := 0x02113c23.
Lemma F_7270c : fetch_word Asan.M.loaded_segments (0x7270c : word) = Some W_7270c.
Proof. vm_refl. Qed.
Lemma D_7270c : decode_any W_7270c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72710 : bv 32 := 0x02813823.
Lemma F_72710 : fetch_word Asan.M.loaded_segments (0x72710 : word) = Some W_72710.
Proof. vm_refl. Qed.
Lemma D_72710 : decode_any W_72710 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72714 : bv 32 := 0x02913423.
Lemma F_72714 : fetch_word Asan.M.loaded_segments (0x72714 : word) = Some W_72714.
Proof. vm_refl. Qed.
Lemma D_72714 : decode_any W_72714 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72718 : bv 32 := 0x03213023.
Lemma F_72718 : fetch_word Asan.M.loaded_segments (0x72718 : word) = Some W_72718.
Proof. vm_refl. Qed.
Lemma D_72718 : decode_any W_72718 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7271c : bv 32 := 0x01313c23.
Lemma F_7271c : fetch_word Asan.M.loaded_segments (0x7271c : word) = Some W_7271c.
Proof. vm_refl. Qed.
Lemma D_7271c : decode_any W_7271c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72720 : bv 32 := 0x01413823.
Lemma F_72720 : fetch_word Asan.M.loaded_segments (0x72720 : word) = Some W_72720.
Proof. vm_refl. Qed.
Lemma D_72720 : decode_any W_72720 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72724 : bv 32 := 0x01513423.
Lemma F_72724 : fetch_word Asan.M.loaded_segments (0x72724 : word) = Some W_72724.
Proof. vm_refl. Qed.
Lemma D_72724 : decode_any W_72724 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72728 : bv 32 := 0x00058993.
Lemma F_72728 : fetch_word Asan.M.loaded_segments (0x72728 : word) = Some W_72728.
Proof. vm_refl. Qed.
Lemma D_72728 : decode_any W_72728 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7272c : bv 32 := 0x0085aa03.
Lemma F_7272c : fetch_word Asan.M.loaded_segments (0x7272c : word) = Some W_7272c.
Proof. vm_refl. Qed.
Lemma D_7272c : decode_any W_7272c = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72730 : bv 32 := 0x00c5aa83.
Lemma F_72730 : fetch_word Asan.M.loaded_segments (0x72730 : word) = Some W_72730.
Proof. vm_refl. Qed.
Lemma D_72730 : decode_any W_72730 = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72734 : bv 32 := 0x015a65b3.
Lemma F_72734 : fetch_word Asan.M.loaded_segments (0x72734 : word) = Some W_72734.
Proof. vm_refl. Qed.
Lemma D_72734 : decode_any W_72734 = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72738 : bv 32 := 0x00059663.
Lemma F_72738 : fetch_word Asan.M.loaded_segments (0x72738 : word) = Some W_72738.
Proof. vm_refl. Qed.
Lemma D_72738 : decode_any W_72738 = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7273c : bv 32 := 0x00000513.
Lemma F_7273c : fetch_word Asan.M.loaded_segments (0x7273c : word) = Some W_7273c.
Proof. vm_refl. Qed.
Lemma D_7273c : decode_any W_7273c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72740 : bv 32 := 0x0a40006f.
Lemma F_72740 : fetch_word Asan.M.loaded_segments (0x72740 : word) = Some W_72740.
Proof. vm_refl. Qed.
Lemma D_72740 : decode_any W_72740 = Some (Jal 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72744 : bv 32 := 0x00050493.
Lemma F_72744 : fetch_word Asan.M.loaded_segments (0x72744 : word) = Some W_72744.
Proof. vm_refl. Qed.
Lemma D_72744 : decode_any W_72744 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72748 : bv 32 := 0x10000513.
Lemma F_72748 : fetch_word Asan.M.loaded_segments (0x72748 : word) = Some W_72748.
Proof. vm_refl. Qed.
Lemma D_72748 : decode_any W_72748 = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7274c : bv 32 := 0x0aaafe63.
Lemma F_7274c : fetch_word Asan.M.loaded_segments (0x7274c : word) = Some W_7274c.
Proof. vm_refl. Qed.
Lemma D_7274c : decode_any W_7274c = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72750 : bv 32 := 0x00060413.
Lemma F_72750 : fetch_word Asan.M.loaded_segments (0x72750 : word) = Some W_72750.
Proof. vm_refl. Qed.
Lemma D_72750 : decode_any W_72750 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72754 : bv 32 := 0x0ff00513.
Lemma F_72754 : fetch_word Asan.M.loaded_segments (0x72754 : word) = Some W_72754.
Proof. vm_refl. Qed.
Lemma D_72754 : decode_any W_72754 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72758 : bv 32 := 0x00aa6463.
Lemma F_72758 : fetch_word Asan.M.loaded_segments (0x72758 : word) = Some W_72758.
Proof. vm_refl. Qed.
Lemma D_72758 : decode_any W_72758 = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7275c : bv 32 := 0x0ff00a13.
Lemma F_7275c : fetch_word Asan.M.loaded_segments (0x7275c : word) = Some W_7275c.
Proof. vm_refl. Qed.
Lemma D_7275c : decode_any W_7275c = Some (OpImm ALU_ADD 20 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72760 : bv 32 := 0x00013023.
Lemma F_72760 : fetch_word Asan.M.loaded_segments (0x72760 : word) = Some W_72760.
Proof. vm_refl. Qed.
Lemma D_72760 : decode_any W_72760 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72764 : bv 32 := 0x00043023.
Lemma F_72764 : fetch_word Asan.M.loaded_segments (0x72764 : word) = Some W_72764.
Proof. vm_refl. Qed.
Lemma D_72764 : decode_any W_72764 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72768 : bv 32 := 0x001a0913.
Lemma F_72768 : fetch_word Asan.M.loaded_segments (0x72768 : word) = Some W_72768.
Proof. vm_refl. Qed.
Lemma D_72768 : decode_any W_72768 = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7276c : bv 32 := 0x00010613.
Lemma F_7276c : fetch_word Asan.M.loaded_segments (0x7276c : word) = Some W_7276c.
Proof. vm_refl. Qed.
Lemma D_7276c : decode_any W_7276c = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72770 : bv 32 := 0x00048513.
Lemma F_72770 : fetch_word Asan.M.loaded_segments (0x72770 : word) = Some W_72770.
Proof. vm_refl. Qed.
Lemma D_72770 : decode_any W_72770 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72774 : bv 32 := 0x00090593.
Lemma F_72774 : fetch_word Asan.M.loaded_segments (0x72774 : word) = Some W_72774.
Proof. vm_refl. Qed.
Lemma D_72774 : decode_any W_72774 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72778 : bv 32 := 0x00040693.
Lemma F_72778 : fetch_word Asan.M.loaded_segments (0x72778 : word) = Some W_72778.
Proof. vm_refl. Qed.
Lemma D_72778 : decode_any W_72778 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7277c : bv 32 := 0x0b0000ef.
Lemma F_7277c : fetch_word Asan.M.loaded_segments (0x7277c : word) = Some W_7277c.
Proof. vm_refl. Qed.
Lemma D_7277c : decode_any W_7277c = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72780 : bv 32 := 0x06050263.
Lemma F_72780 : fetch_word Asan.M.loaded_segments (0x72780 : word) = Some W_72780.
Proof. vm_refl. Qed.
Lemma D_72780 : decode_any W_72780 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72784 : bv 32 := 0x008a961b.
Lemma F_72784 : fetch_word Asan.M.loaded_segments (0x72784 : word) = Some W_72784.
Proof. vm_refl. Qed.
Lemma D_72784 : decode_any W_72784 = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72788 : bv 32 := 0x0009b583.
Lemma F_72788 : fetch_word Asan.M.loaded_segments (0x72788 : word) = Some W_72788.
Proof. vm_refl. Qed.
Lemma D_72788 : decode_any W_72788 = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7278c : bv 32 := 0x01466633.
Lemma F_7278c : fetch_word Asan.M.loaded_segments (0x7278c : word) = Some W_7278c.
Proof. vm_refl. Qed.
Lemma D_7278c : decode_any W_7278c = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72790 : bv 32 := 0x00c53023.
Lemma F_72790 : fetch_word Asan.M.loaded_segments (0x72790 : word) = Some W_72790.
Proof. vm_refl. Qed.
Lemma D_72790 : decode_any W_72790 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72794 : bv 32 := 0x00850513.
Lemma F_72794 : fetch_word Asan.M.loaded_segments (0x72794 : word) = Some W_72794.
Proof. vm_refl. Qed.
Lemma D_72794 : decode_any W_72794 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72798 : bv 32 := 0x003a1613.
Lemma F_72798 : fetch_word Asan.M.loaded_segments (0x72798 : word) = Some W_72798.
Proof. vm_refl. Qed.
Lemma D_72798 : decode_any W_72798 = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7279c : bv 32 := 0x9a5f30ef.
Lemma F_7279c : fetch_word Asan.M.loaded_segments (0x7279c : word) = Some W_7279c.
Proof. vm_refl. Qed.
Lemma D_7279c : decode_any W_7279c = Some (Jal 1 2046372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727a0 : bv 32 := 0x00013503.
Lemma F_727a0 : fetch_word Asan.M.loaded_segments (0x727a0 : word) = Some W_727a0.
Proof. vm_refl. Qed.
Lemma D_727a0 : decode_any W_727a0 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727a4 : bv 32 := 0x01055513.
Lemma F_727a4 : fetch_word Asan.M.loaded_segments (0x727a4 : word) = Some W_727a4.
Proof. vm_refl. Qed.
Lemma D_727a4 : decode_any W_727a4 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727a8 : bv 32 := 0xff057513.
Lemma F_727a8 : fetch_word Asan.M.loaded_segments (0x727a8 : word) = Some W_727a8.
Proof. vm_refl. Qed.
Lemma D_727a8 : decode_any W_727a8 = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727ac : bv 32 := 0x00a48533.
Lemma F_727ac : fetch_word Asan.M.loaded_segments (0x727ac : word) = Some W_727ac.
Proof. vm_refl. Qed.
Lemma D_727ac : decode_any W_727ac = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727b0 : bv 32 := 0x01850513.
Lemma F_727b0 : fetch_word Asan.M.loaded_segments (0x727b0 : word) = Some W_727b0.
Proof. vm_refl. Qed.
Lemma D_727b0 : decode_any W_727b0 = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727b4 : bv 32 := 0x0325252f.
Lemma F_727b4 : fetch_word Asan.M.loaded_segments (0x727b4 : word) = Some W_727b4.
Proof. vm_refl. Qed.
Lemma D_727b4 : decode_any W_727b4 = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727b8 : bv 32 := 0x001005b7.
Lemma F_727b8 : fetch_word Asan.M.loaded_segments (0x727b8 : word) = Some W_727b8.
Proof. vm_refl. Qed.
Lemma D_727b8 : decode_any W_727b8 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727bc : bv 32 := 0x02051513.
Lemma F_727bc : fetch_word Asan.M.loaded_segments (0x727bc : word) = Some W_727bc.
Proof. vm_refl. Qed.
Lemma D_727bc : decode_any W_727bc = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727c0 : bv 32 := 0x02055513.
Lemma F_727c0 : fetch_word Asan.M.loaded_segments (0x727c0 : word) = Some W_727c0.
Proof. vm_refl. Qed.
Lemma D_727c0 : decode_any W_727c0 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727c4 : bv 32 := 0x00a90533.
Lemma F_727c4 : fetch_word Asan.M.loaded_segments (0x727c4 : word) = Some W_727c4.
Proof. vm_refl. Qed.
Lemma D_727c4 : decode_any W_727c4 = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727c8 : bv 32 := 0x00043603.
Lemma F_727c8 : fetch_word Asan.M.loaded_segments (0x727c8 : word) = Some W_727c8.
Proof. vm_refl. Qed.
Lemma D_727c8 : decode_any W_727c8 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727cc : bv 32 := 0x00b54533.
Lemma F_727cc : fetch_word Asan.M.loaded_segments (0x727cc : word) = Some W_727cc.
Proof. vm_refl. Qed.
Lemma D_727cc : decode_any W_727cc = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727d0 : bv 32 := 0x00012583.
Lemma F_727d0 : fetch_word Asan.M.loaded_segments (0x727d0 : word) = Some W_727d0.
Proof. vm_refl. Qed.
Lemma D_727d0 : decode_any W_727d0 = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727d4 : bv 32 := 0x00153513.
Lemma F_727d4 : fetch_word Asan.M.loaded_segments (0x727d4 : word) = Some W_727d4.
Proof. vm_refl. Qed.
Lemma D_727d4 : decode_any W_727d4 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727d8 : bv 32 := 0x00a60533.
Lemma F_727d8 : fetch_word Asan.M.loaded_segments (0x727d8 : word) = Some W_727d8.
Proof. vm_refl. Qed.
Lemma D_727d8 : decode_any W_727d8 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727dc : bv 32 := 0x00a43023.
Lemma F_727dc : fetch_word Asan.M.loaded_segments (0x727dc : word) = Some W_727dc.
Proof. vm_refl. Qed.
Lemma D_727dc : decode_any W_727dc = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727e0 : bv 32 := 0x0015851b.
Lemma F_727e0 : fetch_word Asan.M.loaded_segments (0x727e0 : word) = Some W_727e0.
Proof. vm_refl. Qed.
Lemma D_727e0 : decode_any W_727e0 = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727e4 : bv 32 := 0x03813083.
Lemma F_727e4 : fetch_word Asan.M.loaded_segments (0x727e4 : word) = Some W_727e4.
Proof. vm_refl. Qed.
Lemma D_727e4 : decode_any W_727e4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727e8 : bv 32 := 0x03013403.
Lemma F_727e8 : fetch_word Asan.M.loaded_segments (0x727e8 : word) = Some W_727e8.
Proof. vm_refl. Qed.
Lemma D_727e8 : decode_any W_727e8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727ec : bv 32 := 0x02813483.
Lemma F_727ec : fetch_word Asan.M.loaded_segments (0x727ec : word) = Some W_727ec.
Proof. vm_refl. Qed.
Lemma D_727ec : decode_any W_727ec = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727f0 : bv 32 := 0x02013903.
Lemma F_727f0 : fetch_word Asan.M.loaded_segments (0x727f0 : word) = Some W_727f0.
Proof. vm_refl. Qed.
Lemma D_727f0 : decode_any W_727f0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727f4 : bv 32 := 0x01813983.
Lemma F_727f4 : fetch_word Asan.M.loaded_segments (0x727f4 : word) = Some W_727f4.
Proof. vm_refl. Qed.
Lemma D_727f4 : decode_any W_727f4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727f8 : bv 32 := 0x01013a03.
Lemma F_727f8 : fetch_word Asan.M.loaded_segments (0x727f8 : word) = Some W_727f8.
Proof. vm_refl. Qed.
Lemma D_727f8 : decode_any W_727f8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_727fc : bv 32 := 0x00813a83.
Lemma F_727fc : fetch_word Asan.M.loaded_segments (0x727fc : word) = Some W_727fc.
Proof. vm_refl. Qed.
Lemma D_727fc : decode_any W_727fc = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72800 : bv 32 := 0x04010113.
Lemma F_72800 : fetch_word Asan.M.loaded_segments (0x72800 : word) = Some W_72800.
Proof. vm_refl. Qed.
Lemma D_72800 : decode_any W_72800 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72804 : bv 32 := 0x00008067.
Lemma F_72804 : fetch_word Asan.M.loaded_segments (0x72804 : word) = Some W_72804.
Proof. vm_refl. Qed.
Lemma D_72804 : decode_any W_72804 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72808 : bv 32 := 0x020a9693.
Lemma F_72808 : fetch_word Asan.M.loaded_segments (0x72808 : word) = Some W_72808.
Proof. vm_refl. Qed.
Lemma D_72808 : decode_any W_72808 = Some (ShiftImm ALU_SLL 13 21 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7280c : bv 32 := 0x0206d693.
Lemma F_7280c : fetch_word Asan.M.loaded_segments (0x7280c : word) = Some W_7280c.
Proof. vm_refl. Qed.
Lemma D_7280c : decode_any W_7280c = Some (ShiftImm ALU_SRL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72810 : bv 32 := 0x0ff6f713.
Lemma F_72810 : fetch_word Asan.M.loaded_segments (0x72810 : word) = Some W_72810.
Proof. vm_refl. Qed.
Lemma D_72810 : decode_any W_72810 = Some (OpImm ALU_AND 14 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72814 : bv 32 := 0xfffae517.
Lemma F_72814 : fetch_word Asan.M.loaded_segments (0x72814 : word) = Some W_72814.
Proof. vm_refl. Qed.
Lemma D_72814 : decode_any W_72814 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72818 : bv 32 := 0xfffa5597.
Lemma F_72818 : fetch_word Asan.M.loaded_segments (0x72818 : word) = Some W_72818.
Proof. vm_refl. Qed.
Lemma D_72818 : decode_any W_72818 = Some (Auipc 11 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7281c : bv 32 := 0xc5550513.
Lemma F_7281c : fetch_word Asan.M.loaded_segments (0x7281c : word) = Some W_7281c.
Proof. vm_refl. Qed.
Lemma D_7281c : decode_any W_7281c = Some (OpImm ALU_ADD 10 10 3157, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72820 : bv 32 := 0x97858613.
Lemma F_72820 : fetch_word Asan.M.loaded_segments (0x72820 : word) = Some W_72820.
Proof. vm_refl. Qed.
Lemma D_72820 : decode_any W_72820 = Some (OpImm ALU_ADD 12 11 2424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72824 : bv 32 := 0x01d00593.
Lemma F_72824 : fetch_word Asan.M.loaded_segments (0x72824 : word) = Some W_72824.
Proof. vm_refl. Qed.
Lemma D_72824 : decode_any W_72824 = Some (OpImm ALU_ADD 11 0 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72828 : bv 32 := 0xe9cfb0ef.
Lemma F_72828 : fetch_word Asan.M.loaded_segments (0x72828 : word) = Some W_72828.
Proof. vm_refl. Qed.
Lemma D_72828 : decode_any W_72828 = Some (Jal 1 2078364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7282c : bv 32 := 0xff010113.
Lemma F_7282c : fetch_word Asan.M.loaded_segments (0x7282c : word) = Some W_7282c.
Proof. vm_refl. Qed.
Lemma D_7282c : decode_any W_7282c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72830 : bv 32 := 0x00113423.
Lemma F_72830 : fetch_word Asan.M.loaded_segments (0x72830 : word) = Some W_72830.
Proof. vm_refl. Qed.
Lemma D_72830 : decode_any W_72830 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72834 : bv 32 := 0x00813023.
Lemma F_72834 : fetch_word Asan.M.loaded_segments (0x72834 : word) = Some W_72834.
Proof. vm_refl. Qed.
Lemma D_72834 : decode_any W_72834 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72838 : bv 32 := 0x00058793.
Lemma F_72838 : fetch_word Asan.M.loaded_segments (0x72838 : word) = Some W_72838.
Proof. vm_refl. Qed.
Lemma D_72838 : decode_any W_72838 = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7283c : bv 32 := 0x00050593.
Lemma F_7283c : fetch_word Asan.M.loaded_segments (0x7283c : word) = Some W_7283c.
Proof. vm_refl. Qed.
Lemma D_7283c : decode_any W_7283c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72840 : bv 32 := 0x00f5342f.
Lemma F_72840 : fetch_word Asan.M.loaded_segments (0x72840 : word) = Some W_72840.
Proof. vm_refl. Qed.
Lemma D_72840 : decode_any W_72840 = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72844 : bv 32 := 0xfff78513.
Lemma F_72844 : fetch_word Asan.M.loaded_segments (0x72844 : word) = Some W_72844.
Proof. vm_refl. Qed.
Lemma D_72844 : decode_any W_72844 = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72848 : bv 32 := 0x01445293.
Lemma F_72848 : fetch_word Asan.M.loaded_segments (0x72848 : word) = Some W_72848.
Proof. vm_refl. Qed.
Lemma D_72848 : decode_any W_72848 = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7284c : bv 32 := 0x00850733.
Lemma F_7284c : fetch_word Asan.M.loaded_segments (0x7284c : word) = Some W_7284c.
Proof. vm_refl. Qed.
Lemma D_7284c : decode_any W_7284c = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72850 : bv 32 := 0x01475313.
Lemma F_72850 : fetch_word Asan.M.loaded_segments (0x72850 : word) = Some W_72850.
Proof. vm_refl. Qed.
Lemma D_72850 : decode_any W_72850 = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72854 : bv 32 := 0x04629863.
Lemma F_72854 : fetch_word Asan.M.loaded_segments (0x72854 : word) = Some W_72854.
Proof. vm_refl. Qed.
Lemma D_72854 : decode_any W_72854 = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72858 : bv 32 := 0x02045513.
Lemma F_72858 : fetch_word Asan.M.loaded_segments (0x72858 : word) = Some W_72858.
Proof. vm_refl. Qed.
Lemma D_72858 : decode_any W_72858 = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7285c : bv 32 := 0x00050c63.
Lemma F_7285c : fetch_word Asan.M.loaded_segments (0x7285c : word) = Some W_7285c.
Proof. vm_refl. Qed.
Lemma D_7285c : decode_any W_7285c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72860 : bv 32 := 0x00000513.
Lemma F_72860 : fetch_word Asan.M.loaded_segments (0x72860 : word) = Some W_72860.
Proof. vm_refl. Qed.
Lemma D_72860 : decode_any W_72860 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72864 : bv 32 := 0x00813083.
Lemma F_72864 : fetch_word Asan.M.loaded_segments (0x72864 : word) = Some W_72864.
Proof. vm_refl. Qed.
Lemma D_72864 : decode_any W_72864 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72868 : bv 32 := 0x00013403.
Lemma F_72868 : fetch_word Asan.M.loaded_segments (0x72868 : word) = Some W_72868.
Proof. vm_refl. Qed.
Lemma D_72868 : decode_any W_72868 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7286c : bv 32 := 0x01010113.
Lemma F_7286c : fetch_word Asan.M.loaded_segments (0x7286c : word) = Some W_7286c.
Proof. vm_refl. Qed.
Lemma D_7286c : decode_any W_7286c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72870 : bv 32 := 0x00008067.
Lemma F_72870 : fetch_word Asan.M.loaded_segments (0x72870 : word) = Some W_72870.
Proof. vm_refl. Qed.
Lemma D_72870 : decode_any W_72870 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72874 : bv 32 := 0x00863023.
Lemma F_72874 : fetch_word Asan.M.loaded_segments (0x72874 : word) = Some W_72874.
Proof. vm_refl. Qed.
Lemma D_72874 : decode_any W_72874 = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72878 : bv 32 := 0x00429613.
Lemma F_72878 : fetch_word Asan.M.loaded_segments (0x72878 : word) = Some W_72878.
Proof. vm_refl. Qed.
Lemma D_72878 : decode_any W_72878 = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7287c : bv 32 := 0x00c58633.
Lemma F_7287c : fetch_word Asan.M.loaded_segments (0x7287c : word) = Some W_7287c.
Proof. vm_refl. Qed.
Lemma D_7287c : decode_any W_7287c = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72880 : bv 32 := 0x01063503.
Lemma F_72880 : fetch_word Asan.M.loaded_segments (0x72880 : word) = Some W_72880.
Proof. vm_refl. Qed.
Lemma D_72880 : decode_any W_72880 = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72884 : bv 32 := 0x0a050a63.
Lemma F_72884 : fetch_word Asan.M.loaded_segments (0x72884 : word) = Some W_72884.
Proof. vm_refl. Qed.
Lemma D_72884 : decode_any W_72884 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72888 : bv 32 := 0x02c41413.
Lemma F_72888 : fetch_word Asan.M.loaded_segments (0x72888 : word) = Some W_72888.
Proof. vm_refl. Qed.
Lemma D_72888 : decode_any W_72888 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7288c : bv 32 := 0x02945413.
Lemma F_7288c : fetch_word Asan.M.loaded_segments (0x7288c : word) = Some W_7288c.
Proof. vm_refl. Qed.
Lemma D_7288c : decode_any W_7288c = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72890 : bv 32 := 0x00850533.
Lemma F_72890 : fetch_word Asan.M.loaded_segments (0x72890 : word) = Some W_72890.
Proof. vm_refl. Qed.
Lemma D_72890 : decode_any W_72890 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72894 : bv 32 := 0x00813083.
Lemma F_72894 : fetch_word Asan.M.loaded_segments (0x72894 : word) = Some W_72894.
Proof. vm_refl. Qed.
Lemma D_72894 : decode_any W_72894 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72898 : bv 32 := 0x00013403.
Lemma F_72898 : fetch_word Asan.M.loaded_segments (0x72898 : word) = Some W_72898.
Proof. vm_refl. Qed.
Lemma D_72898 : decode_any W_72898 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7289c : bv 32 := 0x01010113.
Lemma F_7289c : fetch_word Asan.M.loaded_segments (0x7289c : word) = Some W_7289c.
Proof. vm_refl. Qed.
Lemma D_7289c : decode_any W_7289c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_728a0 : bv 32 := 0x00008067.
Lemma F_728a0 : fetch_word Asan.M.loaded_segments (0x728a0 : word) = Some W_728a0.
Proof. vm_refl. Qed.
Lemma D_728a0 : decode_any W_728a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
