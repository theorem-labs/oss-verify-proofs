(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6d928 : bv 32 := 0x00050663.
Lemma F_6d928 : fetch_word Plain.M.loaded_segments (0x6d980 : word) = Some W_6d928.
Proof. vm_refl. Qed.
Lemma D_6d928 : decode_any W_6d928 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d92c : bv 32 := 0x00852503.
Lemma F_6d92c : fetch_word Plain.M.loaded_segments (0x6d984 : word) = Some W_6d92c.
Proof. vm_refl. Qed.
Lemma D_6d92c : decode_any W_6d92c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d930 : bv 32 := 0x00008067.
Lemma F_6d930 : fetch_word Plain.M.loaded_segments (0x6d988 : word) = Some W_6d930.
Proof. vm_refl. Qed.
Lemma D_6d930 : decode_any W_6d930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f67c : bv 32 := 0xfd010113.
Lemma F_8f67c : fetch_word Plain.M.loaded_segments (0x8f6d4 : word) = Some W_8f67c.
Proof. vm_refl. Qed.
Lemma D_8f67c : decode_any W_8f67c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f680 : bv 32 := 0x02113423.
Lemma F_8f680 : fetch_word Plain.M.loaded_segments (0x8f6d8 : word) = Some W_8f680.
Proof. vm_refl. Qed.
Lemma D_8f680 : decode_any W_8f680 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f684 : bv 32 := 0x02813023.
Lemma F_8f684 : fetch_word Plain.M.loaded_segments (0x8f6dc : word) = Some W_8f684.
Proof. vm_refl. Qed.
Lemma D_8f684 : decode_any W_8f684 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f688 : bv 32 := 0x00913c23.
Lemma F_8f688 : fetch_word Plain.M.loaded_segments (0x8f6e0 : word) = Some W_8f688.
Proof. vm_refl. Qed.
Lemma D_8f688 : decode_any W_8f688 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f68c : bv 32 := 0x01213823.
Lemma F_8f68c : fetch_word Plain.M.loaded_segments (0x8f6e4 : word) = Some W_8f68c.
Proof. vm_refl. Qed.
Lemma D_8f68c : decode_any W_8f68c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f690 : bv 32 := 0x01313423.
Lemma F_8f690 : fetch_word Plain.M.loaded_segments (0x8f6e8 : word) = Some W_8f690.
Proof. vm_refl. Qed.
Lemma D_8f690 : decode_any W_8f690 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f694 : bv 32 := 0x00050413.
Lemma F_8f694 : fetch_word Plain.M.loaded_segments (0x8f6ec : word) = Some W_8f694.
Proof. vm_refl. Qed.
Lemma D_8f694 : decode_any W_8f694 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f698 : bv 32 := 0x0006b023.
Lemma F_8f698 : fetch_word Plain.M.loaded_segments (0x8f6f0 : word) = Some W_8f698.
Proof. vm_refl. Qed.
Lemma D_8f698 : decode_any W_8f698 = Some (Store SZ8 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f69c : bv 32 := 0x08058e63.
Lemma F_8f69c : fetch_word Plain.M.loaded_segments (0x8f6f4 : word) = Some W_8f69c.
Proof. vm_refl. Qed.
Lemma D_8f69c : decode_any W_8f69c = Some (Branch BC_EQ 11 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6a0 : bv 32 := 0x0c060063.
Lemma F_8f6a0 : fetch_word Plain.M.loaded_segments (0x8f6f8 : word) = Some W_8f6a0.
Proof. vm_refl. Qed.
Lemma D_8f6a0 : decode_any W_8f6a0 = Some (Branch BC_EQ 12 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6a4 : bv 32 := 0x00060913.
Lemma F_8f6a4 : fetch_word Plain.M.loaded_segments (0x8f6fc : word) = Some W_8f6a4.
Proof. vm_refl. Qed.
Lemma D_8f6a4 : decode_any W_8f6a4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6a8 : bv 32 := 0x00068993.
Lemma F_8f6a8 : fetch_word Plain.M.loaded_segments (0x8f700 : word) = Some W_8f6a8.
Proof. vm_refl. Qed.
Lemma D_8f6a8 : decode_any W_8f6a8 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6ac : bv 32 := 0x00058493.
Lemma F_8f6ac : fetch_word Plain.M.loaded_segments (0x8f704 : word) = Some W_8f6ac.
Proof. vm_refl. Qed.
Lemma D_8f6ac : decode_any W_8f6ac = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6b0 : bv 32 := 0x00058513.
Lemma F_8f6b0 : fetch_word Plain.M.loaded_segments (0x8f708 : word) = Some W_8f6b0.
Proof. vm_refl. Qed.
Lemma D_8f6b0 : decode_any W_8f6b0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6b4 : bv 32 := 0xa74de0ef.
Lemma F_8f6b4 : fetch_word Plain.M.loaded_segments (0x8f70c : word) = Some W_8f6b4.
Proof. vm_refl. Qed.
Lemma D_8f6b4 : decode_any W_8f6b4 = Some (Jal 1 1958516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6b8 : bv 32 := 0x00100593.
Lemma F_8f6b8 : fetch_word Plain.M.loaded_segments (0x8f710 : word) = Some W_8f6b8.
Proof. vm_refl. Qed.
Lemma D_8f6b8 : decode_any W_8f6b8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6bc : bv 32 := 0x0cb51663.
Lemma F_8f6bc : fetch_word Plain.M.loaded_segments (0x8f714 : word) = Some W_8f6bc.
Proof. vm_refl. Qed.
Lemma D_8f6bc : decode_any W_8f6bc = Some (Branch BC_NE 10 11 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6c0 : bv 32 := 0x00410593.
Lemma F_8f6c0 : fetch_word Plain.M.loaded_segments (0x8f718 : word) = Some W_8f6c0.
Proof. vm_refl. Qed.
Lemma D_8f6c0 : decode_any W_8f6c0 = Some (OpImm ALU_ADD 11 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6c4 : bv 32 := 0x00010613.
Lemma F_8f6c4 : fetch_word Plain.M.loaded_segments (0x8f71c : word) = Some W_8f6c4.
Proof. vm_refl. Qed.
Lemma D_8f6c4 : decode_any W_8f6c4 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6c8 : bv 32 := 0x00090513.
Lemma F_8f6c8 : fetch_word Plain.M.loaded_segments (0x8f720 : word) = Some W_8f6c8.
Proof. vm_refl. Qed.
Lemma D_8f6c8 : decode_any W_8f6c8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6cc : bv 32 := 0x00000693.
Lemma F_8f6cc : fetch_word Plain.M.loaded_segments (0x8f724 : word) = Some W_8f6cc.
Proof. vm_refl. Qed.
Lemma D_8f6cc : decode_any W_8f6cc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6d0 : bv 32 := 0x00000713.
Lemma F_8f6d0 : fetch_word Plain.M.loaded_segments (0x8f728 : word) = Some W_8f6d0.
Proof. vm_refl. Qed.
Lemma D_8f6d0 : decode_any W_8f6d0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6d4 : bv 32 := 0x71d020ef.
Lemma F_8f6d4 : fetch_word Plain.M.loaded_segments (0x8f72c : word) = Some W_8f6d4.
Proof. vm_refl. Qed.
Lemma D_8f6d4 : decode_any W_8f6d4 = Some (Jal 1 12060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6d8 : bv 32 := 0x00412503.
Lemma F_8f6d8 : fetch_word Plain.M.loaded_segments (0x8f730 : word) = Some W_8f6d8.
Proof. vm_refl. Qed.
Lemma D_8f6d8 : decode_any W_8f6d8 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6dc : bv 32 := 0x0e050863.
Lemma F_8f6dc : fetch_word Plain.M.loaded_segments (0x8f734 : word) = Some W_8f6dc.
Proof. vm_refl. Qed.
Lemma D_8f6dc : decode_any W_8f6dc = Some (Branch BC_EQ 10 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6e0 : bv 32 := 0x00012503.
Lemma F_8f6e0 : fetch_word Plain.M.loaded_segments (0x8f738 : word) = Some W_8f6e0.
Proof. vm_refl. Qed.
Lemma D_8f6e0 : decode_any W_8f6e0 = Some (Load SZ4 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6e4 : bv 32 := 0x0e050463.
Lemma F_8f6e4 : fetch_word Plain.M.loaded_segments (0x8f73c : word) = Some W_8f6e4.
Proof. vm_refl. Qed.
Lemma D_8f6e4 : decode_any W_8f6e4 = Some (Branch BC_EQ 10 0 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6e8 : bv 32 := 0x10040c63.
Lemma F_8f6e8 : fetch_word Plain.M.loaded_segments (0x8f740 : word) = Some W_8f6e8.
Proof. vm_refl. Qed.
Lemma D_8f6e8 : decode_any W_8f6e8 = Some (Branch BC_EQ 8 0 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7f4 : bv 32 := 0x8d1d30ef.
Lemma F_8f7f4 : fetch_word Plain.M.loaded_segments (0x8f84c : word) = Some W_8f7f4.
Proof. vm_refl. Qed.
Lemma D_8f7f4 : decode_any W_8f7f4 = Some (Jal 1 1915088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7f8 : bv 32 := 0x00050413.
Lemma F_8f7f8 : fetch_word Plain.M.loaded_segments (0x8f850 : word) = Some W_8f7f8.
Proof. vm_refl. Qed.
Lemma D_8f7f8 : decode_any W_8f7f8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7fc : bv 32 := 0x0200006f.
Lemma F_8f7fc : fetch_word Plain.M.loaded_segments (0x8f854 : word) = Some W_8f7fc.
Proof. vm_refl. Qed.
Lemma D_8f7fc : decode_any W_8f7fc = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f800 : bv 32 := 0x00048513.
Lemma F_8f800 : fetch_word Plain.M.loaded_segments (0x8f858 : word) = Some W_8f800.
Proof. vm_refl. Qed.
Lemma D_8f800 : decode_any W_8f800 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f804 : bv 32 := 0xbacdd0ef.
Lemma F_8f804 : fetch_word Plain.M.loaded_segments (0x8f85c : word) = Some W_8f804.
Proof. vm_refl. Qed.
Lemma D_8f804 : decode_any W_8f804 = Some (Jal 1 1954732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f808 : bv 32 := 0x02050a63.
Lemma F_8f808 : fetch_word Plain.M.loaded_segments (0x8f860 : word) = Some W_8f808.
Proof. vm_refl. Qed.
Lemma D_8f808 : decode_any W_8f808 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f80c : bv 32 := 0x00050413.
Lemma F_8f80c : fetch_word Plain.M.loaded_segments (0x8f864 : word) = Some W_8f80c.
Proof. vm_refl. Qed.
Lemma D_8f80c : decode_any W_8f80c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f810 : bv 32 := 0x00048513.
Lemma F_8f810 : fetch_word Plain.M.loaded_segments (0x8f868 : word) = Some W_8f810.
Proof. vm_refl. Qed.
Lemma D_8f810 : decode_any W_8f810 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f814 : bv 32 := 0xbcddd0ef.
Lemma F_8f814 : fetch_word Plain.M.loaded_segments (0x8f86c : word) = Some W_8f814.
Proof. vm_refl. Qed.
Lemma D_8f814 : decode_any W_8f814 = Some (Jal 1 1956812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f818 : bv 32 := 0x00a9b023.
Lemma F_8f818 : fetch_word Plain.M.loaded_segments (0x8f870 : word) = Some W_8f818.
Proof. vm_refl. Qed.
Lemma D_8f818 : decode_any W_8f818 = Some (Store SZ8 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f81c : bv 32 := 0x00040513.
Lemma F_8f81c : fetch_word Plain.M.loaded_segments (0x8f874 : word) = Some W_8f81c.
Proof. vm_refl. Qed.
Lemma D_8f81c : decode_any W_8f81c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f820 : bv 32 := 0x02813083.
Lemma F_8f820 : fetch_word Plain.M.loaded_segments (0x8f878 : word) = Some W_8f820.
Proof. vm_refl. Qed.
Lemma D_8f820 : decode_any W_8f820 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f824 : bv 32 := 0x02013403.
Lemma F_8f824 : fetch_word Plain.M.loaded_segments (0x8f87c : word) = Some W_8f824.
Proof. vm_refl. Qed.
Lemma D_8f824 : decode_any W_8f824 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f828 : bv 32 := 0x01813483.
Lemma F_8f828 : fetch_word Plain.M.loaded_segments (0x8f880 : word) = Some W_8f828.
Proof. vm_refl. Qed.
Lemma D_8f828 : decode_any W_8f828 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f82c : bv 32 := 0x01013903.
Lemma F_8f82c : fetch_word Plain.M.loaded_segments (0x8f884 : word) = Some W_8f82c.
Proof. vm_refl. Qed.
Lemma D_8f82c : decode_any W_8f82c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f830 : bv 32 := 0x00813983.
Lemma F_8f830 : fetch_word Plain.M.loaded_segments (0x8f888 : word) = Some W_8f830.
Proof. vm_refl. Qed.
Lemma D_8f830 : decode_any W_8f830 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f834 : bv 32 := 0x03010113.
Lemma F_8f834 : fetch_word Plain.M.loaded_segments (0x8f88c : word) = Some W_8f834.
Proof. vm_refl. Qed.
Lemma D_8f834 : decode_any W_8f834 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f838 : bv 32 := 0x00008067.
Lemma F_8f838 : fetch_word Plain.M.loaded_segments (0x8f890 : word) = Some W_8f838.
Proof. vm_refl. Qed.
Lemma D_8f838 : decode_any W_8f838 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f83c : bv 32 := 0x00083517.
Lemma F_8f83c : fetch_word Plain.M.loaded_segments (0x8f894 : word) = Some W_8f83c.
Proof. vm_refl. Qed.
Lemma D_8f83c : decode_any W_8f83c = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f840 : bv 32 := 0xd3453503.
Lemma F_8f840 : fetch_word Plain.M.loaded_segments (0x8f898 : word) = Some W_8f840.
Proof. vm_refl. Qed.
Lemma D_8f840 : decode_any W_8f840 = Some (Load SZ8 true 10 10 3380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f844 : bv 32 := 0x00052503.
Lemma F_8f844 : fetch_word Plain.M.loaded_segments (0x8f89c : word) = Some W_8f844.
Proof. vm_refl. Qed.
Lemma D_8f844 : decode_any W_8f844 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f848 : bv 32 := 0x00500593.
Lemma F_8f848 : fetch_word Plain.M.loaded_segments (0x8f8a0 : word) = Some W_8f848.
Proof. vm_refl. Qed.
Lemma D_8f848 : decode_any W_8f848 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f84c : bv 32 := 0x00a5ce63.
Lemma F_8f84c : fetch_word Plain.M.loaded_segments (0x8f8a4 : word) = Some W_8f84c.
Proof. vm_refl. Qed.
Lemma D_8f84c : decode_any W_8f84c = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f850 : bv 32 := 0xfff83517.
Lemma F_8f850 : fetch_word Plain.M.loaded_segments (0x8f8a8 : word) = Some W_8f850.
Proof. vm_refl. Qed.
Lemma D_8f850 : decode_any W_8f850 = Some (Auipc 10 1048451, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f854 : bv 32 := 0xfff8c597.
Lemma F_8f854 : fetch_word Plain.M.loaded_segments (0x8f8ac : word) = Some W_8f854.
Proof. vm_refl. Qed.
Lemma D_8f854 : decode_any W_8f854 = Some (Auipc 11 1048460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f858 : bv 32 := 0xe3250513.
Lemma F_8f858 : fetch_word Plain.M.loaded_segments (0x8f8b0 : word) = Some W_8f858.
Proof. vm_refl. Qed.
Lemma D_8f858 : decode_any W_8f858 = Some (OpImm ALU_ADD 10 10 3634, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f85c : bv 32 := 0xc5f58593.
Lemma F_8f85c : fetch_word Plain.M.loaded_segments (0x8f8b4 : word) = Some W_8f85c.
Proof. vm_refl. Qed.
Lemma D_8f85c : decode_any W_8f85c = Some (OpImm ALU_ADD 11 11 3167, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f860 : bv 32 := 0x00000613.
Lemma F_8f860 : fetch_word Plain.M.loaded_segments (0x8f8b8 : word) = Some W_8f860.
Proof. vm_refl. Qed.
Lemma D_8f860 : decode_any W_8f860 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f864 : bv 32 := 0xf91ff06f.
Lemma F_8f864 : fetch_word Plain.M.loaded_segments (0x8f8bc : word) = Some W_8f864.
Proof. vm_refl. Qed.
Lemma D_8f864 : decode_any W_8f864 = Some (Jal 0 2097040, 4%Z).
Proof. vm_refl. Qed.

