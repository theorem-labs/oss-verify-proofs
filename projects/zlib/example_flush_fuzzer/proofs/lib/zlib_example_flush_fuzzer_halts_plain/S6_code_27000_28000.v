(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.World Require Import Src_zlib_example_flush_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_276c8 : bv 32 := 0x0035f693.
Lemma F_276c8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27800 : word) = Some W_276c8.
Proof. vm_refl. Qed.
Lemma D_276c8 : decode_any W_276c8 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_276cc : bv 32 := 0x10068863.
Lemma F_276cc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27804 : word) = Some W_276cc.
Proof. vm_refl. Qed.
Lemma D_276cc : decode_any W_276cc = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_276d0 : bv 32 := 0x02060e63.
Lemma F_276d0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27808 : word) = Some W_276d0.
Proof. vm_refl. Qed.
Lemma D_276d0 : decode_any W_276d0 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_276d4 : bv 32 := 0x00158713.
Lemma F_276d4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2780c : word) = Some W_276d4.
Proof. vm_refl. Qed.
Lemma D_276d4 : decode_any W_276d4 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_276d8 : bv 32 := 0x00100793.
Lemma F_276d8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27810 : word) = Some W_276d8.
Proof. vm_refl. Qed.
Lemma D_276d8 : decode_any W_276d8 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_276dc : bv 32 := 0x00050693.
Lemma F_276dc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27814 : word) = Some W_276dc.
Proof. vm_refl. Qed.
Lemma D_276dc : decode_any W_276dc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_276e0 : bv 32 := 0x0005c883.
Lemma F_276e0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27818 : word) = Some W_276e0.
Proof. vm_refl. Qed.
Lemma D_276e0 : decode_any W_276e0 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_276e4 : bv 32 := 0x00060813.
Lemma F_276e4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2781c : word) = Some W_276e4.
Proof. vm_refl. Qed.
Lemma D_276e4 : decode_any W_276e4 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_276e8 : bv 32 := 0x00158593.
Lemma F_276e8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27820 : word) = Some W_276e8.
Proof. vm_refl. Qed.
Lemma D_276e8 : decode_any W_276e8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_276ec : bv 32 := 0x00377293.
Lemma F_276ec : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27824 : word) = Some W_276ec.
Proof. vm_refl. Qed.
Lemma D_276ec : decode_any W_276ec = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_276f0 : bv 32 := 0x01168023.
Lemma F_276f0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27828 : word) = Some W_276f0.
Proof. vm_refl. Qed.
Lemma D_276f0 : decode_any W_276f0 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_276f4 : bv 32 := 0x00168693.
Lemma F_276f4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2782c : word) = Some W_276f4.
Proof. vm_refl. Qed.
Lemma D_276f4 : decode_any W_276f4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_276f8 : bv 32 := 0xfff60613.
Lemma F_276f8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27830 : word) = Some W_276f8.
Proof. vm_refl. Qed.
Lemma D_276f8 : decode_any W_276f8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_276fc : bv 32 := 0x00028a63.
Lemma F_276fc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27834 : word) = Some W_276fc.
Proof. vm_refl. Qed.
Lemma D_276fc : decode_any W_276fc = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_27700 : bv 32 := 0x00170713.
Lemma F_27700 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27838 : word) = Some W_27700.
Proof. vm_refl. Qed.
Lemma D_27700 : decode_any W_27700 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27704 : bv 32 := 0xfcf81ee3.
Lemma F_27704 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2783c : word) = Some W_27704.
Proof. vm_refl. Qed.
Lemma D_27704 : decode_any W_27704 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_27708 : bv 32 := 0x0080006f.
Lemma F_27708 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27840 : word) = Some W_27708.
Proof. vm_refl. Qed.
Lemma D_27708 : decode_any W_27708 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2770c : bv 32 := 0x00050693.
Lemma F_2770c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27844 : word) = Some W_2770c.
Proof. vm_refl. Qed.
Lemma D_2770c : decode_any W_2770c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27710 : bv 32 := 0x0036f793.
Lemma F_27710 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27848 : word) = Some W_27710.
Proof. vm_refl. Qed.
Lemma D_27710 : decode_any W_27710 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_27714 : bv 32 := 0x0c078a63.
Lemma F_27714 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2784c : word) = Some W_27714.
Proof. vm_refl. Qed.
Lemma D_27714 : decode_any W_27714 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_27718 : bv 32 := 0x02000713.
Lemma F_27718 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27850 : word) = Some W_27718.
Proof. vm_refl. Qed.
Lemma D_27718 : decode_any W_27718 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_2771c : bv 32 := 0x02e67063.
Lemma F_2771c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27854 : word) = Some W_2771c.
Proof. vm_refl. Qed.
Lemma D_2771c : decode_any W_2771c = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_27720 : bv 32 := 0x01000713.
Lemma F_27720 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27858 : word) = Some W_27720.
Proof. vm_refl. Qed.
Lemma D_27720 : decode_any W_27720 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27724 : bv 32 := 0x24e67863.
Lemma F_27724 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2785c : word) = Some W_27724.
Proof. vm_refl. Qed.
Lemma D_27724 : decode_any W_27724 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_27728 : bv 32 := 0x00867713.
Lemma F_27728 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27860 : word) = Some W_27728.
Proof. vm_refl. Qed.
Lemma D_27728 : decode_any W_27728 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2772c : bv 32 := 0x2c071e63.
Lemma F_2772c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27864 : word) = Some W_2772c.
Proof. vm_refl. Qed.
Lemma D_2772c : decode_any W_2772c = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_27730 : bv 32 := 0x00467713.
Lemma F_27730 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27868 : word) = Some W_27730.
Proof. vm_refl. Qed.
Lemma D_27730 : decode_any W_27730 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27734 : bv 32 := 0x32071463.
Lemma F_27734 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2786c : word) = Some W_27734.
Proof. vm_refl. Qed.
Lemma D_27734 : decode_any W_27734 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_27738 : bv 32 := 0x3500006f.
Lemma F_27738 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27870 : word) = Some W_27738.
Proof. vm_refl. Qed.
Lemma D_27738 : decode_any W_27738 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_2773c : bv 32 := 0x0005a703.
Lemma F_2773c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27874 : word) = Some W_2773c.
Proof. vm_refl. Qed.
Lemma D_2773c : decode_any W_2773c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27740 : bv 32 := 0x00300813.
Lemma F_27740 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27878 : word) = Some W_27740.
Proof. vm_refl. Qed.
Lemma D_27740 : decode_any W_27740 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_27744 : bv 32 := 0x11078e63.
Lemma F_27744 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2787c : word) = Some W_27744.
Proof. vm_refl. Qed.
Lemma D_27744 : decode_any W_27744 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_27748 : bv 32 := 0x00200813.
Lemma F_27748 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27880 : word) = Some W_27748.
Proof. vm_refl. Qed.
Lemma D_27748 : decode_any W_27748 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_2774c : bv 32 := 0x19079c63.
Lemma F_2774c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27884 : word) = Some W_2774c.
Proof. vm_refl. Qed.
Lemma D_2774c : decode_any W_2774c = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_27750 : bv 32 := 0x00875793.
Lemma F_27750 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27888 : word) = Some W_27750.
Proof. vm_refl. Qed.
Lemma D_27750 : decode_any W_27750 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27754 : bv 32 := 0xffe60613.
Lemma F_27754 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2788c : word) = Some W_27754.
Proof. vm_refl. Qed.
Lemma D_27754 : decode_any W_27754 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_27758 : bv 32 := 0x00e68023.
Lemma F_27758 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27890 : word) = Some W_27758.
Proof. vm_refl. Qed.
Lemma D_27758 : decode_any W_27758 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2775c : bv 32 := 0x00f680a3.
Lemma F_2775c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27894 : word) = Some W_2775c.
Proof. vm_refl. Qed.
Lemma D_2775c : decode_any W_2775c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27760 : bv 32 := 0x00268693.
Lemma F_27760 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27898 : word) = Some W_27760.
Proof. vm_refl. Qed.
Lemma D_27760 : decode_any W_27760 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_27764 : bv 32 := 0x01058593.
Lemma F_27764 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2789c : word) = Some W_27764.
Proof. vm_refl. Qed.
Lemma D_27764 : decode_any W_27764 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27768 : bv 32 := 0x01100793.
Lemma F_27768 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278a0 : word) = Some W_27768.
Proof. vm_refl. Qed.
Lemma D_27768 : decode_any W_27768 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_2776c : bv 32 := 0x0107581b.
Lemma F_2776c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278a4 : word) = Some W_2776c.
Proof. vm_refl. Qed.
Lemma D_2776c : decode_any W_2776c = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27770 : bv 32 := 0xff45a883.
Lemma F_27770 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278a8 : word) = Some W_27770.
Proof. vm_refl. Qed.
Lemma D_27770 : decode_any W_27770 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_27774 : bv 32 := 0xff85a283.
Lemma F_27774 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278ac : word) = Some W_27774.
Proof. vm_refl. Qed.
Lemma D_27774 : decode_any W_27774 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_27778 : bv 32 := 0xffc5a303.
Lemma F_27778 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278b0 : word) = Some W_27778.
Proof. vm_refl. Qed.
Lemma D_27778 : decode_any W_27778 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_2777c : bv 32 := 0x0005a703.
Lemma F_2777c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278b4 : word) = Some W_2777c.
Proof. vm_refl. Qed.
Lemma D_2777c : decode_any W_2777c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27780 : bv 32 := 0x01089393.
Lemma F_27780 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278b8 : word) = Some W_27780.
Proof. vm_refl. Qed.
Lemma D_27780 : decode_any W_27780 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27784 : bv 32 := 0x0108d89b.
Lemma F_27784 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278bc : word) = Some W_27784.
Proof. vm_refl. Qed.
Lemma D_27784 : decode_any W_27784 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27788 : bv 32 := 0x0103e833.
Lemma F_27788 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278c0 : word) = Some W_27788.
Proof. vm_refl. Qed.
Lemma D_27788 : decode_any W_27788 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2778c : bv 32 := 0x01029393.
Lemma F_2778c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278c4 : word) = Some W_2778c.
Proof. vm_refl. Qed.
Lemma D_2778c : decode_any W_2778c = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27790 : bv 32 := 0x0102d29b.
Lemma F_27790 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278c8 : word) = Some W_27790.
Proof. vm_refl. Qed.
Lemma D_27790 : decode_any W_27790 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27794 : bv 32 := 0x0113e8b3.
Lemma F_27794 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278cc : word) = Some W_27794.
Proof. vm_refl. Qed.
Lemma D_27794 : decode_any W_27794 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_27798 : bv 32 := 0x01031393.
Lemma F_27798 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278d0 : word) = Some W_27798.
Proof. vm_refl. Qed.
Lemma D_27798 : decode_any W_27798 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2779c : bv 32 := 0x0103531b.
Lemma F_2779c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278d4 : word) = Some W_2779c.
Proof. vm_refl. Qed.
Lemma D_2779c : decode_any W_2779c = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_277a0 : bv 32 := 0x0053e2b3.
Lemma F_277a0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278d8 : word) = Some W_277a0.
Proof. vm_refl. Qed.
Lemma D_277a0 : decode_any W_277a0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_277a4 : bv 32 := 0x01071393.
Lemma F_277a4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278dc : word) = Some W_277a4.
Proof. vm_refl. Qed.
Lemma D_277a4 : decode_any W_277a4 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_277a8 : bv 32 := 0x0063e333.
Lemma F_277a8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278e0 : word) = Some W_277a8.
Proof. vm_refl. Qed.
Lemma D_277a8 : decode_any W_277a8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_277ac : bv 32 := 0xff060613.
Lemma F_277ac : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278e4 : word) = Some W_277ac.
Proof. vm_refl. Qed.
Lemma D_277ac : decode_any W_277ac = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_277b0 : bv 32 := 0x0106a023.
Lemma F_277b0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278e8 : word) = Some W_277b0.
Proof. vm_refl. Qed.
Lemma D_277b0 : decode_any W_277b0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_277b4 : bv 32 := 0x0116a223.
Lemma F_277b4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278ec : word) = Some W_277b4.
Proof. vm_refl. Qed.
Lemma D_277b4 : decode_any W_277b4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_277b8 : bv 32 := 0x0056a423.
Lemma F_277b8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278f0 : word) = Some W_277b8.
Proof. vm_refl. Qed.
Lemma D_277b8 : decode_any W_277b8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_277bc : bv 32 := 0x0066a623.
Lemma F_277bc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278f4 : word) = Some W_277bc.
Proof. vm_refl. Qed.
Lemma D_277bc : decode_any W_277bc = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_277c0 : bv 32 := 0x01068693.
Lemma F_277c0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278f8 : word) = Some W_277c0.
Proof. vm_refl. Qed.
Lemma D_277c0 : decode_any W_277c0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_277c4 : bv 32 := 0x01058593.
Lemma F_277c4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x278fc : word) = Some W_277c4.
Proof. vm_refl. Qed.
Lemma D_277c4 : decode_any W_277c4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_277c8 : bv 32 := 0xfac7e2e3.
Lemma F_277c8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27900 : word) = Some W_277c8.
Proof. vm_refl. Qed.
Lemma D_277c8 : decode_any W_277c8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_277cc : bv 32 := 0xff258593.
Lemma F_277cc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27904 : word) = Some W_277cc.
Proof. vm_refl. Qed.
Lemma D_277cc : decode_any W_277cc = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_277d0 : bv 32 := 0x01000713.
Lemma F_277d0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27908 : word) = Some W_277d0.
Proof. vm_refl. Qed.
Lemma D_277d0 : decode_any W_277d0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_277d4 : bv 32 := 0xf4e66ae3.
Lemma F_277d4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2790c : word) = Some W_277d4.
Proof. vm_refl. Qed.
Lemma D_277d4 : decode_any W_277d4 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_277d8 : bv 32 := 0x19c0006f.
Lemma F_277d8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27910 : word) = Some W_277d8.
Proof. vm_refl. Qed.
Lemma D_277d8 : decode_any W_277d8 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_277dc : bv 32 := 0x00050693.
Lemma F_277dc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27914 : word) = Some W_277dc.
Proof. vm_refl. Qed.
Lemma D_277dc : decode_any W_277dc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_277e0 : bv 32 := 0x00357793.
Lemma F_277e0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27918 : word) = Some W_277e0.
Proof. vm_refl. Qed.
Lemma D_277e0 : decode_any W_277e0 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_277e4 : bv 32 := 0xf2079ae3.
Lemma F_277e4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2791c : word) = Some W_277e4.
Proof. vm_refl. Qed.
Lemma D_277e4 : decode_any W_277e4 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_277e8 : bv 32 := 0x01000713.
Lemma F_277e8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27920 : word) = Some W_277e8.
Proof. vm_refl. Qed.
Lemma D_277e8 : decode_any W_277e8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_277ec : bv 32 := 0x02e66c63.
Lemma F_277ec : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27924 : word) = Some W_277ec.
Proof. vm_refl. Qed.
Lemma D_277ec : decode_any W_277ec = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_277f0 : bv 32 := 0x00f00713.
Lemma F_277f0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27928 : word) = Some W_277f0.
Proof. vm_refl. Qed.
Lemma D_277f0 : decode_any W_277f0 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_277f4 : bv 32 := 0x0005a783.
Lemma F_277f4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2792c : word) = Some W_277f4.
Proof. vm_refl. Qed.
Lemma D_277f4 : decode_any W_277f4 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_277f8 : bv 32 := 0x0045a803.
Lemma F_277f8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27930 : word) = Some W_277f8.
Proof. vm_refl. Qed.
Lemma D_277f8 : decode_any W_277f8 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_277fc : bv 32 := 0x0085a883.
Lemma F_277fc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27934 : word) = Some W_277fc.
Proof. vm_refl. Qed.
Lemma D_277fc : decode_any W_277fc = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27800 : bv 32 := 0x00c5a283.
Lemma F_27800 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27938 : word) = Some W_27800.
Proof. vm_refl. Qed.
Lemma D_27800 : decode_any W_27800 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_27804 : bv 32 := 0x01058593.
Lemma F_27804 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2793c : word) = Some W_27804.
Proof. vm_refl. Qed.
Lemma D_27804 : decode_any W_27804 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27808 : bv 32 := 0xff060613.
Lemma F_27808 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27940 : word) = Some W_27808.
Proof. vm_refl. Qed.
Lemma D_27808 : decode_any W_27808 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_2780c : bv 32 := 0x00f6a023.
Lemma F_2780c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27944 : word) = Some W_2780c.
Proof. vm_refl. Qed.
Lemma D_2780c : decode_any W_2780c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27810 : bv 32 := 0x0106a223.
Lemma F_27810 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27948 : word) = Some W_27810.
Proof. vm_refl. Qed.
Lemma D_27810 : decode_any W_27810 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27814 : bv 32 := 0x0116a423.
Lemma F_27814 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2794c : word) = Some W_27814.
Proof. vm_refl. Qed.
Lemma D_27814 : decode_any W_27814 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27818 : bv 32 := 0x0056a623.
Lemma F_27818 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27950 : word) = Some W_27818.
Proof. vm_refl. Qed.
Lemma D_27818 : decode_any W_27818 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_2781c : bv 32 := 0x01068693.
Lemma F_2781c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27954 : word) = Some W_2781c.
Proof. vm_refl. Qed.
Lemma D_2781c : decode_any W_2781c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27820 : bv 32 := 0xfcc76ae3.
Lemma F_27820 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27958 : word) = Some W_27820.
Proof. vm_refl. Qed.
Lemma D_27820 : decode_any W_27820 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_27824 : bv 32 := 0x00800713.
Lemma F_27824 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2795c : word) = Some W_27824.
Proof. vm_refl. Qed.
Lemma D_27824 : decode_any W_27824 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27828 : bv 32 := 0x00e66e63.
Lemma F_27828 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27960 : word) = Some W_27828.
Proof. vm_refl. Qed.
Lemma D_27828 : decode_any W_27828 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_2782c : bv 32 := 0x0005a703.
Lemma F_2782c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27964 : word) = Some W_2782c.
Proof. vm_refl. Qed.
Lemma D_2782c : decode_any W_2782c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27830 : bv 32 := 0x0045a783.
Lemma F_27830 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27968 : word) = Some W_27830.
Proof. vm_refl. Qed.
Lemma D_27830 : decode_any W_27830 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27834 : bv 32 := 0x00e6a023.
Lemma F_27834 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2796c : word) = Some W_27834.
Proof. vm_refl. Qed.
Lemma D_27834 : decode_any W_27834 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27838 : bv 32 := 0x00f6a223.
Lemma F_27838 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27970 : word) = Some W_27838.
Proof. vm_refl. Qed.
Lemma D_27838 : decode_any W_27838 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_2783c : bv 32 := 0x00868693.
Lemma F_2783c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27974 : word) = Some W_2783c.
Proof. vm_refl. Qed.
Lemma D_2783c : decode_any W_2783c = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27840 : bv 32 := 0x00858593.
Lemma F_27840 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27978 : word) = Some W_27840.
Proof. vm_refl. Qed.
Lemma D_27840 : decode_any W_27840 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27844 : bv 32 := 0x00467713.
Lemma F_27844 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2797c : word) = Some W_27844.
Proof. vm_refl. Qed.
Lemma D_27844 : decode_any W_27844 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27848 : bv 32 := 0x24070063.
Lemma F_27848 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27980 : word) = Some W_27848.
Proof. vm_refl. Qed.
Lemma D_27848 : decode_any W_27848 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_2784c : bv 32 := 0x0005a703.
Lemma F_2784c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27984 : word) = Some W_2784c.
Proof. vm_refl. Qed.
Lemma D_2784c : decode_any W_2784c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27850 : bv 32 := 0x00458593.
Lemma F_27850 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27988 : word) = Some W_27850.
Proof. vm_refl. Qed.
Lemma D_27850 : decode_any W_27850 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27854 : bv 32 := 0x00e6a023.
Lemma F_27854 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2798c : word) = Some W_27854.
Proof. vm_refl. Qed.
Lemma D_27854 : decode_any W_27854 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27858 : bv 32 := 0x00468693.
Lemma F_27858 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27990 : word) = Some W_27858.
Proof. vm_refl. Qed.
Lemma D_27858 : decode_any W_27858 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_2785c : bv 32 := 0x22c0006f.
Lemma F_2785c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27994 : word) = Some W_2785c.
Proof. vm_refl. Qed.
Lemma D_2785c : decode_any W_2785c = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_27860 : bv 32 := 0x00e68023.
Lemma F_27860 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27998 : word) = Some W_27860.
Proof. vm_refl. Qed.
Lemma D_27860 : decode_any W_27860 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27864 : bv 32 := 0x00168693.
Lemma F_27864 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x2799c : word) = Some W_27864.
Proof. vm_refl. Qed.
Lemma D_27864 : decode_any W_27864 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27868 : bv 32 := 0xfff60613.
Lemma F_27868 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279a0 : word) = Some W_27868.
Proof. vm_refl. Qed.
Lemma D_27868 : decode_any W_27868 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_2786c : bv 32 := 0x01058593.
Lemma F_2786c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279a4 : word) = Some W_2786c.
Proof. vm_refl. Qed.
Lemma D_2786c : decode_any W_2786c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27870 : bv 32 := 0x01200793.
Lemma F_27870 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279a8 : word) = Some W_27870.
Proof. vm_refl. Qed.
Lemma D_27870 : decode_any W_27870 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_27874 : bv 32 := 0x0087581b.
Lemma F_27874 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279ac : word) = Some W_27874.
Proof. vm_refl. Qed.
Lemma D_27874 : decode_any W_27874 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27878 : bv 32 := 0xff45a883.
Lemma F_27878 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279b0 : word) = Some W_27878.
Proof. vm_refl. Qed.
Lemma D_27878 : decode_any W_27878 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_2787c : bv 32 := 0xff85a283.
Lemma F_2787c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279b4 : word) = Some W_2787c.
Proof. vm_refl. Qed.
Lemma D_2787c : decode_any W_2787c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_27880 : bv 32 := 0xffc5a303.
Lemma F_27880 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279b8 : word) = Some W_27880.
Proof. vm_refl. Qed.
Lemma D_27880 : decode_any W_27880 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_27884 : bv 32 := 0x0005a703.
Lemma F_27884 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279bc : word) = Some W_27884.
Proof. vm_refl. Qed.
Lemma D_27884 : decode_any W_27884 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27888 : bv 32 := 0x01889393.
Lemma F_27888 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279c0 : word) = Some W_27888.
Proof. vm_refl. Qed.
Lemma D_27888 : decode_any W_27888 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_2788c : bv 32 := 0x0088d89b.
Lemma F_2788c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279c4 : word) = Some W_2788c.
Proof. vm_refl. Qed.
Lemma D_2788c : decode_any W_2788c = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27890 : bv 32 := 0x0103e833.
Lemma F_27890 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279c8 : word) = Some W_27890.
Proof. vm_refl. Qed.
Lemma D_27890 : decode_any W_27890 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27894 : bv 32 := 0x01829393.
Lemma F_27894 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279cc : word) = Some W_27894.
Proof. vm_refl. Qed.
Lemma D_27894 : decode_any W_27894 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_27898 : bv 32 := 0x0082d29b.
Lemma F_27898 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279d0 : word) = Some W_27898.
Proof. vm_refl. Qed.
Lemma D_27898 : decode_any W_27898 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2789c : bv 32 := 0x0113e8b3.
Lemma F_2789c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279d4 : word) = Some W_2789c.
Proof. vm_refl. Qed.
Lemma D_2789c : decode_any W_2789c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_278a0 : bv 32 := 0x01831393.
Lemma F_278a0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279d8 : word) = Some W_278a0.
Proof. vm_refl. Qed.
Lemma D_278a0 : decode_any W_278a0 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_278a4 : bv 32 := 0x0083531b.
Lemma F_278a4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279dc : word) = Some W_278a4.
Proof. vm_refl. Qed.
Lemma D_278a4 : decode_any W_278a4 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_278a8 : bv 32 := 0x0053e2b3.
Lemma F_278a8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279e0 : word) = Some W_278a8.
Proof. vm_refl. Qed.
Lemma D_278a8 : decode_any W_278a8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_278ac : bv 32 := 0x01871393.
Lemma F_278ac : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279e4 : word) = Some W_278ac.
Proof. vm_refl. Qed.
Lemma D_278ac : decode_any W_278ac = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_278b0 : bv 32 := 0x0063e333.
Lemma F_278b0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279e8 : word) = Some W_278b0.
Proof. vm_refl. Qed.
Lemma D_278b0 : decode_any W_278b0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_278b4 : bv 32 := 0xff060613.
Lemma F_278b4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279ec : word) = Some W_278b4.
Proof. vm_refl. Qed.
Lemma D_278b4 : decode_any W_278b4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_278b8 : bv 32 := 0x0106a023.
Lemma F_278b8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279f0 : word) = Some W_278b8.
Proof. vm_refl. Qed.
Lemma D_278b8 : decode_any W_278b8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_278bc : bv 32 := 0x0116a223.
Lemma F_278bc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279f4 : word) = Some W_278bc.
Proof. vm_refl. Qed.
Lemma D_278bc : decode_any W_278bc = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_278c0 : bv 32 := 0x0056a423.
Lemma F_278c0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279f8 : word) = Some W_278c0.
Proof. vm_refl. Qed.
Lemma D_278c0 : decode_any W_278c0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_278c4 : bv 32 := 0x0066a623.
Lemma F_278c4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x279fc : word) = Some W_278c4.
Proof. vm_refl. Qed.
Lemma D_278c4 : decode_any W_278c4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_278c8 : bv 32 := 0x01068693.
Lemma F_278c8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a00 : word) = Some W_278c8.
Proof. vm_refl. Qed.
Lemma D_278c8 : decode_any W_278c8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_278cc : bv 32 := 0x01058593.
Lemma F_278cc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a04 : word) = Some W_278cc.
Proof. vm_refl. Qed.
Lemma D_278cc : decode_any W_278cc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_278d0 : bv 32 := 0xfac7e2e3.
Lemma F_278d0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a08 : word) = Some W_278d0.
Proof. vm_refl. Qed.
Lemma D_278d0 : decode_any W_278d0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_278d4 : bv 32 := 0xff158593.
Lemma F_278d4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a0c : word) = Some W_278d4.
Proof. vm_refl. Qed.
Lemma D_278d4 : decode_any W_278d4 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_278d8 : bv 32 := 0x01000713.
Lemma F_278d8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a10 : word) = Some W_278d8.
Proof. vm_refl. Qed.
Lemma D_278d8 : decode_any W_278d8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_278dc : bv 32 := 0xe4e666e3.
Lemma F_278dc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a14 : word) = Some W_278dc.
Proof. vm_refl. Qed.
Lemma D_278dc : decode_any W_278dc = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_278e0 : bv 32 := 0x0940006f.
Lemma F_278e0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a18 : word) = Some W_278e0.
Proof. vm_refl. Qed.
Lemma D_278e0 : decode_any W_278e0 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_278e4 : bv 32 := 0x00875793.
Lemma F_278e4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a1c : word) = Some W_278e4.
Proof. vm_refl. Qed.
Lemma D_278e4 : decode_any W_278e4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_278e8 : bv 32 := 0x01075813.
Lemma F_278e8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a20 : word) = Some W_278e8.
Proof. vm_refl. Qed.
Lemma D_278e8 : decode_any W_278e8 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_278ec : bv 32 := 0xffd60613.
Lemma F_278ec : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a24 : word) = Some W_278ec.
Proof. vm_refl. Qed.
Lemma D_278ec : decode_any W_278ec = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_278f0 : bv 32 := 0x00e68023.
Lemma F_278f0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a28 : word) = Some W_278f0.
Proof. vm_refl. Qed.
Lemma D_278f0 : decode_any W_278f0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_278f4 : bv 32 := 0x00f680a3.
Lemma F_278f4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a2c : word) = Some W_278f4.
Proof. vm_refl. Qed.
Lemma D_278f4 : decode_any W_278f4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_278f8 : bv 32 := 0x01068123.
Lemma F_278f8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a30 : word) = Some W_278f8.
Proof. vm_refl. Qed.
Lemma D_278f8 : decode_any W_278f8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_278fc : bv 32 := 0x00368693.
Lemma F_278fc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a34 : word) = Some W_278fc.
Proof. vm_refl. Qed.
Lemma D_278fc : decode_any W_278fc = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_27900 : bv 32 := 0x01058593.
Lemma F_27900 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a38 : word) = Some W_27900.
Proof. vm_refl. Qed.
Lemma D_27900 : decode_any W_27900 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27904 : bv 32 := 0x01000793.
Lemma F_27904 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a3c : word) = Some W_27904.
Proof. vm_refl. Qed.
Lemma D_27904 : decode_any W_27904 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27908 : bv 32 := 0x0187581b.
Lemma F_27908 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a40 : word) = Some W_27908.
Proof. vm_refl. Qed.
Lemma D_27908 : decode_any W_27908 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_2790c : bv 32 := 0xff45a883.
Lemma F_2790c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a44 : word) = Some W_2790c.
Proof. vm_refl. Qed.
Lemma D_2790c : decode_any W_2790c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_27910 : bv 32 := 0xff85a283.
Lemma F_27910 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a48 : word) = Some W_27910.
Proof. vm_refl. Qed.
Lemma D_27910 : decode_any W_27910 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_27914 : bv 32 := 0xffc5a303.
Lemma F_27914 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a4c : word) = Some W_27914.
Proof. vm_refl. Qed.
Lemma D_27914 : decode_any W_27914 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_27918 : bv 32 := 0x0005a703.
Lemma F_27918 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a50 : word) = Some W_27918.
Proof. vm_refl. Qed.
Lemma D_27918 : decode_any W_27918 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2791c : bv 32 := 0x00889393.
Lemma F_2791c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a54 : word) = Some W_2791c.
Proof. vm_refl. Qed.
Lemma D_2791c : decode_any W_2791c = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27920 : bv 32 := 0x0188d89b.
Lemma F_27920 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a58 : word) = Some W_27920.
Proof. vm_refl. Qed.
Lemma D_27920 : decode_any W_27920 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_27924 : bv 32 := 0x0103e833.
Lemma F_27924 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a5c : word) = Some W_27924.
Proof. vm_refl. Qed.
Lemma D_27924 : decode_any W_27924 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27928 : bv 32 := 0x00829393.
Lemma F_27928 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a60 : word) = Some W_27928.
Proof. vm_refl. Qed.
Lemma D_27928 : decode_any W_27928 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2792c : bv 32 := 0x0182d29b.
Lemma F_2792c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a64 : word) = Some W_2792c.
Proof. vm_refl. Qed.
Lemma D_2792c : decode_any W_2792c = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_27930 : bv 32 := 0x0113e8b3.
Lemma F_27930 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a68 : word) = Some W_27930.
Proof. vm_refl. Qed.
Lemma D_27930 : decode_any W_27930 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_27934 : bv 32 := 0x00831393.
Lemma F_27934 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a6c : word) = Some W_27934.
Proof. vm_refl. Qed.
Lemma D_27934 : decode_any W_27934 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27938 : bv 32 := 0x0183531b.
Lemma F_27938 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a70 : word) = Some W_27938.
Proof. vm_refl. Qed.
Lemma D_27938 : decode_any W_27938 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_2793c : bv 32 := 0x0053e2b3.
Lemma F_2793c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a74 : word) = Some W_2793c.
Proof. vm_refl. Qed.
Lemma D_2793c : decode_any W_2793c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_27940 : bv 32 := 0x00871393.
Lemma F_27940 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a78 : word) = Some W_27940.
Proof. vm_refl. Qed.
Lemma D_27940 : decode_any W_27940 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27944 : bv 32 := 0x0063e333.
Lemma F_27944 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a7c : word) = Some W_27944.
Proof. vm_refl. Qed.
Lemma D_27944 : decode_any W_27944 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_27948 : bv 32 := 0xff060613.
Lemma F_27948 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a80 : word) = Some W_27948.
Proof. vm_refl. Qed.
Lemma D_27948 : decode_any W_27948 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_2794c : bv 32 := 0x0106a023.
Lemma F_2794c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a84 : word) = Some W_2794c.
Proof. vm_refl. Qed.
Lemma D_2794c : decode_any W_2794c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27950 : bv 32 := 0x0116a223.
Lemma F_27950 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a88 : word) = Some W_27950.
Proof. vm_refl. Qed.
Lemma D_27950 : decode_any W_27950 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27954 : bv 32 := 0x0056a423.
Lemma F_27954 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a8c : word) = Some W_27954.
Proof. vm_refl. Qed.
Lemma D_27954 : decode_any W_27954 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27958 : bv 32 := 0x0066a623.
Lemma F_27958 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a90 : word) = Some W_27958.
Proof. vm_refl. Qed.
Lemma D_27958 : decode_any W_27958 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_2795c : bv 32 := 0x01068693.
Lemma F_2795c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a94 : word) = Some W_2795c.
Proof. vm_refl. Qed.
Lemma D_2795c : decode_any W_2795c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27960 : bv 32 := 0x01058593.
Lemma F_27960 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a98 : word) = Some W_27960.
Proof. vm_refl. Qed.
Lemma D_27960 : decode_any W_27960 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27964 : bv 32 := 0xfac7e2e3.
Lemma F_27964 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27a9c : word) = Some W_27964.
Proof. vm_refl. Qed.
Lemma D_27964 : decode_any W_27964 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_27968 : bv 32 := 0xff358593.
Lemma F_27968 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27aa0 : word) = Some W_27968.
Proof. vm_refl. Qed.
Lemma D_27968 : decode_any W_27968 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_2796c : bv 32 := 0x01000713.
Lemma F_2796c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27aa4 : word) = Some W_2796c.
Proof. vm_refl. Qed.
Lemma D_2796c : decode_any W_2796c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27970 : bv 32 := 0xdae66ce3.
Lemma F_27970 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27aa8 : word) = Some W_27970.
Proof. vm_refl. Qed.
Lemma D_27970 : decode_any W_27970 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_27974 : bv 32 := 0x0005c703.
Lemma F_27974 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27aac : word) = Some W_27974.
Proof. vm_refl. Qed.
Lemma D_27974 : decode_any W_27974 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27978 : bv 32 := 0x0015c783.
Lemma F_27978 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ab0 : word) = Some W_27978.
Proof. vm_refl. Qed.
Lemma D_27978 : decode_any W_27978 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2797c : bv 32 := 0x0025c803.
Lemma F_2797c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ab4 : word) = Some W_2797c.
Proof. vm_refl. Qed.
Lemma D_2797c : decode_any W_2797c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_27980 : bv 32 := 0x0035c883.
Lemma F_27980 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ab8 : word) = Some W_27980.
Proof. vm_refl. Qed.
Lemma D_27980 : decode_any W_27980 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_27984 : bv 32 := 0x0045c283.
Lemma F_27984 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27abc : word) = Some W_27984.
Proof. vm_refl. Qed.
Lemma D_27984 : decode_any W_27984 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27988 : bv 32 := 0x0055c303.
Lemma F_27988 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ac0 : word) = Some W_27988.
Proof. vm_refl. Qed.
Lemma D_27988 : decode_any W_27988 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_2798c : bv 32 := 0x0065c383.
Lemma F_2798c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ac4 : word) = Some W_2798c.
Proof. vm_refl. Qed.
Lemma D_2798c : decode_any W_2798c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_27990 : bv 32 := 0x0075ce03.
Lemma F_27990 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ac8 : word) = Some W_27990.
Proof. vm_refl. Qed.
Lemma D_27990 : decode_any W_27990 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_27994 : bv 32 := 0x00e68023.
Lemma F_27994 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27acc : word) = Some W_27994.
Proof. vm_refl. Qed.
Lemma D_27994 : decode_any W_27994 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27998 : bv 32 := 0x00f680a3.
Lemma F_27998 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ad0 : word) = Some W_27998.
Proof. vm_refl. Qed.
Lemma D_27998 : decode_any W_27998 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2799c : bv 32 := 0x01068123.
Lemma F_2799c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ad4 : word) = Some W_2799c.
Proof. vm_refl. Qed.
Lemma D_2799c : decode_any W_2799c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_279a0 : bv 32 := 0x011681a3.
Lemma F_279a0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ad8 : word) = Some W_279a0.
Proof. vm_refl. Qed.
Lemma D_279a0 : decode_any W_279a0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_279a4 : bv 32 := 0x0085c703.
Lemma F_279a4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27adc : word) = Some W_279a4.
Proof. vm_refl. Qed.
Lemma D_279a4 : decode_any W_279a4 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_279a8 : bv 32 := 0x0095c783.
Lemma F_279a8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ae0 : word) = Some W_279a8.
Proof. vm_refl. Qed.
Lemma D_279a8 : decode_any W_279a8 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_279ac : bv 32 := 0x00a5c803.
Lemma F_279ac : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ae4 : word) = Some W_279ac.
Proof. vm_refl. Qed.
Lemma D_279ac : decode_any W_279ac = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_279b0 : bv 32 := 0x00b5c883.
Lemma F_279b0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ae8 : word) = Some W_279b0.
Proof. vm_refl. Qed.
Lemma D_279b0 : decode_any W_279b0 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_279b4 : bv 32 := 0x00568223.
Lemma F_279b4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27aec : word) = Some W_279b4.
Proof. vm_refl. Qed.
Lemma D_279b4 : decode_any W_279b4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_279b8 : bv 32 := 0x006682a3.
Lemma F_279b8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27af0 : word) = Some W_279b8.
Proof. vm_refl. Qed.
Lemma D_279b8 : decode_any W_279b8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_279bc : bv 32 := 0x00768323.
Lemma F_279bc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27af4 : word) = Some W_279bc.
Proof. vm_refl. Qed.
Lemma D_279bc : decode_any W_279bc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_279c0 : bv 32 := 0x01c683a3.
Lemma F_279c0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27af8 : word) = Some W_279c0.
Proof. vm_refl. Qed.
Lemma D_279c0 : decode_any W_279c0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_279c4 : bv 32 := 0x00c5c283.
Lemma F_279c4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27afc : word) = Some W_279c4.
Proof. vm_refl. Qed.
Lemma D_279c4 : decode_any W_279c4 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_279c8 : bv 32 := 0x00d5c303.
Lemma F_279c8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b00 : word) = Some W_279c8.
Proof. vm_refl. Qed.
Lemma D_279c8 : decode_any W_279c8 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_279cc : bv 32 := 0x00e5c383.
Lemma F_279cc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b04 : word) = Some W_279cc.
Proof. vm_refl. Qed.
Lemma D_279cc : decode_any W_279cc = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_279d0 : bv 32 := 0x00f5ce03.
Lemma F_279d0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b08 : word) = Some W_279d0.
Proof. vm_refl. Qed.
Lemma D_279d0 : decode_any W_279d0 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_279d4 : bv 32 := 0x01058593.
Lemma F_279d4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b0c : word) = Some W_279d4.
Proof. vm_refl. Qed.
Lemma D_279d4 : decode_any W_279d4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_279d8 : bv 32 := 0x00e68423.
Lemma F_279d8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b10 : word) = Some W_279d8.
Proof. vm_refl. Qed.
Lemma D_279d8 : decode_any W_279d8 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_279dc : bv 32 := 0x00f684a3.
Lemma F_279dc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b14 : word) = Some W_279dc.
Proof. vm_refl. Qed.
Lemma D_279dc : decode_any W_279dc = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_279e0 : bv 32 := 0x01068523.
Lemma F_279e0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b18 : word) = Some W_279e0.
Proof. vm_refl. Qed.
Lemma D_279e0 : decode_any W_279e0 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_279e4 : bv 32 := 0x011685a3.
Lemma F_279e4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b1c : word) = Some W_279e4.
Proof. vm_refl. Qed.
Lemma D_279e4 : decode_any W_279e4 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_279e8 : bv 32 := 0x01068713.
Lemma F_279e8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b20 : word) = Some W_279e8.
Proof. vm_refl. Qed.
Lemma D_279e8 : decode_any W_279e8 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_279ec : bv 32 := 0x00568623.
Lemma F_279ec : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b24 : word) = Some W_279ec.
Proof. vm_refl. Qed.
Lemma D_279ec : decode_any W_279ec = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_279f0 : bv 32 := 0x006686a3.
Lemma F_279f0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b28 : word) = Some W_279f0.
Proof. vm_refl. Qed.
Lemma D_279f0 : decode_any W_279f0 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_279f4 : bv 32 := 0x00768723.
Lemma F_279f4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b2c : word) = Some W_279f4.
Proof. vm_refl. Qed.
Lemma D_279f4 : decode_any W_279f4 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_279f8 : bv 32 := 0x01c687a3.
Lemma F_279f8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b30 : word) = Some W_279f8.
Proof. vm_refl. Qed.
Lemma D_279f8 : decode_any W_279f8 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_279fc : bv 32 := 0x00070693.
Lemma F_279fc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b34 : word) = Some W_279fc.
Proof. vm_refl. Qed.
Lemma D_279fc : decode_any W_279fc = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a00 : bv 32 := 0x00867713.
Lemma F_27a00 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b38 : word) = Some W_27a00.
Proof. vm_refl. Qed.
Lemma D_27a00 : decode_any W_27a00 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a04 : bv 32 := 0xd20706e3.
Lemma F_27a04 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b3c : word) = Some W_27a04.
Proof. vm_refl. Qed.
Lemma D_27a04 : decode_any W_27a04 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a08 : bv 32 := 0x0005c703.
Lemma F_27a08 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b40 : word) = Some W_27a08.
Proof. vm_refl. Qed.
Lemma D_27a08 : decode_any W_27a08 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a0c : bv 32 := 0x0015c783.
Lemma F_27a0c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b44 : word) = Some W_27a0c.
Proof. vm_refl. Qed.
Lemma D_27a0c : decode_any W_27a0c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a10 : bv 32 := 0x0025c803.
Lemma F_27a10 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b48 : word) = Some W_27a10.
Proof. vm_refl. Qed.
Lemma D_27a10 : decode_any W_27a10 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a14 : bv 32 := 0x0035c883.
Lemma F_27a14 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b4c : word) = Some W_27a14.
Proof. vm_refl. Qed.
Lemma D_27a14 : decode_any W_27a14 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a18 : bv 32 := 0x0045c283.
Lemma F_27a18 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b50 : word) = Some W_27a18.
Proof. vm_refl. Qed.
Lemma D_27a18 : decode_any W_27a18 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a1c : bv 32 := 0x0055c303.
Lemma F_27a1c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b54 : word) = Some W_27a1c.
Proof. vm_refl. Qed.
Lemma D_27a1c : decode_any W_27a1c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a20 : bv 32 := 0x0065c383.
Lemma F_27a20 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b58 : word) = Some W_27a20.
Proof. vm_refl. Qed.
Lemma D_27a20 : decode_any W_27a20 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a24 : bv 32 := 0x0075ce03.
Lemma F_27a24 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b5c : word) = Some W_27a24.
Proof. vm_refl. Qed.
Lemma D_27a24 : decode_any W_27a24 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a28 : bv 32 := 0x00858593.
Lemma F_27a28 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b60 : word) = Some W_27a28.
Proof. vm_refl. Qed.
Lemma D_27a28 : decode_any W_27a28 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a2c : bv 32 := 0x00e68023.
Lemma F_27a2c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b64 : word) = Some W_27a2c.
Proof. vm_refl. Qed.
Lemma D_27a2c : decode_any W_27a2c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a30 : bv 32 := 0x00f680a3.
Lemma F_27a30 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b68 : word) = Some W_27a30.
Proof. vm_refl. Qed.
Lemma D_27a30 : decode_any W_27a30 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a34 : bv 32 := 0x01068123.
Lemma F_27a34 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b6c : word) = Some W_27a34.
Proof. vm_refl. Qed.
Lemma D_27a34 : decode_any W_27a34 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a38 : bv 32 := 0x011681a3.
Lemma F_27a38 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b70 : word) = Some W_27a38.
Proof. vm_refl. Qed.
Lemma D_27a38 : decode_any W_27a38 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a3c : bv 32 := 0x00868713.
Lemma F_27a3c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b74 : word) = Some W_27a3c.
Proof. vm_refl. Qed.
Lemma D_27a3c : decode_any W_27a3c = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a40 : bv 32 := 0x00568223.
Lemma F_27a40 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b78 : word) = Some W_27a40.
Proof. vm_refl. Qed.
Lemma D_27a40 : decode_any W_27a40 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a44 : bv 32 := 0x006682a3.
Lemma F_27a44 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b7c : word) = Some W_27a44.
Proof. vm_refl. Qed.
Lemma D_27a44 : decode_any W_27a44 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a48 : bv 32 := 0x00768323.
Lemma F_27a48 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b80 : word) = Some W_27a48.
Proof. vm_refl. Qed.
Lemma D_27a48 : decode_any W_27a48 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a4c : bv 32 := 0x01c683a3.
Lemma F_27a4c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b84 : word) = Some W_27a4c.
Proof. vm_refl. Qed.
Lemma D_27a4c : decode_any W_27a4c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a50 : bv 32 := 0x00070693.
Lemma F_27a50 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b88 : word) = Some W_27a50.
Proof. vm_refl. Qed.
Lemma D_27a50 : decode_any W_27a50 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a54 : bv 32 := 0x00467713.
Lemma F_27a54 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b8c : word) = Some W_27a54.
Proof. vm_refl. Qed.
Lemma D_27a54 : decode_any W_27a54 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a58 : bv 32 := 0x02070863.
Lemma F_27a58 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b90 : word) = Some W_27a58.
Proof. vm_refl. Qed.
Lemma D_27a58 : decode_any W_27a58 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a5c : bv 32 := 0x0005c703.
Lemma F_27a5c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b94 : word) = Some W_27a5c.
Proof. vm_refl. Qed.
Lemma D_27a5c : decode_any W_27a5c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a60 : bv 32 := 0x0015c783.
Lemma F_27a60 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b98 : word) = Some W_27a60.
Proof. vm_refl. Qed.
Lemma D_27a60 : decode_any W_27a60 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a64 : bv 32 := 0x0025c803.
Lemma F_27a64 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27b9c : word) = Some W_27a64.
Proof. vm_refl. Qed.
Lemma D_27a64 : decode_any W_27a64 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a68 : bv 32 := 0x0035c883.
Lemma F_27a68 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ba0 : word) = Some W_27a68.
Proof. vm_refl. Qed.
Lemma D_27a68 : decode_any W_27a68 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a6c : bv 32 := 0x00458593.
Lemma F_27a6c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ba4 : word) = Some W_27a6c.
Proof. vm_refl. Qed.
Lemma D_27a6c : decode_any W_27a6c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a70 : bv 32 := 0x00468293.
Lemma F_27a70 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27ba8 : word) = Some W_27a70.
Proof. vm_refl. Qed.
Lemma D_27a70 : decode_any W_27a70 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a74 : bv 32 := 0x00e68023.
Lemma F_27a74 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bac : word) = Some W_27a74.
Proof. vm_refl. Qed.
Lemma D_27a74 : decode_any W_27a74 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a78 : bv 32 := 0x00f680a3.
Lemma F_27a78 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bb0 : word) = Some W_27a78.
Proof. vm_refl. Qed.
Lemma D_27a78 : decode_any W_27a78 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a7c : bv 32 := 0x01068123.
Lemma F_27a7c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bb4 : word) = Some W_27a7c.
Proof. vm_refl. Qed.
Lemma D_27a7c : decode_any W_27a7c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a80 : bv 32 := 0x011681a3.
Lemma F_27a80 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bb8 : word) = Some W_27a80.
Proof. vm_refl. Qed.
Lemma D_27a80 : decode_any W_27a80 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a84 : bv 32 := 0x00028693.
Lemma F_27a84 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bbc : word) = Some W_27a84.
Proof. vm_refl. Qed.
Lemma D_27a84 : decode_any W_27a84 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a88 : bv 32 := 0x00267713.
Lemma F_27a88 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bc0 : word) = Some W_27a88.
Proof. vm_refl. Qed.
Lemma D_27a88 : decode_any W_27a88 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a8c : bv 32 := 0x00071863.
Lemma F_27a8c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bc4 : word) = Some W_27a8c.
Proof. vm_refl. Qed.
Lemma D_27a8c : decode_any W_27a8c = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a90 : bv 32 := 0x00167613.
Lemma F_27a90 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bc8 : word) = Some W_27a90.
Proof. vm_refl. Qed.
Lemma D_27a90 : decode_any W_27a90 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a94 : bv 32 := 0x02061663.
Lemma F_27a94 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bcc : word) = Some W_27a94.
Proof. vm_refl. Qed.
Lemma D_27a94 : decode_any W_27a94 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a98 : bv 32 := 0x00008067.
Lemma F_27a98 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bd0 : word) = Some W_27a98.
Proof. vm_refl. Qed.
Lemma D_27a98 : decode_any W_27a98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27a9c : bv 32 := 0x0005c703.
Lemma F_27a9c : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bd4 : word) = Some W_27a9c.
Proof. vm_refl. Qed.
Lemma D_27a9c : decode_any W_27a9c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27aa0 : bv 32 := 0x0015c783.
Lemma F_27aa0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bd8 : word) = Some W_27aa0.
Proof. vm_refl. Qed.
Lemma D_27aa0 : decode_any W_27aa0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27aa4 : bv 32 := 0x00258593.
Lemma F_27aa4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bdc : word) = Some W_27aa4.
Proof. vm_refl. Qed.
Lemma D_27aa4 : decode_any W_27aa4 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_27aa8 : bv 32 := 0x00268813.
Lemma F_27aa8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27be0 : word) = Some W_27aa8.
Proof. vm_refl. Qed.
Lemma D_27aa8 : decode_any W_27aa8 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_27aac : bv 32 := 0x00e68023.
Lemma F_27aac : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27be4 : word) = Some W_27aac.
Proof. vm_refl. Qed.
Lemma D_27aac : decode_any W_27aac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27ab0 : bv 32 := 0x00f680a3.
Lemma F_27ab0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27be8 : word) = Some W_27ab0.
Proof. vm_refl. Qed.
Lemma D_27ab0 : decode_any W_27ab0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27ab4 : bv 32 := 0x00080693.
Lemma F_27ab4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bec : word) = Some W_27ab4.
Proof. vm_refl. Qed.
Lemma D_27ab4 : decode_any W_27ab4 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27ab8 : bv 32 := 0x00167613.
Lemma F_27ab8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bf0 : word) = Some W_27ab8.
Proof. vm_refl. Qed.
Lemma D_27ab8 : decode_any W_27ab8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_27abc : bv 32 := 0xfc060ee3.
Lemma F_27abc : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bf4 : word) = Some W_27abc.
Proof. vm_refl. Qed.
Lemma D_27abc : decode_any W_27abc = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_27ac0 : bv 32 := 0x0005c583.
Lemma F_27ac0 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bf8 : word) = Some W_27ac0.
Proof. vm_refl. Qed.
Lemma D_27ac0 : decode_any W_27ac0 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27ac4 : bv 32 := 0x00b68023.
Lemma F_27ac4 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27bfc : word) = Some W_27ac4.
Proof. vm_refl. Qed.
Lemma D_27ac4 : decode_any W_27ac4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_27ac8 : bv 32 := 0x00008067.
Lemma F_27ac8 : fetch_word Src_zlib_example_flush_fuzzer_repro.M.loaded_segments (0x27c00 : word) = Some W_27ac8.
Proof. vm_refl. Qed.
Lemma D_27ac8 : decode_any W_27ac8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

















































































































































