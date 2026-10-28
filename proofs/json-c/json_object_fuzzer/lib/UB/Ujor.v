(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_5d65c : bv 32 := 0x0035f693.
Lemma F_5d65c : fetch_word Ubsan.M.loaded_segments (0x5f438 : word) = Some W_5d65c.
Proof. vm_refl. Qed.
Lemma D_5d65c : decode_any W_5d65c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d660 : bv 32 := 0x10068863.
Lemma F_5d660 : fetch_word Ubsan.M.loaded_segments (0x5f43c : word) = Some W_5d660.
Proof. vm_refl. Qed.
Lemma D_5d660 : decode_any W_5d660 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d664 : bv 32 := 0x02060e63.
Lemma F_5d664 : fetch_word Ubsan.M.loaded_segments (0x5f440 : word) = Some W_5d664.
Proof. vm_refl. Qed.
Lemma D_5d664 : decode_any W_5d664 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d668 : bv 32 := 0x00158713.
Lemma F_5d668 : fetch_word Ubsan.M.loaded_segments (0x5f444 : word) = Some W_5d668.
Proof. vm_refl. Qed.
Lemma D_5d668 : decode_any W_5d668 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d66c : bv 32 := 0x00100793.
Lemma F_5d66c : fetch_word Ubsan.M.loaded_segments (0x5f448 : word) = Some W_5d66c.
Proof. vm_refl. Qed.
Lemma D_5d66c : decode_any W_5d66c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d670 : bv 32 := 0x00050693.
Lemma F_5d670 : fetch_word Ubsan.M.loaded_segments (0x5f44c : word) = Some W_5d670.
Proof. vm_refl. Qed.
Lemma D_5d670 : decode_any W_5d670 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d674 : bv 32 := 0x0005c883.
Lemma F_5d674 : fetch_word Ubsan.M.loaded_segments (0x5f450 : word) = Some W_5d674.
Proof. vm_refl. Qed.
Lemma D_5d674 : decode_any W_5d674 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d678 : bv 32 := 0x00060813.
Lemma F_5d678 : fetch_word Ubsan.M.loaded_segments (0x5f454 : word) = Some W_5d678.
Proof. vm_refl. Qed.
Lemma D_5d678 : decode_any W_5d678 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d67c : bv 32 := 0x00158593.
Lemma F_5d67c : fetch_word Ubsan.M.loaded_segments (0x5f458 : word) = Some W_5d67c.
Proof. vm_refl. Qed.
Lemma D_5d67c : decode_any W_5d67c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d680 : bv 32 := 0x00377293.
Lemma F_5d680 : fetch_word Ubsan.M.loaded_segments (0x5f45c : word) = Some W_5d680.
Proof. vm_refl. Qed.
Lemma D_5d680 : decode_any W_5d680 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d684 : bv 32 := 0x01168023.
Lemma F_5d684 : fetch_word Ubsan.M.loaded_segments (0x5f460 : word) = Some W_5d684.
Proof. vm_refl. Qed.
Lemma D_5d684 : decode_any W_5d684 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d688 : bv 32 := 0x00168693.
Lemma F_5d688 : fetch_word Ubsan.M.loaded_segments (0x5f464 : word) = Some W_5d688.
Proof. vm_refl. Qed.
Lemma D_5d688 : decode_any W_5d688 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d68c : bv 32 := 0xfff60613.
Lemma F_5d68c : fetch_word Ubsan.M.loaded_segments (0x5f468 : word) = Some W_5d68c.
Proof. vm_refl. Qed.
Lemma D_5d68c : decode_any W_5d68c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d690 : bv 32 := 0x00028a63.
Lemma F_5d690 : fetch_word Ubsan.M.loaded_segments (0x5f46c : word) = Some W_5d690.
Proof. vm_refl. Qed.
Lemma D_5d690 : decode_any W_5d690 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d694 : bv 32 := 0x00170713.
Lemma F_5d694 : fetch_word Ubsan.M.loaded_segments (0x5f470 : word) = Some W_5d694.
Proof. vm_refl. Qed.
Lemma D_5d694 : decode_any W_5d694 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d698 : bv 32 := 0xfcf81ee3.
Lemma F_5d698 : fetch_word Ubsan.M.loaded_segments (0x5f474 : word) = Some W_5d698.
Proof. vm_refl. Qed.
Lemma D_5d698 : decode_any W_5d698 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d69c : bv 32 := 0x0080006f.
Lemma F_5d69c : fetch_word Ubsan.M.loaded_segments (0x5f478 : word) = Some W_5d69c.
Proof. vm_refl. Qed.
Lemma D_5d69c : decode_any W_5d69c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6a0 : bv 32 := 0x00050693.
Lemma F_5d6a0 : fetch_word Ubsan.M.loaded_segments (0x5f47c : word) = Some W_5d6a0.
Proof. vm_refl. Qed.
Lemma D_5d6a0 : decode_any W_5d6a0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6a4 : bv 32 := 0x0036f793.
Lemma F_5d6a4 : fetch_word Ubsan.M.loaded_segments (0x5f480 : word) = Some W_5d6a4.
Proof. vm_refl. Qed.
Lemma D_5d6a4 : decode_any W_5d6a4 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6a8 : bv 32 := 0x0c078a63.
Lemma F_5d6a8 : fetch_word Ubsan.M.loaded_segments (0x5f484 : word) = Some W_5d6a8.
Proof. vm_refl. Qed.
Lemma D_5d6a8 : decode_any W_5d6a8 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6ac : bv 32 := 0x02000713.
Lemma F_5d6ac : fetch_word Ubsan.M.loaded_segments (0x5f488 : word) = Some W_5d6ac.
Proof. vm_refl. Qed.
Lemma D_5d6ac : decode_any W_5d6ac = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6b0 : bv 32 := 0x02e67063.
Lemma F_5d6b0 : fetch_word Ubsan.M.loaded_segments (0x5f48c : word) = Some W_5d6b0.
Proof. vm_refl. Qed.
Lemma D_5d6b0 : decode_any W_5d6b0 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6b4 : bv 32 := 0x01000713.
Lemma F_5d6b4 : fetch_word Ubsan.M.loaded_segments (0x5f490 : word) = Some W_5d6b4.
Proof. vm_refl. Qed.
Lemma D_5d6b4 : decode_any W_5d6b4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6b8 : bv 32 := 0x24e67863.
Lemma F_5d6b8 : fetch_word Ubsan.M.loaded_segments (0x5f494 : word) = Some W_5d6b8.
Proof. vm_refl. Qed.
Lemma D_5d6b8 : decode_any W_5d6b8 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6bc : bv 32 := 0x00867713.
Lemma F_5d6bc : fetch_word Ubsan.M.loaded_segments (0x5f498 : word) = Some W_5d6bc.
Proof. vm_refl. Qed.
Lemma D_5d6bc : decode_any W_5d6bc = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6c0 : bv 32 := 0x2c071e63.
Lemma F_5d6c0 : fetch_word Ubsan.M.loaded_segments (0x5f49c : word) = Some W_5d6c0.
Proof. vm_refl. Qed.
Lemma D_5d6c0 : decode_any W_5d6c0 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6c4 : bv 32 := 0x00467713.
Lemma F_5d6c4 : fetch_word Ubsan.M.loaded_segments (0x5f4a0 : word) = Some W_5d6c4.
Proof. vm_refl. Qed.
Lemma D_5d6c4 : decode_any W_5d6c4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6c8 : bv 32 := 0x32071463.
Lemma F_5d6c8 : fetch_word Ubsan.M.loaded_segments (0x5f4a4 : word) = Some W_5d6c8.
Proof. vm_refl. Qed.
Lemma D_5d6c8 : decode_any W_5d6c8 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6cc : bv 32 := 0x3500006f.
Lemma F_5d6cc : fetch_word Ubsan.M.loaded_segments (0x5f4a8 : word) = Some W_5d6cc.
Proof. vm_refl. Qed.
Lemma D_5d6cc : decode_any W_5d6cc = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6d0 : bv 32 := 0x0005a703.
Lemma F_5d6d0 : fetch_word Ubsan.M.loaded_segments (0x5f4ac : word) = Some W_5d6d0.
Proof. vm_refl. Qed.
Lemma D_5d6d0 : decode_any W_5d6d0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6d4 : bv 32 := 0x00300813.
Lemma F_5d6d4 : fetch_word Ubsan.M.loaded_segments (0x5f4b0 : word) = Some W_5d6d4.
Proof. vm_refl. Qed.
Lemma D_5d6d4 : decode_any W_5d6d4 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6d8 : bv 32 := 0x11078e63.
Lemma F_5d6d8 : fetch_word Ubsan.M.loaded_segments (0x5f4b4 : word) = Some W_5d6d8.
Proof. vm_refl. Qed.
Lemma D_5d6d8 : decode_any W_5d6d8 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6dc : bv 32 := 0x00200813.
Lemma F_5d6dc : fetch_word Ubsan.M.loaded_segments (0x5f4b8 : word) = Some W_5d6dc.
Proof. vm_refl. Qed.
Lemma D_5d6dc : decode_any W_5d6dc = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6e0 : bv 32 := 0x19079c63.
Lemma F_5d6e0 : fetch_word Ubsan.M.loaded_segments (0x5f4bc : word) = Some W_5d6e0.
Proof. vm_refl. Qed.
Lemma D_5d6e0 : decode_any W_5d6e0 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6e4 : bv 32 := 0x00875793.
Lemma F_5d6e4 : fetch_word Ubsan.M.loaded_segments (0x5f4c0 : word) = Some W_5d6e4.
Proof. vm_refl. Qed.
Lemma D_5d6e4 : decode_any W_5d6e4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6e8 : bv 32 := 0xffe60613.
Lemma F_5d6e8 : fetch_word Ubsan.M.loaded_segments (0x5f4c4 : word) = Some W_5d6e8.
Proof. vm_refl. Qed.
Lemma D_5d6e8 : decode_any W_5d6e8 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6ec : bv 32 := 0x00e68023.
Lemma F_5d6ec : fetch_word Ubsan.M.loaded_segments (0x5f4c8 : word) = Some W_5d6ec.
Proof. vm_refl. Qed.
Lemma D_5d6ec : decode_any W_5d6ec = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6f0 : bv 32 := 0x00f680a3.
Lemma F_5d6f0 : fetch_word Ubsan.M.loaded_segments (0x5f4cc : word) = Some W_5d6f0.
Proof. vm_refl. Qed.
Lemma D_5d6f0 : decode_any W_5d6f0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6f4 : bv 32 := 0x00268693.
Lemma F_5d6f4 : fetch_word Ubsan.M.loaded_segments (0x5f4d0 : word) = Some W_5d6f4.
Proof. vm_refl. Qed.
Lemma D_5d6f4 : decode_any W_5d6f4 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6f8 : bv 32 := 0x01058593.
Lemma F_5d6f8 : fetch_word Ubsan.M.loaded_segments (0x5f4d4 : word) = Some W_5d6f8.
Proof. vm_refl. Qed.
Lemma D_5d6f8 : decode_any W_5d6f8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6fc : bv 32 := 0x01100793.
Lemma F_5d6fc : fetch_word Ubsan.M.loaded_segments (0x5f4d8 : word) = Some W_5d6fc.
Proof. vm_refl. Qed.
Lemma D_5d6fc : decode_any W_5d6fc = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d700 : bv 32 := 0x0107581b.
Lemma F_5d700 : fetch_word Ubsan.M.loaded_segments (0x5f4dc : word) = Some W_5d700.
Proof. vm_refl. Qed.
Lemma D_5d700 : decode_any W_5d700 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d704 : bv 32 := 0xff45a883.
Lemma F_5d704 : fetch_word Ubsan.M.loaded_segments (0x5f4e0 : word) = Some W_5d704.
Proof. vm_refl. Qed.
Lemma D_5d704 : decode_any W_5d704 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d708 : bv 32 := 0xff85a283.
Lemma F_5d708 : fetch_word Ubsan.M.loaded_segments (0x5f4e4 : word) = Some W_5d708.
Proof. vm_refl. Qed.
Lemma D_5d708 : decode_any W_5d708 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d70c : bv 32 := 0xffc5a303.
Lemma F_5d70c : fetch_word Ubsan.M.loaded_segments (0x5f4e8 : word) = Some W_5d70c.
Proof. vm_refl. Qed.
Lemma D_5d70c : decode_any W_5d70c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d710 : bv 32 := 0x0005a703.
Lemma F_5d710 : fetch_word Ubsan.M.loaded_segments (0x5f4ec : word) = Some W_5d710.
Proof. vm_refl. Qed.
Lemma D_5d710 : decode_any W_5d710 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d714 : bv 32 := 0x01089393.
Lemma F_5d714 : fetch_word Ubsan.M.loaded_segments (0x5f4f0 : word) = Some W_5d714.
Proof. vm_refl. Qed.
Lemma D_5d714 : decode_any W_5d714 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d718 : bv 32 := 0x0108d89b.
Lemma F_5d718 : fetch_word Ubsan.M.loaded_segments (0x5f4f4 : word) = Some W_5d718.
Proof. vm_refl. Qed.
Lemma D_5d718 : decode_any W_5d718 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d71c : bv 32 := 0x0103e833.
Lemma F_5d71c : fetch_word Ubsan.M.loaded_segments (0x5f4f8 : word) = Some W_5d71c.
Proof. vm_refl. Qed.
Lemma D_5d71c : decode_any W_5d71c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d720 : bv 32 := 0x01029393.
Lemma F_5d720 : fetch_word Ubsan.M.loaded_segments (0x5f4fc : word) = Some W_5d720.
Proof. vm_refl. Qed.
Lemma D_5d720 : decode_any W_5d720 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d724 : bv 32 := 0x0102d29b.
Lemma F_5d724 : fetch_word Ubsan.M.loaded_segments (0x5f500 : word) = Some W_5d724.
Proof. vm_refl. Qed.
Lemma D_5d724 : decode_any W_5d724 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d728 : bv 32 := 0x0113e8b3.
Lemma F_5d728 : fetch_word Ubsan.M.loaded_segments (0x5f504 : word) = Some W_5d728.
Proof. vm_refl. Qed.
Lemma D_5d728 : decode_any W_5d728 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d72c : bv 32 := 0x01031393.
Lemma F_5d72c : fetch_word Ubsan.M.loaded_segments (0x5f508 : word) = Some W_5d72c.
Proof. vm_refl. Qed.
Lemma D_5d72c : decode_any W_5d72c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d730 : bv 32 := 0x0103531b.
Lemma F_5d730 : fetch_word Ubsan.M.loaded_segments (0x5f50c : word) = Some W_5d730.
Proof. vm_refl. Qed.
Lemma D_5d730 : decode_any W_5d730 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d734 : bv 32 := 0x0053e2b3.
Lemma F_5d734 : fetch_word Ubsan.M.loaded_segments (0x5f510 : word) = Some W_5d734.
Proof. vm_refl. Qed.
Lemma D_5d734 : decode_any W_5d734 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d738 : bv 32 := 0x01071393.
Lemma F_5d738 : fetch_word Ubsan.M.loaded_segments (0x5f514 : word) = Some W_5d738.
Proof. vm_refl. Qed.
Lemma D_5d738 : decode_any W_5d738 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d73c : bv 32 := 0x0063e333.
Lemma F_5d73c : fetch_word Ubsan.M.loaded_segments (0x5f518 : word) = Some W_5d73c.
Proof. vm_refl. Qed.
Lemma D_5d73c : decode_any W_5d73c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d740 : bv 32 := 0xff060613.
Lemma F_5d740 : fetch_word Ubsan.M.loaded_segments (0x5f51c : word) = Some W_5d740.
Proof. vm_refl. Qed.
Lemma D_5d740 : decode_any W_5d740 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d744 : bv 32 := 0x0106a023.
Lemma F_5d744 : fetch_word Ubsan.M.loaded_segments (0x5f520 : word) = Some W_5d744.
Proof. vm_refl. Qed.
Lemma D_5d744 : decode_any W_5d744 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d748 : bv 32 := 0x0116a223.
Lemma F_5d748 : fetch_word Ubsan.M.loaded_segments (0x5f524 : word) = Some W_5d748.
Proof. vm_refl. Qed.
Lemma D_5d748 : decode_any W_5d748 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d74c : bv 32 := 0x0056a423.
Lemma F_5d74c : fetch_word Ubsan.M.loaded_segments (0x5f528 : word) = Some W_5d74c.
Proof. vm_refl. Qed.
Lemma D_5d74c : decode_any W_5d74c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d750 : bv 32 := 0x0066a623.
Lemma F_5d750 : fetch_word Ubsan.M.loaded_segments (0x5f52c : word) = Some W_5d750.
Proof. vm_refl. Qed.
Lemma D_5d750 : decode_any W_5d750 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d754 : bv 32 := 0x01068693.
Lemma F_5d754 : fetch_word Ubsan.M.loaded_segments (0x5f530 : word) = Some W_5d754.
Proof. vm_refl. Qed.
Lemma D_5d754 : decode_any W_5d754 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d758 : bv 32 := 0x01058593.
Lemma F_5d758 : fetch_word Ubsan.M.loaded_segments (0x5f534 : word) = Some W_5d758.
Proof. vm_refl. Qed.
Lemma D_5d758 : decode_any W_5d758 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d75c : bv 32 := 0xfac7e2e3.
Lemma F_5d75c : fetch_word Ubsan.M.loaded_segments (0x5f538 : word) = Some W_5d75c.
Proof. vm_refl. Qed.
Lemma D_5d75c : decode_any W_5d75c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d760 : bv 32 := 0xff258593.
Lemma F_5d760 : fetch_word Ubsan.M.loaded_segments (0x5f53c : word) = Some W_5d760.
Proof. vm_refl. Qed.
Lemma D_5d760 : decode_any W_5d760 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d764 : bv 32 := 0x01000713.
Lemma F_5d764 : fetch_word Ubsan.M.loaded_segments (0x5f540 : word) = Some W_5d764.
Proof. vm_refl. Qed.
Lemma D_5d764 : decode_any W_5d764 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d768 : bv 32 := 0xf4e66ae3.
Lemma F_5d768 : fetch_word Ubsan.M.loaded_segments (0x5f544 : word) = Some W_5d768.
Proof. vm_refl. Qed.
Lemma D_5d768 : decode_any W_5d768 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d76c : bv 32 := 0x19c0006f.
Lemma F_5d76c : fetch_word Ubsan.M.loaded_segments (0x5f548 : word) = Some W_5d76c.
Proof. vm_refl. Qed.
Lemma D_5d76c : decode_any W_5d76c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d770 : bv 32 := 0x00050693.
Lemma F_5d770 : fetch_word Ubsan.M.loaded_segments (0x5f54c : word) = Some W_5d770.
Proof. vm_refl. Qed.
Lemma D_5d770 : decode_any W_5d770 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d774 : bv 32 := 0x00357793.
Lemma F_5d774 : fetch_word Ubsan.M.loaded_segments (0x5f550 : word) = Some W_5d774.
Proof. vm_refl. Qed.
Lemma D_5d774 : decode_any W_5d774 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d778 : bv 32 := 0xf2079ae3.
Lemma F_5d778 : fetch_word Ubsan.M.loaded_segments (0x5f554 : word) = Some W_5d778.
Proof. vm_refl. Qed.
Lemma D_5d778 : decode_any W_5d778 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d77c : bv 32 := 0x01000713.
Lemma F_5d77c : fetch_word Ubsan.M.loaded_segments (0x5f558 : word) = Some W_5d77c.
Proof. vm_refl. Qed.
Lemma D_5d77c : decode_any W_5d77c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d780 : bv 32 := 0x02e66c63.
Lemma F_5d780 : fetch_word Ubsan.M.loaded_segments (0x5f55c : word) = Some W_5d780.
Proof. vm_refl. Qed.
Lemma D_5d780 : decode_any W_5d780 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d784 : bv 32 := 0x00f00713.
Lemma F_5d784 : fetch_word Ubsan.M.loaded_segments (0x5f560 : word) = Some W_5d784.
Proof. vm_refl. Qed.
Lemma D_5d784 : decode_any W_5d784 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d788 : bv 32 := 0x0005a783.
Lemma F_5d788 : fetch_word Ubsan.M.loaded_segments (0x5f564 : word) = Some W_5d788.
Proof. vm_refl. Qed.
Lemma D_5d788 : decode_any W_5d788 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d78c : bv 32 := 0x0045a803.
Lemma F_5d78c : fetch_word Ubsan.M.loaded_segments (0x5f568 : word) = Some W_5d78c.
Proof. vm_refl. Qed.
Lemma D_5d78c : decode_any W_5d78c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d790 : bv 32 := 0x0085a883.
Lemma F_5d790 : fetch_word Ubsan.M.loaded_segments (0x5f56c : word) = Some W_5d790.
Proof. vm_refl. Qed.
Lemma D_5d790 : decode_any W_5d790 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.
