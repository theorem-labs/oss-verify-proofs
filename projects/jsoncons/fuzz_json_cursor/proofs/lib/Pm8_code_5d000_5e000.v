(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5d658 : bv 32 := 0xfd010113.
Lemma F_5d658 : fetch_word Asan.M.loaded_segments (0x5d6a8 : word) = Some W_5d658.
Proof. vm_refl. Qed.
Lemma D_5d658 : decode_any W_5d658 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d65c : bv 32 := 0x02113423.
Lemma F_5d65c : fetch_word Asan.M.loaded_segments (0x5d6ac : word) = Some W_5d65c.
Proof. vm_refl. Qed.
Lemma D_5d65c : decode_any W_5d65c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d660 : bv 32 := 0x02813023.
Lemma F_5d660 : fetch_word Asan.M.loaded_segments (0x5d6b0 : word) = Some W_5d660.
Proof. vm_refl. Qed.
Lemma D_5d660 : decode_any W_5d660 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d664 : bv 32 := 0x00913c23.
Lemma F_5d664 : fetch_word Asan.M.loaded_segments (0x5d6b4 : word) = Some W_5d664.
Proof. vm_refl. Qed.
Lemma D_5d664 : decode_any W_5d664 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d668 : bv 32 := 0x01213823.
Lemma F_5d668 : fetch_word Asan.M.loaded_segments (0x5d6b8 : word) = Some W_5d668.
Proof. vm_refl. Qed.
Lemma D_5d668 : decode_any W_5d668 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d66c : bv 32 := 0x01313423.
Lemma F_5d66c : fetch_word Asan.M.loaded_segments (0x5d6bc : word) = Some W_5d66c.
Proof. vm_refl. Qed.
Lemma D_5d66c : decode_any W_5d66c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d670 : bv 32 := 0x01413023.
Lemma F_5d670 : fetch_word Asan.M.loaded_segments (0x5d6c0 : word) = Some W_5d670.
Proof. vm_refl. Qed.
Lemma D_5d670 : decode_any W_5d670 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d674 : bv 32 := 0x00058413.
Lemma F_5d674 : fetch_word Asan.M.loaded_segments (0x5d6c4 : word) = Some W_5d674.
Proof. vm_refl. Qed.
Lemma D_5d674 : decode_any W_5d674 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d678 : bv 32 := 0x00058583.
Lemma F_5d678 : fetch_word Asan.M.loaded_segments (0x5d6c8 : word) = Some W_5d678.
Proof. vm_refl. Qed.
Lemma D_5d678 : decode_any W_5d678 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d67c : bv 32 := 0x00300613.
Lemma F_5d67c : fetch_word Asan.M.loaded_segments (0x5d6cc : word) = Some W_5d67c.
Proof. vm_refl. Qed.
Lemma D_5d67c : decode_any W_5d67c = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d680 : bv 32 := 0x12c59463.
Lemma F_5d680 : fetch_word Asan.M.loaded_segments (0x5d6d0 : word) = Some W_5d680.
Proof. vm_refl. Qed.
Lemma D_5d680 : decode_any W_5d680 = Some (Branch BC_NE 11 12 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d684 : bv 32 := 0x00068493.
Lemma F_5d684 : fetch_word Asan.M.loaded_segments (0x5d6d4 : word) = Some W_5d684.
Proof. vm_refl. Qed.
Lemma D_5d684 : decode_any W_5d684 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d688 : bv 32 := 0x00050913.
Lemma F_5d688 : fetch_word Asan.M.loaded_segments (0x5d6d8 : word) = Some W_5d688.
Proof. vm_refl. Qed.
Lemma D_5d688 : decode_any W_5d688 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d68c : bv 32 := 0x3e82d0ef.
Lemma F_5d68c : fetch_word Asan.M.loaded_segments (0x5d6dc : word) = Some W_5d68c.
Proof. vm_refl. Qed.
Lemma D_5d68c : decode_any W_5d68c = Some (Jal 1 185320, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d690 : bv 32 := 0x06050c63.
Lemma F_5d690 : fetch_word Asan.M.loaded_segments (0x5d6e0 : word) = Some W_5d690.
Proof. vm_refl. Qed.
Lemma D_5d690 : decode_any W_5d690 = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d694 : bv 32 := 0x00053683.
Lemma F_5d694 : fetch_word Asan.M.loaded_segments (0x5d6e4 : word) = Some W_5d694.
Proof. vm_refl. Qed.
Lemma D_5d694 : decode_any W_5d694 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d698 : bv 32 := 0x0004b603.
Lemma F_5d698 : fetch_word Asan.M.loaded_segments (0x5d6e8 : word) = Some W_5d698.
Proof. vm_refl. Qed.
Lemma D_5d698 : decode_any W_5d698 = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d69c : bv 32 := 0x0084b583.
Lemma F_5d69c : fetch_word Asan.M.loaded_segments (0x5d6ec : word) = Some W_5d69c.
Proof. vm_refl. Qed.
Lemma D_5d69c : decode_any W_5d69c = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6a0 : bv 32 := 0x0086a983.
Lemma F_5d6a0 : fetch_word Asan.M.loaded_segments (0x5d6f0 : word) = Some W_5d6a0.
Proof. vm_refl. Qed.
Lemma D_5d6a0 : decode_any W_5d6a0 = Some (Load SZ4 true 19 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6a4 : bv 32 := 0x00050a13.
Lemma F_5d6a4 : fetch_word Asan.M.loaded_segments (0x5d6f4 : word) = Some W_5d6a4.
Proof. vm_refl. Qed.
Lemma D_5d6a4 : decode_any W_5d6a4 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6a8 : bv 32 := 0x00060513.
Lemma F_5d6a8 : fetch_word Asan.M.loaded_segments (0x5d6f8 : word) = Some W_5d6a8.
Proof. vm_refl. Qed.
Lemma D_5d6a8 : decode_any W_5d6a8 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6ac : bv 32 := 0x2a9430ef.
Lemma F_5d6ac : fetch_word Asan.M.loaded_segments (0x5d6fc : word) = Some W_5d6ac.
Proof. vm_refl. Qed.
Lemma D_5d6ac : decode_any W_5d6ac = Some (Jal 1 277160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6b0 : bv 32 := 0x02099993.
Lemma F_5d6b0 : fetch_word Asan.M.loaded_segments (0x5d700 : word) = Some W_5d6b0.
Proof. vm_refl. Qed.
Lemma D_5d6b0 : decode_any W_5d6b0 = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6b4 : bv 32 := 0x02051513.
Lemma F_5d6b4 : fetch_word Asan.M.loaded_segments (0x5d704 : word) = Some W_5d6b4.
Proof. vm_refl. Qed.
Lemma D_5d6b4 : decode_any W_5d6b4 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6b8 : bv 32 := 0x02055513.
Lemma F_5d6b8 : fetch_word Asan.M.loaded_segments (0x5d708 : word) = Some W_5d6b8.
Proof. vm_refl. Qed.
Lemma D_5d6b8 : decode_any W_5d6b8 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6bc : bv 32 := 0x00a9e533.
Lemma F_5d6bc : fetch_word Asan.M.loaded_segments (0x5d70c : word) = Some W_5d6bc.
Proof. vm_refl. Qed.
Lemma D_5d6bc : decode_any W_5d6bc = Some (Op ALU_OR 10 19 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6c0 : bv 32 := 0x00a43823.
Lemma F_5d6c0 : fetch_word Asan.M.loaded_segments (0x5d710 : word) = Some W_5d6c0.
Proof. vm_refl. Qed.
Lemma D_5d6c0 : decode_any W_5d6c0 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6c4 : bv 32 := 0x050a0593.
Lemma F_5d6c4 : fetch_word Asan.M.loaded_segments (0x5d714 : word) = Some W_5d6c4.
Proof. vm_refl. Qed.
Lemma D_5d6c4 : decode_any W_5d6c4 = Some (OpImm ALU_ADD 11 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6c8 : bv 32 := 0x00245683.
Lemma F_5d6c8 : fetch_word Asan.M.loaded_segments (0x5d718 : word) = Some W_5d6c8.
Proof. vm_refl. Qed.
Lemma D_5d6c8 : decode_any W_5d6c8 = Some (Load SZ2 false 13 8 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6cc : bv 32 := 0x00446703.
Lemma F_5d6cc : fetch_word Asan.M.loaded_segments (0x5d71c : word) = Some W_5d6cc.
Proof. vm_refl. Qed.
Lemma D_5d6cc : decode_any W_5d6cc = Some (Load SZ4 false 14 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6d0 : bv 32 := 0x0d0a0613.
Lemma F_5d6d0 : fetch_word Asan.M.loaded_segments (0x5d720 : word) = Some W_5d6d0.
Proof. vm_refl. Qed.
Lemma D_5d6d0 : decode_any W_5d6d0 = Some (OpImm ALU_ADD 12 20 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6d4 : bv 32 := 0x2d890513.
Lemma F_5d6d4 : fetch_word Asan.M.loaded_segments (0x5d724 : word) = Some W_5d6d4.
Proof. vm_refl. Qed.
Lemma D_5d6d4 : decode_any W_5d6d4 = Some (OpImm ALU_ADD 10 18 728, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6d8 : bv 32 := 0x02069693.
Lemma F_5d6d8 : fetch_word Asan.M.loaded_segments (0x5d728 : word) = Some W_5d6d8.
Proof. vm_refl. Qed.
Lemma D_5d6d8 : decode_any W_5d6d8 = Some (ShiftImm ALU_SLL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6dc : bv 32 := 0x00e6e7b3.
Lemma F_5d6dc : fetch_word Asan.M.loaded_segments (0x5d72c : word) = Some W_5d6dc.
Proof. vm_refl. Qed.
Lemma D_5d6dc : decode_any W_5d6dc = Some (Op ALU_OR 15 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6e0 : bv 32 := 0x00048693.
Lemma F_5d6e0 : fetch_word Asan.M.loaded_segments (0x5d730 : word) = Some W_5d6e0.
Proof. vm_refl. Qed.
Lemma D_5d6e0 : decode_any W_5d6e0 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6e4 : bv 32 := 0x00040713.
Lemma F_5d6e4 : fetch_word Asan.M.loaded_segments (0x5d734 : word) = Some W_5d6e4.
Proof. vm_refl. Qed.
Lemma D_5d6e4 : decode_any W_5d6e4 = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6e8 : bv 32 := 0x02813083.
Lemma F_5d6e8 : fetch_word Asan.M.loaded_segments (0x5d738 : word) = Some W_5d6e8.
Proof. vm_refl. Qed.
Lemma D_5d6e8 : decode_any W_5d6e8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6ec : bv 32 := 0x02013403.
Lemma F_5d6ec : fetch_word Asan.M.loaded_segments (0x5d73c : word) = Some W_5d6ec.
Proof. vm_refl. Qed.
Lemma D_5d6ec : decode_any W_5d6ec = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6f0 : bv 32 := 0x01813483.
Lemma F_5d6f0 : fetch_word Asan.M.loaded_segments (0x5d740 : word) = Some W_5d6f0.
Proof. vm_refl. Qed.
Lemma D_5d6f0 : decode_any W_5d6f0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6f4 : bv 32 := 0x01013903.
Lemma F_5d6f4 : fetch_word Asan.M.loaded_segments (0x5d744 : word) = Some W_5d6f4.
Proof. vm_refl. Qed.
Lemma D_5d6f4 : decode_any W_5d6f4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6f8 : bv 32 := 0x00813983.
Lemma F_5d6f8 : fetch_word Asan.M.loaded_segments (0x5d748 : word) = Some W_5d6f8.
Proof. vm_refl. Qed.
Lemma D_5d6f8 : decode_any W_5d6f8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6fc : bv 32 := 0x00013a03.
Lemma F_5d6fc : fetch_word Asan.M.loaded_segments (0x5d74c : word) = Some W_5d6fc.
Proof. vm_refl. Qed.
Lemma D_5d6fc : decode_any W_5d6fc = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d700 : bv 32 := 0x03010113.
Lemma F_5d700 : fetch_word Asan.M.loaded_segments (0x5d750 : word) = Some W_5d700.
Proof. vm_refl. Qed.
Lemma D_5d700 : decode_any W_5d700 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d704 : bv 32 := 0x0cc0006f.
Lemma F_5d704 : fetch_word Asan.M.loaded_segments (0x5d754 : word) = Some W_5d704.
Proof. vm_refl. Qed.
Lemma D_5d704 : decode_any W_5d704 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7d0 : bv 32 := 0xfb010113.
Lemma F_5d7d0 : fetch_word Asan.M.loaded_segments (0x5d820 : word) = Some W_5d7d0.
Proof. vm_refl. Qed.
Lemma D_5d7d0 : decode_any W_5d7d0 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7d4 : bv 32 := 0x04113423.
Lemma F_5d7d4 : fetch_word Asan.M.loaded_segments (0x5d824 : word) = Some W_5d7d4.
Proof. vm_refl. Qed.
Lemma D_5d7d4 : decode_any W_5d7d4 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7d8 : bv 32 := 0x04813023.
Lemma F_5d7d8 : fetch_word Asan.M.loaded_segments (0x5d828 : word) = Some W_5d7d8.
Proof. vm_refl. Qed.
Lemma D_5d7d8 : decode_any W_5d7d8 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7dc : bv 32 := 0x02913c23.
Lemma F_5d7dc : fetch_word Asan.M.loaded_segments (0x5d82c : word) = Some W_5d7dc.
Proof. vm_refl. Qed.
Lemma D_5d7dc : decode_any W_5d7dc = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7e0 : bv 32 := 0x03213823.
Lemma F_5d7e0 : fetch_word Asan.M.loaded_segments (0x5d830 : word) = Some W_5d7e0.
Proof. vm_refl. Qed.
Lemma D_5d7e0 : decode_any W_5d7e0 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7e4 : bv 32 := 0x03313423.
Lemma F_5d7e4 : fetch_word Asan.M.loaded_segments (0x5d834 : word) = Some W_5d7e4.
Proof. vm_refl. Qed.
Lemma D_5d7e4 : decode_any W_5d7e4 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7e8 : bv 32 := 0x03413023.
Lemma F_5d7e8 : fetch_word Asan.M.loaded_segments (0x5d838 : word) = Some W_5d7e8.
Proof. vm_refl. Qed.
Lemma D_5d7e8 : decode_any W_5d7e8 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7ec : bv 32 := 0x01513c23.
Lemma F_5d7ec : fetch_word Asan.M.loaded_segments (0x5d83c : word) = Some W_5d7ec.
Proof. vm_refl. Qed.
Lemma D_5d7ec : decode_any W_5d7ec = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7f0 : bv 32 := 0x01613823.
Lemma F_5d7f0 : fetch_word Asan.M.loaded_segments (0x5d840 : word) = Some W_5d7f0.
Proof. vm_refl. Qed.
Lemma D_5d7f0 : decode_any W_5d7f0 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7f4 : bv 32 := 0x00050413.
Lemma F_5d7f4 : fetch_word Asan.M.loaded_segments (0x5d844 : word) = Some W_5d7f4.
Proof. vm_refl. Qed.
Lemma D_5d7f4 : decode_any W_5d7f4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7f8 : bv 32 := 0x00c13023.
Lemma F_5d7f8 : fetch_word Asan.M.loaded_segments (0x5d848 : word) = Some W_5d7f8.
Proof. vm_refl. Qed.
Lemma D_5d7f8 : decode_any W_5d7f8 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7fc : bv 32 := 0x00d13423.
Lemma F_5d7fc : fetch_word Asan.M.loaded_segments (0x5d84c : word) = Some W_5d7fc.
Proof. vm_refl. Qed.
Lemma D_5d7fc : decode_any W_5d7fc = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d800 : bv 32 := 0x05053b03.
Lemma F_5d800 : fetch_word Asan.M.loaded_segments (0x5d850 : word) = Some W_5d800.
Proof. vm_refl. Qed.
Lemma D_5d800 : decode_any W_5d800 = Some (Load SZ8 true 22 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d804 : bv 32 := 0x00058493.
Lemma F_5d804 : fetch_word Asan.M.loaded_segments (0x5d854 : word) = Some W_5d804.
Proof. vm_refl. Qed.
Lemma D_5d804 : decode_any W_5d804 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d808 : bv 32 := 0x000b0663.
Lemma F_5d808 : fetch_word Asan.M.loaded_segments (0x5d858 : word) = Some W_5d808.
Proof. vm_refl. Qed.
Lemma D_5d808 : decode_any W_5d808 = Some (Branch BC_EQ 22 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d80c : bv 32 := 0x04043503.
Lemma F_5d80c : fetch_word Asan.M.loaded_segments (0x5d85c : word) = Some W_5d80c.
Proof. vm_refl. Qed.
Lemma D_5d80c : decode_any W_5d80c = Some (Load SZ8 true 10 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d810 : bv 32 := 0x0cf57263.
Lemma F_5d810 : fetch_word Asan.M.loaded_segments (0x5d860 : word) = Some W_5d810.
Proof. vm_refl. Qed.
Lemma D_5d810 : decode_any W_5d810 = Some (Branch BC_GEU 10 15 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d898 : bv 32 := 0x00013603.
Lemma F_5d898 : fetch_word Asan.M.loaded_segments (0x5d8e8 : word) = Some W_5d898.
Proof. vm_refl. Qed.
Lemma D_5d898 : decode_any W_5d898 = Some (Load SZ8 true 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d89c : bv 32 := 0x00813683.
Lemma F_5d89c : fetch_word Asan.M.loaded_segments (0x5d8ec : word) = Some W_5d89c.
Proof. vm_refl. Qed.
Lemma D_5d89c : decode_any W_5d89c = Some (Load SZ8 true 13 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8a0 : bv 32 := 0x00040513.
Lemma F_5d8a0 : fetch_word Asan.M.loaded_segments (0x5d8f0 : word) = Some W_5d8a0.
Proof. vm_refl. Qed.
Lemma D_5d8a0 : decode_any W_5d8a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8a4 : bv 32 := 0x00048593.
Lemma F_5d8a4 : fetch_word Asan.M.loaded_segments (0x5d8f4 : word) = Some W_5d8a4.
Proof. vm_refl. Qed.
Lemma D_5d8a4 : decode_any W_5d8a4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8a8 : bv 32 := 0x831fd0ef.
Lemma F_5d8a8 : fetch_word Asan.M.loaded_segments (0x5d8f8 : word) = Some W_5d8a8.
Proof. vm_refl. Qed.
Lemma D_5d8a8 : decode_any W_5d8a8 = Some (Jal 1 2086960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8ac : bv 32 := 0x04813083.
Lemma F_5d8ac : fetch_word Asan.M.loaded_segments (0x5d8fc : word) = Some W_5d8ac.
Proof. vm_refl. Qed.
Lemma D_5d8ac : decode_any W_5d8ac = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8b0 : bv 32 := 0x04013403.
Lemma F_5d8b0 : fetch_word Asan.M.loaded_segments (0x5d900 : word) = Some W_5d8b0.
Proof. vm_refl. Qed.
Lemma D_5d8b0 : decode_any W_5d8b0 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8b4 : bv 32 := 0x03813483.
Lemma F_5d8b4 : fetch_word Asan.M.loaded_segments (0x5d904 : word) = Some W_5d8b4.
Proof. vm_refl. Qed.
Lemma D_5d8b4 : decode_any W_5d8b4 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8b8 : bv 32 := 0x03013903.
Lemma F_5d8b8 : fetch_word Asan.M.loaded_segments (0x5d908 : word) = Some W_5d8b8.
Proof. vm_refl. Qed.
Lemma D_5d8b8 : decode_any W_5d8b8 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8bc : bv 32 := 0x02813983.
Lemma F_5d8bc : fetch_word Asan.M.loaded_segments (0x5d90c : word) = Some W_5d8bc.
Proof. vm_refl. Qed.
Lemma D_5d8bc : decode_any W_5d8bc = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8c0 : bv 32 := 0x02013a03.
Lemma F_5d8c0 : fetch_word Asan.M.loaded_segments (0x5d910 : word) = Some W_5d8c0.
Proof. vm_refl. Qed.
Lemma D_5d8c0 : decode_any W_5d8c0 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8c4 : bv 32 := 0x01813a83.
Lemma F_5d8c4 : fetch_word Asan.M.loaded_segments (0x5d914 : word) = Some W_5d8c4.
Proof. vm_refl. Qed.
Lemma D_5d8c4 : decode_any W_5d8c4 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8c8 : bv 32 := 0x01013b03.
Lemma F_5d8c8 : fetch_word Asan.M.loaded_segments (0x5d918 : word) = Some W_5d8c8.
Proof. vm_refl. Qed.
Lemma D_5d8c8 : decode_any W_5d8c8 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8cc : bv 32 := 0x05010113.
Lemma F_5d8cc : fetch_word Asan.M.loaded_segments (0x5d91c : word) = Some W_5d8cc.
Proof. vm_refl. Qed.
Lemma D_5d8cc : decode_any W_5d8cc = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8d0 : bv 32 := 0x00008067.
Lemma F_5d8d0 : fetch_word Asan.M.loaded_segments (0x5d920 : word) = Some W_5d8d0.
Proof. vm_refl. Qed.
Lemma D_5d8d0 : decode_any W_5d8d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8d4 : bv 32 := 0x00060a13.
Lemma F_5d8d4 : fetch_word Asan.M.loaded_segments (0x5d924 : word) = Some W_5d8d4.
Proof. vm_refl. Qed.
Lemma D_5d8d4 : decode_any W_5d8d4 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8d8 : bv 32 := 0x00068993.
Lemma F_5d8d8 : fetch_word Asan.M.loaded_segments (0x5d928 : word) = Some W_5d8d8.
Proof. vm_refl. Qed.
Lemma D_5d8d8 : decode_any W_5d8d8 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8dc : bv 32 := 0x00078913.
Lemma F_5d8dc : fetch_word Asan.M.loaded_segments (0x5d92c : word) = Some W_5d8dc.
Proof. vm_refl. Qed.
Lemma D_5d8dc : decode_any W_5d8dc = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8e0 : bv 32 := 0x000f6517.
Lemma F_5d8e0 : fetch_word Asan.M.loaded_segments (0x5d930 : word) = Some W_5d8e0.
Proof. vm_refl. Qed.
Lemma D_5d8e0 : decode_any W_5d8e0 = Some (Auipc 10 246, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8e4 : bv 32 := 0x80053583.
Lemma F_5d8e4 : fetch_word Asan.M.loaded_segments (0x5d934 : word) = Some W_5d8e4.
Proof. vm_refl. Qed.
Lemma D_5d8e4 : decode_any W_5d8e4 = Some (Load SZ8 true 11 10 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8e8 : bv 32 := 0x0305a683.
Lemma F_5d8e8 : fetch_word Asan.M.loaded_segments (0x5d938 : word) = Some W_5d8e8.
Proof. vm_refl. Qed.
Lemma D_5d8e8 : decode_any W_5d8e8 = Some (Load SZ4 true 13 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8ec : bv 32 := 0x04d05463.
Lemma F_5d8ec : fetch_word Asan.M.loaded_segments (0x5d93c : word) = Some W_5d8ec.
Proof. vm_refl. Qed.
Lemma D_5d8ec : decode_any W_5d8ec = Some (Branch BC_GE 0 13 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d934 : bv 32 := 0x00275583.
Lemma F_5d934 : fetch_word Asan.M.loaded_segments (0x5d984 : word) = Some W_5d934.
Proof. vm_refl. Qed.
Lemma D_5d934 : decode_any W_5d934 = Some (Load SZ2 false 11 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d938 : bv 32 := 0x00476603.
Lemma F_5d938 : fetch_word Asan.M.loaded_segments (0x5d988 : word) = Some W_5d938.
Proof. vm_refl. Qed.
Lemma D_5d938 : decode_any W_5d938 = Some (Load SZ4 false 12 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d93c : bv 32 := 0x01070513.
Lemma F_5d93c : fetch_word Asan.M.loaded_segments (0x5d98c : word) = Some W_5d93c.
Proof. vm_refl. Qed.
Lemma D_5d93c : decode_any W_5d93c = Some (OpImm ALU_ADD 10 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d940 : bv 32 := 0x02059593.
Lemma F_5d940 : fetch_word Asan.M.loaded_segments (0x5d990 : word) = Some W_5d940.
Proof. vm_refl. Qed.
Lemma D_5d940 : decode_any W_5d940 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d944 : bv 32 := 0x00c5e5b3.
Lemma F_5d944 : fetch_word Asan.M.loaded_segments (0x5d994 : word) = Some W_5d944.
Proof. vm_refl. Qed.
Lemma D_5d944 : decode_any W_5d944 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d948 : bv 32 := 0x00758593.
Lemma F_5d948 : fetch_word Asan.M.loaded_segments (0x5d998 : word) = Some W_5d948.
Proof. vm_refl. Qed.
Lemma D_5d948 : decode_any W_5d948 = Some (OpImm ALU_ADD 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d94c : bv 32 := 0xff85f593.
Lemma F_5d94c : fetch_word Asan.M.loaded_segments (0x5d99c : word) = Some W_5d94c.
Proof. vm_refl. Qed.
Lemma D_5d94c : decode_any W_5d94c = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d950 : bv 32 := 0x0fd00613.
Lemma F_5d950 : fetch_word Asan.M.loaded_segments (0x5d9a0 : word) = Some W_5d950.
Proof. vm_refl. Qed.
Lemma D_5d950 : decode_any W_5d950 = Some (OpImm ALU_ADD 12 0 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d954 : bv 32 := 0x00070a93.
Lemma F_5d954 : fetch_word Asan.M.loaded_segments (0x5d9a4 : word) = Some W_5d954.
Proof. vm_refl. Qed.
Lemma D_5d954 : decode_any W_5d954 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d958 : bv 32 := 0x370240ef.
Lemma F_5d958 : fetch_word Asan.M.loaded_segments (0x5d9a8 : word) = Some W_5d958.
Proof. vm_refl. Qed.
Lemma D_5d958 : decode_any W_5d958 = Some (Jal 1 148336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d95c : bv 32 := 0x00048513.
Lemma F_5d95c : fetch_word Asan.M.loaded_segments (0x5d9ac : word) = Some W_5d95c.
Proof. vm_refl. Qed.
Lemma D_5d95c : decode_any W_5d95c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d960 : bv 32 := 0x000a0593.
Lemma F_5d960 : fetch_word Asan.M.loaded_segments (0x5d9b0 : word) = Some W_5d960.
Proof. vm_refl. Qed.
Lemma D_5d960 : decode_any W_5d960 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d964 : bv 32 := 0x00098613.
Lemma F_5d964 : fetch_word Asan.M.loaded_segments (0x5d9b4 : word) = Some W_5d964.
Proof. vm_refl. Qed.
Lemma D_5d964 : decode_any W_5d964 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d968 : bv 32 := 0x000a8693.
Lemma F_5d968 : fetch_word Asan.M.loaded_segments (0x5d9b8 : word) = Some W_5d968.
Proof. vm_refl. Qed.
Lemma D_5d968 : decode_any W_5d968 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d96c : bv 32 := 0x00090713.
Lemma F_5d96c : fetch_word Asan.M.loaded_segments (0x5d9bc : word) = Some W_5d96c.
Proof. vm_refl. Qed.
Lemma D_5d96c : decode_any W_5d96c = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d970 : bv 32 := 0x010000ef.
Lemma F_5d970 : fetch_word Asan.M.loaded_segments (0x5d9c0 : word) = Some W_5d970.
Proof. vm_refl. Qed.
Lemma D_5d970 : decode_any W_5d970 = Some (Jal 1 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d974 : bv 32 := 0x0184b503.
Lemma F_5d974 : fetch_word Asan.M.loaded_segments (0x5d9c4 : word) = Some W_5d974.
Proof. vm_refl. Qed.
Lemma D_5d974 : decode_any W_5d974 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d978 : bv 32 := 0xf2ab60e3.
Lemma F_5d978 : fetch_word Asan.M.loaded_segments (0x5d9c8 : word) = Some W_5d978.
Proof. vm_refl. Qed.
Lemma D_5d978 : decode_any W_5d978 = Some (Branch BC_LTU 22 10 7968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d97c : bv 32 := 0xf31ff06f.
Lemma F_5d97c : fetch_word Asan.M.loaded_segments (0x5d9cc : word) = Some W_5d97c.
Proof. vm_refl. Qed.
Lemma D_5d97c : decode_any W_5d97c = Some (Jal 0 2096944, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d980 : bv 32 := 0xfc010113.
Lemma F_5d980 : fetch_word Asan.M.loaded_segments (0x5d9d0 : word) = Some W_5d980.
Proof. vm_refl. Qed.
Lemma D_5d980 : decode_any W_5d980 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d984 : bv 32 := 0x02113c23.
Lemma F_5d984 : fetch_word Asan.M.loaded_segments (0x5d9d4 : word) = Some W_5d984.
Proof. vm_refl. Qed.
Lemma D_5d984 : decode_any W_5d984 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d988 : bv 32 := 0x02813823.
Lemma F_5d988 : fetch_word Asan.M.loaded_segments (0x5d9d8 : word) = Some W_5d988.
Proof. vm_refl. Qed.
Lemma D_5d988 : decode_any W_5d988 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d98c : bv 32 := 0x02913423.
Lemma F_5d98c : fetch_word Asan.M.loaded_segments (0x5d9dc : word) = Some W_5d98c.
Proof. vm_refl. Qed.
Lemma D_5d98c : decode_any W_5d98c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d990 : bv 32 := 0x03213023.
Lemma F_5d990 : fetch_word Asan.M.loaded_segments (0x5d9e0 : word) = Some W_5d990.
Proof. vm_refl. Qed.
Lemma D_5d990 : decode_any W_5d990 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d994 : bv 32 := 0x01313c23.
Lemma F_5d994 : fetch_word Asan.M.loaded_segments (0x5d9e4 : word) = Some W_5d994.
Proof. vm_refl. Qed.
Lemma D_5d994 : decode_any W_5d994 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d998 : bv 32 := 0x01413823.
Lemma F_5d998 : fetch_word Asan.M.loaded_segments (0x5d9e8 : word) = Some W_5d998.
Proof. vm_refl. Qed.
Lemma D_5d998 : decode_any W_5d998 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d99c : bv 32 := 0x01513423.
Lemma F_5d99c : fetch_word Asan.M.loaded_segments (0x5d9ec : word) = Some W_5d99c.
Proof. vm_refl. Qed.
Lemma D_5d99c : decode_any W_5d99c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9a0 : bv 32 := 0x00053783.
Lemma F_5d9a0 : fetch_word Asan.M.loaded_segments (0x5d9f0 : word) = Some W_5d9a0.
Proof. vm_refl. Qed.
Lemma D_5d9a0 : decode_any W_5d9a0 = Some (Load SZ8 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9a4 : bv 32 := 0x00078a63.
Lemma F_5d9a4 : fetch_word Asan.M.loaded_segments (0x5d9f4 : word) = Some W_5d9a4.
Proof. vm_refl. Qed.
Lemma D_5d9a4 : decode_any W_5d9a4 = Some (Branch BC_EQ 15 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9a8 : bv 32 := 0x01053803.
Lemma F_5d9a8 : fetch_word Asan.M.loaded_segments (0x5d9f8 : word) = Some W_5d9a8.
Proof. vm_refl. Qed.
Lemma D_5d9a8 : decode_any W_5d9a8 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9ac : bv 32 := 0x01083783.
Lemma F_5d9ac : fetch_word Asan.M.loaded_segments (0x5d9fc : word) = Some W_5d9ac.
Proof. vm_refl. Qed.
Lemma D_5d9ac : decode_any W_5d9ac = Some (Load SZ8 true 15 16 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9b0 : bv 32 := 0x3fd00893.
Lemma F_5d9b0 : fetch_word Asan.M.loaded_segments (0x5da00 : word) = Some W_5d9b0.
Proof. vm_refl. Qed.
Lemma D_5d9b0 : decode_any W_5d9b0 = Some (OpImm ALU_ADD 17 0 1021, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9b4 : bv 32 := 0x09179463.
Lemma F_5d9b4 : fetch_word Asan.M.loaded_segments (0x5da04 : word) = Some W_5d9b4.
Proof. vm_refl. Qed.
Lemma D_5d9b4 : decode_any W_5d9b4 = Some (Branch BC_NE 15 17 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9b8 : bv 32 := 0x7805a783.
Lemma F_5d9b8 : fetch_word Asan.M.loaded_segments (0x5da08 : word) = Some W_5d9b8.
Proof. vm_refl. Qed.
Lemma D_5d9b8 : decode_any W_5d9b8 = Some (Load SZ4 true 15 11 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9bc : bv 32 := 0x0e078263.
Lemma F_5d9bc : fetch_word Asan.M.loaded_segments (0x5da0c : word) = Some W_5d9bc.
Proof. vm_refl. Qed.
Lemma D_5d9bc : decode_any W_5d9bc = Some (Branch BC_EQ 15 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9c0 : bv 32 := 0xfff78793.
Lemma F_5d9c0 : fetch_word Asan.M.loaded_segments (0x5da10 : word) = Some W_5d9c0.
Proof. vm_refl. Qed.
Lemma D_5d9c0 : decode_any W_5d9c0 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9c4 : bv 32 := 0x02079813.
Lemma F_5d9c4 : fetch_word Asan.M.loaded_segments (0x5da14 : word) = Some W_5d9c4.
Proof. vm_refl. Qed.
Lemma D_5d9c4 : decode_any W_5d9c4 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9c8 : bv 32 := 0x78f5a023.
Lemma F_5d9c8 : fetch_word Asan.M.loaded_segments (0x5da18 : word) = Some W_5d9c8.
Proof. vm_refl. Qed.
Lemma D_5d9c8 : decode_any W_5d9c8 = Some (Store SZ4 11 15 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9cc : bv 32 := 0x01e85793.
Lemma F_5d9cc : fetch_word Asan.M.loaded_segments (0x5da1c : word) = Some W_5d9cc.
Proof. vm_refl. Qed.
Lemma D_5d9cc : decode_any W_5d9cc = Some (ShiftImm ALU_SRL 15 16 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9d0 : bv 32 := 0x00f587b3.
Lemma F_5d9d0 : fetch_word Asan.M.loaded_segments (0x5da20 : word) = Some W_5d9d0.
Proof. vm_refl. Qed.
Lemma D_5d9d0 : decode_any W_5d9d0 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9d4 : bv 32 := 0x7885b803.
Lemma F_5d9d4 : fetch_word Asan.M.loaded_segments (0x5da24 : word) = Some W_5d9d4.
Proof. vm_refl. Qed.
Lemma D_5d9d4 : decode_any W_5d9d4 = Some (Load SZ8 true 16 11 1928, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9d8 : bv 32 := 0x7ff58593.
Lemma F_5d9d8 : fetch_word Asan.M.loaded_segments (0x5da28 : word) = Some W_5d9d8.
Proof. vm_refl. Qed.
Lemma D_5d9d8 : decode_any W_5d9d8 = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9dc : bv 32 := 0x21158593.
Lemma F_5d9dc : fetch_word Asan.M.loaded_segments (0x5da2c : word) = Some W_5d9dc.
Proof. vm_refl. Qed.
Lemma D_5d9dc : decode_any W_5d9dc = Some (OpImm ALU_ADD 11 11 529, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9e0 : bv 32 := 0x7907e783.
Lemma F_5d9e0 : fetch_word Asan.M.loaded_segments (0x5da30 : word) = Some W_5d9e0.
Proof. vm_refl. Qed.
Lemma D_5d9e0 : decode_any W_5d9e0 = Some (Load SZ4 false 15 15 1936, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9e4 : bv 32 := 0x0105b02f.
Lemma F_5d9e4 : fetch_word Asan.M.loaded_segments (0x5da34 : word) = Some W_5d9e4.
Proof. vm_refl. Qed.
Lemma D_5d9e4 : decode_any W_5d9e4 = Some (Amo AMO_ADD AD false false 0 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9e8 : bv 32 := 0x000fc597.
Lemma F_5d9e8 : fetch_word Asan.M.loaded_segments (0x5da38 : word) = Some W_5d9e8.
Proof. vm_refl. Qed.
Lemma D_5d9e8 : decode_any W_5d9e8 = Some (Auipc 11 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9ec : bv 32 := 0x9405b583.
Lemma F_5d9ec : fetch_word Asan.M.loaded_segments (0x5da3c : word) = Some W_5d9ec.
Proof. vm_refl. Qed.
Lemma D_5d9ec : decode_any W_5d9ec = Some (Load SZ8 true 11 11 2368, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9f0 : bv 32 := 0x00300813.
Lemma F_5d9f0 : fetch_word Asan.M.loaded_segments (0x5da40 : word) = Some W_5d9f0.
Proof. vm_refl. Qed.
Lemma D_5d9f0 : decode_any W_5d9f0 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9f4 : bv 32 := 0x00479793.
Lemma F_5d9f4 : fetch_word Asan.M.loaded_segments (0x5da44 : word) = Some W_5d9f4.
Proof. vm_refl. Qed.
Lemma D_5d9f4 : decode_any W_5d9f4 = Some (ShiftImm ALU_SLL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9f8 : bv 32 := 0x02381813.
Lemma F_5d9f8 : fetch_word Asan.M.loaded_segments (0x5da48 : word) = Some W_5d9f8.
Proof. vm_refl. Qed.
Lemma D_5d9f8 : decode_any W_5d9f8 = Some (ShiftImm ALU_SLL 16 16 35, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9fc : bv 32 := 0x010585b3.
Lemma F_5d9fc : fetch_word Asan.M.loaded_segments (0x5da4c : word) = Some W_5d9fc.
Proof. vm_refl. Qed.
Lemma D_5d9fc : decode_any W_5d9fc = Some (Op ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da00 : bv 32 := 0x00b785b3.
Lemma F_5da00 : fetch_word Asan.M.loaded_segments (0x5da50 : word) = Some W_5da00.
Proof. vm_refl. Qed.
Lemma D_5da00 : decode_any W_5da00 = Some (Op ALU_ADD 11 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da04 : bv 32 := 0x0e058863.
Lemma F_5da04 : fetch_word Asan.M.loaded_segments (0x5da54 : word) = Some W_5da04.
Proof. vm_refl. Qed.
Lemma D_5da04 : decode_any W_5da04 = Some (Branch BC_EQ 11 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da08 : bv 32 := 0x00100613.
Lemma F_5da08 : fetch_word Asan.M.loaded_segments (0x5da58 : word) = Some W_5da08.
Proof. vm_refl. Qed.
Lemma D_5da08 : decode_any W_5da08 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da0c : bv 32 := 0x000027b7.
Lemma F_5da0c : fetch_word Asan.M.loaded_segments (0x5da5c : word) = Some W_5da0c.
Proof. vm_refl. Qed.
Lemma D_5da0c : decode_any W_5da0c = Some (Lui 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da10 : bv 32 := 0x00f70733.
Lemma F_5da10 : fetch_word Asan.M.loaded_segments (0x5da60 : word) = Some W_5da10.
Proof. vm_refl. Qed.
Lemma D_5da10 : decode_any W_5da10 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da14 : bv 32 := 0x00053783.
Lemma F_5da14 : fetch_word Asan.M.loaded_segments (0x5da64 : word) = Some W_5da14.
Proof. vm_refl. Qed.
Lemma D_5da14 : decode_any W_5da14 = Some (Load SZ8 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da18 : bv 32 := 0x0005b023.
Lemma F_5da18 : fetch_word Asan.M.loaded_segments (0x5da68 : word) = Some W_5da18.
Proof. vm_refl. Qed.
Lemma D_5da18 : decode_any W_5da18 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da1c : bv 32 := 0x00e5b423.
Lemma F_5da1c : fetch_word Asan.M.loaded_segments (0x5da6c : word) = Some W_5da1c.
Proof. vm_refl. Qed.
Lemma D_5da1c : decode_any W_5da1c = Some (Store SZ8 11 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da20 : bv 32 := 0x00c5b823.
Lemma F_5da20 : fetch_word Asan.M.loaded_segments (0x5da70 : word) = Some W_5da20.
Proof. vm_refl. Qed.
Lemma D_5da20 : decode_any W_5da20 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da24 : bv 32 := 0x00d5bc23.
Lemma F_5da24 : fetch_word Asan.M.loaded_segments (0x5da74 : word) = Some W_5da24.
Proof. vm_refl. Qed.
Lemma D_5da24 : decode_any W_5da24 = Some (Store SZ8 11 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da28 : bv 32 := 0x02078e63.
Lemma F_5da28 : fetch_word Asan.M.loaded_segments (0x5da78 : word) = Some W_5da28.
Proof. vm_refl. Qed.
Lemma D_5da28 : decode_any W_5da28 = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da2c : bv 32 := 0x01053603.
Lemma F_5da2c : fetch_word Asan.M.loaded_segments (0x5da7c : word) = Some W_5da2c.
Proof. vm_refl. Qed.
Lemma D_5da2c : decode_any W_5da2c = Some (Load SZ8 true 12 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da30 : bv 32 := 0x00b63023.
Lemma F_5da30 : fetch_word Asan.M.loaded_segments (0x5da80 : word) = Some W_5da30.
Proof. vm_refl. Qed.
Lemma D_5da30 : decode_any W_5da30 = Some (Store SZ8 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da34 : bv 32 := 0x00178613.
Lemma F_5da34 : fetch_word Asan.M.loaded_segments (0x5da84 : word) = Some W_5da34.
Proof. vm_refl. Qed.
Lemma D_5da34 : decode_any W_5da34 = Some (OpImm ALU_ADD 12 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da38 : bv 32 := 0x0300006f.
Lemma F_5da38 : fetch_word Asan.M.loaded_segments (0x5da88 : word) = Some W_5da38.
Proof. vm_refl. Qed.
Lemma D_5da38 : decode_any W_5da38 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da3c : bv 32 := 0x0d17fc63.
Lemma F_5da3c : fetch_word Asan.M.loaded_segments (0x5da8c : word) = Some W_5da3c.
Proof. vm_refl. Qed.
Lemma D_5da3c : decode_any W_5da3c = Some (Branch BC_GEU 15 17 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da40 : bv 32 := 0x00883583.
Lemma F_5da40 : fetch_word Asan.M.loaded_segments (0x5da90 : word) = Some W_5da40.
Proof. vm_refl. Qed.
Lemma D_5da40 : decode_any W_5da40 = Some (Load SZ8 true 11 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da44 : bv 32 := 0x00379613.
Lemma F_5da44 : fetch_word Asan.M.loaded_segments (0x5da94 : word) = Some W_5da44.
Proof. vm_refl. Qed.
Lemma D_5da44 : decode_any W_5da44 = Some (ShiftImm ALU_SLL 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da48 : bv 32 := 0x00178793.
Lemma F_5da48 : fetch_word Asan.M.loaded_segments (0x5da98 : word) = Some W_5da48.
Proof. vm_refl. Qed.
Lemma D_5da48 : decode_any W_5da48 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da4c : bv 32 := 0x00c80633.
Lemma F_5da4c : fetch_word Asan.M.loaded_segments (0x5da9c : word) = Some W_5da4c.
Proof. vm_refl. Qed.
Lemma D_5da4c : decode_any W_5da4c = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da50 : bv 32 := 0x00e585b3.
Lemma F_5da50 : fetch_word Asan.M.loaded_segments (0x5daa0 : word) = Some W_5da50.
Proof. vm_refl. Qed.
Lemma D_5da50 : decode_any W_5da50 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da54 : bv 32 := 0x00b83423.
Lemma F_5da54 : fetch_word Asan.M.loaded_segments (0x5daa4 : word) = Some W_5da54.
Proof. vm_refl. Qed.
Lemma D_5da54 : decode_any W_5da54 = Some (Store SZ8 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da58 : bv 32 := 0x00f83823.
Lemma F_5da58 : fetch_word Asan.M.loaded_segments (0x5daa8 : word) = Some W_5da58.
Proof. vm_refl. Qed.
Lemma D_5da58 : decode_any W_5da58 = Some (Store SZ8 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da5c : bv 32 := 0x00d63c23.
Lemma F_5da5c : fetch_word Asan.M.loaded_segments (0x5daac : word) = Some W_5da5c.
Proof. vm_refl. Qed.
Lemma D_5da5c : decode_any W_5da5c = Some (Store SZ8 12 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da60 : bv 32 := 0x0100006f.
Lemma F_5da60 : fetch_word Asan.M.loaded_segments (0x5dab0 : word) = Some W_5da60.
Proof. vm_refl. Qed.
Lemma D_5da60 : decode_any W_5da60 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da64 : bv 32 := 0x00b53423.
Lemma F_5da64 : fetch_word Asan.M.loaded_segments (0x5dab4 : word) = Some W_5da64.
Proof. vm_refl. Qed.
Lemma D_5da64 : decode_any W_5da64 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da68 : bv 32 := 0x00c53023.
Lemma F_5da68 : fetch_word Asan.M.loaded_segments (0x5dab8 : word) = Some W_5da68.
Proof. vm_refl. Qed.
Lemma D_5da68 : decode_any W_5da68 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da6c : bv 32 := 0x00b53823.
Lemma F_5da6c : fetch_word Asan.M.loaded_segments (0x5dabc : word) = Some W_5da6c.
Proof. vm_refl. Qed.
Lemma D_5da6c : decode_any W_5da6c = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da70 : bv 32 := 0x01853583.
Lemma F_5da70 : fetch_word Asan.M.loaded_segments (0x5dac0 : word) = Some W_5da70.
Proof. vm_refl. Qed.
Lemma D_5da70 : decode_any W_5da70 = Some (Load SZ8 true 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da74 : bv 32 := 0x00e585b3.
Lemma F_5da74 : fetch_word Asan.M.loaded_segments (0x5dac4 : word) = Some W_5da74.
Proof. vm_refl. Qed.
Lemma D_5da74 : decode_any W_5da74 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da78 : bv 32 := 0x00b53c23.
Lemma F_5da78 : fetch_word Asan.M.loaded_segments (0x5dac8 : word) = Some W_5da78.
Proof. vm_refl. Qed.
Lemma D_5da78 : decode_any W_5da78 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da7c : bv 32 := 0x03813083.
Lemma F_5da7c : fetch_word Asan.M.loaded_segments (0x5dacc : word) = Some W_5da7c.
Proof. vm_refl. Qed.
Lemma D_5da7c : decode_any W_5da7c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da80 : bv 32 := 0x03013403.
Lemma F_5da80 : fetch_word Asan.M.loaded_segments (0x5dad0 : word) = Some W_5da80.
Proof. vm_refl. Qed.
Lemma D_5da80 : decode_any W_5da80 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da84 : bv 32 := 0x02813483.
Lemma F_5da84 : fetch_word Asan.M.loaded_segments (0x5dad4 : word) = Some W_5da84.
Proof. vm_refl. Qed.
Lemma D_5da84 : decode_any W_5da84 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da88 : bv 32 := 0x02013903.
Lemma F_5da88 : fetch_word Asan.M.loaded_segments (0x5dad8 : word) = Some W_5da88.
Proof. vm_refl. Qed.
Lemma D_5da88 : decode_any W_5da88 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da8c : bv 32 := 0x01813983.
Lemma F_5da8c : fetch_word Asan.M.loaded_segments (0x5dadc : word) = Some W_5da8c.
Proof. vm_refl. Qed.
Lemma D_5da8c : decode_any W_5da8c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da90 : bv 32 := 0x01013a03.
Lemma F_5da90 : fetch_word Asan.M.loaded_segments (0x5dae0 : word) = Some W_5da90.
Proof. vm_refl. Qed.
Lemma D_5da90 : decode_any W_5da90 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da94 : bv 32 := 0x00813a83.
Lemma F_5da94 : fetch_word Asan.M.loaded_segments (0x5dae4 : word) = Some W_5da94.
Proof. vm_refl. Qed.
Lemma D_5da94 : decode_any W_5da94 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da98 : bv 32 := 0x04010113.
Lemma F_5da98 : fetch_word Asan.M.loaded_segments (0x5dae8 : word) = Some W_5da98.
Proof. vm_refl. Qed.
Lemma D_5da98 : decode_any W_5da98 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da9c : bv 32 := 0x00008067.
Lemma F_5da9c : fetch_word Asan.M.loaded_segments (0x5daec : word) = Some W_5da9c.
Proof. vm_refl. Qed.
Lemma D_5da9c : decode_any W_5da9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daa0 : bv 32 := 0x78058413.
Lemma F_5daa0 : fetch_word Asan.M.loaded_segments (0x5daf0 : word) = Some W_5daa0.
Proof. vm_refl. Qed.
Lemma D_5daa0 : decode_any W_5daa0 = Some (OpImm ALU_ADD 8 11 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daa4 : bv 32 := 0x000fc797.
Lemma F_5daa4 : fetch_word Asan.M.loaded_segments (0x5daf4 : word) = Some W_5daa4.
Proof. vm_refl. Qed.
Lemma D_5daa4 : decode_any W_5daa4 = Some (Auipc 15 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daa8 : bv 32 := 0x86478793.
Lemma F_5daa8 : fetch_word Asan.M.loaded_segments (0x5daf8 : word) = Some W_5daa8.
Proof. vm_refl. Qed.
Lemma D_5daa8 : decode_any W_5daa8 = Some (OpImm ALU_ADD 15 15 2148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daac : bv 32 := 0x00068913.
Lemma F_5daac : fetch_word Asan.M.loaded_segments (0x5dafc : word) = Some W_5daac.
Proof. vm_refl. Qed.
Lemma D_5daac : decode_any W_5daac = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dab0 : bv 32 := 0x01800693.
Lemma F_5dab0 : fetch_word Asan.M.loaded_segments (0x5db00 : word) = Some W_5dab0.
Proof. vm_refl. Qed.
Lemma D_5dab0 : decode_any W_5dab0 = Some (OpImm ALU_ADD 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dab4 : bv 32 := 0x00050993.
Lemma F_5dab4 : fetch_word Asan.M.loaded_segments (0x5db04 : word) = Some W_5dab4.
Proof. vm_refl. Qed.
Lemma D_5dab4 : decode_any W_5dab4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dab8 : bv 32 := 0x00058493.
Lemma F_5dab8 : fetch_word Asan.M.loaded_segments (0x5db08 : word) = Some W_5dab8.
Proof. vm_refl. Qed.
Lemma D_5dab8 : decode_any W_5dab8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dabc : bv 32 := 0x00058513.
Lemma F_5dabc : fetch_word Asan.M.loaded_segments (0x5db0c : word) = Some W_5dabc.
Proof. vm_refl. Qed.
Lemma D_5dabc : decode_any W_5dabc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dac0 : bv 32 := 0x00040593.
Lemma F_5dac0 : fetch_word Asan.M.loaded_segments (0x5db10 : word) = Some W_5dac0.
Proof. vm_refl. Qed.
Lemma D_5dac0 : decode_any W_5dac0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dac4 : bv 32 := 0x00060a13.
Lemma F_5dac4 : fetch_word Asan.M.loaded_segments (0x5db14 : word) = Some W_5dac4.
Proof. vm_refl. Qed.
Lemma D_5dac4 : decode_any W_5dac4 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dac8 : bv 32 := 0x00078613.
Lemma F_5dac8 : fetch_word Asan.M.loaded_segments (0x5db18 : word) = Some W_5dac8.
Proof. vm_refl. Qed.
Lemma D_5dac8 : decode_any W_5dac8 = Some (OpImm ALU_ADD 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dacc : bv 32 := 0x00070a93.
Lemma F_5dacc : fetch_word Asan.M.loaded_segments (0x5db1c : word) = Some W_5dacc.
Proof. vm_refl. Qed.
Lemma D_5dacc : decode_any W_5dacc = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dad0 : bv 32 := 0x7e4000ef.
Lemma F_5dad0 : fetch_word Asan.M.loaded_segments (0x5db20 : word) = Some W_5dad0.
Proof. vm_refl. Qed.
Lemma D_5dad0 : decode_any W_5dad0 = Some (Jal 1 2020, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dad4 : bv 32 := 0x000a0613.
Lemma F_5dad4 : fetch_word Asan.M.loaded_segments (0x5db24 : word) = Some W_5dad4.
Proof. vm_refl. Qed.
Lemma D_5dad4 : decode_any W_5dad4 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dad8 : bv 32 := 0x00050e63.
Lemma F_5dad8 : fetch_word Asan.M.loaded_segments (0x5db28 : word) = Some W_5dad8.
Proof. vm_refl. Qed.
Lemma D_5dad8 : decode_any W_5dad8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dadc : bv 32 := 0x00090693.
Lemma F_5dadc : fetch_word Asan.M.loaded_segments (0x5db2c : word) = Some W_5dadc.
Proof. vm_refl. Qed.
Lemma D_5dadc : decode_any W_5dadc = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dae0 : bv 32 := 0x000a8713.
Lemma F_5dae0 : fetch_word Asan.M.loaded_segments (0x5db30 : word) = Some W_5dae0.
Proof. vm_refl. Qed.
Lemma D_5dae0 : decode_any W_5dae0 = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dae4 : bv 32 := 0x00098513.
Lemma F_5dae4 : fetch_word Asan.M.loaded_segments (0x5db34 : word) = Some W_5dae4.
Proof. vm_refl. Qed.
Lemma D_5dae4 : decode_any W_5dae4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dae8 : bv 32 := 0x00042783.
Lemma F_5dae8 : fetch_word Asan.M.loaded_segments (0x5db38 : word) = Some W_5dae8.
Proof. vm_refl. Qed.
Lemma D_5dae8 : decode_any W_5dae8 = Some (Load SZ4 true 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daec : bv 32 := 0x00048593.
Lemma F_5daec : fetch_word Asan.M.loaded_segments (0x5db3c : word) = Some W_5daec.
Proof. vm_refl. Qed.
Lemma D_5daec : decode_any W_5daec = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daf0 : bv 32 := 0xed1ff06f.
Lemma F_5daf0 : fetch_word Asan.M.loaded_segments (0x5db40 : word) = Some W_5daf0.
Proof. vm_refl. Qed.
Lemma D_5daf0 : decode_any W_5daf0 = Some (Jal 0 2096848, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db64 : bv 32 := 0xfd010113.
Lemma F_5db64 : fetch_word Asan.M.loaded_segments (0x5dbb4 : word) = Some W_5db64.
Proof. vm_refl. Qed.
Lemma D_5db64 : decode_any W_5db64 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db68 : bv 32 := 0x02113423.
Lemma F_5db68 : fetch_word Asan.M.loaded_segments (0x5dbb8 : word) = Some W_5db68.
Proof. vm_refl. Qed.
Lemma D_5db68 : decode_any W_5db68 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db6c : bv 32 := 0x02813023.
Lemma F_5db6c : fetch_word Asan.M.loaded_segments (0x5dbbc : word) = Some W_5db6c.
Proof. vm_refl. Qed.
Lemma D_5db6c : decode_any W_5db6c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db70 : bv 32 := 0x00913c23.
Lemma F_5db70 : fetch_word Asan.M.loaded_segments (0x5dbc0 : word) = Some W_5db70.
Proof. vm_refl. Qed.
Lemma D_5db70 : decode_any W_5db70 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db74 : bv 32 := 0x01213823.
Lemma F_5db74 : fetch_word Asan.M.loaded_segments (0x5dbc4 : word) = Some W_5db74.
Proof. vm_refl. Qed.
Lemma D_5db74 : decode_any W_5db74 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db78 : bv 32 := 0x01313423.
Lemma F_5db78 : fetch_word Asan.M.loaded_segments (0x5dbc8 : word) = Some W_5db78.
Proof. vm_refl. Qed.
Lemma D_5db78 : decode_any W_5db78 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db7c : bv 32 := 0x01413023.
Lemma F_5db7c : fetch_word Asan.M.loaded_segments (0x5dbcc : word) = Some W_5db7c.
Proof. vm_refl. Qed.
Lemma D_5db7c : decode_any W_5db7c = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db80 : bv 32 := 0x00163713.
Lemma F_5db80 : fetch_word Asan.M.loaded_segments (0x5dbd0 : word) = Some W_5db80.
Proof. vm_refl. Qed.
Lemma D_5db80 : decode_any W_5db80 = Some (OpImm ALU_SLTU 14 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db84 : bv 32 := 0x00e60633.
Lemma F_5db84 : fetch_word Asan.M.loaded_segments (0x5dbd4 : word) = Some W_5db84.
Proof. vm_refl. Qed.
Lemma D_5db84 : decode_any W_5db84 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db88 : bv 32 := 0xfff64713.
Lemma F_5db88 : fetch_word Asan.M.loaded_segments (0x5dbd8 : word) = Some W_5db88.
Proof. vm_refl. Qed.
Lemma D_5db88 : decode_any W_5db88 = Some (OpImm ALU_XOR 14 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db8c : bv 32 := 0x02d77263.
Lemma F_5db8c : fetch_word Asan.M.loaded_segments (0x5dbdc : word) = Some W_5db8c.
Proof. vm_refl. Qed.
Lemma D_5db8c : decode_any W_5db8c = Some (Branch BC_GEU 14 13 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbb0 : bv 32 := 0x00900793.
Lemma F_5dbb0 : fetch_word Asan.M.loaded_segments (0x5dc00 : word) = Some W_5dbb0.
Proof. vm_refl. Qed.
Lemma D_5dbb0 : decode_any W_5dbb0 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbb4 : bv 32 := 0x00060713.
Lemma F_5dbb4 : fetch_word Asan.M.loaded_segments (0x5dc04 : word) = Some W_5dbb4.
Proof. vm_refl. Qed.
Lemma D_5dbb4 : decode_any W_5dbb4 = Some (OpImm ALU_ADD 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbb8 : bv 32 := 0x02f6e063.
Lemma F_5dbb8 : fetch_word Asan.M.loaded_segments (0x5dc08 : word) = Some W_5dbb8.
Proof. vm_refl. Qed.
Lemma D_5dbb8 : decode_any W_5dbb8 = Some (Branch BC_LTU 13 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbd8 : bv 32 := 0x000107b7.
Lemma F_5dbd8 : fetch_word Asan.M.loaded_segments (0x5dc28 : word) = Some W_5dbd8.
Proof. vm_refl. Qed.
Lemma D_5dbd8 : decode_any W_5dbd8 = Some (Lui 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbdc : bv 32 := 0x00d7ee63.
Lemma F_5dbdc : fetch_word Asan.M.loaded_segments (0x5dc2c : word) = Some W_5dbdc.
Proof. vm_refl. Qed.
Lemma D_5dbdc : decode_any W_5dbdc = Some (Branch BC_LTU 15 13 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbe0 : bv 32 := 0x00e7ec63.
Lemma F_5dbe0 : fetch_word Asan.M.loaded_segments (0x5dc30 : word) = Some W_5dbe0.
Proof. vm_refl. Qed.
Lemma D_5dbe0 : decode_any W_5dbe0 = Some (Branch BC_LTU 15 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbe4 : bv 32 := 0x20000613.
Lemma F_5dbe4 : fetch_word Asan.M.loaded_segments (0x5dc34 : word) = Some W_5dbe4.
Proof. vm_refl. Qed.
Lemma D_5dbe4 : decode_any W_5dbe4 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbe8 : bv 32 := 0x02e66a63.
Lemma F_5dbe8 : fetch_word Asan.M.loaded_segments (0x5dc38 : word) = Some W_5dbe8.
Proof. vm_refl. Qed.
Lemma D_5dbe8 : decode_any W_5dbe8 = Some (Branch BC_LTU 12 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbec : bv 32 := 0x01f70713.
Lemma F_5dbec : fetch_word Asan.M.loaded_segments (0x5dc3c : word) = Some W_5dbec.
Proof. vm_refl. Qed.
Lemma D_5dbec : decode_any W_5dbec = Some (OpImm ALU_ADD 14 14 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbf0 : bv 32 := 0x00575413.
Lemma F_5dbf0 : fetch_word Asan.M.loaded_segments (0x5dc40 : word) = Some W_5dbf0.
Proof. vm_refl. Qed.
Lemma D_5dbf0 : decode_any W_5dbf0 = Some (ShiftImm ALU_SRL 8 14 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbf4 : bv 32 := 0x1040006f.
Lemma F_5dbf4 : fetch_word Asan.M.loaded_segments (0x5dc44 : word) = Some W_5dbf4.
Proof. vm_refl. Qed.
Lemma D_5dbf4 : decode_any W_5dbf4 = Some (Jal 0 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbf8 : bv 32 := 0x04050713.
Lemma F_5dbf8 : fetch_word Asan.M.loaded_segments (0x5dc48 : word) = Some W_5dbf8.
Proof. vm_refl. Qed.
Lemma D_5dbf8 : decode_any W_5dbf8 = Some (OpImm ALU_ADD 14 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbfc : bv 32 := 0x2b050593.
Lemma F_5dbfc : fetch_word Asan.M.loaded_segments (0x5dc4c : word) = Some W_5dbfc.
Proof. vm_refl. Qed.
Lemma D_5dbfc : decode_any W_5dbfc = Some (OpImm ALU_ADD 11 10 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc00 : bv 32 := 0x00070513.
Lemma F_5dc00 : fetch_word Asan.M.loaded_segments (0x5dc50 : word) = Some W_5dc00.
Proof. vm_refl. Qed.
Lemma D_5dc00 : decode_any W_5dc00 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc04 : bv 32 := 0x00068413.
Lemma F_5dc04 : fetch_word Asan.M.loaded_segments (0x5dc54 : word) = Some W_5dc04.
Proof. vm_refl. Qed.
Lemma D_5dc04 : decode_any W_5dc04 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc08 : bv 32 := 0x234000ef.
Lemma F_5dc08 : fetch_word Asan.M.loaded_segments (0x5dc58 : word) = Some W_5dc08.
Proof. vm_refl. Qed.
Lemma D_5dc08 : decode_any W_5dc08 = Some (Jal 1 564, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc0c : bv 32 := 0x00040693.
Lemma F_5dc0c : fetch_word Asan.M.loaded_segments (0x5dc5c : word) = Some W_5dc0c.
Proof. vm_refl. Qed.
Lemma D_5dc0c : decode_any W_5dc0c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc10 : bv 32 := 0x00900593.
Lemma F_5dc10 : fetch_word Asan.M.loaded_segments (0x5dc60 : word) = Some W_5dc10.
Proof. vm_refl. Qed.
Lemma D_5dc10 : decode_any W_5dc10 = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc14 : bv 32 := 0x14b47463.
Lemma F_5dc14 : fetch_word Asan.M.loaded_segments (0x5dc64 : word) = Some W_5dc14.
Proof. vm_refl. Qed.
Lemma D_5dc14 : decode_any W_5dc14 = Some (Branch BC_GEU 8 11 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc18 : bv 32 := 0x1500006f.
Lemma F_5dc18 : fetch_word Asan.M.loaded_segments (0x5dc68 : word) = Some W_5dc18.
Proof. vm_refl. Qed.
Lemma D_5dc18 : decode_any W_5dc18 = Some (Jal 0 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc1c : bv 32 := 0x00175613.
Lemma F_5dc1c : fetch_word Asan.M.loaded_segments (0x5dc6c : word) = Some W_5dc1c.
Proof. vm_refl. Qed.
Lemma D_5dc1c : decode_any W_5dc1c = Some (ShiftImm ALU_SRL 12 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc20 : bv 32 := 0x555557b7.
Lemma F_5dc20 : fetch_word Asan.M.loaded_segments (0x5dc70 : word) = Some W_5dc20.
Proof. vm_refl. Qed.
Lemma D_5dc20 : decode_any W_5dc20 = Some (Lui 15 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc24 : bv 32 := 0x33333837.
Lemma F_5dc24 : fetch_word Asan.M.loaded_segments (0x5dc74 : word) = Some W_5dc24.
Proof. vm_refl. Qed.
Lemma D_5dc24 : decode_any W_5dc24 = Some (Lui 16 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc28 : bv 32 := 0x0f0f18b7.
Lemma F_5dc28 : fetch_word Asan.M.loaded_segments (0x5dc78 : word) = Some W_5dc28.
Proof. vm_refl. Qed.
Lemma D_5dc28 : decode_any W_5dc28 = Some (Lui 17 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc2c : bv 32 := 0x010102b7.
Lemma F_5dc2c : fetch_word Asan.M.loaded_segments (0x5dc7c : word) = Some W_5dc2c.
Proof. vm_refl. Qed.
Lemma D_5dc2c : decode_any W_5dc2c = Some (Lui 5 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc30 : bv 32 := 0x00c76633.
Lemma F_5dc30 : fetch_word Asan.M.loaded_segments (0x5dc80 : word) = Some W_5dc30.
Proof. vm_refl. Qed.
Lemma D_5dc30 : decode_any W_5dc30 = Some (Op ALU_OR 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc34 : bv 32 := 0x5557879b.
Lemma F_5dc34 : fetch_word Asan.M.loaded_segments (0x5dc84 : word) = Some W_5dc34.
Proof. vm_refl. Qed.
Lemma D_5dc34 : decode_any W_5dc34 = Some (OpImm32 15 15 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc38 : bv 32 := 0x3338081b.
Lemma F_5dc38 : fetch_word Asan.M.loaded_segments (0x5dc88 : word) = Some W_5dc38.
Proof. vm_refl. Qed.
Lemma D_5dc38 : decode_any W_5dc38 = Some (OpImm32 16 16 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc3c : bv 32 := 0xf0f8889b.
Lemma F_5dc3c : fetch_word Asan.M.loaded_segments (0x5dc8c : word) = Some W_5dc3c.
Proof. vm_refl. Qed.
Lemma D_5dc3c : decode_any W_5dc3c = Some (OpImm32 17 17 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc40 : bv 32 := 0x1012829b.
Lemma F_5dc40 : fetch_word Asan.M.loaded_segments (0x5dc90 : word) = Some W_5dc40.
Proof. vm_refl. Qed.
Lemma D_5dc40 : decode_any W_5dc40 = Some (OpImm32 5 5 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc44 : bv 32 := 0x00265313.
Lemma F_5dc44 : fetch_word Asan.M.loaded_segments (0x5dc94 : word) = Some W_5dc44.
Proof. vm_refl. Qed.
Lemma D_5dc44 : decode_any W_5dc44 = Some (ShiftImm ALU_SRL 6 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc48 : bv 32 := 0x00666633.
Lemma F_5dc48 : fetch_word Asan.M.loaded_segments (0x5dc98 : word) = Some W_5dc48.
Proof. vm_refl. Qed.
Lemma D_5dc48 : decode_any W_5dc48 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc4c : bv 32 := 0x02079313.
Lemma F_5dc4c : fetch_word Asan.M.loaded_segments (0x5dc9c : word) = Some W_5dc4c.
Proof. vm_refl. Qed.
Lemma D_5dc4c : decode_any W_5dc4c = Some (ShiftImm ALU_SLL 6 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc50 : bv 32 := 0x006787b3.
Lemma F_5dc50 : fetch_word Asan.M.loaded_segments (0x5dca0 : word) = Some W_5dc50.
Proof. vm_refl. Qed.
Lemma D_5dc50 : decode_any W_5dc50 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc54 : bv 32 := 0x02081313.
Lemma F_5dc54 : fetch_word Asan.M.loaded_segments (0x5dca4 : word) = Some W_5dc54.
Proof. vm_refl. Qed.
Lemma D_5dc54 : decode_any W_5dc54 = Some (ShiftImm ALU_SLL 6 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc58 : bv 32 := 0x00680833.
Lemma F_5dc58 : fetch_word Asan.M.loaded_segments (0x5dca8 : word) = Some W_5dc58.
Proof. vm_refl. Qed.
Lemma D_5dc58 : decode_any W_5dc58 = Some (Op ALU_ADD 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc5c : bv 32 := 0x02089313.
Lemma F_5dc5c : fetch_word Asan.M.loaded_segments (0x5dcac : word) = Some W_5dc5c.
Proof. vm_refl. Qed.
Lemma D_5dc5c : decode_any W_5dc5c = Some (ShiftImm ALU_SLL 6 17 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc60 : bv 32 := 0x006888b3.
Lemma F_5dc60 : fetch_word Asan.M.loaded_segments (0x5dcb0 : word) = Some W_5dc60.
Proof. vm_refl. Qed.
Lemma D_5dc60 : decode_any W_5dc60 = Some (Op ALU_ADD 17 17 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc64 : bv 32 := 0x02029313.
Lemma F_5dc64 : fetch_word Asan.M.loaded_segments (0x5dcb4 : word) = Some W_5dc64.
Proof. vm_refl. Qed.
Lemma D_5dc64 : decode_any W_5dc64 = Some (ShiftImm ALU_SLL 6 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc68 : bv 32 := 0x006282b3.
Lemma F_5dc68 : fetch_word Asan.M.loaded_segments (0x5dcb8 : word) = Some W_5dc68.
Proof. vm_refl. Qed.
Lemma D_5dc68 : decode_any W_5dc68 = Some (Op ALU_ADD 5 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc6c : bv 32 := 0x00465313.
Lemma F_5dc6c : fetch_word Asan.M.loaded_segments (0x5dcbc : word) = Some W_5dc6c.
Proof. vm_refl. Qed.
Lemma D_5dc6c : decode_any W_5dc6c = Some (ShiftImm ALU_SRL 6 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc70 : bv 32 := 0x00666633.
Lemma F_5dc70 : fetch_word Asan.M.loaded_segments (0x5dcc0 : word) = Some W_5dc70.
Proof. vm_refl. Qed.
Lemma D_5dc70 : decode_any W_5dc70 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc74 : bv 32 := 0x00865313.
Lemma F_5dc74 : fetch_word Asan.M.loaded_segments (0x5dcc4 : word) = Some W_5dc74.
Proof. vm_refl. Qed.
Lemma D_5dc74 : decode_any W_5dc74 = Some (ShiftImm ALU_SRL 6 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc78 : bv 32 := 0x00666633.
Lemma F_5dc78 : fetch_word Asan.M.loaded_segments (0x5dcc8 : word) = Some W_5dc78.
Proof. vm_refl. Qed.
Lemma D_5dc78 : decode_any W_5dc78 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc7c : bv 32 := 0x01065313.
Lemma F_5dc7c : fetch_word Asan.M.loaded_segments (0x5dccc : word) = Some W_5dc7c.
Proof. vm_refl. Qed.
Lemma D_5dc7c : decode_any W_5dc7c = Some (ShiftImm ALU_SRL 6 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc80 : bv 32 := 0x00666633.
Lemma F_5dc80 : fetch_word Asan.M.loaded_segments (0x5dcd0 : word) = Some W_5dc80.
Proof. vm_refl. Qed.
Lemma D_5dc80 : decode_any W_5dc80 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc84 : bv 32 := 0x02065313.
Lemma F_5dc84 : fetch_word Asan.M.loaded_segments (0x5dcd4 : word) = Some W_5dc84.
Proof. vm_refl. Qed.
Lemma D_5dc84 : decode_any W_5dc84 = Some (ShiftImm ALU_SRL 6 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc88 : bv 32 := 0x00666633.
Lemma F_5dc88 : fetch_word Asan.M.loaded_segments (0x5dcd8 : word) = Some W_5dc88.
Proof. vm_refl. Qed.
Lemma D_5dc88 : decode_any W_5dc88 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc8c : bv 32 := 0xfff64613.
Lemma F_5dc8c : fetch_word Asan.M.loaded_segments (0x5dcdc : word) = Some W_5dc8c.
Proof. vm_refl. Qed.
Lemma D_5dc8c : decode_any W_5dc8c = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc90 : bv 32 := 0x00165313.
Lemma F_5dc90 : fetch_word Asan.M.loaded_segments (0x5dce0 : word) = Some W_5dc90.
Proof. vm_refl. Qed.
Lemma D_5dc90 : decode_any W_5dc90 = Some (ShiftImm ALU_SRL 6 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc94 : bv 32 := 0x00f377b3.
Lemma F_5dc94 : fetch_word Asan.M.loaded_segments (0x5dce4 : word) = Some W_5dc94.
Proof. vm_refl. Qed.
Lemma D_5dc94 : decode_any W_5dc94 = Some (Op ALU_AND 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc98 : bv 32 := 0x40f60633.
Lemma F_5dc98 : fetch_word Asan.M.loaded_segments (0x5dce8 : word) = Some W_5dc98.
Proof. vm_refl. Qed.
Lemma D_5dc98 : decode_any W_5dc98 = Some (Op ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc9c : bv 32 := 0x010677b3.
Lemma F_5dc9c : fetch_word Asan.M.loaded_segments (0x5dcec : word) = Some W_5dc9c.
Proof. vm_refl. Qed.
Lemma D_5dc9c : decode_any W_5dc9c = Some (Op ALU_AND 15 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca0 : bv 32 := 0x00265613.
Lemma F_5dca0 : fetch_word Asan.M.loaded_segments (0x5dcf0 : word) = Some W_5dca0.
Proof. vm_refl. Qed.
Lemma D_5dca0 : decode_any W_5dca0 = Some (ShiftImm ALU_SRL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca4 : bv 32 := 0x01067633.
Lemma F_5dca4 : fetch_word Asan.M.loaded_segments (0x5dcf4 : word) = Some W_5dca4.
Proof. vm_refl. Qed.
Lemma D_5dca4 : decode_any W_5dca4 = Some (Op ALU_AND 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca8 : bv 32 := 0x00c78633.
Lemma F_5dca8 : fetch_word Asan.M.loaded_segments (0x5dcf8 : word) = Some W_5dca8.
Proof. vm_refl. Qed.
Lemma D_5dca8 : decode_any W_5dca8 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcac : bv 32 := 0x00465793.
Lemma F_5dcac : fetch_word Asan.M.loaded_segments (0x5dcfc : word) = Some W_5dcac.
Proof. vm_refl. Qed.
Lemma D_5dcac : decode_any W_5dcac = Some (ShiftImm ALU_SRL 15 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb0 : bv 32 := 0x00f60633.
Lemma F_5dcb0 : fetch_word Asan.M.loaded_segments (0x5dd00 : word) = Some W_5dcb0.
Proof. vm_refl. Qed.
Lemma D_5dcb0 : decode_any W_5dcb0 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb4 : bv 32 := 0x03e00793.
Lemma F_5dcb4 : fetch_word Asan.M.loaded_segments (0x5dd04 : word) = Some W_5dcb4.
Proof. vm_refl. Qed.
Lemma D_5dcb4 : decode_any W_5dcb4 = Some (OpImm ALU_ADD 15 0 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb8 : bv 32 := 0x01167633.
Lemma F_5dcb8 : fetch_word Asan.M.loaded_segments (0x5dd08 : word) = Some W_5dcb8.
Proof. vm_refl. Qed.
Lemma D_5dcb8 : decode_any W_5dcb8 = Some (Op ALU_AND 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcbc : bv 32 := 0xfff00813.
Lemma F_5dcbc : fetch_word Asan.M.loaded_segments (0x5dd0c : word) = Some W_5dcbc.
Proof. vm_refl. Qed.
Lemma D_5dcbc : decode_any W_5dcbc = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcc0 : bv 32 := 0x02560633.
Lemma F_5dcc0 : fetch_word Asan.M.loaded_segments (0x5dd10 : word) = Some W_5dcc0.
Proof. vm_refl. Qed.
Lemma D_5dcc0 : decode_any W_5dcc0 = Some (Mul M_MUL 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcc4 : bv 32 := 0x03865613.
Lemma F_5dcc4 : fetch_word Asan.M.loaded_segments (0x5dd14 : word) = Some W_5dcc4.
Proof. vm_refl. Qed.
Lemma D_5dcc4 : decode_any W_5dcc4 = Some (ShiftImm ALU_SRL 12 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcc8 : bv 32 := 0x40c787bb.
Lemma F_5dcc8 : fetch_word Asan.M.loaded_segments (0x5dd18 : word) = Some W_5dcc8.
Proof. vm_refl. Qed.
Lemma D_5dcc8 : decode_any W_5dcc8 = Some (Op32 ALU_SUB 15 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dccc : bv 32 := 0x00161613.
Lemma F_5dccc : fetch_word Asan.M.loaded_segments (0x5dd1c : word) = Some W_5dccc.
Proof. vm_refl. Qed.
Lemma D_5dccc : decode_any W_5dccc = Some (ShiftImm ALU_SLL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcd0 : bv 32 := 0x00f758b3.
Lemma F_5dcd0 : fetch_word Asan.M.loaded_segments (0x5dd20 : word) = Some W_5dcd0.
Proof. vm_refl. Qed.
Lemma D_5dcd0 : decode_any W_5dcd0 = Some (Op ALU_SRL 17 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcd4 : bv 32 := 0x00f817bb.
Lemma F_5dcd4 : fetch_word Asan.M.loaded_segments (0x5dd24 : word) = Some W_5dcd4.
Proof. vm_refl. Qed.
Lemma D_5dcd4 : decode_any W_5dcd4 = Some (Op32 ALU_SLL 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcd8 : bv 32 := 0x07e64613.
Lemma F_5dcd8 : fetch_word Asan.M.loaded_segments (0x5dd28 : word) = Some W_5dcd8.
Proof. vm_refl. Qed.
Lemma D_5dcd8 : decode_any W_5dcd8 = Some (OpImm ALU_XOR 12 12 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcdc : bv 32 := 0x0018f813.
Lemma F_5dcdc : fetch_word Asan.M.loaded_segments (0x5dd2c : word) = Some W_5dcdc.
Proof. vm_refl. Qed.
Lemma D_5dcdc : decode_any W_5dcdc = Some (OpImm ALU_AND 16 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dce0 : bv 32 := 0xfff7c793.
Lemma F_5dce0 : fetch_word Asan.M.loaded_segments (0x5dd30 : word) = Some W_5dce0.
Proof. vm_refl. Qed.
Lemma D_5dce0 : decode_any W_5dce0 = Some (OpImm ALU_XOR 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dce4 : bv 32 := 0x00f77733.
Lemma F_5dce4 : fetch_word Asan.M.loaded_segments (0x5dd34 : word) = Some W_5dce4.
Proof. vm_refl. Qed.
Lemma D_5dce4 : decode_any W_5dce4 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dce8 : bv 32 := 0x01066633.
Lemma F_5dce8 : fetch_word Asan.M.loaded_segments (0x5dd38 : word) = Some W_5dce8.
Proof. vm_refl. Qed.
Lemma D_5dce8 : decode_any W_5dce8 = Some (Op ALU_OR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcec : bv 32 := 0x00e03733.
Lemma F_5dcec : fetch_word Asan.M.loaded_segments (0x5dd3c : word) = Some W_5dcec.
Proof. vm_refl. Qed.
Lemma D_5dcec : decode_any W_5dcec = Some (Op ALU_SLTU 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcf0 : bv 32 := 0x00e60633.
Lemma F_5dcf0 : fetch_word Asan.M.loaded_segments (0x5dd40 : word) = Some W_5dcf0.
Proof. vm_refl. Qed.
Lemma D_5dcf0 : decode_any W_5dcf0 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcf4 : bv 32 := 0xffe60413.
Lemma F_5dcf4 : fetch_word Asan.M.loaded_segments (0x5dd44 : word) = Some W_5dcf4.
Proof. vm_refl. Qed.
Lemma D_5dcf4 : decode_any W_5dcf4 = Some (OpImm ALU_ADD 8 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcf8 : bv 32 := 0x0a040063.
Lemma F_5dcf8 : fetch_word Asan.M.loaded_segments (0x5dd48 : word) = Some W_5dcf8.
Proof. vm_refl. Qed.
Lemma D_5dcf8 : decode_any W_5dcf8 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcfc : bv 32 := 0x02000613.
Lemma F_5dcfc : fetch_word Asan.M.loaded_segments (0x5dd4c : word) = Some W_5dcfc.
Proof. vm_refl. Qed.
Lemma D_5dcfc : decode_any W_5dcfc = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd00 : bv 32 := 0x0cc47a63.
Lemma F_5dd00 : fetch_word Asan.M.loaded_segments (0x5dd50 : word) = Some W_5dd00.
Proof. vm_refl. Qed.
Lemma D_5dd00 : decode_any W_5dd00 = Some (Branch BC_GEU 8 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd04 : bv 32 := 0x05000613.
Lemma F_5dd04 : fetch_word Asan.M.loaded_segments (0x5dd54 : word) = Some W_5dd04.
Proof. vm_refl. Qed.
Lemma D_5dd04 : decode_any W_5dd04 = Some (OpImm ALU_ADD 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd08 : bv 32 := 0x02c404b3.
Lemma F_5dd08 : fetch_word Asan.M.loaded_segments (0x5dd58 : word) = Some W_5dd08.
Proof. vm_refl. Qed.
Lemma D_5dd08 : decode_any W_5dd08 = Some (Mul M_MUL 9 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd0c : bv 32 := 0x009584b3.
Lemma F_5dd0c : fetch_word Asan.M.loaded_segments (0x5dd5c : word) = Some W_5dd0c.
Proof. vm_refl. Qed.
Lemma D_5dd0c : decode_any W_5dd0c = Some (Op ALU_ADD 9 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd10 : bv 32 := 0x0004a603.
Lemma F_5dd10 : fetch_word Asan.M.loaded_segments (0x5dd60 : word) = Some W_5dd10.
Proof. vm_refl. Qed.
Lemma D_5dd10 : decode_any W_5dd10 = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd14 : bv 32 := 0x0e060063.
Lemma F_5dd14 : fetch_word Asan.M.loaded_segments (0x5dd64 : word) = Some W_5dd14.
Proof. vm_refl. Qed.
Lemma D_5dd14 : decode_any W_5dd14 = Some (Branch BC_EQ 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd18 : bv 32 := 0xfff60613.
Lemma F_5dd18 : fetch_word Asan.M.loaded_segments (0x5dd68 : word) = Some W_5dd18.
Proof. vm_refl. Qed.
Lemma D_5dd18 : decode_any W_5dd18 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd1c : bv 32 := 0x7ff58593.
Lemma F_5dd1c : fetch_word Asan.M.loaded_segments (0x5dd6c : word) = Some W_5dd1c.
Proof. vm_refl. Qed.
Lemma D_5dd1c : decode_any W_5dd1c = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd20 : bv 32 := 0x02061713.
Lemma F_5dd20 : fetch_word Asan.M.loaded_segments (0x5dd70 : word) = Some W_5dd20.
Proof. vm_refl. Qed.
Lemma D_5dd20 : decode_any W_5dd20 = Some (ShiftImm ALU_SLL 14 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd24 : bv 32 := 0x00c4a023.
Lemma F_5dd24 : fetch_word Asan.M.loaded_segments (0x5dd74 : word) = Some W_5dd24.
Proof. vm_refl. Qed.
Lemma D_5dd24 : decode_any W_5dd24 = Some (Store SZ4 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd28 : bv 32 := 0x21158593.
Lemma F_5dd28 : fetch_word Asan.M.loaded_segments (0x5dd78 : word) = Some W_5dd28.
Proof. vm_refl. Qed.
Lemma D_5dd28 : decode_any W_5dd28 = Some (OpImm ALU_ADD 11 11 529, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd2c : bv 32 := 0x0084b603.
Lemma F_5dd2c : fetch_word Asan.M.loaded_segments (0x5dd7c : word) = Some W_5dd2c.
Proof. vm_refl. Qed.
Lemma D_5dd2c : decode_any W_5dd2c = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd30 : bv 32 := 0x01e75713.
Lemma F_5dd30 : fetch_word Asan.M.loaded_segments (0x5dd80 : word) = Some W_5dd30.
Proof. vm_refl. Qed.
Lemma D_5dd30 : decode_any W_5dd30 = Some (ShiftImm ALU_SRL 14 14 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd34 : bv 32 := 0x00e48733.
Lemma F_5dd34 : fetch_word Asan.M.loaded_segments (0x5dd84 : word) = Some W_5dd34.
Proof. vm_refl. Qed.
Lemma D_5dd34 : decode_any W_5dd34 = Some (Op ALU_ADD 14 9 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd38 : bv 32 := 0x01076703.
Lemma F_5dd38 : fetch_word Asan.M.loaded_segments (0x5dd88 : word) = Some W_5dd38.
Proof. vm_refl. Qed.
Lemma D_5dd38 : decode_any W_5dd38 = Some (Load SZ4 false 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd3c : bv 32 := 0x00c5b02f.
Lemma F_5dd3c : fetch_word Asan.M.loaded_segments (0x5dd8c : word) = Some W_5dd3c.
Proof. vm_refl. Qed.
Lemma D_5dd3c : decode_any W_5dd3c = Some (Amo AMO_ADD AD false false 0 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd40 : bv 32 := 0x02053503.
Lemma F_5dd40 : fetch_word Asan.M.loaded_segments (0x5dd90 : word) = Some W_5dd40.
Proof. vm_refl. Qed.
Lemma D_5dd40 : decode_any W_5dd40 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd44 : bv 32 := 0x02041413.
Lemma F_5dd44 : fetch_word Asan.M.loaded_segments (0x5dd94 : word) = Some W_5dd44.
Proof. vm_refl. Qed.
Lemma D_5dd44 : decode_any W_5dd44 = Some (ShiftImm ALU_SLL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd48 : bv 32 := 0x00471713.
Lemma F_5dd48 : fetch_word Asan.M.loaded_segments (0x5dd98 : word) = Some W_5dd48.
Proof. vm_refl. Qed.
Lemma D_5dd48 : decode_any W_5dd48 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd4c : bv 32 := 0x00a40533.
Lemma F_5dd4c : fetch_word Asan.M.loaded_segments (0x5dd9c : word) = Some W_5dd4c.
Proof. vm_refl. Qed.
Lemma D_5dd4c : decode_any W_5dd4c = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd50 : bv 32 := 0x00a70533.
Lemma F_5dd50 : fetch_word Asan.M.loaded_segments (0x5dda0 : word) = Some W_5dd50.
Proof. vm_refl. Qed.
Lemma D_5dd50 : decode_any W_5dd50 = Some (Op ALU_ADD 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd54 : bv 32 := 0x00900593.
Lemma F_5dd54 : fetch_word Asan.M.loaded_segments (0x5dda4 : word) = Some W_5dd54.
Proof. vm_refl. Qed.
Lemma D_5dd54 : decode_any W_5dd54 = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd58 : bv 32 := 0x00b6e863.
Lemma F_5dd58 : fetch_word Asan.M.loaded_segments (0x5dda8 : word) = Some W_5dd58.
Proof. vm_refl. Qed.
Lemma D_5dd58 : decode_any W_5dd58 = Some (Branch BC_LTU 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd5c : bv 32 := 0xfff68693.
Lemma F_5dd5c : fetch_word Asan.M.loaded_segments (0x5ddac : word) = Some W_5dd5c.
Proof. vm_refl. Qed.
Lemma D_5dd5c : decode_any W_5dd5c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd60 : bv 32 := 0x00a6f6b3.
Lemma F_5dd60 : fetch_word Asan.M.loaded_segments (0x5ddb0 : word) = Some W_5dd60.
Proof. vm_refl. Qed.
Lemma D_5dd60 : decode_any W_5dd60 = Some (Op ALU_AND 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd64 : bv 32 := 0x04069a63.
Lemma F_5dd64 : fetch_word Asan.M.loaded_segments (0x5ddb4 : word) = Some W_5dd64.
Proof. vm_refl. Qed.
Lemma D_5dd64 : decode_any W_5dd64 = Some (Branch BC_NE 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd68 : bv 32 := 0x02813083.
Lemma F_5dd68 : fetch_word Asan.M.loaded_segments (0x5ddb8 : word) = Some W_5dd68.
Proof. vm_refl. Qed.
Lemma D_5dd68 : decode_any W_5dd68 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd6c : bv 32 := 0x02013403.
Lemma F_5dd6c : fetch_word Asan.M.loaded_segments (0x5ddbc : word) = Some W_5dd6c.
Proof. vm_refl. Qed.
Lemma D_5dd6c : decode_any W_5dd6c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd70 : bv 32 := 0x01813483.
Lemma F_5dd70 : fetch_word Asan.M.loaded_segments (0x5ddc0 : word) = Some W_5dd70.
Proof. vm_refl. Qed.
Lemma D_5dd70 : decode_any W_5dd70 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd74 : bv 32 := 0x01013903.
Lemma F_5dd74 : fetch_word Asan.M.loaded_segments (0x5ddc4 : word) = Some W_5dd74.
Proof. vm_refl. Qed.
Lemma D_5dd74 : decode_any W_5dd74 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd78 : bv 32 := 0x00813983.
Lemma F_5dd78 : fetch_word Asan.M.loaded_segments (0x5ddc8 : word) = Some W_5dd78.
Proof. vm_refl. Qed.
Lemma D_5dd78 : decode_any W_5dd78 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd7c : bv 32 := 0x00013a03.
Lemma F_5dd7c : fetch_word Asan.M.loaded_segments (0x5ddcc : word) = Some W_5dd7c.
Proof. vm_refl. Qed.
Lemma D_5dd7c : decode_any W_5dd7c = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd80 : bv 32 := 0x03010113.
Lemma F_5dd80 : fetch_word Asan.M.loaded_segments (0x5ddd0 : word) = Some W_5dd80.
Proof. vm_refl. Qed.
Lemma D_5dd80 : decode_any W_5dd80 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd84 : bv 32 := 0x00008067.
Lemma F_5dd84 : fetch_word Asan.M.loaded_segments (0x5ddd4 : word) = Some W_5dd84.
Proof. vm_refl. Qed.
Lemma D_5dd84 : decode_any W_5dd84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddf4 : bv 32 := 0x00068913.
Lemma F_5ddf4 : fetch_word Asan.M.loaded_segments (0x5de44 : word) = Some W_5ddf4.
Proof. vm_refl. Qed.
Lemma D_5ddf4 : decode_any W_5ddf4 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddf8 : bv 32 := 0x00050613.
Lemma F_5ddf8 : fetch_word Asan.M.loaded_segments (0x5de48 : word) = Some W_5ddf8.
Proof. vm_refl. Qed.
Lemma D_5ddf8 : decode_any W_5ddf8 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddfc : bv 32 := 0x00058993.
Lemma F_5ddfc : fetch_word Asan.M.loaded_segments (0x5de4c : word) = Some W_5ddfc.
Proof. vm_refl. Qed.
Lemma D_5ddfc : decode_any W_5ddfc = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de00 : bv 32 := 0x00058513.
Lemma F_5de00 : fetch_word Asan.M.loaded_segments (0x5de50 : word) = Some W_5de00.
Proof. vm_refl. Qed.
Lemma D_5de00 : decode_any W_5de00 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de04 : bv 32 := 0x00048593.
Lemma F_5de04 : fetch_word Asan.M.loaded_segments (0x5de54 : word) = Some W_5de04.
Proof. vm_refl. Qed.
Lemma D_5de04 : decode_any W_5de04 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de08 : bv 32 := 0x00060a13.
Lemma F_5de08 : fetch_word Asan.M.loaded_segments (0x5de58 : word) = Some W_5de08.
Proof. vm_refl. Qed.
Lemma D_5de08 : decode_any W_5de08 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de0c : bv 32 := 0x00040693.
Lemma F_5de0c : fetch_word Asan.M.loaded_segments (0x5de5c : word) = Some W_5de0c.
Proof. vm_refl. Qed.
Lemma D_5de0c : decode_any W_5de0c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de10 : bv 32 := 0x4a4000ef.
Lemma F_5de10 : fetch_word Asan.M.loaded_segments (0x5de60 : word) = Some W_5de10.
Proof. vm_refl. Qed.
Lemma D_5de10 : decode_any W_5de10 = Some (Jal 1 1188, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de14 : bv 32 := 0x00050c63.
Lemma F_5de14 : fetch_word Asan.M.loaded_segments (0x5de64 : word) = Some W_5de14.
Proof. vm_refl. Qed.
Lemma D_5de14 : decode_any W_5de14 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de18 : bv 32 := 0x0004a603.
Lemma F_5de18 : fetch_word Asan.M.loaded_segments (0x5de68 : word) = Some W_5de18.
Proof. vm_refl. Qed.
Lemma D_5de18 : decode_any W_5de18 = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de1c : bv 32 := 0x00090693.
Lemma F_5de1c : fetch_word Asan.M.loaded_segments (0x5de6c : word) = Some W_5de1c.
Proof. vm_refl. Qed.
Lemma D_5de1c : decode_any W_5de1c = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de20 : bv 32 := 0x000a0513.
Lemma F_5de20 : fetch_word Asan.M.loaded_segments (0x5de70 : word) = Some W_5de20.
Proof. vm_refl. Qed.
Lemma D_5de20 : decode_any W_5de20 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de24 : bv 32 := 0x00098593.
Lemma F_5de24 : fetch_word Asan.M.loaded_segments (0x5de74 : word) = Some W_5de24.
Proof. vm_refl. Qed.
Lemma D_5de24 : decode_any W_5de24 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de28 : bv 32 := 0xef1ff06f.
Lemma F_5de28 : fetch_word Asan.M.loaded_segments (0x5de78 : word) = Some W_5de28.
Proof. vm_refl. Qed.
Lemma D_5de28 : decode_any W_5de28 = Some (Jal 0 2096880, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de3c : bv 32 := 0xfa010113.
Lemma F_5de3c : fetch_word Asan.M.loaded_segments (0x5de8c : word) = Some W_5de3c.
Proof. vm_refl. Qed.
Lemma D_5de3c : decode_any W_5de3c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de40 : bv 32 := 0x04113c23.
Lemma F_5de40 : fetch_word Asan.M.loaded_segments (0x5de90 : word) = Some W_5de40.
Proof. vm_refl. Qed.
Lemma D_5de40 : decode_any W_5de40 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de44 : bv 32 := 0x04813823.
Lemma F_5de44 : fetch_word Asan.M.loaded_segments (0x5de94 : word) = Some W_5de44.
Proof. vm_refl. Qed.
Lemma D_5de44 : decode_any W_5de44 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de48 : bv 32 := 0x04913423.
Lemma F_5de48 : fetch_word Asan.M.loaded_segments (0x5de98 : word) = Some W_5de48.
Proof. vm_refl. Qed.
Lemma D_5de48 : decode_any W_5de48 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de4c : bv 32 := 0x05213023.
Lemma F_5de4c : fetch_word Asan.M.loaded_segments (0x5de9c : word) = Some W_5de4c.
Proof. vm_refl. Qed.
Lemma D_5de4c : decode_any W_5de4c = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de50 : bv 32 := 0x03313c23.
Lemma F_5de50 : fetch_word Asan.M.loaded_segments (0x5dea0 : word) = Some W_5de50.
Proof. vm_refl. Qed.
Lemma D_5de50 : decode_any W_5de50 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de54 : bv 32 := 0x03413823.
Lemma F_5de54 : fetch_word Asan.M.loaded_segments (0x5dea4 : word) = Some W_5de54.
Proof. vm_refl. Qed.
Lemma D_5de54 : decode_any W_5de54 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de58 : bv 32 := 0x03513423.
Lemma F_5de58 : fetch_word Asan.M.loaded_segments (0x5dea8 : word) = Some W_5de58.
Proof. vm_refl. Qed.
Lemma D_5de58 : decode_any W_5de58 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de5c : bv 32 := 0x03613023.
Lemma F_5de5c : fetch_word Asan.M.loaded_segments (0x5deac : word) = Some W_5de5c.
Proof. vm_refl. Qed.
Lemma D_5de5c : decode_any W_5de5c = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de60 : bv 32 := 0x01713c23.
Lemma F_5de60 : fetch_word Asan.M.loaded_segments (0x5deb0 : word) = Some W_5de60.
Proof. vm_refl. Qed.
Lemma D_5de60 : decode_any W_5de60 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de64 : bv 32 := 0x01813823.
Lemma F_5de64 : fetch_word Asan.M.loaded_segments (0x5deb4 : word) = Some W_5de64.
Proof. vm_refl. Qed.
Lemma D_5de64 : decode_any W_5de64 = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de68 : bv 32 := 0x01913423.
Lemma F_5de68 : fetch_word Asan.M.loaded_segments (0x5deb8 : word) = Some W_5de68.
Proof. vm_refl. Qed.
Lemma D_5de68 : decode_any W_5de68 = Some (Store SZ8 2 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de6c : bv 32 := 0x00058413.
Lemma F_5de6c : fetch_word Asan.M.loaded_segments (0x5debc : word) = Some W_5de6c.
Proof. vm_refl. Qed.
Lemma D_5de6c : decode_any W_5de6c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de70 : bv 32 := 0xfff68c13.
Lemma F_5de70 : fetch_word Asan.M.loaded_segments (0x5dec0 : word) = Some W_5de70.
Proof. vm_refl. Qed.
Lemma D_5de70 : decode_any W_5de70 = Some (OpImm ALU_ADD 24 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de74 : bv 32 := 0x0186f5b3.
Lemma F_5de74 : fetch_word Asan.M.loaded_segments (0x5dec4 : word) = Some W_5de74.
Proof. vm_refl. Qed.
Lemma D_5de74 : decode_any W_5de74 = Some (Op ALU_AND 11 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de78 : bv 32 := 0x2c059a63.
Lemma F_5de78 : fetch_word Asan.M.loaded_segments (0x5dec8 : word) = Some W_5de78.
Proof. vm_refl. Qed.
Lemma D_5de78 : decode_any W_5de78 = Some (Branch BC_NE 11 0 724, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de7c : bv 32 := 0x00050493.
Lemma F_5de7c : fetch_word Asan.M.loaded_segments (0x5decc : word) = Some W_5de7c.
Proof. vm_refl. Qed.
Lemma D_5de7c : decode_any W_5de7c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de80 : bv 32 := 0x00053503.
Lemma F_5de80 : fetch_word Asan.M.loaded_segments (0x5ded0 : word) = Some W_5de80.
Proof. vm_refl. Qed.
Lemma D_5de80 : decode_any W_5de80 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de84 : bv 32 := 0xfff50593.
Lemma F_5de84 : fetch_word Asan.M.loaded_segments (0x5ded4 : word) = Some W_5de84.
Proof. vm_refl. Qed.
Lemma D_5de84 : decode_any W_5de84 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de88 : bv 32 := 0x00b575b3.
Lemma F_5de88 : fetch_word Asan.M.loaded_segments (0x5ded8 : word) = Some W_5de88.
Proof. vm_refl. Qed.
Lemma D_5de88 : decode_any W_5de88 = Some (Op ALU_AND 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de8c : bv 32 := 0x2e059063.
Lemma F_5de8c : fetch_word Asan.M.loaded_segments (0x5dedc : word) = Some W_5de8c.
Proof. vm_refl. Qed.
Lemma D_5de8c : decode_any W_5de8c = Some (Branch BC_NE 11 0 736, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de90 : bv 32 := 0x00060993.
Lemma F_5de90 : fetch_word Asan.M.loaded_segments (0x5dee0 : word) = Some W_5de90.
Proof. vm_refl. Qed.
Lemma D_5de90 : decode_any W_5de90 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de94 : bv 32 := 0x00a605b3.
Lemma F_5de94 : fetch_word Asan.M.loaded_segments (0x5dee4 : word) = Some W_5de94.
Proof. vm_refl. Qed.
Lemma D_5de94 : decode_any W_5de94 = Some (Op ALU_ADD 11 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de98 : bv 32 := 0x40a00633.
Lemma F_5de98 : fetch_word Asan.M.loaded_segments (0x5dee8 : word) = Some W_5de98.
Proof. vm_refl. Qed.
Lemma D_5de98 : decode_any W_5de98 = Some (Op ALU_SUB 12 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de9c : bv 32 := 0xfff58593.
Lemma F_5de9c : fetch_word Asan.M.loaded_segments (0x5deec : word) = Some W_5de9c.
Proof. vm_refl. Qed.
Lemma D_5de9c : decode_any W_5de9c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dea0 : bv 32 := 0x00c5f5b3.
Lemma F_5dea0 : fetch_word Asan.M.loaded_segments (0x5def0 : word) = Some W_5dea0.
Proof. vm_refl. Qed.
Lemma D_5dea0 : decode_any W_5dea0 = Some (Op ALU_AND 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dea4 : bv 32 := 0x00d53633.
Lemma F_5dea4 : fetch_word Asan.M.loaded_segments (0x5def4 : word) = Some W_5dea4.
Proof. vm_refl. Qed.
Lemma D_5dea4 : decode_any W_5dea4 = Some (Op ALU_SLTU 12 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dea8 : bv 32 := 0x40c00633.
Lemma F_5dea8 : fetch_word Asan.M.loaded_segments (0x5def8 : word) = Some W_5dea8.
Proof. vm_refl. Qed.
Lemma D_5dea8 : decode_any W_5dea8 = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5deac : bv 32 := 0x00a58533.
Lemma F_5deac : fetch_word Asan.M.loaded_segments (0x5defc : word) = Some W_5deac.
Proof. vm_refl. Qed.
Lemma D_5deac : decode_any W_5deac = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5deb0 : bv 32 := 0x00d67633.
Lemma F_5deb0 : fetch_word Asan.M.loaded_segments (0x5df00 : word) = Some W_5deb0.
Proof. vm_refl. Qed.
Lemma D_5deb0 : decode_any W_5deb0 = Some (Op ALU_AND 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5deb4 : bv 32 := 0x00c50933.
Lemma F_5deb4 : fetch_word Asan.M.loaded_segments (0x5df04 : word) = Some W_5deb4.
Proof. vm_refl. Qed.
Lemma D_5deb4 : decode_any W_5deb4 = Some (Op ALU_ADD 18 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5deb8 : bv 32 := 0x03397463.
Lemma F_5deb8 : fetch_word Asan.M.loaded_segments (0x5df08 : word) = Some W_5deb8.
Proof. vm_refl. Qed.
Lemma D_5deb8 : decode_any W_5deb8 = Some (Branch BC_GEU 18 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dee0 : bv 32 := 0x00068a93.
Lemma F_5dee0 : fetch_word Asan.M.loaded_segments (0x5df30 : word) = Some W_5dee0.
Proof. vm_refl. Qed.
Lemma D_5dee0 : decode_any W_5dee0 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dee4 : bv 32 := 0x000f5517.
Lemma F_5dee4 : fetch_word Asan.M.loaded_segments (0x5df34 : word) = Some W_5dee4.
Proof. vm_refl. Qed.
Lemma D_5dee4 : decode_any W_5dee4 = Some (Auipc 10 245, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dee8 : bv 32 := 0x1ec53503.
Lemma F_5dee8 : fetch_word Asan.M.loaded_segments (0x5df38 : word) = Some W_5dee8.
Proof. vm_refl. Qed.
Lemma D_5dee8 : decode_any W_5dee8 = Some (Load SZ8 true 10 10 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_5deec : bv 32 := 0x00053583.
Lemma F_5deec : fetch_word Asan.M.loaded_segments (0x5df3c : word) = Some W_5deec.
Proof. vm_refl. Qed.
Lemma D_5deec : decode_any W_5deec = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5def0 : bv 32 := 0x00090513.
Lemma F_5def0 : fetch_word Asan.M.loaded_segments (0x5df40 : word) = Some W_5def0.
Proof. vm_refl. Qed.
Lemma D_5def0 : decode_any W_5def0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5def4 : bv 32 := 0x7e4360ef.
Lemma F_5def4 : fetch_word Asan.M.loaded_segments (0x5df44 : word) = Some W_5def4.
Proof. vm_refl. Qed.
Lemma D_5def4 : decode_any W_5def4 = Some (Jal 1 223204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5def8 : bv 32 := 0x22050063.
Lemma F_5def8 : fetch_word Asan.M.loaded_segments (0x5df48 : word) = Some W_5def8.
Proof. vm_refl. Qed.
Lemma D_5def8 : decode_any W_5def8 = Some (Branch BC_EQ 10 0 544, 4%Z).
Proof. vm_refl. Qed.

Definition W_5defc : bv 32 := 0x00050a13.
Lemma F_5defc : fetch_word Asan.M.loaded_segments (0x5df4c : word) = Some W_5defc.
Proof. vm_refl. Qed.
Lemma D_5defc : decode_any W_5defc = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df00 : bv 32 := 0x0004b503.
Lemma F_5df00 : fetch_word Asan.M.loaded_segments (0x5df50 : word) = Some W_5df00.
Proof. vm_refl. Qed.
Lemma D_5df00 : decode_any W_5df00 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df04 : bv 32 := 0xfff50593.
Lemma F_5df04 : fetch_word Asan.M.loaded_segments (0x5df54 : word) = Some W_5df04.
Proof. vm_refl. Qed.
Lemma D_5df04 : decode_any W_5df04 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df08 : bv 32 := 0x0145f5b3.
Lemma F_5df08 : fetch_word Asan.M.loaded_segments (0x5df58 : word) = Some W_5df08.
Proof. vm_refl. Qed.
Lemma D_5df08 : decode_any W_5df08 = Some (Op ALU_AND 11 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df0c : bv 32 := 0x26059863.
Lemma F_5df0c : fetch_word Asan.M.loaded_segments (0x5df5c : word) = Some W_5df0c.
Proof. vm_refl. Qed.
Lemma D_5df0c : decode_any W_5df0c = Some (Branch BC_NE 11 0 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df10 : bv 32 := 0x01490b33.
Lemma F_5df10 : fetch_word Asan.M.loaded_segments (0x5df60 : word) = Some W_5df10.
Proof. vm_refl. Qed.
Lemma D_5df10 : decode_any W_5df10 = Some (Op ALU_ADD 22 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df14 : bv 32 := 0x01450533.
Lemma F_5df14 : fetch_word Asan.M.loaded_segments (0x5df64 : word) = Some W_5df14.
Proof. vm_refl. Qed.
Lemma D_5df14 : decode_any W_5df14 = Some (Op ALU_ADD 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df18 : bv 32 := 0x018575b3.
Lemma F_5df18 : fetch_word Asan.M.loaded_segments (0x5df68 : word) = Some W_5df18.
Proof. vm_refl. Qed.
Lemma D_5df18 : decode_any W_5df18 = Some (Op ALU_AND 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df1c : bv 32 := 0x0015b613.
Lemma F_5df1c : fetch_word Asan.M.loaded_segments (0x5df6c : word) = Some W_5df1c.
Proof. vm_refl. Qed.
Lemma D_5df1c : decode_any W_5df1c = Some (OpImm ALU_SLTU 12 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df20 : bv 32 := 0x40ba85b3.
Lemma F_5df20 : fetch_word Asan.M.loaded_segments (0x5df70 : word) = Some W_5df20.
Proof. vm_refl. Qed.
Lemma D_5df20 : decode_any W_5df20 = Some (Op ALU_SUB 11 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df24 : bv 32 := 0xfff60613.
Lemma F_5df24 : fetch_word Asan.M.loaded_segments (0x5df74 : word) = Some W_5df24.
Proof. vm_refl. Qed.
Lemma D_5df24 : decode_any W_5df24 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df28 : bv 32 := 0x00b675b3.
Lemma F_5df28 : fetch_word Asan.M.loaded_segments (0x5df78 : word) = Some W_5df28.
Proof. vm_refl. Qed.
Lemma D_5df28 : decode_any W_5df28 = Some (Op ALU_AND 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df2c : bv 32 := 0x00a58cb3.
Lemma F_5df2c : fetch_word Asan.M.loaded_segments (0x5df7c : word) = Some W_5df2c.
Proof. vm_refl. Qed.
Lemma D_5df2c : decode_any W_5df2c = Some (Op ALU_ADD 25 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df30 : bv 32 := 0x013c8ab3.
Lemma F_5df30 : fetch_word Asan.M.loaded_segments (0x5df80 : word) = Some W_5df30.
Proof. vm_refl. Qed.
Lemma D_5df30 : decode_any W_5df30 = Some (Op ALU_ADD 21 25 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df34 : bv 32 := 0x007c8513.
Lemma F_5df34 : fetch_word Asan.M.loaded_segments (0x5df84 : word) = Some W_5df34.
Proof. vm_refl. Qed.
Lemma D_5df34 : decode_any W_5df34 = Some (OpImm ALU_ADD 10 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df38 : bv 32 := 0xff8afb93.
Lemma F_5df38 : fetch_word Asan.M.loaded_segments (0x5df88 : word) = Some W_5df38.
Proof. vm_refl. Qed.
Lemma D_5df38 : decode_any W_5df38 = Some (OpImm ALU_AND 23 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df3c : bv 32 := 0xff857513.
Lemma F_5df3c : fetch_word Asan.M.loaded_segments (0x5df8c : word) = Some W_5df3c.
Proof. vm_refl. Qed.
Lemma D_5df3c : decode_any W_5df3c = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df40 : bv 32 := 0x414505b3.
Lemma F_5df40 : fetch_word Asan.M.loaded_segments (0x5df90 : word) = Some W_5df40.
Proof. vm_refl. Qed.
Lemma D_5df40 : decode_any W_5df40 = Some (Op ALU_SUB 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df44 : bv 32 := 0x0fa00613.
Lemma F_5df44 : fetch_word Asan.M.loaded_segments (0x5df94 : word) = Some W_5df44.
Proof. vm_refl. Qed.
Lemma D_5df44 : decode_any W_5df44 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df48 : bv 32 := 0x000a0513.
Lemma F_5df48 : fetch_word Asan.M.loaded_segments (0x5df98 : word) = Some W_5df48.
Proof. vm_refl. Qed.
Lemma D_5df48 : decode_any W_5df48 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df4c : bv 32 := 0x57d230ef.
Lemma F_5df4c : fetch_word Asan.M.loaded_segments (0x5df9c : word) = Some W_5df4c.
Proof. vm_refl. Qed.
Lemma D_5df4c : decode_any W_5df4c = Some (Jal 1 146812, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df50 : bv 32 := 0x417b05b3.
Lemma F_5df50 : fetch_word Asan.M.loaded_segments (0x5dfa0 : word) = Some W_5df50.
Proof. vm_refl. Qed.
Lemma D_5df50 : decode_any W_5df50 = Some (Op ALU_SUB 11 22 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df54 : bv 32 := 0x0fa00613.
Lemma F_5df54 : fetch_word Asan.M.loaded_segments (0x5dfa4 : word) = Some W_5df54.
Proof. vm_refl. Qed.
Lemma D_5df54 : decode_any W_5df54 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df58 : bv 32 := 0x000b8513.
Lemma F_5df58 : fetch_word Asan.M.loaded_segments (0x5dfa8 : word) = Some W_5df58.
Proof. vm_refl. Qed.
Lemma D_5df58 : decode_any W_5df58 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df5c : bv 32 := 0x56d230ef.
Lemma F_5df5c : fetch_word Asan.M.loaded_segments (0x5dfac : word) = Some W_5df5c.
Proof. vm_refl. Qed.
Lemma D_5df5c : decode_any W_5df5c = Some (Jal 1 146796, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df60 : bv 32 := 0x4e12b0ef.
Lemma F_5df60 : fetch_word Asan.M.loaded_segments (0x5dfb0 : word) = Some W_5df60.
Proof. vm_refl. Qed.
Lemma D_5df60 : decode_any W_5df60 = Some (Jal 1 179424, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df64 : bv 32 := 0x04853603.
Lemma F_5df64 : fetch_word Asan.M.loaded_segments (0x5dfb4 : word) = Some W_5df64.
Proof. vm_refl. Qed.
Lemma D_5df64 : decode_any W_5df64 = Some (Load SZ8 true 12 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df68 : bv 32 := 0x05053683.
Lemma F_5df68 : fetch_word Asan.M.loaded_segments (0x5dfb8 : word) = Some W_5df68.
Proof. vm_refl. Qed.
Lemma D_5df68 : decode_any W_5df68 = Some (Load SZ8 true 13 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df6c : bv 32 := 0x018cf733.
Lemma F_5df6c : fetch_word Asan.M.loaded_segments (0x5dfbc : word) = Some W_5df6c.
Proof. vm_refl. Qed.
Lemma D_5df6c : decode_any W_5df6c = Some (Op ALU_AND 14 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df70 : bv 32 := 0x00160613.
Lemma F_5df70 : fetch_word Asan.M.loaded_segments (0x5dfc0 : word) = Some W_5df70.
Proof. vm_refl. Qed.
Lemma D_5df70 : decode_any W_5df70 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df74 : bv 32 := 0x012686b3.
Lemma F_5df74 : fetch_word Asan.M.loaded_segments (0x5dfc4 : word) = Some W_5df74.
Proof. vm_refl. Qed.
Lemma D_5df74 : decode_any W_5df74 = Some (Op ALU_ADD 13 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df78 : bv 32 := 0x04c53423.
Lemma F_5df78 : fetch_word Asan.M.loaded_segments (0x5dfc8 : word) = Some W_5df78.
Proof. vm_refl. Qed.
Lemma D_5df78 : decode_any W_5df78 = Some (Store SZ8 10 12 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df7c : bv 32 := 0x04d53823.
Lemma F_5df7c : fetch_word Asan.M.loaded_segments (0x5dfcc : word) = Some W_5df7c.
Proof. vm_refl. Qed.
Lemma D_5df7c : decode_any W_5df7c = Some (Store SZ8 10 13 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df80 : bv 32 := 0x20071e63.
Lemma F_5df80 : fetch_word Asan.M.loaded_segments (0x5dfd0 : word) = Some W_5df80.
Proof. vm_refl. Qed.
Lemma D_5df80 : decode_any W_5df80 = Some (Branch BC_NE 14 0 540, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df84 : bv 32 := 0x000c8513.
Lemma F_5df84 : fetch_word Asan.M.loaded_segments (0x5dfd4 : word) = Some W_5df84.
Proof. vm_refl. Qed.
Lemma D_5df84 : decode_any W_5df84 = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df88 : bv 32 := 0x0004b583.
Lemma F_5df88 : fetch_word Asan.M.loaded_segments (0x5dfd8 : word) = Some W_5df88.
Proof. vm_refl. Qed.
Lemma D_5df88 : decode_any W_5df88 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df8c : bv 32 := 0xfff58613.
Lemma F_5df8c : fetch_word Asan.M.loaded_segments (0x5dfdc : word) = Some W_5df8c.
Proof. vm_refl. Qed.
Lemma D_5df8c : decode_any W_5df8c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df90 : bv 32 := 0x01967633.
Lemma F_5df90 : fetch_word Asan.M.loaded_segments (0x5dfe0 : word) = Some W_5df90.
Proof. vm_refl. Qed.
Lemma D_5df90 : decode_any W_5df90 = Some (Op ALU_AND 12 12 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df94 : bv 32 := 0x22061463.
Lemma F_5df94 : fetch_word Asan.M.loaded_segments (0x5dfe4 : word) = Some W_5df94.
Proof. vm_refl. Qed.
Lemma D_5df94 : decode_any W_5df94 = Some (Branch BC_NE 12 0 552, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df98 : bv 32 := 0x254ae263.
Lemma F_5df98 : fetch_word Asan.M.loaded_segments (0x5dfe8 : word) = Some W_5df98.
Proof. vm_refl. Qed.
Lemma D_5df98 : decode_any W_5df98 = Some (Branch BC_LTU 21 20 580, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df9c : bv 32 := 0x275b6063.
Lemma F_5df9c : fetch_word Asan.M.loaded_segments (0x5dfec : word) = Some W_5df9c.
Proof. vm_refl. Qed.
Lemma D_5df9c : decode_any W_5df9c = Some (Branch BC_LTU 22 21 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfa0 : bv 32 := 0x40b50ab3.
Lemma F_5dfa0 : fetch_word Asan.M.loaded_segments (0x5dff0 : word) = Some W_5dfa0.
Proof. vm_refl. Qed.
Lemma D_5dfa0 : decode_any W_5dfa0 = Some (Op ALU_SUB 21 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfa4 : bv 32 := 0x014ab023.
Lemma F_5dfa4 : fetch_word Asan.M.loaded_segments (0x5dff4 : word) = Some W_5dfa4.
Proof. vm_refl. Qed.
Lemma D_5dfa4 : decode_any W_5dfa4 = Some (Store SZ8 21 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfa8 : bv 32 := 0x012ab423.
Lemma F_5dfa8 : fetch_word Asan.M.loaded_segments (0x5dff8 : word) = Some W_5dfa8.
Proof. vm_refl. Qed.
Lemma D_5dfa8 : decode_any W_5dfa8 = Some (Store SZ8 21 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfac : bv 32 := 0x013ab823.
Lemma F_5dfac : fetch_word Asan.M.loaded_segments (0x5dffc : word) = Some W_5dfac.
Proof. vm_refl. Qed.
Lemma D_5dfac : decode_any W_5dfac = Some (Store SZ8 21 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfb0 : bv 32 := 0x26090663.
Lemma F_5dfb0 : fetch_word Asan.M.loaded_segments (0x5e000 : word) = Some W_5dfb0.
Proof. vm_refl. Qed.
Lemma D_5dfb0 : decode_any W_5dfb0 = Some (Branch BC_EQ 18 0 620, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfb4 : bv 32 := 0x26848593.
Lemma F_5dfb4 : fetch_word Asan.M.loaded_segments (0x5e004 : word) = Some W_5dfb4.
Proof. vm_refl. Qed.
Lemma D_5dfb4 : decode_any W_5dfb4 = Some (OpImm ALU_ADD 11 9 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfb8 : bv 32 := 0x0ff00613.
Lemma F_5dfb8 : fetch_word Asan.M.loaded_segments (0x5e008 : word) = Some W_5dfb8.
Proof. vm_refl. Qed.
Lemma D_5dfb8 : decode_any W_5dfb8 = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfbc : bv 32 := 0xffc5f693.
Lemma F_5dfbc : fetch_word Asan.M.loaded_segments (0x5e00c : word) = Some W_5dfbc.
Proof. vm_refl. Qed.
Lemma D_5dfbc : decode_any W_5dfbc = Some (OpImm ALU_AND 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc0 : bv 32 := 0x00100713.
Lemma F_5dfc0 : fetch_word Asan.M.loaded_segments (0x5e010 : word) = Some W_5dfc0.
Proof. vm_refl. Qed.
Lemma D_5dfc0 : decode_any W_5dfc0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc4 : bv 32 := 0x1406a7af.
Lemma F_5dfc4 : fetch_word Asan.M.loaded_segments (0x5e014 : word) = Some W_5dfc4.
Proof. vm_refl. Qed.
Lemma D_5dfc4 : decode_any W_5dfc4 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc8 : bv 32 := 0x00070813.
Lemma F_5dfc8 : fetch_word Asan.M.loaded_segments (0x5e018 : word) = Some W_5dfc8.
Proof. vm_refl. Qed.
Lemma D_5dfc8 : decode_any W_5dfc8 = Some (OpImm ALU_ADD 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfcc : bv 32 := 0x0107c833.
Lemma F_5dfcc : fetch_word Asan.M.loaded_segments (0x5e01c : word) = Some W_5dfcc.
Proof. vm_refl. Qed.
Lemma D_5dfcc : decode_any W_5dfcc = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd0 : bv 32 := 0x00c87833.
Lemma F_5dfd0 : fetch_word Asan.M.loaded_segments (0x5e020 : word) = Some W_5dfd0.
Proof. vm_refl. Qed.
Lemma D_5dfd0 : decode_any W_5dfd0 = Some (Op ALU_AND 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd4 : bv 32 := 0x0107c833.
Lemma F_5dfd4 : fetch_word Asan.M.loaded_segments (0x5e024 : word) = Some W_5dfd4.
Proof. vm_refl. Qed.
Lemma D_5dfd4 : decode_any W_5dfd4 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd8 : bv 32 := 0x1906a82f.
Lemma F_5dfd8 : fetch_word Asan.M.loaded_segments (0x5e028 : word) = Some W_5dfd8.
Proof. vm_refl. Qed.
Lemma D_5dfd8 : decode_any W_5dfd8 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfdc : bv 32 := 0xfe0814e3.
Lemma F_5dfdc : fetch_word Asan.M.loaded_segments (0x5e02c : word) = Some W_5dfdc.
Proof. vm_refl. Qed.
Lemma D_5dfdc : decode_any W_5dfdc = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe0 : bv 32 := 0x0ff7f613.
Lemma F_5dfe0 : fetch_word Asan.M.loaded_segments (0x5e030 : word) = Some W_5dfe0.
Proof. vm_refl. Qed.
Lemma D_5dfe0 : decode_any W_5dfe0 = Some (OpImm ALU_AND 12 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe4 : bv 32 := 0x24061c63.
Lemma F_5dfe4 : fetch_word Asan.M.loaded_segments (0x5e034 : word) = Some W_5dfe4.
Proof. vm_refl. Qed.
Lemma D_5dfe4 : decode_any W_5dfe4 = Some (Branch BC_NE 12 0 600, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe8 : bv 32 := 0x0384b683.
Lemma F_5dfe8 : fetch_word Asan.M.loaded_segments (0x5e038 : word) = Some W_5dfe8.
Proof. vm_refl. Qed.
Lemma D_5dfe8 : decode_any W_5dfe8 = Some (Load SZ8 true 13 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfec : bv 32 := 0x0146d593.
Lemma F_5dfec : fetch_word Asan.M.loaded_segments (0x5e03c : word) = Some W_5dfec.
Proof. vm_refl. Qed.
Lemma D_5dfec : decode_any W_5dfec = Some (ShiftImm ALU_SRL 11 13 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff0 : bv 32 := 0x26059463.
Lemma F_5dff0 : fetch_word Asan.M.loaded_segments (0x5e040 : word) = Some W_5dff0.
Proof. vm_refl. Qed.
Lemma D_5dff0 : decode_any W_5dff0 = Some (Branch BC_NE 11 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff4 : bv 32 := 0x00195593.
Lemma F_5dff4 : fetch_word Asan.M.loaded_segments (0x5e044 : word) = Some W_5dff4.
Proof. vm_refl. Qed.
Lemma D_5dff4 : decode_any W_5dff4 = Some (ShiftImm ALU_SRL 11 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff8 : bv 32 := 0x55555637.
Lemma F_5dff8 : fetch_word Asan.M.loaded_segments (0x5e048 : word) = Some W_5dff8.
Proof. vm_refl. Qed.
Lemma D_5dff8 : decode_any W_5dff8 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dffc : bv 32 := 0x33333737.
Lemma F_5dffc : fetch_word Asan.M.loaded_segments (0x5e04c : word) = Some W_5dffc.
Proof. vm_refl. Qed.
Lemma D_5dffc : decode_any W_5dffc = Some (Lui 14 209715, 4%Z).
Proof. vm_refl. Qed.

