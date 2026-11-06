(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8863c : bv 32 := 0xff010113.
Lemma F_8863c : fetch_word AsanUbsan.M.loaded_segments (0x88684 : word) = Some W_8863c.
Proof. vm_refl. Qed.
Lemma D_8863c : decode_any W_8863c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_88640 : bv 32 := 0x00113423.
Lemma F_88640 : fetch_word AsanUbsan.M.loaded_segments (0x88688 : word) = Some W_88640.
Proof. vm_refl. Qed.
Lemma D_88640 : decode_any W_88640 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88644 : bv 32 := 0x00813023.
Lemma F_88644 : fetch_word AsanUbsan.M.loaded_segments (0x8868c : word) = Some W_88644.
Proof. vm_refl. Qed.
Lemma D_88644 : decode_any W_88644 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88648 : bv 32 := 0x000d6517.
Lemma F_88648 : fetch_word AsanUbsan.M.loaded_segments (0x88690 : word) = Some W_88648.
Proof. vm_refl. Qed.
Lemma D_88648 : decode_any W_88648 = Some (Auipc 10 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_8864c : bv 32 := 0x34850413.
Lemma F_8864c : fetch_word AsanUbsan.M.loaded_segments (0x88694 : word) = Some W_8864c.
Proof. vm_refl. Qed.
Lemma D_8864c : decode_any W_8864c = Some (OpImm ALU_ADD 8 10 840, 4%Z).
Proof. vm_refl. Qed.

Definition W_88650 : bv 32 := 0x00040583.
Lemma F_88650 : fetch_word AsanUbsan.M.loaded_segments (0x88698 : word) = Some W_88650.
Proof. vm_refl. Qed.
Lemma D_88650 : decode_any W_88650 = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88654 : bv 32 := 0x00100513.
Lemma F_88654 : fetch_word AsanUbsan.M.loaded_segments (0x8869c : word) = Some W_88654.
Proof. vm_refl. Qed.
Lemma D_88654 : decode_any W_88654 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_88658 : bv 32 := 0x0230000f.
Lemma F_88658 : fetch_word AsanUbsan.M.loaded_segments (0x886a0 : word) = Some W_88658.
Proof. vm_refl. Qed.
Lemma D_88658 : decode_any W_88658 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8865c : bv 32 := 0x00a59a63.
Lemma F_8865c : fetch_word AsanUbsan.M.loaded_segments (0x886a4 : word) = Some W_8865c.
Proof. vm_refl. Qed.
Lemma D_8865c : decode_any W_8865c = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_88660 : bv 32 := 0x00813083.
Lemma F_88660 : fetch_word AsanUbsan.M.loaded_segments (0x886a8 : word) = Some W_88660.
Proof. vm_refl. Qed.
Lemma D_88660 : decode_any W_88660 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88664 : bv 32 := 0x00013403.
Lemma F_88664 : fetch_word AsanUbsan.M.loaded_segments (0x886ac : word) = Some W_88664.
Proof. vm_refl. Qed.
Lemma D_88664 : decode_any W_88664 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88668 : bv 32 := 0x01010113.
Lemma F_88668 : fetch_word AsanUbsan.M.loaded_segments (0x886b0 : word) = Some W_88668.
Proof. vm_refl. Qed.
Lemma D_88668 : decode_any W_88668 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8866c : bv 32 := 0x00008067.
Lemma F_8866c : fetch_word AsanUbsan.M.loaded_segments (0x886b4 : word) = Some W_8866c.
Proof. vm_refl. Qed.
Lemma D_8866c : decode_any W_8866c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88740 : bv 32 := 0xfb010113.
Lemma F_88740 : fetch_word AsanUbsan.M.loaded_segments (0x88788 : word) = Some W_88740.
Proof. vm_refl. Qed.
Lemma D_88740 : decode_any W_88740 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_88744 : bv 32 := 0x04113423.
Lemma F_88744 : fetch_word AsanUbsan.M.loaded_segments (0x8878c : word) = Some W_88744.
Proof. vm_refl. Qed.
Lemma D_88744 : decode_any W_88744 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_88748 : bv 32 := 0x04813023.
Lemma F_88748 : fetch_word AsanUbsan.M.loaded_segments (0x88790 : word) = Some W_88748.
Proof. vm_refl. Qed.
Lemma D_88748 : decode_any W_88748 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8874c : bv 32 := 0x02913c23.
Lemma F_8874c : fetch_word AsanUbsan.M.loaded_segments (0x88794 : word) = Some W_8874c.
Proof. vm_refl. Qed.
Lemma D_8874c : decode_any W_8874c = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_88750 : bv 32 := 0x03213823.
Lemma F_88750 : fetch_word AsanUbsan.M.loaded_segments (0x88798 : word) = Some W_88750.
Proof. vm_refl. Qed.
Lemma D_88750 : decode_any W_88750 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_88754 : bv 32 := 0x03313423.
Lemma F_88754 : fetch_word AsanUbsan.M.loaded_segments (0x8879c : word) = Some W_88754.
Proof. vm_refl. Qed.
Lemma D_88754 : decode_any W_88754 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_88758 : bv 32 := 0x000d6517.
Lemma F_88758 : fetch_word AsanUbsan.M.loaded_segments (0x887a0 : word) = Some W_88758.
Proof. vm_refl. Qed.
Lemma D_88758 : decode_any W_88758 = Some (Auipc 10 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_8875c : bv 32 := 0x23850493.
Lemma F_8875c : fetch_word AsanUbsan.M.loaded_segments (0x887a4 : word) = Some W_8875c.
Proof. vm_refl. Qed.
Lemma D_8875c : decode_any W_8875c = Some (OpImm ALU_ADD 9 10 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_88760 : bv 32 := 0x00048503.
Lemma F_88760 : fetch_word AsanUbsan.M.loaded_segments (0x887a8 : word) = Some W_88760.
Proof. vm_refl. Qed.
Lemma D_88760 : decode_any W_88760 = Some (Load SZ1 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88764 : bv 32 := 0x00100593.
Lemma F_88764 : fetch_word AsanUbsan.M.loaded_segments (0x887ac : word) = Some W_88764.
Proof. vm_refl. Qed.
Lemma D_88764 : decode_any W_88764 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_88768 : bv 32 := 0x0230000f.
Lemma F_88768 : fetch_word AsanUbsan.M.loaded_segments (0x887b0 : word) = Some W_88768.
Proof. vm_refl. Qed.
Lemma D_88768 : decode_any W_88768 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8876c : bv 32 := 0x10b51e63.
Lemma F_8876c : fetch_word AsanUbsan.M.loaded_segments (0x887b4 : word) = Some W_8876c.
Proof. vm_refl. Qed.
Lemma D_8876c : decode_any W_8876c = Some (Branch BC_NE 10 11 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_88770 : bv 32 := 0xbe1fa0ef.
Lemma F_88770 : fetch_word AsanUbsan.M.loaded_segments (0x887b8 : word) = Some W_88770.
Proof. vm_refl. Qed.
Lemma D_88770 : decode_any W_88770 = Some (Jal 1 2075616, 4%Z).
Proof. vm_refl. Qed.

Definition W_88774 : bv 32 := 0x0e051663.
Lemma F_88774 : fetch_word AsanUbsan.M.loaded_segments (0x887bc : word) = Some W_88774.
Proof. vm_refl. Qed.
Lemma D_88774 : decode_any W_88774 = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_88778 : bv 32 := 0xfff88517.
Lemma F_88778 : fetch_word AsanUbsan.M.loaded_segments (0x887c0 : word) = Some W_88778.
Proof. vm_refl. Qed.
Lemma D_88778 : decode_any W_88778 = Some (Auipc 10 1048456, 4%Z).
Proof. vm_refl. Qed.

Definition W_8877c : bv 32 := 0xcd853403.
Lemma F_8877c : fetch_word AsanUbsan.M.loaded_segments (0x887c4 : word) = Some W_8877c.
Proof. vm_refl. Qed.
Lemma D_8877c : decode_any W_8877c = Some (Load SZ8 true 8 10 3288, 4%Z).
Proof. vm_refl. Qed.

Definition W_88780 : bv 32 := 0x02813023.
Lemma F_88780 : fetch_word AsanUbsan.M.loaded_segments (0x887c8 : word) = Some W_88780.
Proof. vm_refl. Qed.
Lemma D_88780 : decode_any W_88780 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_88784 : bv 32 := 0x00813c23.
Lemma F_88784 : fetch_word AsanUbsan.M.loaded_segments (0x887cc : word) = Some W_88784.
Proof. vm_refl. Qed.
Lemma D_88784 : decode_any W_88784 = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_88788 : bv 32 := 0x6b4020ef.
Lemma F_88788 : fetch_word AsanUbsan.M.loaded_segments (0x887d0 : word) = Some W_88788.
Proof. vm_refl. Qed.
Lemma D_88788 : decode_any W_88788 = Some (Jal 1 9908, 4%Z).
Proof. vm_refl. Qed.

Definition W_8878c : bv 32 := 0x08050263.
Lemma F_8878c : fetch_word AsanUbsan.M.loaded_segments (0x887d4 : word) = Some W_8878c.
Proof. vm_refl. Qed.
Lemma D_8878c : decode_any W_8878c = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_88790 : bv 32 := 0x000cc597.
Lemma F_88790 : fetch_word AsanUbsan.M.loaded_segments (0x887d8 : word) = Some W_88790.
Proof. vm_refl. Qed.
Lemma D_88790 : decode_any W_88790 = Some (Auipc 11 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_88794 : bv 32 := 0xd085b903.
Lemma F_88794 : fetch_word AsanUbsan.M.loaded_segments (0x887dc : word) = Some W_88794.
Proof. vm_refl. Qed.
Lemma D_88794 : decode_any W_88794 = Some (Load SZ8 true 18 11 3336, 4%Z).
Proof. vm_refl. Qed.

Definition W_88798 : bv 32 := 0x00093403.
Lemma F_88798 : fetch_word AsanUbsan.M.loaded_segments (0x887e0 : word) = Some W_88798.
Proof. vm_refl. Qed.
Lemma D_88798 : decode_any W_88798 = Some (Load SZ8 true 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8879c : bv 32 := 0x00041c63.
Lemma F_8879c : fetch_word AsanUbsan.M.loaded_segments (0x887e4 : word) = Some W_8879c.
Proof. vm_refl. Qed.
Lemma D_8879c : decode_any W_8879c = Some (Branch BC_NE 8 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_887b4 : bv 32 := 0x04d020ef.
Lemma F_887b4 : fetch_word AsanUbsan.M.loaded_segments (0x887fc : word) = Some W_887b4.
Proof. vm_refl. Qed.
Lemma D_887b4 : decode_any W_887b4 = Some (Jal 1 10316, 4%Z).
Proof. vm_refl. Qed.

Definition W_887b8 : bv 32 := 0x00050613.
Lemma F_887b8 : fetch_word AsanUbsan.M.loaded_segments (0x88800 : word) = Some W_887b8.
Proof. vm_refl. Qed.
Lemma D_887b8 : decode_any W_887b8 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_887bc : bv 32 := 0x00a13c23.
Lemma F_887bc : fetch_word AsanUbsan.M.loaded_segments (0x88804 : word) = Some W_887bc.
Proof. vm_refl. Qed.
Lemma D_887bc : decode_any W_887bc = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_887c0 : bv 32 := 0x01010513.
Lemma F_887c0 : fetch_word AsanUbsan.M.loaded_segments (0x88808 : word) = Some W_887c0.
Proof. vm_refl. Qed.
Lemma D_887c0 : decode_any W_887c0 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_887c4 : bv 32 := 0x40850533.
Lemma F_887c4 : fetch_word AsanUbsan.M.loaded_segments (0x8880c : word) = Some W_887c4.
Proof. vm_refl. Qed.
Lemma D_887c4 : decode_any W_887c4 = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_887c8 : bv 32 := 0x408006b3.
Lemma F_887c8 : fetch_word AsanUbsan.M.loaded_segments (0x88810 : word) = Some W_887c8.
Proof. vm_refl. Qed.
Lemma D_887c8 : decode_any W_887c8 = Some (Op ALU_SUB 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_887cc : bv 32 := 0x00d576b3.
Lemma F_887cc : fetch_word AsanUbsan.M.loaded_segments (0x88814 : word) = Some W_887cc.
Proof. vm_refl. Qed.
Lemma D_887cc : decode_any W_887cc = Some (Op ALU_AND 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_887d0 : bv 32 := 0x02d13023.
Lemma F_887d0 : fetch_word AsanUbsan.M.loaded_segments (0x88818 : word) = Some W_887d0.
Proof. vm_refl. Qed.
Lemma D_887d0 : decode_any W_887d0 = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_887d4 : bv 32 := 0x40d60733.
Lemma F_887d4 : fetch_word AsanUbsan.M.loaded_segments (0x8881c : word) = Some W_887d4.
Proof. vm_refl. Qed.
Lemma D_887d4 : decode_any W_887d4 = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_887d8 : bv 32 := 0x04000537.
Lemma F_887d8 : fetch_word AsanUbsan.M.loaded_segments (0x88820 : word) = Some W_887d8.
Proof. vm_refl. Qed.
Lemma D_887d8 : decode_any W_887d8 = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_887dc : bv 32 := 0x0015051b.
Lemma F_887dc : fetch_word AsanUbsan.M.loaded_segments (0x88824 : word) = Some W_887dc.
Proof. vm_refl. Qed.
Lemma D_887dc : decode_any W_887dc = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_887e0 : bv 32 := 0x06a76263.
Lemma F_887e0 : fetch_word AsanUbsan.M.loaded_segments (0x88828 : word) = Some W_887e0.
Proof. vm_refl. Qed.
Lemma D_887e0 : decode_any W_887e0 = Some (Branch BC_LTU 14 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_88844 : bv 32 := 0x00770713.
Lemma F_88844 : fetch_word AsanUbsan.M.loaded_segments (0x8888c : word) = Some W_88844.
Proof. vm_refl. Qed.
Lemma D_88844 : decode_any W_88844 = Some (OpImm ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_88848 : bv 32 := 0x10000537.
Lemma F_88848 : fetch_word AsanUbsan.M.loaded_segments (0x88890 : word) = Some W_88848.
Proof. vm_refl. Qed.
Lemma D_88848 : decode_any W_88848 = Some (Lui 10 65536, 4%Z).
Proof. vm_refl. Qed.

Definition W_8884c : bv 32 := 0xff85051b.
Lemma F_8884c : fetch_word AsanUbsan.M.loaded_segments (0x88894 : word) = Some W_8884c.
Proof. vm_refl. Qed.
Lemma D_8884c : decode_any W_8884c = Some (OpImm32 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_88850 : bv 32 := 0x00a775b3.
Lemma F_88850 : fetch_word AsanUbsan.M.loaded_segments (0x88898 : word) = Some W_88850.
Proof. vm_refl. Qed.
Lemma D_88850 : decode_any W_88850 = Some (Op ALU_AND 11 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_88854 : bv 32 := 0x00068513.
Lemma F_88854 : fetch_word AsanUbsan.M.loaded_segments (0x8889c : word) = Some W_88854.
Proof. vm_refl. Qed.
Lemma D_88854 : decode_any W_88854 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88858 : bv 32 := 0x00000613.
Lemma F_88858 : fetch_word AsanUbsan.M.loaded_segments (0x888a0 : word) = Some W_88858.
Proof. vm_refl. Qed.
Lemma D_88858 : decode_any W_88858 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8885c : bv 32 := 0x835f90ef.
Lemma F_8885c : fetch_word AsanUbsan.M.loaded_segments (0x888a4 : word) = Some W_8885c.
Proof. vm_refl. Qed.
Lemma D_8885c : decode_any W_8885c = Some (Jal 1 2070580, 4%Z).
Proof. vm_refl. Qed.

Definition W_88860 : bv 32 := 0x5dc020ef.
Lemma F_88860 : fetch_word AsanUbsan.M.loaded_segments (0x888a8 : word) = Some W_88860.
Proof. vm_refl. Qed.
Lemma D_88860 : decode_any W_88860 = Some (Jal 1 9692, 4%Z).
Proof. vm_refl. Qed.

Definition W_88864 : bv 32 := 0x02050263.
Lemma F_88864 : fetch_word AsanUbsan.M.loaded_segments (0x888ac : word) = Some W_88864.
Proof. vm_refl. Qed.
Lemma D_88864 : decode_any W_88864 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_88868 : bv 32 := 0x02850583.
Lemma F_88868 : fetch_word AsanUbsan.M.loaded_segments (0x888b0 : word) = Some W_88868.
Proof. vm_refl. Qed.
Lemma D_88868 : decode_any W_88868 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8886c : bv 32 := 0x00059e63.
Lemma F_8886c : fetch_word AsanUbsan.M.loaded_segments (0x888b4 : word) = Some W_8886c.
Proof. vm_refl. Qed.
Lemma D_8886c : decode_any W_8886c = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_88870 : bv 32 := 0x04853503.
Lemma F_88870 : fetch_word AsanUbsan.M.loaded_segments (0x888b8 : word) = Some W_88870.
Proof. vm_refl. Qed.
Lemma D_88870 : decode_any W_88870 = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_88874 : bv 32 := 0x00253593.
Lemma F_88874 : fetch_word AsanUbsan.M.loaded_segments (0x888bc : word) = Some W_88874.
Proof. vm_refl. Qed.
Lemma D_88874 : decode_any W_88874 = Some (OpImm ALU_SLTU 11 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_88878 : bv 32 := 0xfff58593.
Lemma F_88878 : fetch_word AsanUbsan.M.loaded_segments (0x888c0 : word) = Some W_88878.
Proof. vm_refl. Qed.
Lemma D_88878 : decode_any W_88878 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8887c : bv 32 := 0x00a5f533.
Lemma F_8887c : fetch_word AsanUbsan.M.loaded_segments (0x888c4 : word) = Some W_8887c.
Proof. vm_refl. Qed.
Lemma D_8887c : decode_any W_8887c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_88880 : bv 32 := 0x00050463.
Lemma F_88880 : fetch_word AsanUbsan.M.loaded_segments (0x888c8 : word) = Some W_88880.
Proof. vm_refl. Qed.
Lemma D_88880 : decode_any W_88880 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88884 : bv 32 := 0xc34dc0ef.
Lemma F_88884 : fetch_word AsanUbsan.M.loaded_segments (0x888cc : word) = Some W_88884.
Proof. vm_refl. Qed.
Lemma D_88884 : decode_any W_88884 = Some (Jal 1 1950772, 4%Z).
Proof. vm_refl. Qed.

Definition W_88888 : bv 32 := 0x04813083.
Lemma F_88888 : fetch_word AsanUbsan.M.loaded_segments (0x888d0 : word) = Some W_88888.
Proof. vm_refl. Qed.
Lemma D_88888 : decode_any W_88888 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8888c : bv 32 := 0x04013403.
Lemma F_8888c : fetch_word AsanUbsan.M.loaded_segments (0x888d4 : word) = Some W_8888c.
Proof. vm_refl. Qed.
Lemma D_8888c : decode_any W_8888c = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_88890 : bv 32 := 0x03813483.
Lemma F_88890 : fetch_word AsanUbsan.M.loaded_segments (0x888d8 : word) = Some W_88890.
Proof. vm_refl. Qed.
Lemma D_88890 : decode_any W_88890 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_88894 : bv 32 := 0x03013903.
Lemma F_88894 : fetch_word AsanUbsan.M.loaded_segments (0x888dc : word) = Some W_88894.
Proof. vm_refl. Qed.
Lemma D_88894 : decode_any W_88894 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_88898 : bv 32 := 0x02813983.
Lemma F_88898 : fetch_word AsanUbsan.M.loaded_segments (0x888e0 : word) = Some W_88898.
Proof. vm_refl. Qed.
Lemma D_88898 : decode_any W_88898 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8889c : bv 32 := 0x05010113.
Lemma F_8889c : fetch_word AsanUbsan.M.loaded_segments (0x888e4 : word) = Some W_8889c.
Proof. vm_refl. Qed.
Lemma D_8889c : decode_any W_8889c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_888a0 : bv 32 := 0x00008067.
Lemma F_888a0 : fetch_word AsanUbsan.M.loaded_segments (0x888e8 : word) = Some W_888a0.
Proof. vm_refl. Qed.
Lemma D_888a0 : decode_any W_888a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

