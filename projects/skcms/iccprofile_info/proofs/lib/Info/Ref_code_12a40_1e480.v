(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
Unset Nia Cache.
Unset Lia Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_12a40 : bv 32 := 0x0040006f.
Lemma F_12a40 : fetch_word Plain.M.loaded_segments (0x12a40 : word) = Some W_12a40.
Proof. vm_refl. Qed.
Lemma D_12a40 : decode_any W_12a40 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a44 : bv 32 := 0x0000e517.
Lemma F_12a44 : fetch_word Plain.M.loaded_segments (0x12a44 : word) = Some W_12a44.
Proof. vm_refl. Qed.
Lemma D_12a44 : decode_any W_12a44 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a48 : bv 32 := 0xc3450513.
Lemma F_12a48 : fetch_word Plain.M.loaded_segments (0x12a48 : word) = Some W_12a48.
Proof. vm_refl. Qed.
Lemma D_12a48 : decode_any W_12a48 = Some (OpImm ALU_ADD 10 10 3124, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a4c : bv 32 := 0x00053503.
Lemma F_12a4c : fetch_word Plain.M.loaded_segments (0x12a4c : word) = Some W_12a4c.
Proof. vm_refl. Qed.
Lemma D_12a4c : decode_any W_12a4c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a50 : bv 32 := 0x6f5030ef.
Lemma F_12a50 : fetch_word Plain.M.loaded_segments (0x12a50 : word) = Some W_12a50.
Proof. vm_refl. Qed.
Lemma D_12a50 : decode_any W_12a50 = Some (Jal 1 16116, 4%Z).
Proof. vm_refl. Qed.

Definition W_12a54 : bv 32 := 0x0040006f.
Lemma F_12a54 : fetch_word Plain.M.loaded_segments (0x12a54 : word) = Some W_12a54.
Proof. vm_refl. Qed.
Lemma D_12a54 : decode_any W_12a54 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_12eb0 : bv 32 := 0x0001e517.
Lemma F_12eb0 : fetch_word Plain.M.loaded_segments (0x12eb0 : word) = Some W_12eb0.
Proof. vm_refl. Qed.
Lemma D_12eb0 : decode_any W_12eb0 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_12eb4 : bv 32 := 0xa3454503.
Lemma F_12eb4 : fetch_word Plain.M.loaded_segments (0x12eb4 : word) = Some W_12eb4.
Proof. vm_refl. Qed.
Lemma D_12eb4 : decode_any W_12eb4 = Some (Load SZ1 false 10 10 2612, 4%Z).
Proof. vm_refl. Qed.

Definition W_12eb8 : bv 32 := 0x00051463.
Lemma F_12eb8 : fetch_word Plain.M.loaded_segments (0x12eb8 : word) = Some W_12eb8.
Proof. vm_refl. Qed.
Lemma D_12eb8 : decode_any W_12eb8 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ebc : bv 32 := 0x00008067.
Lemma F_12ebc : fetch_word Plain.M.loaded_segments (0x12ebc : word) = Some W_12ebc.
Proof. vm_refl. Qed.
Lemma D_12ebc : decode_any W_12ebc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1687c : bv 32 := 0xfd010113.
Lemma F_1687c : fetch_word Plain.M.loaded_segments (0x1687c : word) = Some W_1687c.
Proof. vm_refl. Qed.
Lemma D_1687c : decode_any W_1687c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_16880 : bv 32 := 0x02113423.
Lemma F_16880 : fetch_word Plain.M.loaded_segments (0x16880 : word) = Some W_16880.
Proof. vm_refl. Qed.
Lemma D_16880 : decode_any W_16880 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16884 : bv 32 := 0x02813023.
Lemma F_16884 : fetch_word Plain.M.loaded_segments (0x16884 : word) = Some W_16884.
Proof. vm_refl. Qed.
Lemma D_16884 : decode_any W_16884 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16888 : bv 32 := 0x00913c23.
Lemma F_16888 : fetch_word Plain.M.loaded_segments (0x16888 : word) = Some W_16888.
Proof. vm_refl. Qed.
Lemma D_16888 : decode_any W_16888 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1688c : bv 32 := 0x01213823.
Lemma F_1688c : fetch_word Plain.M.loaded_segments (0x1688c : word) = Some W_1688c.
Proof. vm_refl. Qed.
Lemma D_1688c : decode_any W_1688c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16890 : bv 32 := 0x01313423.
Lemma F_16890 : fetch_word Plain.M.loaded_segments (0x16890 : word) = Some W_16890.
Proof. vm_refl. Qed.
Lemma D_16890 : decode_any W_16890 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16894 : bv 32 := 0x0003a517.
Lemma F_16894 : fetch_word Plain.M.loaded_segments (0x16894 : word) = Some W_16894.
Proof. vm_refl. Qed.
Lemma D_16894 : decode_any W_16894 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_16898 : bv 32 := 0x19c50913.
Lemma F_16898 : fetch_word Plain.M.loaded_segments (0x16898 : word) = Some W_16898.
Proof. vm_refl. Qed.
Lemma D_16898 : decode_any W_16898 = Some (OpImm ALU_ADD 18 10 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_1689c : bv 32 := 0x00490413.
Lemma F_1689c : fetch_word Plain.M.loaded_segments (0x1689c : word) = Some W_1689c.
Proof. vm_refl. Qed.
Lemma D_1689c : decode_any W_1689c = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_168a0 : bv 32 := 0x00040513.
Lemma F_168a0 : fetch_word Plain.M.loaded_segments (0x168a0 : word) = Some W_168a0.
Proof. vm_refl. Qed.
Lemma D_168a0 : decode_any W_168a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_168a4 : bv 32 := 0x149070ef.
Lemma F_168a4 : fetch_word Plain.M.loaded_segments (0x168a4 : word) = Some W_168a4.
Proof. vm_refl. Qed.
Lemma D_168a4 : decode_any W_168a4 = Some (Jal 1 31048, 4%Z).
Proof. vm_refl. Qed.

Definition W_168a8 : bv 32 := 0x01093503.
Lemma F_168a8 : fetch_word Plain.M.loaded_segments (0x168a8 : word) = Some W_168a8.
Proof. vm_refl. Qed.
Lemma D_168a8 : decode_any W_168a8 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_168ac : bv 32 := 0x06050863.
Lemma F_168ac : fetch_word Plain.M.loaded_segments (0x168ac : word) = Some W_168ac.
Proof. vm_refl. Qed.
Lemma D_168ac : decode_any W_168ac = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_168b0 : bv 32 := 0x00892583.
Lemma F_168b0 : fetch_word Plain.M.loaded_segments (0x168b0 : word) = Some W_168b0.
Proof. vm_refl. Qed.
Lemma D_168b0 : decode_any W_168b0 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_168b4 : bv 32 := 0x0180006f.
Lemma F_168b4 : fetch_word Plain.M.loaded_segments (0x168b4 : word) = Some W_168b4.
Proof. vm_refl. Qed.
Lemma D_168b4 : decode_any W_168b4 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_168b8 : bv 32 := 0x00053503.
Lemma F_168b8 : fetch_word Plain.M.loaded_segments (0x168b8 : word) = Some W_168b8.
Proof. vm_refl. Qed.
Lemma D_168b8 : decode_any W_168b8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_168bc : bv 32 := 0x02000593.
Lemma F_168bc : fetch_word Plain.M.loaded_segments (0x168bc : word) = Some W_168bc.
Proof. vm_refl. Qed.
Lemma D_168bc : decode_any W_168bc = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_168c0 : bv 32 := 0x00b92423.
Lemma F_168c0 : fetch_word Plain.M.loaded_segments (0x168c0 : word) = Some W_168c0.
Proof. vm_refl. Qed.
Lemma D_168c0 : decode_any W_168c0 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_168c4 : bv 32 := 0x00a93823.
Lemma F_168c4 : fetch_word Plain.M.loaded_segments (0x168c4 : word) = Some W_168c4.
Proof. vm_refl. Qed.
Lemma D_168c4 : decode_any W_168c4 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_168c8 : bv 32 := 0x04050a63.
Lemma F_168c8 : fetch_word Plain.M.loaded_segments (0x168c8 : word) = Some W_168c8.
Proof. vm_refl. Qed.
Lemma D_168c8 : decode_any W_168c8 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_168cc : bv 32 := 0xfff5861b.
Lemma F_168cc : fetch_word Plain.M.loaded_segments (0x168cc : word) = Some W_168cc.
Proof. vm_refl. Qed.
Lemma D_168cc : decode_any W_168cc = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_168d0 : bv 32 := 0x00c92423.
Lemma F_168d0 : fetch_word Plain.M.loaded_segments (0x168d0 : word) = Some W_168d0.
Proof. vm_refl. Qed.
Lemma D_168d0 : decode_any W_168d0 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_168d4 : bv 32 := 0xfeb052e3.
Lemma F_168d4 : fetch_word Plain.M.loaded_segments (0x168d4 : word) = Some W_168d4.
Proof. vm_refl. Qed.
Lemma D_168d4 : decode_any W_168d4 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_168d8 : bv 32 := 0x01093503.
Lemma F_168d8 : fetch_word Plain.M.loaded_segments (0x168d8 : word) = Some W_168d8.
Proof. vm_refl. Qed.
Lemma D_168d8 : decode_any W_168d8 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_168dc : bv 32 := 0x00361613.
Lemma F_168dc : fetch_word Plain.M.loaded_segments (0x168dc : word) = Some W_168dc.
Proof. vm_refl. Qed.
Lemma D_168dc : decode_any W_168dc = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_168e0 : bv 32 := 0x00c50533.
Lemma F_168e0 : fetch_word Plain.M.loaded_segments (0x168e0 : word) = Some W_168e0.
Proof. vm_refl. Qed.
Lemma D_168e0 : decode_any W_168e0 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_168e4 : bv 32 := 0x00853983.
Lemma F_168e4 : fetch_word Plain.M.loaded_segments (0x168e4 : word) = Some W_168e4.
Proof. vm_refl. Qed.
Lemma D_168e4 : decode_any W_168e4 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_168e8 : bv 32 := 0x10853483.
Lemma F_168e8 : fetch_word Plain.M.loaded_segments (0x168e8 : word) = Some W_168e8.
Proof. vm_refl. Qed.
Lemma D_168e8 : decode_any W_168e8 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_168ec : bv 32 := 0x00040513.
Lemma F_168ec : fetch_word Plain.M.loaded_segments (0x168ec : word) = Some W_168ec.
Proof. vm_refl. Qed.
Lemma D_168ec : decode_any W_168ec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_168f0 : bv 32 := 0x385070ef.
Lemma F_168f0 : fetch_word Plain.M.loaded_segments (0x168f0 : word) = Some W_168f0.
Proof. vm_refl. Qed.
Lemma D_168f0 : decode_any W_168f0 = Some (Jal 1 31620, 4%Z).
Proof. vm_refl. Qed.

Definition W_168f4 : bv 32 := 0x00048513.
Lemma F_168f4 : fetch_word Plain.M.loaded_segments (0x168f4 : word) = Some W_168f4.
Proof. vm_refl. Qed.
Lemma D_168f4 : decode_any W_168f4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_168f8 : bv 32 := 0x000980e7.
Lemma F_168f8 : fetch_word Plain.M.loaded_segments (0x168f8 : word) = Some W_168f8.
Proof. vm_refl. Qed.
Lemma D_168f8 : decode_any W_168f8 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_168fc : bv 32 := 0x00040513.
Lemma F_168fc : fetch_word Plain.M.loaded_segments (0x168fc : word) = Some W_168fc.
Proof. vm_refl. Qed.
Lemma D_168fc : decode_any W_168fc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16900 : bv 32 := 0x0ed070ef.
Lemma F_16900 : fetch_word Plain.M.loaded_segments (0x16900 : word) = Some W_16900.
Proof. vm_refl. Qed.
Lemma D_16900 : decode_any W_16900 = Some (Jal 1 30956, 4%Z).
Proof. vm_refl. Qed.

Definition W_16904 : bv 32 := 0x00892503.
Lemma F_16904 : fetch_word Plain.M.loaded_segments (0x16904 : word) = Some W_16904.
Proof. vm_refl. Qed.
Lemma D_16904 : decode_any W_16904 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16908 : bv 32 := 0xfff5061b.
Lemma F_16908 : fetch_word Plain.M.loaded_segments (0x16908 : word) = Some W_16908.
Proof. vm_refl. Qed.
Lemma D_16908 : decode_any W_16908 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1690c : bv 32 := 0x00c92423.
Lemma F_1690c : fetch_word Plain.M.loaded_segments (0x1690c : word) = Some W_1690c.
Proof. vm_refl. Qed.
Lemma D_1690c : decode_any W_1690c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16910 : bv 32 := 0xfca044e3.
Lemma F_16910 : fetch_word Plain.M.loaded_segments (0x16910 : word) = Some W_16910.
Proof. vm_refl. Qed.
Lemma D_16910 : decode_any W_16910 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_16914 : bv 32 := 0x01093503.
Lemma F_16914 : fetch_word Plain.M.loaded_segments (0x16914 : word) = Some W_16914.
Proof. vm_refl. Qed.
Lemma D_16914 : decode_any W_16914 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16918 : bv 32 := 0xfa1ff06f.
Lemma F_16918 : fetch_word Plain.M.loaded_segments (0x16918 : word) = Some W_16918.
Proof. vm_refl. Qed.
Lemma D_16918 : decode_any W_16918 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_1691c : bv 32 := 0x00100513.
Lemma F_1691c : fetch_word Plain.M.loaded_segments (0x1691c : word) = Some W_1691c.
Proof. vm_refl. Qed.
Lemma D_1691c : decode_any W_1691c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16920 : bv 32 := 0x00a90023.
Lemma F_16920 : fetch_word Plain.M.loaded_segments (0x16920 : word) = Some W_16920.
Proof. vm_refl. Qed.
Lemma D_16920 : decode_any W_16920 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16924 : bv 32 := 0x00040513.
Lemma F_16924 : fetch_word Plain.M.loaded_segments (0x16924 : word) = Some W_16924.
Proof. vm_refl. Qed.
Lemma D_16924 : decode_any W_16924 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16928 : bv 32 := 0x02813083.
Lemma F_16928 : fetch_word Plain.M.loaded_segments (0x16928 : word) = Some W_16928.
Proof. vm_refl. Qed.
Lemma D_16928 : decode_any W_16928 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1692c : bv 32 := 0x02013403.
Lemma F_1692c : fetch_word Plain.M.loaded_segments (0x1692c : word) = Some W_1692c.
Proof. vm_refl. Qed.
Lemma D_1692c : decode_any W_1692c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16930 : bv 32 := 0x01813483.
Lemma F_16930 : fetch_word Plain.M.loaded_segments (0x16930 : word) = Some W_16930.
Proof. vm_refl. Qed.
Lemma D_16930 : decode_any W_16930 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16934 : bv 32 := 0x01013903.
Lemma F_16934 : fetch_word Plain.M.loaded_segments (0x16934 : word) = Some W_16934.
Proof. vm_refl. Qed.
Lemma D_16934 : decode_any W_16934 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16938 : bv 32 := 0x00813983.
Lemma F_16938 : fetch_word Plain.M.loaded_segments (0x16938 : word) = Some W_16938.
Proof. vm_refl. Qed.
Lemma D_16938 : decode_any W_16938 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1693c : bv 32 := 0x03010113.
Lemma F_1693c : fetch_word Plain.M.loaded_segments (0x1693c : word) = Some W_1693c.
Proof. vm_refl. Qed.
Lemma D_1693c : decode_any W_1693c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_16940 : bv 32 := 0x3350706f.
Lemma F_16940 : fetch_word Plain.M.loaded_segments (0x16940 : word) = Some W_16940.
Proof. vm_refl. Qed.
Lemma D_16940 : decode_any W_16940 = Some (Jal 0 31540, 4%Z).
Proof. vm_refl. Qed.

Definition W_16944 : bv 32 := 0x00008067.
Lemma F_16944 : fetch_word Plain.M.loaded_segments (0x16944 : word) = Some W_16944.
Proof. vm_refl. Qed.
Lemma D_16944 : decode_any W_16944 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16a0c : bv 32 := 0x00050067.
Lemma F_16a0c : fetch_word Plain.M.loaded_segments (0x16a0c : word) = Some W_16a0c.
Proof. vm_refl. Qed.
Lemma D_16a0c : decode_any W_16a0c = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1e474 : bv 32 := 0x00052583.
Lemma F_1e474 : fetch_word Plain.M.loaded_segments (0x1e474 : word) = Some W_1e474.
Proof. vm_refl. Qed.
Lemma D_1e474 : decode_any W_1e474 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1e478 : bv 32 := 0x0005c463.
Lemma F_1e478 : fetch_word Plain.M.loaded_segments (0x1e478 : word) = Some W_1e478.
Proof. vm_refl. Qed.
Lemma D_1e478 : decode_any W_1e478 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1e47c : bv 32 := 0x00008067.
Lemma F_1e47c : fetch_word Plain.M.loaded_segments (0x1e47c : word) = Some W_1e47c.
Proof. vm_refl. Qed.
Lemma D_1e47c : decode_any W_1e47c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
