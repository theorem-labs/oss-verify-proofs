(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_80808 : bv 32 := 0xfd010113.
Lemma F_80808 : fetch_word AsanUbsan.M.loaded_segments (0x80808 : word) = Some W_80808.
Proof. vm_refl. Qed.
Lemma D_80808 : decode_any W_80808 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_8080c : bv 32 := 0x02113423.
Lemma F_8080c : fetch_word AsanUbsan.M.loaded_segments (0x8080c : word) = Some W_8080c.
Proof. vm_refl. Qed.
Lemma D_8080c : decode_any W_8080c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80810 : bv 32 := 0x02813023.
Lemma F_80810 : fetch_word AsanUbsan.M.loaded_segments (0x80810 : word) = Some W_80810.
Proof. vm_refl. Qed.
Lemma D_80810 : decode_any W_80810 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80814 : bv 32 := 0x00913c23.
Lemma F_80814 : fetch_word AsanUbsan.M.loaded_segments (0x80814 : word) = Some W_80814.
Proof. vm_refl. Qed.
Lemma D_80814 : decode_any W_80814 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80818 : bv 32 := 0x01213823.
Lemma F_80818 : fetch_word AsanUbsan.M.loaded_segments (0x80818 : word) = Some W_80818.
Proof. vm_refl. Qed.
Lemma D_80818 : decode_any W_80818 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8081c : bv 32 := 0x01313423.
Lemma F_8081c : fetch_word AsanUbsan.M.loaded_segments (0x8081c : word) = Some W_8081c.
Proof. vm_refl. Qed.
Lemma D_8081c : decode_any W_8081c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80820 : bv 32 := 0x02059593.
Lemma F_80820 : fetch_word AsanUbsan.M.loaded_segments (0x80820 : word) = Some W_80820.
Proof. vm_refl. Qed.
Lemma D_80820 : decode_any W_80820 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80824 : bv 32 := 0x00400637.
Lemma F_80824 : fetch_word AsanUbsan.M.loaded_segments (0x80824 : word) = Some W_80824.
Proof. vm_refl. Qed.
Lemma D_80824 : decode_any W_80824 = Some (Lui 12 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80828 : bv 32 := 0x0205d593.
Lemma F_80828 : fetch_word AsanUbsan.M.loaded_segments (0x80828 : word) = Some W_80828.
Proof. vm_refl. Qed.
Lemma D_80828 : decode_any W_80828 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8082c : bv 32 := 0x0106049b.
Lemma F_8082c : fetch_word AsanUbsan.M.loaded_segments (0x8082c : word) = Some W_8082c.
Proof. vm_refl. Qed.
Lemma D_8082c : decode_any W_8082c = Some (OpImm32 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80830 : bv 32 := 0x0086061b.
Lemma F_80830 : fetch_word AsanUbsan.M.loaded_segments (0x80830 : word) = Some W_80830.
Proof. vm_refl. Qed.
Lemma D_80830 : decode_any W_80830 = Some (OpImm32 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80834 : bv 32 := 0x009504b3.
Lemma F_80834 : fetch_word AsanUbsan.M.loaded_segments (0x80834 : word) = Some W_80834.
Proof. vm_refl. Qed.
Lemma D_80834 : decode_any W_80834 = Some (Op ALU_ADD 9 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80838 : bv 32 := 0x00c50433.
Lemma F_80838 : fetch_word AsanUbsan.M.loaded_segments (0x80838 : word) = Some W_80838.
Proof. vm_refl. Qed.
Lemma D_80838 : decode_any W_80838 = Some (Op ALU_ADD 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8083c : bv 32 := 0x00058913.
Lemma F_8083c : fetch_word AsanUbsan.M.loaded_segments (0x8083c : word) = Some W_8083c.
Proof. vm_refl. Qed.
Lemma D_8083c : decode_any W_8083c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80840 : bv 32 := 0x04058e63.
Lemma F_80840 : fetch_word AsanUbsan.M.loaded_segments (0x80840 : word) = Some W_80840.
Proof. vm_refl. Qed.
Lemma D_80840 : decode_any W_80840 = Some (Branch BC_EQ 11 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_80844 : bv 32 := 0x01095593.
Lemma F_80844 : fetch_word AsanUbsan.M.loaded_segments (0x80844 : word) = Some W_80844.
Proof. vm_refl. Qed.
Lemma D_80844 : decode_any W_80844 = Some (ShiftImm ALU_SRL 11 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80848 : bv 32 := 0x00359513.
Lemma F_80848 : fetch_word AsanUbsan.M.loaded_segments (0x80848 : word) = Some W_80848.
Proof. vm_refl. Qed.
Lemma D_80848 : decode_any W_80848 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8084c : bv 32 := 0x00a48533.
Lemma F_8084c : fetch_word AsanUbsan.M.loaded_segments (0x8084c : word) = Some W_8084c.
Proof. vm_refl. Qed.
Lemma D_8084c : decode_any W_8084c = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80850 : bv 32 := 0x00053503.
Lemma F_80850 : fetch_word AsanUbsan.M.loaded_segments (0x80850 : word) = Some W_80850.
Proof. vm_refl. Qed.
Lemma D_80850 : decode_any W_80850 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80854 : bv 32 := 0x02050063.
Lemma F_80854 : fetch_word AsanUbsan.M.loaded_segments (0x80854 : word) = Some W_80854.
Proof. vm_refl. Qed.
Lemma D_80854 : decode_any W_80854 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80858 : bv 32 := 0x03091593.
Lemma F_80858 : fetch_word AsanUbsan.M.loaded_segments (0x80858 : word) = Some W_80858.
Proof. vm_refl. Qed.
Lemma D_80858 : decode_any W_80858 = Some (ShiftImm ALU_SLL 11 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8085c : bv 32 := 0x02c5d593.
Lemma F_8085c : fetch_word AsanUbsan.M.loaded_segments (0x8085c : word) = Some W_8085c.
Proof. vm_refl. Qed.
Lemma D_8085c : decode_any W_8085c = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_80860 : bv 32 := 0x00b50533.
Lemma F_80860 : fetch_word AsanUbsan.M.loaded_segments (0x80860 : word) = Some W_80860.
Proof. vm_refl. Qed.
Lemma D_80860 : decode_any W_80860 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80864 : bv 32 := 0x00053603.
Lemma F_80864 : fetch_word AsanUbsan.M.loaded_segments (0x80864 : word) = Some W_80864.
Proof. vm_refl. Qed.
Lemma D_80864 : decode_any W_80864 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80868 : bv 32 := 0x00856583.
Lemma F_80868 : fetch_word AsanUbsan.M.loaded_segments (0x80868 : word) = Some W_80868.
Proof. vm_refl. Qed.
Lemma D_80868 : decode_any W_80868 = Some (Load SZ4 false 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8086c : bv 32 := 0xfcc718e3.
Lemma F_8086c : fetch_word AsanUbsan.M.loaded_segments (0x8086c : word) = Some W_8086c.
Proof. vm_refl. Qed.
Lemma D_8086c : decode_any W_8086c = Some (Branch BC_NE 14 12 8144, 4%Z).
Proof. vm_refl. Qed.

Definition W_80870 : bv 32 := 0x02c0006f.
Lemma F_80870 : fetch_word AsanUbsan.M.loaded_segments (0x80870 : word) = Some W_80870.
Proof. vm_refl. Qed.
Lemma D_80870 : decode_any W_80870 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_80874 : bv 32 := 0x00040513.
Lemma F_80874 : fetch_word AsanUbsan.M.loaded_segments (0x80874 : word) = Some W_80874.
Proof. vm_refl. Qed.
Lemma D_80874 : decode_any W_80874 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80878 : bv 32 := 0x00070993.
Lemma F_80878 : fetch_word AsanUbsan.M.loaded_segments (0x80878 : word) = Some W_80878.
Proof. vm_refl. Qed.
Lemma D_80878 : decode_any W_80878 = Some (OpImm ALU_ADD 19 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8087c : bv 32 := 0x0d0000ef.
Lemma F_8087c : fetch_word AsanUbsan.M.loaded_segments (0x8087c : word) = Some W_8087c.
Proof. vm_refl. Qed.
Lemma D_8087c : decode_any W_8087c = Some (Jal 1 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_80880 : bv 32 := 0x00098713.
Lemma F_80880 : fetch_word AsanUbsan.M.loaded_segments (0x80880 : word) = Some W_80880.
Proof. vm_refl. Qed.
Lemma D_80880 : decode_any W_80880 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80884 : bv 32 := 0x03091593.
Lemma F_80884 : fetch_word AsanUbsan.M.loaded_segments (0x80884 : word) = Some W_80884.
Proof. vm_refl. Qed.
Lemma D_80884 : decode_any W_80884 = Some (ShiftImm ALU_SLL 11 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80888 : bv 32 := 0x02c5d593.
Lemma F_80888 : fetch_word AsanUbsan.M.loaded_segments (0x80888 : word) = Some W_80888.
Proof. vm_refl. Qed.
Lemma D_80888 : decode_any W_80888 = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8088c : bv 32 := 0x00b50533.
Lemma F_8088c : fetch_word AsanUbsan.M.loaded_segments (0x8088c : word) = Some W_8088c.
Proof. vm_refl. Qed.
Lemma D_8088c : decode_any W_8088c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80890 : bv 32 := 0x00053603.
Lemma F_80890 : fetch_word AsanUbsan.M.loaded_segments (0x80890 : word) = Some W_80890.
Proof. vm_refl. Qed.
Lemma D_80890 : decode_any W_80890 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80894 : bv 32 := 0x00856583.
Lemma F_80894 : fetch_word AsanUbsan.M.loaded_segments (0x80894 : word) = Some W_80894.
Proof. vm_refl. Qed.
Lemma D_80894 : decode_any W_80894 = Some (Load SZ4 false 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80898 : bv 32 := 0xfac992e3.
Lemma F_80898 : fetch_word AsanUbsan.M.loaded_segments (0x80898 : word) = Some W_80898.
Proof. vm_refl. Qed.
Lemma D_80898 : decode_any W_80898 = Some (Branch BC_NE 19 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_8089c : bv 32 := 0x0009051b.
Lemma F_8089c : fetch_word AsanUbsan.M.loaded_segments (0x8089c : word) = Some W_8089c.
Proof. vm_refl. Qed.
Lemma D_8089c : decode_any W_8089c = Some (OpImm32 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a0 : bv 32 := 0x02813083.
Lemma F_808a0 : fetch_word AsanUbsan.M.loaded_segments (0x808a0 : word) = Some W_808a0.
Proof. vm_refl. Qed.
Lemma D_808a0 : decode_any W_808a0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a4 : bv 32 := 0x02013403.
Lemma F_808a4 : fetch_word AsanUbsan.M.loaded_segments (0x808a4 : word) = Some W_808a4.
Proof. vm_refl. Qed.
Lemma D_808a4 : decode_any W_808a4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a8 : bv 32 := 0x01813483.
Lemma F_808a8 : fetch_word AsanUbsan.M.loaded_segments (0x808a8 : word) = Some W_808a8.
Proof. vm_refl. Qed.
Lemma D_808a8 : decode_any W_808a8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_808ac : bv 32 := 0x01013903.
Lemma F_808ac : fetch_word AsanUbsan.M.loaded_segments (0x808ac : word) = Some W_808ac.
Proof. vm_refl. Qed.
Lemma D_808ac : decode_any W_808ac = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b0 : bv 32 := 0x00813983.
Lemma F_808b0 : fetch_word AsanUbsan.M.loaded_segments (0x808b0 : word) = Some W_808b0.
Proof. vm_refl. Qed.
Lemma D_808b0 : decode_any W_808b0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b4 : bv 32 := 0x03010113.
Lemma F_808b4 : fetch_word AsanUbsan.M.loaded_segments (0x808b4 : word) = Some W_808b4.
Proof. vm_refl. Qed.
Lemma D_808b4 : decode_any W_808b4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b8 : bv 32 := 0x00008067.
Lemma F_808b8 : fetch_word AsanUbsan.M.loaded_segments (0x808b8 : word) = Some W_808b8.
Proof. vm_refl. Qed.
Lemma D_808b8 : decode_any W_808b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808bc : bv 32 := 0xfd010113.
Lemma F_808bc : fetch_word AsanUbsan.M.loaded_segments (0x808bc : word) = Some W_808bc.
Proof. vm_refl. Qed.
Lemma D_808bc : decode_any W_808bc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c0 : bv 32 := 0x02113423.
Lemma F_808c0 : fetch_word AsanUbsan.M.loaded_segments (0x808c0 : word) = Some W_808c0.
Proof. vm_refl. Qed.
Lemma D_808c0 : decode_any W_808c0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c4 : bv 32 := 0x02813023.
Lemma F_808c4 : fetch_word AsanUbsan.M.loaded_segments (0x808c4 : word) = Some W_808c4.
Proof. vm_refl. Qed.
Lemma D_808c4 : decode_any W_808c4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c8 : bv 32 := 0x00913c23.
Lemma F_808c8 : fetch_word AsanUbsan.M.loaded_segments (0x808c8 : word) = Some W_808c8.
Proof. vm_refl. Qed.
Lemma D_808c8 : decode_any W_808c8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_808cc : bv 32 := 0x01213823.
Lemma F_808cc : fetch_word AsanUbsan.M.loaded_segments (0x808cc : word) = Some W_808cc.
Proof. vm_refl. Qed.
Lemma D_808cc : decode_any W_808cc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d0 : bv 32 := 0x01313423.
Lemma F_808d0 : fetch_word AsanUbsan.M.loaded_segments (0x808d0 : word) = Some W_808d0.
Proof. vm_refl. Qed.
Lemma D_808d0 : decode_any W_808d0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d4 : bv 32 := 0x00050413.
Lemma F_808d4 : fetch_word AsanUbsan.M.loaded_segments (0x808d4 : word) = Some W_808d4.
Proof. vm_refl. Qed.
Lemma D_808d4 : decode_any W_808d4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d8 : bv 32 := 0x00000593.
Lemma F_808d8 : fetch_word AsanUbsan.M.loaded_segments (0x808d8 : word) = Some W_808d8.
Proof. vm_refl. Qed.
Lemma D_808d8 : decode_any W_808d8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808dc : bv 32 := 0x800004b7.
Lemma F_808dc : fetch_word AsanUbsan.M.loaded_segments (0x808dc : word) = Some W_808dc.
Proof. vm_refl. Qed.
Lemma D_808dc : decode_any W_808dc = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e0 : bv 32 := 0x00900913.
Lemma F_808e0 : fetch_word AsanUbsan.M.loaded_segments (0x808e0 : word) = Some W_808e0.
Proof. vm_refl. Qed.
Lemma D_808e0 : decode_any W_808e0 = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e4 : bv 32 := 0x00052503.
Lemma F_808e4 : fetch_word AsanUbsan.M.loaded_segments (0x808e4 : word) = Some W_808e4.
Proof. vm_refl. Qed.
Lemma D_808e4 : decode_any W_808e4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e8 : bv 32 := 0x00055a63.
Lemma F_808e8 : fetch_word AsanUbsan.M.loaded_segments (0x808e8 : word) = Some W_808e8.
Proof. vm_refl. Qed.
Lemma D_808e8 : decode_any W_808e8 = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_808ec : bv 32 := 0x0280006f.
Lemma F_808ec : fetch_word AsanUbsan.M.loaded_segments (0x808ec : word) = Some W_808ec.
Proof. vm_refl. Qed.
Lemma D_808ec : decode_any W_808ec = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f0 : bv 32 := 0x00098593.
Lemma F_808f0 : fetch_word AsanUbsan.M.loaded_segments (0x808f0 : word) = Some W_808f0.
Proof. vm_refl. Qed.
Lemma D_808f0 : decode_any W_808f0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f4 : bv 32 := 0x00042503.
Lemma F_808f4 : fetch_word AsanUbsan.M.loaded_segments (0x808f4 : word) = Some W_808f4.
Proof. vm_refl. Qed.
Lemma D_808f4 : decode_any W_808f4 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f8 : bv 32 := 0x00054e63.
Lemma F_808f8 : fetch_word AsanUbsan.M.loaded_segments (0x808f8 : word) = Some W_808f8.
Proof. vm_refl. Qed.
Lemma D_808f8 : decode_any W_808f8 = Some (Branch BC_LT 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_808fc : bv 32 := 0x00956633.
Lemma F_808fc : fetch_word AsanUbsan.M.loaded_segments (0x808fc : word) = Some W_808fc.
Proof. vm_refl. Qed.
Lemma D_808fc : decode_any W_808fc = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80900 : bv 32 := 0x160426af.
Lemma F_80900 : fetch_word AsanUbsan.M.loaded_segments (0x80900 : word) = Some W_80900.
Proof. vm_refl. Qed.
Lemma D_80900 : decode_any W_80900 = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80904 : bv 32 := 0x00a69663.
Lemma F_80904 : fetch_word AsanUbsan.M.loaded_segments (0x80904 : word) = Some W_80904.
Proof. vm_refl. Qed.
Lemma D_80904 : decode_any W_80904 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80908 : bv 32 := 0x1ac4272f.
Lemma F_80908 : fetch_word AsanUbsan.M.loaded_segments (0x80908 : word) = Some W_80908.
Proof. vm_refl. Qed.
Lemma D_80908 : decode_any W_80908 = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8090c : bv 32 := 0xfe071ae3.
Lemma F_8090c : fetch_word AsanUbsan.M.loaded_segments (0x8090c : word) = Some W_8090c.
Proof. vm_refl. Qed.
Lemma D_8090c : decode_any W_8090c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_80910 : bv 32 := 0x02a68063.
Lemma F_80910 : fetch_word AsanUbsan.M.loaded_segments (0x80910 : word) = Some W_80910.
Proof. vm_refl. Qed.
Lemma D_80910 : decode_any W_80910 = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80914 : bv 32 := 0x0015899b.
Lemma F_80914 : fetch_word AsanUbsan.M.loaded_segments (0x80914 : word) = Some W_80914.
Proof. vm_refl. Qed.
Lemma D_80914 : decode_any W_80914 = Some (OpImm32 19 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80918 : bv 32 := 0xfcb97ce3.
Lemma F_80918 : fetch_word AsanUbsan.M.loaded_segments (0x80918 : word) = Some W_80918.
Proof. vm_refl. Qed.
Lemma D_80918 : decode_any W_80918 = Some (Branch BC_GEU 18 11 8152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8091c : bv 32 := 0xe24f10ef.
Lemma F_8091c : fetch_word AsanUbsan.M.loaded_segments (0x8091c : word) = Some W_8091c.
Proof. vm_refl. Qed.
Lemma D_8091c : decode_any W_8091c = Some (Jal 1 2037284, 4%Z).
Proof. vm_refl. Qed.

Definition W_80920 : bv 32 := 0x00098593.
Lemma F_80920 : fetch_word AsanUbsan.M.loaded_segments (0x80920 : word) = Some W_80920.
Proof. vm_refl. Qed.
Lemma D_80920 : decode_any W_80920 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80924 : bv 32 := 0x00042503.
Lemma F_80924 : fetch_word AsanUbsan.M.loaded_segments (0x80924 : word) = Some W_80924.
Proof. vm_refl. Qed.
Lemma D_80924 : decode_any W_80924 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80928 : bv 32 := 0xfc055ae3.
Lemma F_80928 : fetch_word AsanUbsan.M.loaded_segments (0x80928 : word) = Some W_80928.
Proof. vm_refl. Qed.
Lemma D_80928 : decode_any W_80928 = Some (Branch BC_GE 10 0 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_8092c : bv 32 := 0xfe9ff06f.
Lemma F_8092c : fetch_word AsanUbsan.M.loaded_segments (0x8092c : word) = Some W_8092c.
Proof. vm_refl. Qed.
Lemma D_8092c : decode_any W_8092c = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

Definition W_80930 : bv 32 := 0x02813083.
Lemma F_80930 : fetch_word AsanUbsan.M.loaded_segments (0x80930 : word) = Some W_80930.
Proof. vm_refl. Qed.
Lemma D_80930 : decode_any W_80930 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80934 : bv 32 := 0x02013403.
Lemma F_80934 : fetch_word AsanUbsan.M.loaded_segments (0x80934 : word) = Some W_80934.
Proof. vm_refl. Qed.
Lemma D_80934 : decode_any W_80934 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80938 : bv 32 := 0x01813483.
Lemma F_80938 : fetch_word AsanUbsan.M.loaded_segments (0x80938 : word) = Some W_80938.
Proof. vm_refl. Qed.
Lemma D_80938 : decode_any W_80938 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8093c : bv 32 := 0x01013903.
Lemma F_8093c : fetch_word AsanUbsan.M.loaded_segments (0x8093c : word) = Some W_8093c.
Proof. vm_refl. Qed.
Lemma D_8093c : decode_any W_8093c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80940 : bv 32 := 0x00813983.
Lemma F_80940 : fetch_word AsanUbsan.M.loaded_segments (0x80940 : word) = Some W_80940.
Proof. vm_refl. Qed.
Lemma D_80940 : decode_any W_80940 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80944 : bv 32 := 0x03010113.
Lemma F_80944 : fetch_word AsanUbsan.M.loaded_segments (0x80944 : word) = Some W_80944.
Proof. vm_refl. Qed.
Lemma D_80944 : decode_any W_80944 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80948 : bv 32 := 0x00008067.
Lemma F_80948 : fetch_word AsanUbsan.M.loaded_segments (0x80948 : word) = Some W_80948.
Proof. vm_refl. Qed.
Lemma D_80948 : decode_any W_80948 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
