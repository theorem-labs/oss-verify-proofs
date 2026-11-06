(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8082c : bv 32 := 0x00008513.
Lemma F_8082c : fetch_word Asan.M.loaded_segments (0x8082c : word) = Some W_8082c.
Proof. vm_refl. Qed.
Lemma D_8082c : decode_any W_8082c = Some (OpImm ALU_ADD 10 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80830 : bv 32 := 0x00008067.
Lemma F_80830 : fetch_word Asan.M.loaded_segments (0x80830 : word) = Some W_80830.
Proof. vm_refl. Qed.
Lemma D_80830 : decode_any W_80830 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80834 : bv 32 := 0xfc010113.
Lemma F_80834 : fetch_word Asan.M.loaded_segments (0x80834 : word) = Some W_80834.
Proof. vm_refl. Qed.
Lemma D_80834 : decode_any W_80834 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80838 : bv 32 := 0x02113c23.
Lemma F_80838 : fetch_word Asan.M.loaded_segments (0x80838 : word) = Some W_80838.
Proof. vm_refl. Qed.
Lemma D_80838 : decode_any W_80838 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8083c : bv 32 := 0x02813823.
Lemma F_8083c : fetch_word Asan.M.loaded_segments (0x8083c : word) = Some W_8083c.
Proof. vm_refl. Qed.
Lemma D_8083c : decode_any W_8083c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80840 : bv 32 := 0x02913423.
Lemma F_80840 : fetch_word Asan.M.loaded_segments (0x80840 : word) = Some W_80840.
Proof. vm_refl. Qed.
Lemma D_80840 : decode_any W_80840 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80844 : bv 32 := 0x03213023.
Lemma F_80844 : fetch_word Asan.M.loaded_segments (0x80844 : word) = Some W_80844.
Proof. vm_refl. Qed.
Lemma D_80844 : decode_any W_80844 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80848 : bv 32 := 0x01313c23.
Lemma F_80848 : fetch_word Asan.M.loaded_segments (0x80848 : word) = Some W_80848.
Proof. vm_refl. Qed.
Lemma D_80848 : decode_any W_80848 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8084c : bv 32 := 0x01413823.
Lemma F_8084c : fetch_word Asan.M.loaded_segments (0x8084c : word) = Some W_8084c.
Proof. vm_refl. Qed.
Lemma D_8084c : decode_any W_8084c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80850 : bv 32 := 0x01513423.
Lemma F_80850 : fetch_word Asan.M.loaded_segments (0x80850 : word) = Some W_80850.
Proof. vm_refl. Qed.
Lemma D_80850 : decode_any W_80850 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80854 : bv 32 := 0x01613023.
Lemma F_80854 : fetch_word Asan.M.loaded_segments (0x80854 : word) = Some W_80854.
Proof. vm_refl. Qed.
Lemma D_80854 : decode_any W_80854 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80858 : bv 32 := 0x00068493.
Lemma F_80858 : fetch_word Asan.M.loaded_segments (0x80858 : word) = Some W_80858.
Proof. vm_refl. Qed.
Lemma D_80858 : decode_any W_80858 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8085c : bv 32 := 0x02079413.
Lemma F_8085c : fetch_word Asan.M.loaded_segments (0x8085c : word) = Some W_8085c.
Proof. vm_refl. Qed.
Lemma D_8085c : decode_any W_8085c = Some (ShiftImm ALU_SLL 8 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80860 : bv 32 := 0x00100693.
Lemma F_80860 : fetch_word Asan.M.loaded_segments (0x80860 : word) = Some W_80860.
Proof. vm_refl. Qed.
Lemma D_80860 : decode_any W_80860 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80864 : bv 32 := 0x02045413.
Lemma F_80864 : fetch_word Asan.M.loaded_segments (0x80864 : word) = Some W_80864.
Proof. vm_refl. Qed.
Lemma D_80864 : decode_any W_80864 = Some (ShiftImm ALU_SRL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80868 : bv 32 := 0x0ef6f863.
Lemma F_80868 : fetch_word Asan.M.loaded_segments (0x80868 : word) = Some W_80868.
Proof. vm_refl. Qed.
Lemma D_80868 : decode_any W_80868 = Some (Branch BC_GEU 13 15 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_8086c : bv 32 := 0x00055697.
Lemma F_8086c : fetch_word Asan.M.loaded_segments (0x8086c : word) = Some W_8086c.
Proof. vm_refl. Qed.
Lemma D_8086c : decode_any W_8086c = Some (Auipc 13 85, 4%Z).
Proof. vm_refl. Qed.

Definition W_80870 : bv 32 := 0x02c6b903.
Lemma F_80870 : fetch_word Asan.M.loaded_segments (0x80870 : word) = Some W_80870.
Proof. vm_refl. Qed.
Lemma D_80870 : decode_any W_80870 = Some (Load SZ8 true 18 13 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_80874 : bv 32 := 0x00093683.
Lemma F_80874 : fetch_word Asan.M.loaded_segments (0x80874 : word) = Some W_80874.
Proof. vm_refl. Qed.
Lemma D_80874 : decode_any W_80874 = Some (Load SZ8 true 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80878 : bv 32 := 0x00068e63.
Lemma F_80878 : fetch_word Asan.M.loaded_segments (0x80878 : word) = Some W_80878.
Proof. vm_refl. Qed.
Lemma D_80878 : decode_any W_80878 = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8087c : bv 32 := 0x00100793.
Lemma F_8087c : fetch_word Asan.M.loaded_segments (0x8087c : word) = Some W_8087c.
Proof. vm_refl. Qed.
Lemma D_8087c : decode_any W_8087c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80880 : bv 32 := 0x00c4d813.
Lemma F_80880 : fetch_word Asan.M.loaded_segments (0x80880 : word) = Some W_80880.
Proof. vm_refl. Qed.
Lemma D_80880 : decode_any W_80880 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80884 : bv 32 := 0x00f52423.
Lemma F_80884 : fetch_word Asan.M.loaded_segments (0x80884 : word) = Some W_80884.
Proof. vm_refl. Qed.
Lemma D_80884 : decode_any W_80884 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80888 : bv 32 := 0x00b53823.
Lemma F_80888 : fetch_word Asan.M.loaded_segments (0x80888 : word) = Some W_80888.
Proof. vm_refl. Qed.
Lemma D_80888 : decode_any W_80888 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8088c : bv 32 := 0x04081463.
Lemma F_8088c : fetch_word Asan.M.loaded_segments (0x8088c : word) = Some W_8088c.
Proof. vm_refl. Qed.
Lemma D_8088c : decode_any W_8088c = Some (Branch BC_NE 16 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_80890 : bv 32 := 0x0a00006f.
Lemma F_80890 : fetch_word Asan.M.loaded_segments (0x80890 : word) = Some W_80890.
Proof. vm_refl. Qed.
Lemma D_80890 : decode_any W_80890 = Some (Jal 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_80894 : bv 32 := 0x00058a13.
Lemma F_80894 : fetch_word Asan.M.loaded_segments (0x80894 : word) = Some W_80894.
Proof. vm_refl. Qed.
Lemma D_80894 : decode_any W_80894 = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80898 : bv 32 := 0x00050993.
Lemma F_80898 : fetch_word Asan.M.loaded_segments (0x80898 : word) = Some W_80898.
Proof. vm_refl. Qed.
Lemma D_80898 : decode_any W_80898 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8089c : bv 32 := 0x00060a93.
Lemma F_8089c : fetch_word Asan.M.loaded_segments (0x8089c : word) = Some W_8089c.
Proof. vm_refl. Qed.
Lemma D_8089c : decode_any W_8089c = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a0 : bv 32 := 0x00070b13.
Lemma F_808a0 : fetch_word Asan.M.loaded_segments (0x808a0 : word) = Some W_808a0.
Proof. vm_refl. Qed.
Lemma D_808a0 : decode_any W_808a0 = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a4 : bv 32 := 0x9e8f20ef.
Lemma F_808a4 : fetch_word Asan.M.loaded_segments (0x808a4 : word) = Some W_808a4.
Proof. vm_refl. Qed.
Lemma D_808a4 : decode_any W_808a4 = Some (Jal 1 2040296, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a8 : bv 32 := 0x000b0713.
Lemma F_808a8 : fetch_word Asan.M.loaded_segments (0x808a8 : word) = Some W_808a8.
Proof. vm_refl. Qed.
Lemma D_808a8 : decode_any W_808a8 = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808ac : bv 32 := 0x000a8613.
Lemma F_808ac : fetch_word Asan.M.loaded_segments (0x808ac : word) = Some W_808ac.
Proof. vm_refl. Qed.
Lemma D_808ac : decode_any W_808ac = Some (OpImm ALU_ADD 12 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b0 : bv 32 := 0x000a0593.
Lemma F_808b0 : fetch_word Asan.M.loaded_segments (0x808b0 : word) = Some W_808b0.
Proof. vm_refl. Qed.
Lemma D_808b0 : decode_any W_808b0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b4 : bv 32 := 0x00050693.
Lemma F_808b4 : fetch_word Asan.M.loaded_segments (0x808b4 : word) = Some W_808b4.
Proof. vm_refl. Qed.
Lemma D_808b4 : decode_any W_808b4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b8 : bv 32 := 0x00098513.
Lemma F_808b8 : fetch_word Asan.M.loaded_segments (0x808b8 : word) = Some W_808b8.
Proof. vm_refl. Qed.
Lemma D_808b8 : decode_any W_808b8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808bc : bv 32 := 0x00d93023.
Lemma F_808bc : fetch_word Asan.M.loaded_segments (0x808bc : word) = Some W_808bc.
Proof. vm_refl. Qed.
Lemma D_808bc : decode_any W_808bc = Some (Store SZ8 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c0 : bv 32 := 0x00100793.
Lemma F_808c0 : fetch_word Asan.M.loaded_segments (0x808c0 : word) = Some W_808c0.
Proof. vm_refl. Qed.
Lemma D_808c0 : decode_any W_808c0 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c4 : bv 32 := 0x00c4d813.
Lemma F_808c4 : fetch_word Asan.M.loaded_segments (0x808c4 : word) = Some W_808c4.
Proof. vm_refl. Qed.
Lemma D_808c4 : decode_any W_808c4 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c8 : bv 32 := 0x00f9a423.
Lemma F_808c8 : fetch_word Asan.M.loaded_segments (0x808c8 : word) = Some W_808c8.
Proof. vm_refl. Qed.
Lemma D_808c8 : decode_any W_808c8 = Some (Store SZ4 19 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_808cc : bv 32 := 0x0149b823.
Lemma F_808cc : fetch_word Asan.M.loaded_segments (0x808cc : word) = Some W_808cc.
Proof. vm_refl. Qed.
Lemma D_808cc : decode_any W_808cc = Some (Store SZ8 19 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d0 : bv 32 := 0x06080063.
Lemma F_808d0 : fetch_word Asan.M.loaded_segments (0x808d0 : word) = Some W_808d0.
Proof. vm_refl. Qed.
Lemma D_808d0 : decode_any W_808d0 = Some (Branch BC_EQ 16 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d4 : bv 32 := 0x0a977263.
Lemma F_808d4 : fetch_word Asan.M.loaded_segments (0x808d4 : word) = Some W_808d4.
Proof. vm_refl. Qed.
Lemma D_808d4 : decode_any W_808d4 = Some (Branch BC_GEU 14 9 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d8 : bv 32 := 0x04c77c63.
Lemma F_808d8 : fetch_word Asan.M.loaded_segments (0x808d8 : word) = Some W_808d8.
Proof. vm_refl. Qed.
Lemma D_808d8 : decode_any W_808d8 = Some (Branch BC_GEU 14 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_808dc : bv 32 := 0xff048493.
Lemma F_808dc : fetch_word Asan.M.loaded_segments (0x808dc : word) = Some W_808dc.
Proof. vm_refl. Qed.
Lemma D_808dc : decode_any W_808dc = Some (OpImm ALU_ADD 9 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e0 : bv 32 := 0x04967863.
Lemma F_808e0 : fetch_word Asan.M.loaded_segments (0x808e0 : word) = Some W_808e0.
Proof. vm_refl. Qed.
Lemma D_808e0 : decode_any W_808e0 = Some (Branch BC_GEU 12 9 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e4 : bv 32 := 0x00767713.
Lemma F_808e4 : fetch_word Asan.M.loaded_segments (0x808e4 : word) = Some W_808e4.
Proof. vm_refl. Qed.
Lemma D_808e4 : decode_any W_808e4 = Some (OpImm ALU_AND 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e8 : bv 32 := 0x04071463.
Lemma F_808e8 : fetch_word Asan.M.loaded_segments (0x808e8 : word) = Some W_808e8.
Proof. vm_refl. Qed.
Lemma D_808e8 : decode_any W_808e8 = Some (Branch BC_NE 14 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_808ec : bv 32 := 0x01050713.
Lemma F_808ec : fetch_word Asan.M.loaded_segments (0x808ec : word) = Some W_808ec.
Proof. vm_refl. Qed.
Lemma D_808ec : decode_any W_808ec = Some (OpImm ALU_ADD 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f0 : bv 32 := 0x00100793.
Lemma F_808f0 : fetch_word Asan.M.loaded_segments (0x808f0 : word) = Some W_808f0.
Proof. vm_refl. Qed.
Lemma D_808f0 : decode_any W_808f0 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f4 : bv 32 := 0x0287fe63.
Lemma F_808f4 : fetch_word Asan.M.loaded_segments (0x808f4 : word) = Some W_808f4.
Proof. vm_refl. Qed.
Lemma D_808f4 : decode_any W_808f4 = Some (Branch BC_GEU 15 8 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f8 : bv 32 := 0xff863803.
Lemma F_808f8 : fetch_word Asan.M.loaded_segments (0x808f8 : word) = Some W_808f8.
Proof. vm_refl. Qed.
Lemma D_808f8 : decode_any W_808f8 = Some (Load SZ8 true 16 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_808fc : bv 32 := 0x02d86a63.
Lemma F_808fc : fetch_word Asan.M.loaded_segments (0x808fc : word) = Some W_808fc.
Proof. vm_refl. Qed.
Lemma D_808fc : decode_any W_808fc = Some (Branch BC_LTU 16 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_80900 : bv 32 := 0x00b80c63.
Lemma F_80900 : fetch_word Asan.M.loaded_segments (0x80900 : word) = Some W_80900.
Proof. vm_refl. Qed.
Lemma D_80900 : decode_any W_80900 = Some (Branch BC_EQ 16 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80904 : bv 32 := 0x00379893.
Lemma F_80904 : fetch_word Asan.M.loaded_segments (0x80904 : word) = Some W_80904.
Proof. vm_refl. Qed.
Lemma D_80904 : decode_any W_80904 = Some (ShiftImm ALU_SLL 17 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80908 : bv 32 := 0x00178793.
Lemma F_80908 : fetch_word Asan.M.loaded_segments (0x80908 : word) = Some W_80908.
Proof. vm_refl. Qed.
Lemma D_80908 : decode_any W_80908 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8090c : bv 32 := 0x011708b3.
Lemma F_8090c : fetch_word Asan.M.loaded_segments (0x8090c : word) = Some W_8090c.
Proof. vm_refl. Qed.
Lemma D_8090c : decode_any W_8090c = Some (Op ALU_ADD 17 14 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_80910 : bv 32 := 0x00f52423.
Lemma F_80910 : fetch_word Asan.M.loaded_segments (0x80910 : word) = Some W_80910.
Proof. vm_refl. Qed.
Lemma D_80910 : decode_any W_80910 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80914 : bv 32 := 0x0108b023.
Lemma F_80914 : fetch_word Asan.M.loaded_segments (0x80914 : word) = Some W_80914.
Proof. vm_refl. Qed.
Lemma D_80914 : decode_any W_80914 = Some (Store SZ8 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80918 : bv 32 := 0xff063803.
Lemma F_80918 : fetch_word Asan.M.loaded_segments (0x80918 : word) = Some W_80918.
Proof. vm_refl. Qed.
Lemma D_80918 : decode_any W_80918 = Some (Load SZ8 true 16 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_8091c : bv 32 := 0x01067a63.
Lemma F_8091c : fetch_word Asan.M.loaded_segments (0x8091c : word) = Some W_8091c.
Proof. vm_refl. Qed.
Lemma D_8091c : decode_any W_8091c = Some (Branch BC_GEU 12 16 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80920 : bv 32 := 0x00987863.
Lemma F_80920 : fetch_word Asan.M.loaded_segments (0x80920 : word) = Some W_80920.
Proof. vm_refl. Qed.
Lemma D_80920 : decode_any W_80920 = Some (Branch BC_GEU 16 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80924 : bv 32 := 0x00787893.
Lemma F_80924 : fetch_word Asan.M.loaded_segments (0x80924 : word) = Some W_80924.
Proof. vm_refl. Qed.
Lemma D_80924 : decode_any W_80924 = Some (OpImm ALU_AND 17 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80928 : bv 32 := 0x00080613.
Lemma F_80928 : fetch_word Asan.M.loaded_segments (0x80928 : word) = Some W_80928.
Proof. vm_refl. Qed.
Lemma D_80928 : decode_any W_80928 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8092c : bv 32 := 0xfc0884e3.
Lemma F_8092c : fetch_word Asan.M.loaded_segments (0x8092c : word) = Some W_8092c.
Proof. vm_refl. Qed.
Lemma D_8092c : decode_any W_8092c = Some (Branch BC_EQ 17 0 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_80930 : bv 32 := 0x03813083.
Lemma F_80930 : fetch_word Asan.M.loaded_segments (0x80930 : word) = Some W_80930.
Proof. vm_refl. Qed.
Lemma D_80930 : decode_any W_80930 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80934 : bv 32 := 0x03013403.
Lemma F_80934 : fetch_word Asan.M.loaded_segments (0x80934 : word) = Some W_80934.
Proof. vm_refl. Qed.
Lemma D_80934 : decode_any W_80934 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80938 : bv 32 := 0x02813483.
Lemma F_80938 : fetch_word Asan.M.loaded_segments (0x80938 : word) = Some W_80938.
Proof. vm_refl. Qed.
Lemma D_80938 : decode_any W_80938 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8093c : bv 32 := 0x02013903.
Lemma F_8093c : fetch_word Asan.M.loaded_segments (0x8093c : word) = Some W_8093c.
Proof. vm_refl. Qed.
Lemma D_8093c : decode_any W_8093c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80940 : bv 32 := 0x01813983.
Lemma F_80940 : fetch_word Asan.M.loaded_segments (0x80940 : word) = Some W_80940.
Proof. vm_refl. Qed.
Lemma D_80940 : decode_any W_80940 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80944 : bv 32 := 0x01013a03.
Lemma F_80944 : fetch_word Asan.M.loaded_segments (0x80944 : word) = Some W_80944.
Proof. vm_refl. Qed.
Lemma D_80944 : decode_any W_80944 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80948 : bv 32 := 0x00813a83.
Lemma F_80948 : fetch_word Asan.M.loaded_segments (0x80948 : word) = Some W_80948.
Proof. vm_refl. Qed.
Lemma D_80948 : decode_any W_80948 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8094c : bv 32 := 0x00013b03.
Lemma F_8094c : fetch_word Asan.M.loaded_segments (0x8094c : word) = Some W_8094c.
Proof. vm_refl. Qed.
Lemma D_8094c : decode_any W_8094c = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80950 : bv 32 := 0x04010113.
Lemma F_80950 : fetch_word Asan.M.loaded_segments (0x80950 : word) = Some W_80950.
Proof. vm_refl. Qed.
Lemma D_80950 : decode_any W_80950 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_80954 : bv 32 := 0x00008067.
Lemma F_80954 : fetch_word Asan.M.loaded_segments (0x80954 : word) = Some W_80954.
Proof. vm_refl. Qed.
Lemma D_80954 : decode_any W_80954 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80958 : bv 32 := 0xfff9e517.
Lemma F_80958 : fetch_word Asan.M.loaded_segments (0x80958 : word) = Some W_80958.
Proof. vm_refl. Qed.
Lemma D_80958 : decode_any W_80958 = Some (Auipc 10 1048478, 4%Z).
Proof. vm_refl. Qed.

Definition W_8095c : bv 32 := 0xfff9b617.
Lemma F_8095c : fetch_word Asan.M.loaded_segments (0x8095c : word) = Some W_8095c.
Proof. vm_refl. Qed.
Lemma D_8095c : decode_any W_8095c = Some (Auipc 12 1048475, 4%Z).
Proof. vm_refl. Qed.

Definition W_80960 : bv 32 := 0x06400593.
Lemma F_80960 : fetch_word Asan.M.loaded_segments (0x80960 : word) = Some W_80960.
Proof. vm_refl. Qed.
Lemma D_80960 : decode_any W_80960 = Some (OpImm ALU_ADD 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_80964 : bv 32 := 0x16650513.
Lemma F_80964 : fetch_word Asan.M.loaded_segments (0x80964 : word) = Some W_80964.
Proof. vm_refl. Qed.
Lemma D_80964 : decode_any W_80964 = Some (OpImm ALU_ADD 10 10 358, 4%Z).
Proof. vm_refl. Qed.

Definition W_80968 : bv 32 := 0x58a60613.
Lemma F_80968 : fetch_word Asan.M.loaded_segments (0x80968 : word) = Some W_80968.
Proof. vm_refl. Qed.
Lemma D_80968 : decode_any W_80968 = Some (OpImm ALU_ADD 12 12 1418, 4%Z).
Proof. vm_refl. Qed.

Definition W_8096c : bv 32 := 0x00200713.
Lemma F_8096c : fetch_word Asan.M.loaded_segments (0x8096c : word) = Some W_8096c.
Proof. vm_refl. Qed.
Lemma D_8096c : decode_any W_8096c = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80970 : bv 32 := 0x00040693.
Lemma F_80970 : fetch_word Asan.M.loaded_segments (0x80970 : word) = Some W_80970.
Proof. vm_refl. Qed.
Lemma D_80970 : decode_any W_80970 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80974 : bv 32 := 0xef4f80ef.
Lemma F_80974 : fetch_word Asan.M.loaded_segments (0x80974 : word) = Some W_80974.
Proof. vm_refl. Qed.
Lemma D_80974 : decode_any W_80974 = Some (Jal 1 2066164, 4%Z).
Proof. vm_refl. Qed.

Definition W_80978 : bv 32 := 0xfff9e517.
Lemma F_80978 : fetch_word Asan.M.loaded_segments (0x80978 : word) = Some W_80978.
Proof. vm_refl. Qed.
Lemma D_80978 : decode_any W_80978 = Some (Auipc 10 1048478, 4%Z).
Proof. vm_refl. Qed.

Definition W_8097c : bv 32 := 0xfff93597.
Lemma F_8097c : fetch_word Asan.M.loaded_segments (0x8097c : word) = Some W_8097c.
Proof. vm_refl. Qed.
Lemma D_8097c : decode_any W_8097c = Some (Auipc 11 1048467, 4%Z).
Proof. vm_refl. Qed.

Definition W_80980 : bv 32 := 0x14650513.
Lemma F_80980 : fetch_word Asan.M.loaded_segments (0x80980 : word) = Some W_80980.
Proof. vm_refl. Qed.
Lemma D_80980 : decode_any W_80980 = Some (OpImm ALU_ADD 10 10 326, 4%Z).
Proof. vm_refl. Qed.

Definition W_80984 : bv 32 := 0x6e458613.
Lemma F_80984 : fetch_word Asan.M.loaded_segments (0x80984 : word) = Some W_80984.
Proof. vm_refl. Qed.
Lemma D_80984 : decode_any W_80984 = Some (OpImm ALU_ADD 12 11 1764, 4%Z).
Proof. vm_refl. Qed.

Definition W_80988 : bv 32 := 0x04e00593.
Lemma F_80988 : fetch_word Asan.M.loaded_segments (0x80988 : word) = Some W_80988.
Proof. vm_refl. Qed.
Lemma D_80988 : decode_any W_80988 = Some (OpImm ALU_ADD 11 0 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_8098c : bv 32 := 0x00048693.
Lemma F_8098c : fetch_word Asan.M.loaded_segments (0x8098c : word) = Some W_8098c.
Proof. vm_refl. Qed.
Lemma D_8098c : decode_any W_8098c = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80990 : bv 32 := 0xed8f80ef.
Lemma F_80990 : fetch_word Asan.M.loaded_segments (0x80990 : word) = Some W_80990.
Proof. vm_refl. Qed.
Lemma D_80990 : decode_any W_80990 = Some (Jal 1 2066136, 4%Z).
Proof. vm_refl. Qed.
