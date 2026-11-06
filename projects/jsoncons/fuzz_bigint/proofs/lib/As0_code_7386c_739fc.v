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

Definition W_7386c : bv 32 := 0x00060693.
Lemma F_7386c : fetch_word Asan.M.loaded_segments (0x7386c : word) = Some W_7386c.
Proof. vm_refl. Qed.
Lemma D_7386c : decode_any W_7386c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73870 : bv 32 := 0x00000613.
Lemma F_73870 : fetch_word Asan.M.loaded_segments (0x73870 : word) = Some W_73870.
Proof. vm_refl. Qed.
Lemma D_73870 : decode_any W_73870 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73874 : bv 32 := 0x0040006f.
Lemma F_73874 : fetch_word Asan.M.loaded_segments (0x73874 : word) = Some W_73874.
Proof. vm_refl. Qed.
Lemma D_73874 : decode_any W_73874 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_73878 : bv 32 := 0xfa010113.
Lemma F_73878 : fetch_word Asan.M.loaded_segments (0x73878 : word) = Some W_73878.
Proof. vm_refl. Qed.
Lemma D_73878 : decode_any W_73878 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7387c : bv 32 := 0x04113c23.
Lemma F_7387c : fetch_word Asan.M.loaded_segments (0x7387c : word) = Some W_7387c.
Proof. vm_refl. Qed.
Lemma D_7387c : decode_any W_7387c = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_73880 : bv 32 := 0x04813823.
Lemma F_73880 : fetch_word Asan.M.loaded_segments (0x73880 : word) = Some W_73880.
Proof. vm_refl. Qed.
Lemma D_73880 : decode_any W_73880 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_73884 : bv 32 := 0x04913423.
Lemma F_73884 : fetch_word Asan.M.loaded_segments (0x73884 : word) = Some W_73884.
Proof. vm_refl. Qed.
Lemma D_73884 : decode_any W_73884 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_73888 : bv 32 := 0x05213023.
Lemma F_73888 : fetch_word Asan.M.loaded_segments (0x73888 : word) = Some W_73888.
Proof. vm_refl. Qed.
Lemma D_73888 : decode_any W_73888 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7388c : bv 32 := 0x03313c23.
Lemma F_7388c : fetch_word Asan.M.loaded_segments (0x7388c : word) = Some W_7388c.
Proof. vm_refl. Qed.
Lemma D_7388c : decode_any W_7388c = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_73890 : bv 32 := 0x03413823.
Lemma F_73890 : fetch_word Asan.M.loaded_segments (0x73890 : word) = Some W_73890.
Proof. vm_refl. Qed.
Lemma D_73890 : decode_any W_73890 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_73894 : bv 32 := 0x00068993.
Lemma F_73894 : fetch_word Asan.M.loaded_segments (0x73894 : word) = Some W_73894.
Proof. vm_refl. Qed.
Lemma D_73894 : decode_any W_73894 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73898 : bv 32 := 0x00060493.
Lemma F_73898 : fetch_word Asan.M.loaded_segments (0x73898 : word) = Some W_73898.
Proof. vm_refl. Qed.
Lemma D_73898 : decode_any W_73898 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7389c : bv 32 := 0x00058413.
Lemma F_7389c : fetch_word Asan.M.loaded_segments (0x7389c : word) = Some W_7389c.
Proof. vm_refl. Qed.
Lemma D_7389c : decode_any W_7389c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_738a0 : bv 32 := 0x00062597.
Lemma F_738a0 : fetch_word Asan.M.loaded_segments (0x738a0 : word) = Some W_738a0.
Proof. vm_refl. Qed.
Lemma D_738a0 : decode_any W_738a0 = Some (Auipc 11 98, 4%Z).
Proof. vm_refl. Qed.

Definition W_738a4 : bv 32 := 0xff85ba03.
Lemma F_738a4 : fetch_word Asan.M.loaded_segments (0x738a4 : word) = Some W_738a4.
Proof. vm_refl. Qed.
Lemma D_738a4 : decode_any W_738a4 = Some (Load SZ8 true 20 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_738a8 : bv 32 := 0x000a3583.
Lemma F_738a8 : fetch_word Asan.M.loaded_segments (0x738a8 : word) = Some W_738a8.
Proof. vm_refl. Qed.
Lemma D_738a8 : decode_any W_738a8 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_738ac : bv 32 := 0x00050913.
Lemma F_738ac : fetch_word Asan.M.loaded_segments (0x738ac : word) = Some W_738ac.
Proof. vm_refl. Qed.
Lemma D_738ac : decode_any W_738ac = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_738b0 : bv 32 := 0x00059863.
Lemma F_738b0 : fetch_word Asan.M.loaded_segments (0x738b0 : word) = Some W_738b0.
Proof. vm_refl. Qed.
Lemma D_738b0 : decode_any W_738b0 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_738b4 : bv 32 := 0x9d8ff0ef.
Lemma F_738b4 : fetch_word Asan.M.loaded_segments (0x738b4 : word) = Some W_738b4.
Proof. vm_refl. Qed.
Lemma D_738b4 : decode_any W_738b4 = Some (Jal 1 2093528, 4%Z).
Proof. vm_refl. Qed.

Definition W_738b8 : bv 32 := 0x00050593.
Lemma F_738b8 : fetch_word Asan.M.loaded_segments (0x738b8 : word) = Some W_738b8.
Proof. vm_refl. Qed.
Lemma D_738b8 : decode_any W_738b8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_738bc : bv 32 := 0x00aa3023.
Lemma F_738bc : fetch_word Asan.M.loaded_segments (0x738bc : word) = Some W_738bc.
Proof. vm_refl. Qed.
Lemma D_738bc : decode_any W_738bc = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_738c0 : bv 32 := 0xfff58513.
Lemma F_738c0 : fetch_word Asan.M.loaded_segments (0x738c0 : word) = Some W_738c0.
Proof. vm_refl. Qed.
Lemma D_738c0 : decode_any W_738c0 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_738c4 : bv 32 := 0x00a5f533.
Lemma F_738c4 : fetch_word Asan.M.loaded_segments (0x738c4 : word) = Some W_738c4.
Proof. vm_refl. Qed.
Lemma D_738c4 : decode_any W_738c4 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_738c8 : bv 32 := 0x0a051863.
Lemma F_738c8 : fetch_word Asan.M.loaded_segments (0x738c8 : word) = Some W_738c8.
Proof. vm_refl. Qed.
Lemma D_738c8 : decode_any W_738c8 = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_738cc : bv 32 := 0x00b40433.
Lemma F_738cc : fetch_word Asan.M.loaded_segments (0x738cc : word) = Some W_738cc.
Proof. vm_refl. Qed.
Lemma D_738cc : decode_any W_738cc = Some (Op ALU_ADD 8 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_738d0 : bv 32 := 0xfff40413.
Lemma F_738d0 : fetch_word Asan.M.loaded_segments (0x738d0 : word) = Some W_738d0.
Proof. vm_refl. Qed.
Lemma D_738d0 : decode_any W_738d0 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_738d4 : bv 32 := 0x40b00533.
Lemma F_738d4 : fetch_word Asan.M.loaded_segments (0x738d4 : word) = Some W_738d4.
Proof. vm_refl. Qed.
Lemma D_738d4 : decode_any W_738d4 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_738d8 : bv 32 := 0x00a47433.
Lemma F_738d8 : fetch_word Asan.M.loaded_segments (0x738d8 : word) = Some W_738d8.
Proof. vm_refl. Qed.
Lemma D_738d8 : decode_any W_738d8 = Some (Op ALU_AND 8 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_738dc : bv 32 := 0x00059863.
Lemma F_738dc : fetch_word Asan.M.loaded_segments (0x738dc : word) = Some W_738dc.
Proof. vm_refl. Qed.
Lemma D_738dc : decode_any W_738dc = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_738e0 : bv 32 := 0x9acff0ef.
Lemma F_738e0 : fetch_word Asan.M.loaded_segments (0x738e0 : word) = Some W_738e0.
Proof. vm_refl. Qed.
Lemma D_738e0 : decode_any W_738e0 = Some (Jal 1 2093484, 4%Z).
Proof. vm_refl. Qed.

Definition W_738e4 : bv 32 := 0x00aa3023.
Lemma F_738e4 : fetch_word Asan.M.loaded_segments (0x738e4 : word) = Some W_738e4.
Proof. vm_refl. Qed.
Lemma D_738e4 : decode_any W_738e4 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_738e8 : bv 32 := 0x40a00533.
Lemma F_738e8 : fetch_word Asan.M.loaded_segments (0x738e8 : word) = Some W_738e8.
Proof. vm_refl. Qed.
Lemma D_738e8 : decode_any W_738e8 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_738ec : bv 32 := 0x00a97933.
Lemma F_738ec : fetch_word Asan.M.loaded_segments (0x738ec : word) = Some W_738ec.
Proof. vm_refl. Qed.
Lemma D_738ec : decode_any W_738ec = Some (Op ALU_AND 18 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_738f0 : bv 32 := 0x03200513.
Lemma F_738f0 : fetch_word Asan.M.loaded_segments (0x738f0 : word) = Some W_738f0.
Proof. vm_refl. Qed.
Lemma D_738f0 : decode_any W_738f0 = Some (OpImm ALU_ADD 10 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_738f4 : bv 32 := 0x00a12023.
Lemma F_738f4 : fetch_word Asan.M.loaded_segments (0x738f4 : word) = Some W_738f4.
Proof. vm_refl. Qed.
Lemma D_738f4 : decode_any W_738f4 = Some (Store SZ4 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_738f8 : bv 32 := 0x00010613.
Lemma F_738f8 : fetch_word Asan.M.loaded_segments (0x738f8 : word) = Some W_738f8.
Proof. vm_refl. Qed.
Lemma D_738f8 : decode_any W_738f8 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_738fc : bv 32 := 0x00098513.
Lemma F_738fc : fetch_word Asan.M.loaded_segments (0x738fc : word) = Some W_738fc.
Proof. vm_refl. Qed.
Lemma D_738fc : decode_any W_738fc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73900 : bv 32 := 0x00040593.
Lemma F_73900 : fetch_word Asan.M.loaded_segments (0x73900 : word) = Some W_73900.
Proof. vm_refl. Qed.
Lemma D_73900 : decode_any W_73900 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73904 : bv 32 := 0x608000ef.
Lemma F_73904 : fetch_word Asan.M.loaded_segments (0x73904 : word) = Some W_73904.
Proof. vm_refl. Qed.
Lemma D_73904 : decode_any W_73904 = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

Definition W_73908 : bv 32 := 0x00012683.
Lemma F_73908 : fetch_word Asan.M.loaded_segments (0x73908 : word) = Some W_73908.
Proof. vm_refl. Qed.
Lemma D_73908 : decode_any W_73908 = Some (Load SZ4 true 13 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7390c : bv 32 := 0x00050713.
Lemma F_7390c : fetch_word Asan.M.loaded_segments (0x7390c : word) = Some W_7390c.
Proof. vm_refl. Qed.
Lemma D_7390c : decode_any W_7390c = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73910 : bv 32 := 0x00300613.
Lemma F_73910 : fetch_word Asan.M.loaded_segments (0x73910 : word) = Some W_73910.
Proof. vm_refl. Qed.
Lemma D_73910 : decode_any W_73910 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_73914 : bv 32 := 0x00090513.
Lemma F_73914 : fetch_word Asan.M.loaded_segments (0x73914 : word) = Some W_73914.
Proof. vm_refl. Qed.
Lemma D_73914 : decode_any W_73914 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73918 : bv 32 := 0x00040593.
Lemma F_73918 : fetch_word Asan.M.loaded_segments (0x73918 : word) = Some W_73918.
Proof. vm_refl. Qed.
Lemma D_73918 : decode_any W_73918 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7391c : bv 32 := 0x00000793.
Lemma F_7391c : fetch_word Asan.M.loaded_segments (0x7391c : word) = Some W_7391c.
Proof. vm_refl. Qed.
Lemma D_7391c : decode_any W_7391c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73920 : bv 32 := 0xa40fe0ef.
Lemma F_73920 : fetch_word Asan.M.loaded_segments (0x73920 : word) = Some W_73920.
Proof. vm_refl. Qed.
Lemma D_73920 : decode_any W_73920 = Some (Jal 1 2089536, 4%Z).
Proof. vm_refl. Qed.

Definition W_73924 : bv 32 := 0x00050993.
Lemma F_73924 : fetch_word Asan.M.loaded_segments (0x73924 : word) = Some W_73924.
Proof. vm_refl. Qed.
Lemma D_73924 : decode_any W_73924 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73928 : bv 32 := 0x00000593.
Lemma F_73928 : fetch_word Asan.M.loaded_segments (0x73928 : word) = Some W_73928.
Proof. vm_refl. Qed.
Lemma D_73928 : decode_any W_73928 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7392c : bv 32 := 0xa14fe0ef.
Lemma F_7392c : fetch_word Asan.M.loaded_segments (0x7392c : word) = Some W_7392c.
Proof. vm_refl. Qed.
Lemma D_7392c : decode_any W_7392c = Some (Jal 1 2089492, 4%Z).
Proof. vm_refl. Qed.

Definition W_73930 : bv 32 := 0xaaaab537.
Lemma F_73930 : fetch_word Asan.M.loaded_segments (0x73930 : word) = Some W_73930.
Proof. vm_refl. Qed.
Lemma D_73930 : decode_any W_73930 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_73934 : bv 32 := 0xaaa50513.
Lemma F_73934 : fetch_word Asan.M.loaded_segments (0x73934 : word) = Some W_73934.
Proof. vm_refl. Qed.
Lemma D_73934 : decode_any W_73934 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_73938 : bv 32 := 0x02a12623.
Lemma F_73938 : fetch_word Asan.M.loaded_segments (0x73938 : word) = Some W_73938.
Proof. vm_refl. Qed.
Lemma D_73938 : decode_any W_73938 = Some (Store SZ4 2 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_7393c : bv 32 := 0x02c10593.
Lemma F_7393c : fetch_word Asan.M.loaded_segments (0x7393c : word) = Some W_7393c.
Proof. vm_refl. Qed.
Lemma D_7393c : decode_any W_7393c = Some (OpImm ALU_ADD 11 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_73940 : bv 32 := 0x00098513.
Lemma F_73940 : fetch_word Asan.M.loaded_segments (0x73940 : word) = Some W_73940.
Proof. vm_refl. Qed.
Lemma D_73940 : decode_any W_73940 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73944 : bv 32 := 0x9fcfe0ef.
Lemma F_73944 : fetch_word Asan.M.loaded_segments (0x73944 : word) = Some W_73944.
Proof. vm_refl. Qed.
Lemma D_73944 : decode_any W_73944 = Some (Jal 1 2089468, 4%Z).
Proof. vm_refl. Qed.

Definition W_73948 : bv 32 := 0x04051063.
Lemma F_73948 : fetch_word Asan.M.loaded_segments (0x73948 : word) = Some W_73948.
Proof. vm_refl. Qed.
Lemma D_73948 : decode_any W_73948 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7394c : bv 32 := 0x00040513.
Lemma F_7394c : fetch_word Asan.M.loaded_segments (0x7394c : word) = Some W_7394c.
Proof. vm_refl. Qed.
Lemma D_7394c : decode_any W_7394c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73950 : bv 32 := 0x8f4fa0ef.
Lemma F_73950 : fetch_word Asan.M.loaded_segments (0x73950 : word) = Some W_73950.
Proof. vm_refl. Qed.
Lemma D_73950 : decode_any W_73950 = Some (Jal 1 2072820, 4%Z).
Proof. vm_refl. Qed.

Definition W_73954 : bv 32 := 0x00098513.
Lemma F_73954 : fetch_word Asan.M.loaded_segments (0x73954 : word) = Some W_73954.
Proof. vm_refl. Qed.
Lemma D_73954 : decode_any W_73954 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73958 : bv 32 := 0x05813083.
Lemma F_73958 : fetch_word Asan.M.loaded_segments (0x73958 : word) = Some W_73958.
Proof. vm_refl. Qed.
Lemma D_73958 : decode_any W_73958 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7395c : bv 32 := 0x05013403.
Lemma F_7395c : fetch_word Asan.M.loaded_segments (0x7395c : word) = Some W_7395c.
Proof. vm_refl. Qed.
Lemma D_7395c : decode_any W_7395c = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_73960 : bv 32 := 0x04813483.
Lemma F_73960 : fetch_word Asan.M.loaded_segments (0x73960 : word) = Some W_73960.
Proof. vm_refl. Qed.
Lemma D_73960 : decode_any W_73960 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_73964 : bv 32 := 0x04013903.
Lemma F_73964 : fetch_word Asan.M.loaded_segments (0x73964 : word) = Some W_73964.
Proof. vm_refl. Qed.
Lemma D_73964 : decode_any W_73964 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_73968 : bv 32 := 0x03813983.
Lemma F_73968 : fetch_word Asan.M.loaded_segments (0x73968 : word) = Some W_73968.
Proof. vm_refl. Qed.
Lemma D_73968 : decode_any W_73968 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7396c : bv 32 := 0x03013a03.
Lemma F_7396c : fetch_word Asan.M.loaded_segments (0x7396c : word) = Some W_7396c.
Proof. vm_refl. Qed.
Lemma D_7396c : decode_any W_7396c = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_73970 : bv 32 := 0x06010113.
Lemma F_73970 : fetch_word Asan.M.loaded_segments (0x73970 : word) = Some W_73970.
Proof. vm_refl. Qed.
Lemma D_73970 : decode_any W_73970 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_73974 : bv 32 := 0x00008067.
Lemma F_73974 : fetch_word Asan.M.loaded_segments (0x73974 : word) = Some W_73974.
Proof. vm_refl. Qed.
Lemma D_73974 : decode_any W_73974 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73978 : bv 32 := 0xfff9f517.
Lemma F_73978 : fetch_word Asan.M.loaded_segments (0x73978 : word) = Some W_73978.
Proof. vm_refl. Qed.
Lemma D_73978 : decode_any W_73978 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_7397c : bv 32 := 0xdf250513.
Lemma F_7397c : fetch_word Asan.M.loaded_segments (0x7397c : word) = Some W_7397c.
Proof. vm_refl. Qed.
Lemma D_7397c : decode_any W_7397c = Some (OpImm ALU_ADD 10 10 3570, 4%Z).
Proof. vm_refl. Qed.

Definition W_73980 : bv 32 := 0x895fa0ef.
Lemma F_73980 : fetch_word Asan.M.loaded_segments (0x73980 : word) = Some W_73980.
Proof. vm_refl. Qed.
Lemma D_73980 : decode_any W_73980 = Some (Jal 1 2074772, 4%Z).
Proof. vm_refl. Qed.

Definition W_73984 : bv 32 := 0x618050ef.
Lemma F_73984 : fetch_word Asan.M.loaded_segments (0x73984 : word) = Some W_73984.
Proof. vm_refl. Qed.
Lemma D_73984 : decode_any W_73984 = Some (Jal 1 22040, 4%Z).
Proof. vm_refl. Qed.

Definition W_73988 : bv 32 := 0x00048c63.
Lemma F_73988 : fetch_word Asan.M.loaded_segments (0x73988 : word) = Some W_73988.
Proof. vm_refl. Qed.
Lemma D_73988 : decode_any W_73988 = Some (Branch BC_EQ 9 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7398c : bv 32 := 0x02c12503.
Lemma F_7398c : fetch_word Asan.M.loaded_segments (0x7398c : word) = Some W_7398c.
Proof. vm_refl. Qed.
Lemma D_7398c : decode_any W_7398c = Some (Load SZ4 true 10 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_73990 : bv 32 := 0x00c00593.
Lemma F_73990 : fetch_word Asan.M.loaded_segments (0x73990 : word) = Some W_73990.
Proof. vm_refl. Qed.
Lemma D_73990 : decode_any W_73990 = Some (OpImm ALU_ADD 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73994 : bv 32 := 0x00b51663.
Lemma F_73994 : fetch_word Asan.M.loaded_segments (0x73994 : word) = Some W_73994.
Proof. vm_refl. Qed.
Lemma D_73994 : decode_any W_73994 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73998 : bv 32 := 0x00000993.
Lemma F_73998 : fetch_word Asan.M.loaded_segments (0x73998 : word) = Some W_73998.
Proof. vm_refl. Qed.
Lemma D_73998 : decode_any W_73998 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7399c : bv 32 := 0xfb9ff06f.
Lemma F_7399c : fetch_word Asan.M.loaded_segments (0x7399c : word) = Some W_7399c.
Proof. vm_refl. Qed.
Lemma D_7399c : decode_any W_7399c = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

Definition W_739a0 : bv 32 := 0xfff9d517.
Lemma F_739a0 : fetch_word Asan.M.loaded_segments (0x739a0 : word) = Some W_739a0.
Proof. vm_refl. Qed.
Lemma D_739a0 : decode_any W_739a0 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_739a4 : bv 32 := 0xa6853503.
Lemma F_739a4 : fetch_word Asan.M.loaded_segments (0x739a4 : word) = Some W_739a4.
Proof. vm_refl. Qed.
Lemma D_739a4 : decode_any W_739a4 = Some (Load SZ8 true 10 10 2664, 4%Z).
Proof. vm_refl. Qed.

Definition W_739a8 : bv 32 := 0x02a13023.
Lemma F_739a8 : fetch_word Asan.M.loaded_segments (0x739a8 : word) = Some W_739a8.
Proof. vm_refl. Qed.
Lemma D_739a8 : decode_any W_739a8 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_739ac : bv 32 := 0x00a13023.
Lemma F_739ac : fetch_word Asan.M.loaded_segments (0x739ac : word) = Some W_739ac.
Proof. vm_refl. Qed.
Lemma D_739ac : decode_any W_739ac = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_739b0 : bv 32 := 0x00a13423.
Lemma F_739b0 : fetch_word Asan.M.loaded_segments (0x739b0 : word) = Some W_739b0.
Proof. vm_refl. Qed.
Lemma D_739b0 : decode_any W_739b0 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_739b4 : bv 32 := 0x00a13823.
Lemma F_739b4 : fetch_word Asan.M.loaded_segments (0x739b4 : word) = Some W_739b4.
Proof. vm_refl. Qed.
Lemma D_739b4 : decode_any W_739b4 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_739b8 : bv 32 := 0x00a13c23.
Lemma F_739b8 : fetch_word Asan.M.loaded_segments (0x739b8 : word) = Some W_739b8.
Proof. vm_refl. Qed.
Lemma D_739b8 : decode_any W_739b8 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_739bc : bv 32 := 0xfffaa597.
Lemma F_739bc : fetch_word Asan.M.loaded_segments (0x739bc : word) = Some W_739bc.
Proof. vm_refl. Qed.
Lemma D_739bc : decode_any W_739bc = Some (Auipc 11 1048490, 4%Z).
Proof. vm_refl. Qed.

Definition W_739c0 : bv 32 := 0x00010513.
Lemma F_739c0 : fetch_word Asan.M.loaded_segments (0x739c0 : word) = Some W_739c0.
Proof. vm_refl. Qed.
Lemma D_739c0 : decode_any W_739c0 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_739c4 : bv 32 := 0x6c258613.
Lemma F_739c4 : fetch_word Asan.M.loaded_segments (0x739c4 : word) = Some W_739c4.
Proof. vm_refl. Qed.
Lemma D_739c4 : decode_any W_739c4 = Some (OpImm ALU_ADD 12 11 1730, 4%Z).
Proof. vm_refl. Qed.

Definition W_739c8 : bv 32 := 0x02800593.
Lemma F_739c8 : fetch_word Asan.M.loaded_segments (0x739c8 : word) = Some W_739c8.
Proof. vm_refl. Qed.
Lemma D_739c8 : decode_any W_739c8 = Some (OpImm ALU_ADD 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_739cc : bv 32 := 0x00090693.
Lemma F_739cc : fetch_word Asan.M.loaded_segments (0x739cc : word) = Some W_739cc.
Proof. vm_refl. Qed.
Lemma D_739cc : decode_any W_739cc = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_739d0 : bv 32 := 0x605000ef.
Lemma F_739d0 : fetch_word Asan.M.loaded_segments (0x739d0 : word) = Some W_739d0.
Proof. vm_refl. Qed.
Lemma D_739d0 : decode_any W_739d0 = Some (Jal 1 3588, 4%Z).
Proof. vm_refl. Qed.

Definition W_739d4 : bv 32 := 0x02c12683.
Lemma F_739d4 : fetch_word Asan.M.loaded_segments (0x739d4 : word) = Some W_739d4.
Proof. vm_refl. Qed.
Lemma D_739d4 : decode_any W_739d4 = Some (Load SZ4 true 13 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_739d8 : bv 32 := 0xfffa7517.
Lemma F_739d8 : fetch_word Asan.M.loaded_segments (0x739d8 : word) = Some W_739d8.
Proof. vm_refl. Qed.
Lemma D_739d8 : decode_any W_739d8 = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_739dc : bv 32 := 0x1fa50613.
Lemma F_739dc : fetch_word Asan.M.loaded_segments (0x739dc : word) = Some W_739dc.
Proof. vm_refl. Qed.
Lemma D_739dc : decode_any W_739dc = Some (OpImm ALU_ADD 12 10 506, 4%Z).
Proof. vm_refl. Qed.

Definition W_739e0 : bv 32 := 0x00010593.
Lemma F_739e0 : fetch_word Asan.M.loaded_segments (0x739e0 : word) = Some W_739e0.
Proof. vm_refl. Qed.
Lemma D_739e0 : decode_any W_739e0 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_739e4 : bv 32 := 0x00040513.
Lemma F_739e4 : fetch_word Asan.M.loaded_segments (0x739e4 : word) = Some W_739e4.
Proof. vm_refl. Qed.
Lemma D_739e4 : decode_any W_739e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_739e8 : bv 32 := 0x00000713.
Lemma F_739e8 : fetch_word Asan.M.loaded_segments (0x739e8 : word) = Some W_739e8.
Proof. vm_refl. Qed.
Lemma D_739e8 : decode_any W_739e8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_739ec : bv 32 := 0x9c1f90ef.
Lemma F_739ec : fetch_word Asan.M.loaded_segments (0x739ec : word) = Some W_739ec.
Proof. vm_refl. Qed.
Lemma D_739ec : decode_any W_739ec = Some (Jal 1 2070976, 4%Z).
Proof. vm_refl. Qed.

Definition W_739f0 : bv 32 := 0x00060693.
Lemma F_739f0 : fetch_word Asan.M.loaded_segments (0x739f0 : word) = Some W_739f0.
Proof. vm_refl. Qed.
Lemma D_739f0 : decode_any W_739f0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_739f4 : bv 32 := 0x00100613.
Lemma F_739f4 : fetch_word Asan.M.loaded_segments (0x739f4 : word) = Some W_739f4.
Proof. vm_refl. Qed.
Lemma D_739f4 : decode_any W_739f4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_739f8 : bv 32 := 0xe81ff06f.
Lemma F_739f8 : fetch_word Asan.M.loaded_segments (0x739f8 : word) = Some W_739f8.
Proof. vm_refl. Qed.
Lemma D_739f8 : decode_any W_739f8 = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.
