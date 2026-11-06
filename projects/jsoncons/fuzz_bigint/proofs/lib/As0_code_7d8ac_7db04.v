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

Definition W_7d8ac : bv 32 := 0xfc010113.
Lemma F_7d8ac : fetch_word Asan.M.loaded_segments (0x7d8ac : word) = Some W_7d8ac.
Proof. vm_refl. Qed.
Lemma D_7d8ac : decode_any W_7d8ac = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8b0 : bv 32 := 0x02113c23.
Lemma F_7d8b0 : fetch_word Asan.M.loaded_segments (0x7d8b0 : word) = Some W_7d8b0.
Proof. vm_refl. Qed.
Lemma D_7d8b0 : decode_any W_7d8b0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8b4 : bv 32 := 0x02813823.
Lemma F_7d8b4 : fetch_word Asan.M.loaded_segments (0x7d8b4 : word) = Some W_7d8b4.
Proof. vm_refl. Qed.
Lemma D_7d8b4 : decode_any W_7d8b4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8b8 : bv 32 := 0x02913423.
Lemma F_7d8b8 : fetch_word Asan.M.loaded_segments (0x7d8b8 : word) = Some W_7d8b8.
Proof. vm_refl. Qed.
Lemma D_7d8b8 : decode_any W_7d8b8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8bc : bv 32 := 0x03213023.
Lemma F_7d8bc : fetch_word Asan.M.loaded_segments (0x7d8bc : word) = Some W_7d8bc.
Proof. vm_refl. Qed.
Lemma D_7d8bc : decode_any W_7d8bc = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8c0 : bv 32 := 0x01313c23.
Lemma F_7d8c0 : fetch_word Asan.M.loaded_segments (0x7d8c0 : word) = Some W_7d8c0.
Proof. vm_refl. Qed.
Lemma D_7d8c0 : decode_any W_7d8c0 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8c4 : bv 32 := 0x01413823.
Lemma F_7d8c4 : fetch_word Asan.M.loaded_segments (0x7d8c4 : word) = Some W_7d8c4.
Proof. vm_refl. Qed.
Lemma D_7d8c4 : decode_any W_7d8c4 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8c8 : bv 32 := 0x01513423.
Lemma F_7d8c8 : fetch_word Asan.M.loaded_segments (0x7d8c8 : word) = Some W_7d8c8.
Proof. vm_refl. Qed.
Lemma D_7d8c8 : decode_any W_7d8c8 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8cc : bv 32 := 0x00058993.
Lemma F_7d8cc : fetch_word Asan.M.loaded_segments (0x7d8cc : word) = Some W_7d8cc.
Proof. vm_refl. Qed.
Lemma D_7d8cc : decode_any W_7d8cc = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8d0 : bv 32 := 0x0085aa03.
Lemma F_7d8d0 : fetch_word Asan.M.loaded_segments (0x7d8d0 : word) = Some W_7d8d0.
Proof. vm_refl. Qed.
Lemma D_7d8d0 : decode_any W_7d8d0 = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8d4 : bv 32 := 0x00c5aa83.
Lemma F_7d8d4 : fetch_word Asan.M.loaded_segments (0x7d8d4 : word) = Some W_7d8d4.
Proof. vm_refl. Qed.
Lemma D_7d8d4 : decode_any W_7d8d4 = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8d8 : bv 32 := 0x015a65b3.
Lemma F_7d8d8 : fetch_word Asan.M.loaded_segments (0x7d8d8 : word) = Some W_7d8d8.
Proof. vm_refl. Qed.
Lemma D_7d8d8 : decode_any W_7d8d8 = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8dc : bv 32 := 0x00059663.
Lemma F_7d8dc : fetch_word Asan.M.loaded_segments (0x7d8dc : word) = Some W_7d8dc.
Proof. vm_refl. Qed.
Lemma D_7d8dc : decode_any W_7d8dc = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8e0 : bv 32 := 0x00000513.
Lemma F_7d8e0 : fetch_word Asan.M.loaded_segments (0x7d8e0 : word) = Some W_7d8e0.
Proof. vm_refl. Qed.
Lemma D_7d8e0 : decode_any W_7d8e0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8e4 : bv 32 := 0x0a40006f.
Lemma F_7d8e4 : fetch_word Asan.M.loaded_segments (0x7d8e4 : word) = Some W_7d8e4.
Proof. vm_refl. Qed.
Lemma D_7d8e4 : decode_any W_7d8e4 = Some (Jal 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8e8 : bv 32 := 0x00050493.
Lemma F_7d8e8 : fetch_word Asan.M.loaded_segments (0x7d8e8 : word) = Some W_7d8e8.
Proof. vm_refl. Qed.
Lemma D_7d8e8 : decode_any W_7d8e8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8ec : bv 32 := 0x10000513.
Lemma F_7d8ec : fetch_word Asan.M.loaded_segments (0x7d8ec : word) = Some W_7d8ec.
Proof. vm_refl. Qed.
Lemma D_7d8ec : decode_any W_7d8ec = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8f0 : bv 32 := 0x0aaafe63.
Lemma F_7d8f0 : fetch_word Asan.M.loaded_segments (0x7d8f0 : word) = Some W_7d8f0.
Proof. vm_refl. Qed.
Lemma D_7d8f0 : decode_any W_7d8f0 = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8f4 : bv 32 := 0x00060413.
Lemma F_7d8f4 : fetch_word Asan.M.loaded_segments (0x7d8f4 : word) = Some W_7d8f4.
Proof. vm_refl. Qed.
Lemma D_7d8f4 : decode_any W_7d8f4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8f8 : bv 32 := 0x0ff00513.
Lemma F_7d8f8 : fetch_word Asan.M.loaded_segments (0x7d8f8 : word) = Some W_7d8f8.
Proof. vm_refl. Qed.
Lemma D_7d8f8 : decode_any W_7d8f8 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d8fc : bv 32 := 0x00aa6463.
Lemma F_7d8fc : fetch_word Asan.M.loaded_segments (0x7d8fc : word) = Some W_7d8fc.
Proof. vm_refl. Qed.
Lemma D_7d8fc : decode_any W_7d8fc = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d900 : bv 32 := 0x0ff00a13.
Lemma F_7d900 : fetch_word Asan.M.loaded_segments (0x7d900 : word) = Some W_7d900.
Proof. vm_refl. Qed.
Lemma D_7d900 : decode_any W_7d900 = Some (OpImm ALU_ADD 20 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d904 : bv 32 := 0x00013023.
Lemma F_7d904 : fetch_word Asan.M.loaded_segments (0x7d904 : word) = Some W_7d904.
Proof. vm_refl. Qed.
Lemma D_7d904 : decode_any W_7d904 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d908 : bv 32 := 0x00043023.
Lemma F_7d908 : fetch_word Asan.M.loaded_segments (0x7d908 : word) = Some W_7d908.
Proof. vm_refl. Qed.
Lemma D_7d908 : decode_any W_7d908 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d90c : bv 32 := 0x001a0913.
Lemma F_7d90c : fetch_word Asan.M.loaded_segments (0x7d90c : word) = Some W_7d90c.
Proof. vm_refl. Qed.
Lemma D_7d90c : decode_any W_7d90c = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d910 : bv 32 := 0x00010613.
Lemma F_7d910 : fetch_word Asan.M.loaded_segments (0x7d910 : word) = Some W_7d910.
Proof. vm_refl. Qed.
Lemma D_7d910 : decode_any W_7d910 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d914 : bv 32 := 0x00048513.
Lemma F_7d914 : fetch_word Asan.M.loaded_segments (0x7d914 : word) = Some W_7d914.
Proof. vm_refl. Qed.
Lemma D_7d914 : decode_any W_7d914 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d918 : bv 32 := 0x00090593.
Lemma F_7d918 : fetch_word Asan.M.loaded_segments (0x7d918 : word) = Some W_7d918.
Proof. vm_refl. Qed.
Lemma D_7d918 : decode_any W_7d918 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d91c : bv 32 := 0x00040693.
Lemma F_7d91c : fetch_word Asan.M.loaded_segments (0x7d91c : word) = Some W_7d91c.
Proof. vm_refl. Qed.
Lemma D_7d91c : decode_any W_7d91c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d920 : bv 32 := 0x0b0000ef.
Lemma F_7d920 : fetch_word Asan.M.loaded_segments (0x7d920 : word) = Some W_7d920.
Proof. vm_refl. Qed.
Lemma D_7d920 : decode_any W_7d920 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d924 : bv 32 := 0x06050263.
Lemma F_7d924 : fetch_word Asan.M.loaded_segments (0x7d924 : word) = Some W_7d924.
Proof. vm_refl. Qed.
Lemma D_7d924 : decode_any W_7d924 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d928 : bv 32 := 0x008a961b.
Lemma F_7d928 : fetch_word Asan.M.loaded_segments (0x7d928 : word) = Some W_7d928.
Proof. vm_refl. Qed.
Lemma D_7d928 : decode_any W_7d928 = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d92c : bv 32 := 0x0009b583.
Lemma F_7d92c : fetch_word Asan.M.loaded_segments (0x7d92c : word) = Some W_7d92c.
Proof. vm_refl. Qed.
Lemma D_7d92c : decode_any W_7d92c = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d930 : bv 32 := 0x01466633.
Lemma F_7d930 : fetch_word Asan.M.loaded_segments (0x7d930 : word) = Some W_7d930.
Proof. vm_refl. Qed.
Lemma D_7d930 : decode_any W_7d930 = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d934 : bv 32 := 0x00c53023.
Lemma F_7d934 : fetch_word Asan.M.loaded_segments (0x7d934 : word) = Some W_7d934.
Proof. vm_refl. Qed.
Lemma D_7d934 : decode_any W_7d934 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d938 : bv 32 := 0x00850513.
Lemma F_7d938 : fetch_word Asan.M.loaded_segments (0x7d938 : word) = Some W_7d938.
Proof. vm_refl. Qed.
Lemma D_7d938 : decode_any W_7d938 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d93c : bv 32 := 0x003a1613.
Lemma F_7d93c : fetch_word Asan.M.loaded_segments (0x7d93c : word) = Some W_7d93c.
Proof. vm_refl. Qed.
Lemma D_7d93c : decode_any W_7d93c = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d940 : bv 32 := 0x9a5f30ef.
Lemma F_7d940 : fetch_word Asan.M.loaded_segments (0x7d940 : word) = Some W_7d940.
Proof. vm_refl. Qed.
Lemma D_7d940 : decode_any W_7d940 = Some (Jal 1 2046372, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d944 : bv 32 := 0x00013503.
Lemma F_7d944 : fetch_word Asan.M.loaded_segments (0x7d944 : word) = Some W_7d944.
Proof. vm_refl. Qed.
Lemma D_7d944 : decode_any W_7d944 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d948 : bv 32 := 0x01055513.
Lemma F_7d948 : fetch_word Asan.M.loaded_segments (0x7d948 : word) = Some W_7d948.
Proof. vm_refl. Qed.
Lemma D_7d948 : decode_any W_7d948 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d94c : bv 32 := 0xff057513.
Lemma F_7d94c : fetch_word Asan.M.loaded_segments (0x7d94c : word) = Some W_7d94c.
Proof. vm_refl. Qed.
Lemma D_7d94c : decode_any W_7d94c = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d950 : bv 32 := 0x00a48533.
Lemma F_7d950 : fetch_word Asan.M.loaded_segments (0x7d950 : word) = Some W_7d950.
Proof. vm_refl. Qed.
Lemma D_7d950 : decode_any W_7d950 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d954 : bv 32 := 0x01850513.
Lemma F_7d954 : fetch_word Asan.M.loaded_segments (0x7d954 : word) = Some W_7d954.
Proof. vm_refl. Qed.
Lemma D_7d954 : decode_any W_7d954 = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d958 : bv 32 := 0x0325252f.
Lemma F_7d958 : fetch_word Asan.M.loaded_segments (0x7d958 : word) = Some W_7d958.
Proof. vm_refl. Qed.
Lemma D_7d958 : decode_any W_7d958 = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d95c : bv 32 := 0x001005b7.
Lemma F_7d95c : fetch_word Asan.M.loaded_segments (0x7d95c : word) = Some W_7d95c.
Proof. vm_refl. Qed.
Lemma D_7d95c : decode_any W_7d95c = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d960 : bv 32 := 0x02051513.
Lemma F_7d960 : fetch_word Asan.M.loaded_segments (0x7d960 : word) = Some W_7d960.
Proof. vm_refl. Qed.
Lemma D_7d960 : decode_any W_7d960 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d964 : bv 32 := 0x02055513.
Lemma F_7d964 : fetch_word Asan.M.loaded_segments (0x7d964 : word) = Some W_7d964.
Proof. vm_refl. Qed.
Lemma D_7d964 : decode_any W_7d964 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d968 : bv 32 := 0x00a90533.
Lemma F_7d968 : fetch_word Asan.M.loaded_segments (0x7d968 : word) = Some W_7d968.
Proof. vm_refl. Qed.
Lemma D_7d968 : decode_any W_7d968 = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d96c : bv 32 := 0x00043603.
Lemma F_7d96c : fetch_word Asan.M.loaded_segments (0x7d96c : word) = Some W_7d96c.
Proof. vm_refl. Qed.
Lemma D_7d96c : decode_any W_7d96c = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d970 : bv 32 := 0x00b54533.
Lemma F_7d970 : fetch_word Asan.M.loaded_segments (0x7d970 : word) = Some W_7d970.
Proof. vm_refl. Qed.
Lemma D_7d970 : decode_any W_7d970 = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d974 : bv 32 := 0x00012583.
Lemma F_7d974 : fetch_word Asan.M.loaded_segments (0x7d974 : word) = Some W_7d974.
Proof. vm_refl. Qed.
Lemma D_7d974 : decode_any W_7d974 = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d978 : bv 32 := 0x00153513.
Lemma F_7d978 : fetch_word Asan.M.loaded_segments (0x7d978 : word) = Some W_7d978.
Proof. vm_refl. Qed.
Lemma D_7d978 : decode_any W_7d978 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d97c : bv 32 := 0x00a60533.
Lemma F_7d97c : fetch_word Asan.M.loaded_segments (0x7d97c : word) = Some W_7d97c.
Proof. vm_refl. Qed.
Lemma D_7d97c : decode_any W_7d97c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d980 : bv 32 := 0x00a43023.
Lemma F_7d980 : fetch_word Asan.M.loaded_segments (0x7d980 : word) = Some W_7d980.
Proof. vm_refl. Qed.
Lemma D_7d980 : decode_any W_7d980 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d984 : bv 32 := 0x0015851b.
Lemma F_7d984 : fetch_word Asan.M.loaded_segments (0x7d984 : word) = Some W_7d984.
Proof. vm_refl. Qed.
Lemma D_7d984 : decode_any W_7d984 = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d988 : bv 32 := 0x03813083.
Lemma F_7d988 : fetch_word Asan.M.loaded_segments (0x7d988 : word) = Some W_7d988.
Proof. vm_refl. Qed.
Lemma D_7d988 : decode_any W_7d988 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d98c : bv 32 := 0x03013403.
Lemma F_7d98c : fetch_word Asan.M.loaded_segments (0x7d98c : word) = Some W_7d98c.
Proof. vm_refl. Qed.
Lemma D_7d98c : decode_any W_7d98c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d990 : bv 32 := 0x02813483.
Lemma F_7d990 : fetch_word Asan.M.loaded_segments (0x7d990 : word) = Some W_7d990.
Proof. vm_refl. Qed.
Lemma D_7d990 : decode_any W_7d990 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d994 : bv 32 := 0x02013903.
Lemma F_7d994 : fetch_word Asan.M.loaded_segments (0x7d994 : word) = Some W_7d994.
Proof. vm_refl. Qed.
Lemma D_7d994 : decode_any W_7d994 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d998 : bv 32 := 0x01813983.
Lemma F_7d998 : fetch_word Asan.M.loaded_segments (0x7d998 : word) = Some W_7d998.
Proof. vm_refl. Qed.
Lemma D_7d998 : decode_any W_7d998 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d99c : bv 32 := 0x01013a03.
Lemma F_7d99c : fetch_word Asan.M.loaded_segments (0x7d99c : word) = Some W_7d99c.
Proof. vm_refl. Qed.
Lemma D_7d99c : decode_any W_7d99c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9a0 : bv 32 := 0x00813a83.
Lemma F_7d9a0 : fetch_word Asan.M.loaded_segments (0x7d9a0 : word) = Some W_7d9a0.
Proof. vm_refl. Qed.
Lemma D_7d9a0 : decode_any W_7d9a0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9a4 : bv 32 := 0x04010113.
Lemma F_7d9a4 : fetch_word Asan.M.loaded_segments (0x7d9a4 : word) = Some W_7d9a4.
Proof. vm_refl. Qed.
Lemma D_7d9a4 : decode_any W_7d9a4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9a8 : bv 32 := 0x00008067.
Lemma F_7d9a8 : fetch_word Asan.M.loaded_segments (0x7d9a8 : word) = Some W_7d9a8.
Proof. vm_refl. Qed.
Lemma D_7d9a8 : decode_any W_7d9a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9ac : bv 32 := 0x020a9693.
Lemma F_7d9ac : fetch_word Asan.M.loaded_segments (0x7d9ac : word) = Some W_7d9ac.
Proof. vm_refl. Qed.
Lemma D_7d9ac : decode_any W_7d9ac = Some (ShiftImm ALU_SLL 13 21 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9b0 : bv 32 := 0x0206d693.
Lemma F_7d9b0 : fetch_word Asan.M.loaded_segments (0x7d9b0 : word) = Some W_7d9b0.
Proof. vm_refl. Qed.
Lemma D_7d9b0 : decode_any W_7d9b0 = Some (ShiftImm ALU_SRL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9b4 : bv 32 := 0x0ff6f713.
Lemma F_7d9b4 : fetch_word Asan.M.loaded_segments (0x7d9b4 : word) = Some W_7d9b4.
Proof. vm_refl. Qed.
Lemma D_7d9b4 : decode_any W_7d9b4 = Some (OpImm ALU_AND 14 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9b8 : bv 32 := 0xfffa3517.
Lemma F_7d9b8 : fetch_word Asan.M.loaded_segments (0x7d9b8 : word) = Some W_7d9b8.
Proof. vm_refl. Qed.
Lemma D_7d9b8 : decode_any W_7d9b8 = Some (Auipc 10 1048483, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9bc : bv 32 := 0xfff9a597.
Lemma F_7d9bc : fetch_word Asan.M.loaded_segments (0x7d9bc : word) = Some W_7d9bc.
Proof. vm_refl. Qed.
Lemma D_7d9bc : decode_any W_7d9bc = Some (Auipc 11 1048474, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9c0 : bv 32 := 0x69c50513.
Lemma F_7d9c0 : fetch_word Asan.M.loaded_segments (0x7d9c0 : word) = Some W_7d9c0.
Proof. vm_refl. Qed.
Lemma D_7d9c0 : decode_any W_7d9c0 = Some (OpImm ALU_ADD 10 10 1692, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9c4 : bv 32 := 0xd2758613.
Lemma F_7d9c4 : fetch_word Asan.M.loaded_segments (0x7d9c4 : word) = Some W_7d9c4.
Proof. vm_refl. Qed.
Lemma D_7d9c4 : decode_any W_7d9c4 = Some (OpImm ALU_ADD 12 11 3367, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9c8 : bv 32 := 0x01d00593.
Lemma F_7d9c8 : fetch_word Asan.M.loaded_segments (0x7d9c8 : word) = Some W_7d9c8.
Proof. vm_refl. Qed.
Lemma D_7d9c8 : decode_any W_7d9c8 = Some (OpImm ALU_ADD 11 0 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9cc : bv 32 := 0xe9cfb0ef.
Lemma F_7d9cc : fetch_word Asan.M.loaded_segments (0x7d9cc : word) = Some W_7d9cc.
Proof. vm_refl. Qed.
Lemma D_7d9cc : decode_any W_7d9cc = Some (Jal 1 2078364, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9d0 : bv 32 := 0xff010113.
Lemma F_7d9d0 : fetch_word Asan.M.loaded_segments (0x7d9d0 : word) = Some W_7d9d0.
Proof. vm_refl. Qed.
Lemma D_7d9d0 : decode_any W_7d9d0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9d4 : bv 32 := 0x00113423.
Lemma F_7d9d4 : fetch_word Asan.M.loaded_segments (0x7d9d4 : word) = Some W_7d9d4.
Proof. vm_refl. Qed.
Lemma D_7d9d4 : decode_any W_7d9d4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9d8 : bv 32 := 0x00813023.
Lemma F_7d9d8 : fetch_word Asan.M.loaded_segments (0x7d9d8 : word) = Some W_7d9d8.
Proof. vm_refl. Qed.
Lemma D_7d9d8 : decode_any W_7d9d8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9dc : bv 32 := 0x00058793.
Lemma F_7d9dc : fetch_word Asan.M.loaded_segments (0x7d9dc : word) = Some W_7d9dc.
Proof. vm_refl. Qed.
Lemma D_7d9dc : decode_any W_7d9dc = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9e0 : bv 32 := 0x00050593.
Lemma F_7d9e0 : fetch_word Asan.M.loaded_segments (0x7d9e0 : word) = Some W_7d9e0.
Proof. vm_refl. Qed.
Lemma D_7d9e0 : decode_any W_7d9e0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9e4 : bv 32 := 0x00f5342f.
Lemma F_7d9e4 : fetch_word Asan.M.loaded_segments (0x7d9e4 : word) = Some W_7d9e4.
Proof. vm_refl. Qed.
Lemma D_7d9e4 : decode_any W_7d9e4 = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9e8 : bv 32 := 0xfff78513.
Lemma F_7d9e8 : fetch_word Asan.M.loaded_segments (0x7d9e8 : word) = Some W_7d9e8.
Proof. vm_refl. Qed.
Lemma D_7d9e8 : decode_any W_7d9e8 = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9ec : bv 32 := 0x01445293.
Lemma F_7d9ec : fetch_word Asan.M.loaded_segments (0x7d9ec : word) = Some W_7d9ec.
Proof. vm_refl. Qed.
Lemma D_7d9ec : decode_any W_7d9ec = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9f0 : bv 32 := 0x00850733.
Lemma F_7d9f0 : fetch_word Asan.M.loaded_segments (0x7d9f0 : word) = Some W_7d9f0.
Proof. vm_refl. Qed.
Lemma D_7d9f0 : decode_any W_7d9f0 = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9f4 : bv 32 := 0x01475313.
Lemma F_7d9f4 : fetch_word Asan.M.loaded_segments (0x7d9f4 : word) = Some W_7d9f4.
Proof. vm_refl. Qed.
Lemma D_7d9f4 : decode_any W_7d9f4 = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9f8 : bv 32 := 0x04629863.
Lemma F_7d9f8 : fetch_word Asan.M.loaded_segments (0x7d9f8 : word) = Some W_7d9f8.
Proof. vm_refl. Qed.
Lemma D_7d9f8 : decode_any W_7d9f8 = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7d9fc : bv 32 := 0x02045513.
Lemma F_7d9fc : fetch_word Asan.M.loaded_segments (0x7d9fc : word) = Some W_7d9fc.
Proof. vm_refl. Qed.
Lemma D_7d9fc : decode_any W_7d9fc = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da00 : bv 32 := 0x00050c63.
Lemma F_7da00 : fetch_word Asan.M.loaded_segments (0x7da00 : word) = Some W_7da00.
Proof. vm_refl. Qed.
Lemma D_7da00 : decode_any W_7da00 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da04 : bv 32 := 0x00000513.
Lemma F_7da04 : fetch_word Asan.M.loaded_segments (0x7da04 : word) = Some W_7da04.
Proof. vm_refl. Qed.
Lemma D_7da04 : decode_any W_7da04 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da08 : bv 32 := 0x00813083.
Lemma F_7da08 : fetch_word Asan.M.loaded_segments (0x7da08 : word) = Some W_7da08.
Proof. vm_refl. Qed.
Lemma D_7da08 : decode_any W_7da08 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da0c : bv 32 := 0x00013403.
Lemma F_7da0c : fetch_word Asan.M.loaded_segments (0x7da0c : word) = Some W_7da0c.
Proof. vm_refl. Qed.
Lemma D_7da0c : decode_any W_7da0c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da10 : bv 32 := 0x01010113.
Lemma F_7da10 : fetch_word Asan.M.loaded_segments (0x7da10 : word) = Some W_7da10.
Proof. vm_refl. Qed.
Lemma D_7da10 : decode_any W_7da10 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da14 : bv 32 := 0x00008067.
Lemma F_7da14 : fetch_word Asan.M.loaded_segments (0x7da14 : word) = Some W_7da14.
Proof. vm_refl. Qed.
Lemma D_7da14 : decode_any W_7da14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da18 : bv 32 := 0x00863023.
Lemma F_7da18 : fetch_word Asan.M.loaded_segments (0x7da18 : word) = Some W_7da18.
Proof. vm_refl. Qed.
Lemma D_7da18 : decode_any W_7da18 = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da1c : bv 32 := 0x00429613.
Lemma F_7da1c : fetch_word Asan.M.loaded_segments (0x7da1c : word) = Some W_7da1c.
Proof. vm_refl. Qed.
Lemma D_7da1c : decode_any W_7da1c = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da20 : bv 32 := 0x00c58633.
Lemma F_7da20 : fetch_word Asan.M.loaded_segments (0x7da20 : word) = Some W_7da20.
Proof. vm_refl. Qed.
Lemma D_7da20 : decode_any W_7da20 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da24 : bv 32 := 0x01063503.
Lemma F_7da24 : fetch_word Asan.M.loaded_segments (0x7da24 : word) = Some W_7da24.
Proof. vm_refl. Qed.
Lemma D_7da24 : decode_any W_7da24 = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da28 : bv 32 := 0x0a050a63.
Lemma F_7da28 : fetch_word Asan.M.loaded_segments (0x7da28 : word) = Some W_7da28.
Proof. vm_refl. Qed.
Lemma D_7da28 : decode_any W_7da28 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da2c : bv 32 := 0x02c41413.
Lemma F_7da2c : fetch_word Asan.M.loaded_segments (0x7da2c : word) = Some W_7da2c.
Proof. vm_refl. Qed.
Lemma D_7da2c : decode_any W_7da2c = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da30 : bv 32 := 0x02945413.
Lemma F_7da30 : fetch_word Asan.M.loaded_segments (0x7da30 : word) = Some W_7da30.
Proof. vm_refl. Qed.
Lemma D_7da30 : decode_any W_7da30 = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da34 : bv 32 := 0x00850533.
Lemma F_7da34 : fetch_word Asan.M.loaded_segments (0x7da34 : word) = Some W_7da34.
Proof. vm_refl. Qed.
Lemma D_7da34 : decode_any W_7da34 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da38 : bv 32 := 0x00813083.
Lemma F_7da38 : fetch_word Asan.M.loaded_segments (0x7da38 : word) = Some W_7da38.
Proof. vm_refl. Qed.
Lemma D_7da38 : decode_any W_7da38 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da3c : bv 32 := 0x00013403.
Lemma F_7da3c : fetch_word Asan.M.loaded_segments (0x7da3c : word) = Some W_7da3c.
Proof. vm_refl. Qed.
Lemma D_7da3c : decode_any W_7da3c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da40 : bv 32 := 0x01010113.
Lemma F_7da40 : fetch_word Asan.M.loaded_segments (0x7da40 : word) = Some W_7da40.
Proof. vm_refl. Qed.
Lemma D_7da40 : decode_any W_7da40 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da44 : bv 32 := 0x00008067.
Lemma F_7da44 : fetch_word Asan.M.loaded_segments (0x7da44 : word) = Some W_7da44.
Proof. vm_refl. Qed.
Lemma D_7da44 : decode_any W_7da44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da48 : bv 32 := 0x00100737.
Lemma F_7da48 : fetch_word Asan.M.loaded_segments (0x7da48 : word) = Some W_7da48.
Proof. vm_refl. Qed.
Lemma D_7da48 : decode_any W_7da48 = Some (Lui 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da4c : bv 32 := 0x08f76e63.
Lemma F_7da4c : fetch_word Asan.M.loaded_segments (0x7da4c : word) = Some W_7da4c.
Proof. vm_refl. Qed.
Lemma D_7da4c : decode_any W_7da4c = Some (Branch BC_LTU 14 15 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da50 : bv 32 := 0x01058813.
Lemma F_7da50 : fetch_word Asan.M.loaded_segments (0x7da50 : word) = Some W_7da50.
Proof. vm_refl. Qed.
Lemma D_7da50 : decode_any W_7da50 = Some (OpImm ALU_ADD 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da54 : bv 32 := 0xfff7089b.
Lemma F_7da54 : fetch_word Asan.M.loaded_segments (0x7da54 : word) = Some W_7da54.
Proof. vm_refl. Qed.
Lemma D_7da54 : decode_any W_7da54 = Some (OpImm32 17 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da58 : bv 32 := 0x011473b3.
Lemma F_7da58 : fetch_word Asan.M.loaded_segments (0x7da58 : word) = Some W_7da58.
Proof. vm_refl. Qed.
Lemma D_7da58 : decode_any W_7da58 = Some (Op ALU_AND 7 8 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da5c : bv 32 := 0x00429293.
Lemma F_7da5c : fetch_word Asan.M.loaded_segments (0x7da5c : word) = Some W_7da5c.
Proof. vm_refl. Qed.
Lemma D_7da5c : decode_any W_7da5c = Some (ShiftImm ALU_SLL 5 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da60 : bv 32 := 0x407703b3.
Lemma F_7da60 : fetch_word Asan.M.loaded_segments (0x7da60 : word) = Some W_7da60.
Proof. vm_refl. Qed.
Lemma D_7da60 : decode_any W_7da60 = Some (Op ALU_SUB 7 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da64 : bv 32 := 0x005802b3.
Lemma F_7da64 : fetch_word Asan.M.loaded_segments (0x7da64 : word) = Some W_7da64.
Proof. vm_refl. Qed.
Lemma D_7da64 : decode_any W_7da64 = Some (Op ALU_ADD 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da68 : bv 32 := 0x00828293.
Lemma F_7da68 : fetch_word Asan.M.loaded_segments (0x7da68 : word) = Some W_7da68.
Proof. vm_refl. Qed.
Lemma D_7da68 : decode_any W_7da68 = Some (OpImm ALU_ADD 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da6c : bv 32 := 0x0272a2af.
Lemma F_7da6c : fetch_word Asan.M.loaded_segments (0x7da6c : word) = Some W_7da6c.
Proof. vm_refl. Qed.
Lemma D_7da6c : decode_any W_7da6c = Some (Amo AMO_ADD AW false true 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da70 : bv 32 := 0x00431313.
Lemma F_7da70 : fetch_word Asan.M.loaded_segments (0x7da70 : word) = Some W_7da70.
Proof. vm_refl. Qed.
Lemma D_7da70 : decode_any W_7da70 = Some (ShiftImm ALU_SLL 6 6 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da74 : bv 32 := 0x00680333.
Lemma F_7da74 : fetch_word Asan.M.loaded_segments (0x7da74 : word) = Some W_7da74.
Proof. vm_refl. Qed.
Lemma D_7da74 : decode_any W_7da74 = Some (Op ALU_ADD 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da78 : bv 32 := 0x40778e33.
Lemma F_7da78 : fetch_word Asan.M.loaded_segments (0x7da78 : word) = Some W_7da78.
Proof. vm_refl. Qed.
Lemma D_7da78 : decode_any W_7da78 = Some (Op ALU_SUB 28 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da7c : bv 32 := 0x02029293.
Lemma F_7da7c : fetch_word Asan.M.loaded_segments (0x7da7c : word) = Some W_7da7c.
Proof. vm_refl. Qed.
Lemma D_7da7c : decode_any W_7da7c = Some (ShiftImm ALU_SLL 5 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da80 : bv 32 := 0x0202d293.
Lemma F_7da80 : fetch_word Asan.M.loaded_segments (0x7da80 : word) = Some W_7da80.
Proof. vm_refl. Qed.
Lemma D_7da80 : decode_any W_7da80 = Some (ShiftImm ALU_SRL 5 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da84 : bv 32 := 0x005382b3.
Lemma F_7da84 : fetch_word Asan.M.loaded_segments (0x7da84 : word) = Some W_7da84.
Proof. vm_refl. Qed.
Lemma D_7da84 : decode_any W_7da84 = Some (Op ALU_ADD 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da88 : bv 32 := 0x0006b383.
Lemma F_7da88 : fetch_word Asan.M.loaded_segments (0x7da88 : word) = Some W_7da88.
Proof. vm_refl. Qed.
Lemma D_7da88 : decode_any W_7da88 = Some (Load SZ8 true 7 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da8c : bv 32 := 0x00830313.
Lemma F_7da8c : fetch_word Asan.M.loaded_segments (0x7da8c : word) = Some W_7da8c.
Proof. vm_refl. Qed.
Lemma D_7da8c : decode_any W_7da8c = Some (OpImm ALU_ADD 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da90 : bv 32 := 0x00e2c2b3.
Lemma F_7da90 : fetch_word Asan.M.loaded_segments (0x7da90 : word) = Some W_7da90.
Proof. vm_refl. Qed.
Lemma D_7da90 : decode_any W_7da90 = Some (Op ALU_XOR 5 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da94 : bv 32 := 0x0012b293.
Lemma F_7da94 : fetch_word Asan.M.loaded_segments (0x7da94 : word) = Some W_7da94.
Proof. vm_refl. Qed.
Lemma D_7da94 : decode_any W_7da94 = Some (OpImm ALU_SLTU 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da98 : bv 32 := 0x005382b3.
Lemma F_7da98 : fetch_word Asan.M.loaded_segments (0x7da98 : word) = Some W_7da98.
Proof. vm_refl. Qed.
Lemma D_7da98 : decode_any W_7da98 = Some (Op ALU_ADD 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7da9c : bv 32 := 0x0056b023.
Lemma F_7da9c : fetch_word Asan.M.loaded_segments (0x7da9c : word) = Some W_7da9c.
Proof. vm_refl. Qed.
Lemma D_7da9c : decode_any W_7da9c = Some (Store SZ8 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7daa0 : bv 32 := 0x03c322af.
Lemma F_7daa0 : fetch_word Asan.M.loaded_segments (0x7daa0 : word) = Some W_7daa0.
Proof. vm_refl. Qed.
Lemma D_7daa0 : decode_any W_7daa0 = Some (Amo AMO_ADD AW false true 5 6 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7daa4 : bv 32 := 0x0006b303.
Lemma F_7daa4 : fetch_word Asan.M.loaded_segments (0x7daa4 : word) = Some W_7daa4.
Proof. vm_refl. Qed.
Lemma D_7daa4 : decode_any W_7daa4 = Some (Load SZ8 true 6 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7daa8 : bv 32 := 0x02029293.
Lemma F_7daa8 : fetch_word Asan.M.loaded_segments (0x7daa8 : word) = Some W_7daa8.
Proof. vm_refl. Qed.
Lemma D_7daa8 : decode_any W_7daa8 = Some (ShiftImm ALU_SLL 5 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7daac : bv 32 := 0x0202d293.
Lemma F_7daac : fetch_word Asan.M.loaded_segments (0x7daac : word) = Some W_7daac.
Proof. vm_refl. Qed.
Lemma D_7daac : decode_any W_7daac = Some (ShiftImm ALU_SRL 5 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dab0 : bv 32 := 0x005e02b3.
Lemma F_7dab0 : fetch_word Asan.M.loaded_segments (0x7dab0 : word) = Some W_7dab0.
Proof. vm_refl. Qed.
Lemma D_7dab0 : decode_any W_7dab0 = Some (Op ALU_ADD 5 28 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dab4 : bv 32 := 0x00e2c2b3.
Lemma F_7dab4 : fetch_word Asan.M.loaded_segments (0x7dab4 : word) = Some W_7dab4.
Proof. vm_refl. Qed.
Lemma D_7dab4 : decode_any W_7dab4 = Some (Op ALU_XOR 5 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dab8 : bv 32 := 0x0012b293.
Lemma F_7dab8 : fetch_word Asan.M.loaded_segments (0x7dab8 : word) = Some W_7dab8.
Proof. vm_refl. Qed.
Lemma D_7dab8 : decode_any W_7dab8 = Some (OpImm ALU_SLTU 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dabc : bv 32 := 0x005302b3.
Lemma F_7dabc : fetch_word Asan.M.loaded_segments (0x7dabc : word) = Some W_7dabc.
Proof. vm_refl. Qed.
Lemma D_7dabc : decode_any W_7dabc = Some (Op ALU_ADD 5 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dac0 : bv 32 := 0x0056b023.
Lemma F_7dac0 : fetch_word Asan.M.loaded_segments (0x7dac0 : word) = Some W_7dac0.
Proof. vm_refl. Qed.
Lemma D_7dac0 : decode_any W_7dac0 = Some (Store SZ8 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dac4 : bv 32 := 0x00f5b42f.
Lemma F_7dac4 : fetch_word Asan.M.loaded_segments (0x7dac4 : word) = Some W_7dac4.
Proof. vm_refl. Qed.
Lemma D_7dac4 : decode_any W_7dac4 = Some (Amo AMO_ADD AD false false 8 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dac8 : bv 32 := 0x01445293.
Lemma F_7dac8 : fetch_word Asan.M.loaded_segments (0x7dac8 : word) = Some W_7dac8.
Proof. vm_refl. Qed.
Lemma D_7dac8 : decode_any W_7dac8 = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dacc : bv 32 := 0x00850333.
Lemma F_7dacc : fetch_word Asan.M.loaded_segments (0x7dacc : word) = Some W_7dacc.
Proof. vm_refl. Qed.
Lemma D_7dacc : decode_any W_7dacc = Some (Op ALU_ADD 6 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dad0 : bv 32 := 0x01435313.
Lemma F_7dad0 : fetch_word Asan.M.loaded_segments (0x7dad0 : word) = Some W_7dad0.
Proof. vm_refl. Qed.
Lemma D_7dad0 : decode_any W_7dad0 = Some (ShiftImm ALU_SRL 6 6 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dad4 : bv 32 := 0xf26284e3.
Lemma F_7dad4 : fetch_word Asan.M.loaded_segments (0x7dad4 : word) = Some W_7dad4.
Proof. vm_refl. Qed.
Lemma D_7dad4 : decode_any W_7dad4 = Some (Branch BC_EQ 5 6 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dad8 : bv 32 := 0xf81ff06f.
Lemma F_7dad8 : fetch_word Asan.M.loaded_segments (0x7dad8 : word) = Some W_7dad8.
Proof. vm_refl. Qed.
Lemma D_7dad8 : decode_any W_7dad8 = Some (Jal 0 2097024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dadc : bv 32 := 0x01060513.
Lemma F_7dadc : fetch_word Asan.M.loaded_segments (0x7dadc : word) = Some W_7dadc.
Proof. vm_refl. Qed.
Lemma D_7dadc : decode_any W_7dadc = Some (OpImm ALU_ADD 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dae0 : bv 32 := 0x0d9000ef.
Lemma F_7dae0 : fetch_word Asan.M.loaded_segments (0x7dae0 : word) = Some W_7dae0.
Proof. vm_refl. Qed.
Lemma D_7dae0 : decode_any W_7dae0 = Some (Jal 1 2264, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dae4 : bv 32 := 0xf49ff06f.
Lemma F_7dae4 : fetch_word Asan.M.loaded_segments (0x7dae4 : word) = Some W_7dae4.
Proof. vm_refl. Qed.
Lemma D_7dae4 : decode_any W_7dae4 = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dae8 : bv 32 := 0xfffa3517.
Lemma F_7dae8 : fetch_word Asan.M.loaded_segments (0x7dae8 : word) = Some W_7dae8.
Proof. vm_refl. Qed.
Lemma D_7dae8 : decode_any W_7dae8 = Some (Auipc 10 1048483, 4%Z).
Proof. vm_refl. Qed.

Definition W_7daec : bv 32 := 0xfff9d617.
Lemma F_7daec : fetch_word Asan.M.loaded_segments (0x7daec : word) = Some W_7daec.
Proof. vm_refl. Qed.
Lemma D_7daec : decode_any W_7daec = Some (Auipc 12 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_7daf0 : bv 32 := 0x05b00593.
Lemma F_7daf0 : fetch_word Asan.M.loaded_segments (0x7daf0 : word) = Some W_7daf0.
Proof. vm_refl. Qed.
Lemma D_7daf0 : decode_any W_7daf0 = Some (OpImm ALU_ADD 11 0 91, 4%Z).
Proof. vm_refl. Qed.

Definition W_7daf4 : bv 32 := 0x56c50513.
Lemma F_7daf4 : fetch_word Asan.M.loaded_segments (0x7daf4 : word) = Some W_7daf4.
Proof. vm_refl. Qed.
Lemma D_7daf4 : decode_any W_7daf4 = Some (OpImm ALU_ADD 10 10 1388, 4%Z).
Proof. vm_refl. Qed.

Definition W_7daf8 : bv 32 := 0x14460613.
Lemma F_7daf8 : fetch_word Asan.M.loaded_segments (0x7daf8 : word) = Some W_7daf8.
Proof. vm_refl. Qed.
Lemma D_7daf8 : decode_any W_7daf8 = Some (OpImm ALU_ADD 12 12 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7dafc : bv 32 := 0x00078693.
Lemma F_7dafc : fetch_word Asan.M.loaded_segments (0x7dafc : word) = Some W_7dafc.
Proof. vm_refl. Qed.
Lemma D_7dafc : decode_any W_7dafc = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7db00 : bv 32 := 0xd68fb0ef.
Lemma F_7db00 : fetch_word Asan.M.loaded_segments (0x7db00 : word) = Some W_7db00.
Proof. vm_refl. Qed.
Lemma D_7db00 : decode_any W_7db00 = Some (Jal 1 2078056, 4%Z).
Proof. vm_refl. Qed.
