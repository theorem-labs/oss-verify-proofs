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

Definition W_61900 : bv 32 := 0xfc010113.
Lemma F_61900 : fetch_word Asan.M.loaded_segments (0x61900 : word) = Some W_61900.
Proof. vm_refl. Qed.
Lemma D_61900 : decode_any W_61900 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_61904 : bv 32 := 0x02113c23.
Lemma F_61904 : fetch_word Asan.M.loaded_segments (0x61904 : word) = Some W_61904.
Proof. vm_refl. Qed.
Lemma D_61904 : decode_any W_61904 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61908 : bv 32 := 0x02813823.
Lemma F_61908 : fetch_word Asan.M.loaded_segments (0x61908 : word) = Some W_61908.
Proof. vm_refl. Qed.
Lemma D_61908 : decode_any W_61908 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6190c : bv 32 := 0x02913423.
Lemma F_6190c : fetch_word Asan.M.loaded_segments (0x6190c : word) = Some W_6190c.
Proof. vm_refl. Qed.
Lemma D_6190c : decode_any W_6190c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61910 : bv 32 := 0x03213023.
Lemma F_61910 : fetch_word Asan.M.loaded_segments (0x61910 : word) = Some W_61910.
Proof. vm_refl. Qed.
Lemma D_61910 : decode_any W_61910 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61914 : bv 32 := 0x01313c23.
Lemma F_61914 : fetch_word Asan.M.loaded_segments (0x61914 : word) = Some W_61914.
Proof. vm_refl. Qed.
Lemma D_61914 : decode_any W_61914 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61918 : bv 32 := 0x01413823.
Lemma F_61918 : fetch_word Asan.M.loaded_segments (0x61918 : word) = Some W_61918.
Proof. vm_refl. Qed.
Lemma D_61918 : decode_any W_61918 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6191c : bv 32 := 0x01513423.
Lemma F_6191c : fetch_word Asan.M.loaded_segments (0x6191c : word) = Some W_6191c.
Proof. vm_refl. Qed.
Lemma D_6191c : decode_any W_6191c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61920 : bv 32 := 0x14058c63.
Lemma F_61920 : fetch_word Asan.M.loaded_segments (0x61920 : word) = Some W_61920.
Proof. vm_refl. Qed.
Lemma D_61920 : decode_any W_61920 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_61924 : bv 32 := 0x00058493.
Lemma F_61924 : fetch_word Asan.M.loaded_segments (0x61924 : word) = Some W_61924.
Proof. vm_refl. Qed.
Lemma D_61924 : decode_any W_61924 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61928 : bv 32 := 0x00050413.
Lemma F_61928 : fetch_word Asan.M.loaded_segments (0x61928 : word) = Some W_61928.
Proof. vm_refl. Qed.
Lemma D_61928 : decode_any W_61928 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6192c : bv 32 := 0x00074517.
Lemma F_6192c : fetch_word Asan.M.loaded_segments (0x6192c : word) = Some W_6192c.
Proof. vm_refl. Qed.
Lemma D_6192c : decode_any W_6192c = Some (Auipc 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61930 : bv 32 := 0xf8c53a83.
Lemma F_61930 : fetch_word Asan.M.loaded_segments (0x61930 : word) = Some W_61930.
Proof. vm_refl. Qed.
Lemma D_61930 : decode_any W_61930 = Some (Load SZ8 true 21 10 3980, 4%Z).
Proof. vm_refl. Qed.

Definition W_61934 : bv 32 := 0x000ab583.
Lemma F_61934 : fetch_word Asan.M.loaded_segments (0x61934 : word) = Some W_61934.
Proof. vm_refl. Qed.
Lemma D_61934 : decode_any W_61934 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61938 : bv 32 := 0xfff58513.
Lemma F_61938 : fetch_word Asan.M.loaded_segments (0x61938 : word) = Some W_61938.
Proof. vm_refl. Qed.
Lemma D_61938 : decode_any W_61938 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6193c : bv 32 := 0x00a5b633.
Lemma F_6193c : fetch_word Asan.M.loaded_segments (0x6193c : word) = Some W_6193c.
Proof. vm_refl. Qed.
Lemma D_6193c : decode_any W_6193c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61940 : bv 32 := 0xfff60613.
Lemma F_61940 : fetch_word Asan.M.loaded_segments (0x61940 : word) = Some W_61940.
Proof. vm_refl. Qed.
Lemma D_61940 : decode_any W_61940 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61944 : bv 32 := 0x00a67633.
Lemma F_61944 : fetch_word Asan.M.loaded_segments (0x61944 : word) = Some W_61944.
Proof. vm_refl. Qed.
Lemma D_61944 : decode_any W_61944 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61948 : bv 32 := 0x04867263.
Lemma F_61948 : fetch_word Asan.M.loaded_segments (0x61948 : word) = Some W_61948.
Proof. vm_refl. Qed.
Lemma D_61948 : decode_any W_61948 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6194c : bv 32 := 0x00074697.
Lemma F_6194c : fetch_word Asan.M.loaded_segments (0x6194c : word) = Some W_6194c.
Proof. vm_refl. Qed.
Lemma D_6194c : decode_any W_6194c = Some (Auipc 13 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61950 : bv 32 := 0xf746b683.
Lemma F_61950 : fetch_word Asan.M.loaded_segments (0x61950 : word) = Some W_61950.
Proof. vm_refl. Qed.
Lemma D_61950 : decode_any W_61950 = Some (Load SZ8 true 13 13 3956, 4%Z).
Proof. vm_refl. Qed.

Definition W_61954 : bv 32 := 0x00074717.
Lemma F_61954 : fetch_word Asan.M.loaded_segments (0x61954 : word) = Some W_61954.
Proof. vm_refl. Qed.
Lemma D_61954 : decode_any W_61954 = Some (Auipc 14 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61958 : bv 32 := 0xf7473703.
Lemma F_61958 : fetch_word Asan.M.loaded_segments (0x61958 : word) = Some W_61958.
Proof. vm_refl. Qed.
Lemma D_61958 : decode_any W_61958 = Some (Load SZ8 true 14 14 3956, 4%Z).
Proof. vm_refl. Qed.

Definition W_6195c : bv 32 := 0x0006b803.
Lemma F_6195c : fetch_word Asan.M.loaded_segments (0x6195c : word) = Some W_6195c.
Proof. vm_refl. Qed.
Lemma D_6195c : decode_any W_6195c = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61960 : bv 32 := 0x00073683.
Lemma F_61960 : fetch_word Asan.M.loaded_segments (0x61960 : word) = Some W_61960.
Proof. vm_refl. Qed.
Lemma D_61960 : decode_any W_61960 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61964 : bv 32 := 0xfff80793.
Lemma F_61964 : fetch_word Asan.M.loaded_segments (0x61964 : word) = Some W_61964.
Proof. vm_refl. Qed.
Lemma D_61964 : decode_any W_61964 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61968 : bv 32 := 0x0087f463.
Lemma F_61968 : fetch_word Asan.M.loaded_segments (0x61968 : word) = Some W_61968.
Proof. vm_refl. Qed.
Lemma D_61968 : decode_any W_61968 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6196c : bv 32 := 0x0286f063.
Lemma F_6196c : fetch_word Asan.M.loaded_segments (0x6196c : word) = Some W_6196c.
Proof. vm_refl. Qed.
Lemma D_6196c : decode_any W_6196c = Some (Branch BC_GEU 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61970 : bv 32 := 0x00074717.
Lemma F_61970 : fetch_word Asan.M.loaded_segments (0x61970 : word) = Some W_61970.
Proof. vm_refl. Qed.
Lemma D_61970 : decode_any W_61970 = Some (Auipc 14 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61974 : bv 32 := 0xf6073703.
Lemma F_61974 : fetch_word Asan.M.loaded_segments (0x61974 : word) = Some W_61974.
Proof. vm_refl. Qed.
Lemma D_61974 : decode_any W_61974 = Some (Load SZ8 true 14 14 3936, 4%Z).
Proof. vm_refl. Qed.

Definition W_61978 : bv 32 := 0x00073283.
Lemma F_61978 : fetch_word Asan.M.loaded_segments (0x61978 : word) = Some W_61978.
Proof. vm_refl. Qed.
Lemma D_61978 : decode_any W_61978 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6197c : bv 32 := 0x0032d713.
Lemma F_6197c : fetch_word Asan.M.loaded_segments (0x6197c : word) = Some W_6197c.
Proof. vm_refl. Qed.
Lemma D_6197c : decode_any W_6197c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61980 : bv 32 := 0x00b708b3.
Lemma F_61980 : fetch_word Asan.M.loaded_segments (0x61980 : word) = Some W_61980.
Proof. vm_refl. Qed.
Lemma D_61980 : decode_any W_61980 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61984 : bv 32 := 0x1282e063.
Lemma F_61984 : fetch_word Asan.M.loaded_segments (0x61984 : word) = Some W_61984.
Proof. vm_refl. Qed.
Lemma D_61984 : decode_any W_61984 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_61988 : bv 32 := 0x1088fe63.
Lemma F_61988 : fetch_word Asan.M.loaded_segments (0x61988 : word) = Some W_61988.
Proof. vm_refl. Qed.
Lemma D_61988 : decode_any W_61988 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_6198c : bv 32 := 0x00848933.
Lemma F_6198c : fetch_word Asan.M.loaded_segments (0x6198c : word) = Some W_6198c.
Proof. vm_refl. Qed.
Lemma D_6198c : decode_any W_6198c = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61990 : bv 32 := 0x05267263.
Lemma F_61990 : fetch_word Asan.M.loaded_segments (0x61990 : word) = Some W_61990.
Proof. vm_refl. Qed.
Lemma D_61990 : decode_any W_61990 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_61994 : bv 32 := 0x00074617.
Lemma F_61994 : fetch_word Asan.M.loaded_segments (0x61994 : word) = Some W_61994.
Proof. vm_refl. Qed.
Lemma D_61994 : decode_any W_61994 = Some (Auipc 12 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61998 : bv 32 := 0xf2c63603.
Lemma F_61998 : fetch_word Asan.M.loaded_segments (0x61998 : word) = Some W_61998.
Proof. vm_refl. Qed.
Lemma D_61998 : decode_any W_61998 = Some (Load SZ8 true 12 12 3884, 4%Z).
Proof. vm_refl. Qed.

Definition W_6199c : bv 32 := 0x00074697.
Lemma F_6199c : fetch_word Asan.M.loaded_segments (0x6199c : word) = Some W_6199c.
Proof. vm_refl. Qed.
Lemma D_6199c : decode_any W_6199c = Some (Auipc 13 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_619a0 : bv 32 := 0xf2c6b683.
Lemma F_619a0 : fetch_word Asan.M.loaded_segments (0x619a0 : word) = Some W_619a0.
Proof. vm_refl. Qed.
Lemma D_619a0 : decode_any W_619a0 = Some (Load SZ8 true 13 13 3884, 4%Z).
Proof. vm_refl. Qed.

Definition W_619a4 : bv 32 := 0x00063783.
Lemma F_619a4 : fetch_word Asan.M.loaded_segments (0x619a4 : word) = Some W_619a4.
Proof. vm_refl. Qed.
Lemma D_619a4 : decode_any W_619a4 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_619a8 : bv 32 := 0x0006b603.
Lemma F_619a8 : fetch_word Asan.M.loaded_segments (0x619a8 : word) = Some W_619a8.
Proof. vm_refl. Qed.
Lemma D_619a8 : decode_any W_619a8 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_619ac : bv 32 := 0xfff78713.
Lemma F_619ac : fetch_word Asan.M.loaded_segments (0x619ac : word) = Some W_619ac.
Proof. vm_refl. Qed.
Lemma D_619ac : decode_any W_619ac = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_619b0 : bv 32 := 0x01277463.
Lemma F_619b0 : fetch_word Asan.M.loaded_segments (0x619b0 : word) = Some W_619b0.
Proof. vm_refl. Qed.
Lemma D_619b0 : decode_any W_619b0 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_619b4 : bv 32 := 0x03267063.
Lemma F_619b4 : fetch_word Asan.M.loaded_segments (0x619b4 : word) = Some W_619b4.
Proof. vm_refl. Qed.
Lemma D_619b4 : decode_any W_619b4 = Some (Branch BC_GEU 12 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_619b8 : bv 32 := 0x00074697.
Lemma F_619b8 : fetch_word Asan.M.loaded_segments (0x619b8 : word) = Some W_619b8.
Proof. vm_refl. Qed.
Lemma D_619b8 : decode_any W_619b8 = Some (Auipc 13 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_619bc : bv 32 := 0xf186b683.
Lemma F_619bc : fetch_word Asan.M.loaded_segments (0x619bc : word) = Some W_619bc.
Proof. vm_refl. Qed.
Lemma D_619bc : decode_any W_619bc = Some (Load SZ8 true 13 13 3864, 4%Z).
Proof. vm_refl. Qed.

Definition W_619c0 : bv 32 := 0x0006b883.
Lemma F_619c0 : fetch_word Asan.M.loaded_segments (0x619c0 : word) = Some W_619c0.
Proof. vm_refl. Qed.
Lemma D_619c0 : decode_any W_619c0 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_619c4 : bv 32 := 0x0038d693.
Lemma F_619c4 : fetch_word Asan.M.loaded_segments (0x619c4 : word) = Some W_619c4.
Proof. vm_refl. Qed.
Lemma D_619c4 : decode_any W_619c4 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_619c8 : bv 32 := 0x00b68833.
Lemma F_619c8 : fetch_word Asan.M.loaded_segments (0x619c8 : word) = Some W_619c8.
Proof. vm_refl. Qed.
Lemma D_619c8 : decode_any W_619c8 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_619cc : bv 32 := 0x1328e463.
Lemma F_619cc : fetch_word Asan.M.loaded_segments (0x619cc : word) = Some W_619cc.
Proof. vm_refl. Qed.
Lemma D_619cc : decode_any W_619cc = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_619d0 : bv 32 := 0x13287263.
Lemma F_619d0 : fetch_word Asan.M.loaded_segments (0x619d0 : word) = Some W_619d0.
Proof. vm_refl. Qed.
Lemma D_619d0 : decode_any W_619d0 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_619d4 : bv 32 := 0x23247863.
Lemma F_619d4 : fetch_word Asan.M.loaded_segments (0x619d4 : word) = Some W_619d4.
Proof. vm_refl. Qed.
Lemma D_619d4 : decode_any W_619d4 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_619d8 : bv 32 := 0x00740513.
Lemma F_619d8 : fetch_word Asan.M.loaded_segments (0x619d8 : word) = Some W_619d8.
Proof. vm_refl. Qed.
Lemma D_619d8 : decode_any W_619d8 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_619dc : bv 32 := 0xff857513.
Lemma F_619dc : fetch_word Asan.M.loaded_segments (0x619dc : word) = Some W_619dc.
Proof. vm_refl. Qed.
Lemma D_619dc : decode_any W_619dc = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_619e0 : bv 32 := 0xff897a13.
Lemma F_619e0 : fetch_word Asan.M.loaded_segments (0x619e0 : word) = Some W_619e0.
Proof. vm_refl. Qed.
Lemma D_619e0 : decode_any W_619e0 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_619e4 : bv 32 := 0xa91ff0ef.
Lemma F_619e4 : fetch_word Asan.M.loaded_segments (0x619e4 : word) = Some W_619e4.
Proof. vm_refl. Qed.
Lemma D_619e4 : decode_any W_619e4 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

Definition W_619e8 : bv 32 := 0x00050993.
Lemma F_619e8 : fetch_word Asan.M.loaded_segments (0x619e8 : word) = Some W_619e8.
Proof. vm_refl. Qed.
Lemma D_619e8 : decode_any W_619e8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_619ec : bv 32 := 0x000a0513.
Lemma F_619ec : fetch_word Asan.M.loaded_segments (0x619ec : word) = Some W_619ec.
Proof. vm_refl. Qed.
Lemma D_619ec : decode_any W_619ec = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_619f0 : bv 32 := 0xa85ff0ef.
Lemma F_619f0 : fetch_word Asan.M.loaded_segments (0x619f0 : word) = Some W_619f0.
Proof. vm_refl. Qed.
Lemma D_619f0 : decode_any W_619f0 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

Definition W_619f4 : bv 32 := 0x000ab583.
Lemma F_619f4 : fetch_word Asan.M.loaded_segments (0x619f4 : word) = Some W_619f4.
Proof. vm_refl. Qed.
Lemma D_619f4 : decode_any W_619f4 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_619f8 : bv 32 := 0x00345613.
Lemma F_619f8 : fetch_word Asan.M.loaded_segments (0x619f8 : word) = Some W_619f8.
Proof. vm_refl. Qed.
Lemma D_619f8 : decode_any W_619f8 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_619fc : bv 32 := 0x00c58633.
Lemma F_619fc : fetch_word Asan.M.loaded_segments (0x619fc : word) = Some W_619fc.
Proof. vm_refl. Qed.
Lemma D_619fc : decode_any W_619fc = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a00 : bv 32 := 0x00060603.
Lemma F_61a00 : fetch_word Asan.M.loaded_segments (0x61a00 : word) = Some W_61a00.
Proof. vm_refl. Qed.
Lemma D_61a00 : decode_any W_61a00 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a04 : bv 32 := 0x00060663.
Lemma F_61a04 : fetch_word Asan.M.loaded_segments (0x61a04 : word) = Some W_61a04.
Proof. vm_refl. Qed.
Lemma D_61a04 : decode_any W_61a04 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a08 : bv 32 := 0x00747693.
Lemma F_61a08 : fetch_word Asan.M.loaded_segments (0x61a08 : word) = Some W_61a08.
Proof. vm_refl. Qed.
Lemma D_61a08 : decode_any W_61a08 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a0c : bv 32 := 0x02c6d063.
Lemma F_61a0c : fetch_word Asan.M.loaded_segments (0x61a0c : word) = Some W_61a0c.
Proof. vm_refl. Qed.
Lemma D_61a0c : decode_any W_61a0c = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a10 : bv 32 := 0xfff90913.
Lemma F_61a10 : fetch_word Asan.M.loaded_segments (0x61a10 : word) = Some W_61a10.
Proof. vm_refl. Qed.
Lemma D_61a10 : decode_any W_61a10 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a14 : bv 32 := 0x00395613.
Lemma F_61a14 : fetch_word Asan.M.loaded_segments (0x61a14 : word) = Some W_61a14.
Proof. vm_refl. Qed.
Lemma D_61a14 : decode_any W_61a14 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a18 : bv 32 := 0x00c585b3.
Lemma F_61a18 : fetch_word Asan.M.loaded_segments (0x61a18 : word) = Some W_61a18.
Proof. vm_refl. Qed.
Lemma D_61a18 : decode_any W_61a18 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a1c : bv 32 := 0x00058583.
Lemma F_61a1c : fetch_word Asan.M.loaded_segments (0x61a1c : word) = Some W_61a1c.
Proof. vm_refl. Qed.
Lemma D_61a1c : decode_any W_61a1c = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a20 : bv 32 := 0x04058263.
Lemma F_61a20 : fetch_word Asan.M.loaded_segments (0x61a20 : word) = Some W_61a20.
Proof. vm_refl. Qed.
Lemma D_61a20 : decode_any W_61a20 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a24 : bv 32 := 0x00797613.
Lemma F_61a24 : fetch_word Asan.M.loaded_segments (0x61a24 : word) = Some W_61a24.
Proof. vm_refl. Qed.
Lemma D_61a24 : decode_any W_61a24 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a28 : bv 32 := 0x02b64e63.
Lemma F_61a28 : fetch_word Asan.M.loaded_segments (0x61a28 : word) = Some W_61a28.
Proof. vm_refl. Qed.
Lemma D_61a28 : decode_any W_61a28 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a2c : bv 32 := 0x000ab503.
Lemma F_61a2c : fetch_word Asan.M.loaded_segments (0x61a2c : word) = Some W_61a2c.
Proof. vm_refl. Qed.
Lemma D_61a2c : decode_any W_61a2c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a30 : bv 32 := 0x00040593.
Lemma F_61a30 : fetch_word Asan.M.loaded_segments (0x61a30 : word) = Some W_61a30.
Proof. vm_refl. Qed.
Lemma D_61a30 : decode_any W_61a30 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a34 : bv 32 := 0x0140006f.
Lemma F_61a34 : fetch_word Asan.M.loaded_segments (0x61a34 : word) = Some W_61a34.
Proof. vm_refl. Qed.
Lemma D_61a34 : decode_any W_61a34 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a38 : bv 32 := 0x00140413.
Lemma F_61a38 : fetch_word Asan.M.loaded_segments (0x61a38 : word) = Some W_61a38.
Proof. vm_refl. Qed.
Lemma D_61a38 : decode_any W_61a38 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a3c : bv 32 := 0xfff48493.
Lemma F_61a3c : fetch_word Asan.M.loaded_segments (0x61a3c : word) = Some W_61a3c.
Proof. vm_refl. Qed.
Lemma D_61a3c : decode_any W_61a3c = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a40 : bv 32 := 0x00158593.
Lemma F_61a40 : fetch_word Asan.M.loaded_segments (0x61a40 : word) = Some W_61a40.
Proof. vm_refl. Qed.
Lemma D_61a40 : decode_any W_61a40 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a44 : bv 32 := 0x1e048063.
Lemma F_61a44 : fetch_word Asan.M.loaded_segments (0x61a44 : word) = Some W_61a44.
Proof. vm_refl. Qed.
Lemma D_61a44 : decode_any W_61a44 = Some (Branch BC_EQ 9 0 480, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a48 : bv 32 := 0x00345613.
Lemma F_61a48 : fetch_word Asan.M.loaded_segments (0x61a48 : word) = Some W_61a48.
Proof. vm_refl. Qed.
Lemma D_61a48 : decode_any W_61a48 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a4c : bv 32 := 0x00c50633.
Lemma F_61a4c : fetch_word Asan.M.loaded_segments (0x61a4c : word) = Some W_61a4c.
Proof. vm_refl. Qed.
Lemma D_61a4c : decode_any W_61a4c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a50 : bv 32 := 0x00060603.
Lemma F_61a50 : fetch_word Asan.M.loaded_segments (0x61a50 : word) = Some W_61a50.
Proof. vm_refl. Qed.
Lemma D_61a50 : decode_any W_61a50 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a54 : bv 32 := 0xfe0602e3.
Lemma F_61a54 : fetch_word Asan.M.loaded_segments (0x61a54 : word) = Some W_61a54.
Proof. vm_refl. Qed.
Lemma D_61a54 : decode_any W_61a54 = Some (Branch BC_EQ 12 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a58 : bv 32 := 0x0075f693.
Lemma F_61a58 : fetch_word Asan.M.loaded_segments (0x61a58 : word) = Some W_61a58.
Proof. vm_refl. Qed.
Lemma D_61a58 : decode_any W_61a58 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a5c : bv 32 := 0xfcc6cee3.
Lemma F_61a5c : fetch_word Asan.M.loaded_segments (0x61a5c : word) = Some W_61a5c.
Proof. vm_refl. Qed.
Lemma D_61a5c : decode_any W_61a5c = Some (Branch BC_LT 13 12 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a60 : bv 32 := 0x01c0006f.
Lemma F_61a60 : fetch_word Asan.M.loaded_segments (0x61a60 : word) = Some W_61a60.
Proof. vm_refl. Qed.
Lemma D_61a60 : decode_any W_61a60 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a64 : bv 32 := 0x00a9fa63.
Lemma F_61a64 : fetch_word Asan.M.loaded_segments (0x61a64 : word) = Some W_61a64.
Proof. vm_refl. Qed.
Lemma D_61a64 : decode_any W_61a64 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a68 : bv 32 := 0x413505b3.
Lemma F_61a68 : fetch_word Asan.M.loaded_segments (0x61a68 : word) = Some W_61a68.
Proof. vm_refl. Qed.
Lemma D_61a68 : decode_any W_61a68 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a6c : bv 32 := 0x00098513.
Lemma F_61a6c : fetch_word Asan.M.loaded_segments (0x61a6c : word) = Some W_61a6c.
Proof. vm_refl. Qed.
Lemma D_61a6c : decode_any W_61a6c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a70 : bv 32 := 0x6210f0ef.
Lemma F_61a70 : fetch_word Asan.M.loaded_segments (0x61a70 : word) = Some W_61a70.
Proof. vm_refl. Qed.
Lemma D_61a70 : decode_any W_61a70 = Some (Jal 1 65056, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a74 : bv 32 := 0xfa050ce3.
Lemma F_61a74 : fetch_word Asan.M.loaded_segments (0x61a74 : word) = Some W_61a74.
Proof. vm_refl. Qed.
Lemma D_61a74 : decode_any W_61a74 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a78 : bv 32 := 0x00000413.
Lemma F_61a78 : fetch_word Asan.M.loaded_segments (0x61a78 : word) = Some W_61a78.
Proof. vm_refl. Qed.
Lemma D_61a78 : decode_any W_61a78 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a7c : bv 32 := 0x00040513.
Lemma F_61a7c : fetch_word Asan.M.loaded_segments (0x61a7c : word) = Some W_61a7c.
Proof. vm_refl. Qed.
Lemma D_61a7c : decode_any W_61a7c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a80 : bv 32 := 0x03813083.
Lemma F_61a80 : fetch_word Asan.M.loaded_segments (0x61a80 : word) = Some W_61a80.
Proof. vm_refl. Qed.
Lemma D_61a80 : decode_any W_61a80 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a84 : bv 32 := 0x03013403.
Lemma F_61a84 : fetch_word Asan.M.loaded_segments (0x61a84 : word) = Some W_61a84.
Proof. vm_refl. Qed.
Lemma D_61a84 : decode_any W_61a84 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a88 : bv 32 := 0x02813483.
Lemma F_61a88 : fetch_word Asan.M.loaded_segments (0x61a88 : word) = Some W_61a88.
Proof. vm_refl. Qed.
Lemma D_61a88 : decode_any W_61a88 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a8c : bv 32 := 0x02013903.
Lemma F_61a8c : fetch_word Asan.M.loaded_segments (0x61a8c : word) = Some W_61a8c.
Proof. vm_refl. Qed.
Lemma D_61a8c : decode_any W_61a8c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a90 : bv 32 := 0x01813983.
Lemma F_61a90 : fetch_word Asan.M.loaded_segments (0x61a90 : word) = Some W_61a90.
Proof. vm_refl. Qed.
Lemma D_61a90 : decode_any W_61a90 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a94 : bv 32 := 0x01013a03.
Lemma F_61a94 : fetch_word Asan.M.loaded_segments (0x61a94 : word) = Some W_61a94.
Proof. vm_refl. Qed.
Lemma D_61a94 : decode_any W_61a94 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a98 : bv 32 := 0x00813a83.
Lemma F_61a98 : fetch_word Asan.M.loaded_segments (0x61a98 : word) = Some W_61a98.
Proof. vm_refl. Qed.
Lemma D_61a98 : decode_any W_61a98 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61a9c : bv 32 := 0x04010113.
Lemma F_61a9c : fetch_word Asan.M.loaded_segments (0x61a9c : word) = Some W_61a9c.
Proof. vm_refl. Qed.
Lemma D_61a9c : decode_any W_61a9c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_61aa0 : bv 32 := 0x00008067.
Lemma F_61aa0 : fetch_word Asan.M.loaded_segments (0x61aa0 : word) = Some W_61aa0.
Proof. vm_refl. Qed.
Lemma D_61aa0 : decode_any W_61aa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61aa4 : bv 32 := 0x00074297.
Lemma F_61aa4 : fetch_word Asan.M.loaded_segments (0x61aa4 : word) = Some W_61aa4.
Proof. vm_refl. Qed.
Lemma D_61aa4 : decode_any W_61aa4 = Some (Auipc 5 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61aa8 : bv 32 := 0xe0c2b283.
Lemma F_61aa8 : fetch_word Asan.M.loaded_segments (0x61aa8 : word) = Some W_61aa8.
Proof. vm_refl. Qed.
Lemma D_61aa8 : decode_any W_61aa8 = Some (Load SZ8 true 5 5 3596, 4%Z).
Proof. vm_refl. Qed.

Definition W_61aac : bv 32 := 0x04e2c283.
Lemma F_61aac : fetch_word Asan.M.loaded_segments (0x61aac : word) = Some W_61aac.
Proof. vm_refl. Qed.
Lemma D_61aac : decode_any W_61aac = Some (Load SZ1 false 5 5 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ab0 : bv 32 := 0xfc0296e3.
Lemma F_61ab0 : fetch_word Asan.M.loaded_segments (0x61ab0 : word) = Some W_61ab0.
Proof. vm_refl. Qed.
Lemma D_61ab0 : decode_any W_61ab0 = Some (Branch BC_NE 5 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ab4 : bv 32 := 0x08080c63.
Lemma F_61ab4 : fetch_word Asan.M.loaded_segments (0x61ab4 : word) = Some W_61ab4.
Proof. vm_refl. Qed.
Lemma D_61ab4 : decode_any W_61ab4 = Some (Branch BC_EQ 16 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ab8 : bv 32 := 0x00385813.
Lemma F_61ab8 : fetch_word Asan.M.loaded_segments (0x61ab8 : word) = Some W_61ab8.
Proof. vm_refl. Qed.
Lemma D_61ab8 : decode_any W_61ab8 = Some (ShiftImm ALU_SRL 16 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61abc : bv 32 := 0x00a80833.
Lemma F_61abc : fetch_word Asan.M.loaded_segments (0x61abc : word) = Some W_61abc.
Proof. vm_refl. Qed.
Lemma D_61abc : decode_any W_61abc = Some (Op ALU_ADD 16 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ac0 : bv 32 := 0x0e887263.
Lemma F_61ac0 : fetch_word Asan.M.loaded_segments (0x61ac0 : word) = Some W_61ac0.
Proof. vm_refl. Qed.
Lemma D_61ac0 : decode_any W_61ac0 = Some (Branch BC_GEU 16 8 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ac4 : bv 32 := 0x00158813.
Lemma F_61ac4 : fetch_word Asan.M.loaded_segments (0x61ac4 : word) = Some W_61ac4.
Proof. vm_refl. Qed.
Lemma D_61ac4 : decode_any W_61ac4 = Some (OpImm ALU_ADD 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ac8 : bv 32 := 0x0087e863.
Lemma F_61ac8 : fetch_word Asan.M.loaded_segments (0x61ac8 : word) = Some W_61ac8.
Proof. vm_refl. Qed.
Lemma D_61ac8 : decode_any W_61ac8 = Some (Branch BC_LTU 15 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61acc : bv 32 := 0x0036d793.
Lemma F_61acc : fetch_word Asan.M.loaded_segments (0x61acc : word) = Some W_61acc.
Proof. vm_refl. Qed.
Lemma D_61acc : decode_any W_61acc = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ad0 : bv 32 := 0x010787b3.
Lemma F_61ad0 : fetch_word Asan.M.loaded_segments (0x61ad0 : word) = Some W_61ad0.
Proof. vm_refl. Qed.
Lemma D_61ad0 : decode_any W_61ad0 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ad4 : bv 32 := 0xeaf47ce3.
Lemma F_61ad4 : fetch_word Asan.M.loaded_segments (0x61ad4 : word) = Some W_61ad4.
Proof. vm_refl. Qed.
Lemma D_61ad4 : decode_any W_61ad4 = Some (Branch BC_GEU 8 15 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ad8 : bv 32 := 0x00168693.
Lemma F_61ad8 : fetch_word Asan.M.loaded_segments (0x61ad8 : word) = Some W_61ad8.
Proof. vm_refl. Qed.
Lemma D_61ad8 : decode_any W_61ad8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61adc : bv 32 := 0xfad460e3.
Lemma F_61adc : fetch_word Asan.M.loaded_segments (0x61adc : word) = Some W_61adc.
Proof. vm_refl. Qed.
Lemma D_61adc : decode_any W_61adc = Some (Branch BC_LTU 8 13 8096, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ae0 : bv 32 := 0x01070733.
Lemma F_61ae0 : fetch_word Asan.M.loaded_segments (0x61ae0 : word) = Some W_61ae0.
Proof. vm_refl. Qed.
Lemma D_61ae0 : decode_any W_61ae0 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ae4 : bv 32 := 0x00375713.
Lemma F_61ae4 : fetch_word Asan.M.loaded_segments (0x61ae4 : word) = Some W_61ae4.
Proof. vm_refl. Qed.
Lemma D_61ae4 : decode_any W_61ae4 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ae8 : bv 32 := 0x00a70733.
Lemma F_61ae8 : fetch_word Asan.M.loaded_segments (0x61ae8 : word) = Some W_61ae8.
Proof. vm_refl. Qed.
Lemma D_61ae8 : decode_any W_61ae8 = Some (Op ALU_ADD 14 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61aec : bv 32 := 0xea8770e3.
Lemma F_61aec : fetch_word Asan.M.loaded_segments (0x61aec : word) = Some W_61aec.
Proof. vm_refl. Qed.
Lemma D_61aec : decode_any W_61aec = Some (Branch BC_GEU 14 8 7840, 4%Z).
Proof. vm_refl. Qed.

Definition W_61af0 : bv 32 := 0xf8dff06f.
Lemma F_61af0 : fetch_word Asan.M.loaded_segments (0x61af0 : word) = Some W_61af0.
Proof. vm_refl. Qed.
Lemma D_61af0 : decode_any W_61af0 = Some (Jal 0 2097036, 4%Z).
Proof. vm_refl. Qed.

Definition W_61af4 : bv 32 := 0x00074897.
Lemma F_61af4 : fetch_word Asan.M.loaded_segments (0x61af4 : word) = Some W_61af4.
Proof. vm_refl. Qed.
Lemma D_61af4 : decode_any W_61af4 = Some (Auipc 17 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61af8 : bv 32 := 0xdbc8b883.
Lemma F_61af8 : fetch_word Asan.M.loaded_segments (0x61af8 : word) = Some W_61af8.
Proof. vm_refl. Qed.
Lemma D_61af8 : decode_any W_61af8 = Some (Load SZ8 true 17 17 3516, 4%Z).
Proof. vm_refl. Qed.

Definition W_61afc : bv 32 := 0x04e8c883.
Lemma F_61afc : fetch_word Asan.M.loaded_segments (0x61afc : word) = Some W_61afc.
Proof. vm_refl. Qed.
Lemma D_61afc : decode_any W_61afc = Some (Load SZ1 false 17 17 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b00 : bv 32 := 0x00088663.
Lemma F_61b00 : fetch_word Asan.M.loaded_segments (0x61b00 : word) = Some W_61b00.
Proof. vm_refl. Qed.
Lemma D_61b00 : decode_any W_61b00 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b04 : bv 32 := 0x00090413.
Lemma F_61b04 : fetch_word Asan.M.loaded_segments (0x61b04 : word) = Some W_61b04.
Proof. vm_refl. Qed.
Lemma D_61b04 : decode_any W_61b04 = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b08 : bv 32 := 0xf75ff06f.
Lemma F_61b08 : fetch_word Asan.M.loaded_segments (0x61b08 : word) = Some W_61b08.
Proof. vm_refl. Qed.
Lemma D_61b08 : decode_any W_61b08 = Some (Jal 0 2097012, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b0c : bv 32 := 0x06078663.
Lemma F_61b0c : fetch_word Asan.M.loaded_segments (0x61b0c : word) = Some W_61b0c.
Proof. vm_refl. Qed.
Lemma D_61b0c : decode_any W_61b0c = Some (Branch BC_EQ 15 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b10 : bv 32 := 0x0037d793.
Lemma F_61b10 : fetch_word Asan.M.loaded_segments (0x61b10 : word) = Some W_61b10.
Proof. vm_refl. Qed.
Lemma D_61b10 : decode_any W_61b10 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b14 : bv 32 := 0x00a787b3.
Lemma F_61b14 : fetch_word Asan.M.loaded_segments (0x61b14 : word) = Some W_61b14.
Proof. vm_refl. Qed.
Lemma D_61b14 : decode_any W_61b14 = Some (Op ALU_ADD 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b18 : bv 32 := 0x0b27f463.
Lemma F_61b18 : fetch_word Asan.M.loaded_segments (0x61b18 : word) = Some W_61b18.
Proof. vm_refl. Qed.
Lemma D_61b18 : decode_any W_61b18 = Some (Branch BC_GEU 15 18 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b1c : bv 32 := 0x00158593.
Lemma F_61b1c : fetch_word Asan.M.loaded_segments (0x61b1c : word) = Some W_61b1c.
Proof. vm_refl. Qed.
Lemma D_61b1c : decode_any W_61b1c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b20 : bv 32 := 0x01276863.
Lemma F_61b20 : fetch_word Asan.M.loaded_segments (0x61b20 : word) = Some W_61b20.
Proof. vm_refl. Qed.
Lemma D_61b20 : decode_any W_61b20 = Some (Branch BC_LTU 14 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b24 : bv 32 := 0x00365713.
Lemma F_61b24 : fetch_word Asan.M.loaded_segments (0x61b24 : word) = Some W_61b24.
Proof. vm_refl. Qed.
Lemma D_61b24 : decode_any W_61b24 = Some (ShiftImm ALU_SRL 14 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b28 : bv 32 := 0x00b70733.
Lemma F_61b28 : fetch_word Asan.M.loaded_segments (0x61b28 : word) = Some W_61b28.
Proof. vm_refl. Qed.
Lemma D_61b28 : decode_any W_61b28 = Some (Op ALU_ADD 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b2c : bv 32 := 0xeae974e3.
Lemma F_61b2c : fetch_word Asan.M.loaded_segments (0x61b2c : word) = Some W_61b2c.
Proof. vm_refl. Qed.
Lemma D_61b2c : decode_any W_61b2c = Some (Branch BC_GEU 18 14 7848, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b30 : bv 32 := 0x00160613.
Lemma F_61b30 : fetch_word Asan.M.loaded_segments (0x61b30 : word) = Some W_61b30.
Proof. vm_refl. Qed.
Lemma D_61b30 : decode_any W_61b30 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b34 : bv 32 := 0xfcc968e3.
Lemma F_61b34 : fetch_word Asan.M.loaded_segments (0x61b34 : word) = Some W_61b34.
Proof. vm_refl. Qed.
Lemma D_61b34 : decode_any W_61b34 = Some (Branch BC_LTU 18 12 8144, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b38 : bv 32 := 0x00b685b3.
Lemma F_61b38 : fetch_word Asan.M.loaded_segments (0x61b38 : word) = Some W_61b38.
Proof. vm_refl. Qed.
Lemma D_61b38 : decode_any W_61b38 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b3c : bv 32 := 0x0035d593.
Lemma F_61b3c : fetch_word Asan.M.loaded_segments (0x61b3c : word) = Some W_61b3c.
Proof. vm_refl. Qed.
Lemma D_61b3c : decode_any W_61b3c = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b40 : bv 32 := 0x00a58533.
Lemma F_61b40 : fetch_word Asan.M.loaded_segments (0x61b40 : word) = Some W_61b40.
Proof. vm_refl. Qed.
Lemma D_61b40 : decode_any W_61b40 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b44 : bv 32 := 0xe92578e3.
Lemma F_61b44 : fetch_word Asan.M.loaded_segments (0x61b44 : word) = Some W_61b44.
Proof. vm_refl. Qed.
Lemma D_61b44 : decode_any W_61b44 = Some (Branch BC_GEU 10 18 7824, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b48 : bv 32 := 0xfbdff06f.
Lemma F_61b48 : fetch_word Asan.M.loaded_segments (0x61b48 : word) = Some W_61b48.
Proof. vm_refl. Qed.
Lemma D_61b48 : decode_any W_61b48 = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b4c : bv 32 := 0x08058863.
Lemma F_61b4c : fetch_word Asan.M.loaded_segments (0x61b4c : word) = Some W_61b4c.
Proof. vm_refl. Qed.
Lemma D_61b4c : decode_any W_61b4c = Some (Branch BC_EQ 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b50 : bv 32 := 0x00355693.
Lemma F_61b50 : fetch_word Asan.M.loaded_segments (0x61b50 : word) = Some W_61b50.
Proof. vm_refl. Qed.
Lemma D_61b50 : decode_any W_61b50 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b54 : bv 32 := 0x00b686b3.
Lemma F_61b54 : fetch_word Asan.M.loaded_segments (0x61b54 : word) = Some W_61b54.
Proof. vm_refl. Qed.
Lemma D_61b54 : decode_any W_61b54 = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b58 : bv 32 := 0x00068663.
Lemma F_61b58 : fetch_word Asan.M.loaded_segments (0x61b58 : word) = Some W_61b58.
Proof. vm_refl. Qed.
Lemma D_61b58 : decode_any W_61b58 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b5c : bv 32 := 0x00168693.
Lemma F_61b5c : fetch_word Asan.M.loaded_segments (0x61b5c : word) = Some W_61b5c.
Proof. vm_refl. Qed.
Lemma D_61b5c : decode_any W_61b5c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b60 : bv 32 := 0xf0d46ee3.
Lemma F_61b60 : fetch_word Asan.M.loaded_segments (0x61b60 : word) = Some W_61b60.
Proof. vm_refl. Qed.
Lemma D_61b60 : decode_any W_61b60 = Some (Branch BC_LTU 8 13 7964, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b64 : bv 32 := 0x00188893.
Lemma F_61b64 : fetch_word Asan.M.loaded_segments (0x61b64 : word) = Some W_61b64.
Proof. vm_refl. Qed.
Lemma D_61b64 : decode_any W_61b64 = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b68 : bv 32 := 0x0038d693.
Lemma F_61b68 : fetch_word Asan.M.loaded_segments (0x61b68 : word) = Some W_61b68.
Proof. vm_refl. Qed.
Lemma D_61b68 : decode_any W_61b68 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b6c : bv 32 := 0x00a686b3.
Lemma F_61b6c : fetch_word Asan.M.loaded_segments (0x61b6c : word) = Some W_61b6c.
Proof. vm_refl. Qed.
Lemma D_61b6c : decode_any W_61b6c = Some (Op ALU_ADD 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b70 : bv 32 := 0xe086fee3.
Lemma F_61b70 : fetch_word Asan.M.loaded_segments (0x61b70 : word) = Some W_61b70.
Proof. vm_refl. Qed.
Lemma D_61b70 : decode_any W_61b70 = Some (Branch BC_GEU 13 8 7708, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b74 : bv 32 := 0xf09ff06f.
Lemma F_61b74 : fetch_word Asan.M.loaded_segments (0x61b74 : word) = Some W_61b74.
Proof. vm_refl. Qed.
Lemma D_61b74 : decode_any W_61b74 = Some (Jal 0 2096904, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b78 : bv 32 := 0x06058c63.
Lemma F_61b78 : fetch_word Asan.M.loaded_segments (0x61b78 : word) = Some W_61b78.
Proof. vm_refl. Qed.
Lemma D_61b78 : decode_any W_61b78 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b7c : bv 32 := 0x00355613.
Lemma F_61b7c : fetch_word Asan.M.loaded_segments (0x61b7c : word) = Some W_61b7c.
Proof. vm_refl. Qed.
Lemma D_61b7c : decode_any W_61b7c = Some (ShiftImm ALU_SRL 12 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b80 : bv 32 := 0x00b605b3.
Lemma F_61b80 : fetch_word Asan.M.loaded_segments (0x61b80 : word) = Some W_61b80.
Proof. vm_refl. Qed.
Lemma D_61b80 : decode_any W_61b80 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b84 : bv 32 := 0x00058663.
Lemma F_61b84 : fetch_word Asan.M.loaded_segments (0x61b84 : word) = Some W_61b84.
Proof. vm_refl. Qed.
Lemma D_61b84 : decode_any W_61b84 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b88 : bv 32 := 0x00158593.
Lemma F_61b88 : fetch_word Asan.M.loaded_segments (0x61b88 : word) = Some W_61b88.
Proof. vm_refl. Qed.
Lemma D_61b88 : decode_any W_61b88 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b8c : bv 32 := 0xf6b96ce3.
Lemma F_61b8c : fetch_word Asan.M.loaded_segments (0x61b8c : word) = Some W_61b8c.
Proof. vm_refl. Qed.
Lemma D_61b8c : decode_any W_61b8c = Some (Branch BC_LTU 18 11 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b90 : bv 32 := 0x00180813.
Lemma F_61b90 : fetch_word Asan.M.loaded_segments (0x61b90 : word) = Some W_61b90.
Proof. vm_refl. Qed.
Lemma D_61b90 : decode_any W_61b90 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b94 : bv 32 := 0x00385593.
Lemma F_61b94 : fetch_word Asan.M.loaded_segments (0x61b94 : word) = Some W_61b94.
Proof. vm_refl. Qed.
Lemma D_61b94 : decode_any W_61b94 = Some (ShiftImm ALU_SRL 11 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b98 : bv 32 := 0x00a58533.
Lemma F_61b98 : fetch_word Asan.M.loaded_segments (0x61b98 : word) = Some W_61b98.
Proof. vm_refl. Qed.
Lemma D_61b98 : decode_any W_61b98 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_61b9c : bv 32 := 0xe3257ce3.
Lemma F_61b9c : fetch_word Asan.M.loaded_segments (0x61b9c : word) = Some W_61b9c.
Proof. vm_refl. Qed.
Lemma D_61b9c : decode_any W_61b9c = Some (Branch BC_GEU 10 18 7736, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ba0 : bv 32 := 0xf65ff06f.
Lemma F_61ba0 : fetch_word Asan.M.loaded_segments (0x61ba0 : word) = Some W_61ba0.
Proof. vm_refl. Qed.
Lemma D_61ba0 : decode_any W_61ba0 = Some (Jal 0 2096996, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ba4 : bv 32 := 0xde0584e3.
Lemma F_61ba4 : fetch_word Asan.M.loaded_segments (0x61ba4 : word) = Some W_61ba4.
Proof. vm_refl. Qed.
Lemma D_61ba4 : decode_any W_61ba4 = Some (Branch BC_EQ 11 0 7656, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ba8 : bv 32 := 0x00355693.
Lemma F_61ba8 : fetch_word Asan.M.loaded_segments (0x61ba8 : word) = Some W_61ba8.
Proof. vm_refl. Qed.
Lemma D_61ba8 : decode_any W_61ba8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bac : bv 32 := 0x00b686b3.
Lemma F_61bac : fetch_word Asan.M.loaded_segments (0x61bac : word) = Some W_61bac.
Proof. vm_refl. Qed.
Lemma D_61bac : decode_any W_61bac = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bb0 : bv 32 := 0xdc068ee3.
Lemma F_61bb0 : fetch_word Asan.M.loaded_segments (0x61bb0 : word) = Some W_61bb0.
Proof. vm_refl. Qed.
Lemma D_61bb0 : decode_any W_61bb0 = Some (Branch BC_EQ 13 0 7644, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bb4 : bv 32 := 0x00168693.
Lemma F_61bb4 : fetch_word Asan.M.loaded_segments (0x61bb4 : word) = Some W_61bb4.
Proof. vm_refl. Qed.
Lemma D_61bb4 : decode_any W_61bb4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bb8 : bv 32 := 0xecd462e3.
Lemma F_61bb8 : fetch_word Asan.M.loaded_segments (0x61bb8 : word) = Some W_61bb8.
Proof. vm_refl. Qed.
Lemma D_61bb8 : decode_any W_61bb8 = Some (Branch BC_LTU 8 13 7876, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bbc : bv 32 := 0xdd1ff06f.
Lemma F_61bbc : fetch_word Asan.M.loaded_segments (0x61bbc : word) = Some W_61bbc.
Proof. vm_refl. Qed.
Lemma D_61bbc : decode_any W_61bbc = Some (Jal 0 2096592, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bc0 : bv 32 := 0xe0058ae3.
Lemma F_61bc0 : fetch_word Asan.M.loaded_segments (0x61bc0 : word) = Some W_61bc0.
Proof. vm_refl. Qed.
Lemma D_61bc0 : decode_any W_61bc0 = Some (Branch BC_EQ 11 0 7700, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bc4 : bv 32 := 0x00355513.
Lemma F_61bc4 : fetch_word Asan.M.loaded_segments (0x61bc4 : word) = Some W_61bc4.
Proof. vm_refl. Qed.
Lemma D_61bc4 : decode_any W_61bc4 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bc8 : bv 32 := 0x00b505b3.
Lemma F_61bc8 : fetch_word Asan.M.loaded_segments (0x61bc8 : word) = Some W_61bc8.
Proof. vm_refl. Qed.
Lemma D_61bc8 : decode_any W_61bc8 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bcc : bv 32 := 0xe00584e3.
Lemma F_61bcc : fetch_word Asan.M.loaded_segments (0x61bcc : word) = Some W_61bcc.
Proof. vm_refl. Qed.
Lemma D_61bcc : decode_any W_61bcc = Some (Branch BC_EQ 11 0 7688, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bd0 : bv 32 := 0x00158593.
Lemma F_61bd0 : fetch_word Asan.M.loaded_segments (0x61bd0 : word) = Some W_61bd0.
Proof. vm_refl. Qed.
Lemma D_61bd0 : decode_any W_61bd0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bd4 : bv 32 := 0xf2b968e3.
Lemma F_61bd4 : fetch_word Asan.M.loaded_segments (0x61bd4 : word) = Some W_61bd4.
Proof. vm_refl. Qed.
Lemma D_61bd4 : decode_any W_61bd4 = Some (Branch BC_LTU 18 11 7984, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bd8 : bv 32 := 0xdfdff06f.
Lemma F_61bd8 : fetch_word Asan.M.loaded_segments (0x61bd8 : word) = Some W_61bd8.
Proof. vm_refl. Qed.
Lemma D_61bd8 : decode_any W_61bd8 = Some (Jal 0 2096636, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bdc : bv 32 := 0x00170713.
Lemma F_61bdc : fetch_word Asan.M.loaded_segments (0x61bdc : word) = Some W_61bdc.
Proof. vm_refl. Qed.
Lemma D_61bdc : decode_any W_61bdc = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61be0 : bv 32 := 0x00375713.
Lemma F_61be0 : fetch_word Asan.M.loaded_segments (0x61be0 : word) = Some W_61be0.
Proof. vm_refl. Qed.
Lemma D_61be0 : decode_any W_61be0 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61be4 : bv 32 := 0xfff70713.
Lemma F_61be4 : fetch_word Asan.M.loaded_segments (0x61be4 : word) = Some W_61be4.
Proof. vm_refl. Qed.
Lemma D_61be4 : decode_any W_61be4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61be8 : bv 32 := 0xda8772e3.
Lemma F_61be8 : fetch_word Asan.M.loaded_segments (0x61be8 : word) = Some W_61be8.
Proof. vm_refl. Qed.
Lemma D_61be8 : decode_any W_61be8 = Some (Branch BC_GEU 14 8 7588, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bec : bv 32 := 0xe91ff06f.
Lemma F_61bec : fetch_word Asan.M.loaded_segments (0x61bec : word) = Some W_61bec.
Proof. vm_refl. Qed.
Lemma D_61bec : decode_any W_61bec = Some (Jal 0 2096784, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bf0 : bv 32 := 0x00168693.
Lemma F_61bf0 : fetch_word Asan.M.loaded_segments (0x61bf0 : word) = Some W_61bf0.
Proof. vm_refl. Qed.
Lemma D_61bf0 : decode_any W_61bf0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bf4 : bv 32 := 0x0036d693.
Lemma F_61bf4 : fetch_word Asan.M.loaded_segments (0x61bf4 : word) = Some W_61bf4.
Proof. vm_refl. Qed.
Lemma D_61bf4 : decode_any W_61bf4 = Some (ShiftImm ALU_SRL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bf8 : bv 32 := 0xfff68693.
Lemma F_61bf8 : fetch_word Asan.M.loaded_segments (0x61bf8 : word) = Some W_61bf8.
Proof. vm_refl. Qed.
Lemma D_61bf8 : decode_any W_61bf8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61bfc : bv 32 := 0xdd26fce3.
Lemma F_61bfc : fetch_word Asan.M.loaded_segments (0x61bfc : word) = Some W_61bfc.
Proof. vm_refl. Qed.
Lemma D_61bfc : decode_any W_61bfc = Some (Branch BC_GEU 13 18 7640, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c00 : bv 32 := 0xf05ff06f.
Lemma F_61c00 : fetch_word Asan.M.loaded_segments (0x61c00 : word) = Some W_61c00.
Proof. vm_refl. Qed.
Lemma D_61c00 : decode_any W_61c00 = Some (Jal 0 2096900, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c04 : bv 32 := 0xfffbf517.
Lemma F_61c04 : fetch_word Asan.M.loaded_segments (0x61c04 : word) = Some W_61c04.
Proof. vm_refl. Qed.
Lemma D_61c04 : decode_any W_61c04 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c08 : bv 32 := 0xfffc0597.
Lemma F_61c08 : fetch_word Asan.M.loaded_segments (0x61c08 : word) = Some W_61c08.
Proof. vm_refl. Qed.
Lemma D_61c08 : decode_any W_61c08 = Some (Auipc 11 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c0c : bv 32 := 0x06850513.
Lemma F_61c0c : fetch_word Asan.M.loaded_segments (0x61c0c : word) = Some W_61c0c.
Proof. vm_refl. Qed.
Lemma D_61c0c : decode_any W_61c0c = Some (OpImm ALU_ADD 10 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c10 : bv 32 := 0x14d58613.
Lemma F_61c10 : fetch_word Asan.M.loaded_segments (0x61c10 : word) = Some W_61c10.
Proof. vm_refl. Qed.
Lemma D_61c10 : decode_any W_61c10 = Some (OpImm ALU_ADD 12 11 333, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c14 : bv 32 := 0x0be00593.
Lemma F_61c14 : fetch_word Asan.M.loaded_segments (0x61c14 : word) = Some W_61c14.
Proof. vm_refl. Qed.
Lemma D_61c14 : decode_any W_61c14 = Some (OpImm ALU_ADD 11 0 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c18 : bv 32 := 0x00040693.
Lemma F_61c18 : fetch_word Asan.M.loaded_segments (0x61c18 : word) = Some W_61c18.
Proof. vm_refl. Qed.
Lemma D_61c18 : decode_any W_61c18 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c1c : bv 32 := 0x00090713.
Lemma F_61c1c : fetch_word Asan.M.loaded_segments (0x61c1c : word) = Some W_61c1c.
Proof. vm_refl. Qed.
Lemma D_61c1c : decode_any W_61c1c = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c20 : bv 32 := 0x448170ef.
Lemma F_61c20 : fetch_word Asan.M.loaded_segments (0x61c20 : word) = Some W_61c20.
Proof. vm_refl. Qed.
Lemma D_61c20 : decode_any W_61c20 = Some (Jal 1 95304, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c24 : bv 32 := 0xfffbf517.
Lemma F_61c24 : fetch_word Asan.M.loaded_segments (0x61c24 : word) = Some W_61c24.
Proof. vm_refl. Qed.
Lemma D_61c24 : decode_any W_61c24 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c28 : bv 32 := 0xfffb4597.
Lemma F_61c28 : fetch_word Asan.M.loaded_segments (0x61c28 : word) = Some W_61c28.
Proof. vm_refl. Qed.
Lemma D_61c28 : decode_any W_61c28 = Some (Auipc 11 1048500, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c2c : bv 32 := 0x04850513.
Lemma F_61c2c : fetch_word Asan.M.loaded_segments (0x61c2c : word) = Some W_61c2c.
Proof. vm_refl. Qed.
Lemma D_61c2c : decode_any W_61c2c = Some (OpImm ALU_ADD 10 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c30 : bv 32 := 0xebe58613.
Lemma F_61c30 : fetch_word Asan.M.loaded_segments (0x61c30 : word) = Some W_61c30.
Proof. vm_refl. Qed.
Lemma D_61c30 : decode_any W_61c30 = Some (OpImm ALU_ADD 12 11 3774, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c34 : bv 32 := 0x0d000593.
Lemma F_61c34 : fetch_word Asan.M.loaded_segments (0x61c34 : word) = Some W_61c34.
Proof. vm_refl. Qed.
Lemma D_61c34 : decode_any W_61c34 = Some (OpImm ALU_ADD 11 0 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c38 : bv 32 := 0x00000693.
Lemma F_61c38 : fetch_word Asan.M.loaded_segments (0x61c38 : word) = Some W_61c38.
Proof. vm_refl. Qed.
Lemma D_61c38 : decode_any W_61c38 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c3c : bv 32 := 0x00000713.
Lemma F_61c3c : fetch_word Asan.M.loaded_segments (0x61c3c : word) = Some W_61c3c.
Proof. vm_refl. Qed.
Lemma D_61c3c : decode_any W_61c3c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61c40 : bv 32 := 0x428170ef.
Lemma F_61c40 : fetch_word Asan.M.loaded_segments (0x61c40 : word) = Some W_61c40.
Proof. vm_refl. Qed.
Lemma D_61c40 : decode_any W_61c40 = Some (Jal 1 95272, 4%Z).
Proof. vm_refl. Qed.
