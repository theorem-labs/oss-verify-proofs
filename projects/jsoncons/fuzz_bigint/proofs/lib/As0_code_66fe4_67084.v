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

Definition W_66fe4 : bv 32 := 0xff010113.
Lemma F_66fe4 : fetch_word Asan.M.loaded_segments (0x66fe4 : word) = Some W_66fe4.
Proof. vm_refl. Qed.
Lemma D_66fe4 : decode_any W_66fe4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_66fe8 : bv 32 := 0x00113423.
Lemma F_66fe8 : fetch_word Asan.M.loaded_segments (0x66fe8 : word) = Some W_66fe8.
Proof. vm_refl. Qed.
Lemma D_66fe8 : decode_any W_66fe8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_66fec : bv 32 := 0x00813023.
Lemma F_66fec : fetch_word Asan.M.loaded_segments (0x66fec : word) = Some W_66fec.
Proof. vm_refl. Qed.
Lemma D_66fec : decode_any W_66fec = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66ff0 : bv 32 := 0x00078517.
Lemma F_66ff0 : fetch_word Asan.M.loaded_segments (0x66ff0 : word) = Some W_66ff0.
Proof. vm_refl. Qed.
Lemma D_66ff0 : decode_any W_66ff0 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_66ff4 : bv 32 := 0x82850413.
Lemma F_66ff4 : fetch_word Asan.M.loaded_segments (0x66ff4 : word) = Some W_66ff4.
Proof. vm_refl. Qed.
Lemma D_66ff4 : decode_any W_66ff4 = Some (OpImm ALU_ADD 8 10 2088, 4%Z).
Proof. vm_refl. Qed.

Definition W_66ff8 : bv 32 := 0x00040583.
Lemma F_66ff8 : fetch_word Asan.M.loaded_segments (0x66ff8 : word) = Some W_66ff8.
Proof. vm_refl. Qed.
Lemma D_66ff8 : decode_any W_66ff8 = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66ffc : bv 32 := 0x00100513.
Lemma F_66ffc : fetch_word Asan.M.loaded_segments (0x66ffc : word) = Some W_66ffc.
Proof. vm_refl. Qed.
Lemma D_66ffc : decode_any W_66ffc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67000 : bv 32 := 0x0230000f.
Lemma F_67000 : fetch_word Asan.M.loaded_segments (0x67000 : word) = Some W_67000.
Proof. vm_refl. Qed.
Lemma D_67000 : decode_any W_67000 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67004 : bv 32 := 0x00a59a63.
Lemma F_67004 : fetch_word Asan.M.loaded_segments (0x67004 : word) = Some W_67004.
Proof. vm_refl. Qed.
Lemma D_67004 : decode_any W_67004 = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_67008 : bv 32 := 0x00813083.
Lemma F_67008 : fetch_word Asan.M.loaded_segments (0x67008 : word) = Some W_67008.
Proof. vm_refl. Qed.
Lemma D_67008 : decode_any W_67008 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6700c : bv 32 := 0x00013403.
Lemma F_6700c : fetch_word Asan.M.loaded_segments (0x6700c : word) = Some W_6700c.
Proof. vm_refl. Qed.
Lemma D_6700c : decode_any W_6700c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67010 : bv 32 := 0x01010113.
Lemma F_67010 : fetch_word Asan.M.loaded_segments (0x67010 : word) = Some W_67010.
Proof. vm_refl. Qed.
Lemma D_67010 : decode_any W_67010 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_67014 : bv 32 := 0x00008067.
Lemma F_67014 : fetch_word Asan.M.loaded_segments (0x67014 : word) = Some W_67014.
Proof. vm_refl. Qed.
Lemma D_67014 : decode_any W_67014 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67018 : bv 32 := 0x00240513.
Lemma F_67018 : fetch_word Asan.M.loaded_segments (0x67018 : word) = Some W_67018.
Proof. vm_refl. Qed.
Lemma D_67018 : decode_any W_67018 = Some (OpImm ALU_ADD 10 8 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6701c : bv 32 := 0x00ff05b7.
Lemma F_6701c : fetch_word Asan.M.loaded_segments (0x6701c : word) = Some W_6701c.
Proof. vm_refl. Qed.
Lemma D_6701c : decode_any W_6701c = Some (Lui 11 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_67020 : bv 32 := 0xffc57513.
Lemma F_67020 : fetch_word Asan.M.loaded_segments (0x67020 : word) = Some W_67020.
Proof. vm_refl. Qed.
Lemma D_67020 : decode_any W_67020 = Some (OpImm ALU_AND 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_67024 : bv 32 := 0x00010637.
Lemma F_67024 : fetch_word Asan.M.loaded_segments (0x67024 : word) = Some W_67024.
Proof. vm_refl. Qed.
Lemma D_67024 : decode_any W_67024 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_67028 : bv 32 := 0x140526af.
Lemma F_67028 : fetch_word Asan.M.loaded_segments (0x67028 : word) = Some W_67028.
Proof. vm_refl. Qed.
Lemma D_67028 : decode_any W_67028 = Some (Lr AW true false 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6702c : bv 32 := 0x00060713.
Lemma F_6702c : fetch_word Asan.M.loaded_segments (0x6702c : word) = Some W_6702c.
Proof. vm_refl. Qed.
Lemma D_6702c : decode_any W_6702c = Some (OpImm ALU_ADD 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67030 : bv 32 := 0x00e6c733.
Lemma F_67030 : fetch_word Asan.M.loaded_segments (0x67030 : word) = Some W_67030.
Proof. vm_refl. Qed.
Lemma D_67030 : decode_any W_67030 = Some (Op ALU_XOR 14 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_67034 : bv 32 := 0x00b77733.
Lemma F_67034 : fetch_word Asan.M.loaded_segments (0x67034 : word) = Some W_67034.
Proof. vm_refl. Qed.
Lemma D_67034 : decode_any W_67034 = Some (Op ALU_AND 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_67038 : bv 32 := 0x00e6c733.
Lemma F_67038 : fetch_word Asan.M.loaded_segments (0x67038 : word) = Some W_67038.
Proof. vm_refl. Qed.
Lemma D_67038 : decode_any W_67038 = Some (Op ALU_XOR 14 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6703c : bv 32 := 0x18e5272f.
Lemma F_6703c : fetch_word Asan.M.loaded_segments (0x6703c : word) = Some W_6703c.
Proof. vm_refl. Qed.
Lemma D_6703c : decode_any W_6703c = Some (Sc AW false false 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_67040 : bv 32 := 0xfe0714e3.
Lemma F_67040 : fetch_word Asan.M.loaded_segments (0x67040 : word) = Some W_67040.
Proof. vm_refl. Qed.
Lemma D_67040 : decode_any W_67040 = Some (Branch BC_NE 14 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_67044 : bv 32 := 0x02869693.
Lemma F_67044 : fetch_word Asan.M.loaded_segments (0x67044 : word) = Some W_67044.
Proof. vm_refl. Qed.
Lemma D_67044 : decode_any W_67044 = Some (ShiftImm ALU_SLL 13 13 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_67048 : bv 32 := 0x0386d693.
Lemma F_67048 : fetch_word Asan.M.loaded_segments (0x67048 : word) = Some W_67048.
Proof. vm_refl. Qed.
Lemma D_67048 : decode_any W_67048 = Some (ShiftImm ALU_SRL 13 13 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6704c : bv 32 := 0x00068c63.
Lemma F_6704c : fetch_word Asan.M.loaded_segments (0x6704c : word) = Some W_6704c.
Proof. vm_refl. Qed.
Lemma D_6704c : decode_any W_6704c = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_67050 : bv 32 := 0x00000513.
Lemma F_67050 : fetch_word Asan.M.loaded_segments (0x67050 : word) = Some W_67050.
Proof. vm_refl. Qed.
Lemma D_67050 : decode_any W_67050 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67054 : bv 32 := 0x00813083.
Lemma F_67054 : fetch_word Asan.M.loaded_segments (0x67054 : word) = Some W_67054.
Proof. vm_refl. Qed.
Lemma D_67054 : decode_any W_67054 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_67058 : bv 32 := 0x00013403.
Lemma F_67058 : fetch_word Asan.M.loaded_segments (0x67058 : word) = Some W_67058.
Proof. vm_refl. Qed.
Lemma D_67058 : decode_any W_67058 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6705c : bv 32 := 0x01010113.
Lemma F_6705c : fetch_word Asan.M.loaded_segments (0x6705c : word) = Some W_6705c.
Proof. vm_refl. Qed.
Lemma D_6705c : decode_any W_6705c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_67060 : bv 32 := 0x00008067.
Lemma F_67060 : fetch_word Asan.M.loaded_segments (0x67060 : word) = Some W_67060.
Proof. vm_refl. Qed.
Lemma D_67060 : decode_any W_67060 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67064 : bv 32 := 0xccdff0ef.
Lemma F_67064 : fetch_word Asan.M.loaded_segments (0x67064 : word) = Some W_67064.
Proof. vm_refl. Qed.
Lemma D_67064 : decode_any W_67064 = Some (Jal 1 2096332, 4%Z).
Proof. vm_refl. Qed.

Definition W_67068 : bv 32 := 0x00100513.
Lemma F_67068 : fetch_word Asan.M.loaded_segments (0x67068 : word) = Some W_67068.
Proof. vm_refl. Qed.
Lemma D_67068 : decode_any W_67068 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6706c : bv 32 := 0x0310000f.
Lemma F_6706c : fetch_word Asan.M.loaded_segments (0x6706c : word) = Some W_6706c.
Proof. vm_refl. Qed.
Lemma D_6706c : decode_any W_6706c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67070 : bv 32 := 0x00040123.
Lemma F_67070 : fetch_word Asan.M.loaded_segments (0x67070 : word) = Some W_67070.
Proof. vm_refl. Qed.
Lemma D_67070 : decode_any W_67070 = Some (Store SZ1 8 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_67074 : bv 32 := 0x00813083.
Lemma F_67074 : fetch_word Asan.M.loaded_segments (0x67074 : word) = Some W_67074.
Proof. vm_refl. Qed.
Lemma D_67074 : decode_any W_67074 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_67078 : bv 32 := 0x00013403.
Lemma F_67078 : fetch_word Asan.M.loaded_segments (0x67078 : word) = Some W_67078.
Proof. vm_refl. Qed.
Lemma D_67078 : decode_any W_67078 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6707c : bv 32 := 0x01010113.
Lemma F_6707c : fetch_word Asan.M.loaded_segments (0x6707c : word) = Some W_6707c.
Proof. vm_refl. Qed.
Lemma D_6707c : decode_any W_6707c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_67080 : bv 32 := 0x00008067.
Lemma F_67080 : fetch_word Asan.M.loaded_segments (0x67080 : word) = Some W_67080.
Proof. vm_refl. Qed.
Lemma D_67080 : decode_any W_67080 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
