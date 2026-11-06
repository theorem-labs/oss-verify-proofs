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

Definition W_71890 : bv 32 := 0xff010113.
Lemma F_71890 : fetch_word Asan.M.loaded_segments (0x71890 : word) = Some W_71890.
Proof. vm_refl. Qed.
Lemma D_71890 : decode_any W_71890 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_71894 : bv 32 := 0x00113423.
Lemma F_71894 : fetch_word Asan.M.loaded_segments (0x71894 : word) = Some W_71894.
Proof. vm_refl. Qed.
Lemma D_71894 : decode_any W_71894 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_71898 : bv 32 := 0x00058693.
Lemma F_71898 : fetch_word Asan.M.loaded_segments (0x71898 : word) = Some W_71898.
Proof. vm_refl. Qed.
Lemma D_71898 : decode_any W_71898 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7189c : bv 32 := 0x00100713.
Lemma F_7189c : fetch_word Asan.M.loaded_segments (0x7189c : word) = Some W_7189c.
Proof. vm_refl. Qed.
Lemma D_7189c : decode_any W_7189c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_718a0 : bv 32 := 0x02871713.
Lemma F_718a0 : fetch_word Asan.M.loaded_segments (0x718a0 : word) = Some W_718a0.
Proof. vm_refl. Qed.
Lemma D_718a0 : decode_any W_718a0 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_718a4 : bv 32 := 0x00170593.
Lemma F_718a4 : fetch_word Asan.M.loaded_segments (0x718a4 : word) = Some W_718a4.
Proof. vm_refl. Qed.
Lemma D_718a4 : decode_any W_718a4 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_718a8 : bv 32 := 0x08b6f263.
Lemma F_718a8 : fetch_word Asan.M.loaded_segments (0x718a8 : word) = Some W_718a8.
Proof. vm_refl. Qed.
Lemma D_718a8 : decode_any W_718a8 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_718ac : bv 32 := 0x00000593.
Lemma F_718ac : fetch_word Asan.M.loaded_segments (0x718ac : word) = Some W_718ac.
Proof. vm_refl. Qed.
Lemma D_718ac : decode_any W_718ac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_718b0 : bv 32 := 0x00d50733.
Lemma F_718b0 : fetch_word Asan.M.loaded_segments (0x718b0 : word) = Some W_718b0.
Proof. vm_refl. Qed.
Lemma D_718b0 : decode_any W_718b0 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_718b4 : bv 32 := 0x00750793.
Lemma F_718b4 : fetch_word Asan.M.loaded_segments (0x718b4 : word) = Some W_718b4.
Proof. vm_refl. Qed.
Lemma D_718b4 : decode_any W_718b4 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_718b8 : bv 32 := 0xff87f793.
Lemma F_718b8 : fetch_word Asan.M.loaded_segments (0x718b8 : word) = Some W_718b8.
Proof. vm_refl. Qed.
Lemma D_718b8 : decode_any W_718b8 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_718bc : bv 32 := 0xff877613.
Lemma F_718bc : fetch_word Asan.M.loaded_segments (0x718bc : word) = Some W_718bc.
Proof. vm_refl. Qed.
Lemma D_718bc : decode_any W_718bc = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_718c0 : bv 32 := 0x02f57463.
Lemma F_718c0 : fetch_word Asan.M.loaded_segments (0x718c0 : word) = Some W_718c0.
Proof. vm_refl. Qed.
Lemma D_718c0 : decode_any W_718c0 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_718c4 : bv 32 := 0x02068263.
Lemma F_718c4 : fetch_word Asan.M.loaded_segments (0x718c4 : word) = Some W_718c4.
Proof. vm_refl. Qed.
Lemma D_718c4 : decode_any W_718c4 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_718c8 : bv 32 := 0x00000593.
Lemma F_718c8 : fetch_word Asan.M.loaded_segments (0x718c8 : word) = Some W_718c8.
Proof. vm_refl. Qed.
Lemma D_718c8 : decode_any W_718c8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_718cc : bv 32 := 0x00150693.
Lemma F_718cc : fetch_word Asan.M.loaded_segments (0x718cc : word) = Some W_718cc.
Proof. vm_refl. Qed.
Lemma D_718cc : decode_any W_718cc = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_718d0 : bv 32 := 0x00068813.
Lemma F_718d0 : fetch_word Asan.M.loaded_segments (0x718d0 : word) = Some W_718d0.
Proof. vm_refl. Qed.
Lemma D_718d0 : decode_any W_718d0 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_718d4 : bv 32 := 0xfff6c683.
Lemma F_718d4 : fetch_word Asan.M.loaded_segments (0x718d4 : word) = Some W_718d4.
Proof. vm_refl. Qed.
Lemma D_718d4 : decode_any W_718d4 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_718d8 : bv 32 := 0x00d5e5b3.
Lemma F_718d8 : fetch_word Asan.M.loaded_segments (0x718d8 : word) = Some W_718d8.
Proof. vm_refl. Qed.
Lemma D_718d8 : decode_any W_718d8 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_718dc : bv 32 := 0x00f87663.
Lemma F_718dc : fetch_word Asan.M.loaded_segments (0x718dc : word) = Some W_718dc.
Proof. vm_refl. Qed.
Lemma D_718dc : decode_any W_718dc = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_718e0 : bv 32 := 0x00180693.
Lemma F_718e0 : fetch_word Asan.M.loaded_segments (0x718e0 : word) = Some W_718e0.
Proof. vm_refl. Qed.
Lemma D_718e0 : decode_any W_718e0 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_718e4 : bv 32 := 0xfee866e3.
Lemma F_718e4 : fetch_word Asan.M.loaded_segments (0x718e4 : word) = Some W_718e4.
Proof. vm_refl. Qed.
Lemma D_718e4 : decode_any W_718e4 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_718e8 : bv 32 := 0x00c7fa63.
Lemma F_718e8 : fetch_word Asan.M.loaded_segments (0x718e8 : word) = Some W_718e8.
Proof. vm_refl. Qed.
Lemma D_718e8 : decode_any W_718e8 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_718ec : bv 32 := 0x0007b683.
Lemma F_718ec : fetch_word Asan.M.loaded_segments (0x718ec : word) = Some W_718ec.
Proof. vm_refl. Qed.
Lemma D_718ec : decode_any W_718ec = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_718f0 : bv 32 := 0x00878793.
Lemma F_718f0 : fetch_word Asan.M.loaded_segments (0x718f0 : word) = Some W_718f0.
Proof. vm_refl. Qed.
Lemma D_718f0 : decode_any W_718f0 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_718f4 : bv 32 := 0x00b6e5b3.
Lemma F_718f4 : fetch_word Asan.M.loaded_segments (0x718f4 : word) = Some W_718f4.
Proof. vm_refl. Qed.
Lemma D_718f4 : decode_any W_718f4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_718f8 : bv 32 := 0xfec7eae3.
Lemma F_718f8 : fetch_word Asan.M.loaded_segments (0x718f8 : word) = Some W_718f8.
Proof. vm_refl. Qed.
Lemma D_718f8 : decode_any W_718f8 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_718fc : bv 32 := 0x02a66063.
Lemma F_718fc : fetch_word Asan.M.loaded_segments (0x718fc : word) = Some W_718fc.
Proof. vm_refl. Qed.
Lemma D_718fc : decode_any W_718fc = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_71900 : bv 32 := 0x00e67e63.
Lemma F_71900 : fetch_word Asan.M.loaded_segments (0x71900 : word) = Some W_71900.
Proof. vm_refl. Qed.
Lemma D_71900 : decode_any W_71900 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_71904 : bv 32 := 0x40c70733.
Lemma F_71904 : fetch_word Asan.M.loaded_segments (0x71904 : word) = Some W_71904.
Proof. vm_refl. Qed.
Lemma D_71904 : decode_any W_71904 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71908 : bv 32 := 0x00064503.
Lemma F_71908 : fetch_word Asan.M.loaded_segments (0x71908 : word) = Some W_71908.
Proof. vm_refl. Qed.
Lemma D_71908 : decode_any W_71908 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7190c : bv 32 := 0xfff70713.
Lemma F_7190c : fetch_word Asan.M.loaded_segments (0x7190c : word) = Some W_7190c.
Proof. vm_refl. Qed.
Lemma D_7190c : decode_any W_7190c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_71910 : bv 32 := 0x00a5e5b3.
Lemma F_71910 : fetch_word Asan.M.loaded_segments (0x71910 : word) = Some W_71910.
Proof. vm_refl. Qed.
Lemma D_71910 : decode_any W_71910 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_71914 : bv 32 := 0x00160613.
Lemma F_71914 : fetch_word Asan.M.loaded_segments (0x71914 : word) = Some W_71914.
Proof. vm_refl. Qed.
Lemma D_71914 : decode_any W_71914 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71918 : bv 32 := 0xfe0718e3.
Lemma F_71918 : fetch_word Asan.M.loaded_segments (0x71918 : word) = Some W_71918.
Proof. vm_refl. Qed.
Lemma D_71918 : decode_any W_71918 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7191c : bv 32 := 0x0015b513.
Lemma F_7191c : fetch_word Asan.M.loaded_segments (0x7191c : word) = Some W_7191c.
Proof. vm_refl. Qed.
Lemma D_7191c : decode_any W_7191c = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71920 : bv 32 := 0x00813083.
Lemma F_71920 : fetch_word Asan.M.loaded_segments (0x71920 : word) = Some W_71920.
Proof. vm_refl. Qed.
Lemma D_71920 : decode_any W_71920 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_71924 : bv 32 := 0x01010113.
Lemma F_71924 : fetch_word Asan.M.loaded_segments (0x71924 : word) = Some W_71924.
Proof. vm_refl. Qed.
Lemma D_71924 : decode_any W_71924 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_71928 : bv 32 := 0x00008067.
Lemma F_71928 : fetch_word Asan.M.loaded_segments (0x71928 : word) = Some W_71928.
Proof. vm_refl. Qed.
Lemma D_71928 : decode_any W_71928 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7192c : bv 32 := 0xfffa2517.
Lemma F_7192c : fetch_word Asan.M.loaded_segments (0x7192c : word) = Some W_7192c.
Proof. vm_refl. Qed.
Lemma D_7192c : decode_any W_7192c = Some (Auipc 10 1048482, 4%Z).
Proof. vm_refl. Qed.

Definition W_71930 : bv 32 := 0xfffa7597.
Lemma F_71930 : fetch_word Asan.M.loaded_segments (0x71930 : word) = Some W_71930.
Proof. vm_refl. Qed.
Lemma D_71930 : decode_any W_71930 = Some (Auipc 11 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_71934 : bv 32 := 0xf7a50513.
Lemma F_71934 : fetch_word Asan.M.loaded_segments (0x71934 : word) = Some W_71934.
Proof. vm_refl. Qed.
Lemma D_71934 : decode_any W_71934 = Some (OpImm ALU_ADD 10 10 3962, 4%Z).
Proof. vm_refl. Qed.

Definition W_71938 : bv 32 := 0x7eb58613.
Lemma F_71938 : fetch_word Asan.M.loaded_segments (0x71938 : word) = Some W_71938.
Proof. vm_refl. Qed.
Lemma D_71938 : decode_any W_71938 = Some (OpImm ALU_ADD 12 11 2027, 4%Z).
Proof. vm_refl. Qed.

Definition W_7193c : bv 32 := 0x12b00593.
Lemma F_7193c : fetch_word Asan.M.loaded_segments (0x7193c : word) = Some W_7193c.
Proof. vm_refl. Qed.
Lemma D_7193c : decode_any W_7193c = Some (OpImm ALU_ADD 11 0 299, 4%Z).
Proof. vm_refl. Qed.

Definition W_71940 : bv 32 := 0x728070ef.
Lemma F_71940 : fetch_word Asan.M.loaded_segments (0x71940 : word) = Some W_71940.
Proof. vm_refl. Qed.
Lemma D_71940 : decode_any W_71940 = Some (Jal 1 30504, 4%Z).
Proof. vm_refl. Qed.
