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

Definition W_712e4 : bv 32 := 0x02060063.
Lemma F_712e4 : fetch_word Asan.M.loaded_segments (0x712e4 : word) = Some W_712e4.
Proof. vm_refl. Qed.
Lemma D_712e4 : decode_any W_712e4 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_712e8 : bv 32 := 0x00c50633.
Lemma F_712e8 : fetch_word Asan.M.loaded_segments (0x712e8 : word) = Some W_712e8.
Proof. vm_refl. Qed.
Lemma D_712e8 : decode_any W_712e8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_712ec : bv 32 := 0x00050693.
Lemma F_712ec : fetch_word Asan.M.loaded_segments (0x712ec : word) = Some W_712ec.
Proof. vm_refl. Qed.
Lemma D_712ec : decode_any W_712ec = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712f0 : bv 32 := 0x0005c703.
Lemma F_712f0 : fetch_word Asan.M.loaded_segments (0x712f0 : word) = Some W_712f0.
Proof. vm_refl. Qed.
Lemma D_712f0 : decode_any W_712f0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712f4 : bv 32 := 0x00e68023.
Lemma F_712f4 : fetch_word Asan.M.loaded_segments (0x712f4 : word) = Some W_712f4.
Proof. vm_refl. Qed.
Lemma D_712f4 : decode_any W_712f4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712f8 : bv 32 := 0x00168693.
Lemma F_712f8 : fetch_word Asan.M.loaded_segments (0x712f8 : word) = Some W_712f8.
Proof. vm_refl. Qed.
Lemma D_712f8 : decode_any W_712f8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_712fc : bv 32 := 0x00158593.
Lemma F_712fc : fetch_word Asan.M.loaded_segments (0x712fc : word) = Some W_712fc.
Proof. vm_refl. Qed.
Lemma D_712fc : decode_any W_712fc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71300 : bv 32 := 0xfec698e3.
Lemma F_71300 : fetch_word Asan.M.loaded_segments (0x71300 : word) = Some W_71300.
Proof. vm_refl. Qed.
Lemma D_71300 : decode_any W_71300 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_71304 : bv 32 := 0x00008067.
Lemma F_71304 : fetch_word Asan.M.loaded_segments (0x71304 : word) = Some W_71304.
Proof. vm_refl. Qed.
Lemma D_71304 : decode_any W_71304 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71308 : bv 32 := 0x02b57463.
Lemma F_71308 : fetch_word Asan.M.loaded_segments (0x71308 : word) = Some W_71308.
Proof. vm_refl. Qed.
Lemma D_71308 : decode_any W_71308 = Some (Branch BC_GEU 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7130c : bv 32 := 0x04c05863.
Lemma F_7130c : fetch_word Asan.M.loaded_segments (0x7130c : word) = Some W_7130c.
Proof. vm_refl. Qed.
Lemma D_7130c : decode_any W_7130c = Some (Branch BC_GE 0 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_71310 : bv 32 := 0x00c50633.
Lemma F_71310 : fetch_word Asan.M.loaded_segments (0x71310 : word) = Some W_71310.
Proof. vm_refl. Qed.
Lemma D_71310 : decode_any W_71310 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71314 : bv 32 := 0x00050693.
Lemma F_71314 : fetch_word Asan.M.loaded_segments (0x71314 : word) = Some W_71314.
Proof. vm_refl. Qed.
Lemma D_71314 : decode_any W_71314 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71318 : bv 32 := 0x0005c703.
Lemma F_71318 : fetch_word Asan.M.loaded_segments (0x71318 : word) = Some W_71318.
Proof. vm_refl. Qed.
Lemma D_71318 : decode_any W_71318 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7131c : bv 32 := 0x00e68023.
Lemma F_7131c : fetch_word Asan.M.loaded_segments (0x7131c : word) = Some W_7131c.
Proof. vm_refl. Qed.
Lemma D_7131c : decode_any W_7131c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71320 : bv 32 := 0x00168693.
Lemma F_71320 : fetch_word Asan.M.loaded_segments (0x71320 : word) = Some W_71320.
Proof. vm_refl. Qed.
Lemma D_71320 : decode_any W_71320 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71324 : bv 32 := 0x00158593.
Lemma F_71324 : fetch_word Asan.M.loaded_segments (0x71324 : word) = Some W_71324.
Proof. vm_refl. Qed.
Lemma D_71324 : decode_any W_71324 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71328 : bv 32 := 0xfec698e3.
Lemma F_71328 : fetch_word Asan.M.loaded_segments (0x71328 : word) = Some W_71328.
Proof. vm_refl. Qed.
Lemma D_71328 : decode_any W_71328 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7132c : bv 32 := 0x0300006f.
Lemma F_7132c : fetch_word Asan.M.loaded_segments (0x7132c : word) = Some W_7132c.
Proof. vm_refl. Qed.
Lemma D_7132c : decode_any W_7132c = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_71330 : bv 32 := 0x02a5f663.
Lemma F_71330 : fetch_word Asan.M.loaded_segments (0x71330 : word) = Some W_71330.
Proof. vm_refl. Qed.
Lemma D_71330 : decode_any W_71330 = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_71334 : bv 32 := 0x02c05463.
Lemma F_71334 : fetch_word Asan.M.loaded_segments (0x71334 : word) = Some W_71334.
Proof. vm_refl. Qed.
Lemma D_71334 : decode_any W_71334 = Some (Branch BC_GE 0 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_71338 : bv 32 := 0xfff60693.
Lemma F_71338 : fetch_word Asan.M.loaded_segments (0x71338 : word) = Some W_71338.
Proof. vm_refl. Qed.
Lemma D_71338 : decode_any W_71338 = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7133c : bv 32 := 0x00100613.
Lemma F_7133c : fetch_word Asan.M.loaded_segments (0x7133c : word) = Some W_7133c.
Proof. vm_refl. Qed.
Lemma D_7133c : decode_any W_7133c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71340 : bv 32 := 0x00d58733.
Lemma F_71340 : fetch_word Asan.M.loaded_segments (0x71340 : word) = Some W_71340.
Proof. vm_refl. Qed.
Lemma D_71340 : decode_any W_71340 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_71344 : bv 32 := 0x00074703.
Lemma F_71344 : fetch_word Asan.M.loaded_segments (0x71344 : word) = Some W_71344.
Proof. vm_refl. Qed.
Lemma D_71344 : decode_any W_71344 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71348 : bv 32 := 0x00d507b3.
Lemma F_71348 : fetch_word Asan.M.loaded_segments (0x71348 : word) = Some W_71348.
Proof. vm_refl. Qed.
Lemma D_71348 : decode_any W_71348 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7134c : bv 32 := 0x00168813.
Lemma F_7134c : fetch_word Asan.M.loaded_segments (0x7134c : word) = Some W_7134c.
Proof. vm_refl. Qed.
Lemma D_7134c : decode_any W_7134c = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71350 : bv 32 := 0xfff68693.
Lemma F_71350 : fetch_word Asan.M.loaded_segments (0x71350 : word) = Some W_71350.
Proof. vm_refl. Qed.
Lemma D_71350 : decode_any W_71350 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_71354 : bv 32 := 0x00e78023.
Lemma F_71354 : fetch_word Asan.M.loaded_segments (0x71354 : word) = Some W_71354.
Proof. vm_refl. Qed.
Lemma D_71354 : decode_any W_71354 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71358 : bv 32 := 0xff0664e3.
Lemma F_71358 : fetch_word Asan.M.loaded_segments (0x71358 : word) = Some W_71358.
Proof. vm_refl. Qed.
Lemma D_71358 : decode_any W_71358 = Some (Branch BC_LTU 12 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7135c : bv 32 := 0x00008067.
Lemma F_7135c : fetch_word Asan.M.loaded_segments (0x7135c : word) = Some W_7135c.
Proof. vm_refl. Qed.
Lemma D_7135c : decode_any W_7135c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71360 : bv 32 := 0x00a666b3.
Lemma F_71360 : fetch_word Asan.M.loaded_segments (0x71360 : word) = Some W_71360.
Proof. vm_refl. Qed.
Lemma D_71360 : decode_any W_71360 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_71364 : bv 32 := 0x00f6f693.
Lemma F_71364 : fetch_word Asan.M.loaded_segments (0x71364 : word) = Some W_71364.
Proof. vm_refl. Qed.
Lemma D_71364 : decode_any W_71364 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_71368 : bv 32 := 0x02068063.
Lemma F_71368 : fetch_word Asan.M.loaded_segments (0x71368 : word) = Some W_71368.
Proof. vm_refl. Qed.
Lemma D_71368 : decode_any W_71368 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7136c : bv 32 := 0x04060863.
Lemma F_7136c : fetch_word Asan.M.loaded_segments (0x7136c : word) = Some W_7136c.
Proof. vm_refl. Qed.
Lemma D_7136c : decode_any W_7136c = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_71370 : bv 32 := 0x00c50633.
Lemma F_71370 : fetch_word Asan.M.loaded_segments (0x71370 : word) = Some W_71370.
Proof. vm_refl. Qed.
Lemma D_71370 : decode_any W_71370 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71374 : bv 32 := 0x00050693.
Lemma F_71374 : fetch_word Asan.M.loaded_segments (0x71374 : word) = Some W_71374.
Proof. vm_refl. Qed.
Lemma D_71374 : decode_any W_71374 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71378 : bv 32 := 0x00b68023.
Lemma F_71378 : fetch_word Asan.M.loaded_segments (0x71378 : word) = Some W_71378.
Proof. vm_refl. Qed.
Lemma D_71378 : decode_any W_71378 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7137c : bv 32 := 0x00168693.
Lemma F_7137c : fetch_word Asan.M.loaded_segments (0x7137c : word) = Some W_7137c.
Proof. vm_refl. Qed.
Lemma D_7137c : decode_any W_7137c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71380 : bv 32 := 0xfec69ce3.
Lemma F_71380 : fetch_word Asan.M.loaded_segments (0x71380 : word) = Some W_71380.
Proof. vm_refl. Qed.
Lemma D_71380 : decode_any W_71380 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_71384 : bv 32 := 0x0380006f.
Lemma F_71384 : fetch_word Asan.M.loaded_segments (0x71384 : word) = Some W_71384.
Proof. vm_refl. Qed.
Lemma D_71384 : decode_any W_71384 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_71388 : bv 32 := 0x02060a63.
Lemma F_71388 : fetch_word Asan.M.loaded_segments (0x71388 : word) = Some W_71388.
Proof. vm_refl. Qed.
Lemma D_71388 : decode_any W_71388 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7138c : bv 32 := 0x00c50633.
Lemma F_7138c : fetch_word Asan.M.loaded_segments (0x7138c : word) = Some W_7138c.
Proof. vm_refl. Qed.
Lemma D_7138c : decode_any W_7138c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71390 : bv 32 := 0x00859693.
Lemma F_71390 : fetch_word Asan.M.loaded_segments (0x71390 : word) = Some W_71390.
Proof. vm_refl. Qed.
Lemma D_71390 : decode_any W_71390 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_71394 : bv 32 := 0x00b6e5b3.
Lemma F_71394 : fetch_word Asan.M.loaded_segments (0x71394 : word) = Some W_71394.
Proof. vm_refl. Qed.
Lemma D_71394 : decode_any W_71394 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_71398 : bv 32 := 0x01059693.
Lemma F_71398 : fetch_word Asan.M.loaded_segments (0x71398 : word) = Some W_71398.
Proof. vm_refl. Qed.
Lemma D_71398 : decode_any W_71398 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7139c : bv 32 := 0x00b6e5b3.
Lemma F_7139c : fetch_word Asan.M.loaded_segments (0x7139c : word) = Some W_7139c.
Proof. vm_refl. Qed.
Lemma D_7139c : decode_any W_7139c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_713a0 : bv 32 := 0x02059693.
Lemma F_713a0 : fetch_word Asan.M.loaded_segments (0x713a0 : word) = Some W_713a0.
Proof. vm_refl. Qed.
Lemma D_713a0 : decode_any W_713a0 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_713a4 : bv 32 := 0x00b6e5b3.
Lemma F_713a4 : fetch_word Asan.M.loaded_segments (0x713a4 : word) = Some W_713a4.
Proof. vm_refl. Qed.
Lemma D_713a4 : decode_any W_713a4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_713a8 : bv 32 := 0x00050693.
Lemma F_713a8 : fetch_word Asan.M.loaded_segments (0x713a8 : word) = Some W_713a8.
Proof. vm_refl. Qed.
Lemma D_713a8 : decode_any W_713a8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_713ac : bv 32 := 0x00b6b023.
Lemma F_713ac : fetch_word Asan.M.loaded_segments (0x713ac : word) = Some W_713ac.
Proof. vm_refl. Qed.
Lemma D_713ac : decode_any W_713ac = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_713b0 : bv 32 := 0x00b6b423.
Lemma F_713b0 : fetch_word Asan.M.loaded_segments (0x713b0 : word) = Some W_713b0.
Proof. vm_refl. Qed.
Lemma D_713b0 : decode_any W_713b0 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_713b4 : bv 32 := 0x01068693.
Lemma F_713b4 : fetch_word Asan.M.loaded_segments (0x713b4 : word) = Some W_713b4.
Proof. vm_refl. Qed.
Lemma D_713b4 : decode_any W_713b4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_713b8 : bv 32 := 0xfec6eae3.
Lemma F_713b8 : fetch_word Asan.M.loaded_segments (0x713b8 : word) = Some W_713b8.
Proof. vm_refl. Qed.
Lemma D_713b8 : decode_any W_713b8 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_713bc : bv 32 := 0x00008067.
Lemma F_713bc : fetch_word Asan.M.loaded_segments (0x713bc : word) = Some W_713bc.
Proof. vm_refl. Qed.
Lemma D_713bc : decode_any W_713bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
