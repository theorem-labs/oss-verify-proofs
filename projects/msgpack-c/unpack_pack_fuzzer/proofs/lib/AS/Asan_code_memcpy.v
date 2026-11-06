(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c747c : bv 32 := 0x0035f693.
Lemma F_c747c : fetch_word Asan.M.loaded_segments (0xc74a0 : word) = Some W_c747c.
Proof. vm_refl. Qed.
Lemma D_c747c : decode_any W_c747c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7480 : bv 32 := 0x10068863.
Lemma F_c7480 : fetch_word Asan.M.loaded_segments (0xc74a4 : word) = Some W_c7480.
Proof. vm_refl. Qed.
Lemma D_c7480 : decode_any W_c7480 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7484 : bv 32 := 0x02060e63.
Lemma F_c7484 : fetch_word Asan.M.loaded_segments (0xc74a8 : word) = Some W_c7484.
Proof. vm_refl. Qed.
Lemma D_c7484 : decode_any W_c7484 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7488 : bv 32 := 0x00158713.
Lemma F_c7488 : fetch_word Asan.M.loaded_segments (0xc74ac : word) = Some W_c7488.
Proof. vm_refl. Qed.
Lemma D_c7488 : decode_any W_c7488 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c748c : bv 32 := 0x00100793.
Lemma F_c748c : fetch_word Asan.M.loaded_segments (0xc74b0 : word) = Some W_c748c.
Proof. vm_refl. Qed.
Lemma D_c748c : decode_any W_c748c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7490 : bv 32 := 0x00050693.
Lemma F_c7490 : fetch_word Asan.M.loaded_segments (0xc74b4 : word) = Some W_c7490.
Proof. vm_refl. Qed.
Lemma D_c7490 : decode_any W_c7490 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7494 : bv 32 := 0x0005c883.
Lemma F_c7494 : fetch_word Asan.M.loaded_segments (0xc74b8 : word) = Some W_c7494.
Proof. vm_refl. Qed.
Lemma D_c7494 : decode_any W_c7494 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7498 : bv 32 := 0x00060813.
Lemma F_c7498 : fetch_word Asan.M.loaded_segments (0xc74bc : word) = Some W_c7498.
Proof. vm_refl. Qed.
Lemma D_c7498 : decode_any W_c7498 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c749c : bv 32 := 0x00158593.
Lemma F_c749c : fetch_word Asan.M.loaded_segments (0xc74c0 : word) = Some W_c749c.
Proof. vm_refl. Qed.
Lemma D_c749c : decode_any W_c749c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74a0 : bv 32 := 0x00377293.
Lemma F_c74a0 : fetch_word Asan.M.loaded_segments (0xc74c4 : word) = Some W_c74a0.
Proof. vm_refl. Qed.
Lemma D_c74a0 : decode_any W_c74a0 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74a4 : bv 32 := 0x01168023.
Lemma F_c74a4 : fetch_word Asan.M.loaded_segments (0xc74c8 : word) = Some W_c74a4.
Proof. vm_refl. Qed.
Lemma D_c74a4 : decode_any W_c74a4 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74a8 : bv 32 := 0x00168693.
Lemma F_c74a8 : fetch_word Asan.M.loaded_segments (0xc74cc : word) = Some W_c74a8.
Proof. vm_refl. Qed.
Lemma D_c74a8 : decode_any W_c74a8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74ac : bv 32 := 0xfff60613.
Lemma F_c74ac : fetch_word Asan.M.loaded_segments (0xc74d0 : word) = Some W_c74ac.
Proof. vm_refl. Qed.
Lemma D_c74ac : decode_any W_c74ac = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74b0 : bv 32 := 0x00028a63.
Lemma F_c74b0 : fetch_word Asan.M.loaded_segments (0xc74d4 : word) = Some W_c74b0.
Proof. vm_refl. Qed.
Lemma D_c74b0 : decode_any W_c74b0 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74b4 : bv 32 := 0x00170713.
Lemma F_c74b4 : fetch_word Asan.M.loaded_segments (0xc74d8 : word) = Some W_c74b4.
Proof. vm_refl. Qed.
Lemma D_c74b4 : decode_any W_c74b4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74b8 : bv 32 := 0xfcf81ee3.
Lemma F_c74b8 : fetch_word Asan.M.loaded_segments (0xc74dc : word) = Some W_c74b8.
Proof. vm_refl. Qed.
Lemma D_c74b8 : decode_any W_c74b8 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74bc : bv 32 := 0x0080006f.
Lemma F_c74bc : fetch_word Asan.M.loaded_segments (0xc74e0 : word) = Some W_c74bc.
Proof. vm_refl. Qed.
Lemma D_c74bc : decode_any W_c74bc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74c0 : bv 32 := 0x00050693.
Lemma F_c74c0 : fetch_word Asan.M.loaded_segments (0xc74e4 : word) = Some W_c74c0.
Proof. vm_refl. Qed.
Lemma D_c74c0 : decode_any W_c74c0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74c4 : bv 32 := 0x0036f793.
Lemma F_c74c4 : fetch_word Asan.M.loaded_segments (0xc74e8 : word) = Some W_c74c4.
Proof. vm_refl. Qed.
Lemma D_c74c4 : decode_any W_c74c4 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74c8 : bv 32 := 0x0c078a63.
Lemma F_c74c8 : fetch_word Asan.M.loaded_segments (0xc74ec : word) = Some W_c74c8.
Proof. vm_refl. Qed.
Lemma D_c74c8 : decode_any W_c74c8 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74cc : bv 32 := 0x02000713.
Lemma F_c74cc : fetch_word Asan.M.loaded_segments (0xc74f0 : word) = Some W_c74cc.
Proof. vm_refl. Qed.
Lemma D_c74cc : decode_any W_c74cc = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74d0 : bv 32 := 0x02e67063.
Lemma F_c74d0 : fetch_word Asan.M.loaded_segments (0xc74f4 : word) = Some W_c74d0.
Proof. vm_refl. Qed.
Lemma D_c74d0 : decode_any W_c74d0 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74d4 : bv 32 := 0x01000713.
Lemma F_c74d4 : fetch_word Asan.M.loaded_segments (0xc74f8 : word) = Some W_c74d4.
Proof. vm_refl. Qed.
Lemma D_c74d4 : decode_any W_c74d4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74d8 : bv 32 := 0x24e67863.
Lemma F_c74d8 : fetch_word Asan.M.loaded_segments (0xc74fc : word) = Some W_c74d8.
Proof. vm_refl. Qed.
Lemma D_c74d8 : decode_any W_c74d8 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74dc : bv 32 := 0x00867713.
Lemma F_c74dc : fetch_word Asan.M.loaded_segments (0xc7500 : word) = Some W_c74dc.
Proof. vm_refl. Qed.
Lemma D_c74dc : decode_any W_c74dc = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74e0 : bv 32 := 0x2c071e63.
Lemma F_c74e0 : fetch_word Asan.M.loaded_segments (0xc7504 : word) = Some W_c74e0.
Proof. vm_refl. Qed.
Lemma D_c74e0 : decode_any W_c74e0 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74e4 : bv 32 := 0x00467713.
Lemma F_c74e4 : fetch_word Asan.M.loaded_segments (0xc7508 : word) = Some W_c74e4.
Proof. vm_refl. Qed.
Lemma D_c74e4 : decode_any W_c74e4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74e8 : bv 32 := 0x32071463.
Lemma F_c74e8 : fetch_word Asan.M.loaded_segments (0xc750c : word) = Some W_c74e8.
Proof. vm_refl. Qed.
Lemma D_c74e8 : decode_any W_c74e8 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74ec : bv 32 := 0x3500006f.
Lemma F_c74ec : fetch_word Asan.M.loaded_segments (0xc7510 : word) = Some W_c74ec.
Proof. vm_refl. Qed.
Lemma D_c74ec : decode_any W_c74ec = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74f0 : bv 32 := 0x0005a703.
Lemma F_c74f0 : fetch_word Asan.M.loaded_segments (0xc7514 : word) = Some W_c74f0.
Proof. vm_refl. Qed.
Lemma D_c74f0 : decode_any W_c74f0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74f4 : bv 32 := 0x00300813.
Lemma F_c74f4 : fetch_word Asan.M.loaded_segments (0xc7518 : word) = Some W_c74f4.
Proof. vm_refl. Qed.
Lemma D_c74f4 : decode_any W_c74f4 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74f8 : bv 32 := 0x11078e63.
Lemma F_c74f8 : fetch_word Asan.M.loaded_segments (0xc751c : word) = Some W_c74f8.
Proof. vm_refl. Qed.
Lemma D_c74f8 : decode_any W_c74f8 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74fc : bv 32 := 0x00200813.
Lemma F_c74fc : fetch_word Asan.M.loaded_segments (0xc7520 : word) = Some W_c74fc.
Proof. vm_refl. Qed.
Lemma D_c74fc : decode_any W_c74fc = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7500 : bv 32 := 0x19079c63.
Lemma F_c7500 : fetch_word Asan.M.loaded_segments (0xc7524 : word) = Some W_c7500.
Proof. vm_refl. Qed.
Lemma D_c7500 : decode_any W_c7500 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7504 : bv 32 := 0x00875793.
Lemma F_c7504 : fetch_word Asan.M.loaded_segments (0xc7528 : word) = Some W_c7504.
Proof. vm_refl. Qed.
Lemma D_c7504 : decode_any W_c7504 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7508 : bv 32 := 0xffe60613.
Lemma F_c7508 : fetch_word Asan.M.loaded_segments (0xc752c : word) = Some W_c7508.
Proof. vm_refl. Qed.
Lemma D_c7508 : decode_any W_c7508 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c750c : bv 32 := 0x00e68023.
Lemma F_c750c : fetch_word Asan.M.loaded_segments (0xc7530 : word) = Some W_c750c.
Proof. vm_refl. Qed.
Lemma D_c750c : decode_any W_c750c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7510 : bv 32 := 0x00f680a3.
Lemma F_c7510 : fetch_word Asan.M.loaded_segments (0xc7534 : word) = Some W_c7510.
Proof. vm_refl. Qed.
Lemma D_c7510 : decode_any W_c7510 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7514 : bv 32 := 0x00268693.
Lemma F_c7514 : fetch_word Asan.M.loaded_segments (0xc7538 : word) = Some W_c7514.
Proof. vm_refl. Qed.
Lemma D_c7514 : decode_any W_c7514 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7518 : bv 32 := 0x01058593.
Lemma F_c7518 : fetch_word Asan.M.loaded_segments (0xc753c : word) = Some W_c7518.
Proof. vm_refl. Qed.
Lemma D_c7518 : decode_any W_c7518 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c751c : bv 32 := 0x01100793.
Lemma F_c751c : fetch_word Asan.M.loaded_segments (0xc7540 : word) = Some W_c751c.
Proof. vm_refl. Qed.
Lemma D_c751c : decode_any W_c751c = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7520 : bv 32 := 0x0107581b.
Lemma F_c7520 : fetch_word Asan.M.loaded_segments (0xc7544 : word) = Some W_c7520.
Proof. vm_refl. Qed.
Lemma D_c7520 : decode_any W_c7520 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7524 : bv 32 := 0xff45a883.
Lemma F_c7524 : fetch_word Asan.M.loaded_segments (0xc7548 : word) = Some W_c7524.
Proof. vm_refl. Qed.
Lemma D_c7524 : decode_any W_c7524 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7528 : bv 32 := 0xff85a283.
Lemma F_c7528 : fetch_word Asan.M.loaded_segments (0xc754c : word) = Some W_c7528.
Proof. vm_refl. Qed.
Lemma D_c7528 : decode_any W_c7528 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c752c : bv 32 := 0xffc5a303.
Lemma F_c752c : fetch_word Asan.M.loaded_segments (0xc7550 : word) = Some W_c752c.
Proof. vm_refl. Qed.
Lemma D_c752c : decode_any W_c752c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7530 : bv 32 := 0x0005a703.
Lemma F_c7530 : fetch_word Asan.M.loaded_segments (0xc7554 : word) = Some W_c7530.
Proof. vm_refl. Qed.
Lemma D_c7530 : decode_any W_c7530 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7534 : bv 32 := 0x01089393.
Lemma F_c7534 : fetch_word Asan.M.loaded_segments (0xc7558 : word) = Some W_c7534.
Proof. vm_refl. Qed.
Lemma D_c7534 : decode_any W_c7534 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7538 : bv 32 := 0x0108d89b.
Lemma F_c7538 : fetch_word Asan.M.loaded_segments (0xc755c : word) = Some W_c7538.
Proof. vm_refl. Qed.
Lemma D_c7538 : decode_any W_c7538 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c753c : bv 32 := 0x0103e833.
Lemma F_c753c : fetch_word Asan.M.loaded_segments (0xc7560 : word) = Some W_c753c.
Proof. vm_refl. Qed.
Lemma D_c753c : decode_any W_c753c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7540 : bv 32 := 0x01029393.
Lemma F_c7540 : fetch_word Asan.M.loaded_segments (0xc7564 : word) = Some W_c7540.
Proof. vm_refl. Qed.
Lemma D_c7540 : decode_any W_c7540 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7544 : bv 32 := 0x0102d29b.
Lemma F_c7544 : fetch_word Asan.M.loaded_segments (0xc7568 : word) = Some W_c7544.
Proof. vm_refl. Qed.
Lemma D_c7544 : decode_any W_c7544 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7548 : bv 32 := 0x0113e8b3.
Lemma F_c7548 : fetch_word Asan.M.loaded_segments (0xc756c : word) = Some W_c7548.
Proof. vm_refl. Qed.
Lemma D_c7548 : decode_any W_c7548 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c754c : bv 32 := 0x01031393.
Lemma F_c754c : fetch_word Asan.M.loaded_segments (0xc7570 : word) = Some W_c754c.
Proof. vm_refl. Qed.
Lemma D_c754c : decode_any W_c754c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7550 : bv 32 := 0x0103531b.
Lemma F_c7550 : fetch_word Asan.M.loaded_segments (0xc7574 : word) = Some W_c7550.
Proof. vm_refl. Qed.
Lemma D_c7550 : decode_any W_c7550 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7554 : bv 32 := 0x0053e2b3.
Lemma F_c7554 : fetch_word Asan.M.loaded_segments (0xc7578 : word) = Some W_c7554.
Proof. vm_refl. Qed.
Lemma D_c7554 : decode_any W_c7554 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7558 : bv 32 := 0x01071393.
Lemma F_c7558 : fetch_word Asan.M.loaded_segments (0xc757c : word) = Some W_c7558.
Proof. vm_refl. Qed.
Lemma D_c7558 : decode_any W_c7558 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c755c : bv 32 := 0x0063e333.
Lemma F_c755c : fetch_word Asan.M.loaded_segments (0xc7580 : word) = Some W_c755c.
Proof. vm_refl. Qed.
Lemma D_c755c : decode_any W_c755c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7560 : bv 32 := 0xff060613.
Lemma F_c7560 : fetch_word Asan.M.loaded_segments (0xc7584 : word) = Some W_c7560.
Proof. vm_refl. Qed.
Lemma D_c7560 : decode_any W_c7560 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7564 : bv 32 := 0x0106a023.
Lemma F_c7564 : fetch_word Asan.M.loaded_segments (0xc7588 : word) = Some W_c7564.
Proof. vm_refl. Qed.
Lemma D_c7564 : decode_any W_c7564 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7568 : bv 32 := 0x0116a223.
Lemma F_c7568 : fetch_word Asan.M.loaded_segments (0xc758c : word) = Some W_c7568.
Proof. vm_refl. Qed.
Lemma D_c7568 : decode_any W_c7568 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c756c : bv 32 := 0x0056a423.
Lemma F_c756c : fetch_word Asan.M.loaded_segments (0xc7590 : word) = Some W_c756c.
Proof. vm_refl. Qed.
Lemma D_c756c : decode_any W_c756c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7570 : bv 32 := 0x0066a623.
Lemma F_c7570 : fetch_word Asan.M.loaded_segments (0xc7594 : word) = Some W_c7570.
Proof. vm_refl. Qed.
Lemma D_c7570 : decode_any W_c7570 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7574 : bv 32 := 0x01068693.
Lemma F_c7574 : fetch_word Asan.M.loaded_segments (0xc7598 : word) = Some W_c7574.
Proof. vm_refl. Qed.
Lemma D_c7574 : decode_any W_c7574 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7578 : bv 32 := 0x01058593.
Lemma F_c7578 : fetch_word Asan.M.loaded_segments (0xc759c : word) = Some W_c7578.
Proof. vm_refl. Qed.
Lemma D_c7578 : decode_any W_c7578 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c757c : bv 32 := 0xfac7e2e3.
Lemma F_c757c : fetch_word Asan.M.loaded_segments (0xc75a0 : word) = Some W_c757c.
Proof. vm_refl. Qed.
Lemma D_c757c : decode_any W_c757c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7580 : bv 32 := 0xff258593.
Lemma F_c7580 : fetch_word Asan.M.loaded_segments (0xc75a4 : word) = Some W_c7580.
Proof. vm_refl. Qed.
Lemma D_c7580 : decode_any W_c7580 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7584 : bv 32 := 0x01000713.
Lemma F_c7584 : fetch_word Asan.M.loaded_segments (0xc75a8 : word) = Some W_c7584.
Proof. vm_refl. Qed.
Lemma D_c7584 : decode_any W_c7584 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7588 : bv 32 := 0xf4e66ae3.
Lemma F_c7588 : fetch_word Asan.M.loaded_segments (0xc75ac : word) = Some W_c7588.
Proof. vm_refl. Qed.
Lemma D_c7588 : decode_any W_c7588 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_c758c : bv 32 := 0x19c0006f.
Lemma F_c758c : fetch_word Asan.M.loaded_segments (0xc75b0 : word) = Some W_c758c.
Proof. vm_refl. Qed.
Lemma D_c758c : decode_any W_c758c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7590 : bv 32 := 0x00050693.
Lemma F_c7590 : fetch_word Asan.M.loaded_segments (0xc75b4 : word) = Some W_c7590.
Proof. vm_refl. Qed.
Lemma D_c7590 : decode_any W_c7590 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7594 : bv 32 := 0x00357793.
Lemma F_c7594 : fetch_word Asan.M.loaded_segments (0xc75b8 : word) = Some W_c7594.
Proof. vm_refl. Qed.
Lemma D_c7594 : decode_any W_c7594 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7598 : bv 32 := 0xf2079ae3.
Lemma F_c7598 : fetch_word Asan.M.loaded_segments (0xc75bc : word) = Some W_c7598.
Proof. vm_refl. Qed.
Lemma D_c7598 : decode_any W_c7598 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_c759c : bv 32 := 0x01000713.
Lemma F_c759c : fetch_word Asan.M.loaded_segments (0xc75c0 : word) = Some W_c759c.
Proof. vm_refl. Qed.
Lemma D_c759c : decode_any W_c759c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75a0 : bv 32 := 0x02e66c63.
Lemma F_c75a0 : fetch_word Asan.M.loaded_segments (0xc75c4 : word) = Some W_c75a0.
Proof. vm_refl. Qed.
Lemma D_c75a0 : decode_any W_c75a0 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75a4 : bv 32 := 0x00f00713.
Lemma F_c75a4 : fetch_word Asan.M.loaded_segments (0xc75c8 : word) = Some W_c75a4.
Proof. vm_refl. Qed.
Lemma D_c75a4 : decode_any W_c75a4 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75a8 : bv 32 := 0x0005a783.
Lemma F_c75a8 : fetch_word Asan.M.loaded_segments (0xc75cc : word) = Some W_c75a8.
Proof. vm_refl. Qed.
Lemma D_c75a8 : decode_any W_c75a8 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75ac : bv 32 := 0x0045a803.
Lemma F_c75ac : fetch_word Asan.M.loaded_segments (0xc75d0 : word) = Some W_c75ac.
Proof. vm_refl. Qed.
Lemma D_c75ac : decode_any W_c75ac = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75b0 : bv 32 := 0x0085a883.
Lemma F_c75b0 : fetch_word Asan.M.loaded_segments (0xc75d4 : word) = Some W_c75b0.
Proof. vm_refl. Qed.
Lemma D_c75b0 : decode_any W_c75b0 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75b4 : bv 32 := 0x00c5a283.
Lemma F_c75b4 : fetch_word Asan.M.loaded_segments (0xc75d8 : word) = Some W_c75b4.
Proof. vm_refl. Qed.
Lemma D_c75b4 : decode_any W_c75b4 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75b8 : bv 32 := 0x01058593.
Lemma F_c75b8 : fetch_word Asan.M.loaded_segments (0xc75dc : word) = Some W_c75b8.
Proof. vm_refl. Qed.
Lemma D_c75b8 : decode_any W_c75b8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75bc : bv 32 := 0xff060613.
Lemma F_c75bc : fetch_word Asan.M.loaded_segments (0xc75e0 : word) = Some W_c75bc.
Proof. vm_refl. Qed.
Lemma D_c75bc : decode_any W_c75bc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75c0 : bv 32 := 0x00f6a023.
Lemma F_c75c0 : fetch_word Asan.M.loaded_segments (0xc75e4 : word) = Some W_c75c0.
Proof. vm_refl. Qed.
Lemma D_c75c0 : decode_any W_c75c0 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75c4 : bv 32 := 0x0106a223.
Lemma F_c75c4 : fetch_word Asan.M.loaded_segments (0xc75e8 : word) = Some W_c75c4.
Proof. vm_refl. Qed.
Lemma D_c75c4 : decode_any W_c75c4 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75c8 : bv 32 := 0x0116a423.
Lemma F_c75c8 : fetch_word Asan.M.loaded_segments (0xc75ec : word) = Some W_c75c8.
Proof. vm_refl. Qed.
Lemma D_c75c8 : decode_any W_c75c8 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75cc : bv 32 := 0x0056a623.
Lemma F_c75cc : fetch_word Asan.M.loaded_segments (0xc75f0 : word) = Some W_c75cc.
Proof. vm_refl. Qed.
Lemma D_c75cc : decode_any W_c75cc = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75d0 : bv 32 := 0x01068693.
Lemma F_c75d0 : fetch_word Asan.M.loaded_segments (0xc75f4 : word) = Some W_c75d0.
Proof. vm_refl. Qed.
Lemma D_c75d0 : decode_any W_c75d0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75d4 : bv 32 := 0xfcc76ae3.
Lemma F_c75d4 : fetch_word Asan.M.loaded_segments (0xc75f8 : word) = Some W_c75d4.
Proof. vm_refl. Qed.
Lemma D_c75d4 : decode_any W_c75d4 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75d8 : bv 32 := 0x00800713.
Lemma F_c75d8 : fetch_word Asan.M.loaded_segments (0xc75fc : word) = Some W_c75d8.
Proof. vm_refl. Qed.
Lemma D_c75d8 : decode_any W_c75d8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75dc : bv 32 := 0x00e66e63.
Lemma F_c75dc : fetch_word Asan.M.loaded_segments (0xc7600 : word) = Some W_c75dc.
Proof. vm_refl. Qed.
Lemma D_c75dc : decode_any W_c75dc = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75e0 : bv 32 := 0x0005a703.
Lemma F_c75e0 : fetch_word Asan.M.loaded_segments (0xc7604 : word) = Some W_c75e0.
Proof. vm_refl. Qed.
Lemma D_c75e0 : decode_any W_c75e0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75e4 : bv 32 := 0x0045a783.
Lemma F_c75e4 : fetch_word Asan.M.loaded_segments (0xc7608 : word) = Some W_c75e4.
Proof. vm_refl. Qed.
Lemma D_c75e4 : decode_any W_c75e4 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75e8 : bv 32 := 0x00e6a023.
Lemma F_c75e8 : fetch_word Asan.M.loaded_segments (0xc760c : word) = Some W_c75e8.
Proof. vm_refl. Qed.
Lemma D_c75e8 : decode_any W_c75e8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75ec : bv 32 := 0x00f6a223.
Lemma F_c75ec : fetch_word Asan.M.loaded_segments (0xc7610 : word) = Some W_c75ec.
Proof. vm_refl. Qed.
Lemma D_c75ec : decode_any W_c75ec = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75f0 : bv 32 := 0x00868693.
Lemma F_c75f0 : fetch_word Asan.M.loaded_segments (0xc7614 : word) = Some W_c75f0.
Proof. vm_refl. Qed.
Lemma D_c75f0 : decode_any W_c75f0 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75f4 : bv 32 := 0x00858593.
Lemma F_c75f4 : fetch_word Asan.M.loaded_segments (0xc7618 : word) = Some W_c75f4.
Proof. vm_refl. Qed.
Lemma D_c75f4 : decode_any W_c75f4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75f8 : bv 32 := 0x00467713.
Lemma F_c75f8 : fetch_word Asan.M.loaded_segments (0xc761c : word) = Some W_c75f8.
Proof. vm_refl. Qed.
Lemma D_c75f8 : decode_any W_c75f8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c75fc : bv 32 := 0x24070063.
Lemma F_c75fc : fetch_word Asan.M.loaded_segments (0xc7620 : word) = Some W_c75fc.
Proof. vm_refl. Qed.
Lemma D_c75fc : decode_any W_c75fc = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7600 : bv 32 := 0x0005a703.
Lemma F_c7600 : fetch_word Asan.M.loaded_segments (0xc7624 : word) = Some W_c7600.
Proof. vm_refl. Qed.
Lemma D_c7600 : decode_any W_c7600 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7604 : bv 32 := 0x00458593.
Lemma F_c7604 : fetch_word Asan.M.loaded_segments (0xc7628 : word) = Some W_c7604.
Proof. vm_refl. Qed.
Lemma D_c7604 : decode_any W_c7604 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7608 : bv 32 := 0x00e6a023.
Lemma F_c7608 : fetch_word Asan.M.loaded_segments (0xc762c : word) = Some W_c7608.
Proof. vm_refl. Qed.
Lemma D_c7608 : decode_any W_c7608 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c760c : bv 32 := 0x00468693.
Lemma F_c760c : fetch_word Asan.M.loaded_segments (0xc7630 : word) = Some W_c760c.
Proof. vm_refl. Qed.
Lemma D_c760c : decode_any W_c760c = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7610 : bv 32 := 0x22c0006f.
Lemma F_c7610 : fetch_word Asan.M.loaded_segments (0xc7634 : word) = Some W_c7610.
Proof. vm_refl. Qed.
Lemma D_c7610 : decode_any W_c7610 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7614 : bv 32 := 0x00e68023.
Lemma F_c7614 : fetch_word Asan.M.loaded_segments (0xc7638 : word) = Some W_c7614.
Proof. vm_refl. Qed.
Lemma D_c7614 : decode_any W_c7614 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7618 : bv 32 := 0x00168693.
Lemma F_c7618 : fetch_word Asan.M.loaded_segments (0xc763c : word) = Some W_c7618.
Proof. vm_refl. Qed.
Lemma D_c7618 : decode_any W_c7618 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c761c : bv 32 := 0xfff60613.
Lemma F_c761c : fetch_word Asan.M.loaded_segments (0xc7640 : word) = Some W_c761c.
Proof. vm_refl. Qed.
Lemma D_c761c : decode_any W_c761c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7620 : bv 32 := 0x01058593.
Lemma F_c7620 : fetch_word Asan.M.loaded_segments (0xc7644 : word) = Some W_c7620.
Proof. vm_refl. Qed.
Lemma D_c7620 : decode_any W_c7620 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7624 : bv 32 := 0x01200793.
Lemma F_c7624 : fetch_word Asan.M.loaded_segments (0xc7648 : word) = Some W_c7624.
Proof. vm_refl. Qed.
Lemma D_c7624 : decode_any W_c7624 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7628 : bv 32 := 0x0087581b.
Lemma F_c7628 : fetch_word Asan.M.loaded_segments (0xc764c : word) = Some W_c7628.
Proof. vm_refl. Qed.
Lemma D_c7628 : decode_any W_c7628 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c762c : bv 32 := 0xff45a883.
Lemma F_c762c : fetch_word Asan.M.loaded_segments (0xc7650 : word) = Some W_c762c.
Proof. vm_refl. Qed.
Lemma D_c762c : decode_any W_c762c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7630 : bv 32 := 0xff85a283.
Lemma F_c7630 : fetch_word Asan.M.loaded_segments (0xc7654 : word) = Some W_c7630.
Proof. vm_refl. Qed.
Lemma D_c7630 : decode_any W_c7630 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7634 : bv 32 := 0xffc5a303.
Lemma F_c7634 : fetch_word Asan.M.loaded_segments (0xc7658 : word) = Some W_c7634.
Proof. vm_refl. Qed.
Lemma D_c7634 : decode_any W_c7634 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7638 : bv 32 := 0x0005a703.
Lemma F_c7638 : fetch_word Asan.M.loaded_segments (0xc765c : word) = Some W_c7638.
Proof. vm_refl. Qed.
Lemma D_c7638 : decode_any W_c7638 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c763c : bv 32 := 0x01889393.
Lemma F_c763c : fetch_word Asan.M.loaded_segments (0xc7660 : word) = Some W_c763c.
Proof. vm_refl. Qed.
Lemma D_c763c : decode_any W_c763c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7640 : bv 32 := 0x0088d89b.
Lemma F_c7640 : fetch_word Asan.M.loaded_segments (0xc7664 : word) = Some W_c7640.
Proof. vm_refl. Qed.
Lemma D_c7640 : decode_any W_c7640 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7644 : bv 32 := 0x0103e833.
Lemma F_c7644 : fetch_word Asan.M.loaded_segments (0xc7668 : word) = Some W_c7644.
Proof. vm_refl. Qed.
Lemma D_c7644 : decode_any W_c7644 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7648 : bv 32 := 0x01829393.
Lemma F_c7648 : fetch_word Asan.M.loaded_segments (0xc766c : word) = Some W_c7648.
Proof. vm_refl. Qed.
Lemma D_c7648 : decode_any W_c7648 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c764c : bv 32 := 0x0082d29b.
Lemma F_c764c : fetch_word Asan.M.loaded_segments (0xc7670 : word) = Some W_c764c.
Proof. vm_refl. Qed.
Lemma D_c764c : decode_any W_c764c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7650 : bv 32 := 0x0113e8b3.
Lemma F_c7650 : fetch_word Asan.M.loaded_segments (0xc7674 : word) = Some W_c7650.
Proof. vm_refl. Qed.
Lemma D_c7650 : decode_any W_c7650 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7654 : bv 32 := 0x01831393.
Lemma F_c7654 : fetch_word Asan.M.loaded_segments (0xc7678 : word) = Some W_c7654.
Proof. vm_refl. Qed.
Lemma D_c7654 : decode_any W_c7654 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7658 : bv 32 := 0x0083531b.
Lemma F_c7658 : fetch_word Asan.M.loaded_segments (0xc767c : word) = Some W_c7658.
Proof. vm_refl. Qed.
Lemma D_c7658 : decode_any W_c7658 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c765c : bv 32 := 0x0053e2b3.
Lemma F_c765c : fetch_word Asan.M.loaded_segments (0xc7680 : word) = Some W_c765c.
Proof. vm_refl. Qed.
Lemma D_c765c : decode_any W_c765c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7660 : bv 32 := 0x01871393.
Lemma F_c7660 : fetch_word Asan.M.loaded_segments (0xc7684 : word) = Some W_c7660.
Proof. vm_refl. Qed.
Lemma D_c7660 : decode_any W_c7660 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7664 : bv 32 := 0x0063e333.
Lemma F_c7664 : fetch_word Asan.M.loaded_segments (0xc7688 : word) = Some W_c7664.
Proof. vm_refl. Qed.
Lemma D_c7664 : decode_any W_c7664 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7668 : bv 32 := 0xff060613.
Lemma F_c7668 : fetch_word Asan.M.loaded_segments (0xc768c : word) = Some W_c7668.
Proof. vm_refl. Qed.
Lemma D_c7668 : decode_any W_c7668 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c766c : bv 32 := 0x0106a023.
Lemma F_c766c : fetch_word Asan.M.loaded_segments (0xc7690 : word) = Some W_c766c.
Proof. vm_refl. Qed.
Lemma D_c766c : decode_any W_c766c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7670 : bv 32 := 0x0116a223.
Lemma F_c7670 : fetch_word Asan.M.loaded_segments (0xc7694 : word) = Some W_c7670.
Proof. vm_refl. Qed.
Lemma D_c7670 : decode_any W_c7670 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7674 : bv 32 := 0x0056a423.
Lemma F_c7674 : fetch_word Asan.M.loaded_segments (0xc7698 : word) = Some W_c7674.
Proof. vm_refl. Qed.
Lemma D_c7674 : decode_any W_c7674 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7678 : bv 32 := 0x0066a623.
Lemma F_c7678 : fetch_word Asan.M.loaded_segments (0xc769c : word) = Some W_c7678.
Proof. vm_refl. Qed.
Lemma D_c7678 : decode_any W_c7678 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c767c : bv 32 := 0x01068693.
Lemma F_c767c : fetch_word Asan.M.loaded_segments (0xc76a0 : word) = Some W_c767c.
Proof. vm_refl. Qed.
Lemma D_c767c : decode_any W_c767c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7680 : bv 32 := 0x01058593.
Lemma F_c7680 : fetch_word Asan.M.loaded_segments (0xc76a4 : word) = Some W_c7680.
Proof. vm_refl. Qed.
Lemma D_c7680 : decode_any W_c7680 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7684 : bv 32 := 0xfac7e2e3.
Lemma F_c7684 : fetch_word Asan.M.loaded_segments (0xc76a8 : word) = Some W_c7684.
Proof. vm_refl. Qed.
Lemma D_c7684 : decode_any W_c7684 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7688 : bv 32 := 0xff158593.
Lemma F_c7688 : fetch_word Asan.M.loaded_segments (0xc76ac : word) = Some W_c7688.
Proof. vm_refl. Qed.
Lemma D_c7688 : decode_any W_c7688 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_c768c : bv 32 := 0x01000713.
Lemma F_c768c : fetch_word Asan.M.loaded_segments (0xc76b0 : word) = Some W_c768c.
Proof. vm_refl. Qed.
Lemma D_c768c : decode_any W_c768c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7690 : bv 32 := 0xe4e666e3.
Lemma F_c7690 : fetch_word Asan.M.loaded_segments (0xc76b4 : word) = Some W_c7690.
Proof. vm_refl. Qed.
Lemma D_c7690 : decode_any W_c7690 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7694 : bv 32 := 0x0940006f.
Lemma F_c7694 : fetch_word Asan.M.loaded_segments (0xc76b8 : word) = Some W_c7694.
Proof. vm_refl. Qed.
Lemma D_c7694 : decode_any W_c7694 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7698 : bv 32 := 0x00875793.
Lemma F_c7698 : fetch_word Asan.M.loaded_segments (0xc76bc : word) = Some W_c7698.
Proof. vm_refl. Qed.
Lemma D_c7698 : decode_any W_c7698 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c769c : bv 32 := 0x01075813.
Lemma F_c769c : fetch_word Asan.M.loaded_segments (0xc76c0 : word) = Some W_c769c.
Proof. vm_refl. Qed.
Lemma D_c769c : decode_any W_c769c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76a0 : bv 32 := 0xffd60613.
Lemma F_c76a0 : fetch_word Asan.M.loaded_segments (0xc76c4 : word) = Some W_c76a0.
Proof. vm_refl. Qed.
Lemma D_c76a0 : decode_any W_c76a0 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76a4 : bv 32 := 0x00e68023.
Lemma F_c76a4 : fetch_word Asan.M.loaded_segments (0xc76c8 : word) = Some W_c76a4.
Proof. vm_refl. Qed.
Lemma D_c76a4 : decode_any W_c76a4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76a8 : bv 32 := 0x00f680a3.
Lemma F_c76a8 : fetch_word Asan.M.loaded_segments (0xc76cc : word) = Some W_c76a8.
Proof. vm_refl. Qed.
Lemma D_c76a8 : decode_any W_c76a8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76ac : bv 32 := 0x01068123.
Lemma F_c76ac : fetch_word Asan.M.loaded_segments (0xc76d0 : word) = Some W_c76ac.
Proof. vm_refl. Qed.
Lemma D_c76ac : decode_any W_c76ac = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76b0 : bv 32 := 0x00368693.
Lemma F_c76b0 : fetch_word Asan.M.loaded_segments (0xc76d4 : word) = Some W_c76b0.
Proof. vm_refl. Qed.
Lemma D_c76b0 : decode_any W_c76b0 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76b4 : bv 32 := 0x01058593.
Lemma F_c76b4 : fetch_word Asan.M.loaded_segments (0xc76d8 : word) = Some W_c76b4.
Proof. vm_refl. Qed.
Lemma D_c76b4 : decode_any W_c76b4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76b8 : bv 32 := 0x01000793.
Lemma F_c76b8 : fetch_word Asan.M.loaded_segments (0xc76dc : word) = Some W_c76b8.
Proof. vm_refl. Qed.
Lemma D_c76b8 : decode_any W_c76b8 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76bc : bv 32 := 0x0187581b.
Lemma F_c76bc : fetch_word Asan.M.loaded_segments (0xc76e0 : word) = Some W_c76bc.
Proof. vm_refl. Qed.
Lemma D_c76bc : decode_any W_c76bc = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76c0 : bv 32 := 0xff45a883.
Lemma F_c76c0 : fetch_word Asan.M.loaded_segments (0xc76e4 : word) = Some W_c76c0.
Proof. vm_refl. Qed.
Lemma D_c76c0 : decode_any W_c76c0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76c4 : bv 32 := 0xff85a283.
Lemma F_c76c4 : fetch_word Asan.M.loaded_segments (0xc76e8 : word) = Some W_c76c4.
Proof. vm_refl. Qed.
Lemma D_c76c4 : decode_any W_c76c4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76c8 : bv 32 := 0xffc5a303.
Lemma F_c76c8 : fetch_word Asan.M.loaded_segments (0xc76ec : word) = Some W_c76c8.
Proof. vm_refl. Qed.
Lemma D_c76c8 : decode_any W_c76c8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76cc : bv 32 := 0x0005a703.
Lemma F_c76cc : fetch_word Asan.M.loaded_segments (0xc76f0 : word) = Some W_c76cc.
Proof. vm_refl. Qed.
Lemma D_c76cc : decode_any W_c76cc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76d0 : bv 32 := 0x00889393.
Lemma F_c76d0 : fetch_word Asan.M.loaded_segments (0xc76f4 : word) = Some W_c76d0.
Proof. vm_refl. Qed.
Lemma D_c76d0 : decode_any W_c76d0 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76d4 : bv 32 := 0x0188d89b.
Lemma F_c76d4 : fetch_word Asan.M.loaded_segments (0xc76f8 : word) = Some W_c76d4.
Proof. vm_refl. Qed.
Lemma D_c76d4 : decode_any W_c76d4 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76d8 : bv 32 := 0x0103e833.
Lemma F_c76d8 : fetch_word Asan.M.loaded_segments (0xc76fc : word) = Some W_c76d8.
Proof. vm_refl. Qed.
Lemma D_c76d8 : decode_any W_c76d8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76dc : bv 32 := 0x00829393.
Lemma F_c76dc : fetch_word Asan.M.loaded_segments (0xc7700 : word) = Some W_c76dc.
Proof. vm_refl. Qed.
Lemma D_c76dc : decode_any W_c76dc = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76e0 : bv 32 := 0x0182d29b.
Lemma F_c76e0 : fetch_word Asan.M.loaded_segments (0xc7704 : word) = Some W_c76e0.
Proof. vm_refl. Qed.
Lemma D_c76e0 : decode_any W_c76e0 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76e4 : bv 32 := 0x0113e8b3.
Lemma F_c76e4 : fetch_word Asan.M.loaded_segments (0xc7708 : word) = Some W_c76e4.
Proof. vm_refl. Qed.
Lemma D_c76e4 : decode_any W_c76e4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76e8 : bv 32 := 0x00831393.
Lemma F_c76e8 : fetch_word Asan.M.loaded_segments (0xc770c : word) = Some W_c76e8.
Proof. vm_refl. Qed.
Lemma D_c76e8 : decode_any W_c76e8 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76ec : bv 32 := 0x0183531b.
Lemma F_c76ec : fetch_word Asan.M.loaded_segments (0xc7710 : word) = Some W_c76ec.
Proof. vm_refl. Qed.
Lemma D_c76ec : decode_any W_c76ec = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76f0 : bv 32 := 0x0053e2b3.
Lemma F_c76f0 : fetch_word Asan.M.loaded_segments (0xc7714 : word) = Some W_c76f0.
Proof. vm_refl. Qed.
Lemma D_c76f0 : decode_any W_c76f0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76f4 : bv 32 := 0x00871393.
Lemma F_c76f4 : fetch_word Asan.M.loaded_segments (0xc7718 : word) = Some W_c76f4.
Proof. vm_refl. Qed.
Lemma D_c76f4 : decode_any W_c76f4 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76f8 : bv 32 := 0x0063e333.
Lemma F_c76f8 : fetch_word Asan.M.loaded_segments (0xc771c : word) = Some W_c76f8.
Proof. vm_refl. Qed.
Lemma D_c76f8 : decode_any W_c76f8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76fc : bv 32 := 0xff060613.
Lemma F_c76fc : fetch_word Asan.M.loaded_segments (0xc7720 : word) = Some W_c76fc.
Proof. vm_refl. Qed.
Lemma D_c76fc : decode_any W_c76fc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7700 : bv 32 := 0x0106a023.
Lemma F_c7700 : fetch_word Asan.M.loaded_segments (0xc7724 : word) = Some W_c7700.
Proof. vm_refl. Qed.
Lemma D_c7700 : decode_any W_c7700 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7704 : bv 32 := 0x0116a223.
Lemma F_c7704 : fetch_word Asan.M.loaded_segments (0xc7728 : word) = Some W_c7704.
Proof. vm_refl. Qed.
Lemma D_c7704 : decode_any W_c7704 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7708 : bv 32 := 0x0056a423.
Lemma F_c7708 : fetch_word Asan.M.loaded_segments (0xc772c : word) = Some W_c7708.
Proof. vm_refl. Qed.
Lemma D_c7708 : decode_any W_c7708 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c770c : bv 32 := 0x0066a623.
Lemma F_c770c : fetch_word Asan.M.loaded_segments (0xc7730 : word) = Some W_c770c.
Proof. vm_refl. Qed.
Lemma D_c770c : decode_any W_c770c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7710 : bv 32 := 0x01068693.
Lemma F_c7710 : fetch_word Asan.M.loaded_segments (0xc7734 : word) = Some W_c7710.
Proof. vm_refl. Qed.
Lemma D_c7710 : decode_any W_c7710 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7714 : bv 32 := 0x01058593.
Lemma F_c7714 : fetch_word Asan.M.loaded_segments (0xc7738 : word) = Some W_c7714.
Proof. vm_refl. Qed.
Lemma D_c7714 : decode_any W_c7714 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7718 : bv 32 := 0xfac7e2e3.
Lemma F_c7718 : fetch_word Asan.M.loaded_segments (0xc773c : word) = Some W_c7718.
Proof. vm_refl. Qed.
Lemma D_c7718 : decode_any W_c7718 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c771c : bv 32 := 0xff358593.
Lemma F_c771c : fetch_word Asan.M.loaded_segments (0xc7740 : word) = Some W_c771c.
Proof. vm_refl. Qed.
Lemma D_c771c : decode_any W_c771c = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7720 : bv 32 := 0x01000713.
Lemma F_c7720 : fetch_word Asan.M.loaded_segments (0xc7744 : word) = Some W_c7720.
Proof. vm_refl. Qed.
Lemma D_c7720 : decode_any W_c7720 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7724 : bv 32 := 0xdae66ce3.
Lemma F_c7724 : fetch_word Asan.M.loaded_segments (0xc7748 : word) = Some W_c7724.
Proof. vm_refl. Qed.
Lemma D_c7724 : decode_any W_c7724 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7728 : bv 32 := 0x0005c703.
Lemma F_c7728 : fetch_word Asan.M.loaded_segments (0xc774c : word) = Some W_c7728.
Proof. vm_refl. Qed.
Lemma D_c7728 : decode_any W_c7728 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c772c : bv 32 := 0x0015c783.
Lemma F_c772c : fetch_word Asan.M.loaded_segments (0xc7750 : word) = Some W_c772c.
Proof. vm_refl. Qed.
Lemma D_c772c : decode_any W_c772c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7730 : bv 32 := 0x0025c803.
Lemma F_c7730 : fetch_word Asan.M.loaded_segments (0xc7754 : word) = Some W_c7730.
Proof. vm_refl. Qed.
Lemma D_c7730 : decode_any W_c7730 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7734 : bv 32 := 0x0035c883.
Lemma F_c7734 : fetch_word Asan.M.loaded_segments (0xc7758 : word) = Some W_c7734.
Proof. vm_refl. Qed.
Lemma D_c7734 : decode_any W_c7734 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7738 : bv 32 := 0x0045c283.
Lemma F_c7738 : fetch_word Asan.M.loaded_segments (0xc775c : word) = Some W_c7738.
Proof. vm_refl. Qed.
Lemma D_c7738 : decode_any W_c7738 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c773c : bv 32 := 0x0055c303.
Lemma F_c773c : fetch_word Asan.M.loaded_segments (0xc7760 : word) = Some W_c773c.
Proof. vm_refl. Qed.
Lemma D_c773c : decode_any W_c773c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7740 : bv 32 := 0x0065c383.
Lemma F_c7740 : fetch_word Asan.M.loaded_segments (0xc7764 : word) = Some W_c7740.
Proof. vm_refl. Qed.
Lemma D_c7740 : decode_any W_c7740 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7744 : bv 32 := 0x0075ce03.
Lemma F_c7744 : fetch_word Asan.M.loaded_segments (0xc7768 : word) = Some W_c7744.
Proof. vm_refl. Qed.
Lemma D_c7744 : decode_any W_c7744 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7748 : bv 32 := 0x00e68023.
Lemma F_c7748 : fetch_word Asan.M.loaded_segments (0xc776c : word) = Some W_c7748.
Proof. vm_refl. Qed.
Lemma D_c7748 : decode_any W_c7748 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c774c : bv 32 := 0x00f680a3.
Lemma F_c774c : fetch_word Asan.M.loaded_segments (0xc7770 : word) = Some W_c774c.
Proof. vm_refl. Qed.
Lemma D_c774c : decode_any W_c774c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7750 : bv 32 := 0x01068123.
Lemma F_c7750 : fetch_word Asan.M.loaded_segments (0xc7774 : word) = Some W_c7750.
Proof. vm_refl. Qed.
Lemma D_c7750 : decode_any W_c7750 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7754 : bv 32 := 0x011681a3.
Lemma F_c7754 : fetch_word Asan.M.loaded_segments (0xc7778 : word) = Some W_c7754.
Proof. vm_refl. Qed.
Lemma D_c7754 : decode_any W_c7754 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7758 : bv 32 := 0x0085c703.
Lemma F_c7758 : fetch_word Asan.M.loaded_segments (0xc777c : word) = Some W_c7758.
Proof. vm_refl. Qed.
Lemma D_c7758 : decode_any W_c7758 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c775c : bv 32 := 0x0095c783.
Lemma F_c775c : fetch_word Asan.M.loaded_segments (0xc7780 : word) = Some W_c775c.
Proof. vm_refl. Qed.
Lemma D_c775c : decode_any W_c775c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7760 : bv 32 := 0x00a5c803.
Lemma F_c7760 : fetch_word Asan.M.loaded_segments (0xc7784 : word) = Some W_c7760.
Proof. vm_refl. Qed.
Lemma D_c7760 : decode_any W_c7760 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7764 : bv 32 := 0x00b5c883.
Lemma F_c7764 : fetch_word Asan.M.loaded_segments (0xc7788 : word) = Some W_c7764.
Proof. vm_refl. Qed.
Lemma D_c7764 : decode_any W_c7764 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7768 : bv 32 := 0x00568223.
Lemma F_c7768 : fetch_word Asan.M.loaded_segments (0xc778c : word) = Some W_c7768.
Proof. vm_refl. Qed.
Lemma D_c7768 : decode_any W_c7768 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c776c : bv 32 := 0x006682a3.
Lemma F_c776c : fetch_word Asan.M.loaded_segments (0xc7790 : word) = Some W_c776c.
Proof. vm_refl. Qed.
Lemma D_c776c : decode_any W_c776c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7770 : bv 32 := 0x00768323.
Lemma F_c7770 : fetch_word Asan.M.loaded_segments (0xc7794 : word) = Some W_c7770.
Proof. vm_refl. Qed.
Lemma D_c7770 : decode_any W_c7770 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7774 : bv 32 := 0x01c683a3.
Lemma F_c7774 : fetch_word Asan.M.loaded_segments (0xc7798 : word) = Some W_c7774.
Proof. vm_refl. Qed.
Lemma D_c7774 : decode_any W_c7774 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7778 : bv 32 := 0x00c5c283.
Lemma F_c7778 : fetch_word Asan.M.loaded_segments (0xc779c : word) = Some W_c7778.
Proof. vm_refl. Qed.
Lemma D_c7778 : decode_any W_c7778 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c777c : bv 32 := 0x00d5c303.
Lemma F_c777c : fetch_word Asan.M.loaded_segments (0xc77a0 : word) = Some W_c777c.
Proof. vm_refl. Qed.
Lemma D_c777c : decode_any W_c777c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7780 : bv 32 := 0x00e5c383.
Lemma F_c7780 : fetch_word Asan.M.loaded_segments (0xc77a4 : word) = Some W_c7780.
Proof. vm_refl. Qed.
Lemma D_c7780 : decode_any W_c7780 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7784 : bv 32 := 0x00f5ce03.
Lemma F_c7784 : fetch_word Asan.M.loaded_segments (0xc77a8 : word) = Some W_c7784.
Proof. vm_refl. Qed.
Lemma D_c7784 : decode_any W_c7784 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7788 : bv 32 := 0x01058593.
Lemma F_c7788 : fetch_word Asan.M.loaded_segments (0xc77ac : word) = Some W_c7788.
Proof. vm_refl. Qed.
Lemma D_c7788 : decode_any W_c7788 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c778c : bv 32 := 0x00e68423.
Lemma F_c778c : fetch_word Asan.M.loaded_segments (0xc77b0 : word) = Some W_c778c.
Proof. vm_refl. Qed.
Lemma D_c778c : decode_any W_c778c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7790 : bv 32 := 0x00f684a3.
Lemma F_c7790 : fetch_word Asan.M.loaded_segments (0xc77b4 : word) = Some W_c7790.
Proof. vm_refl. Qed.
Lemma D_c7790 : decode_any W_c7790 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7794 : bv 32 := 0x01068523.
Lemma F_c7794 : fetch_word Asan.M.loaded_segments (0xc77b8 : word) = Some W_c7794.
Proof. vm_refl. Qed.
Lemma D_c7794 : decode_any W_c7794 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7798 : bv 32 := 0x011685a3.
Lemma F_c7798 : fetch_word Asan.M.loaded_segments (0xc77bc : word) = Some W_c7798.
Proof. vm_refl. Qed.
Lemma D_c7798 : decode_any W_c7798 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c779c : bv 32 := 0x01068713.
Lemma F_c779c : fetch_word Asan.M.loaded_segments (0xc77c0 : word) = Some W_c779c.
Proof. vm_refl. Qed.
Lemma D_c779c : decode_any W_c779c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77a0 : bv 32 := 0x00568623.
Lemma F_c77a0 : fetch_word Asan.M.loaded_segments (0xc77c4 : word) = Some W_c77a0.
Proof. vm_refl. Qed.
Lemma D_c77a0 : decode_any W_c77a0 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77a4 : bv 32 := 0x006686a3.
Lemma F_c77a4 : fetch_word Asan.M.loaded_segments (0xc77c8 : word) = Some W_c77a4.
Proof. vm_refl. Qed.
Lemma D_c77a4 : decode_any W_c77a4 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77a8 : bv 32 := 0x00768723.
Lemma F_c77a8 : fetch_word Asan.M.loaded_segments (0xc77cc : word) = Some W_c77a8.
Proof. vm_refl. Qed.
Lemma D_c77a8 : decode_any W_c77a8 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77ac : bv 32 := 0x01c687a3.
Lemma F_c77ac : fetch_word Asan.M.loaded_segments (0xc77d0 : word) = Some W_c77ac.
Proof. vm_refl. Qed.
Lemma D_c77ac : decode_any W_c77ac = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77b0 : bv 32 := 0x00070693.
Lemma F_c77b0 : fetch_word Asan.M.loaded_segments (0xc77d4 : word) = Some W_c77b0.
Proof. vm_refl. Qed.
Lemma D_c77b0 : decode_any W_c77b0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77b4 : bv 32 := 0x00867713.
Lemma F_c77b4 : fetch_word Asan.M.loaded_segments (0xc77d8 : word) = Some W_c77b4.
Proof. vm_refl. Qed.
Lemma D_c77b4 : decode_any W_c77b4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77b8 : bv 32 := 0xd20706e3.
Lemma F_c77b8 : fetch_word Asan.M.loaded_segments (0xc77dc : word) = Some W_c77b8.
Proof. vm_refl. Qed.
Lemma D_c77b8 : decode_any W_c77b8 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77bc : bv 32 := 0x0005c703.
Lemma F_c77bc : fetch_word Asan.M.loaded_segments (0xc77e0 : word) = Some W_c77bc.
Proof. vm_refl. Qed.
Lemma D_c77bc : decode_any W_c77bc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77c0 : bv 32 := 0x0015c783.
Lemma F_c77c0 : fetch_word Asan.M.loaded_segments (0xc77e4 : word) = Some W_c77c0.
Proof. vm_refl. Qed.
Lemma D_c77c0 : decode_any W_c77c0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77c4 : bv 32 := 0x0025c803.
Lemma F_c77c4 : fetch_word Asan.M.loaded_segments (0xc77e8 : word) = Some W_c77c4.
Proof. vm_refl. Qed.
Lemma D_c77c4 : decode_any W_c77c4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77c8 : bv 32 := 0x0035c883.
Lemma F_c77c8 : fetch_word Asan.M.loaded_segments (0xc77ec : word) = Some W_c77c8.
Proof. vm_refl. Qed.
Lemma D_c77c8 : decode_any W_c77c8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77cc : bv 32 := 0x0045c283.
Lemma F_c77cc : fetch_word Asan.M.loaded_segments (0xc77f0 : word) = Some W_c77cc.
Proof. vm_refl. Qed.
Lemma D_c77cc : decode_any W_c77cc = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77d0 : bv 32 := 0x0055c303.
Lemma F_c77d0 : fetch_word Asan.M.loaded_segments (0xc77f4 : word) = Some W_c77d0.
Proof. vm_refl. Qed.
Lemma D_c77d0 : decode_any W_c77d0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77d4 : bv 32 := 0x0065c383.
Lemma F_c77d4 : fetch_word Asan.M.loaded_segments (0xc77f8 : word) = Some W_c77d4.
Proof. vm_refl. Qed.
Lemma D_c77d4 : decode_any W_c77d4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77d8 : bv 32 := 0x0075ce03.
Lemma F_c77d8 : fetch_word Asan.M.loaded_segments (0xc77fc : word) = Some W_c77d8.
Proof. vm_refl. Qed.
Lemma D_c77d8 : decode_any W_c77d8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77dc : bv 32 := 0x00858593.
Lemma F_c77dc : fetch_word Asan.M.loaded_segments (0xc7800 : word) = Some W_c77dc.
Proof. vm_refl. Qed.
Lemma D_c77dc : decode_any W_c77dc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77e0 : bv 32 := 0x00e68023.
Lemma F_c77e0 : fetch_word Asan.M.loaded_segments (0xc7804 : word) = Some W_c77e0.
Proof. vm_refl. Qed.
Lemma D_c77e0 : decode_any W_c77e0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77e4 : bv 32 := 0x00f680a3.
Lemma F_c77e4 : fetch_word Asan.M.loaded_segments (0xc7808 : word) = Some W_c77e4.
Proof. vm_refl. Qed.
Lemma D_c77e4 : decode_any W_c77e4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77e8 : bv 32 := 0x01068123.
Lemma F_c77e8 : fetch_word Asan.M.loaded_segments (0xc780c : word) = Some W_c77e8.
Proof. vm_refl. Qed.
Lemma D_c77e8 : decode_any W_c77e8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77ec : bv 32 := 0x011681a3.
Lemma F_c77ec : fetch_word Asan.M.loaded_segments (0xc7810 : word) = Some W_c77ec.
Proof. vm_refl. Qed.
Lemma D_c77ec : decode_any W_c77ec = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77f0 : bv 32 := 0x00868713.
Lemma F_c77f0 : fetch_word Asan.M.loaded_segments (0xc7814 : word) = Some W_c77f0.
Proof. vm_refl. Qed.
Lemma D_c77f0 : decode_any W_c77f0 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77f4 : bv 32 := 0x00568223.
Lemma F_c77f4 : fetch_word Asan.M.loaded_segments (0xc7818 : word) = Some W_c77f4.
Proof. vm_refl. Qed.
Lemma D_c77f4 : decode_any W_c77f4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77f8 : bv 32 := 0x006682a3.
Lemma F_c77f8 : fetch_word Asan.M.loaded_segments (0xc781c : word) = Some W_c77f8.
Proof. vm_refl. Qed.
Lemma D_c77f8 : decode_any W_c77f8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77fc : bv 32 := 0x00768323.
Lemma F_c77fc : fetch_word Asan.M.loaded_segments (0xc7820 : word) = Some W_c77fc.
Proof. vm_refl. Qed.
Lemma D_c77fc : decode_any W_c77fc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7800 : bv 32 := 0x01c683a3.
Lemma F_c7800 : fetch_word Asan.M.loaded_segments (0xc7824 : word) = Some W_c7800.
Proof. vm_refl. Qed.
Lemma D_c7800 : decode_any W_c7800 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7804 : bv 32 := 0x00070693.
Lemma F_c7804 : fetch_word Asan.M.loaded_segments (0xc7828 : word) = Some W_c7804.
Proof. vm_refl. Qed.
Lemma D_c7804 : decode_any W_c7804 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7808 : bv 32 := 0x00467713.
Lemma F_c7808 : fetch_word Asan.M.loaded_segments (0xc782c : word) = Some W_c7808.
Proof. vm_refl. Qed.
Lemma D_c7808 : decode_any W_c7808 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c780c : bv 32 := 0x02070863.
Lemma F_c780c : fetch_word Asan.M.loaded_segments (0xc7830 : word) = Some W_c780c.
Proof. vm_refl. Qed.
Lemma D_c780c : decode_any W_c780c = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7810 : bv 32 := 0x0005c703.
Lemma F_c7810 : fetch_word Asan.M.loaded_segments (0xc7834 : word) = Some W_c7810.
Proof. vm_refl. Qed.
Lemma D_c7810 : decode_any W_c7810 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7814 : bv 32 := 0x0015c783.
Lemma F_c7814 : fetch_word Asan.M.loaded_segments (0xc7838 : word) = Some W_c7814.
Proof. vm_refl. Qed.
Lemma D_c7814 : decode_any W_c7814 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7818 : bv 32 := 0x0025c803.
Lemma F_c7818 : fetch_word Asan.M.loaded_segments (0xc783c : word) = Some W_c7818.
Proof. vm_refl. Qed.
Lemma D_c7818 : decode_any W_c7818 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c781c : bv 32 := 0x0035c883.
Lemma F_c781c : fetch_word Asan.M.loaded_segments (0xc7840 : word) = Some W_c781c.
Proof. vm_refl. Qed.
Lemma D_c781c : decode_any W_c781c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7820 : bv 32 := 0x00458593.
Lemma F_c7820 : fetch_word Asan.M.loaded_segments (0xc7844 : word) = Some W_c7820.
Proof. vm_refl. Qed.
Lemma D_c7820 : decode_any W_c7820 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7824 : bv 32 := 0x00468293.
Lemma F_c7824 : fetch_word Asan.M.loaded_segments (0xc7848 : word) = Some W_c7824.
Proof. vm_refl. Qed.
Lemma D_c7824 : decode_any W_c7824 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7828 : bv 32 := 0x00e68023.
Lemma F_c7828 : fetch_word Asan.M.loaded_segments (0xc784c : word) = Some W_c7828.
Proof. vm_refl. Qed.
Lemma D_c7828 : decode_any W_c7828 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c782c : bv 32 := 0x00f680a3.
Lemma F_c782c : fetch_word Asan.M.loaded_segments (0xc7850 : word) = Some W_c782c.
Proof. vm_refl. Qed.
Lemma D_c782c : decode_any W_c782c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7830 : bv 32 := 0x01068123.
Lemma F_c7830 : fetch_word Asan.M.loaded_segments (0xc7854 : word) = Some W_c7830.
Proof. vm_refl. Qed.
Lemma D_c7830 : decode_any W_c7830 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7834 : bv 32 := 0x011681a3.
Lemma F_c7834 : fetch_word Asan.M.loaded_segments (0xc7858 : word) = Some W_c7834.
Proof. vm_refl. Qed.
Lemma D_c7834 : decode_any W_c7834 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7838 : bv 32 := 0x00028693.
Lemma F_c7838 : fetch_word Asan.M.loaded_segments (0xc785c : word) = Some W_c7838.
Proof. vm_refl. Qed.
Lemma D_c7838 : decode_any W_c7838 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c783c : bv 32 := 0x00267713.
Lemma F_c783c : fetch_word Asan.M.loaded_segments (0xc7860 : word) = Some W_c783c.
Proof. vm_refl. Qed.
Lemma D_c783c : decode_any W_c783c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7840 : bv 32 := 0x00071863.
Lemma F_c7840 : fetch_word Asan.M.loaded_segments (0xc7864 : word) = Some W_c7840.
Proof. vm_refl. Qed.
Lemma D_c7840 : decode_any W_c7840 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7844 : bv 32 := 0x00167613.
Lemma F_c7844 : fetch_word Asan.M.loaded_segments (0xc7868 : word) = Some W_c7844.
Proof. vm_refl. Qed.
Lemma D_c7844 : decode_any W_c7844 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7848 : bv 32 := 0x02061663.
Lemma F_c7848 : fetch_word Asan.M.loaded_segments (0xc786c : word) = Some W_c7848.
Proof. vm_refl. Qed.
Lemma D_c7848 : decode_any W_c7848 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_c784c : bv 32 := 0x00008067.
Lemma F_c784c : fetch_word Asan.M.loaded_segments (0xc7870 : word) = Some W_c784c.
Proof. vm_refl. Qed.
Lemma D_c784c : decode_any W_c784c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7850 : bv 32 := 0x0005c703.
Lemma F_c7850 : fetch_word Asan.M.loaded_segments (0xc7874 : word) = Some W_c7850.
Proof. vm_refl. Qed.
Lemma D_c7850 : decode_any W_c7850 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7854 : bv 32 := 0x0015c783.
Lemma F_c7854 : fetch_word Asan.M.loaded_segments (0xc7878 : word) = Some W_c7854.
Proof. vm_refl. Qed.
Lemma D_c7854 : decode_any W_c7854 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7858 : bv 32 := 0x00258593.
Lemma F_c7858 : fetch_word Asan.M.loaded_segments (0xc787c : word) = Some W_c7858.
Proof. vm_refl. Qed.
Lemma D_c7858 : decode_any W_c7858 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c785c : bv 32 := 0x00268813.
Lemma F_c785c : fetch_word Asan.M.loaded_segments (0xc7880 : word) = Some W_c785c.
Proof. vm_refl. Qed.
Lemma D_c785c : decode_any W_c785c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7860 : bv 32 := 0x00e68023.
Lemma F_c7860 : fetch_word Asan.M.loaded_segments (0xc7884 : word) = Some W_c7860.
Proof. vm_refl. Qed.
Lemma D_c7860 : decode_any W_c7860 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7864 : bv 32 := 0x00f680a3.
Lemma F_c7864 : fetch_word Asan.M.loaded_segments (0xc7888 : word) = Some W_c7864.
Proof. vm_refl. Qed.
Lemma D_c7864 : decode_any W_c7864 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7868 : bv 32 := 0x00080693.
Lemma F_c7868 : fetch_word Asan.M.loaded_segments (0xc788c : word) = Some W_c7868.
Proof. vm_refl. Qed.
Lemma D_c7868 : decode_any W_c7868 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c786c : bv 32 := 0x00167613.
Lemma F_c786c : fetch_word Asan.M.loaded_segments (0xc7890 : word) = Some W_c786c.
Proof. vm_refl. Qed.
Lemma D_c786c : decode_any W_c786c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7870 : bv 32 := 0xfc060ee3.
Lemma F_c7870 : fetch_word Asan.M.loaded_segments (0xc7894 : word) = Some W_c7870.
Proof. vm_refl. Qed.
Lemma D_c7870 : decode_any W_c7870 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7874 : bv 32 := 0x0005c583.
Lemma F_c7874 : fetch_word Asan.M.loaded_segments (0xc7898 : word) = Some W_c7874.
Proof. vm_refl. Qed.
Lemma D_c7874 : decode_any W_c7874 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7878 : bv 32 := 0x00b68023.
Lemma F_c7878 : fetch_word Asan.M.loaded_segments (0xc789c : word) = Some W_c7878.
Proof. vm_refl. Qed.
Lemma D_c7878 : decode_any W_c7878 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c787c : bv 32 := 0x00008067.
Lemma F_c787c : fetch_word Asan.M.loaded_segments (0xc78a0 : word) = Some W_c787c.
Proof. vm_refl. Qed.
Lemma D_c787c : decode_any W_c787c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
