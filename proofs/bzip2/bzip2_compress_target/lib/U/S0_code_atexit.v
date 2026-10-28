From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_n1f518 : bv 32 := 0xfd010113.
Lemma F_n1f518 : fetch_word Ubsan.M.loaded_segments (0x28fdc : word) = Some W_n1f518.
Proof. vm_refl. Qed.
Lemma D_n1f518 : decode_any W_n1f518 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f51c : bv 32 := 0x02113423.
Lemma F_n1f51c : fetch_word Ubsan.M.loaded_segments (0x28fe0 : word) = Some W_n1f51c.
Proof. vm_refl. Qed.
Lemma D_n1f51c : decode_any W_n1f51c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f520 : bv 32 := 0x02813023.
Lemma F_n1f520 : fetch_word Ubsan.M.loaded_segments (0x28fe4 : word) = Some W_n1f520.
Proof. vm_refl. Qed.
Lemma D_n1f520 : decode_any W_n1f520 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f524 : bv 32 := 0x00913c23.
Lemma F_n1f524 : fetch_word Ubsan.M.loaded_segments (0x28fe8 : word) = Some W_n1f524.
Proof. vm_refl. Qed.
Lemma D_n1f524 : decode_any W_n1f524 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f528 : bv 32 := 0x01213823.
Lemma F_n1f528 : fetch_word Ubsan.M.loaded_segments (0x28fec : word) = Some W_n1f528.
Proof. vm_refl. Qed.
Lemma D_n1f528 : decode_any W_n1f528 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f52c : bv 32 := 0x01313423.
Lemma F_n1f52c : fetch_word Ubsan.M.loaded_segments (0x28ff0 : word) = Some W_n1f52c.
Proof. vm_refl. Qed.
Lemma D_n1f52c : decode_any W_n1f52c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f530 : bv 32 := 0x0003b517.
Lemma F_n1f530 : fetch_word Ubsan.M.loaded_segments (0x28ff4 : word) = Some W_n1f530.
Proof. vm_refl. Qed.
Lemma D_n1f530 : decode_any W_n1f530 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f534 : bv 32 := 0x23450913.
Lemma F_n1f534 : fetch_word Ubsan.M.loaded_segments (0x28ff8 : word) = Some W_n1f534.
Proof. vm_refl. Qed.
Lemma D_n1f534 : decode_any W_n1f534 = Some (OpImm ALU_ADD 18 10 564, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f538 : bv 32 := 0x00490413.
Lemma F_n1f538 : fetch_word Ubsan.M.loaded_segments (0x28ffc : word) = Some W_n1f538.
Proof. vm_refl. Qed.
Lemma D_n1f538 : decode_any W_n1f538 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f53c : bv 32 := 0x00040513.
Lemma F_n1f53c : fetch_word Ubsan.M.loaded_segments (0x29000 : word) = Some W_n1f53c.
Proof. vm_refl. Qed.
Lemma D_n1f53c : decode_any W_n1f53c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f540 : bv 32 := 0x4b5070ef.
Lemma F_n1f540 : fetch_word Ubsan.M.loaded_segments (0x29004 : word) = Some W_n1f540.
Proof. vm_refl. Qed.
Lemma D_n1f540 : decode_any W_n1f540 = Some (Jal 1 31924, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f544 : bv 32 := 0x01093503.
Lemma F_n1f544 : fetch_word Ubsan.M.loaded_segments (0x29008 : word) = Some W_n1f544.
Proof. vm_refl. Qed.
Lemma D_n1f544 : decode_any W_n1f544 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f548 : bv 32 := 0x06050863.
Lemma F_n1f548 : fetch_word Ubsan.M.loaded_segments (0x2900c : word) = Some W_n1f548.
Proof. vm_refl. Qed.
Lemma D_n1f548 : decode_any W_n1f548 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f54c : bv 32 := 0x00892583.
Lemma F_n1f54c : fetch_word Ubsan.M.loaded_segments (0x29010 : word) = Some W_n1f54c.
Proof. vm_refl. Qed.
Lemma D_n1f54c : decode_any W_n1f54c = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f550 : bv 32 := 0x0180006f.
Lemma F_n1f550 : fetch_word Ubsan.M.loaded_segments (0x29014 : word) = Some W_n1f550.
Proof. vm_refl. Qed.
Lemma D_n1f550 : decode_any W_n1f550 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f554 : bv 32 := 0x00053503.
Lemma F_n1f554 : fetch_word Ubsan.M.loaded_segments (0x29018 : word) = Some W_n1f554.
Proof. vm_refl. Qed.
Lemma D_n1f554 : decode_any W_n1f554 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f558 : bv 32 := 0x02000593.
Lemma F_n1f558 : fetch_word Ubsan.M.loaded_segments (0x2901c : word) = Some W_n1f558.
Proof. vm_refl. Qed.
Lemma D_n1f558 : decode_any W_n1f558 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f55c : bv 32 := 0x00b92423.
Lemma F_n1f55c : fetch_word Ubsan.M.loaded_segments (0x29020 : word) = Some W_n1f55c.
Proof. vm_refl. Qed.
Lemma D_n1f55c : decode_any W_n1f55c = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f560 : bv 32 := 0x00a93823.
Lemma F_n1f560 : fetch_word Ubsan.M.loaded_segments (0x29024 : word) = Some W_n1f560.
Proof. vm_refl. Qed.
Lemma D_n1f560 : decode_any W_n1f560 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f564 : bv 32 := 0x04050a63.
Lemma F_n1f564 : fetch_word Ubsan.M.loaded_segments (0x29028 : word) = Some W_n1f564.
Proof. vm_refl. Qed.
Lemma D_n1f564 : decode_any W_n1f564 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f568 : bv 32 := 0xfff5861b.
Lemma F_n1f568 : fetch_word Ubsan.M.loaded_segments (0x2902c : word) = Some W_n1f568.
Proof. vm_refl. Qed.
Lemma D_n1f568 : decode_any W_n1f568 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f56c : bv 32 := 0x00c92423.
Lemma F_n1f56c : fetch_word Ubsan.M.loaded_segments (0x29030 : word) = Some W_n1f56c.
Proof. vm_refl. Qed.
Lemma D_n1f56c : decode_any W_n1f56c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f570 : bv 32 := 0xfeb052e3.
Lemma F_n1f570 : fetch_word Ubsan.M.loaded_segments (0x29034 : word) = Some W_n1f570.
Proof. vm_refl. Qed.
Lemma D_n1f570 : decode_any W_n1f570 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f574 : bv 32 := 0x01093503.
Lemma F_n1f574 : fetch_word Ubsan.M.loaded_segments (0x29038 : word) = Some W_n1f574.
Proof. vm_refl. Qed.
Lemma D_n1f574 : decode_any W_n1f574 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f578 : bv 32 := 0x00361613.
Lemma F_n1f578 : fetch_word Ubsan.M.loaded_segments (0x2903c : word) = Some W_n1f578.
Proof. vm_refl. Qed.
Lemma D_n1f578 : decode_any W_n1f578 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f57c : bv 32 := 0x00c50533.
Lemma F_n1f57c : fetch_word Ubsan.M.loaded_segments (0x29040 : word) = Some W_n1f57c.
Proof. vm_refl. Qed.
Lemma D_n1f57c : decode_any W_n1f57c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f580 : bv 32 := 0x00853983.
Lemma F_n1f580 : fetch_word Ubsan.M.loaded_segments (0x29044 : word) = Some W_n1f580.
Proof. vm_refl. Qed.
Lemma D_n1f580 : decode_any W_n1f580 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f584 : bv 32 := 0x10853483.
Lemma F_n1f584 : fetch_word Ubsan.M.loaded_segments (0x29048 : word) = Some W_n1f584.
Proof. vm_refl. Qed.
Lemma D_n1f584 : decode_any W_n1f584 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f588 : bv 32 := 0x00040513.
Lemma F_n1f588 : fetch_word Ubsan.M.loaded_segments (0x2904c : word) = Some W_n1f588.
Proof. vm_refl. Qed.
Lemma D_n1f588 : decode_any W_n1f588 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f58c : bv 32 := 0x6f1070ef.
Lemma F_n1f58c : fetch_word Ubsan.M.loaded_segments (0x29050 : word) = Some W_n1f58c.
Proof. vm_refl. Qed.
Lemma D_n1f58c : decode_any W_n1f58c = Some (Jal 1 32496, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f590 : bv 32 := 0x00048513.
Lemma F_n1f590 : fetch_word Ubsan.M.loaded_segments (0x29054 : word) = Some W_n1f590.
Proof. vm_refl. Qed.
Lemma D_n1f590 : decode_any W_n1f590 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f594 : bv 32 := 0x000980e7.
Lemma F_n1f594 : fetch_word Ubsan.M.loaded_segments (0x29058 : word) = Some W_n1f594.
Proof. vm_refl. Qed.
Lemma D_n1f594 : decode_any W_n1f594 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f598 : bv 32 := 0x00040513.
Lemma F_n1f598 : fetch_word Ubsan.M.loaded_segments (0x2905c : word) = Some W_n1f598.
Proof. vm_refl. Qed.
Lemma D_n1f598 : decode_any W_n1f598 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f59c : bv 32 := 0x459070ef.
Lemma F_n1f59c : fetch_word Ubsan.M.loaded_segments (0x29060 : word) = Some W_n1f59c.
Proof. vm_refl. Qed.
Lemma D_n1f59c : decode_any W_n1f59c = Some (Jal 1 31832, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5a0 : bv 32 := 0x00892503.
Lemma F_n1f5a0 : fetch_word Ubsan.M.loaded_segments (0x29064 : word) = Some W_n1f5a0.
Proof. vm_refl. Qed.
Lemma D_n1f5a0 : decode_any W_n1f5a0 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5a4 : bv 32 := 0xfff5061b.
Lemma F_n1f5a4 : fetch_word Ubsan.M.loaded_segments (0x29068 : word) = Some W_n1f5a4.
Proof. vm_refl. Qed.
Lemma D_n1f5a4 : decode_any W_n1f5a4 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5a8 : bv 32 := 0x00c92423.
Lemma F_n1f5a8 : fetch_word Ubsan.M.loaded_segments (0x2906c : word) = Some W_n1f5a8.
Proof. vm_refl. Qed.
Lemma D_n1f5a8 : decode_any W_n1f5a8 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5ac : bv 32 := 0xfca044e3.
Lemma F_n1f5ac : fetch_word Ubsan.M.loaded_segments (0x29070 : word) = Some W_n1f5ac.
Proof. vm_refl. Qed.
Lemma D_n1f5ac : decode_any W_n1f5ac = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5b0 : bv 32 := 0x01093503.
Lemma F_n1f5b0 : fetch_word Ubsan.M.loaded_segments (0x29074 : word) = Some W_n1f5b0.
Proof. vm_refl. Qed.
Lemma D_n1f5b0 : decode_any W_n1f5b0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5b4 : bv 32 := 0xfa1ff06f.
Lemma F_n1f5b4 : fetch_word Ubsan.M.loaded_segments (0x29078 : word) = Some W_n1f5b4.
Proof. vm_refl. Qed.
Lemma D_n1f5b4 : decode_any W_n1f5b4 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5b8 : bv 32 := 0x00100513.
Lemma F_n1f5b8 : fetch_word Ubsan.M.loaded_segments (0x2907c : word) = Some W_n1f5b8.
Proof. vm_refl. Qed.
Lemma D_n1f5b8 : decode_any W_n1f5b8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5bc : bv 32 := 0x00a90023.
Lemma F_n1f5bc : fetch_word Ubsan.M.loaded_segments (0x29080 : word) = Some W_n1f5bc.
Proof. vm_refl. Qed.
Lemma D_n1f5bc : decode_any W_n1f5bc = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5c0 : bv 32 := 0x00040513.
Lemma F_n1f5c0 : fetch_word Ubsan.M.loaded_segments (0x29084 : word) = Some W_n1f5c0.
Proof. vm_refl. Qed.
Lemma D_n1f5c0 : decode_any W_n1f5c0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5c4 : bv 32 := 0x02813083.
Lemma F_n1f5c4 : fetch_word Ubsan.M.loaded_segments (0x29088 : word) = Some W_n1f5c4.
Proof. vm_refl. Qed.
Lemma D_n1f5c4 : decode_any W_n1f5c4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5c8 : bv 32 := 0x02013403.
Lemma F_n1f5c8 : fetch_word Ubsan.M.loaded_segments (0x2908c : word) = Some W_n1f5c8.
Proof. vm_refl. Qed.
Lemma D_n1f5c8 : decode_any W_n1f5c8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5cc : bv 32 := 0x01813483.
Lemma F_n1f5cc : fetch_word Ubsan.M.loaded_segments (0x29090 : word) = Some W_n1f5cc.
Proof. vm_refl. Qed.
Lemma D_n1f5cc : decode_any W_n1f5cc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5d0 : bv 32 := 0x01013903.
Lemma F_n1f5d0 : fetch_word Ubsan.M.loaded_segments (0x29094 : word) = Some W_n1f5d0.
Proof. vm_refl. Qed.
Lemma D_n1f5d0 : decode_any W_n1f5d0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5d4 : bv 32 := 0x00813983.
Lemma F_n1f5d4 : fetch_word Ubsan.M.loaded_segments (0x29098 : word) = Some W_n1f5d4.
Proof. vm_refl. Qed.
Lemma D_n1f5d4 : decode_any W_n1f5d4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5d8 : bv 32 := 0x03010113.
Lemma F_n1f5d8 : fetch_word Ubsan.M.loaded_segments (0x2909c : word) = Some W_n1f5d8.
Proof. vm_refl. Qed.
Lemma D_n1f5d8 : decode_any W_n1f5d8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5dc : bv 32 := 0x6a10706f.
Lemma F_n1f5dc : fetch_word Ubsan.M.loaded_segments (0x290a0 : word) = Some W_n1f5dc.
Proof. vm_refl. Qed.
Lemma D_n1f5dc : decode_any W_n1f5dc = Some (Jal 0 32416, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f5e0 : bv 32 := 0x00008067.
Lemma F_n1f5e0 : fetch_word Ubsan.M.loaded_segments (0x290a4 : word) = Some W_n1f5e0.
Proof. vm_refl. Qed.
Lemma D_n1f5e0 : decode_any W_n1f5e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1f6a8 : bv 32 := 0x00050067.
Lemma F_n1f6a8 : fetch_word Ubsan.M.loaded_segments (0x2916c : word) = Some W_n1f6a8.
Proof. vm_refl. Qed.
Lemma D_n1f6a8 : decode_any W_n1f6a8 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_n13970 : bv 32 := 0x00030517.
Lemma F_n13970 : fetch_word Ubsan.M.loaded_segments (0x139a8 : word) = Some W_n13970.
Proof. vm_refl. Qed.
Lemma D_n13970 : decode_any W_n13970 = Some (Auipc 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_n13974 : bv 32 := 0x73c54503.
Lemma F_n13974 : fetch_word Ubsan.M.loaded_segments (0x139ac : word) = Some W_n13974.
Proof. vm_refl. Qed.
Lemma D_n13974 : decode_any W_n13974 = Some (Load SZ1 false 10 10 1852, 4%Z).
Proof. vm_refl. Qed.

Definition W_n13978 : bv 32 := 0x00051463.
Lemma F_n13978 : fetch_word Ubsan.M.loaded_segments (0x139b0 : word) = Some W_n13978.
Proof. vm_refl. Qed.
Lemma D_n13978 : decode_any W_n13978 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_n1397c : bv 32 := 0x00008067.
Lemma F_n1397c : fetch_word Ubsan.M.loaded_segments (0x139b4 : word) = Some W_n1397c.
Proof. vm_refl. Qed.
Lemma D_n1397c : decode_any W_n1397c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13480 : bv 32 := 0x0040006f.
Lemma F_13480 : fetch_word Ubsan.M.loaded_segments (0x13538 : word) = Some W_13480.
Proof. vm_refl. Qed.
Lemma D_13480 : decode_any W_13480 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13484 : bv 32 := 0x00020517.
Lemma F_13484 : fetch_word Ubsan.M.loaded_segments (0x1353c : word) = Some W_13484.
Proof. vm_refl. Qed.
Lemma D_13484 : decode_any W_13484 = Some (Auipc 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_13488 : bv 32 := 0xc1450513.
Lemma F_13488 : fetch_word Ubsan.M.loaded_segments (0x13540 : word) = Some W_13488.
Proof. vm_refl. Qed.
Lemma D_13488 : decode_any W_13488 = Some (OpImm ALU_ADD 10 10 3092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1348c : bv 32 := 0x00053503.
Lemma F_1348c : fetch_word Ubsan.M.loaded_segments (0x13544 : word) = Some W_1348c.
Proof. vm_refl. Qed.
Lemma D_1348c : decode_any W_1348c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13490 : bv 32 := 0x35d150ef.
Lemma F_13490 : fetch_word Ubsan.M.loaded_segments (0x13548 : word) = Some W_13490.
Proof. vm_refl. Qed.
Lemma D_13490 : decode_any W_13490 = Some (Jal 1 88924, 4%Z).
Proof. vm_refl. Qed.

Definition W_13494 : bv 32 := 0x0040006f.
Lemma F_13494 : fetch_word Ubsan.M.loaded_segments (0x1354c : word) = Some W_13494.
Proof. vm_refl. Qed.
Lemma D_13494 : decode_any W_13494 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_26dc8 : bv 32 := 0x00052583.
Lemma F_26dc8 : fetch_word Ubsan.M.loaded_segments (0x30f40 : word) = Some W_26dc8.
Proof. vm_refl. Qed.
Lemma D_26dc8 : decode_any W_26dc8 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_26dcc : bv 32 := 0x0005c463.
Lemma F_26dcc : fetch_word Ubsan.M.loaded_segments (0x30f44 : word) = Some W_26dcc.
Proof. vm_refl. Qed.
Lemma D_26dcc : decode_any W_26dcc = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_26dd0 : bv 32 := 0x00008067.
Lemma F_26dd0 : fetch_word Ubsan.M.loaded_segments (0x30f48 : word) = Some W_26dd0.
Proof. vm_refl. Qed.
Lemma D_26dd0 : decode_any W_26dd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
