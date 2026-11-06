(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_65f74 : bv 32 := 0xfc010113.
Lemma F_65f74 : fetch_word Ubsan.M.loaded_segments (0x65fb4 : word) = Some W_65f74.
Proof. vm_refl. Qed.
Lemma D_65f74 : decode_any W_65f74 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f78 : bv 32 := 0x02113c23.
Lemma F_65f78 : fetch_word Ubsan.M.loaded_segments (0x65fb8 : word) = Some W_65f78.
Proof. vm_refl. Qed.
Lemma D_65f78 : decode_any W_65f78 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f7c : bv 32 := 0x02813823.
Lemma F_65f7c : fetch_word Ubsan.M.loaded_segments (0x65fbc : word) = Some W_65f7c.
Proof. vm_refl. Qed.
Lemma D_65f7c : decode_any W_65f7c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f80 : bv 32 := 0x02913423.
Lemma F_65f80 : fetch_word Ubsan.M.loaded_segments (0x65fc0 : word) = Some W_65f80.
Proof. vm_refl. Qed.
Lemma D_65f80 : decode_any W_65f80 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f84 : bv 32 := 0x00050413.
Lemma F_65f84 : fetch_word Ubsan.M.loaded_segments (0x65fc4 : word) = Some W_65f84.
Proof. vm_refl. Qed.
Lemma D_65f84 : decode_any W_65f84 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f88 : bv 32 := 0x00853603.
Lemma F_65f88 : fetch_word Ubsan.M.loaded_segments (0x65fc8 : word) = Some W_65f88.
Proof. vm_refl. Qed.
Lemma D_65f88 : decode_any W_65f88 = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f8c : bv 32 := 0x01053503.
Lemma F_65f8c : fetch_word Ubsan.M.loaded_segments (0x65fcc : word) = Some W_65f8c.
Proof. vm_refl. Qed.
Lemma D_65f8c : decode_any W_65f8c = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f90 : bv 32 := 0x40c506b3.
Lemma F_65f90 : fetch_word Ubsan.M.loaded_segments (0x65fd0 : word) = Some W_65f90.
Proof. vm_refl. Qed.
Lemma D_65f90 : decode_any W_65f90 = Some (Op ALU_SUB 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f94 : bv 32 := 0x4026d693.
Lemma F_65f94 : fetch_word Ubsan.M.loaded_segments (0x65fd4 : word) = Some W_65f94.
Proof. vm_refl. Qed.
Lemma D_65f94 : decode_any W_65f94 = Some (ShiftImm ALU_SRA 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f98 : bv 32 := 0x00058493.
Lemma F_65f98 : fetch_word Ubsan.M.loaded_segments (0x65fd8 : word) = Some W_65f98.
Proof. vm_refl. Qed.
Lemma D_65f98 : decode_any W_65f98 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f9c : bv 32 := 0x08b6f063.
Lemma F_65f9c : fetch_word Ubsan.M.loaded_segments (0x65fdc : word) = Some W_65f9c.
Proof. vm_refl. Qed.
Lemma D_65f9c : decode_any W_65f9c = Some (Branch BC_GEU 13 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fa0 : bv 32 := 0x00043583.
Lemma F_65fa0 : fetch_word Ubsan.M.loaded_segments (0x65fe0 : word) = Some W_65fa0.
Proof. vm_refl. Qed.
Lemma D_65fa0 : decode_any W_65fa0 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fa4 : bv 32 := 0x40b60633.
Lemma F_65fa4 : fetch_word Ubsan.M.loaded_segments (0x65fe4 : word) = Some W_65fa4.
Proof. vm_refl. Qed.
Lemma D_65fa4 : decode_any W_65fa4 = Some (Op ALU_SUB 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fa8 : bv 32 := 0x40265613.
Lemma F_65fa8 : fetch_word Ubsan.M.loaded_segments (0x65fe8 : word) = Some W_65fa8.
Proof. vm_refl. Qed.
Lemma D_65fa8 : decode_any W_65fa8 = Some (ShiftImm ALU_SRA 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fac : bv 32 := 0x009606b3.
Lemma F_65fac : fetch_word Ubsan.M.loaded_segments (0x65fec : word) = Some W_65fac.
Proof. vm_refl. Qed.
Lemma D_65fac : decode_any W_65fac = Some (Op ALU_ADD 13 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fb0 : bv 32 := 0x03e6d713.
Lemma F_65fb0 : fetch_word Ubsan.M.loaded_segments (0x65ff0 : word) = Some W_65fb0.
Proof. vm_refl. Qed.
Lemma D_65fb0 : decode_any W_65fb0 = Some (ShiftImm ALU_SRL 14 13 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fb4 : bv 32 := 0x08071263.
Lemma F_65fb4 : fetch_word Ubsan.M.loaded_segments (0x65ff4 : word) = Some W_65fb4.
Proof. vm_refl. Qed.
Lemma D_65fb4 : decode_any W_65fb4 = Some (Branch BC_NE 14 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fb8 : bv 32 := 0x40b50533.
Lemma F_65fb8 : fetch_word Ubsan.M.loaded_segments (0x65ff8 : word) = Some W_65fb8.
Proof. vm_refl. Qed.
Lemma D_65fb8 : decode_any W_65fb8 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fbc : bv 32 := 0x00155593.
Lemma F_65fbc : fetch_word Ubsan.M.loaded_segments (0x65ffc : word) = Some W_65fbc.
Proof. vm_refl. Qed.
Lemma D_65fbc : decode_any W_65fbc = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fc0 : bv 32 := 0x00b6e463.
Lemma F_65fc0 : fetch_word Ubsan.M.loaded_segments (0x66000 : word) = Some W_65fc0.
Proof. vm_refl. Qed.
Lemma D_65fc0 : decode_any W_65fc0 = Some (Branch BC_LTU 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fc4 : bv 32 := 0x00068593.
Lemma F_65fc4 : fetch_word Ubsan.M.loaded_segments (0x66004 : word) = Some W_65fc4.
Proof. vm_refl. Qed.
Lemma D_65fc4 : decode_any W_65fc4 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fc8 : bv 32 := 0xff900693.
Lemma F_65fc8 : fetch_word Ubsan.M.loaded_segments (0x66008 : word) = Some W_65fc8.
Proof. vm_refl. Qed.
Lemma D_65fc8 : decode_any W_65fc8 = Some (OpImm ALU_ADD 13 0 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fcc : bv 32 := 0x0016d693.
Lemma F_65fcc : fetch_word Ubsan.M.loaded_segments (0x6600c : word) = Some W_65fcc.
Proof. vm_refl. Qed.
Lemma D_65fcc : decode_any W_65fcc = Some (ShiftImm ALU_SRL 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fd0 : bv 32 := 0x00d56663.
Lemma F_65fd0 : fetch_word Ubsan.M.loaded_segments (0x66010 : word) = Some W_65fd0.
Proof. vm_refl. Qed.
Lemma D_65fd0 : decode_any W_65fd0 = Some (Branch BC_LTU 10 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fdc : bv 32 := 0x00010513.
Lemma F_65fdc : fetch_word Ubsan.M.loaded_segments (0x6601c : word) = Some W_65fdc.
Proof. vm_refl. Qed.
Lemma D_65fdc : decode_any W_65fdc = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fe0 : bv 32 := 0x00040693.
Lemma F_65fe0 : fetch_word Ubsan.M.loaded_segments (0x66020 : word) = Some W_65fe0.
Proof. vm_refl. Qed.
Lemma D_65fe0 : decode_any W_65fe0 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fe4 : bv 32 := 0x0ec000ef.
Lemma F_65fe4 : fetch_word Ubsan.M.loaded_segments (0x66024 : word) = Some W_65fe4.
Proof. vm_refl. Qed.
Lemma D_65fe4 : decode_any W_65fe4 = Some (Jal 1 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fe8 : bv 32 := 0x00010513.
Lemma F_65fe8 : fetch_word Ubsan.M.loaded_segments (0x66028 : word) = Some W_65fe8.
Proof. vm_refl. Qed.
Lemma D_65fe8 : decode_any W_65fe8 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fec : bv 32 := 0x00048593.
Lemma F_65fec : fetch_word Ubsan.M.loaded_segments (0x6602c : word) = Some W_65fec.
Proof. vm_refl. Qed.
Lemma D_65fec : decode_any W_65fec = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ff0 : bv 32 := 0x188000ef.
Lemma F_65ff0 : fetch_word Ubsan.M.loaded_segments (0x66030 : word) = Some W_65ff0.
Proof. vm_refl. Qed.
Lemma D_65ff0 : decode_any W_65ff0 = Some (Jal 1 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ff4 : bv 32 := 0x00010593.
Lemma F_65ff4 : fetch_word Ubsan.M.loaded_segments (0x66034 : word) = Some W_65ff4.
Proof. vm_refl. Qed.
Lemma D_65ff4 : decode_any W_65ff4 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ff8 : bv 32 := 0x00040513.
Lemma F_65ff8 : fetch_word Ubsan.M.loaded_segments (0x66038 : word) = Some W_65ff8.
Proof. vm_refl. Qed.
Lemma D_65ff8 : decode_any W_65ff8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ffc : bv 32 := 0x200000ef.
Lemma F_65ffc : fetch_word Ubsan.M.loaded_segments (0x6603c : word) = Some W_65ffc.
Proof. vm_refl. Qed.
Lemma D_65ffc : decode_any W_65ffc = Some (Jal 1 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_66000 : bv 32 := 0x00010513.
Lemma F_66000 : fetch_word Ubsan.M.loaded_segments (0x66040 : word) = Some W_66000.
Proof. vm_refl. Qed.
Lemma D_66000 : decode_any W_66000 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66004 : bv 32 := 0x2d8000ef.
Lemma F_66004 : fetch_word Ubsan.M.loaded_segments (0x66044 : word) = Some W_66004.
Proof. vm_refl. Qed.
Lemma D_66004 : decode_any W_66004 = Some (Jal 1 728, 4%Z).
Proof. vm_refl. Qed.

Definition W_66008 : bv 32 := 0x03813083.
Lemma F_66008 : fetch_word Ubsan.M.loaded_segments (0x66048 : word) = Some W_66008.
Proof. vm_refl. Qed.
Lemma D_66008 : decode_any W_66008 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6600c : bv 32 := 0x03013403.
Lemma F_6600c : fetch_word Ubsan.M.loaded_segments (0x6604c : word) = Some W_6600c.
Proof. vm_refl. Qed.
Lemma D_6600c : decode_any W_6600c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_66010 : bv 32 := 0x02813483.
Lemma F_66010 : fetch_word Ubsan.M.loaded_segments (0x66050 : word) = Some W_66010.
Proof. vm_refl. Qed.
Lemma D_66010 : decode_any W_66010 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_66014 : bv 32 := 0x04010113.
Lemma F_66014 : fetch_word Ubsan.M.loaded_segments (0x66054 : word) = Some W_66014.
Proof. vm_refl. Qed.
Lemma D_66014 : decode_any W_66014 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_66018 : bv 32 := 0x00008067.
Lemma F_66018 : fetch_word Ubsan.M.loaded_segments (0x66058 : word) = Some W_66018.
Proof. vm_refl. Qed.
Lemma D_66018 : decode_any W_66018 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6601c : bv 32 := 0x00040513.

Definition W_66020 : bv 32 := 0x00048593.

Definition W_66024 : bv 32 := 0x03813083.

Definition W_66028 : bv 32 := 0x03013403.

Definition W_6602c : bv 32 := 0x02813483.

Definition W_66030 : bv 32 := 0x04010113.

Definition W_66034 : bv 32 := 0x0200006f.

Definition W_66038 : bv 32 := 0x2f0000ef.

Definition W_6603c : bv 32 := 0xc0001073.

Definition W_66040 : bv 32 := 0x00050413.

Definition W_66044 : bv 32 := 0x00010513.

Definition W_66048 : bv 32 := 0x294000ef.

Definition W_6604c : bv 32 := 0x00040513.

Definition W_66050 : bv 32 := 0x34d640ef.

Definition W_66054 : bv 32 := 0x00853603.

Definition W_66058 : bv 32 := 0x00259693.

Definition W_6605c : bv 32 := 0x00c68733.

Definition W_66060 : bv 32 := 0x00c037b3.

Definition W_66064 : bv 32 := 0x00173813.

Definition W_66068 : bv 32 := 0x07078263.

Definition W_6606c : bv 32 := 0x00100793.

Definition W_66070 : bv 32 := 0x03d79793.

Definition W_66074 : bv 32 := 0x00f587b3.

Definition W_66078 : bv 32 := 0x03e7d793.

Definition W_6607c : bv 32 := 0x04079863.

Definition W_66080 : bv 32 := 0x04c76663.

Definition W_66084 : bv 32 := 0x04058063.

Definition W_66088 : bv 32 := 0x00259593.

Definition W_6608c : bv 32 := 0x00367713.

Definition W_66090 : bv 32 := 0x00b605b3.

Definition W_66094 : bv 32 := 0xffc00793.

Definition W_66098 : bv 32 := 0x00060813.

Definition W_6609c : bv 32 := 0x02060863.

Definition W_660a0 : bv 32 := 0x02071663.

Definition W_660a4 : bv 32 := 0x00062023.

Definition W_660a8 : bv 32 := 0x02080263.

Definition W_660ac : bv 32 := 0x02f80063.

Definition W_660b0 : bv 32 := 0x00460613.

Definition W_660b4 : bv 32 := 0xffc68693.

Definition W_660d0 : bv 32 := 0xfe010113.
Lemma F_660d0 : fetch_word Ubsan.M.loaded_segments (0x66110 : word) = Some W_660d0.
Proof. vm_refl. Qed.
Lemma D_660d0 : decode_any W_660d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_660d4 : bv 32 := 0x00113c23.
Lemma F_660d4 : fetch_word Ubsan.M.loaded_segments (0x66114 : word) = Some W_660d4.
Proof. vm_refl. Qed.
Lemma D_660d4 : decode_any W_660d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_660d8 : bv 32 := 0x00813823.
Lemma F_660d8 : fetch_word Ubsan.M.loaded_segments (0x66118 : word) = Some W_660d8.
Proof. vm_refl. Qed.
Lemma D_660d8 : decode_any W_660d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_660dc : bv 32 := 0x00913423.
Lemma F_660dc : fetch_word Ubsan.M.loaded_segments (0x6611c : word) = Some W_660dc.
Proof. vm_refl. Qed.
Lemma D_660dc : decode_any W_660dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_660e0 : bv 32 := 0x00060493.
Lemma F_660e0 : fetch_word Ubsan.M.loaded_segments (0x66120 : word) = Some W_660e0.
Proof. vm_refl. Qed.
Lemma D_660e0 : decode_any W_660e0 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_660e4 : bv 32 := 0x00050413.
Lemma F_660e4 : fetch_word Ubsan.M.loaded_segments (0x66124 : word) = Some W_660e4.
Proof. vm_refl. Qed.
Lemma D_660e4 : decode_any W_660e4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_660e8 : bv 32 := 0x00053c23.
Lemma F_660e8 : fetch_word Ubsan.M.loaded_segments (0x66128 : word) = Some W_660e8.
Proof. vm_refl. Qed.
Lemma D_660e8 : decode_any W_660e8 = Some (Store SZ8 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_660ec : bv 32 := 0x02d53023.
Lemma F_660ec : fetch_word Ubsan.M.loaded_segments (0x6612c : word) = Some W_660ec.
Proof. vm_refl. Qed.
Lemma D_660ec : decode_any W_660ec = Some (Store SZ8 10 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_660f0 : bv 32 := 0x00058863.
Lemma F_660f0 : fetch_word Ubsan.M.loaded_segments (0x66130 : word) = Some W_660f0.
Proof. vm_refl. Qed.
Lemma D_660f0 : decode_any W_660f0 = Some (Branch BC_EQ 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_660f4 : bv 32 := 0x00068513.
Lemma F_660f4 : fetch_word Ubsan.M.loaded_segments (0x66134 : word) = Some W_660f4.
Proof. vm_refl. Qed.
Lemma D_660f4 : decode_any W_660f4 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_660f8 : bv 32 := 0x2e4000ef.
Lemma F_660f8 : fetch_word Ubsan.M.loaded_segments (0x66138 : word) = Some W_660f8.
Proof. vm_refl. Qed.
Lemma D_660f8 : decode_any W_660f8 = Some (Jal 1 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_660fc : bv 32 := 0x0080006f.
Lemma F_660fc : fetch_word Ubsan.M.loaded_segments (0x6613c : word) = Some W_660fc.
Proof. vm_refl. Qed.
Lemma D_660fc : decode_any W_660fc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_66104 : bv 32 := 0x00249613.
Lemma F_66104 : fetch_word Ubsan.M.loaded_segments (0x66144 : word) = Some W_66104.
Proof. vm_refl. Qed.
Lemma D_66104 : decode_any W_66104 = Some (ShiftImm ALU_SLL 12 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_66108 : bv 32 := 0x00a60633.
Lemma F_66108 : fetch_word Ubsan.M.loaded_segments (0x66148 : word) = Some W_66108.
Proof. vm_refl. Qed.
Lemma D_66108 : decode_any W_66108 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6610c : bv 32 := 0x00a036b3.
Lemma F_6610c : fetch_word Ubsan.M.loaded_segments (0x6614c : word) = Some W_6610c.
Proof. vm_refl. Qed.
Lemma D_6610c : decode_any W_6610c = Some (Op ALU_SLTU 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_66110 : bv 32 := 0x00163713.
Lemma F_66110 : fetch_word Ubsan.M.loaded_segments (0x66150 : word) = Some W_66110.
Proof. vm_refl. Qed.
Lemma D_66110 : decode_any W_66110 = Some (OpImm ALU_SLTU 14 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_66114 : bv 32 := 0x00a43023.
Lemma F_66114 : fetch_word Ubsan.M.loaded_segments (0x66154 : word) = Some W_66114.
Proof. vm_refl. Qed.
Lemma D_66114 : decode_any W_66114 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66118 : bv 32 := 0x04e68e63.
Lemma F_66118 : fetch_word Ubsan.M.loaded_segments (0x66158 : word) = Some W_66118.
Proof. vm_refl. Qed.
Lemma D_66118 : decode_any W_66118 = Some (Branch BC_EQ 13 14 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_6611c : bv 32 := 0x00100713.
Lemma F_6611c : fetch_word Ubsan.M.loaded_segments (0x6615c : word) = Some W_6611c.
Proof. vm_refl. Qed.
Lemma D_6611c : decode_any W_6611c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_66120 : bv 32 := 0x03d71713.
Lemma F_66120 : fetch_word Ubsan.M.loaded_segments (0x66160 : word) = Some W_66120.
Proof. vm_refl. Qed.
Lemma D_66120 : decode_any W_66120 = Some (ShiftImm ALU_SLL 14 14 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_66124 : bv 32 := 0x00e484b3.
Lemma F_66124 : fetch_word Ubsan.M.loaded_segments (0x66164 : word) = Some W_66124.
Proof. vm_refl. Qed.
Lemma D_66124 : decode_any W_66124 = Some (Op ALU_ADD 9 9 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_66128 : bv 32 := 0x03e4d493.
Lemma F_66128 : fetch_word Ubsan.M.loaded_segments (0x66168 : word) = Some W_66128.
Proof. vm_refl. Qed.
Lemma D_66128 : decode_any W_66128 = Some (ShiftImm ALU_SRL 9 9 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_6612c : bv 32 := 0x04049463.
Lemma F_6612c : fetch_word Ubsan.M.loaded_segments (0x6616c : word) = Some W_6612c.
Proof. vm_refl. Qed.
Lemma D_6612c : decode_any W_6612c = Some (Branch BC_NE 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_66130 : bv 32 := 0x04a66263.
Lemma F_66130 : fetch_word Ubsan.M.loaded_segments (0x66170 : word) = Some W_66130.
Proof. vm_refl. Qed.
Lemma D_66130 : decode_any W_66130 = Some (Branch BC_LTU 12 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_66134 : bv 32 := 0x00259793.
Lemma F_66134 : fetch_word Ubsan.M.loaded_segments (0x66174 : word) = Some W_66134.
Proof. vm_refl. Qed.
Lemma D_66134 : decode_any W_66134 = Some (ShiftImm ALU_SLL 15 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_66138 : bv 32 := 0x00a787b3.
Lemma F_66138 : fetch_word Ubsan.M.loaded_segments (0x66178 : word) = Some W_66138.
Proof. vm_refl. Qed.
Lemma D_66138 : decode_any W_66138 = Some (Op ALU_ADD 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6613c : bv 32 := 0x0017b813.
Lemma F_6613c : fetch_word Ubsan.M.loaded_segments (0x6617c : word) = Some W_6613c.
Proof. vm_refl. Qed.
Lemma D_6613c : decode_any W_6613c = Some (OpImm ALU_SLTU 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_66140 : bv 32 := 0x00c43423.
Lemma F_66140 : fetch_word Ubsan.M.loaded_segments (0x66180 : word) = Some W_66140.
Proof. vm_refl. Qed.
Lemma D_66140 : decode_any W_66140 = Some (Store SZ8 8 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_66144 : bv 32 := 0x00c43823.
Lemma F_66144 : fetch_word Ubsan.M.loaded_segments (0x66184 : word) = Some W_66144.
Proof. vm_refl. Qed.
Lemma D_66144 : decode_any W_66144 = Some (Store SZ8 8 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_66148 : bv 32 := 0x03068663.
Lemma F_66148 : fetch_word Ubsan.M.loaded_segments (0x66188 : word) = Some W_66148.
Proof. vm_refl. Qed.
Lemma D_66148 : decode_any W_66148 = Some (Branch BC_EQ 13 16 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_6614c : bv 32 := 0x00e585b3.
Lemma F_6614c : fetch_word Ubsan.M.loaded_segments (0x6618c : word) = Some W_6614c.
Proof. vm_refl. Qed.
Lemma D_6614c : decode_any W_6614c = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_66150 : bv 32 := 0x03e5d593.
Lemma F_66150 : fetch_word Ubsan.M.loaded_segments (0x66190 : word) = Some W_66150.
Proof. vm_refl. Qed.
Lemma D_66150 : decode_any W_66150 = Some (ShiftImm ALU_SRL 11 11 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_66154 : bv 32 := 0x02059063.
Lemma F_66154 : fetch_word Ubsan.M.loaded_segments (0x66194 : word) = Some W_66154.
Proof. vm_refl. Qed.
Lemma D_66154 : decode_any W_66154 = Some (Branch BC_NE 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_66158 : bv 32 := 0x00a7ee63.
Lemma F_66158 : fetch_word Ubsan.M.loaded_segments (0x66198 : word) = Some W_66158.
Proof. vm_refl. Qed.
Lemma D_66158 : decode_any W_66158 = Some (Branch BC_LTU 15 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6615c : bv 32 := 0x00f43c23.
Lemma F_6615c : fetch_word Ubsan.M.loaded_segments (0x6619c : word) = Some W_6615c.
Proof. vm_refl. Qed.
Lemma D_6615c : decode_any W_6615c = Some (Store SZ8 8 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_66160 : bv 32 := 0x01813083.
Lemma F_66160 : fetch_word Ubsan.M.loaded_segments (0x661a0 : word) = Some W_66160.
Proof. vm_refl. Qed.
Lemma D_66160 : decode_any W_66160 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_66164 : bv 32 := 0x01013403.
Lemma F_66164 : fetch_word Ubsan.M.loaded_segments (0x661a4 : word) = Some W_66164.
Proof. vm_refl. Qed.
Lemma D_66164 : decode_any W_66164 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_66168 : bv 32 := 0x00813483.
Lemma F_66168 : fetch_word Ubsan.M.loaded_segments (0x661a8 : word) = Some W_66168.
Proof. vm_refl. Qed.
Lemma D_66168 : decode_any W_66168 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6616c : bv 32 := 0x02010113.
Lemma F_6616c : fetch_word Ubsan.M.loaded_segments (0x661ac : word) = Some W_6616c.
Proof. vm_refl. Qed.
Lemma D_6616c : decode_any W_6616c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_66170 : bv 32 := 0x00008067.
Lemma F_66170 : fetch_word Ubsan.M.loaded_segments (0x661b0 : word) = Some W_66170.
Proof. vm_refl. Qed.
Lemma D_66170 : decode_any W_66170 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66178 : bv 32 := 0x01053603.
Lemma F_66178 : fetch_word Ubsan.M.loaded_segments (0x661b8 : word) = Some W_66178.
Proof. vm_refl. Qed.
Lemma D_66178 : decode_any W_66178 = Some (Load SZ8 true 12 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6617c : bv 32 := 0x00259693.
Lemma F_6617c : fetch_word Ubsan.M.loaded_segments (0x661bc : word) = Some W_6617c.
Proof. vm_refl. Qed.
Lemma D_6617c : decode_any W_6617c = Some (ShiftImm ALU_SLL 13 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_66180 : bv 32 := 0x00c68733.
Lemma F_66180 : fetch_word Ubsan.M.loaded_segments (0x661c0 : word) = Some W_66180.
Proof. vm_refl. Qed.
Lemma D_66180 : decode_any W_66180 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_66184 : bv 32 := 0x00c037b3.
Lemma F_66184 : fetch_word Ubsan.M.loaded_segments (0x661c4 : word) = Some W_66184.
Proof. vm_refl. Qed.
Lemma D_66184 : decode_any W_66184 = Some (Op ALU_SLTU 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_66188 : bv 32 := 0x00173813.
Lemma F_66188 : fetch_word Ubsan.M.loaded_segments (0x661c8 : word) = Some W_66188.
Proof. vm_refl. Qed.
Lemma D_66188 : decode_any W_66188 = Some (OpImm ALU_SLTU 16 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6618c : bv 32 := 0x07078663.
Lemma F_6618c : fetch_word Ubsan.M.loaded_segments (0x661cc : word) = Some W_6618c.
Proof. vm_refl. Qed.
Lemma D_6618c : decode_any W_6618c = Some (Branch BC_EQ 15 16 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_66190 : bv 32 := 0x00100793.
Lemma F_66190 : fetch_word Ubsan.M.loaded_segments (0x661d0 : word) = Some W_66190.
Proof. vm_refl. Qed.
Lemma D_66190 : decode_any W_66190 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_66194 : bv 32 := 0x03d79793.
Lemma F_66194 : fetch_word Ubsan.M.loaded_segments (0x661d4 : word) = Some W_66194.
Proof. vm_refl. Qed.
Lemma D_66194 : decode_any W_66194 = Some (ShiftImm ALU_SLL 15 15 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_66198 : bv 32 := 0x00f587b3.
Lemma F_66198 : fetch_word Ubsan.M.loaded_segments (0x661d8 : word) = Some W_66198.
Proof. vm_refl. Qed.
Lemma D_66198 : decode_any W_66198 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6619c : bv 32 := 0x03e7d793.
Lemma F_6619c : fetch_word Ubsan.M.loaded_segments (0x661dc : word) = Some W_6619c.
Proof. vm_refl. Qed.
Lemma D_6619c : decode_any W_6619c = Some (ShiftImm ALU_SRL 15 15 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_661a0 : bv 32 := 0x04079c63.
Lemma F_661a0 : fetch_word Ubsan.M.loaded_segments (0x661e0 : word) = Some W_661a0.
Proof. vm_refl. Qed.
Lemma D_661a0 : decode_any W_661a0 = Some (Branch BC_NE 15 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_661a4 : bv 32 := 0x04c76a63.
Lemma F_661a4 : fetch_word Ubsan.M.loaded_segments (0x661e4 : word) = Some W_661a4.
Proof. vm_refl. Qed.
Lemma D_661a4 : decode_any W_661a4 = Some (Branch BC_LTU 14 12 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_661a8 : bv 32 := 0x04058463.
Lemma F_661a8 : fetch_word Ubsan.M.loaded_segments (0x661e8 : word) = Some W_661a8.
Proof. vm_refl. Qed.
Lemma D_661a8 : decode_any W_661a8 = Some (Branch BC_EQ 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_661ac : bv 32 := 0x00259593.
Lemma F_661ac : fetch_word Ubsan.M.loaded_segments (0x661ec : word) = Some W_661ac.
Proof. vm_refl. Qed.
Lemma D_661ac : decode_any W_661ac = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_661b0 : bv 32 := 0x02053703.
Lemma F_661b0 : fetch_word Ubsan.M.loaded_segments (0x661f0 : word) = Some W_661b0.
Proof. vm_refl. Qed.
Lemma D_661b0 : decode_any W_661b0 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_661b4 : bv 32 := 0x00b605b3.
Lemma F_661b4 : fetch_word Ubsan.M.loaded_segments (0x661f4 : word) = Some W_661b4.
Proof. vm_refl. Qed.
Lemma D_661b4 : decode_any W_661b4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_661b8 : bv 32 := 0x00367793.
Lemma F_661b8 : fetch_word Ubsan.M.loaded_segments (0x661f8 : word) = Some W_661b8.
Proof. vm_refl. Qed.
Lemma D_661b8 : decode_any W_661b8 = Some (OpImm ALU_AND 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_661bc : bv 32 := 0xffc00813.
Lemma F_661bc : fetch_word Ubsan.M.loaded_segments (0x661fc : word) = Some W_661bc.
Proof. vm_refl. Qed.
Lemma D_661bc : decode_any W_661bc = Some (OpImm ALU_ADD 16 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_661c0 : bv 32 := 0x00060893.
Lemma F_661c0 : fetch_word Ubsan.M.loaded_segments (0x66200 : word) = Some W_661c0.
Proof. vm_refl. Qed.
Lemma D_661c0 : decode_any W_661c0 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_661c4 : bv 32 := 0x02070a63.
Lemma F_661c4 : fetch_word Ubsan.M.loaded_segments (0x66204 : word) = Some W_661c4.
Proof. vm_refl. Qed.
Lemma D_661c4 : decode_any W_661c4 = Some (Branch BC_EQ 14 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_661c8 : bv 32 := 0x02060863.
Lemma F_661c8 : fetch_word Ubsan.M.loaded_segments (0x66208 : word) = Some W_661c8.
Proof. vm_refl. Qed.
Lemma D_661c8 : decode_any W_661c8 = Some (Branch BC_EQ 12 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_661cc : bv 32 := 0x02079663.
Lemma F_661cc : fetch_word Ubsan.M.loaded_segments (0x6620c : word) = Some W_661cc.
Proof. vm_refl. Qed.
Lemma D_661cc : decode_any W_661cc = Some (Branch BC_NE 15 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_661d0 : bv 32 := 0x00062023.
Lemma F_661d0 : fetch_word Ubsan.M.loaded_segments (0x66210 : word) = Some W_661d0.
Proof. vm_refl. Qed.
Lemma D_661d0 : decode_any W_661d0 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_661d4 : bv 32 := 0x02088263.
Lemma F_661d4 : fetch_word Ubsan.M.loaded_segments (0x66214 : word) = Some W_661d4.
Proof. vm_refl. Qed.
Lemma D_661d4 : decode_any W_661d4 = Some (Branch BC_EQ 17 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_661d8 : bv 32 := 0x03088063.
Lemma F_661d8 : fetch_word Ubsan.M.loaded_segments (0x66218 : word) = Some W_661d8.
Proof. vm_refl. Qed.
Lemma D_661d8 : decode_any W_661d8 = Some (Branch BC_EQ 17 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_661dc : bv 32 := 0x00460613.
Lemma F_661dc : fetch_word Ubsan.M.loaded_segments (0x6621c : word) = Some W_661dc.
Proof. vm_refl. Qed.
Lemma D_661dc : decode_any W_661dc = Some (OpImm ALU_ADD 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_661e0 : bv 32 := 0xffc68693.
Lemma F_661e0 : fetch_word Ubsan.M.loaded_segments (0x66220 : word) = Some W_661e0.
Proof. vm_refl. Qed.
Lemma D_661e0 : decode_any W_661e0 = Some (OpImm ALU_ADD 13 13 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_661e4 : bv 32 := 0x00488893.
Lemma F_661e4 : fetch_word Ubsan.M.loaded_segments (0x66224 : word) = Some W_661e4.
Proof. vm_refl. Qed.
Lemma D_661e4 : decode_any W_661e4 = Some (OpImm ALU_ADD 17 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_661e8 : bv 32 := 0xfc069ee3.
Lemma F_661e8 : fetch_word Ubsan.M.loaded_segments (0x66228 : word) = Some W_661e8.
Proof. vm_refl. Qed.
Lemma D_661e8 : decode_any W_661e8 = Some (Branch BC_NE 13 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_661ec : bv 32 := 0x00058613.
Lemma F_661ec : fetch_word Ubsan.M.loaded_segments (0x6622c : word) = Some W_661ec.
Proof. vm_refl. Qed.
Lemma D_661ec : decode_any W_661ec = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_661f0 : bv 32 := 0x00c53823.
Lemma F_661f0 : fetch_word Ubsan.M.loaded_segments (0x66230 : word) = Some W_661f0.
Proof. vm_refl. Qed.
Lemma D_661f0 : decode_any W_661f0 = Some (Store SZ8 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_661f4 : bv 32 := 0x00008067.
Lemma F_661f4 : fetch_word Ubsan.M.loaded_segments (0x66234 : word) = Some W_661f4.
Proof. vm_refl. Qed.
Lemma D_661f4 : decode_any W_661f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_661fc : bv 32 := 0xfe010113.
Lemma F_661fc : fetch_word Ubsan.M.loaded_segments (0x6623c : word) = Some W_661fc.
Proof. vm_refl. Qed.
Lemma D_661fc : decode_any W_661fc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_66200 : bv 32 := 0x00113c23.
Lemma F_66200 : fetch_word Ubsan.M.loaded_segments (0x66240 : word) = Some W_66200.
Proof. vm_refl. Qed.
Lemma D_66200 : decode_any W_66200 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_66204 : bv 32 := 0x00813823.
Lemma F_66204 : fetch_word Ubsan.M.loaded_segments (0x66244 : word) = Some W_66204.
Proof. vm_refl. Qed.
Lemma D_66204 : decode_any W_66204 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_66208 : bv 32 := 0x00913423.
Lemma F_66208 : fetch_word Ubsan.M.loaded_segments (0x66248 : word) = Some W_66208.
Proof. vm_refl. Qed.
Lemma D_66208 : decode_any W_66208 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6620c : bv 32 := 0x01213023.
Lemma F_6620c : fetch_word Ubsan.M.loaded_segments (0x6624c : word) = Some W_6620c.
Proof. vm_refl. Qed.
Lemma D_6620c : decode_any W_6620c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66210 : bv 32 := 0x00058413.
Lemma F_66210 : fetch_word Ubsan.M.loaded_segments (0x66250 : word) = Some W_66210.
Proof. vm_refl. Qed.
Lemma D_66210 : decode_any W_66210 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66214 : bv 32 := 0x00050493.
Lemma F_66214 : fetch_word Ubsan.M.loaded_segments (0x66254 : word) = Some W_66214.
Proof. vm_refl. Qed.
Lemma D_66214 : decode_any W_66214 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66218 : bv 32 := 0x00053583.
Lemma F_66218 : fetch_word Ubsan.M.loaded_segments (0x66258 : word) = Some W_66218.
Proof. vm_refl. Qed.
Lemma D_66218 : decode_any W_66218 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6621c : bv 32 := 0x00853603.
Lemma F_6621c : fetch_word Ubsan.M.loaded_segments (0x6625c : word) = Some W_6621c.
Proof. vm_refl. Qed.
Lemma D_6621c : decode_any W_6621c = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_66220 : bv 32 := 0x00843903.
Lemma F_66220 : fetch_word Ubsan.M.loaded_segments (0x66260 : word) = Some W_66220.
Proof. vm_refl. Qed.
Lemma D_66220 : decode_any W_66220 = Some (Load SZ8 true 18 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_66224 : bv 32 := 0x40b60633.
Lemma F_66224 : fetch_word Ubsan.M.loaded_segments (0x66264 : word) = Some W_66224.
Proof. vm_refl. Qed.
Lemma D_66224 : decode_any W_66224 = Some (Op ALU_SUB 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_66228 : bv 32 := 0x40c90533.
Lemma F_66228 : fetch_word Ubsan.M.loaded_segments (0x66268 : word) = Some W_66228.
Proof. vm_refl. Qed.
Lemma D_66228 : decode_any W_66228 = Some (Op ALU_SUB 10 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6622c : bv 32 := 0x012036b3.
Lemma F_6622c : fetch_word Ubsan.M.loaded_segments (0x6626c : word) = Some W_6622c.
Proof. vm_refl. Qed.
Lemma D_6622c : decode_any W_6622c = Some (Op ALU_SLTU 13 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_66230 : bv 32 := 0x00153713.
Lemma F_66230 : fetch_word Ubsan.M.loaded_segments (0x66270 : word) = Some W_66230.
Proof. vm_refl. Qed.
Lemma D_66230 : decode_any W_66230 = Some (OpImm ALU_SLTU 14 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_66234 : bv 32 := 0x0ae68263.
Lemma F_66234 : fetch_word Ubsan.M.loaded_segments (0x66274 : word) = Some W_66234.
Proof. vm_refl. Qed.
Lemma D_66234 : decode_any W_66234 = Some (Branch BC_EQ 13 14 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_66238 : bv 32 := 0x40265693.
Lemma F_66238 : fetch_word Ubsan.M.loaded_segments (0x66278 : word) = Some W_66238.
Proof. vm_refl. Qed.
Lemma D_66238 : decode_any W_66238 = Some (ShiftImm ALU_SRA 13 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6623c : bv 32 := 0xfff00713.
Lemma F_6623c : fetch_word Ubsan.M.loaded_segments (0x6627c : word) = Some W_6623c.
Proof. vm_refl. Qed.
Lemma D_6623c : decode_any W_6623c = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_66240 : bv 32 := 0x00375713.
Lemma F_66240 : fetch_word Ubsan.M.loaded_segments (0x66280 : word) = Some W_66240.
Proof. vm_refl. Qed.
Lemma D_66240 : decode_any W_66240 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_66244 : bv 32 := 0x00e68733.
Lemma F_66244 : fetch_word Ubsan.M.loaded_segments (0x66284 : word) = Some W_66244.
Proof. vm_refl. Qed.
Lemma D_66244 : decode_any W_66244 = Some (Op ALU_ADD 14 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_66248 : bv 32 := 0x03e75713.
Lemma F_66248 : fetch_word Ubsan.M.loaded_segments (0x66288 : word) = Some W_66248.
Proof. vm_refl. Qed.
Lemma D_66248 : decode_any W_66248 = Some (ShiftImm ALU_SRL 14 14 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_6624c : bv 32 := 0x08071663.
Lemma F_6624c : fetch_word Ubsan.M.loaded_segments (0x6628c : word) = Some W_6624c.
Proof. vm_refl. Qed.
Lemma D_6624c : decode_any W_6624c = Some (Branch BC_NE 14 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_66250 : bv 32 := 0x40d006b3.
Lemma F_66250 : fetch_word Ubsan.M.loaded_segments (0x66290 : word) = Some W_66250.
Proof. vm_refl. Qed.
Lemma D_66250 : decode_any W_66250 = Some (Op ALU_SUB 13 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_66254 : bv 32 := 0x00269693.
Lemma F_66254 : fetch_word Ubsan.M.loaded_segments (0x66294 : word) = Some W_66254.
Proof. vm_refl. Qed.
Lemma D_66254 : decode_any W_66254 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_66258 : bv 32 := 0x01253533.
Lemma F_66258 : fetch_word Ubsan.M.loaded_segments (0x66298 : word) = Some W_66258.
Proof. vm_refl. Qed.
Lemma D_66258 : decode_any W_66258 = Some (Op ALU_SLTU 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6625c : bv 32 := 0x0006a713.
Lemma F_6625c : fetch_word Ubsan.M.loaded_segments (0x6629c : word) = Some W_6625c.
Proof. vm_refl. Qed.
Lemma D_6625c : decode_any W_6625c = Some (OpImm ALU_SLT 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66260 : bv 32 := 0x00e54533.
Lemma F_66260 : fetch_word Ubsan.M.loaded_segments (0x662a0 : word) = Some W_66260.
Proof. vm_refl. Qed.
Lemma D_66260 : decode_any W_66260 = Some (Op ALU_XOR 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_66264 : bv 32 := 0x00154513.
Lemma F_66264 : fetch_word Ubsan.M.loaded_segments (0x662a4 : word) = Some W_66264.
Proof. vm_refl. Qed.
Lemma D_66264 : decode_any W_66264 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_66268 : bv 32 := 0x06050863.
Lemma F_66268 : fetch_word Ubsan.M.loaded_segments (0x662a8 : word) = Some W_66268.
Proof. vm_refl. Qed.
Lemma D_66268 : decode_any W_66268 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6626c : bv 32 := 0x0035f513.
Lemma F_6626c : fetch_word Ubsan.M.loaded_segments (0x662ac : word) = Some W_6626c.
Proof. vm_refl. Qed.
Lemma D_6626c : decode_any W_6626c = Some (OpImm ALU_AND 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_66270 : bv 32 := 0x06051463.
Lemma F_66270 : fetch_word Ubsan.M.loaded_segments (0x662b0 : word) = Some W_66270.
Proof. vm_refl. Qed.
Lemma D_66270 : decode_any W_66270 = Some (Branch BC_NE 10 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_66274 : bv 32 := 0x00d90933.
Lemma F_66274 : fetch_word Ubsan.M.loaded_segments (0x662b4 : word) = Some W_66274.
Proof. vm_refl. Qed.
Lemma D_66274 : decode_any W_66274 = Some (Op ALU_ADD 18 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_66278 : bv 32 := 0x00090513.
Lemma F_66278 : fetch_word Ubsan.M.loaded_segments (0x662b8 : word) = Some W_66278.
Proof. vm_refl. Qed.
Lemma D_66278 : decode_any W_66278 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6627c : bv 32 := 0x0e17c0ef.
Lemma F_6627c : fetch_word Ubsan.M.loaded_segments (0x662bc : word) = Some W_6627c.
Proof. vm_refl. Qed.
Lemma D_6627c : decode_any W_6627c = Some (Jal 1 510176, 4%Z).
Proof. vm_refl. Qed.

Definition W_66280 : bv 32 := 0x0004b503.
Lemma F_66280 : fetch_word Ubsan.M.loaded_segments (0x662c0 : word) = Some W_66280.
Proof. vm_refl. Qed.
Lemma D_66280 : decode_any W_66280 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66284 : bv 32 := 0x01243423.
Lemma F_66284 : fetch_word Ubsan.M.loaded_segments (0x662c4 : word) = Some W_66284.
Proof. vm_refl. Qed.
Lemma D_66284 : decode_any W_66284 = Some (Store SZ8 8 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_66288 : bv 32 := 0x00a4b423.
Lemma F_66288 : fetch_word Ubsan.M.loaded_segments (0x662c8 : word) = Some W_66288.
Proof. vm_refl. Qed.
Lemma D_66288 : decode_any W_66288 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6628c : bv 32 := 0x00843583.
Lemma F_6628c : fetch_word Ubsan.M.loaded_segments (0x662cc : word) = Some W_6628c.
Proof. vm_refl. Qed.
Lemma D_6628c : decode_any W_6628c = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_66290 : bv 32 := 0x00b4b023.
Lemma F_66290 : fetch_word Ubsan.M.loaded_segments (0x662d0 : word) = Some W_66290.
Proof. vm_refl. Qed.
Lemma D_66290 : decode_any W_66290 = Some (Store SZ8 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66294 : bv 32 := 0x01043583.
Lemma F_66294 : fetch_word Ubsan.M.loaded_segments (0x662d4 : word) = Some W_66294.
Proof. vm_refl. Qed.
Lemma D_66294 : decode_any W_66294 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_66298 : bv 32 := 0x00a43423.
Lemma F_66298 : fetch_word Ubsan.M.loaded_segments (0x662d8 : word) = Some W_66298.
Proof. vm_refl. Qed.
Lemma D_66298 : decode_any W_66298 = Some (Store SZ8 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6629c : bv 32 := 0x0084b503.
Lemma F_6629c : fetch_word Ubsan.M.loaded_segments (0x662dc : word) = Some W_6629c.
Proof. vm_refl. Qed.
Lemma D_6629c : decode_any W_6629c = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_662a0 : bv 32 := 0x00b4b423.
Lemma F_662a0 : fetch_word Ubsan.M.loaded_segments (0x662e0 : word) = Some W_662a0.
Proof. vm_refl. Qed.
Lemma D_662a0 : decode_any W_662a0 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_662a4 : bv 32 := 0x01843583.
Lemma F_662a4 : fetch_word Ubsan.M.loaded_segments (0x662e4 : word) = Some W_662a4.
Proof. vm_refl. Qed.
Lemma D_662a4 : decode_any W_662a4 = Some (Load SZ8 true 11 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_662a8 : bv 32 := 0x00a43823.
Lemma F_662a8 : fetch_word Ubsan.M.loaded_segments (0x662e8 : word) = Some W_662a8.
Proof. vm_refl. Qed.
Lemma D_662a8 : decode_any W_662a8 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_662ac : bv 32 := 0x0104b503.
Lemma F_662ac : fetch_word Ubsan.M.loaded_segments (0x662ec : word) = Some W_662ac.
Proof. vm_refl. Qed.
Lemma D_662ac : decode_any W_662ac = Some (Load SZ8 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_662b0 : bv 32 := 0x00b4b823.
Lemma F_662b0 : fetch_word Ubsan.M.loaded_segments (0x662f0 : word) = Some W_662b0.
Proof. vm_refl. Qed.
Lemma D_662b0 : decode_any W_662b0 = Some (Store SZ8 9 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_662b4 : bv 32 := 0x00843583.
Lemma F_662b4 : fetch_word Ubsan.M.loaded_segments (0x662f4 : word) = Some W_662b4.
Proof. vm_refl. Qed.
Lemma D_662b4 : decode_any W_662b4 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_662b8 : bv 32 := 0x00b43023.
Lemma F_662b8 : fetch_word Ubsan.M.loaded_segments (0x662f8 : word) = Some W_662b8.
Proof. vm_refl. Qed.
Lemma D_662b8 : decode_any W_662b8 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_662bc : bv 32 := 0x00a43c23.
Lemma F_662bc : fetch_word Ubsan.M.loaded_segments (0x662fc : word) = Some W_662bc.
Proof. vm_refl. Qed.
Lemma D_662bc : decode_any W_662bc = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_662c0 : bv 32 := 0x01813083.
Lemma F_662c0 : fetch_word Ubsan.M.loaded_segments (0x66300 : word) = Some W_662c0.
Proof. vm_refl. Qed.
Lemma D_662c0 : decode_any W_662c0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_662c4 : bv 32 := 0x01013403.
Lemma F_662c4 : fetch_word Ubsan.M.loaded_segments (0x66304 : word) = Some W_662c4.
Proof. vm_refl. Qed.
Lemma D_662c4 : decode_any W_662c4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_662c8 : bv 32 := 0x00813483.
Lemma F_662c8 : fetch_word Ubsan.M.loaded_segments (0x66308 : word) = Some W_662c8.
Proof. vm_refl. Qed.
Lemma D_662c8 : decode_any W_662c8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_662cc : bv 32 := 0x00013903.
Lemma F_662cc : fetch_word Ubsan.M.loaded_segments (0x6630c : word) = Some W_662cc.
Proof. vm_refl. Qed.
Lemma D_662cc : decode_any W_662cc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_662d0 : bv 32 := 0x02010113.
Lemma F_662d0 : fetch_word Ubsan.M.loaded_segments (0x66310 : word) = Some W_662d0.
Proof. vm_refl. Qed.
Lemma D_662d0 : decode_any W_662d0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_662d4 : bv 32 := 0x00008067.
Lemma F_662d4 : fetch_word Ubsan.M.loaded_segments (0x66314 : word) = Some W_662d4.
Proof. vm_refl. Qed.
Lemma D_662d4 : decode_any W_662d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_662dc : bv 32 := 0x00853603.
Lemma F_662dc : fetch_word Ubsan.M.loaded_segments (0x6631c : word) = Some W_662dc.
Proof. vm_refl. Qed.
Lemma D_662dc : decode_any W_662dc = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_662e0 : bv 32 := 0x01053683.
Lemma F_662e0 : fetch_word Ubsan.M.loaded_segments (0x66320 : word) = Some W_662e0.
Proof. vm_refl. Qed.
Lemma D_662e0 : decode_any W_662e0 = Some (Load SZ8 true 13 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_662e4 : bv 32 := 0x02053583.
Lemma F_662e4 : fetch_word Ubsan.M.loaded_segments (0x66324 : word) = Some W_662e4.
Proof. vm_refl. Qed.
Lemma D_662e4 : decode_any W_662e4 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_662e8 : bv 32 := 0x00d60e63.
Lemma F_662e8 : fetch_word Ubsan.M.loaded_segments (0x66328 : word) = Some W_662e8.
Proof. vm_refl. Qed.
Lemma D_662e8 : decode_any W_662e8 = Some (Branch BC_EQ 12 13 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_66304 : bv 32 := 0x00053603.
Lemma F_66304 : fetch_word Ubsan.M.loaded_segments (0x66344 : word) = Some W_66304.
Proof. vm_refl. Qed.
Lemma D_66304 : decode_any W_66304 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66308 : bv 32 := 0x00060c63.
Lemma F_66308 : fetch_word Ubsan.M.loaded_segments (0x66348 : word) = Some W_66308.
Proof. vm_refl. Qed.
Lemma D_66308 : decode_any W_66308 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_66320 : bv 32 := 0x00008067.
Lemma F_66320 : fetch_word Ubsan.M.loaded_segments (0x66360 : word) = Some W_66320.
Proof. vm_refl. Qed.
Lemma D_66320 : decode_any W_66320 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
