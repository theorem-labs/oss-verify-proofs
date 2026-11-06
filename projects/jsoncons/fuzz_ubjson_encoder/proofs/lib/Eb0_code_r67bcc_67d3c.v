(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_82fc8 : bv 32 := 0x000c4517.
Lemma F_82fc8 : fetch_word AsanUbsan.M.loaded_segments (0x83018 : word) = Some W_82fc8.
Proof. vm_refl. Qed.
Lemma D_82fc8 : decode_any W_82fc8 = Some (Auipc 10 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fcc : bv 32 := 0xde452503.
Lemma F_82fcc : fetch_word AsanUbsan.M.loaded_segments (0x8301c : word) = Some W_82fcc.
Proof. vm_refl. Qed.
Lemma D_82fcc : decode_any W_82fcc = Some (Load SZ4 true 10 10 3556, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fd0 : bv 32 := 0x0230000f.
Lemma F_82fd0 : fetch_word AsanUbsan.M.loaded_segments (0x83020 : word) = Some W_82fd0.
Proof. vm_refl. Qed.
Lemma D_82fd0 : decode_any W_82fd0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fd4 : bv 32 := 0x00008067.
Lemma F_82fd4 : fetch_word AsanUbsan.M.loaded_segments (0x83024 : word) = Some W_82fd4.
Proof. vm_refl. Qed.
Lemma D_82fd4 : decode_any W_82fd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fd8 : bv 32 := 0xfb010113.
Lemma F_82fd8 : fetch_word AsanUbsan.M.loaded_segments (0x83028 : word) = Some W_82fd8.
Proof. vm_refl. Qed.
Lemma D_82fd8 : decode_any W_82fd8 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fdc : bv 32 := 0x04113423.
Lemma F_82fdc : fetch_word AsanUbsan.M.loaded_segments (0x8302c : word) = Some W_82fdc.
Proof. vm_refl. Qed.
Lemma D_82fdc : decode_any W_82fdc = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fe0 : bv 32 := 0x04813023.
Lemma F_82fe0 : fetch_word AsanUbsan.M.loaded_segments (0x83030 : word) = Some W_82fe0.
Proof. vm_refl. Qed.
Lemma D_82fe0 : decode_any W_82fe0 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fe4 : bv 32 := 0x02913c23.
Lemma F_82fe4 : fetch_word AsanUbsan.M.loaded_segments (0x83034 : word) = Some W_82fe4.
Proof. vm_refl. Qed.
Lemma D_82fe4 : decode_any W_82fe4 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fe8 : bv 32 := 0x03213823.
Lemma F_82fe8 : fetch_word AsanUbsan.M.loaded_segments (0x83038 : word) = Some W_82fe8.
Proof. vm_refl. Qed.
Lemma D_82fe8 : decode_any W_82fe8 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82fec : bv 32 := 0x03313423.
Lemma F_82fec : fetch_word AsanUbsan.M.loaded_segments (0x8303c : word) = Some W_82fec.
Proof. vm_refl. Qed.
Lemma D_82fec : decode_any W_82fec = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ff0 : bv 32 := 0x03413023.
Lemma F_82ff0 : fetch_word AsanUbsan.M.loaded_segments (0x83040 : word) = Some W_82ff0.
Proof. vm_refl. Qed.
Lemma D_82ff0 : decode_any W_82ff0 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ff4 : bv 32 := 0x01513c23.
Lemma F_82ff4 : fetch_word AsanUbsan.M.loaded_segments (0x83044 : word) = Some W_82ff4.
Proof. vm_refl. Qed.
Lemma D_82ff4 : decode_any W_82ff4 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ff8 : bv 32 := 0x01613823.
Lemma F_82ff8 : fetch_word AsanUbsan.M.loaded_segments (0x83048 : word) = Some W_82ff8.
Proof. vm_refl. Qed.
Lemma D_82ff8 : decode_any W_82ff8 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ffc : bv 32 := 0x01713423.
Lemma F_82ffc : fetch_word AsanUbsan.M.loaded_segments (0x8304c : word) = Some W_82ffc.
Proof. vm_refl. Qed.
Lemma D_82ffc : decode_any W_82ffc = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_83000 : bv 32 := 0x01813023.
Lemma F_83000 : fetch_word AsanUbsan.M.loaded_segments (0x83050 : word) = Some W_83000.
Proof. vm_refl. Qed.
Lemma D_83000 : decode_any W_83000 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83004 : bv 32 := 0x00078493.
Lemma F_83004 : fetch_word AsanUbsan.M.loaded_segments (0x83054 : word) = Some W_83004.
Proof. vm_refl. Qed.
Lemma D_83004 : decode_any W_83004 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83008 : bv 32 := 0x00070a93.
Lemma F_83008 : fetch_word AsanUbsan.M.loaded_segments (0x83058 : word) = Some W_83008.
Proof. vm_refl. Qed.
Lemma D_83008 : decode_any W_83008 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8300c : bv 32 := 0x00068a13.
Lemma F_8300c : fetch_word AsanUbsan.M.loaded_segments (0x8305c : word) = Some W_8300c.
Proof. vm_refl. Qed.
Lemma D_8300c : decode_any W_8300c = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83010 : bv 32 := 0x00060413.
Lemma F_83010 : fetch_word AsanUbsan.M.loaded_segments (0x83060 : word) = Some W_83010.
Proof. vm_refl. Qed.
Lemma D_83010 : decode_any W_83010 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83014 : bv 32 := 0x00058913.
Lemma F_83014 : fetch_word AsanUbsan.M.loaded_segments (0x83064 : word) = Some W_83014.
Proof. vm_refl. Qed.
Lemma D_83014 : decode_any W_83014 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83018 : bv 32 := 0x00050993.
Lemma F_83018 : fetch_word AsanUbsan.M.loaded_segments (0x83068 : word) = Some W_83018.
Proof. vm_refl. Qed.
Lemma D_83018 : decode_any W_83018 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8301c : bv 32 := 0x00052423.
Lemma F_8301c : fetch_word AsanUbsan.M.loaded_segments (0x8306c : word) = Some W_8301c.
Proof. vm_refl. Qed.
Lemma D_8301c : decode_any W_8301c = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_83020 : bv 32 := 0xb10fe0ef.
Lemma F_83020 : fetch_word AsanUbsan.M.loaded_segments (0x83070 : word) = Some W_83020.
Proof. vm_refl. Qed.
Lemma D_83020 : decode_any W_83020 = Some (Jal 1 2089744, 4%Z).
Proof. vm_refl. Qed.

Definition W_83024 : bv 32 := 0x0c050a63.
Lemma F_83024 : fetch_word AsanUbsan.M.loaded_segments (0x83074 : word) = Some W_83024.
Proof. vm_refl. Qed.
Lemma D_83024 : decode_any W_83024 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_83028 : bv 32 := 0x219010ef.
Lemma F_83028 : fetch_word AsanUbsan.M.loaded_segments (0x83078 : word) = Some W_83028.
Proof. vm_refl. Qed.
Lemma D_83028 : decode_any W_83028 = Some (Jal 1 6680, 4%Z).
Proof. vm_refl. Qed.

Definition W_8302c : bv 32 := 0x04050a63.
Lemma F_8302c : fetch_word AsanUbsan.M.loaded_segments (0x8307c : word) = Some W_8302c.
Proof. vm_refl. Qed.
Lemma D_8302c : decode_any W_8302c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_83030 : bv 32 := 0x7ff50c13.
Lemma F_83030 : fetch_word AsanUbsan.M.loaded_segments (0x83080 : word) = Some W_83030.
Proof. vm_refl. Qed.
Lemma D_83030 : decode_any W_83030 = Some (OpImm ALU_ADD 24 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_83034 : bv 32 := 0x461c4583.
Lemma F_83034 : fetch_word AsanUbsan.M.loaded_segments (0x83084 : word) = Some W_83034.
Proof. vm_refl. Qed.
Lemma D_83034 : decode_any W_83034 = Some (Load SZ1 false 11 24 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_83038 : bv 32 := 0x00100613.
Lemma F_83038 : fetch_word AsanUbsan.M.loaded_segments (0x83088 : word) = Some W_83038.
Proof. vm_refl. Qed.
Lemma D_83038 : decode_any W_83038 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8303c : bv 32 := 0x46cc00a3.
Lemma F_8303c : fetch_word AsanUbsan.M.loaded_segments (0x8308c : word) = Some W_8303c.
Proof. vm_refl. Qed.
Lemma D_8303c : decode_any W_8303c = Some (Store SZ1 24 12 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_83040 : bv 32 := 0x0a059a63.
Lemma F_83040 : fetch_word AsanUbsan.M.loaded_segments (0x83090 : word) = Some W_83040.
Proof. vm_refl. Qed.
Lemma D_83040 : decode_any W_83040 = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_83044 : bv 32 := 0x00050b93.
Lemma F_83044 : fetch_word AsanUbsan.M.loaded_segments (0x83094 : word) = Some W_83044.
Proof. vm_refl. Qed.
Lemma D_83044 : decode_any W_83044 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83048 : bv 32 := 0x3bd010ef.
Lemma F_83048 : fetch_word AsanUbsan.M.loaded_segments (0x83098 : word) = Some W_83048.
Proof. vm_refl. Qed.
Lemma D_83048 : decode_any W_83048 = Some (Jal 1 7100, 4%Z).
Proof. vm_refl. Qed.

Definition W_8304c : bv 32 := 0x00050b13.
Lemma F_8304c : fetch_word AsanUbsan.M.loaded_segments (0x8309c : word) = Some W_8304c.
Proof. vm_refl. Qed.
Lemma D_8304c : decode_any W_8304c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83050 : bv 32 := 0x000b8513.
Lemma F_83050 : fetch_word AsanUbsan.M.loaded_segments (0x830a0 : word) = Some W_83050.
Proof. vm_refl. Qed.
Lemma D_83050 : decode_any W_83050 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83054 : bv 32 := 0x409010ef.
Lemma F_83054 : fetch_word AsanUbsan.M.loaded_segments (0x830a4 : word) = Some W_83054.
Proof. vm_refl. Qed.
Lemma D_83054 : decode_any W_83054 = Some (Jal 1 7176, 4%Z).
Proof. vm_refl. Qed.

Definition W_83058 : bv 32 := 0x00050813.
Lemma F_83058 : fetch_word AsanUbsan.M.loaded_segments (0x830a8 : word) = Some W_83058.
Proof. vm_refl. Qed.
Lemma D_83058 : decode_any W_83058 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8305c : bv 32 := 0x060a8c63.
Lemma F_8305c : fetch_word AsanUbsan.M.loaded_segments (0x830ac : word) = Some W_8305c.
Proof. vm_refl. Qed.
Lemma D_8305c : decode_any W_8305c = Some (Branch BC_EQ 21 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_83060 : bv 32 := 0x00100893.
Lemma F_83060 : fetch_word AsanUbsan.M.loaded_segments (0x830b0 : word) = Some W_83060.
Proof. vm_refl. Qed.
Lemma D_83060 : decode_any W_83060 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_83064 : bv 32 := 0x00098513.
Lemma F_83064 : fetch_word AsanUbsan.M.loaded_segments (0x830b4 : word) = Some W_83064.
Proof. vm_refl. Qed.
Lemma D_83064 : decode_any W_83064 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83068 : bv 32 := 0x00048593.
Lemma F_83068 : fetch_word AsanUbsan.M.loaded_segments (0x830b8 : word) = Some W_83068.
Proof. vm_refl. Qed.
Lemma D_83068 : decode_any W_83068 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8306c : bv 32 := 0x00090613.
Lemma F_8306c : fetch_word AsanUbsan.M.loaded_segments (0x830bc : word) = Some W_8306c.
Proof. vm_refl. Qed.
Lemma D_8306c : decode_any W_8306c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83070 : bv 32 := 0x00040693.
Lemma F_83070 : fetch_word AsanUbsan.M.loaded_segments (0x830c0 : word) = Some W_83070.
Proof. vm_refl. Qed.
Lemma D_83070 : decode_any W_83070 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83074 : bv 32 := 0x00000713.
Lemma F_83074 : fetch_word AsanUbsan.M.loaded_segments (0x830c4 : word) = Some W_83074.
Proof. vm_refl. Qed.
Lemma D_83074 : decode_any W_83074 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83078 : bv 32 := 0x000b0793.
Lemma F_83078 : fetch_word AsanUbsan.M.loaded_segments (0x830c8 : word) = Some W_83078.
Proof. vm_refl. Qed.
Lemma D_83078 : decode_any W_83078 = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8307c : bv 32 := 0x0740006f.
Lemma F_8307c : fetch_word AsanUbsan.M.loaded_segments (0x830cc : word) = Some W_8307c.
Proof. vm_refl. Qed.
Lemma D_8307c : decode_any W_8307c = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_830f0 : bv 32 := 0x018190ef.
Lemma F_830f0 : fetch_word AsanUbsan.M.loaded_segments (0x83140 : word) = Some W_830f0.
Proof. vm_refl. Qed.
Lemma D_830f0 : decode_any W_830f0 = Some (Jal 1 102424, 4%Z).
Proof. vm_refl. Qed.

Definition W_830f4 : bv 32 := 0x460c00a3.
Lemma F_830f4 : fetch_word AsanUbsan.M.loaded_segments (0x83144 : word) = Some W_830f4.
Proof. vm_refl. Qed.
Lemma D_830f4 : decode_any W_830f4 = Some (Store SZ1 24 0 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_830f8 : bv 32 := 0x04813083.
Lemma F_830f8 : fetch_word AsanUbsan.M.loaded_segments (0x83148 : word) = Some W_830f8.
Proof. vm_refl. Qed.
Lemma D_830f8 : decode_any W_830f8 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_830fc : bv 32 := 0x04013403.
Lemma F_830fc : fetch_word AsanUbsan.M.loaded_segments (0x8314c : word) = Some W_830fc.
Proof. vm_refl. Qed.
Lemma D_830fc : decode_any W_830fc = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_83100 : bv 32 := 0x03813483.
Lemma F_83100 : fetch_word AsanUbsan.M.loaded_segments (0x83150 : word) = Some W_83100.
Proof. vm_refl. Qed.
Lemma D_83100 : decode_any W_83100 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_83104 : bv 32 := 0x03013903.
Lemma F_83104 : fetch_word AsanUbsan.M.loaded_segments (0x83154 : word) = Some W_83104.
Proof. vm_refl. Qed.
Lemma D_83104 : decode_any W_83104 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_83108 : bv 32 := 0x02813983.
Lemma F_83108 : fetch_word AsanUbsan.M.loaded_segments (0x83158 : word) = Some W_83108.
Proof. vm_refl. Qed.
Lemma D_83108 : decode_any W_83108 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8310c : bv 32 := 0x02013a03.
Lemma F_8310c : fetch_word AsanUbsan.M.loaded_segments (0x8315c : word) = Some W_8310c.
Proof. vm_refl. Qed.
Lemma D_8310c : decode_any W_8310c = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_83110 : bv 32 := 0x01813a83.
Lemma F_83110 : fetch_word AsanUbsan.M.loaded_segments (0x83160 : word) = Some W_83110.
Proof. vm_refl. Qed.
Lemma D_83110 : decode_any W_83110 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_83114 : bv 32 := 0x01013b03.
Lemma F_83114 : fetch_word AsanUbsan.M.loaded_segments (0x83164 : word) = Some W_83114.
Proof. vm_refl. Qed.
Lemma D_83114 : decode_any W_83114 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_83118 : bv 32 := 0x00813b83.
Lemma F_83118 : fetch_word AsanUbsan.M.loaded_segments (0x83168 : word) = Some W_83118.
Proof. vm_refl. Qed.
Lemma D_83118 : decode_any W_83118 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8311c : bv 32 := 0x00013c03.
Lemma F_8311c : fetch_word AsanUbsan.M.loaded_segments (0x8316c : word) = Some W_8311c.
Proof. vm_refl. Qed.
Lemma D_8311c : decode_any W_8311c = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_83120 : bv 32 := 0x05010113.
Lemma F_83120 : fetch_word AsanUbsan.M.loaded_segments (0x83170 : word) = Some W_83120.
Proof. vm_refl. Qed.
Lemma D_83120 : decode_any W_83120 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_83124 : bv 32 := 0x00008067.
Lemma F_83124 : fetch_word AsanUbsan.M.loaded_segments (0x83174 : word) = Some W_83124.
Proof. vm_refl. Qed.
Lemma D_83124 : decode_any W_83124 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
