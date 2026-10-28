(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_174ffc : bv 32 := 0x0ff5f593.
Lemma F_174ffc : fetch_word AsanUbsan.M.loaded_segments (0x1769a4 : word) = Some W_174ffc.
Proof. vm_refl. Qed.
Lemma D_174ffc : decode_any W_174ffc = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_175000 : bv 32 := 0x00757693.
Lemma F_175000 : fetch_word AsanUbsan.M.loaded_segments (0x1769a8 : word) = Some W_175000.
Proof. vm_refl. Qed.
Lemma D_175000 : decode_any W_175000 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_175004 : bv 32 := 0x00c03733.
Lemma F_175004 : fetch_word AsanUbsan.M.loaded_segments (0x1769ac : word) = Some W_175004.
Proof. vm_refl. Qed.
Lemma D_175004 : decode_any W_175004 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_175008 : bv 32 := 0x02068c63.
Lemma F_175008 : fetch_word AsanUbsan.M.loaded_segments (0x1769b0 : word) = Some W_175008.
Proof. vm_refl. Qed.
Lemma D_175008 : decode_any W_175008 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_17500c : bv 32 := 0x02060a63.
Lemma F_17500c : fetch_word AsanUbsan.M.loaded_segments (0x1769b4 : word) = Some W_17500c.
Proof. vm_refl. Qed.
Lemma D_17500c : decode_any W_17500c = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_175010 : bv 32 := 0x00150793.
Lemma F_175010 : fetch_word AsanUbsan.M.loaded_segments (0x1769b8 : word) = Some W_175010.
Proof. vm_refl. Qed.
Lemma D_175010 : decode_any W_175010 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_175014 : bv 32 := 0x00100813.
Lemma F_175014 : fetch_word AsanUbsan.M.loaded_segments (0x1769bc : word) = Some W_175014.
Proof. vm_refl. Qed.
Lemma D_175014 : decode_any W_175014 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_175018 : bv 32 := 0x00054703.
Lemma F_175018 : fetch_word AsanUbsan.M.loaded_segments (0x1769c0 : word) = Some W_175018.
Proof. vm_refl. Qed.
Lemma D_175018 : decode_any W_175018 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17501c : bv 32 := 0x00060693.
Lemma F_17501c : fetch_word AsanUbsan.M.loaded_segments (0x1769c4 : word) = Some W_17501c.
Proof. vm_refl. Qed.
Lemma D_17501c : decode_any W_17501c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175020 : bv 32 := 0x06b70e63.
Lemma F_175020 : fetch_word AsanUbsan.M.loaded_segments (0x1769c8 : word) = Some W_175020.
Proof. vm_refl. Qed.
Lemma D_175020 : decode_any W_175020 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_175024 : bv 32 := 0x00150513.
Lemma F_175024 : fetch_word AsanUbsan.M.loaded_segments (0x1769cc : word) = Some W_175024.
Proof. vm_refl. Qed.
Lemma D_175024 : decode_any W_175024 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_175028 : bv 32 := 0xfff68613.
Lemma F_175028 : fetch_word AsanUbsan.M.loaded_segments (0x1769d0 : word) = Some W_175028.
Proof. vm_refl. Qed.
Lemma D_175028 : decode_any W_175028 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17502c : bv 32 := 0x0077f893.
Lemma F_17502c : fetch_word AsanUbsan.M.loaded_segments (0x1769d4 : word) = Some W_17502c.
Proof. vm_refl. Qed.
Lemma D_17502c : decode_any W_17502c = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_175030 : bv 32 := 0x00c03733.
Lemma F_175030 : fetch_word AsanUbsan.M.loaded_segments (0x1769d8 : word) = Some W_175030.
Proof. vm_refl. Qed.
Lemma D_175030 : decode_any W_175030 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_175034 : bv 32 := 0x00088663.
Lemma F_175034 : fetch_word AsanUbsan.M.loaded_segments (0x1769dc : word) = Some W_175034.
Proof. vm_refl. Qed.
Lemma D_175034 : decode_any W_175034 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_175038 : bv 32 := 0x00178793.
Lemma F_175038 : fetch_word AsanUbsan.M.loaded_segments (0x1769e0 : word) = Some W_175038.
Proof. vm_refl. Qed.
Lemma D_175038 : decode_any W_175038 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17503c : bv 32 := 0xfd069ee3.
Lemma F_17503c : fetch_word AsanUbsan.M.loaded_segments (0x1769e4 : word) = Some W_17503c.
Proof. vm_refl. Qed.
Lemma D_17503c : decode_any W_17503c = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_175040 : bv 32 := 0x06070863.
Lemma F_175040 : fetch_word AsanUbsan.M.loaded_segments (0x1769e8 : word) = Some W_175040.
Proof. vm_refl. Qed.
Lemma D_175040 : decode_any W_175040 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_175044 : bv 32 := 0x00054683.
Lemma F_175044 : fetch_word AsanUbsan.M.loaded_segments (0x1769ec : word) = Some W_175044.
Proof. vm_refl. Qed.
Lemma D_175044 : decode_any W_175044 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175048 : bv 32 := 0x04b68663.
Lemma F_175048 : fetch_word AsanUbsan.M.loaded_segments (0x1769f0 : word) = Some W_175048.
Proof. vm_refl. Qed.
Lemma D_175048 : decode_any W_175048 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_17504c : bv 32 := 0x00800693.
Lemma F_17504c : fetch_word AsanUbsan.M.loaded_segments (0x1769f4 : word) = Some W_17504c.
Proof. vm_refl. Qed.
Lemma D_17504c : decode_any W_17504c = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_175050 : bv 32 := 0x04d66263.
Lemma F_175050 : fetch_word AsanUbsan.M.loaded_segments (0x1769f8 : word) = Some W_175050.
Proof. vm_refl. Qed.
Lemma D_175050 : decode_any W_175050 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_175054 : bv 32 := 0xffe9a697.
Lemma F_175054 : fetch_word AsanUbsan.M.loaded_segments (0x1769fc : word) = Some W_175054.
Proof. vm_refl. Qed.
Lemma D_175054 : decode_any W_175054 = Some (Auipc 13 1048218, 4%Z).
Proof. vm_refl. Qed.

Definition W_175058 : bv 32 := 0x9f46b683.
Lemma F_175058 : fetch_word AsanUbsan.M.loaded_segments (0x176a00 : word) = Some W_175058.
Proof. vm_refl. Qed.
Lemma D_175058 : decode_any W_175058 = Some (Load SZ8 true 13 13 2548, 4%Z).
Proof. vm_refl. Qed.

Definition W_17505c : bv 32 := 0xffe9a717.
Lemma F_17505c : fetch_word AsanUbsan.M.loaded_segments (0x176a04 : word) = Some W_17505c.
Proof. vm_refl. Qed.
Lemma D_17505c : decode_any W_17505c = Some (Auipc 14 1048218, 4%Z).
Proof. vm_refl. Qed.

Definition W_175060 : bv 32 := 0x9d473703.
Lemma F_175060 : fetch_word AsanUbsan.M.loaded_segments (0x176a08 : word) = Some W_175060.
Proof. vm_refl. Qed.
Lemma D_175060 : decode_any W_175060 = Some (Load SZ8 true 14 14 2516, 4%Z).
Proof. vm_refl. Qed.

Definition W_175064 : bv 32 := 0x00168793.
Lemma F_175064 : fetch_word AsanUbsan.M.loaded_segments (0x176a0c : word) = Some W_175064.
Proof. vm_refl. Qed.
Lemma D_175064 : decode_any W_175064 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_175068 : bv 32 := 0x02f587b3.
Lemma F_175068 : fetch_word AsanUbsan.M.loaded_segments (0x176a10 : word) = Some W_175068.
Proof. vm_refl. Qed.
Lemma D_175068 : decode_any W_175068 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17506c : bv 32 := 0x00700813.
Lemma F_17506c : fetch_word AsanUbsan.M.loaded_segments (0x176a14 : word) = Some W_17506c.
Proof. vm_refl. Qed.
Lemma D_17506c : decode_any W_17506c = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_175070 : bv 32 := 0x00053883.
Lemma F_175070 : fetch_word AsanUbsan.M.loaded_segments (0x176a18 : word) = Some W_175070.
Proof. vm_refl. Qed.
Lemma D_175070 : decode_any W_175070 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175074 : bv 32 := 0x00f8c8b3.
Lemma F_175074 : fetch_word AsanUbsan.M.loaded_segments (0x176a1c : word) = Some W_175074.
Proof. vm_refl. Qed.
Lemma D_175074 : decode_any W_175074 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_175078 : bv 32 := 0x411682b3.
Lemma F_175078 : fetch_word AsanUbsan.M.loaded_segments (0x176a20 : word) = Some W_175078.
Proof. vm_refl. Qed.
Lemma D_175078 : decode_any W_175078 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_17507c : bv 32 := 0x0112e8b3.
Lemma F_17507c : fetch_word AsanUbsan.M.loaded_segments (0x176a24 : word) = Some W_17507c.
Proof. vm_refl. Qed.
Lemma D_17507c : decode_any W_17507c = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_175080 : bv 32 := 0x00e8f8b3.
Lemma F_175080 : fetch_word AsanUbsan.M.loaded_segments (0x176a28 : word) = Some W_175080.
Proof. vm_refl. Qed.
Lemma D_175080 : decode_any W_175080 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_175084 : bv 32 := 0x02e89a63.
Lemma F_175084 : fetch_word AsanUbsan.M.loaded_segments (0x176a2c : word) = Some W_175084.
Proof. vm_refl. Qed.
Lemma D_175084 : decode_any W_175084 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_175088 : bv 32 := 0xff860613.
Lemma F_175088 : fetch_word AsanUbsan.M.loaded_segments (0x176a30 : word) = Some W_175088.
Proof. vm_refl. Qed.
Lemma D_175088 : decode_any W_175088 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_17508c : bv 32 := 0x00850513.
Lemma F_17508c : fetch_word AsanUbsan.M.loaded_segments (0x176a34 : word) = Some W_17508c.
Proof. vm_refl. Qed.
Lemma D_17508c : decode_any W_17508c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_175090 : bv 32 := 0xfec860e3.
Lemma F_175090 : fetch_word AsanUbsan.M.loaded_segments (0x176a38 : word) = Some W_175090.
Proof. vm_refl. Qed.
Lemma D_175090 : decode_any W_175090 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_175094 : bv 32 := 0x00060693.
Lemma F_175094 : fetch_word AsanUbsan.M.loaded_segments (0x176a3c : word) = Some W_175094.
Proof. vm_refl. Qed.
Lemma D_175094 : decode_any W_175094 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175098 : bv 32 := 0x00060c63.
Lemma F_175098 : fetch_word AsanUbsan.M.loaded_segments (0x176a40 : word) = Some W_175098.
Proof. vm_refl. Qed.
Lemma D_175098 : decode_any W_175098 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17509c : bv 32 := 0x00054603.
Lemma F_17509c : fetch_word AsanUbsan.M.loaded_segments (0x176a44 : word) = Some W_17509c.
Proof. vm_refl. Qed.
Lemma D_17509c : decode_any W_17509c = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750a0 : bv 32 := 0x00b60a63.
Lemma F_1750a0 : fetch_word AsanUbsan.M.loaded_segments (0x176a48 : word) = Some W_1750a0.
Proof. vm_refl. Qed.
Lemma D_1750a0 : decode_any W_1750a0 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750a4 : bv 32 := 0xfff68693.
Lemma F_1750a4 : fetch_word AsanUbsan.M.loaded_segments (0x176a4c : word) = Some W_1750a4.
Proof. vm_refl. Qed.
Lemma D_1750a4 : decode_any W_1750a4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750a8 : bv 32 := 0x00150513.
Lemma F_1750a8 : fetch_word AsanUbsan.M.loaded_segments (0x176a50 : word) = Some W_1750a8.
Proof. vm_refl. Qed.
Lemma D_1750a8 : decode_any W_1750a8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750ac : bv 32 := 0xfe0698e3.
Lemma F_1750ac : fetch_word AsanUbsan.M.loaded_segments (0x176a54 : word) = Some W_1750ac.
Proof. vm_refl. Qed.
Lemma D_1750ac : decode_any W_1750ac = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750b4 : bv 32 := 0x00008067.
Lemma F_1750b4 : fetch_word AsanUbsan.M.loaded_segments (0x176a5c : word) = Some W_1750b4.
Proof. vm_refl. Qed.
Lemma D_1750b4 : decode_any W_1750b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750b8 : bv 32 := 0x00060693.
Lemma F_1750b8 : fetch_word AsanUbsan.M.loaded_segments (0x176a60 : word) = Some W_1750b8.
Proof. vm_refl. Qed.
Lemma D_1750b8 : decode_any W_1750b8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750bc : bv 32 := 0x00054603.
Lemma F_1750bc : fetch_word AsanUbsan.M.loaded_segments (0x176a64 : word) = Some W_1750bc.
Proof. vm_refl. Qed.
Lemma D_1750bc : decode_any W_1750bc = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750c0 : bv 32 := 0xfeb612e3.
Lemma F_1750c0 : fetch_word AsanUbsan.M.loaded_segments (0x176a68 : word) = Some W_1750c0.
Proof. vm_refl. Qed.
Lemma D_1750c0 : decode_any W_1750c0 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750c4 : bv 32 := 0xff1ff06f.
Lemma F_1750c4 : fetch_word AsanUbsan.M.loaded_segments (0x176a6c : word) = Some W_1750c4.
Proof. vm_refl. Qed.
Lemma D_1750c4 : decode_any W_1750c4 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.
