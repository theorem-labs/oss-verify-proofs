(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1a12c : bv 32 := 0x00062703.
Lemma F_1a12c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a25c : word) = Some W_1a12c.
Proof. vm_refl. Qed.
Lemma D_1a12c : decode_any W_1a12c = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a130 : bv 32 := 0x00d777b3.
Lemma F_1a130 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a260 : word) = Some W_1a130.
Proof. vm_refl. Qed.
Lemma D_1a130 : decode_any W_1a130 = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a134 : bv 32 := 0x1606282f.
Lemma F_1a134 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a264 : word) = Some W_1a134.
Proof. vm_refl. Qed.
Lemma D_1a134 : decode_any W_1a134 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a138 : bv 32 := 0x00e81663.
Lemma F_1a138 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a268 : word) = Some W_1a138.
Proof. vm_refl. Qed.
Lemma D_1a138 : decode_any W_1a138 = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a13c : bv 32 := 0x1ef628af.
Lemma F_1a13c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a26c : word) = Some W_1a13c.
Proof. vm_refl. Qed.
Lemma D_1a13c : decode_any W_1a13c = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a140 : bv 32 := 0xfe089ae3.
Lemma F_1a140 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a270 : word) = Some W_1a140.
Proof. vm_refl. Qed.
Lemma D_1a140 : decode_any W_1a140 = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a144 : bv 32 := 0x0008081b.
Lemma F_1a144 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a274 : word) = Some W_1a144.
Proof. vm_refl. Qed.
Lemma D_1a144 : decode_any W_1a144 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a148 : bv 32 := 0xfee812e3.
Lemma F_1a148 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a278 : word) = Some W_1a148.
Proof. vm_refl. Qed.
Lemma D_1a148 : decode_any W_1a148 = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a890 : bv 32 := 0x02053703.
Lemma F_1a890 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9c0 : word) = Some W_1a890.
Proof. vm_refl. Qed.
Lemma D_1a890 : decode_any W_1a890 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a894 : bv 32 := 0x00c75793.
Lemma F_1a894 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9c4 : word) = Some W_1a894.
Proof. vm_refl. Qed.
Lemma D_1a894 : decode_any W_1a894 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a898 : bv 32 := 0x00078e63.
Lemma F_1a898 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9c8 : word) = Some W_1a898.
Proof. vm_refl. Qed.
Lemma D_1a898 : decode_any W_1a898 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a89c : bv 32 := 0x01f77793.
Lemma F_1a89c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9cc : word) = Some W_1a89c.
Proof. vm_refl. Qed.
Lemma D_1a89c : decode_any W_1a89c = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8a0 : bv 32 := 0x00079a63.
Lemma F_1a8a0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9d0 : word) = Some W_1a8a0.
Proof. vm_refl. Qed.
Lemma D_1a8a0 : decode_any W_1a8a0 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8a4 : bv 32 := 0xfffff7b7.
Lemma F_1a8a4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9d4 : word) = Some W_1a8a4.
Proof. vm_refl. Qed.
Lemma D_1a8a4 : decode_any W_1a8a4 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8a8 : bv 32 := 0x00f77733.
Lemma F_1a8a8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9d8 : word) = Some W_1a8a8.
Proof. vm_refl. Qed.
Lemma D_1a8a8 : decode_any W_1a8a8 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8ac : bv 32 := 0xff070713.
Lemma F_1a8ac : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9dc : word) = Some W_1a8ac.
Proof. vm_refl. Qed.
Lemma D_1a8ac : decode_any W_1a8ac = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8b0 : bv 32 := 0x0200006f.
Lemma F_1a8b0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9e0 : word) = Some W_1a8b0.
Proof. vm_refl. Qed.
Lemma D_1a8b0 : decode_any W_1a8b0 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8b4 : bv 32 := 0x00575713.
Lemma F_1a8b4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9e4 : word) = Some W_1a8b4.
Proof. vm_refl. Qed.
Lemma D_1a8b4 : decode_any W_1a8b4 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8b8 : bv 32 := 0xffff8797.
Lemma F_1a8b8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9e8 : word) = Some W_1a8b8.
Proof. vm_refl. Qed.
Lemma D_1a8b8 : decode_any W_1a8b8 = Some (Auipc 15 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8bc : bv 32 := 0x07e77713.
Lemma F_1a8bc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9ec : word) = Some W_1a8bc.
Proof. vm_refl. Qed.
Lemma D_1a8bc : decode_any W_1a8bc = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8c0 : bv 32 := 0xa7478793.
Lemma F_1a8c0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9f0 : word) = Some W_1a8c0.
Proof. vm_refl. Qed.
Lemma D_1a8c0 : decode_any W_1a8c0 = Some (OpImm ALU_ADD 15 15 2676, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8c4 : bv 32 := 0x00e78733.
Lemma F_1a8c4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9f4 : word) = Some W_1a8c4.
Proof. vm_refl. Qed.
Lemma D_1a8c4 : decode_any W_1a8c4 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8c8 : bv 32 := 0x00075703.
Lemma F_1a8c8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9f8 : word) = Some W_1a8c8.
Proof. vm_refl. Qed.
Lemma D_1a8c8 : decode_any W_1a8c8 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8cc : bv 32 := 0x00471713.
Lemma F_1a8cc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1a9fc : word) = Some W_1a8cc.
Proof. vm_refl. Qed.
Lemma D_1a8cc : decode_any W_1a8cc = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8d0 : bv 32 := 0x01053803.
Lemma F_1a8d0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa00 : word) = Some W_1a8d0.
Proof. vm_refl. Qed.
Lemma D_1a8d0 : decode_any W_1a8d0 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8d4 : bv 32 := 0x02b707b3.
Lemma F_1a8d4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa04 : word) = Some W_1a8d4.
Proof. vm_refl. Qed.
Lemma D_1a8d4 : decode_any W_1a8d4 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8d8 : bv 32 := 0x00f807b3.
Lemma F_1a8d8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa08 : word) = Some W_1a8d8.
Proof. vm_refl. Qed.
Lemma D_1a8d8 : decode_any W_1a8d8 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8dc : bv 32 := 0x00d7c883.
Lemma F_1a8dc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa0c : word) = Some W_1a8dc.
Proof. vm_refl. Qed.
Lemma D_1a8dc : decode_any W_1a8dc = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8e0 : bv 32 := 0x40c702b3.
Lemma F_1a8e0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa10 : word) = Some W_1a8e0.
Proof. vm_refl. Qed.
Lemma D_1a8e0 : decode_any W_1a8e0 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8e4 : bv 32 := 0xffc28293.
Lemma F_1a8e4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa14 : word) = Some W_1a8e4.
Proof. vm_refl. Qed.
Lemma D_1a8e4 : decode_any W_1a8e4 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8e8 : bv 32 := 0x01078793.
Lemma F_1a8e8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa18 : word) = Some W_1a8e8.
Proof. vm_refl. Qed.
Lemma D_1a8e8 : decode_any W_1a8e8 = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8ec : bv 32 := 0x00088663.
Lemma F_1a8ec : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa1c : word) = Some W_1a8ec.
Proof. vm_refl. Qed.
Lemma D_1a8ec : decode_any W_1a8ec = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8f0 : bv 32 := 0xffe7d683.
Lemma F_1a8f0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa20 : word) = Some W_1a8f0.
Proof. vm_refl. Qed.
Lemma D_1a8f0 : decode_any W_1a8f0 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8f4 : bv 32 := 0x00168693.
Lemma F_1a8f4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa24 : word) = Some W_1a8f4.
Proof. vm_refl. Qed.
Lemma D_1a8f4 : decode_any W_1a8f4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8f8 : bv 32 := 0xffc7c383.
Lemma F_1a8f8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa28 : word) = Some W_1a8f8.
Proof. vm_refl. Qed.
Lemma D_1a8f8 : decode_any W_1a8f8 = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8fc : bv 32 := 0x0042d313.
Lemma F_1a8fc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa2c : word) = Some W_1a8fc.
Proof. vm_refl. Qed.
Lemma D_1a8fc : decode_any W_1a8fc = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a900 : bv 32 := 0x0ff6f893.
Lemma F_1a900 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa30 : word) = Some W_1a900.
Proof. vm_refl. Qed.
Lemma D_1a900 : decode_any W_1a900 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a904 : bv 32 := 0x00038463.
Lemma F_1a904 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa34 : word) = Some W_1a904.
Proof. vm_refl. Qed.
Lemma D_1a904 : decode_any W_1a904 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a90c : bv 32 := 0x03137e63.
Lemma F_1a90c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa3c : word) = Some W_1a90c.
Proof. vm_refl. Qed.
Lemma D_1a90c : decode_any W_1a90c = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a910 : bv 32 := 0x0052d693.
Lemma F_1a910 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa40 : word) = Some W_1a910.
Proof. vm_refl. Qed.
Lemma D_1a910 : decode_any W_1a910 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a914 : bv 32 := 0x00d366b3.
Lemma F_1a914 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa44 : word) = Some W_1a914.
Proof. vm_refl. Qed.
Lemma D_1a914 : decode_any W_1a914 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a918 : bv 32 := 0x0026d293.
Lemma F_1a918 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa48 : word) = Some W_1a918.
Proof. vm_refl. Qed.
Lemma D_1a918 : decode_any W_1a918 = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a91c : bv 32 := 0x00d2e6b3.
Lemma F_1a91c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa4c : word) = Some W_1a91c.
Proof. vm_refl. Qed.
Lemma D_1a91c : decode_any W_1a91c = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a920 : bv 32 := 0x0046d293.
Lemma F_1a920 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa50 : word) = Some W_1a920.
Proof. vm_refl. Qed.
Lemma D_1a920 : decode_any W_1a920 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a924 : bv 32 := 0x00d2e6b3.
Lemma F_1a924 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa54 : word) = Some W_1a924.
Proof. vm_refl. Qed.
Lemma D_1a924 : decode_any W_1a924 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a928 : bv 32 := 0x00d8f6b3.
Lemma F_1a928 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa58 : word) = Some W_1a928.
Proof. vm_refl. Qed.
Lemma D_1a928 : decode_any W_1a928 = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a92c : bv 32 := 0x00d338b3.
Lemma F_1a92c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa5c : word) = Some W_1a92c.
Proof. vm_refl. Qed.
Lemma D_1a92c : decode_any W_1a92c = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a930 : bv 32 := 0xfff34293.
Lemma F_1a930 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa60 : word) = Some W_1a930.
Proof. vm_refl. Qed.
Lemma D_1a930 : decode_any W_1a930 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a934 : bv 32 := 0x411008bb.
Lemma F_1a934 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa64 : word) = Some W_1a934.
Proof. vm_refl. Qed.
Lemma D_1a934 : decode_any W_1a934 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a938 : bv 32 := 0x0058f8b3.
Lemma F_1a938 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa68 : word) = Some W_1a938.
Proof. vm_refl. Qed.
Lemma D_1a938 : decode_any W_1a938 = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a93c : bv 32 := 0x00d888bb.
Lemma F_1a93c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa6c : word) = Some W_1a93c.
Proof. vm_refl. Qed.
Lemma D_1a93c : decode_any W_1a93c = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a940 : bv 32 := 0x01137463.
Lemma F_1a940 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa70 : word) = Some W_1a940.
Proof. vm_refl. Qed.
Lemma D_1a940 : decode_any W_1a940 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a948 : bv 32 := 0x00078693.
Lemma F_1a948 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa78 : word) = Some W_1a948.
Proof. vm_refl. Qed.
Lemma D_1a948 : decode_any W_1a948 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a94c : bv 32 := 0x02088063.
Lemma F_1a94c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa7c : word) = Some W_1a94c.
Proof. vm_refl. Qed.
Lemma D_1a94c : decode_any W_1a94c = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a950 : bv 32 := 0xfe000813.
Lemma F_1a950 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa80 : word) = Some W_1a950.
Proof. vm_refl. Qed.
Lemma D_1a950 : decode_any W_1a950 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a954 : bv 32 := 0x0048969b.
Lemma F_1a954 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa84 : word) = Some W_1a954.
Proof. vm_refl. Qed.
Lemma D_1a954 : decode_any W_1a954 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a958 : bv 32 := 0x00d786b3.
Lemma F_1a958 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa88 : word) = Some W_1a958.
Proof. vm_refl. Qed.
Lemma D_1a958 : decode_any W_1a958 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a95c : bv 32 := 0xff078ea3.
Lemma F_1a95c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa8c : word) = Some W_1a95c.
Proof. vm_refl. Qed.
Lemma D_1a95c : decode_any W_1a95c = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a960 : bv 32 := 0xff179f23.
Lemma F_1a960 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa90 : word) = Some W_1a960.
Proof. vm_refl. Qed.
Lemma D_1a960 : decode_any W_1a960 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a964 : bv 32 := 0xfe068e23.
Lemma F_1a964 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa94 : word) = Some W_1a964.
Proof. vm_refl. Qed.
Lemma D_1a964 : decode_any W_1a964 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a968 : bv 32 := 0x01053803.
Lemma F_1a968 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa98 : word) = Some W_1a968.
Proof. vm_refl. Qed.
Lemma D_1a968 : decode_any W_1a968 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a96c : bv 32 := 0x00e78733.
Lemma F_1a96c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aa9c : word) = Some W_1a96c.
Proof. vm_refl. Qed.
Lemma D_1a96c : decode_any W_1a96c = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a970 : bv 32 := 0x410687bb.
Lemma F_1a970 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aaa0 : word) = Some W_1a970.
Proof. vm_refl. Qed.
Lemma D_1a970 : decode_any W_1a970 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a974 : bv 32 := 0x00d60633.
Lemma F_1a974 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aaa4 : word) = Some W_1a974.
Proof. vm_refl. Qed.
Lemma D_1a974 : decode_any W_1a974 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a978 : bv 32 := 0xffc70513.
Lemma F_1a978 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aaa8 : word) = Some W_1a978.
Proof. vm_refl. Qed.
Lemma D_1a978 : decode_any W_1a978 = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a97c : bv 32 := 0xff078793.
Lemma F_1a97c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aaac : word) = Some W_1a97c.
Proof. vm_refl. Qed.
Lemma D_1a97c : decode_any W_1a97c = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a980 : bv 32 := 0x0047d793.
Lemma F_1a980 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aab0 : word) = Some W_1a980.
Proof. vm_refl. Qed.
Lemma D_1a980 : decode_any W_1a980 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a984 : bv 32 := 0x40c5083b.
Lemma F_1a984 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aab4 : word) = Some W_1a984.
Proof. vm_refl. Qed.
Lemma D_1a984 : decode_any W_1a984 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a988 : bv 32 := 0xfeb68ea3.
Lemma F_1a988 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aab8 : word) = Some W_1a988.
Proof. vm_refl. Qed.
Lemma D_1a988 : decode_any W_1a988 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a98c : bv 32 := 0xfef69f23.
Lemma F_1a98c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aabc : word) = Some W_1a98c.
Proof. vm_refl. Qed.
Lemma D_1a98c : decode_any W_1a98c = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a990 : bv 32 := 0x02080463.
Lemma F_1a990 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aac0 : word) = Some W_1a990.
Proof. vm_refl. Qed.
Lemma D_1a990 : decode_any W_1a990 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a994 : bv 32 := 0x40c505bb.
Lemma F_1a994 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aac4 : word) = Some W_1a994.
Proof. vm_refl. Qed.
Lemma D_1a994 : decode_any W_1a994 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a998 : bv 32 := 0x40b0063b.
Lemma F_1a998 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aac8 : word) = Some W_1a998.
Proof. vm_refl. Qed.
Lemma D_1a998 : decode_any W_1a998 = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a99c : bv 32 := 0x00c50633.
Lemma F_1a99c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aacc : word) = Some W_1a99c.
Proof. vm_refl. Qed.
Lemma D_1a99c : decode_any W_1a99c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9a0 : bv 32 := 0x00500513.
Lemma F_1a9a0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aad0 : word) = Some W_1a9a0.
Proof. vm_refl. Qed.
Lemma D_1a9a0 : decode_any W_1a9a0 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9a4 : bv 32 := 0x00060023.
Lemma F_1a9a4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aad4 : word) = Some W_1a9a4.
Proof. vm_refl. Qed.
Lemma D_1a9a4 : decode_any W_1a9a4 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9a8 : bv 32 := 0x00a5cc63.
Lemma F_1a9a8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aad8 : word) = Some W_1a9a8.
Proof. vm_refl. Qed.
Lemma D_1a9a8 : decode_any W_1a9a8 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9ac : bv 32 := 0xfe070ba3.
Lemma F_1a9ac : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aadc : word) = Some W_1a9ac.
Proof. vm_refl. Qed.
Lemma D_1a9ac : decode_any W_1a9ac = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9b0 : bv 32 := 0xfeb72c23.
Lemma F_1a9b0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aae0 : word) = Some W_1a9b0.
Proof. vm_refl. Qed.
Lemma D_1a9b0 : decode_any W_1a9b0 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9b4 : bv 32 := 0x0100006f.
Lemma F_1a9b4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aae4 : word) = Some W_1a9b4.
Proof. vm_refl. Qed.
Lemma D_1a9b4 : decode_any W_1a9b4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9b8 : bv 32 := 0x00000513.
Lemma F_1a9b8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aae8 : word) = Some W_1a9b8.
Proof. vm_refl. Qed.
Lemma D_1a9b8 : decode_any W_1a9b8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9bc : bv 32 := 0x0080006f.
Lemma F_1a9bc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aaec : word) = Some W_1a9bc.
Proof. vm_refl. Qed.
Lemma D_1a9bc : decode_any W_1a9bc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9c0 : bv 32 := 0x00058513.
Lemma F_1a9c0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aaf0 : word) = Some W_1a9c0.
Proof. vm_refl. Qed.
Lemma D_1a9c0 : decode_any W_1a9c0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9c4 : bv 32 := 0xffd6c583.
Lemma F_1a9c4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aaf4 : word) = Some W_1a9c4.
Proof. vm_refl. Qed.
Lemma D_1a9c4 : decode_any W_1a9c4 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9c8 : bv 32 := 0x01f5f593.
Lemma F_1a9c8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aaf8 : word) = Some W_1a9c8.
Proof. vm_refl. Qed.
Lemma D_1a9c8 : decode_any W_1a9c8 = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9cc : bv 32 := 0x00551513.
Lemma F_1a9cc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1aafc : word) = Some W_1a9cc.
Proof. vm_refl. Qed.
Lemma D_1a9cc : decode_any W_1a9cc = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9d0 : bv 32 := 0x00b56533.
Lemma F_1a9d0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1ab00 : word) = Some W_1a9d0.
Proof. vm_refl. Qed.
Lemma D_1a9d0 : decode_any W_1a9d0 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9d4 : bv 32 := 0xfea68ea3.
Lemma F_1a9d4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1ab04 : word) = Some W_1a9d4.
Proof. vm_refl. Qed.
Lemma D_1a9d4 : decode_any W_1a9d4 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9d8 : bv 32 := 0x00068513.
Lemma F_1a9d8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1ab08 : word) = Some W_1a9d8.
Proof. vm_refl. Qed.
Lemma D_1a9d8 : decode_any W_1a9d8 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9dc : bv 32 := 0x00008067.
Lemma F_1a9dc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1ab0c : word) = Some W_1a9dc.
Proof. vm_refl. Qed.
Lemma D_1a9dc : decode_any W_1a9dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
