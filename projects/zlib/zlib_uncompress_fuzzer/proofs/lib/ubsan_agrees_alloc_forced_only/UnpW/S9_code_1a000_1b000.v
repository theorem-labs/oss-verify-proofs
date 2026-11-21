(* reloc-zl14c *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1a170 : bv 32 := 0x00062703.
Lemma F_1a170 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a288 : word) = Some W_1a170.
Proof. vm_refl. Qed.
Lemma D_1a170 : decode_any W_1a170 = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a174 : bv 32 := 0x00d777b3.
Lemma F_1a174 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a28c : word) = Some W_1a174.
Proof. vm_refl. Qed.
Lemma D_1a174 : decode_any W_1a174 = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a178 : bv 32 := 0x1606282f.
Lemma F_1a178 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a290 : word) = Some W_1a178.
Proof. vm_refl. Qed.
Lemma D_1a178 : decode_any W_1a178 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a17c : bv 32 := 0x00e81663.
Lemma F_1a17c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a294 : word) = Some W_1a17c.
Proof. vm_refl. Qed.
Lemma D_1a17c : decode_any W_1a17c = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a180 : bv 32 := 0x1ef628af.
Lemma F_1a180 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a298 : word) = Some W_1a180.
Proof. vm_refl. Qed.
Lemma D_1a180 : decode_any W_1a180 = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a184 : bv 32 := 0xfe089ae3.
Lemma F_1a184 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a29c : word) = Some W_1a184.
Proof. vm_refl. Qed.
Lemma D_1a184 : decode_any W_1a184 = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a188 : bv 32 := 0x0008081b.
Lemma F_1a188 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a2a0 : word) = Some W_1a188.
Proof. vm_refl. Qed.
Lemma D_1a188 : decode_any W_1a188 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a18c : bv 32 := 0xfee812e3.
Lemma F_1a18c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a2a4 : word) = Some W_1a18c.
Proof. vm_refl. Qed.
Lemma D_1a18c : decode_any W_1a18c = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8d4 : bv 32 := 0x02053703.
Lemma F_1a8d4 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a9ec : word) = Some W_1a8d4.
Proof. vm_refl. Qed.
Lemma D_1a8d4 : decode_any W_1a8d4 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8d8 : bv 32 := 0x00c75793.
Lemma F_1a8d8 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a9f0 : word) = Some W_1a8d8.
Proof. vm_refl. Qed.
Lemma D_1a8d8 : decode_any W_1a8d8 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8dc : bv 32 := 0x00078e63.
Lemma F_1a8dc : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a9f4 : word) = Some W_1a8dc.
Proof. vm_refl. Qed.
Lemma D_1a8dc : decode_any W_1a8dc = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8e0 : bv 32 := 0x01f77793.
Lemma F_1a8e0 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a9f8 : word) = Some W_1a8e0.
Proof. vm_refl. Qed.
Lemma D_1a8e0 : decode_any W_1a8e0 = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8e4 : bv 32 := 0x00079a63.
Lemma F_1a8e4 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1a9fc : word) = Some W_1a8e4.
Proof. vm_refl. Qed.
Lemma D_1a8e4 : decode_any W_1a8e4 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8e8 : bv 32 := 0xfffff7b7.
Lemma F_1a8e8 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa00 : word) = Some W_1a8e8.
Proof. vm_refl. Qed.
Lemma D_1a8e8 : decode_any W_1a8e8 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8ec : bv 32 := 0x00f77733.
Lemma F_1a8ec : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa04 : word) = Some W_1a8ec.
Proof. vm_refl. Qed.
Lemma D_1a8ec : decode_any W_1a8ec = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8f0 : bv 32 := 0xff070713.
Lemma F_1a8f0 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa08 : word) = Some W_1a8f0.
Proof. vm_refl. Qed.
Lemma D_1a8f0 : decode_any W_1a8f0 = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8f4 : bv 32 := 0x0200006f.
Lemma F_1a8f4 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa0c : word) = Some W_1a8f4.
Proof. vm_refl. Qed.
Lemma D_1a8f4 : decode_any W_1a8f4 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8f8 : bv 32 := 0x00575713.
Lemma F_1a8f8 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa10 : word) = Some W_1a8f8.
Proof. vm_refl. Qed.
Lemma D_1a8f8 : decode_any W_1a8f8 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8fc : bv 32 := 0xffff8797.
Lemma F_1a8fc : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa14 : word) = Some W_1a8fc.
Proof. vm_refl. Qed.
Lemma D_1a8fc : decode_any W_1a8fc = Some (Auipc 15 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a900 : bv 32 := 0x07e77713.
Lemma F_1a900 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa18 : word) = Some W_1a900.
Proof. vm_refl. Qed.
Lemma D_1a900 : decode_any W_1a900 = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a904 : bv 32 := 0xa4878793.
Lemma F_1a904 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa1c : word) = Some W_1a904.
Proof. vm_refl. Qed.
Lemma D_1a904 : decode_any W_1a904 = Some (OpImm ALU_ADD 15 15 2632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a908 : bv 32 := 0x00e78733.
Lemma F_1a908 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa20 : word) = Some W_1a908.
Proof. vm_refl. Qed.
Lemma D_1a908 : decode_any W_1a908 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a90c : bv 32 := 0x00075703.
Lemma F_1a90c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa24 : word) = Some W_1a90c.
Proof. vm_refl. Qed.
Lemma D_1a90c : decode_any W_1a90c = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a910 : bv 32 := 0x00471713.
Lemma F_1a910 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa28 : word) = Some W_1a910.
Proof. vm_refl. Qed.
Lemma D_1a910 : decode_any W_1a910 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a914 : bv 32 := 0x01053803.
Lemma F_1a914 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa2c : word) = Some W_1a914.
Proof. vm_refl. Qed.
Lemma D_1a914 : decode_any W_1a914 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a918 : bv 32 := 0x02b707b3.
Lemma F_1a918 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa30 : word) = Some W_1a918.
Proof. vm_refl. Qed.
Lemma D_1a918 : decode_any W_1a918 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a91c : bv 32 := 0x00f807b3.
Lemma F_1a91c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa34 : word) = Some W_1a91c.
Proof. vm_refl. Qed.
Lemma D_1a91c : decode_any W_1a91c = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a920 : bv 32 := 0x00d7c883.
Lemma F_1a920 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa38 : word) = Some W_1a920.
Proof. vm_refl. Qed.
Lemma D_1a920 : decode_any W_1a920 = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a924 : bv 32 := 0x40c702b3.
Lemma F_1a924 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa3c : word) = Some W_1a924.
Proof. vm_refl. Qed.
Lemma D_1a924 : decode_any W_1a924 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a928 : bv 32 := 0xffc28293.
Lemma F_1a928 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa40 : word) = Some W_1a928.
Proof. vm_refl. Qed.
Lemma D_1a928 : decode_any W_1a928 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a92c : bv 32 := 0x01078793.
Lemma F_1a92c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa44 : word) = Some W_1a92c.
Proof. vm_refl. Qed.
Lemma D_1a92c : decode_any W_1a92c = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a930 : bv 32 := 0x00088663.
Lemma F_1a930 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa48 : word) = Some W_1a930.
Proof. vm_refl. Qed.
Lemma D_1a930 : decode_any W_1a930 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a934 : bv 32 := 0xffe7d683.
Lemma F_1a934 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa4c : word) = Some W_1a934.
Proof. vm_refl. Qed.
Lemma D_1a934 : decode_any W_1a934 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a938 : bv 32 := 0x00168693.
Lemma F_1a938 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa50 : word) = Some W_1a938.
Proof. vm_refl. Qed.
Lemma D_1a938 : decode_any W_1a938 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a93c : bv 32 := 0xffc7c383.
Lemma F_1a93c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa54 : word) = Some W_1a93c.
Proof. vm_refl. Qed.
Lemma D_1a93c : decode_any W_1a93c = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a940 : bv 32 := 0x0042d313.
Lemma F_1a940 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa58 : word) = Some W_1a940.
Proof. vm_refl. Qed.
Lemma D_1a940 : decode_any W_1a940 = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a944 : bv 32 := 0x0ff6f893.
Lemma F_1a944 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa5c : word) = Some W_1a944.
Proof. vm_refl. Qed.
Lemma D_1a944 : decode_any W_1a944 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a948 : bv 32 := 0x00038463.
Lemma F_1a948 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa60 : word) = Some W_1a948.
Proof. vm_refl. Qed.
Lemma D_1a948 : decode_any W_1a948 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a950 : bv 32 := 0x03137e63.
Lemma F_1a950 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa68 : word) = Some W_1a950.
Proof. vm_refl. Qed.
Lemma D_1a950 : decode_any W_1a950 = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a954 : bv 32 := 0x0052d693.
Lemma F_1a954 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa6c : word) = Some W_1a954.
Proof. vm_refl. Qed.
Lemma D_1a954 : decode_any W_1a954 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a958 : bv 32 := 0x00d366b3.
Lemma F_1a958 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa70 : word) = Some W_1a958.
Proof. vm_refl. Qed.
Lemma D_1a958 : decode_any W_1a958 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a95c : bv 32 := 0x0026d293.
Lemma F_1a95c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa74 : word) = Some W_1a95c.
Proof. vm_refl. Qed.
Lemma D_1a95c : decode_any W_1a95c = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a960 : bv 32 := 0x00d2e6b3.
Lemma F_1a960 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa78 : word) = Some W_1a960.
Proof. vm_refl. Qed.
Lemma D_1a960 : decode_any W_1a960 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a964 : bv 32 := 0x0046d293.
Lemma F_1a964 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa7c : word) = Some W_1a964.
Proof. vm_refl. Qed.
Lemma D_1a964 : decode_any W_1a964 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a968 : bv 32 := 0x00d2e6b3.
Lemma F_1a968 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa80 : word) = Some W_1a968.
Proof. vm_refl. Qed.
Lemma D_1a968 : decode_any W_1a968 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a96c : bv 32 := 0x00d8f6b3.
Lemma F_1a96c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa84 : word) = Some W_1a96c.
Proof. vm_refl. Qed.
Lemma D_1a96c : decode_any W_1a96c = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a970 : bv 32 := 0x00d338b3.
Lemma F_1a970 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa88 : word) = Some W_1a970.
Proof. vm_refl. Qed.
Lemma D_1a970 : decode_any W_1a970 = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a974 : bv 32 := 0xfff34293.
Lemma F_1a974 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa8c : word) = Some W_1a974.
Proof. vm_refl. Qed.
Lemma D_1a974 : decode_any W_1a974 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a978 : bv 32 := 0x411008bb.
Lemma F_1a978 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa90 : word) = Some W_1a978.
Proof. vm_refl. Qed.
Lemma D_1a978 : decode_any W_1a978 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a97c : bv 32 := 0x0058f8b3.
Lemma F_1a97c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa94 : word) = Some W_1a97c.
Proof. vm_refl. Qed.
Lemma D_1a97c : decode_any W_1a97c = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a980 : bv 32 := 0x00d888bb.
Lemma F_1a980 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa98 : word) = Some W_1a980.
Proof. vm_refl. Qed.
Lemma D_1a980 : decode_any W_1a980 = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a984 : bv 32 := 0x01137463.
Lemma F_1a984 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aa9c : word) = Some W_1a984.
Proof. vm_refl. Qed.
Lemma D_1a984 : decode_any W_1a984 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a98c : bv 32 := 0x00078693.
Lemma F_1a98c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aaa4 : word) = Some W_1a98c.
Proof. vm_refl. Qed.
Lemma D_1a98c : decode_any W_1a98c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a990 : bv 32 := 0x02088063.
Lemma F_1a990 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aaa8 : word) = Some W_1a990.
Proof. vm_refl. Qed.
Lemma D_1a990 : decode_any W_1a990 = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a994 : bv 32 := 0xfe000813.
Lemma F_1a994 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aaac : word) = Some W_1a994.
Proof. vm_refl. Qed.
Lemma D_1a994 : decode_any W_1a994 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a998 : bv 32 := 0x0048969b.
Lemma F_1a998 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aab0 : word) = Some W_1a998.
Proof. vm_refl. Qed.
Lemma D_1a998 : decode_any W_1a998 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a99c : bv 32 := 0x00d786b3.
Lemma F_1a99c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aab4 : word) = Some W_1a99c.
Proof. vm_refl. Qed.
Lemma D_1a99c : decode_any W_1a99c = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9a0 : bv 32 := 0xff078ea3.
Lemma F_1a9a0 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aab8 : word) = Some W_1a9a0.
Proof. vm_refl. Qed.
Lemma D_1a9a0 : decode_any W_1a9a0 = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9a4 : bv 32 := 0xff179f23.
Lemma F_1a9a4 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aabc : word) = Some W_1a9a4.
Proof. vm_refl. Qed.
Lemma D_1a9a4 : decode_any W_1a9a4 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9a8 : bv 32 := 0xfe068e23.
Lemma F_1a9a8 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aac0 : word) = Some W_1a9a8.
Proof. vm_refl. Qed.
Lemma D_1a9a8 : decode_any W_1a9a8 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9ac : bv 32 := 0x01053803.
Lemma F_1a9ac : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aac4 : word) = Some W_1a9ac.
Proof. vm_refl. Qed.
Lemma D_1a9ac : decode_any W_1a9ac = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9b0 : bv 32 := 0x00e78733.
Lemma F_1a9b0 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aac8 : word) = Some W_1a9b0.
Proof. vm_refl. Qed.
Lemma D_1a9b0 : decode_any W_1a9b0 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9b4 : bv 32 := 0x410687bb.
Lemma F_1a9b4 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aacc : word) = Some W_1a9b4.
Proof. vm_refl. Qed.
Lemma D_1a9b4 : decode_any W_1a9b4 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9b8 : bv 32 := 0x00d60633.
Lemma F_1a9b8 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aad0 : word) = Some W_1a9b8.
Proof. vm_refl. Qed.
Lemma D_1a9b8 : decode_any W_1a9b8 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9bc : bv 32 := 0xffc70513.
Lemma F_1a9bc : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aad4 : word) = Some W_1a9bc.
Proof. vm_refl. Qed.
Lemma D_1a9bc : decode_any W_1a9bc = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9c0 : bv 32 := 0xff078793.
Lemma F_1a9c0 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aad8 : word) = Some W_1a9c0.
Proof. vm_refl. Qed.
Lemma D_1a9c0 : decode_any W_1a9c0 = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9c4 : bv 32 := 0x0047d793.
Lemma F_1a9c4 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aadc : word) = Some W_1a9c4.
Proof. vm_refl. Qed.
Lemma D_1a9c4 : decode_any W_1a9c4 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9c8 : bv 32 := 0x40c5083b.
Lemma F_1a9c8 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aae0 : word) = Some W_1a9c8.
Proof. vm_refl. Qed.
Lemma D_1a9c8 : decode_any W_1a9c8 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9cc : bv 32 := 0xfeb68ea3.
Lemma F_1a9cc : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aae4 : word) = Some W_1a9cc.
Proof. vm_refl. Qed.
Lemma D_1a9cc : decode_any W_1a9cc = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9d0 : bv 32 := 0xfef69f23.
Lemma F_1a9d0 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aae8 : word) = Some W_1a9d0.
Proof. vm_refl. Qed.
Lemma D_1a9d0 : decode_any W_1a9d0 = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9d4 : bv 32 := 0x02080463.
Lemma F_1a9d4 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aaec : word) = Some W_1a9d4.
Proof. vm_refl. Qed.
Lemma D_1a9d4 : decode_any W_1a9d4 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9d8 : bv 32 := 0x40c505bb.
Lemma F_1a9d8 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aaf0 : word) = Some W_1a9d8.
Proof. vm_refl. Qed.
Lemma D_1a9d8 : decode_any W_1a9d8 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9dc : bv 32 := 0x40b0063b.
Lemma F_1a9dc : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aaf4 : word) = Some W_1a9dc.
Proof. vm_refl. Qed.
Lemma D_1a9dc : decode_any W_1a9dc = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9e0 : bv 32 := 0x00c50633.
Lemma F_1a9e0 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aaf8 : word) = Some W_1a9e0.
Proof. vm_refl. Qed.
Lemma D_1a9e0 : decode_any W_1a9e0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9e4 : bv 32 := 0x00500513.
Lemma F_1a9e4 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1aafc : word) = Some W_1a9e4.
Proof. vm_refl. Qed.
Lemma D_1a9e4 : decode_any W_1a9e4 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9e8 : bv 32 := 0x00060023.
Lemma F_1a9e8 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab00 : word) = Some W_1a9e8.
Proof. vm_refl. Qed.
Lemma D_1a9e8 : decode_any W_1a9e8 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9ec : bv 32 := 0x00a5cc63.
Lemma F_1a9ec : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab04 : word) = Some W_1a9ec.
Proof. vm_refl. Qed.
Lemma D_1a9ec : decode_any W_1a9ec = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9f0 : bv 32 := 0xfe070ba3.
Lemma F_1a9f0 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab08 : word) = Some W_1a9f0.
Proof. vm_refl. Qed.
Lemma D_1a9f0 : decode_any W_1a9f0 = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9f4 : bv 32 := 0xfeb72c23.
Lemma F_1a9f4 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab0c : word) = Some W_1a9f4.
Proof. vm_refl. Qed.
Lemma D_1a9f4 : decode_any W_1a9f4 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9f8 : bv 32 := 0x0100006f.
Lemma F_1a9f8 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab10 : word) = Some W_1a9f8.
Proof. vm_refl. Qed.
Lemma D_1a9f8 : decode_any W_1a9f8 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a9fc : bv 32 := 0x00000513.
Lemma F_1a9fc : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab14 : word) = Some W_1a9fc.
Proof. vm_refl. Qed.
Lemma D_1a9fc : decode_any W_1a9fc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1aa00 : bv 32 := 0x0080006f.
Lemma F_1aa00 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab18 : word) = Some W_1aa00.
Proof. vm_refl. Qed.
Lemma D_1aa00 : decode_any W_1aa00 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1aa04 : bv 32 := 0x00058513.
Lemma F_1aa04 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab1c : word) = Some W_1aa04.
Proof. vm_refl. Qed.
Lemma D_1aa04 : decode_any W_1aa04 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1aa08 : bv 32 := 0xffd6c583.
Lemma F_1aa08 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab20 : word) = Some W_1aa08.
Proof. vm_refl. Qed.
Lemma D_1aa08 : decode_any W_1aa08 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1aa0c : bv 32 := 0x01f5f593.
Lemma F_1aa0c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab24 : word) = Some W_1aa0c.
Proof. vm_refl. Qed.
Lemma D_1aa0c : decode_any W_1aa0c = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1aa10 : bv 32 := 0x00551513.
Lemma F_1aa10 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab28 : word) = Some W_1aa10.
Proof. vm_refl. Qed.
Lemma D_1aa10 : decode_any W_1aa10 = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1aa14 : bv 32 := 0x00b56533.
Lemma F_1aa14 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab2c : word) = Some W_1aa14.
Proof. vm_refl. Qed.
Lemma D_1aa14 : decode_any W_1aa14 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1aa18 : bv 32 := 0xfea68ea3.
Lemma F_1aa18 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab30 : word) = Some W_1aa18.
Proof. vm_refl. Qed.
Lemma D_1aa18 : decode_any W_1aa18 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1aa1c : bv 32 := 0x00068513.
Lemma F_1aa1c : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab34 : word) = Some W_1aa1c.
Proof. vm_refl. Qed.
Lemma D_1aa1c : decode_any W_1aa1c = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1aa20 : bv 32 := 0x00008067.
Lemma F_1aa20 : fetch_word SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments (0x1ab38 : word) = Some W_1aa20.
Proof. vm_refl. Qed.
Lemma D_1aa20 : decode_any W_1aa20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
