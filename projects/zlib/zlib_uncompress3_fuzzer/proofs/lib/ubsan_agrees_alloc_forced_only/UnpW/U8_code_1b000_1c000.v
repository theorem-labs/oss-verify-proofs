(* reloc-zl14c *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress3_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1b48c : bv 32 := 0x00062703.
Lemma F_1b48c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1b5e4 : word) = Some W_1b48c.
Proof. vm_refl. Qed.
Lemma D_1b48c : decode_any W_1b48c = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b490 : bv 32 := 0x00d777b3.
Lemma F_1b490 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1b5e8 : word) = Some W_1b490.
Proof. vm_refl. Qed.
Lemma D_1b490 : decode_any W_1b490 = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b494 : bv 32 := 0x1606282f.
Lemma F_1b494 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1b5ec : word) = Some W_1b494.
Proof. vm_refl. Qed.
Lemma D_1b494 : decode_any W_1b494 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b498 : bv 32 := 0x00e81663.
Lemma F_1b498 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1b5f0 : word) = Some W_1b498.
Proof. vm_refl. Qed.
Lemma D_1b498 : decode_any W_1b498 = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b49c : bv 32 := 0x1ef628af.
Lemma F_1b49c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1b5f4 : word) = Some W_1b49c.
Proof. vm_refl. Qed.
Lemma D_1b49c : decode_any W_1b49c = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4a0 : bv 32 := 0xfe089ae3.
Lemma F_1b4a0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1b5f8 : word) = Some W_1b4a0.
Proof. vm_refl. Qed.
Lemma D_1b4a0 : decode_any W_1b4a0 = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4a4 : bv 32 := 0x0008081b.
Lemma F_1b4a4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1b5fc : word) = Some W_1b4a4.
Proof. vm_refl. Qed.
Lemma D_1b4a4 : decode_any W_1b4a4 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4a8 : bv 32 := 0xfee812e3.
Lemma F_1b4a8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1b600 : word) = Some W_1b4a8.
Proof. vm_refl. Qed.
Lemma D_1b4a8 : decode_any W_1b4a8 = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbf0 : bv 32 := 0x02053703.
Lemma F_1bbf0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd48 : word) = Some W_1bbf0.
Proof. vm_refl. Qed.
Lemma D_1bbf0 : decode_any W_1bbf0 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbf4 : bv 32 := 0x00c75793.
Lemma F_1bbf4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd4c : word) = Some W_1bbf4.
Proof. vm_refl. Qed.
Lemma D_1bbf4 : decode_any W_1bbf4 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbf8 : bv 32 := 0x00078e63.
Lemma F_1bbf8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd50 : word) = Some W_1bbf8.
Proof. vm_refl. Qed.
Lemma D_1bbf8 : decode_any W_1bbf8 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbfc : bv 32 := 0x01f77793.
Lemma F_1bbfc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd54 : word) = Some W_1bbfc.
Proof. vm_refl. Qed.
Lemma D_1bbfc : decode_any W_1bbfc = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc00 : bv 32 := 0x00079a63.
Lemma F_1bc00 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd58 : word) = Some W_1bc00.
Proof. vm_refl. Qed.
Lemma D_1bc00 : decode_any W_1bc00 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc04 : bv 32 := 0xfffff7b7.
Lemma F_1bc04 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd5c : word) = Some W_1bc04.
Proof. vm_refl. Qed.
Lemma D_1bc04 : decode_any W_1bc04 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc08 : bv 32 := 0x00f77733.
Lemma F_1bc08 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd60 : word) = Some W_1bc08.
Proof. vm_refl. Qed.
Lemma D_1bc08 : decode_any W_1bc08 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc0c : bv 32 := 0xff070713.
Lemma F_1bc0c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd64 : word) = Some W_1bc0c.
Proof. vm_refl. Qed.
Lemma D_1bc0c : decode_any W_1bc0c = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc10 : bv 32 := 0x0200006f.
Lemma F_1bc10 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd68 : word) = Some W_1bc10.
Proof. vm_refl. Qed.
Lemma D_1bc10 : decode_any W_1bc10 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc14 : bv 32 := 0x00575713.
Lemma F_1bc14 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd6c : word) = Some W_1bc14.
Proof. vm_refl. Qed.
Lemma D_1bc14 : decode_any W_1bc14 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc18 : bv 32 := 0xffff6797.
Lemma F_1bc18 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd70 : word) = Some W_1bc18.
Proof. vm_refl. Qed.
Lemma D_1bc18 : decode_any W_1bc18 = Some (Auipc 15 1048566, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc1c : bv 32 := 0x07e77713.
Lemma F_1bc1c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd74 : word) = Some W_1bc1c.
Proof. vm_refl. Qed.
Lemma D_1bc1c : decode_any W_1bc1c = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc20 : bv 32 := 0x6ec78793.
Lemma F_1bc20 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd78 : word) = Some W_1bc20.
Proof. vm_refl. Qed.
Lemma D_1bc20 : decode_any W_1bc20 = Some (OpImm ALU_ADD 15 15 1772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc24 : bv 32 := 0x00e78733.
Lemma F_1bc24 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd7c : word) = Some W_1bc24.
Proof. vm_refl. Qed.
Lemma D_1bc24 : decode_any W_1bc24 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc28 : bv 32 := 0x00075703.
Lemma F_1bc28 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd80 : word) = Some W_1bc28.
Proof. vm_refl. Qed.
Lemma D_1bc28 : decode_any W_1bc28 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc2c : bv 32 := 0x00471713.
Lemma F_1bc2c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd84 : word) = Some W_1bc2c.
Proof. vm_refl. Qed.
Lemma D_1bc2c : decode_any W_1bc2c = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc30 : bv 32 := 0x01053803.
Lemma F_1bc30 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd88 : word) = Some W_1bc30.
Proof. vm_refl. Qed.
Lemma D_1bc30 : decode_any W_1bc30 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc34 : bv 32 := 0x02b707b3.
Lemma F_1bc34 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd8c : word) = Some W_1bc34.
Proof. vm_refl. Qed.
Lemma D_1bc34 : decode_any W_1bc34 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc38 : bv 32 := 0x00f807b3.
Lemma F_1bc38 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd90 : word) = Some W_1bc38.
Proof. vm_refl. Qed.
Lemma D_1bc38 : decode_any W_1bc38 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc3c : bv 32 := 0x00d7c883.
Lemma F_1bc3c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd94 : word) = Some W_1bc3c.
Proof. vm_refl. Qed.
Lemma D_1bc3c : decode_any W_1bc3c = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc40 : bv 32 := 0x40c702b3.
Lemma F_1bc40 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd98 : word) = Some W_1bc40.
Proof. vm_refl. Qed.
Lemma D_1bc40 : decode_any W_1bc40 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc44 : bv 32 := 0xffc28293.
Lemma F_1bc44 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bd9c : word) = Some W_1bc44.
Proof. vm_refl. Qed.
Lemma D_1bc44 : decode_any W_1bc44 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc48 : bv 32 := 0x01078793.
Lemma F_1bc48 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bda0 : word) = Some W_1bc48.
Proof. vm_refl. Qed.
Lemma D_1bc48 : decode_any W_1bc48 = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc4c : bv 32 := 0x00088663.
Lemma F_1bc4c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bda4 : word) = Some W_1bc4c.
Proof. vm_refl. Qed.
Lemma D_1bc4c : decode_any W_1bc4c = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc50 : bv 32 := 0xffe7d683.
Lemma F_1bc50 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bda8 : word) = Some W_1bc50.
Proof. vm_refl. Qed.
Lemma D_1bc50 : decode_any W_1bc50 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc54 : bv 32 := 0x00168693.
Lemma F_1bc54 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdac : word) = Some W_1bc54.
Proof. vm_refl. Qed.
Lemma D_1bc54 : decode_any W_1bc54 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc58 : bv 32 := 0xffc7c383.
Lemma F_1bc58 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdb0 : word) = Some W_1bc58.
Proof. vm_refl. Qed.
Lemma D_1bc58 : decode_any W_1bc58 = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc5c : bv 32 := 0x0042d313.
Lemma F_1bc5c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdb4 : word) = Some W_1bc5c.
Proof. vm_refl. Qed.
Lemma D_1bc5c : decode_any W_1bc5c = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc60 : bv 32 := 0x0ff6f893.
Lemma F_1bc60 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdb8 : word) = Some W_1bc60.
Proof. vm_refl. Qed.
Lemma D_1bc60 : decode_any W_1bc60 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc64 : bv 32 := 0x00038463.
Lemma F_1bc64 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdbc : word) = Some W_1bc64.
Proof. vm_refl. Qed.
Lemma D_1bc64 : decode_any W_1bc64 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc6c : bv 32 := 0x03137e63.
Lemma F_1bc6c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdc4 : word) = Some W_1bc6c.
Proof. vm_refl. Qed.
Lemma D_1bc6c : decode_any W_1bc6c = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc70 : bv 32 := 0x0052d693.
Lemma F_1bc70 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdc8 : word) = Some W_1bc70.
Proof. vm_refl. Qed.
Lemma D_1bc70 : decode_any W_1bc70 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc74 : bv 32 := 0x00d366b3.
Lemma F_1bc74 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdcc : word) = Some W_1bc74.
Proof. vm_refl. Qed.
Lemma D_1bc74 : decode_any W_1bc74 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc78 : bv 32 := 0x0026d293.
Lemma F_1bc78 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdd0 : word) = Some W_1bc78.
Proof. vm_refl. Qed.
Lemma D_1bc78 : decode_any W_1bc78 = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc7c : bv 32 := 0x00d2e6b3.
Lemma F_1bc7c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdd4 : word) = Some W_1bc7c.
Proof. vm_refl. Qed.
Lemma D_1bc7c : decode_any W_1bc7c = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc80 : bv 32 := 0x0046d293.
Lemma F_1bc80 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdd8 : word) = Some W_1bc80.
Proof. vm_refl. Qed.
Lemma D_1bc80 : decode_any W_1bc80 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc84 : bv 32 := 0x00d2e6b3.
Lemma F_1bc84 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bddc : word) = Some W_1bc84.
Proof. vm_refl. Qed.
Lemma D_1bc84 : decode_any W_1bc84 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc88 : bv 32 := 0x00d8f6b3.
Lemma F_1bc88 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bde0 : word) = Some W_1bc88.
Proof. vm_refl. Qed.
Lemma D_1bc88 : decode_any W_1bc88 = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc8c : bv 32 := 0x00d338b3.
Lemma F_1bc8c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bde4 : word) = Some W_1bc8c.
Proof. vm_refl. Qed.
Lemma D_1bc8c : decode_any W_1bc8c = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc90 : bv 32 := 0xfff34293.
Lemma F_1bc90 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bde8 : word) = Some W_1bc90.
Proof. vm_refl. Qed.
Lemma D_1bc90 : decode_any W_1bc90 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc94 : bv 32 := 0x411008bb.
Lemma F_1bc94 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdec : word) = Some W_1bc94.
Proof. vm_refl. Qed.
Lemma D_1bc94 : decode_any W_1bc94 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc98 : bv 32 := 0x0058f8b3.
Lemma F_1bc98 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdf0 : word) = Some W_1bc98.
Proof. vm_refl. Qed.
Lemma D_1bc98 : decode_any W_1bc98 = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc9c : bv 32 := 0x00d888bb.
Lemma F_1bc9c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdf4 : word) = Some W_1bc9c.
Proof. vm_refl. Qed.
Lemma D_1bc9c : decode_any W_1bc9c = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bca0 : bv 32 := 0x01137463.
Lemma F_1bca0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1bdf8 : word) = Some W_1bca0.
Proof. vm_refl. Qed.
Lemma D_1bca0 : decode_any W_1bca0 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bca8 : bv 32 := 0x00078693.
Lemma F_1bca8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be00 : word) = Some W_1bca8.
Proof. vm_refl. Qed.
Lemma D_1bca8 : decode_any W_1bca8 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcac : bv 32 := 0x02088063.
Lemma F_1bcac : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be04 : word) = Some W_1bcac.
Proof. vm_refl. Qed.
Lemma D_1bcac : decode_any W_1bcac = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcb0 : bv 32 := 0xfe000813.
Lemma F_1bcb0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be08 : word) = Some W_1bcb0.
Proof. vm_refl. Qed.
Lemma D_1bcb0 : decode_any W_1bcb0 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcb4 : bv 32 := 0x0048969b.
Lemma F_1bcb4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be0c : word) = Some W_1bcb4.
Proof. vm_refl. Qed.
Lemma D_1bcb4 : decode_any W_1bcb4 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcb8 : bv 32 := 0x00d786b3.
Lemma F_1bcb8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be10 : word) = Some W_1bcb8.
Proof. vm_refl. Qed.
Lemma D_1bcb8 : decode_any W_1bcb8 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcbc : bv 32 := 0xff078ea3.
Lemma F_1bcbc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be14 : word) = Some W_1bcbc.
Proof. vm_refl. Qed.
Lemma D_1bcbc : decode_any W_1bcbc = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcc0 : bv 32 := 0xff179f23.
Lemma F_1bcc0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be18 : word) = Some W_1bcc0.
Proof. vm_refl. Qed.
Lemma D_1bcc0 : decode_any W_1bcc0 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcc4 : bv 32 := 0xfe068e23.
Lemma F_1bcc4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be1c : word) = Some W_1bcc4.
Proof. vm_refl. Qed.
Lemma D_1bcc4 : decode_any W_1bcc4 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcc8 : bv 32 := 0x01053803.
Lemma F_1bcc8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be20 : word) = Some W_1bcc8.
Proof. vm_refl. Qed.
Lemma D_1bcc8 : decode_any W_1bcc8 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bccc : bv 32 := 0x00e78733.
Lemma F_1bccc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be24 : word) = Some W_1bccc.
Proof. vm_refl. Qed.
Lemma D_1bccc : decode_any W_1bccc = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcd0 : bv 32 := 0x410687bb.
Lemma F_1bcd0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be28 : word) = Some W_1bcd0.
Proof. vm_refl. Qed.
Lemma D_1bcd0 : decode_any W_1bcd0 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcd4 : bv 32 := 0x00d60633.
Lemma F_1bcd4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be2c : word) = Some W_1bcd4.
Proof. vm_refl. Qed.
Lemma D_1bcd4 : decode_any W_1bcd4 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcd8 : bv 32 := 0xffc70513.
Lemma F_1bcd8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be30 : word) = Some W_1bcd8.
Proof. vm_refl. Qed.
Lemma D_1bcd8 : decode_any W_1bcd8 = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcdc : bv 32 := 0xff078793.
Lemma F_1bcdc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be34 : word) = Some W_1bcdc.
Proof. vm_refl. Qed.
Lemma D_1bcdc : decode_any W_1bcdc = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bce0 : bv 32 := 0x0047d793.
Lemma F_1bce0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be38 : word) = Some W_1bce0.
Proof. vm_refl. Qed.
Lemma D_1bce0 : decode_any W_1bce0 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bce4 : bv 32 := 0x40c5083b.
Lemma F_1bce4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be3c : word) = Some W_1bce4.
Proof. vm_refl. Qed.
Lemma D_1bce4 : decode_any W_1bce4 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bce8 : bv 32 := 0xfeb68ea3.
Lemma F_1bce8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be40 : word) = Some W_1bce8.
Proof. vm_refl. Qed.
Lemma D_1bce8 : decode_any W_1bce8 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcec : bv 32 := 0xfef69f23.
Lemma F_1bcec : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be44 : word) = Some W_1bcec.
Proof. vm_refl. Qed.
Lemma D_1bcec : decode_any W_1bcec = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcf0 : bv 32 := 0x02080463.
Lemma F_1bcf0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be48 : word) = Some W_1bcf0.
Proof. vm_refl. Qed.
Lemma D_1bcf0 : decode_any W_1bcf0 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcf4 : bv 32 := 0x40c505bb.
Lemma F_1bcf4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be4c : word) = Some W_1bcf4.
Proof. vm_refl. Qed.
Lemma D_1bcf4 : decode_any W_1bcf4 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcf8 : bv 32 := 0x40b0063b.
Lemma F_1bcf8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be50 : word) = Some W_1bcf8.
Proof. vm_refl. Qed.
Lemma D_1bcf8 : decode_any W_1bcf8 = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcfc : bv 32 := 0x00c50633.
Lemma F_1bcfc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be54 : word) = Some W_1bcfc.
Proof. vm_refl. Qed.
Lemma D_1bcfc : decode_any W_1bcfc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd00 : bv 32 := 0x00500513.
Lemma F_1bd00 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be58 : word) = Some W_1bd00.
Proof. vm_refl. Qed.
Lemma D_1bd00 : decode_any W_1bd00 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd04 : bv 32 := 0x00060023.
Lemma F_1bd04 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be5c : word) = Some W_1bd04.
Proof. vm_refl. Qed.
Lemma D_1bd04 : decode_any W_1bd04 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd08 : bv 32 := 0x00a5cc63.
Lemma F_1bd08 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be60 : word) = Some W_1bd08.
Proof. vm_refl. Qed.
Lemma D_1bd08 : decode_any W_1bd08 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd0c : bv 32 := 0xfe070ba3.
Lemma F_1bd0c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be64 : word) = Some W_1bd0c.
Proof. vm_refl. Qed.
Lemma D_1bd0c : decode_any W_1bd0c = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd10 : bv 32 := 0xfeb72c23.
Lemma F_1bd10 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be68 : word) = Some W_1bd10.
Proof. vm_refl. Qed.
Lemma D_1bd10 : decode_any W_1bd10 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd14 : bv 32 := 0x0100006f.
Lemma F_1bd14 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be6c : word) = Some W_1bd14.
Proof. vm_refl. Qed.
Lemma D_1bd14 : decode_any W_1bd14 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd18 : bv 32 := 0x00000513.
Lemma F_1bd18 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be70 : word) = Some W_1bd18.
Proof. vm_refl. Qed.
Lemma D_1bd18 : decode_any W_1bd18 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd1c : bv 32 := 0x0080006f.
Lemma F_1bd1c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be74 : word) = Some W_1bd1c.
Proof. vm_refl. Qed.
Lemma D_1bd1c : decode_any W_1bd1c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd20 : bv 32 := 0x00058513.
Lemma F_1bd20 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be78 : word) = Some W_1bd20.
Proof. vm_refl. Qed.
Lemma D_1bd20 : decode_any W_1bd20 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd24 : bv 32 := 0xffd6c583.
Lemma F_1bd24 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be7c : word) = Some W_1bd24.
Proof. vm_refl. Qed.
Lemma D_1bd24 : decode_any W_1bd24 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd28 : bv 32 := 0x01f5f593.
Lemma F_1bd28 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be80 : word) = Some W_1bd28.
Proof. vm_refl. Qed.
Lemma D_1bd28 : decode_any W_1bd28 = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd2c : bv 32 := 0x00551513.
Lemma F_1bd2c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be84 : word) = Some W_1bd2c.
Proof. vm_refl. Qed.
Lemma D_1bd2c : decode_any W_1bd2c = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd30 : bv 32 := 0x00b56533.
Lemma F_1bd30 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be88 : word) = Some W_1bd30.
Proof. vm_refl. Qed.
Lemma D_1bd30 : decode_any W_1bd30 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd34 : bv 32 := 0xfea68ea3.
Lemma F_1bd34 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be8c : word) = Some W_1bd34.
Proof. vm_refl. Qed.
Lemma D_1bd34 : decode_any W_1bd34 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd38 : bv 32 := 0x00068513.
Lemma F_1bd38 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be90 : word) = Some W_1bd38.
Proof. vm_refl. Qed.
Lemma D_1bd38 : decode_any W_1bd38 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd3c : bv 32 := 0x00008067.
Lemma F_1bd3c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1be94 : word) = Some W_1bd3c.
Proof. vm_refl. Qed.
Lemma D_1bd3c : decode_any W_1bd3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
