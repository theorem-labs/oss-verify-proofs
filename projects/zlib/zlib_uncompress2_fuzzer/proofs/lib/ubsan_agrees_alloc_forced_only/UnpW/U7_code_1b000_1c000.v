(* reloc-zl14c *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress2_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1b3fc : bv 32 := 0x00062703.
Lemma F_1b3fc : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1b554 : word) = Some W_1b3fc.
Proof. vm_refl. Qed.
Lemma D_1b3fc : decode_any W_1b3fc = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b400 : bv 32 := 0x00d777b3.
Lemma F_1b400 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1b558 : word) = Some W_1b400.
Proof. vm_refl. Qed.
Lemma D_1b400 : decode_any W_1b400 = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b404 : bv 32 := 0x1606282f.
Lemma F_1b404 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1b55c : word) = Some W_1b404.
Proof. vm_refl. Qed.
Lemma D_1b404 : decode_any W_1b404 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b408 : bv 32 := 0x00e81663.
Lemma F_1b408 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1b560 : word) = Some W_1b408.
Proof. vm_refl. Qed.
Lemma D_1b408 : decode_any W_1b408 = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b40c : bv 32 := 0x1ef628af.
Lemma F_1b40c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1b564 : word) = Some W_1b40c.
Proof. vm_refl. Qed.
Lemma D_1b40c : decode_any W_1b40c = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b410 : bv 32 := 0xfe089ae3.
Lemma F_1b410 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1b568 : word) = Some W_1b410.
Proof. vm_refl. Qed.
Lemma D_1b410 : decode_any W_1b410 = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b414 : bv 32 := 0x0008081b.
Lemma F_1b414 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1b56c : word) = Some W_1b414.
Proof. vm_refl. Qed.
Lemma D_1b414 : decode_any W_1b414 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b418 : bv 32 := 0xfee812e3.
Lemma F_1b418 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1b570 : word) = Some W_1b418.
Proof. vm_refl. Qed.
Lemma D_1b418 : decode_any W_1b418 = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb60 : bv 32 := 0x02053703.
Lemma F_1bb60 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcb8 : word) = Some W_1bb60.
Proof. vm_refl. Qed.
Lemma D_1bb60 : decode_any W_1bb60 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb64 : bv 32 := 0x00c75793.
Lemma F_1bb64 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcbc : word) = Some W_1bb64.
Proof. vm_refl. Qed.
Lemma D_1bb64 : decode_any W_1bb64 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb68 : bv 32 := 0x00078e63.
Lemma F_1bb68 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcc0 : word) = Some W_1bb68.
Proof. vm_refl. Qed.
Lemma D_1bb68 : decode_any W_1bb68 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb6c : bv 32 := 0x01f77793.
Lemma F_1bb6c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcc4 : word) = Some W_1bb6c.
Proof. vm_refl. Qed.
Lemma D_1bb6c : decode_any W_1bb6c = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb70 : bv 32 := 0x00079a63.
Lemma F_1bb70 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcc8 : word) = Some W_1bb70.
Proof. vm_refl. Qed.
Lemma D_1bb70 : decode_any W_1bb70 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb74 : bv 32 := 0xfffff7b7.
Lemma F_1bb74 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bccc : word) = Some W_1bb74.
Proof. vm_refl. Qed.
Lemma D_1bb74 : decode_any W_1bb74 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb78 : bv 32 := 0x00f77733.
Lemma F_1bb78 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcd0 : word) = Some W_1bb78.
Proof. vm_refl. Qed.
Lemma D_1bb78 : decode_any W_1bb78 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb7c : bv 32 := 0xff070713.
Lemma F_1bb7c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcd4 : word) = Some W_1bb7c.
Proof. vm_refl. Qed.
Lemma D_1bb7c : decode_any W_1bb7c = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb80 : bv 32 := 0x0200006f.
Lemma F_1bb80 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcd8 : word) = Some W_1bb80.
Proof. vm_refl. Qed.
Lemma D_1bb80 : decode_any W_1bb80 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb84 : bv 32 := 0x00575713.
Lemma F_1bb84 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcdc : word) = Some W_1bb84.
Proof. vm_refl. Qed.
Lemma D_1bb84 : decode_any W_1bb84 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb88 : bv 32 := 0xffff6797.
Lemma F_1bb88 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bce0 : word) = Some W_1bb88.
Proof. vm_refl. Qed.
Lemma D_1bb88 : decode_any W_1bb88 = Some (Auipc 15 1048566, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb8c : bv 32 := 0x07e77713.
Lemma F_1bb8c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bce4 : word) = Some W_1bb8c.
Proof. vm_refl. Qed.
Lemma D_1bb8c : decode_any W_1bb8c = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb90 : bv 32 := 0x77c78793.
Lemma F_1bb90 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bce8 : word) = Some W_1bb90.
Proof. vm_refl. Qed.
Lemma D_1bb90 : decode_any W_1bb90 = Some (OpImm ALU_ADD 15 15 1916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb94 : bv 32 := 0x00e78733.
Lemma F_1bb94 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcec : word) = Some W_1bb94.
Proof. vm_refl. Qed.
Lemma D_1bb94 : decode_any W_1bb94 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb98 : bv 32 := 0x00075703.
Lemma F_1bb98 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcf0 : word) = Some W_1bb98.
Proof. vm_refl. Qed.
Lemma D_1bb98 : decode_any W_1bb98 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb9c : bv 32 := 0x00471713.
Lemma F_1bb9c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcf4 : word) = Some W_1bb9c.
Proof. vm_refl. Qed.
Lemma D_1bb9c : decode_any W_1bb9c = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bba0 : bv 32 := 0x01053803.
Lemma F_1bba0 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcf8 : word) = Some W_1bba0.
Proof. vm_refl. Qed.
Lemma D_1bba0 : decode_any W_1bba0 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bba4 : bv 32 := 0x02b707b3.
Lemma F_1bba4 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bcfc : word) = Some W_1bba4.
Proof. vm_refl. Qed.
Lemma D_1bba4 : decode_any W_1bba4 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bba8 : bv 32 := 0x00f807b3.
Lemma F_1bba8 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd00 : word) = Some W_1bba8.
Proof. vm_refl. Qed.
Lemma D_1bba8 : decode_any W_1bba8 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbac : bv 32 := 0x00d7c883.
Lemma F_1bbac : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd04 : word) = Some W_1bbac.
Proof. vm_refl. Qed.
Lemma D_1bbac : decode_any W_1bbac = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbb0 : bv 32 := 0x40c702b3.
Lemma F_1bbb0 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd08 : word) = Some W_1bbb0.
Proof. vm_refl. Qed.
Lemma D_1bbb0 : decode_any W_1bbb0 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbb4 : bv 32 := 0xffc28293.
Lemma F_1bbb4 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd0c : word) = Some W_1bbb4.
Proof. vm_refl. Qed.
Lemma D_1bbb4 : decode_any W_1bbb4 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbb8 : bv 32 := 0x01078793.
Lemma F_1bbb8 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd10 : word) = Some W_1bbb8.
Proof. vm_refl. Qed.
Lemma D_1bbb8 : decode_any W_1bbb8 = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbbc : bv 32 := 0x00088663.
Lemma F_1bbbc : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd14 : word) = Some W_1bbbc.
Proof. vm_refl. Qed.
Lemma D_1bbbc : decode_any W_1bbbc = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbc0 : bv 32 := 0xffe7d683.
Lemma F_1bbc0 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd18 : word) = Some W_1bbc0.
Proof. vm_refl. Qed.
Lemma D_1bbc0 : decode_any W_1bbc0 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbc4 : bv 32 := 0x00168693.
Lemma F_1bbc4 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd1c : word) = Some W_1bbc4.
Proof. vm_refl. Qed.
Lemma D_1bbc4 : decode_any W_1bbc4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbc8 : bv 32 := 0xffc7c383.
Lemma F_1bbc8 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd20 : word) = Some W_1bbc8.
Proof. vm_refl. Qed.
Lemma D_1bbc8 : decode_any W_1bbc8 = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbcc : bv 32 := 0x0042d313.
Lemma F_1bbcc : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd24 : word) = Some W_1bbcc.
Proof. vm_refl. Qed.
Lemma D_1bbcc : decode_any W_1bbcc = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbd0 : bv 32 := 0x0ff6f893.
Lemma F_1bbd0 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd28 : word) = Some W_1bbd0.
Proof. vm_refl. Qed.
Lemma D_1bbd0 : decode_any W_1bbd0 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbd4 : bv 32 := 0x00038463.
Lemma F_1bbd4 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd2c : word) = Some W_1bbd4.
Proof. vm_refl. Qed.
Lemma D_1bbd4 : decode_any W_1bbd4 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbdc : bv 32 := 0x03137e63.
Lemma F_1bbdc : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd34 : word) = Some W_1bbdc.
Proof. vm_refl. Qed.
Lemma D_1bbdc : decode_any W_1bbdc = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbe0 : bv 32 := 0x0052d693.
Lemma F_1bbe0 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd38 : word) = Some W_1bbe0.
Proof. vm_refl. Qed.
Lemma D_1bbe0 : decode_any W_1bbe0 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbe4 : bv 32 := 0x00d366b3.
Lemma F_1bbe4 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd3c : word) = Some W_1bbe4.
Proof. vm_refl. Qed.
Lemma D_1bbe4 : decode_any W_1bbe4 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbe8 : bv 32 := 0x0026d293.
Lemma F_1bbe8 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd40 : word) = Some W_1bbe8.
Proof. vm_refl. Qed.
Lemma D_1bbe8 : decode_any W_1bbe8 = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbec : bv 32 := 0x00d2e6b3.
Lemma F_1bbec : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd44 : word) = Some W_1bbec.
Proof. vm_refl. Qed.
Lemma D_1bbec : decode_any W_1bbec = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbf0 : bv 32 := 0x0046d293.
Lemma F_1bbf0 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd48 : word) = Some W_1bbf0.
Proof. vm_refl. Qed.
Lemma D_1bbf0 : decode_any W_1bbf0 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbf4 : bv 32 := 0x00d2e6b3.
Lemma F_1bbf4 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd4c : word) = Some W_1bbf4.
Proof. vm_refl. Qed.
Lemma D_1bbf4 : decode_any W_1bbf4 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbf8 : bv 32 := 0x00d8f6b3.
Lemma F_1bbf8 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd50 : word) = Some W_1bbf8.
Proof. vm_refl. Qed.
Lemma D_1bbf8 : decode_any W_1bbf8 = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bbfc : bv 32 := 0x00d338b3.
Lemma F_1bbfc : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd54 : word) = Some W_1bbfc.
Proof. vm_refl. Qed.
Lemma D_1bbfc : decode_any W_1bbfc = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc00 : bv 32 := 0xfff34293.
Lemma F_1bc00 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd58 : word) = Some W_1bc00.
Proof. vm_refl. Qed.
Lemma D_1bc00 : decode_any W_1bc00 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc04 : bv 32 := 0x411008bb.
Lemma F_1bc04 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd5c : word) = Some W_1bc04.
Proof. vm_refl. Qed.
Lemma D_1bc04 : decode_any W_1bc04 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc08 : bv 32 := 0x0058f8b3.
Lemma F_1bc08 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd60 : word) = Some W_1bc08.
Proof. vm_refl. Qed.
Lemma D_1bc08 : decode_any W_1bc08 = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc0c : bv 32 := 0x00d888bb.
Lemma F_1bc0c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd64 : word) = Some W_1bc0c.
Proof. vm_refl. Qed.
Lemma D_1bc0c : decode_any W_1bc0c = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc10 : bv 32 := 0x01137463.
Lemma F_1bc10 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd68 : word) = Some W_1bc10.
Proof. vm_refl. Qed.
Lemma D_1bc10 : decode_any W_1bc10 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc18 : bv 32 := 0x00078693.
Lemma F_1bc18 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd70 : word) = Some W_1bc18.
Proof. vm_refl. Qed.
Lemma D_1bc18 : decode_any W_1bc18 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc1c : bv 32 := 0x02088063.
Lemma F_1bc1c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd74 : word) = Some W_1bc1c.
Proof. vm_refl. Qed.
Lemma D_1bc1c : decode_any W_1bc1c = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc20 : bv 32 := 0xfe000813.
Lemma F_1bc20 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd78 : word) = Some W_1bc20.
Proof. vm_refl. Qed.
Lemma D_1bc20 : decode_any W_1bc20 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc24 : bv 32 := 0x0048969b.
Lemma F_1bc24 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd7c : word) = Some W_1bc24.
Proof. vm_refl. Qed.
Lemma D_1bc24 : decode_any W_1bc24 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc28 : bv 32 := 0x00d786b3.
Lemma F_1bc28 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd80 : word) = Some W_1bc28.
Proof. vm_refl. Qed.
Lemma D_1bc28 : decode_any W_1bc28 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc2c : bv 32 := 0xff078ea3.
Lemma F_1bc2c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd84 : word) = Some W_1bc2c.
Proof. vm_refl. Qed.
Lemma D_1bc2c : decode_any W_1bc2c = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc30 : bv 32 := 0xff179f23.
Lemma F_1bc30 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd88 : word) = Some W_1bc30.
Proof. vm_refl. Qed.
Lemma D_1bc30 : decode_any W_1bc30 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc34 : bv 32 := 0xfe068e23.
Lemma F_1bc34 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd8c : word) = Some W_1bc34.
Proof. vm_refl. Qed.
Lemma D_1bc34 : decode_any W_1bc34 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc38 : bv 32 := 0x01053803.
Lemma F_1bc38 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd90 : word) = Some W_1bc38.
Proof. vm_refl. Qed.
Lemma D_1bc38 : decode_any W_1bc38 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc3c : bv 32 := 0x00e78733.
Lemma F_1bc3c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd94 : word) = Some W_1bc3c.
Proof. vm_refl. Qed.
Lemma D_1bc3c : decode_any W_1bc3c = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc40 : bv 32 := 0x410687bb.
Lemma F_1bc40 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd98 : word) = Some W_1bc40.
Proof. vm_refl. Qed.
Lemma D_1bc40 : decode_any W_1bc40 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc44 : bv 32 := 0x00d60633.
Lemma F_1bc44 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bd9c : word) = Some W_1bc44.
Proof. vm_refl. Qed.
Lemma D_1bc44 : decode_any W_1bc44 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc48 : bv 32 := 0xffc70513.
Lemma F_1bc48 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bda0 : word) = Some W_1bc48.
Proof. vm_refl. Qed.
Lemma D_1bc48 : decode_any W_1bc48 = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc4c : bv 32 := 0xff078793.
Lemma F_1bc4c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bda4 : word) = Some W_1bc4c.
Proof. vm_refl. Qed.
Lemma D_1bc4c : decode_any W_1bc4c = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc50 : bv 32 := 0x0047d793.
Lemma F_1bc50 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bda8 : word) = Some W_1bc50.
Proof. vm_refl. Qed.
Lemma D_1bc50 : decode_any W_1bc50 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc54 : bv 32 := 0x40c5083b.
Lemma F_1bc54 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdac : word) = Some W_1bc54.
Proof. vm_refl. Qed.
Lemma D_1bc54 : decode_any W_1bc54 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc58 : bv 32 := 0xfeb68ea3.
Lemma F_1bc58 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdb0 : word) = Some W_1bc58.
Proof. vm_refl. Qed.
Lemma D_1bc58 : decode_any W_1bc58 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc5c : bv 32 := 0xfef69f23.
Lemma F_1bc5c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdb4 : word) = Some W_1bc5c.
Proof. vm_refl. Qed.
Lemma D_1bc5c : decode_any W_1bc5c = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc60 : bv 32 := 0x02080463.
Lemma F_1bc60 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdb8 : word) = Some W_1bc60.
Proof. vm_refl. Qed.
Lemma D_1bc60 : decode_any W_1bc60 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc64 : bv 32 := 0x40c505bb.
Lemma F_1bc64 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdbc : word) = Some W_1bc64.
Proof. vm_refl. Qed.
Lemma D_1bc64 : decode_any W_1bc64 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc68 : bv 32 := 0x40b0063b.
Lemma F_1bc68 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdc0 : word) = Some W_1bc68.
Proof. vm_refl. Qed.
Lemma D_1bc68 : decode_any W_1bc68 = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc6c : bv 32 := 0x00c50633.
Lemma F_1bc6c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdc4 : word) = Some W_1bc6c.
Proof. vm_refl. Qed.
Lemma D_1bc6c : decode_any W_1bc6c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc70 : bv 32 := 0x00500513.
Lemma F_1bc70 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdc8 : word) = Some W_1bc70.
Proof. vm_refl. Qed.
Lemma D_1bc70 : decode_any W_1bc70 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc74 : bv 32 := 0x00060023.
Lemma F_1bc74 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdcc : word) = Some W_1bc74.
Proof. vm_refl. Qed.
Lemma D_1bc74 : decode_any W_1bc74 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc78 : bv 32 := 0x00a5cc63.
Lemma F_1bc78 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdd0 : word) = Some W_1bc78.
Proof. vm_refl. Qed.
Lemma D_1bc78 : decode_any W_1bc78 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc7c : bv 32 := 0xfe070ba3.
Lemma F_1bc7c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdd4 : word) = Some W_1bc7c.
Proof. vm_refl. Qed.
Lemma D_1bc7c : decode_any W_1bc7c = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc80 : bv 32 := 0xfeb72c23.
Lemma F_1bc80 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdd8 : word) = Some W_1bc80.
Proof. vm_refl. Qed.
Lemma D_1bc80 : decode_any W_1bc80 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc84 : bv 32 := 0x0100006f.
Lemma F_1bc84 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bddc : word) = Some W_1bc84.
Proof. vm_refl. Qed.
Lemma D_1bc84 : decode_any W_1bc84 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc88 : bv 32 := 0x00000513.
Lemma F_1bc88 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bde0 : word) = Some W_1bc88.
Proof. vm_refl. Qed.
Lemma D_1bc88 : decode_any W_1bc88 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc8c : bv 32 := 0x0080006f.
Lemma F_1bc8c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bde4 : word) = Some W_1bc8c.
Proof. vm_refl. Qed.
Lemma D_1bc8c : decode_any W_1bc8c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc90 : bv 32 := 0x00058513.
Lemma F_1bc90 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bde8 : word) = Some W_1bc90.
Proof. vm_refl. Qed.
Lemma D_1bc90 : decode_any W_1bc90 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc94 : bv 32 := 0xffd6c583.
Lemma F_1bc94 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdec : word) = Some W_1bc94.
Proof. vm_refl. Qed.
Lemma D_1bc94 : decode_any W_1bc94 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc98 : bv 32 := 0x01f5f593.
Lemma F_1bc98 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdf0 : word) = Some W_1bc98.
Proof. vm_refl. Qed.
Lemma D_1bc98 : decode_any W_1bc98 = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc9c : bv 32 := 0x00551513.
Lemma F_1bc9c : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdf4 : word) = Some W_1bc9c.
Proof. vm_refl. Qed.
Lemma D_1bc9c : decode_any W_1bc9c = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bca0 : bv 32 := 0x00b56533.
Lemma F_1bca0 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdf8 : word) = Some W_1bca0.
Proof. vm_refl. Qed.
Lemma D_1bca0 : decode_any W_1bca0 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bca4 : bv 32 := 0xfea68ea3.
Lemma F_1bca4 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1bdfc : word) = Some W_1bca4.
Proof. vm_refl. Qed.
Lemma D_1bca4 : decode_any W_1bca4 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bca8 : bv 32 := 0x00068513.
Lemma F_1bca8 : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1be00 : word) = Some W_1bca8.
Proof. vm_refl. Qed.
Lemma D_1bca8 : decode_any W_1bca8 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcac : bv 32 := 0x00008067.
Lemma F_1bcac : fetch_word TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1be04 : word) = Some W_1bcac.
Proof. vm_refl. Qed.
Lemma D_1bcac : decode_any W_1bcac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
