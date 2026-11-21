(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_15240 : bv 32 := 0x00008067.
Lemma F_15240 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x152ec : word) = Some W_15240.
Proof. vm_refl. Qed.
Lemma D_15240 : decode_any W_15240 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15244 : bv 32 := 0xe8010113.
Lemma F_15244 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x152f0 : word) = Some W_15244.
Proof. vm_refl. Qed.
Lemma D_15244 : decode_any W_15244 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_15248 : bv 32 := 0x16113c23.
Lemma F_15248 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x152f4 : word) = Some W_15248.
Proof. vm_refl. Qed.
Lemma D_15248 : decode_any W_15248 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_1524c : bv 32 := 0x16813823.
Lemma F_1524c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x152f8 : word) = Some W_1524c.
Proof. vm_refl. Qed.
Lemma D_1524c : decode_any W_1524c = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_15250 : bv 32 := 0x16913423.
Lemma F_15250 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x152fc : word) = Some W_15250.
Proof. vm_refl. Qed.
Lemma D_15250 : decode_any W_15250 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_15254 : bv 32 := 0x17213023.
Lemma F_15254 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15300 : word) = Some W_15254.
Proof. vm_refl. Qed.
Lemma D_15254 : decode_any W_15254 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_15258 : bv 32 := 0x00058413.
Lemma F_15258 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15304 : word) = Some W_15258.
Proof. vm_refl. Qed.
Lemma D_15258 : decode_any W_15258 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1525c : bv 32 := 0x00050493.
Lemma F_1525c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15308 : word) = Some W_1525c.
Proof. vm_refl. Qed.
Lemma D_1525c : decode_any W_1525c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15260 : bv 32 := 0x03010513.
Lemma F_15260 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1530c : word) = Some W_15260.
Proof. vm_refl. Qed.
Lemma D_15260 : decode_any W_15260 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_15264 : bv 32 := 0x13000613.
Lemma F_15264 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15310 : word) = Some W_15264.
Proof. vm_refl. Qed.
Lemma D_15264 : decode_any W_15264 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_15268 : bv 32 := 0x00000593.
Lemma F_15268 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15314 : word) = Some W_15268.
Proof. vm_refl. Qed.
Lemma D_15268 : decode_any W_15268 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1526c : bv 32 := 0x5f1070ef.
Lemma F_1526c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15318 : word) = Some W_1526c.
Proof. vm_refl. Qed.
Lemma D_1526c : decode_any W_1526c = Some (Jal 1 32240, 4%Z).
Proof. vm_refl. Qed.

Definition W_15270 : bv 32 := 0x00009517.
Lemma F_15270 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1531c : word) = Some W_15270.
Proof. vm_refl. Qed.
Lemma D_15270 : decode_any W_15270 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15274 : bv 32 := 0x43c53503.
Lemma F_15274 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15320 : word) = Some W_15274.
Proof. vm_refl. Qed.
Lemma D_15274 : decode_any W_15274 = Some (Load SZ8 true 10 10 1084, 4%Z).
Proof. vm_refl. Qed.

Definition W_15278 : bv 32 := 0x00953023.
Lemma F_15278 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15324 : word) = Some W_15278.
Proof. vm_refl. Qed.
Lemma D_15278 : decode_any W_15278 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1527c : bv 32 := 0x0004b503.
Lemma F_1527c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15328 : word) = Some W_1527c.
Proof. vm_refl. Qed.
Lemma D_1527c : decode_any W_1527c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15280 : bv 32 := 0x00848493.
Lemma F_15280 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1532c : word) = Some W_15280.
Proof. vm_refl. Qed.
Lemma D_15280 : decode_any W_15280 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15284 : bv 32 := 0xfe051ce3.
Lemma F_15284 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15330 : word) = Some W_15284.
Proof. vm_refl. Qed.
Lemma D_15284 : decode_any W_15284 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_15288 : bv 32 := 0x0003b517.
Lemma F_15288 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15334 : word) = Some W_15288.
Proof. vm_refl. Qed.
Lemma D_15288 : decode_any W_15288 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_1528c : bv 32 := 0xa5c50913.
Lemma F_1528c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15338 : word) = Some W_1528c.
Proof. vm_refl. Qed.
Lemma D_1528c : decode_any W_1528c = Some (OpImm ALU_ADD 18 10 2652, 4%Z).
Proof. vm_refl. Qed.

Definition W_15290 : bv 32 := 0x00993423.
Lemma F_15290 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1533c : word) = Some W_15290.
Proof. vm_refl. Qed.
Lemma D_15290 : decode_any W_15290 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15294 : bv 32 := 0x0004b583.
Lemma F_15294 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15340 : word) = Some W_15294.
Proof. vm_refl. Qed.
Lemma D_15294 : decode_any W_15294 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15298 : bv 32 := 0x04058c63.
Lemma F_15298 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15344 : word) = Some W_15298.
Proof. vm_refl. Qed.
Lemma D_15298 : decode_any W_15298 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1529c : bv 32 := 0x01048493.
Lemma F_1529c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15348 : word) = Some W_1529c.
Proof. vm_refl. Qed.
Lemma D_1529c : decode_any W_1529c = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_152a0 : bv 32 := 0x02500513.
Lemma F_152a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1534c : word) = Some W_152a0.
Proof. vm_refl. Qed.
Lemma D_152a0 : decode_any W_152a0 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_152a4 : bv 32 := 0x03010613.
Lemma F_152a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15350 : word) = Some W_152a4.
Proof. vm_refl. Qed.
Lemma D_152a4 : decode_any W_152a4 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_152a8 : bv 32 := 0x0100006f.
Lemma F_152a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15354 : word) = Some W_152a8.
Proof. vm_refl. Qed.
Lemma D_152a8 : decode_any W_152a8 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_152ac : bv 32 := 0x0004b583.
Lemma F_152ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15358 : word) = Some W_152ac.
Proof. vm_refl. Qed.
Lemma D_152ac : decode_any W_152ac = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_152b0 : bv 32 := 0x01048493.
Lemma F_152b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1535c : word) = Some W_152b0.
Proof. vm_refl. Qed.
Lemma D_152b0 : decode_any W_152b0 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_152b4 : bv 32 := 0x00058e63.
Lemma F_152b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15360 : word) = Some W_152b4.
Proof. vm_refl. Qed.
Lemma D_152b4 : decode_any W_152b4 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_152b8 : bv 32 := 0xfeb56ae3.
Lemma F_152b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15364 : word) = Some W_152b8.
Proof. vm_refl. Qed.
Lemma D_152b8 : decode_any W_152b8 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_152bc : bv 32 := 0xff84b683.
Lemma F_152bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15368 : word) = Some W_152bc.
Proof. vm_refl. Qed.
Lemma D_152bc : decode_any W_152bc = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_152c0 : bv 32 := 0x00359593.
Lemma F_152c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1536c : word) = Some W_152c0.
Proof. vm_refl. Qed.
Lemma D_152c0 : decode_any W_152c0 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_152c4 : bv 32 := 0x00b605b3.
Lemma F_152c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15370 : word) = Some W_152c4.
Proof. vm_refl. Qed.
Lemma D_152c4 : decode_any W_152c4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_152c8 : bv 32 := 0x00d5b023.
Lemma F_152c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15374 : word) = Some W_152c8.
Proof. vm_refl. Qed.
Lemma D_152c8 : decode_any W_152c8 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_152cc : bv 32 := 0xfe1ff06f.
Lemma F_152cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15378 : word) = Some W_152cc.
Proof. vm_refl. Qed.
Lemma D_152cc : decode_any W_152cc = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_152d0 : bv 32 := 0x0b013583.
Lemma F_152d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1537c : word) = Some W_152d0.
Proof. vm_refl. Qed.
Lemma D_152d0 : decode_any W_152d0 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_152d4 : bv 32 := 0x13013503.
Lemma F_152d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15380 : word) = Some W_152d4.
Proof. vm_refl. Qed.
Lemma D_152d4 : decode_any W_152d4 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_152d8 : bv 32 := 0x0003b617.
Lemma F_152d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15384 : word) = Some W_152d8.
Proof. vm_refl. Qed.
Lemma D_152d8 : decode_any W_152d8 = Some (Auipc 12 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_152dc : bv 32 := 0xa6b63a23.
Lemma F_152dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15388 : word) = Some W_152dc.
Proof. vm_refl. Qed.
Lemma D_152dc : decode_any W_152dc = Some (Store SZ8 12 11 2676, 4%Z).
Proof. vm_refl. Qed.

Definition W_152e0 : bv 32 := 0x00050c63.
Lemma F_152e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1538c : word) = Some W_152e0.
Proof. vm_refl. Qed.
Lemma D_152e0 : decode_any W_152e0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_152e4 : bv 32 := 0x0003b597.
Lemma F_152e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15390 : word) = Some W_152e4.
Proof. vm_refl. Qed.
Lemma D_152e4 : decode_any W_152e4 = Some (Auipc 11 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_152e8 : bv 32 := 0x9ea5b423.
Lemma F_152e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15394 : word) = Some W_152e8.
Proof. vm_refl. Qed.
Lemma D_152e8 : decode_any W_152e8 = Some (Store SZ8 11 10 2536, 4%Z).
Proof. vm_refl. Qed.

Definition W_152ec : bv 32 := 0x00c0006f.
Lemma F_152ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15398 : word) = Some W_152ec.
Proof. vm_refl. Qed.
Lemma D_152ec : decode_any W_152ec = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_152f0 : bv 32 := 0x0003b517.
Lemma F_152f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1539c : word) = Some W_152f0.
Proof. vm_refl. Qed.
Lemma D_152f0 : decode_any W_152f0 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_152f4 : bv 32 := 0xa4053e23.
Lemma F_152f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153a0 : word) = Some W_152f4.
Proof. vm_refl. Qed.
Lemma D_152f4 : decode_any W_152f4 = Some (Store SZ8 10 0 2652, 4%Z).
Proof. vm_refl. Qed.

Definition W_152f8 : bv 32 := 0x06013503.
Lemma F_152f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153a4 : word) = Some W_152f8.
Proof. vm_refl. Qed.
Lemma D_152f8 : decode_any W_152f8 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_152fc : bv 32 := 0x02a93823.
Lemma F_152fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153a8 : word) = Some W_152fc.
Proof. vm_refl. Qed.
Lemma D_152fc : decode_any W_152fc = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_15300 : bv 32 := 0x00041463.
Lemma F_15300 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153ac : word) = Some W_15300.
Proof. vm_refl. Qed.
Lemma D_15300 : decode_any W_15300 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15304 : bv 32 := 0x12813403.
Lemma F_15304 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153b0 : word) = Some W_15304.
Proof. vm_refl. Qed.
Lemma D_15304 : decode_any W_15304 = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_15308 : bv 32 := 0x00041663.
Lemma F_15308 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153b4 : word) = Some W_15308.
Proof. vm_refl. Qed.
Lemma D_15308 : decode_any W_15308 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1530c : bv 32 := 0xffffb517.
Lemma F_1530c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153b8 : word) = Some W_1530c.
Proof. vm_refl. Qed.
Lemma D_1530c : decode_any W_1530c = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

Definition W_15310 : bv 32 := 0xfb850413.
Lemma F_15310 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153bc : word) = Some W_15310.
Proof. vm_refl. Qed.
Lemma D_15310 : decode_any W_15310 = Some (OpImm ALU_ADD 8 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_15314 : bv 32 := 0x00009517.
Lemma F_15314 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153c0 : word) = Some W_15314.
Proof. vm_refl. Qed.
Lemma D_15314 : decode_any W_15314 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15318 : bv 32 := 0x3a053583.
Lemma F_15318 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153c4 : word) = Some W_15318.
Proof. vm_refl. Qed.
Lemma D_15318 : decode_any W_15318 = Some (Load SZ8 true 11 10 928, 4%Z).
Proof. vm_refl. Qed.

Definition W_1531c : bv 32 := 0x00009517.
Lemma F_1531c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153c8 : word) = Some W_1531c.
Proof. vm_refl. Qed.
Lemma D_1531c : decode_any W_1531c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15320 : bv 32 := 0x3a053503.
Lemma F_15320 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153cc : word) = Some W_15320.
Proof. vm_refl. Qed.
Lemma D_15320 : decode_any W_15320 = Some (Load SZ8 true 10 10 928, 4%Z).
Proof. vm_refl. Qed.

Definition W_15324 : bv 32 := 0x0085b023.
Lemma F_15324 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153d0 : word) = Some W_15324.
Proof. vm_refl. Qed.
Lemma D_15324 : decode_any W_15324 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15328 : bv 32 := 0x00140593.
Lemma F_15328 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153d4 : word) = Some W_15328.
Proof. vm_refl. Qed.
Lemma D_15328 : decode_any W_15328 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1532c : bv 32 := 0x00853023.
Lemma F_1532c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153d8 : word) = Some W_1532c.
Proof. vm_refl. Qed.
Lemma D_1532c : decode_any W_1532c = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15330 : bv 32 := 0x02f00613.
Lemma F_15330 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153dc : word) = Some W_15330.
Proof. vm_refl. Qed.
Lemma D_15330 : decode_any W_15330 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_15334 : bv 32 := 0x00c0006f.
Lemma F_15334 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153e0 : word) = Some W_15334.
Proof. vm_refl. Qed.
Lemma D_15334 : decode_any W_15334 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15338 : bv 32 := 0x00b53023.
Lemma F_15338 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153e4 : word) = Some W_15338.
Proof. vm_refl. Qed.
Lemma D_15338 : decode_any W_15338 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1533c : bv 32 := 0x00158593.
Lemma F_1533c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153e8 : word) = Some W_1533c.
Proof. vm_refl. Qed.
Lemma D_1533c : decode_any W_1533c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15340 : bv 32 := 0xfff5c683.
Lemma F_15340 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153ec : word) = Some W_15340.
Proof. vm_refl. Qed.
Lemma D_15340 : decode_any W_15340 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_15344 : bv 32 := 0xfec68ae3.
Lemma F_15344 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153f0 : word) = Some W_15344.
Proof. vm_refl. Qed.
Lemma D_15344 : decode_any W_15344 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_15348 : bv 32 := 0xfe069ae3.
Lemma F_15348 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153f4 : word) = Some W_15348.
Proof. vm_refl. Qed.
Lemma D_15348 : decode_any W_15348 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1534c : bv 32 := 0x03010513.
Lemma F_1534c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153f8 : word) = Some W_1534c.
Proof. vm_refl. Qed.
Lemma D_1534c : decode_any W_1534c = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_15350 : bv 32 := 0x214000ef.
Lemma F_15350 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x153fc : word) = Some W_15350.
Proof. vm_refl. Qed.
Lemma D_15350 : decode_any W_15350 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_15354 : bv 32 := 0x0f813503.
Lemma F_15354 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15400 : word) = Some W_15354.
Proof. vm_refl. Qed.
Lemma D_15354 : decode_any W_15354 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_15358 : bv 32 := 0x0d9000ef.
Lemma F_15358 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15404 : word) = Some W_15358.
Proof. vm_refl. Qed.
Lemma D_15358 : decode_any W_15358 = Some (Jal 1 2264, 4%Z).
Proof. vm_refl. Qed.

Definition W_1535c : bv 32 := 0x08813503.
Lemma F_1535c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15408 : word) = Some W_1535c.
Proof. vm_refl. Qed.
Lemma D_1535c : decode_any W_1535c = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_15360 : bv 32 := 0x09013583.
Lemma F_15360 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1540c : word) = Some W_15360.
Proof. vm_refl. Qed.
Lemma D_15360 : decode_any W_15360 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_15364 : bv 32 := 0x00b51c63.
Lemma F_15364 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15410 : word) = Some W_15364.
Proof. vm_refl. Qed.
Lemma D_15364 : decode_any W_15364 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15368 : bv 32 := 0x09813503.
Lemma F_15368 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15414 : word) = Some W_15368.
Proof. vm_refl. Qed.
Lemma D_15368 : decode_any W_15368 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_1536c : bv 32 := 0x0a013583.
Lemma F_1536c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15418 : word) = Some W_1536c.
Proof. vm_refl. Qed.
Lemma D_1536c : decode_any W_1536c = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_15370 : bv 32 := 0x00b51663.
Lemma F_15370 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1541c : word) = Some W_15370.
Proof. vm_refl. Qed.
Lemma D_15370 : decode_any W_15370 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15374 : bv 32 := 0x0e813503.
Lemma F_15374 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15420 : word) = Some W_15374.
Proof. vm_refl. Qed.
Lemma D_15374 : decode_any W_15374 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_15378 : bv 32 := 0x0e050063.
Lemma F_15378 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15424 : word) = Some W_15378.
Proof. vm_refl. Qed.
Lemma D_15378 : decode_any W_15378 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_1537c : bv 32 := 0x00200693.
Lemma F_1537c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15428 : word) = Some W_1537c.
Proof. vm_refl. Qed.
Lemma D_1537c : decode_any W_1537c = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_15380 : bv 32 := 0x00100793.
Lemma F_15380 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1542c : word) = Some W_15380.
Proof. vm_refl. Qed.
Lemma D_15380 : decode_any W_15380 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15384 : bv 32 := 0x00013423.
Lemma F_15384 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15430 : word) = Some W_15384.
Proof. vm_refl. Qed.
Lemma D_15384 : decode_any W_15384 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15388 : bv 32 := 0x00013823.
Lemma F_15388 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15434 : word) = Some W_15388.
Proof. vm_refl. Qed.
Lemma D_15388 : decode_any W_15388 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1538c : bv 32 := 0x04900893.
Lemma F_1538c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15438 : word) = Some W_1538c.
Proof. vm_refl. Qed.
Lemma D_1538c : decode_any W_1538c = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_15390 : bv 32 := 0x01810513.
Lemma F_15390 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1543c : word) = Some W_15390.
Proof. vm_refl. Qed.
Lemma D_15390 : decode_any W_15390 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15394 : bv 32 := 0x00300593.
Lemma F_15394 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15440 : word) = Some W_15394.
Proof. vm_refl. Qed.
Lemma D_15394 : decode_any W_15394 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_15398 : bv 32 := 0x00810613.
Lemma F_15398 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15444 : word) = Some W_15398.
Proof. vm_refl. Qed.
Lemma D_15398 : decode_any W_15398 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1539c : bv 32 := 0x00800713.
Lemma F_1539c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15448 : word) = Some W_1539c.
Proof. vm_refl. Qed.
Lemma D_1539c : decode_any W_1539c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_153a0 : bv 32 := 0x00013c23.
Lemma F_153a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1544c : word) = Some W_153a0.
Proof. vm_refl. Qed.
Lemma D_153a0 : decode_any W_153a0 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_153a4 : bv 32 := 0x02f13023.
Lemma F_153a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15450 : word) = Some W_153a4.
Proof. vm_refl. Qed.
Lemma D_153a4 : decode_any W_153a4 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_153a8 : bv 32 := 0x02d13423.
Lemma F_153a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15454 : word) = Some W_153a8.
Proof. vm_refl. Qed.
Lemma D_153a8 : decode_any W_153a8 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_153ac : bv 32 := 0x00000693.
Lemma F_153ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15458 : word) = Some W_153ac.
Proof. vm_refl. Qed.
Lemma D_153ac : decode_any W_153ac = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_153b0 : bv 32 := 0x00000073.
Lemma F_153b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1545c : word) = Some W_153b0.
Proof. vm_refl. Qed.
Lemma D_153b0 : decode_any W_153b0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_153b0 : is_ecall W_153b0 = true.
Proof. reflexivity. Qed.

Definition W_153b4 : bv 32 := 0x02051513.
Lemma F_153b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15460 : word) = Some W_153b4.
Proof. vm_refl. Qed.
Lemma D_153b4 : decode_any W_153b4 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_153b8 : bv 32 := 0x00055463.
Lemma F_153b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15464 : word) = Some W_153b8.
Proof. vm_refl. Qed.
Lemma D_153b8 : decode_any W_153b8 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_153bc : bv 32 := 0x00000023.
Lemma F_153bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15468 : word) = Some W_153bc.
Proof. vm_refl. Qed.
Lemma D_153bc : decode_any W_153bc = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_153c0 : bv 32 := 0x01e15503.
Lemma F_153c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1546c : word) = Some W_153c0.
Proof. vm_refl. Qed.
Lemma D_153c0 : decode_any W_153c0 = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_153c4 : bv 32 := 0x02057513.
Lemma F_153c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15470 : word) = Some W_153c4.
Proof. vm_refl. Qed.
Lemma D_153c4 : decode_any W_153c4 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_153c8 : bv 32 := 0x02050463.
Lemma F_153c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15474 : word) = Some W_153c8.
Proof. vm_refl. Qed.
Lemma D_153c8 : decode_any W_153c8 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_153cc : bv 32 := 0xffffb517.
Lemma F_153cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15478 : word) = Some W_153cc.
Proof. vm_refl. Qed.
Lemma D_153cc : decode_any W_153cc = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

Definition W_153d0 : bv 32 := 0x00008637.
Lemma F_153d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1547c : word) = Some W_153d0.
Proof. vm_refl. Qed.
Lemma D_153d0 : decode_any W_153d0 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_153d4 : bv 32 := 0x03800893.
Lemma F_153d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15480 : word) = Some W_153d4.
Proof. vm_refl. Qed.
Lemma D_153d4 : decode_any W_153d4 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_153d8 : bv 32 := 0x0c950593.
Lemma F_153d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15484 : word) = Some W_153d8.
Proof. vm_refl. Qed.
Lemma D_153d8 : decode_any W_153d8 = Some (OpImm ALU_ADD 11 10 201, 4%Z).
Proof. vm_refl. Qed.

Definition W_153dc : bv 32 := 0x0026061b.
Lemma F_153dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15488 : word) = Some W_153dc.
Proof. vm_refl. Qed.
Lemma D_153dc : decode_any W_153dc = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_153e0 : bv 32 := 0xf9c00513.
Lemma F_153e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1548c : word) = Some W_153e0.
Proof. vm_refl. Qed.
Lemma D_153e0 : decode_any W_153e0 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_153e4 : bv 32 := 0x00000073.
Lemma F_153e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15490 : word) = Some W_153e4.
Proof. vm_refl. Qed.
Lemma D_153e4 : decode_any W_153e4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_153e4 : is_ecall W_153e4 = true.
Proof. reflexivity. Qed.

Definition W_153e8 : bv 32 := 0x00055463.
Lemma F_153e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15494 : word) = Some W_153e8.
Proof. vm_refl. Qed.
Lemma D_153e8 : decode_any W_153e8 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_153ec : bv 32 := 0x00000023.
Lemma F_153ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15498 : word) = Some W_153ec.
Proof. vm_refl. Qed.
Lemma D_153ec : decode_any W_153ec = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_153f0 : bv 32 := 0x02615503.
Lemma F_153f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1549c : word) = Some W_153f0.
Proof. vm_refl. Qed.
Lemma D_153f0 : decode_any W_153f0 = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

Definition W_153f4 : bv 32 := 0x02057513.
Lemma F_153f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154a0 : word) = Some W_153f4.
Proof. vm_refl. Qed.
Lemma D_153f4 : decode_any W_153f4 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_153f8 : bv 32 := 0x02050463.
Lemma F_153f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154a4 : word) = Some W_153f8.
Proof. vm_refl. Qed.
Lemma D_153f8 : decode_any W_153f8 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_153fc : bv 32 := 0xffffb517.
Lemma F_153fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154a8 : word) = Some W_153fc.
Proof. vm_refl. Qed.
Lemma D_153fc : decode_any W_153fc = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

Definition W_15400 : bv 32 := 0x00008637.
Lemma F_15400 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154ac : word) = Some W_15400.
Proof. vm_refl. Qed.
Lemma D_15400 : decode_any W_15400 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15404 : bv 32 := 0x03800893.
Lemma F_15404 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154b0 : word) = Some W_15404.
Proof. vm_refl. Qed.
Lemma D_15404 : decode_any W_15404 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_15408 : bv 32 := 0x09950593.
Lemma F_15408 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154b4 : word) = Some W_15408.
Proof. vm_refl. Qed.
Lemma D_15408 : decode_any W_15408 = Some (OpImm ALU_ADD 11 10 153, 4%Z).
Proof. vm_refl. Qed.

Definition W_1540c : bv 32 := 0x0026061b.
Lemma F_1540c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154b8 : word) = Some W_1540c.
Proof. vm_refl. Qed.
Lemma D_1540c : decode_any W_1540c = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_15410 : bv 32 := 0xf9c00513.
Lemma F_15410 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154bc : word) = Some W_15410.
Proof. vm_refl. Qed.
Lemma D_15410 : decode_any W_15410 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_15414 : bv 32 := 0x00000073.
Lemma F_15414 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154c0 : word) = Some W_15414.
Proof. vm_refl. Qed.
Lemma D_15414 : decode_any W_15414 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_15414 : is_ecall W_15414 = true.
Proof. reflexivity. Qed.

Definition W_15418 : bv 32 := 0x00055463.
Lemma F_15418 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154c4 : word) = Some W_15418.
Proof. vm_refl. Qed.
Lemma D_15418 : decode_any W_15418 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1541c : bv 32 := 0x00000023.
Lemma F_1541c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154c8 : word) = Some W_1541c.
Proof. vm_refl. Qed.
Lemma D_1541c : decode_any W_1541c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15420 : bv 32 := 0x02e15503.
Lemma F_15420 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154cc : word) = Some W_15420.
Proof. vm_refl. Qed.
Lemma D_15420 : decode_any W_15420 = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

Definition W_15424 : bv 32 := 0x02057513.
Lemma F_15424 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154d0 : word) = Some W_15424.
Proof. vm_refl. Qed.
Lemma D_15424 : decode_any W_15424 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15428 : bv 32 := 0x02050463.
Lemma F_15428 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154d4 : word) = Some W_15428.
Proof. vm_refl. Qed.
Lemma D_15428 : decode_any W_15428 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1542c : bv 32 := 0xffffb517.
Lemma F_1542c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154d8 : word) = Some W_1542c.
Proof. vm_refl. Qed.
Lemma D_1542c : decode_any W_1542c = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

Definition W_15430 : bv 32 := 0x00008637.
Lemma F_15430 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154dc : word) = Some W_15430.
Proof. vm_refl. Qed.
Lemma D_15430 : decode_any W_15430 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15434 : bv 32 := 0x03800893.
Lemma F_15434 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154e0 : word) = Some W_15434.
Proof. vm_refl. Qed.
Lemma D_15434 : decode_any W_15434 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_15438 : bv 32 := 0x06950593.
Lemma F_15438 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154e4 : word) = Some W_15438.
Proof. vm_refl. Qed.
Lemma D_15438 : decode_any W_15438 = Some (OpImm ALU_ADD 11 10 105, 4%Z).
Proof. vm_refl. Qed.

Definition W_1543c : bv 32 := 0x0026061b.
Lemma F_1543c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154e8 : word) = Some W_1543c.
Proof. vm_refl. Qed.
Lemma D_1543c : decode_any W_1543c = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_15440 : bv 32 := 0xf9c00513.
Lemma F_15440 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154ec : word) = Some W_15440.
Proof. vm_refl. Qed.
Lemma D_15440 : decode_any W_15440 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_15444 : bv 32 := 0x00000073.
Lemma F_15444 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154f0 : word) = Some W_15444.
Proof. vm_refl. Qed.
Lemma D_15444 : decode_any W_15444 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_15444 : is_ecall W_15444 = true.
Proof. reflexivity. Qed.

Definition W_15448 : bv 32 := 0x00055463.
Lemma F_15448 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154f4 : word) = Some W_15448.
Proof. vm_refl. Qed.
Lemma D_15448 : decode_any W_15448 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1544c : bv 32 := 0x00000023.
Lemma F_1544c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154f8 : word) = Some W_1544c.
Proof. vm_refl. Qed.
Lemma D_1544c : decode_any W_1544c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15450 : bv 32 := 0x00100513.
Lemma F_15450 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x154fc : word) = Some W_15450.
Proof. vm_refl. Qed.
Lemma D_15450 : decode_any W_15450 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15454 : bv 32 := 0x00a90123.
Lemma F_15454 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15500 : word) = Some W_15454.
Proof. vm_refl. Qed.
Lemma D_15454 : decode_any W_15454 = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_15458 : bv 32 := 0x17813083.
Lemma F_15458 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15504 : word) = Some W_15458.
Proof. vm_refl. Qed.
Lemma D_15458 : decode_any W_15458 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_1545c : bv 32 := 0x17013403.
Lemma F_1545c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15508 : word) = Some W_1545c.
Proof. vm_refl. Qed.
Lemma D_1545c : decode_any W_1545c = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_15460 : bv 32 := 0x16813483.
Lemma F_15460 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1550c : word) = Some W_15460.
Proof. vm_refl. Qed.
Lemma D_15460 : decode_any W_15460 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_15464 : bv 32 := 0x16013903.
Lemma F_15464 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15510 : word) = Some W_15464.
Proof. vm_refl. Qed.
Lemma D_15464 : decode_any W_15464 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_15468 : bv 32 := 0x18010113.
Lemma F_15468 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15514 : word) = Some W_15468.
Proof. vm_refl. Qed.
Lemma D_15468 : decode_any W_15468 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_1546c : bv 32 := 0x00008067.
Lemma F_1546c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15518 : word) = Some W_1546c.
Proof. vm_refl. Qed.
Lemma D_1546c : decode_any W_1546c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15470 : bv 32 := 0xfe010113.
Lemma F_15470 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1551c : word) = Some W_15470.
Proof. vm_refl. Qed.
Lemma D_15470 : decode_any W_15470 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_15474 : bv 32 := 0x00113c23.
Lemma F_15474 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15520 : word) = Some W_15474.
Proof. vm_refl. Qed.
Lemma D_15474 : decode_any W_15474 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15478 : bv 32 := 0x00813823.
Lemma F_15478 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15524 : word) = Some W_15478.
Proof. vm_refl. Qed.
Lemma D_15478 : decode_any W_15478 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1547c : bv 32 := 0x00913423.
Lemma F_1547c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15528 : word) = Some W_1547c.
Proof. vm_refl. Qed.
Lemma D_1547c : decode_any W_1547c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15480 : bv 32 := 0xdc1ff0ef.
Lemma F_15480 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1552c : word) = Some W_15480.
Proof. vm_refl. Qed.
Lemma D_15480 : decode_any W_15480 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_15484 : bv 32 := 0x00009517.
Lemma F_15484 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15530 : word) = Some W_15484.
Proof. vm_refl. Qed.
Lemma D_15484 : decode_any W_15484 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15488 : bv 32 := 0x00009597.
Lemma F_15488 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15534 : word) = Some W_15488.
Proof. vm_refl. Qed.
Lemma D_15488 : decode_any W_15488 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1548c : bv 32 := 0x24053403.
Lemma F_1548c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15538 : word) = Some W_1548c.
Proof. vm_refl. Qed.
Lemma D_1548c : decode_any W_1548c = Some (Load SZ8 true 8 10 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_15490 : bv 32 := 0x2445b483.
Lemma F_15490 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1553c : word) = Some W_15490.
Proof. vm_refl. Qed.
Lemma D_15490 : decode_any W_15490 = Some (Load SZ8 true 9 11 580, 4%Z).
Proof. vm_refl. Qed.

Definition W_15494 : bv 32 := 0x0084fa63.
Lemma F_15494 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15540 : word) = Some W_15494.
Proof. vm_refl. Qed.
Lemma D_15494 : decode_any W_15494 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_15498 : bv 32 := 0x0004b503.
Lemma F_15498 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15544 : word) = Some W_15498.
Proof. vm_refl. Qed.
Lemma D_15498 : decode_any W_15498 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1549c : bv 32 := 0x000500e7.
Lemma F_1549c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15548 : word) = Some W_1549c.
Proof. vm_refl. Qed.
Lemma D_1549c : decode_any W_1549c = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154a0 : bv 32 := 0x00848493.
Lemma F_154a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1554c : word) = Some W_154a0.
Proof. vm_refl. Qed.
Lemma D_154a0 : decode_any W_154a0 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_154a4 : bv 32 := 0xfe84eae3.
Lemma F_154a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15550 : word) = Some W_154a4.
Proof. vm_refl. Qed.
Lemma D_154a4 : decode_any W_154a4 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_154a8 : bv 32 := 0x01813083.
Lemma F_154a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15554 : word) = Some W_154a8.
Proof. vm_refl. Qed.
Lemma D_154a8 : decode_any W_154a8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_154ac : bv 32 := 0x01013403.
Lemma F_154ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15558 : word) = Some W_154ac.
Proof. vm_refl. Qed.
Lemma D_154ac : decode_any W_154ac = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_154b0 : bv 32 := 0x00813483.
Lemma F_154b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1555c : word) = Some W_154b0.
Proof. vm_refl. Qed.
Lemma D_154b0 : decode_any W_154b0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_154b4 : bv 32 := 0x02010113.
Lemma F_154b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15560 : word) = Some W_154b4.
Proof. vm_refl. Qed.
Lemma D_154b4 : decode_any W_154b4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_154b8 : bv 32 := 0x00008067.
Lemma F_154b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15564 : word) = Some W_154b8.
Proof. vm_refl. Qed.
Lemma D_154b8 : decode_any W_154b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154bc : bv 32 := 0xfe010113.
Lemma F_154bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15568 : word) = Some W_154bc.
Proof. vm_refl. Qed.
Lemma D_154bc : decode_any W_154bc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_154c0 : bv 32 := 0x00113c23.
Lemma F_154c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1556c : word) = Some W_154c0.
Proof. vm_refl. Qed.
Lemma D_154c0 : decode_any W_154c0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_154c4 : bv 32 := 0x00813823.
Lemma F_154c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15570 : word) = Some W_154c4.
Proof. vm_refl. Qed.
Lemma D_154c4 : decode_any W_154c4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_154c8 : bv 32 := 0x00913423.
Lemma F_154c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15574 : word) = Some W_154c8.
Proof. vm_refl. Qed.
Lemma D_154c8 : decode_any W_154c8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_154cc : bv 32 := 0x01213023.
Lemma F_154cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15578 : word) = Some W_154cc.
Proof. vm_refl. Qed.
Lemma D_154cc : decode_any W_154cc = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154d0 : bv 32 := 0x00060413.
Lemma F_154d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1557c : word) = Some W_154d0.
Proof. vm_refl. Qed.
Lemma D_154d0 : decode_any W_154d0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154d4 : bv 32 := 0x00058493.
Lemma F_154d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15580 : word) = Some W_154d4.
Proof. vm_refl. Qed.
Lemma D_154d4 : decode_any W_154d4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154d8 : bv 32 := 0x00050913.
Lemma F_154d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15584 : word) = Some W_154d8.
Proof. vm_refl. Qed.
Lemma D_154d8 : decode_any W_154d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154dc : bv 32 := 0x00063583.
Lemma F_154dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15588 : word) = Some W_154dc.
Proof. vm_refl. Qed.
Lemma D_154dc : decode_any W_154dc = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154e0 : bv 32 := 0x00349513.
Lemma F_154e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1558c : word) = Some W_154e0.
Proof. vm_refl. Qed.
Lemma D_154e0 : decode_any W_154e0 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_154e4 : bv 32 := 0x00a60533.
Lemma F_154e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15590 : word) = Some W_154e4.
Proof. vm_refl. Qed.
Lemma D_154e4 : decode_any W_154e4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_154e8 : bv 32 := 0x00850513.
Lemma F_154e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15594 : word) = Some W_154e8.
Proof. vm_refl. Qed.
Lemma D_154e8 : decode_any W_154e8 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_154ec : bv 32 := 0xd59ff0ef.
Lemma F_154ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15598 : word) = Some W_154ec.
Proof. vm_refl. Qed.
Lemma D_154ec : decode_any W_154ec = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_154f0 : bv 32 := 0x00000517.
Lemma F_154f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1559c : word) = Some W_154f0.
Proof. vm_refl. Qed.
Lemma D_154f0 : decode_any W_154f0 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154f4 : bv 32 := 0x02c50313.
Lemma F_154f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155a0 : word) = Some W_154f4.
Proof. vm_refl. Qed.
Lemma D_154f4 : decode_any W_154f4 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_154f8 : bv 32 := 0x00090513.
Lemma F_154f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155a4 : word) = Some W_154f8.
Proof. vm_refl. Qed.
Lemma D_154f8 : decode_any W_154f8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154fc : bv 32 := 0x00048593.
Lemma F_154fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155a8 : word) = Some W_154fc.
Proof. vm_refl. Qed.
Lemma D_154fc : decode_any W_154fc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15500 : bv 32 := 0x00040613.
Lemma F_15500 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155ac : word) = Some W_15500.
Proof. vm_refl. Qed.
Lemma D_15500 : decode_any W_15500 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15504 : bv 32 := 0x01813083.
Lemma F_15504 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155b0 : word) = Some W_15504.
Proof. vm_refl. Qed.
Lemma D_15504 : decode_any W_15504 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15508 : bv 32 := 0x01013403.
Lemma F_15508 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155b4 : word) = Some W_15508.
Proof. vm_refl. Qed.
Lemma D_15508 : decode_any W_15508 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1550c : bv 32 := 0x00813483.
Lemma F_1550c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155b8 : word) = Some W_1550c.
Proof. vm_refl. Qed.
Lemma D_1550c : decode_any W_1550c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15510 : bv 32 := 0x00013903.
Lemma F_15510 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155bc : word) = Some W_15510.
Proof. vm_refl. Qed.
Lemma D_15510 : decode_any W_15510 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15514 : bv 32 := 0x02010113.
Lemma F_15514 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155c0 : word) = Some W_15514.
Proof. vm_refl. Qed.
Lemma D_15514 : decode_any W_15514 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15518 : bv 32 := 0x00030067.
Lemma F_15518 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155c4 : word) = Some W_15518.
Proof. vm_refl. Qed.
Lemma D_15518 : decode_any W_15518 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1551c : bv 32 := 0xfd010113.
Lemma F_1551c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155c8 : word) = Some W_1551c.
Proof. vm_refl. Qed.
Lemma D_1551c : decode_any W_1551c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_15520 : bv 32 := 0x02113423.
Lemma F_15520 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155cc : word) = Some W_15520.
Proof. vm_refl. Qed.
Lemma D_15520 : decode_any W_15520 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15524 : bv 32 := 0x02813023.
Lemma F_15524 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155d0 : word) = Some W_15524.
Proof. vm_refl. Qed.
Lemma D_15524 : decode_any W_15524 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15528 : bv 32 := 0x00913c23.
Lemma F_15528 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155d4 : word) = Some W_15528.
Proof. vm_refl. Qed.
Lemma D_15528 : decode_any W_15528 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1552c : bv 32 := 0x01213823.
Lemma F_1552c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155d8 : word) = Some W_1552c.
Proof. vm_refl. Qed.
Lemma D_1552c : decode_any W_1552c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15530 : bv 32 := 0x01313423.
Lemma F_15530 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155dc : word) = Some W_15530.
Proof. vm_refl. Qed.
Lemma D_15530 : decode_any W_15530 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15534 : bv 32 := 0x00060413.
Lemma F_15534 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155e0 : word) = Some W_15534.
Proof. vm_refl. Qed.
Lemma D_15534 : decode_any W_15534 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15538 : bv 32 := 0x00058493.
Lemma F_15538 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155e4 : word) = Some W_15538.
Proof. vm_refl. Qed.
Lemma D_15538 : decode_any W_15538 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1553c : bv 32 := 0x00050913.
Lemma F_1553c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155e8 : word) = Some W_1553c.
Proof. vm_refl. Qed.
Lemma D_1553c : decode_any W_1553c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15540 : bv 32 := 0x00359513.
Lemma F_15540 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155ec : word) = Some W_15540.
Proof. vm_refl. Qed.
Lemma D_15540 : decode_any W_15540 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_15544 : bv 32 := 0x00a60533.
Lemma F_15544 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155f0 : word) = Some W_15544.
Proof. vm_refl. Qed.
Lemma D_15544 : decode_any W_15544 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_15548 : bv 32 := 0x00850993.
Lemma F_15548 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155f4 : word) = Some W_15548.
Proof. vm_refl. Qed.
Lemma D_15548 : decode_any W_15548 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1554c : bv 32 := 0xf25ff0ef.
Lemma F_1554c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155f8 : word) = Some W_1554c.
Proof. vm_refl. Qed.
Lemma D_1554c : decode_any W_1554c = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_15550 : bv 32 := 0x00048513.
Lemma F_15550 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x155fc : word) = Some W_15550.
Proof. vm_refl. Qed.
Lemma D_15550 : decode_any W_15550 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15554 : bv 32 := 0x00040593.
Lemma F_15554 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15600 : word) = Some W_15554.
Proof. vm_refl. Qed.
Lemma D_15554 : decode_any W_15554 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15558 : bv 32 := 0x00098613.
Lemma F_15558 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15604 : word) = Some W_15558.
Proof. vm_refl. Qed.
Lemma D_15558 : decode_any W_15558 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1555c : bv 32 := 0x000900e7.
Lemma F_1555c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15608 : word) = Some W_1555c.
Proof. vm_refl. Qed.
Lemma D_1555c : decode_any W_1555c = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15560 : bv 32 := 0x578000ef.
Lemma F_15560 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1560c : word) = Some W_15560.
Proof. vm_refl. Qed.
Lemma D_15560 : decode_any W_15560 = Some (Jal 1 1400, 4%Z).
Proof. vm_refl. Qed.

Definition W_15564 : bv 32 := 0xfc010113.
Lemma F_15564 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15610 : word) = Some W_15564.
Proof. vm_refl. Qed.
Lemma D_15564 : decode_any W_15564 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15614 : bv 32 := 0x02113c23.
Lemma TF_15614 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15614 : word) = Some TW_15614.
Proof. vm_refl. Qed.
Lemma TD_15614 : decode_any TW_15614 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15618 : bv 32 := 0x02813823.
Lemma TF_15618 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15618 : word) = Some TW_15618.
Proof. vm_refl. Qed.
Lemma TD_15618 : decode_any TW_15618 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1561c : bv 32 := 0x02913423.
Lemma TF_1561c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1561c : word) = Some TW_1561c.
Proof. vm_refl. Qed.
Lemma TD_1561c : decode_any TW_1561c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15620 : bv 32 := 0x03213023.
Lemma TF_15620 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15620 : word) = Some TW_15620.
Proof. vm_refl. Qed.
Lemma TD_15620 : decode_any TW_15620 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15624 : bv 32 := 0x01313c23.
Lemma TF_15624 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15624 : word) = Some TW_15624.
Proof. vm_refl. Qed.
Lemma TD_15624 : decode_any TW_15624 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15628 : bv 32 := 0x01413823.
Lemma TF_15628 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15628 : word) = Some TW_15628.
Proof. vm_refl. Qed.
Lemma TD_15628 : decode_any TW_15628 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1562c : bv 32 := 0x01513423.
Lemma TF_1562c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1562c : word) = Some TW_1562c.
Proof. vm_refl. Qed.
Lemma TD_1562c : decode_any TW_1562c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15630 : bv 32 := 0x02853683.
Lemma TF_15630 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15630 : word) = Some TW_15630.
Proof. vm_refl. Qed.
Lemma TD_15630 : decode_any TW_15630 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15634 : bv 32 := 0x0003a597.
Lemma TF_15634 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15634 : word) = Some TW_15634.
Proof. vm_refl. Qed.
Lemma TD_15634 : decode_any TW_15634 = Some (Auipc 11 58, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15638 : bv 32 := 0x4d458593.
Lemma TF_15638 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15638 : word) = Some TW_15638.
Proof. vm_refl. Qed.
Lemma TD_15638 : decode_any TW_15638 = Some (OpImm ALU_ADD 11 11 1236, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1563c : bv 32 := 0x0003a617.
Lemma TF_1563c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1563c : word) = Some TW_1563c.
Proof. vm_refl. Qed.
Lemma TD_1563c : decode_any TW_1563c = Some (Auipc 12 58, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15640 : bv 32 := 0x75460493.
Lemma TF_15640 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15640 : word) = Some TW_15640.
Proof. vm_refl. Qed.
Lemma TD_15640 : decode_any TW_15640 = Some (OpImm ALU_ADD 9 12 1876, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15644 : bv 32 := 0x0c068e63.
Lemma TF_15644 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15644 : word) = Some TW_15644.
Proof. vm_refl. Qed.
Lemma TD_15644 : decode_any TW_15644 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15648 : bv 32 := 0x00000613.
Lemma TF_15648 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15648 : word) = Some TW_15648.
Proof. vm_refl. Qed.
Lemma TD_15648 : decode_any TW_15648 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1564c : bv 32 := 0x00000893.
Lemma TF_1564c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1564c : word) = Some TW_1564c.
Proof. vm_refl. Qed.
Lemma TD_1564c : decode_any TW_1564c = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15650 : bv 32 := 0x0000a717.
Lemma TF_15650 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15650 : word) = Some TW_15650.
Proof. vm_refl. Qed.
Lemma TD_15650 : decode_any TW_15650 = Some (Auipc 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15654 : bv 32 := 0x01853783.
Lemma TF_15654 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15654 : word) = Some TW_15654.
Proof. vm_refl. Qed.
Lemma TD_15654 : decode_any TW_15654 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15658 : bv 32 := 0x02053503.
Lemma TF_15658 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15658 : word) = Some TW_15658.
Proof. vm_refl. Qed.
Lemma TD_15658 : decode_any TW_15658 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1565c : bv 32 := 0x00600813.
Lemma TF_1565c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1565c : word) = Some TW_1565c.
Proof. vm_refl. Qed.
Lemma TD_1565c : decode_any TW_1565c = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15660 : bv 32 := 0x00009297.
Lemma TF_15660 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15660 : word) = Some TW_15660.
Proof. vm_refl. Qed.
Lemma TD_15660 : decode_any TW_15660 = Some (Auipc 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15664 : bv 32 := 0x35076f03.
Lemma TF_15664 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15664 : word) = Some TW_15664.
Proof. vm_refl. Qed.
Lemma TD_15664 : decode_any TW_15664 = Some (Load SZ4 false 30 14 848, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15668 : bv 32 := 0x0a82b283.
Lemma TF_15668 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15668 : word) = Some TW_15668.
Proof. vm_refl. Qed.
Lemma TD_15668 : decode_any TW_15668 = Some (Load SZ8 true 5 5 168, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1566c : bv 32 := 0x00200313.
Lemma TF_1566c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1566c : word) = Some TW_1566c.
Proof. vm_refl. Qed.
Lemma TD_1566c : decode_any TW_1566c = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15670 : bv 32 := 0x00700393.
Lemma TF_15670 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15670 : word) = Some TW_15670.
Proof. vm_refl. Qed.
Lemma TD_15670 : decode_any TW_15670 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15674 : bv 32 := 0x6474ee37.
Lemma TF_15674 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15674 : word) = Some TW_15674.
Proof. vm_refl. Qed.
Lemma TD_15674 : decode_any TW_15674 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15678 : bv 32 := 0x551e0e1b.
Lemma TF_15678 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15678 : word) = Some TW_15678.
Proof. vm_refl. Qed.
Lemma TD_15678 : decode_any TW_15678 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1567c : bv 32 := 0x00078e93.
Lemma TF_1567c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1567c : word) = Some TW_1567c.
Proof. vm_refl. Qed.
Lemma TD_1567c : decode_any TW_1567c = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15680 : bv 32 := 0x0180006f.
Lemma TF_15680 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15680 : word) = Some TW_15680.
Proof. vm_refl. Qed.
Lemma TD_15680 : decode_any TW_15680 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15684 : bv 32 := 0x010eb603.
Lemma TF_15684 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15684 : word) = Some TW_15684.
Proof. vm_refl. Qed.
Lemma TD_15684 : decode_any TW_15684 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15688 : bv 32 := 0x40c78633.
Lemma TF_15688 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15688 : word) = Some TW_15688.
Proof. vm_refl. Qed.
Lemma TD_15688 : decode_any TW_15688 = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1568c : bv 32 := 0xfff68693.
Lemma TF_1568c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1568c : word) = Some TW_1568c.
Proof. vm_refl. Qed.
Lemma TD_1568c : decode_any TW_1568c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15690 : bv 32 := 0x00ae8eb3.
Lemma TF_15690 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15690 : word) = Some TW_15690.
Proof. vm_refl. Qed.
Lemma TD_15690 : decode_any TW_15690 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15694 : bv 32 := 0x04068a63.
Lemma TF_15694 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15694 : word) = Some TW_15694.
Proof. vm_refl. Qed.
Lemma TD_15694 : decode_any TW_15694 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15698 : bv 32 := 0x000ea403.
Lemma TF_15698 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15698 : word) = Some TW_15698.
Proof. vm_refl. Qed.
Lemma TD_15698 : decode_any TW_15698 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1569c : bv 32 := 0xff0404e3.
Lemma TF_1569c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1569c : word) = Some TW_1569c.
Proof. vm_refl. Qed.
Lemma TD_1569c : decode_any TW_1569c = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156a0 : bv 32 := 0x00028a63.
Lemma TF_156a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156a0 : word) = Some TW_156a0.
Proof. vm_refl. Qed.
Lemma TD_156a0 : decode_any TW_156a0 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156a4 : bv 32 := 0x00641863.
Lemma TF_156a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156a4 : word) = Some TW_156a4.
Proof. vm_refl. Qed.
Lemma TD_156a4 : decode_any TW_156a4 = Some (Branch BC_NE 8 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156a8 : bv 32 := 0x010eb603.
Lemma TF_156a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156a8 : word) = Some TW_156a8.
Proof. vm_refl. Qed.
Lemma TD_156a8 : decode_any TW_156a8 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156ac : bv 32 := 0x40c28633.
Lemma TF_156ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156ac : word) = Some TW_156ac.
Proof. vm_refl. Qed.
Lemma TD_156ac : decode_any TW_156ac = Some (Op ALU_SUB 12 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156b0 : bv 32 := 0xfddff06f.
Lemma TF_156b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156b0 : word) = Some TW_156b0.
Proof. vm_refl. Qed.
Lemma TD_156b0 : decode_any TW_156b0 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156b4 : bv 32 := 0x000e8f93.
Lemma TF_156b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156b4 : word) = Some TW_156b4.
Proof. vm_refl. Qed.
Lemma TD_156b4 : decode_any TW_156b4 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156b8 : bv 32 := 0x00740463.
Lemma TF_156b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156b8 : word) = Some TW_156b8.
Proof. vm_refl. Qed.
Lemma TD_156b8 : decode_any TW_156b8 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156bc : bv 32 := 0x00088f93.
Lemma TF_156bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156bc : word) = Some TW_156bc.
Proof. vm_refl. Qed.
Lemma TD_156bc : decode_any TW_156bc = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156c0 : bv 32 := 0x03c41063.
Lemma TF_156c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156c0 : word) = Some TW_156c0.
Proof. vm_refl. Qed.
Lemma TD_156c0 : decode_any TW_156c0 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156c4 : bv 32 := 0x028eb883.
Lemma TF_156c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156c4 : word) = Some TW_156c4.
Proof. vm_refl. Qed.
Lemma TD_156c4 : decode_any TW_156c4 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156c8 : bv 32 := 0x011f7c63.
Lemma TF_156c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156c8 : word) = Some TW_156c8.
Proof. vm_refl. Qed.
Lemma TD_156c8 : decode_any TW_156c8 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156cc : bv 32 := 0x00800f37.
Lemma TF_156cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156cc : word) = Some TW_156cc.
Proof. vm_refl. Qed.
Lemma TD_156cc : decode_any TW_156cc = Some (Lui 30 2048, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156d0 : bv 32 := 0x01e8e463.
Lemma TF_156d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156d0 : word) = Some TW_156d0.
Proof. vm_refl. Qed.
Lemma TD_156d0 : decode_any TW_156d0 = Some (Branch BC_LTU 17 30 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156d4 : bv 32 := 0x008008b7.
Lemma TF_156d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156d4 : word) = Some TW_156d4.
Proof. vm_refl. Qed.
Lemma TD_156d4 : decode_any TW_156d4 = Some (Lui 17 2048, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156d8 : bv 32 := 0x35172823.
Lemma TF_156d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156d8 : word) = Some TW_156d8.
Proof. vm_refl. Qed.
Lemma TD_156d8 : decode_any TW_156d8 = Some (Store SZ4 14 17 848, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156dc : bv 32 := 0x00088f13.
Lemma TF_156dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156dc : word) = Some TW_156dc.
Proof. vm_refl. Qed.
Lemma TD_156dc : decode_any TW_156dc = Some (OpImm ALU_ADD 30 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156e0 : bv 32 := 0x000f8893.
Lemma TF_156e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156e0 : word) = Some TW_156e0.
Proof. vm_refl. Qed.
Lemma TD_156e0 : decode_any TW_156e0 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156e4 : bv 32 := 0xfa9ff06f.
Lemma TF_156e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156e4 : word) = Some TW_156e4.
Proof. vm_refl. Qed.
Lemma TD_156e4 : decode_any TW_156e4 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156e8 : bv 32 := 0x02088c63.
Lemma TF_156e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156e8 : word) = Some TW_156e8.
Proof. vm_refl. Qed.
Lemma TD_156e8 : decode_any TW_156e8 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156ec : bv 32 := 0x00858713.
Lemma TF_156ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156ec : word) = Some TW_156ec.
Proof. vm_refl. Qed.
Lemma TD_156ec : decode_any TW_156ec = Some (OpImm ALU_ADD 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156f0 : bv 32 := 0x0108b783.
Lemma TF_156f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156f0 : word) = Some TW_156f0.
Proof. vm_refl. Qed.
Lemma TD_156f0 : decode_any TW_156f0 = Some (Load SZ8 true 15 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156f4 : bv 32 := 0x0208b803.
Lemma TF_156f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156f4 : word) = Some TW_156f4.
Proof. vm_refl. Qed.
Lemma TD_156f4 : decode_any TW_156f4 = Some (Load SZ8 true 16 17 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156f8 : bv 32 := 0x0288b683.
Lemma TF_156f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156f8 : word) = Some TW_156f8.
Proof. vm_refl. Qed.
Lemma TD_156f8 : decode_any TW_156f8 = Some (Load SZ8 true 13 17 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_156fc : bv 32 := 0x0308b503.
Lemma TF_156fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x156fc : word) = Some TW_156fc.
Proof. vm_refl. Qed.
Lemma TD_156fc : decode_any TW_156fc = Some (Load SZ8 true 10 17 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15700 : bv 32 := 0x00c78633.
Lemma TF_15700 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15700 : word) = Some TW_15700.
Proof. vm_refl. Qed.
Lemma TD_15700 : decode_any TW_15700 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15704 : bv 32 := 0x00100793.
Lemma TF_15704 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15704 : word) = Some TW_15704.
Proof. vm_refl. Qed.
Lemma TD_15704 : decode_any TW_15704 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15708 : bv 32 := 0x00c5b823.
Lemma TF_15708 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15708 : word) = Some TW_15708.
Proof. vm_refl. Qed.
Lemma TD_15708 : decode_any TW_15708 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1570c : bv 32 := 0x0105bc23.
Lemma TF_1570c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1570c : word) = Some TW_1570c.
Proof. vm_refl. Qed.
Lemma TD_1570c : decode_any TW_1570c = Some (Store SZ8 11 16 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15710 : bv 32 := 0x02a5b423.
Lemma TF_15710 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15710 : word) = Some TW_15710.
Proof. vm_refl. Qed.
Lemma TD_15710 : decode_any TW_15710 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15714 : bv 32 := 0x00e4b823.
Lemma TF_15714 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15714 : word) = Some TW_15714.
Proof. vm_refl. Qed.
Lemma TD_15714 : decode_any TW_15714 = Some (Store SZ8 9 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15718 : bv 32 := 0x02f4b423.
Lemma TF_15718 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15718 : word) = Some TW_15718.
Proof. vm_refl. Qed.
Lemma TD_15718 : decode_any TW_15718 = Some (Store SZ8 9 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1571c : bv 32 := 0x0100006f.
Lemma TF_1571c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1571c : word) = Some TW_1571c.
Proof. vm_refl. Qed.
Lemma TD_1571c : decode_any TW_1571c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15720 : bv 32 := 0x0105b603.
Lemma TF_15720 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15720 : word) = Some TW_15720.
Proof. vm_refl. Qed.
Lemma TD_15720 : decode_any TW_15720 = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15724 : bv 32 := 0x0205b683.
Lemma TF_15724 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15724 : word) = Some TW_15724.
Proof. vm_refl. Qed.
Lemma TD_15724 : decode_any TW_15724 = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15728 : bv 32 := 0x0285b503.
Lemma TF_15728 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15728 : word) = Some TW_15728.
Proof. vm_refl. Qed.
Lemma TD_15728 : decode_any TW_15728 = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1572c : bv 32 := 0x00c68733.
Lemma TF_1572c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1572c : word) = Some TW_1572c.
Proof. vm_refl. Qed.
Lemma TD_1572c : decode_any TW_1572c = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15730 : bv 32 := 0xfff50793.
Lemma TF_15730 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15730 : word) = Some TW_15730.
Proof. vm_refl. Qed.
Lemma TD_15730 : decode_any TW_15730 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15734 : bv 32 := 0x40e00733.
Lemma TF_15734 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15734 : word) = Some TW_15734.
Proof. vm_refl. Qed.
Lemma TD_15734 : decode_any TW_15734 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15738 : bv 32 := 0x00c7f633.
Lemma TF_15738 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15738 : word) = Some TW_15738.
Proof. vm_refl. Qed.
Lemma TD_15738 : decode_any TW_15738 = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1573c : bv 32 := 0x00e7f733.
Lemma TF_1573c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1573c : word) = Some TW_1573c.
Proof. vm_refl. Qed.
Lemma TD_1573c : decode_any TW_1573c = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15740 : bv 32 := 0x00700793.
Lemma TF_15740 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15740 : word) = Some TW_15740.
Proof. vm_refl. Qed.
Lemma TD_15740 : decode_any TW_15740 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15744 : bv 32 := 0x00d706b3.
Lemma TF_15744 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15744 : word) = Some TW_15744.
Proof. vm_refl. Qed.
Lemma TD_15744 : decode_any TW_15744 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15748 : bv 32 := 0x02d5b023.
Lemma TF_15748 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15748 : word) = Some TW_15748.
Proof. vm_refl. Qed.
Lemma TD_15748 : decode_any TW_15748 = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1574c : bv 32 := 0x02c5b823.
Lemma TF_1574c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1574c : word) = Some TW_1574c.
Proof. vm_refl. Qed.
Lemma TD_1574c : decode_any TW_1574c = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15750 : bv 32 := 0x00a7e663.
Lemma TF_15750 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15750 : word) = Some TW_15750.
Proof. vm_refl. Qed.
Lemma TD_15750 : decode_any TW_15750 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15754 : bv 32 := 0x00800513.
Lemma TF_15754 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15754 : word) = Some TW_15754.
Proof. vm_refl. Qed.
Lemma TD_15754 : decode_any TW_15754 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15758 : bv 32 := 0x02a5b423.
Lemma TF_15758 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15758 : word) = Some TW_15758.
Proof. vm_refl. Qed.
Lemma TD_15758 : decode_any TW_15758 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1575c : bv 32 := 0x00d60633.
Lemma TF_1575c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1575c : word) = Some TW_1575c.
Proof. vm_refl. Qed.
Lemma TD_1575c : decode_any TW_1575c = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15760 : bv 32 := 0x000205b7.
Lemma TF_15760 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15760 : word) = Some TW_15760.
Proof. vm_refl. Qed.
Lemma TD_15760 : decode_any TW_15760 = Some (Lui 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15764 : bv 32 := 0x00a60633.
Lemma TF_15764 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15764 : word) = Some TW_15764.
Proof. vm_refl. Qed.
Lemma TD_15764 : decode_any TW_15764 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15768 : bv 32 := 0x0d15869b.
Lemma TF_15768 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15768 : word) = Some TW_15768.
Proof. vm_refl. Qed.
Lemma TD_15768 : decode_any TW_15768 = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1576c : bv 32 := 0x0df60593.
Lemma TF_1576c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1576c : word) = Some TW_1576c.
Proof. vm_refl. Qed.
Lemma TD_1576c : decode_any TW_1576c = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15770 : bv 32 := 0xff85f593.
Lemma TF_15770 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15770 : word) = Some TW_15770.
Proof. vm_refl. Qed.
Lemma TD_15770 : decode_any TW_15770 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15774 : bv 32 := 0x00b4bc23.
Lemma TF_15774 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15774 : word) = Some TW_15774.
Proof. vm_refl. Qed.
Lemma TD_15774 : decode_any TW_15774 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15778 : bv 32 := 0x02a4b023.
Lemma TF_15778 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15778 : word) = Some TW_15778.
Proof. vm_refl. Qed.
Lemma TD_15778 : decode_any TW_15778 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1577c : bv 32 := 0x02d5ea63.
Lemma TF_1577c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1577c : word) = Some TW_1577c.
Proof. vm_refl. Qed.
Lemma TD_1577c : decode_any TW_1577c = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15780 : bv 32 := 0xffffc597.
Lemma TF_15780 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15780 : word) = Some TW_15780.
Proof. vm_refl. Qed.
Lemma TD_15780 : decode_any TW_15780 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15784 : bv 32 := 0x04000893.
Lemma TF_15784 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15784 : word) = Some TW_15784.
Proof. vm_refl. Qed.
Lemma TD_15784 : decode_any TW_15784 = Some (OpImm ALU_ADD 17 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15788 : bv 32 := 0x00200513.
Lemma TF_15788 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15788 : word) = Some TW_15788.
Proof. vm_refl. Qed.
Lemma TD_15788 : decode_any TW_15788 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1578c : bv 32 := 0x2b058593.
Lemma TF_1578c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1578c : word) = Some TW_1578c.
Proof. vm_refl. Qed.
Lemma TD_1578c : decode_any TW_1578c = Some (OpImm ALU_ADD 11 11 688, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15790 : bv 32 := 0x05b00613.
Lemma TF_15790 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15790 : word) = Some TW_15790.
Proof. vm_refl. Qed.
Lemma TD_15790 : decode_any TW_15790 = Some (OpImm ALU_ADD 12 0 91, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15794 : bv 32 := 0x00000073.
Lemma TF_15794 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15794 : word) = Some TW_15794.
Proof. vm_refl. Qed.
Lemma TD_15794 : decode_any TW_15794 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_15794 : is_ecall TW_15794 = true.
Proof. reflexivity. Qed.

Definition TW_15798 : bv 32 := 0x00000023.
Lemma TF_15798 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15798 : word) = Some TW_15798.
Proof. vm_refl. Qed.
Lemma TD_15798 : decode_any TW_15798 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1579c : bv 32 := 0x05e00893.
Lemma TF_1579c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1579c : word) = Some TW_1579c.
Proof. vm_refl. Qed.
Lemma TD_1579c : decode_any TW_1579c = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157a0 : bv 32 := 0x07f00513.
Lemma TF_157a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157a0 : word) = Some TW_157a0.
Proof. vm_refl. Qed.
Lemma TD_157a0 : decode_any TW_157a0 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157a4 : bv 32 := 0x00000073.
Lemma TF_157a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157a4 : word) = Some TW_157a4.
Proof. vm_refl. Qed.
Lemma TD_157a4 : decode_any TW_157a4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_157a4 : is_ecall TW_157a4 = true.
Proof. reflexivity. Qed.

Definition TW_157a8 : bv 32 := 0x0184b583.
Lemma TF_157a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157a8 : word) = Some TW_157a8.
Proof. vm_refl. Qed.
Lemma TD_157a8 : decode_any TW_157a8 = Some (Load SZ8 true 11 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157ac : bv 32 := 0x0204b503.
Lemma TF_157ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157ac : word) = Some TW_157ac.
Proof. vm_refl. Qed.
Lemma TD_157ac : decode_any TW_157ac = Some (Load SZ8 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157b0 : bv 32 := 0x0001a697.
Lemma TF_157b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157b0 : word) = Some TW_157b0.
Proof. vm_refl. Qed.
Lemma TD_157b0 : decode_any TW_157b0 = Some (Auipc 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157b4 : bv 32 := 0x0104b983.
Lemma TF_157b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157b4 : word) = Some TW_157b4.
Proof. vm_refl. Qed.
Lemma TD_157b4 : decode_any TW_157b4 = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157b8 : bv 32 := 0x0284b603.
Lemma TF_157b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157b8 : word) = Some TW_157b8.
Proof. vm_refl. Qed.
Lemma TD_157b8 : decode_any TW_157b8 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157bc : bv 32 := 0xfff50713.
Lemma TF_157bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157bc : word) = Some TW_157bc.
Proof. vm_refl. Qed.
Lemma TD_157bc : decode_any TW_157bc = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157c0 : bv 32 := 0xf3800793.
Lemma TF_157c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157c0 : word) = Some TW_157c0.
Proof. vm_refl. Qed.
Lemma TD_157c0 : decode_any TW_157c0 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157c4 : bv 32 := 0x28868513.
Lemma TF_157c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157c4 : word) = Some TW_157c4.
Proof. vm_refl. Qed.
Lemma TD_157c4 : decode_any TW_157c4 = Some (OpImm ALU_ADD 10 13 648, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157c8 : bv 32 := 0x40a787b3.
Lemma TF_157c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157c8 : word) = Some TW_157c8.
Proof. vm_refl. Qed.
Lemma TD_157c8 : decode_any TW_157c8 = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157cc : bv 32 := 0x00f77733.
Lemma TF_157cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157cc : word) = Some TW_157cc.
Proof. vm_refl. Qed.
Lemma TD_157cc : decode_any TW_157cc = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157d0 : bv 32 := 0xfff64693.
Lemma TF_157d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157d0 : word) = Some TW_157d0.
Proof. vm_refl. Qed.
Lemma TD_157d0 : decode_any TW_157d0 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157d4 : bv 32 := 0x00e50933.
Lemma TF_157d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157d4 : word) = Some TW_157d4.
Proof. vm_refl. Qed.
Lemma TD_157d4 : decode_any TW_157d4 = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157d8 : bv 32 := 0x00369693.
Lemma TF_157d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157d8 : word) = Some TW_157d8.
Proof. vm_refl. Qed.
Lemma TD_157d8 : decode_any TW_157d8 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157dc : bv 32 := 0x00d506b3.
Lemma TF_157dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157dc : word) = Some TW_157dc.
Proof. vm_refl. Qed.
Lemma TD_157dc : decode_any TW_157dc = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157e0 : bv 32 := 0x00b68a33.
Lemma TF_157e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157e0 : word) = Some TW_157e0.
Proof. vm_refl. Qed.
Lemma TD_157e0 : decode_any TW_157e0 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157e4 : bv 32 := 0x0c890413.
Lemma TF_157e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157e4 : word) = Some TW_157e4.
Proof. vm_refl. Qed.
Lemma TD_157e4 : decode_any TW_157e4 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157e8 : bv 32 := 0x04098463.
Lemma TF_157e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157e8 : word) = Some TW_157e8.
Proof. vm_refl. Qed.
Lemma TD_157e8 : decode_any TW_157e8 = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157ec : bv 32 := 0x00361613.
Lemma TF_157ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157ec : word) = Some TW_157ec.
Proof. vm_refl. Qed.
Lemma TD_157ec : decode_any TW_157ec = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157f0 : bv 32 := 0x40c50533.
Lemma TF_157f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157f0 : word) = Some TW_157f0.
Proof. vm_refl. Qed.
Lemma TD_157f0 : decode_any TW_157f0 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157f4 : bv 32 := 0x00b50ab3.
Lemma TF_157f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157f4 : word) = Some TW_157f4.
Proof. vm_refl. Qed.
Lemma TD_157f4 : decode_any TW_157f4 = Some (Op ALU_ADD 21 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157f8 : bv 32 := 0x0289b503.
Lemma TF_157f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157f8 : word) = Some TW_157f8.
Proof. vm_refl. Qed.
Lemma TD_157f8 : decode_any TW_157f8 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_157fc : bv 32 := 0x00a40533.
Lemma TF_157fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x157fc : word) = Some TW_157fc.
Proof. vm_refl. Qed.
Lemma TD_157fc : decode_any TW_157fc = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15800 : bv 32 := 0x7ff50513.
Lemma TF_15800 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15800 : word) = Some TW_15800.
Proof. vm_refl. Qed.
Lemma TD_15800 : decode_any TW_15800 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15804 : bv 32 := 0x00150513.
Lemma TF_15804 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15804 : word) = Some TW_15804.
Proof. vm_refl. Qed.
Lemma TD_15804 : decode_any TW_15804 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15808 : bv 32 := 0x00aab023.
Lemma TF_15808 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15808 : word) = Some TW_15808.
Proof. vm_refl. Qed.
Lemma TD_15808 : decode_any TW_15808 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1580c : bv 32 := 0x0289b503.
Lemma TF_1580c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1580c : word) = Some TW_1580c.
Proof. vm_refl. Qed.
Lemma TD_1580c : decode_any TW_1580c = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15810 : bv 32 := 0x0089b583.
Lemma TF_15810 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15810 : word) = Some TW_15810.
Proof. vm_refl. Qed.
Lemma TD_15810 : decode_any TW_15810 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15814 : bv 32 := 0x0109b603.
Lemma TF_15814 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15814 : word) = Some TW_15814.
Proof. vm_refl. Qed.
Lemma TD_15814 : decode_any TW_15814 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15818 : bv 32 := 0x00a40533.
Lemma TF_15818 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15818 : word) = Some TW_15818.
Proof. vm_refl. Qed.
Lemma TD_15818 : decode_any TW_15818 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1581c : bv 32 := 0x4e8070ef.
Lemma TF_1581c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1581c : word) = Some TW_1581c.
Proof. vm_refl. Qed.
Lemma TD_1581c : decode_any TW_1581c = Some (Jal 1 29928, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15820 : bv 32 := 0x0009b983.
Lemma TF_15820 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15820 : word) = Some TW_15820.
Proof. vm_refl. Qed.
Lemma TD_15820 : decode_any TW_15820 = Some (Load SZ8 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15824 : bv 32 := 0x008a8a93.
Lemma TF_15824 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15824 : word) = Some TW_15824.
Proof. vm_refl. Qed.
Lemma TD_15824 : decode_any TW_15824 = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15828 : bv 32 := 0xfc0998e3.
Lemma TF_15828 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15828 : word) = Some TW_15828.
Proof. vm_refl. Qed.
Lemma TD_15828 : decode_any TW_15828 = Some (Branch BC_NE 19 0 8144, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1582c : bv 32 := 0x0284b603.
Lemma TF_1582c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1582c : word) = Some TW_1582c.
Proof. vm_refl. Qed.
Lemma TD_1582c : decode_any TW_1582c = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15830 : bv 32 := 0x00ca3023.
Lemma TF_15830 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15830 : word) = Some TW_15830.
Proof. vm_refl. Qed.
Lemma TD_15830 : decode_any TW_15830 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15834 : bv 32 := 0x0d493023.
Lemma TF_15834 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15834 : word) = Some TW_15834.
Proof. vm_refl. Qed.
Lemma TD_15834 : decode_any TW_15834 = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15838 : bv 32 := 0x01293023.
Lemma TF_15838 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15838 : word) = Some TW_15838.
Proof. vm_refl. Qed.
Lemma TD_15838 : decode_any TW_15838 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1583c : bv 32 := 0x00040513.
Lemma TF_1583c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1583c : word) = Some TW_1583c.
Proof. vm_refl. Qed.
Lemma TD_1583c : decode_any TW_1583c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15840 : bv 32 := 0x5f5070ef.
Lemma TF_15840 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15840 : word) = Some TW_15840.
Proof. vm_refl. Qed.
Lemma TD_15840 : decode_any TW_15840 = Some (Jal 1 32244, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15844 : bv 32 := 0x04054a63.
Lemma TF_15844 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15844 : word) = Some TW_15844.
Proof. vm_refl. Qed.
Lemma TD_15844 : decode_any TW_15844 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15848 : bv 32 := 0x00051663.
Lemma TF_15848 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15848 : word) = Some TW_15848.
Proof. vm_refl. Qed.
Lemma TD_15848 : decode_any TW_15848 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1584c : bv 32 := 0x00100513.
Lemma TF_1584c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1584c : word) = Some TW_1584c.
Proof. vm_refl. Qed.
Lemma TD_1584c : decode_any TW_1584c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15850 : bv 32 := 0x00a48023.
Lemma TF_15850 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15850 : word) = Some TW_15850.
Proof. vm_refl. Qed.
Lemma TD_15850 : decode_any TW_15850 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15854 : bv 32 := 0x00200513.
Lemma TF_15854 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15854 : word) = Some TW_15854.
Proof. vm_refl. Qed.
Lemma TD_15854 : decode_any TW_15854 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15858 : bv 32 := 0x0003a597.
Lemma TF_15858 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15858 : word) = Some TW_15858.
Proof. vm_refl. Qed.
Lemma TD_15858 : decode_any TW_15858 = Some (Auipc 11 58, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1585c : bv 32 := 0x02a92423.
Lemma TF_1585c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1585c : word) = Some TW_1585c.
Proof. vm_refl. Qed.
Lemma TD_1585c : decode_any TW_1585c = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15860 : bv 32 := 0x06000893.
Lemma TF_15860 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15860 : word) = Some TW_15860.
Proof. vm_refl. Qed.
Lemma TD_15860 : decode_any TW_15860 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15864 : bv 32 := 0x2b058513.
Lemma TF_15864 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15864 : word) = Some TW_15864.
Proof. vm_refl. Qed.
Lemma TD_15864 : decode_any TW_15864 = Some (OpImm ALU_ADD 10 11 688, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15868 : bv 32 := 0x03848593.
Lemma TF_15868 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15868 : word) = Some TW_15868.
Proof. vm_refl. Qed.
Lemma TD_15868 : decode_any TW_15868 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1586c : bv 32 := 0x00000073.
Lemma TF_1586c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1586c : word) = Some TW_1586c.
Proof. vm_refl. Qed.
Lemma TD_1586c : decode_any TW_1586c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_1586c : is_ecall TW_1586c = true.
Proof. reflexivity. Qed.

Definition TW_15870 : bv 32 := 0x07890613.
Lemma TF_15870 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15870 : word) = Some TW_15870.
Proof. vm_refl. Qed.
Lemma TD_15870 : decode_any TW_15870 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15874 : bv 32 := 0x02a92023.
Lemma TF_15874 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15874 : word) = Some TW_15874.
Proof. vm_refl. Qed.
Lemma TD_15874 : decode_any TW_15874 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15878 : bv 32 := 0x08b93c23.
Lemma TF_15878 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15878 : word) = Some TW_15878.
Proof. vm_refl. Qed.
Lemma TD_15878 : decode_any TW_15878 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1587c : bv 32 := 0x06c93c23.
Lemma TF_1587c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1587c : word) = Some TW_1587c.
Proof. vm_refl. Qed.
Lemma TD_1587c : decode_any TW_1587c = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15880 : bv 32 := 0x0003a517.
Lemma TF_15880 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15880 : word) = Some TW_15880.
Proof. vm_refl. Qed.
Lemma TD_15880 : decode_any TW_15880 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15884 : bv 32 := 0x4f853503.
Lemma TF_15884 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15884 : word) = Some TW_15884.
Proof. vm_refl. Qed.
Lemma TD_15884 : decode_any TW_15884 = Some (Load SZ8 true 10 10 1272, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15888 : bv 32 := 0x01293423.
Lemma TF_15888 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15888 : word) = Some TW_15888.
Proof. vm_refl. Qed.
Lemma TD_15888 : decode_any TW_15888 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1588c : bv 32 := 0x01293823.
Lemma TF_1588c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1588c : word) = Some TW_1588c.
Proof. vm_refl. Qed.
Lemma TD_1588c : decode_any TW_1588c = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15890 : bv 32 := 0x00a93c23.
Lemma TF_15890 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15890 : word) = Some TW_15890.
Proof. vm_refl. Qed.
Lemma TD_15890 : decode_any TW_15890 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15894 : bv 32 := 0x0080006f.
Lemma TF_15894 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15894 : word) = Some TW_15894.
Proof. vm_refl. Qed.
Lemma TD_15894 : decode_any TW_15894 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15898 : bv 32 := 0x00000023.
Lemma TF_15898 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15898 : word) = Some TW_15898.
Proof. vm_refl. Qed.
Lemma TD_15898 : decode_any TW_15898 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1589c : bv 32 := 0x03813083.
Lemma TF_1589c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1589c : word) = Some TW_1589c.
Proof. vm_refl. Qed.
Lemma TD_1589c : decode_any TW_1589c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158a0 : bv 32 := 0x03013403.
Lemma TF_158a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x158a0 : word) = Some TW_158a0.
Proof. vm_refl. Qed.
Lemma TD_158a0 : decode_any TW_158a0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158a4 : bv 32 := 0x02813483.
Lemma TF_158a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x158a4 : word) = Some TW_158a4.
Proof. vm_refl. Qed.
Lemma TD_158a4 : decode_any TW_158a4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158a8 : bv 32 := 0x02013903.
Lemma TF_158a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x158a8 : word) = Some TW_158a8.
Proof. vm_refl. Qed.
Lemma TD_158a8 : decode_any TW_158a8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158ac : bv 32 := 0x01813983.
Lemma TF_158ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x158ac : word) = Some TW_158ac.
Proof. vm_refl. Qed.
Lemma TD_158ac : decode_any TW_158ac = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158b0 : bv 32 := 0x01013a03.
Lemma TF_158b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x158b0 : word) = Some TW_158b0.
Proof. vm_refl. Qed.
Lemma TD_158b0 : decode_any TW_158b0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158b4 : bv 32 := 0x00813a83.
Lemma TF_158b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x158b4 : word) = Some TW_158b4.
Proof. vm_refl. Qed.
Lemma TD_158b4 : decode_any TW_158b4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158b8 : bv 32 := 0x04010113.
Lemma TF_158b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x158b8 : word) = Some TW_158b8.
Proof. vm_refl. Qed.
Lemma TD_158b8 : decode_any TW_158b8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158bc : bv 32 := 0x00008067.
Lemma TF_158bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x158bc : word) = Some TW_158bc.
Proof. vm_refl. Qed.
Lemma TD_158bc : decode_any TW_158bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_158e4 : bv 32 := 0x00050593.
Lemma F_158e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15984 : word) = Some W_158e4.
Proof. vm_refl. Qed.
Lemma D_158e4 : decode_any W_158e4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_158e8 : bv 32 := 0x05e00893.
Lemma F_158e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15988 : word) = Some W_158e8.
Proof. vm_refl. Qed.
Lemma D_158e8 : decode_any W_158e8 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_158ec : bv 32 := 0x00000073.
Lemma F_158ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1598c : word) = Some W_158ec.
Proof. vm_refl. Qed.
Lemma D_158ec : decode_any W_158ec = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_158ec : is_ecall W_158ec = true.
Proof. reflexivity. Qed.

Definition W_15900 : bv 32 := 0xfd010113.
Lemma F_15900 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159a0 : word) = Some W_15900.
Proof. vm_refl. Qed.
Lemma D_15900 : decode_any W_15900 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_15904 : bv 32 := 0x02113423.
Lemma F_15904 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159a4 : word) = Some W_15904.
Proof. vm_refl. Qed.
Lemma D_15904 : decode_any W_15904 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15908 : bv 32 := 0x02813023.
Lemma F_15908 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159a8 : word) = Some W_15908.
Proof. vm_refl. Qed.
Lemma D_15908 : decode_any W_15908 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1590c : bv 32 := 0x00913c23.
Lemma F_1590c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159ac : word) = Some W_1590c.
Proof. vm_refl. Qed.
Lemma D_1590c : decode_any W_1590c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15910 : bv 32 := 0x01213823.
Lemma F_15910 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159b0 : word) = Some W_15910.
Proof. vm_refl. Qed.
Lemma D_15910 : decode_any W_15910 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15914 : bv 32 := 0x01313423.
Lemma F_15914 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159b4 : word) = Some W_15914.
Proof. vm_refl. Qed.
Lemma D_15914 : decode_any W_15914 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15918 : bv 32 := 0x0003a517.
Lemma F_15918 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159b8 : word) = Some W_15918.
Proof. vm_refl. Qed.
Lemma D_15918 : decode_any W_15918 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_1591c : bv 32 := 0x19050913.
Lemma F_1591c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159bc : word) = Some W_1591c.
Proof. vm_refl. Qed.
Lemma D_1591c : decode_any W_1591c = Some (OpImm ALU_ADD 18 10 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_15920 : bv 32 := 0x00490413.
Lemma F_15920 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159c0 : word) = Some W_15920.
Proof. vm_refl. Qed.
Lemma D_15920 : decode_any W_15920 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_15924 : bv 32 := 0x00040513.
Lemma F_15924 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159c4 : word) = Some W_15924.
Proof. vm_refl. Qed.
Lemma D_15924 : decode_any W_15924 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15928 : bv 32 := 0x149070ef.
Lemma F_15928 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159c8 : word) = Some W_15928.
Proof. vm_refl. Qed.
Lemma D_15928 : decode_any W_15928 = Some (Jal 1 31048, 4%Z).
Proof. vm_refl. Qed.

Definition W_1592c : bv 32 := 0x01093503.
Lemma F_1592c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159cc : word) = Some W_1592c.
Proof. vm_refl. Qed.
Lemma D_1592c : decode_any W_1592c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15930 : bv 32 := 0x06050863.
Lemma F_15930 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159d0 : word) = Some W_15930.
Proof. vm_refl. Qed.
Lemma D_15930 : decode_any W_15930 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_15934 : bv 32 := 0x00892583.
Lemma F_15934 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159d4 : word) = Some W_15934.
Proof. vm_refl. Qed.
Lemma D_15934 : decode_any W_15934 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15938 : bv 32 := 0x0180006f.
Lemma F_15938 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159d8 : word) = Some W_15938.
Proof. vm_refl. Qed.
Lemma D_15938 : decode_any W_15938 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1593c : bv 32 := 0x00053503.
Lemma F_1593c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159dc : word) = Some W_1593c.
Proof. vm_refl. Qed.
Lemma D_1593c : decode_any W_1593c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15940 : bv 32 := 0x02000593.
Lemma F_15940 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159e0 : word) = Some W_15940.
Proof. vm_refl. Qed.
Lemma D_15940 : decode_any W_15940 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15944 : bv 32 := 0x00b92423.
Lemma F_15944 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159e4 : word) = Some W_15944.
Proof. vm_refl. Qed.
Lemma D_15944 : decode_any W_15944 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15948 : bv 32 := 0x00a93823.
Lemma F_15948 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159e8 : word) = Some W_15948.
Proof. vm_refl. Qed.
Lemma D_15948 : decode_any W_15948 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1594c : bv 32 := 0x04050a63.
Lemma F_1594c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159ec : word) = Some W_1594c.
Proof. vm_refl. Qed.
Lemma D_1594c : decode_any W_1594c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_15950 : bv 32 := 0xfff5861b.
Lemma F_15950 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159f0 : word) = Some W_15950.
Proof. vm_refl. Qed.
Lemma D_15950 : decode_any W_15950 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_15954 : bv 32 := 0x00c92423.
Lemma F_15954 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159f4 : word) = Some W_15954.
Proof. vm_refl. Qed.
Lemma D_15954 : decode_any W_15954 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15958 : bv 32 := 0xfeb052e3.
Lemma F_15958 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159f8 : word) = Some W_15958.
Proof. vm_refl. Qed.
Lemma D_15958 : decode_any W_15958 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_1595c : bv 32 := 0x01093503.
Lemma F_1595c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x159fc : word) = Some W_1595c.
Proof. vm_refl. Qed.
Lemma D_1595c : decode_any W_1595c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15960 : bv 32 := 0x00361613.
Lemma F_15960 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a00 : word) = Some W_15960.
Proof. vm_refl. Qed.
Lemma D_15960 : decode_any W_15960 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_15964 : bv 32 := 0x00c50533.
Lemma F_15964 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a04 : word) = Some W_15964.
Proof. vm_refl. Qed.
Lemma D_15964 : decode_any W_15964 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15968 : bv 32 := 0x00853983.
Lemma F_15968 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a08 : word) = Some W_15968.
Proof. vm_refl. Qed.
Lemma D_15968 : decode_any W_15968 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1596c : bv 32 := 0x10853483.
Lemma F_1596c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a0c : word) = Some W_1596c.
Proof. vm_refl. Qed.
Lemma D_1596c : decode_any W_1596c = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_15970 : bv 32 := 0x00040513.
Lemma F_15970 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a10 : word) = Some W_15970.
Proof. vm_refl. Qed.
Lemma D_15970 : decode_any W_15970 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15974 : bv 32 := 0x385070ef.
Lemma F_15974 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a14 : word) = Some W_15974.
Proof. vm_refl. Qed.
Lemma D_15974 : decode_any W_15974 = Some (Jal 1 31620, 4%Z).
Proof. vm_refl. Qed.

Definition W_15978 : bv 32 := 0x00048513.
Lemma F_15978 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a18 : word) = Some W_15978.
Proof. vm_refl. Qed.
Lemma D_15978 : decode_any W_15978 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1597c : bv 32 := 0x000980e7.
Lemma F_1597c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a1c : word) = Some W_1597c.
Proof. vm_refl. Qed.
Lemma D_1597c : decode_any W_1597c = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15980 : bv 32 := 0x00040513.
Lemma F_15980 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a20 : word) = Some W_15980.
Proof. vm_refl. Qed.
Lemma D_15980 : decode_any W_15980 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15984 : bv 32 := 0x0ed070ef.
Lemma F_15984 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a24 : word) = Some W_15984.
Proof. vm_refl. Qed.
Lemma D_15984 : decode_any W_15984 = Some (Jal 1 30956, 4%Z).
Proof. vm_refl. Qed.

Definition W_15988 : bv 32 := 0x00892503.
Lemma F_15988 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a28 : word) = Some W_15988.
Proof. vm_refl. Qed.
Lemma D_15988 : decode_any W_15988 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1598c : bv 32 := 0xfff5061b.
Lemma F_1598c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a2c : word) = Some W_1598c.
Proof. vm_refl. Qed.
Lemma D_1598c : decode_any W_1598c = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_15990 : bv 32 := 0x00c92423.
Lemma F_15990 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a30 : word) = Some W_15990.
Proof. vm_refl. Qed.
Lemma D_15990 : decode_any W_15990 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15994 : bv 32 := 0xfca044e3.
Lemma F_15994 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a34 : word) = Some W_15994.
Proof. vm_refl. Qed.
Lemma D_15994 : decode_any W_15994 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_15998 : bv 32 := 0x01093503.
Lemma F_15998 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a38 : word) = Some W_15998.
Proof. vm_refl. Qed.
Lemma D_15998 : decode_any W_15998 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1599c : bv 32 := 0xfa1ff06f.
Lemma F_1599c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a3c : word) = Some W_1599c.
Proof. vm_refl. Qed.
Lemma D_1599c : decode_any W_1599c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_159a0 : bv 32 := 0x00100513.
Lemma F_159a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a40 : word) = Some W_159a0.
Proof. vm_refl. Qed.
Lemma D_159a0 : decode_any W_159a0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_159a4 : bv 32 := 0x00a90023.
Lemma F_159a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a44 : word) = Some W_159a4.
Proof. vm_refl. Qed.
Lemma D_159a4 : decode_any W_159a4 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_159a8 : bv 32 := 0x00040513.
Lemma F_159a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a48 : word) = Some W_159a8.
Proof. vm_refl. Qed.
Lemma D_159a8 : decode_any W_159a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_159ac : bv 32 := 0x02813083.
Lemma F_159ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a4c : word) = Some W_159ac.
Proof. vm_refl. Qed.
Lemma D_159ac : decode_any W_159ac = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_159b0 : bv 32 := 0x02013403.
Lemma F_159b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a50 : word) = Some W_159b0.
Proof. vm_refl. Qed.
Lemma D_159b0 : decode_any W_159b0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_159b4 : bv 32 := 0x01813483.
Lemma F_159b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a54 : word) = Some W_159b4.
Proof. vm_refl. Qed.
Lemma D_159b4 : decode_any W_159b4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_159b8 : bv 32 := 0x01013903.
Lemma F_159b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a58 : word) = Some W_159b8.
Proof. vm_refl. Qed.
Lemma D_159b8 : decode_any W_159b8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_159bc : bv 32 := 0x00813983.
Lemma F_159bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a5c : word) = Some W_159bc.
Proof. vm_refl. Qed.
Lemma D_159bc : decode_any W_159bc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_159c0 : bv 32 := 0x03010113.
Lemma F_159c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a60 : word) = Some W_159c0.
Proof. vm_refl. Qed.
Lemma D_159c0 : decode_any W_159c0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_159c4 : bv 32 := 0x3350706f.
Lemma F_159c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a64 : word) = Some W_159c4.
Proof. vm_refl. Qed.
Lemma D_159c4 : decode_any W_159c4 = Some (Jal 0 31540, 4%Z).
Proof. vm_refl. Qed.

Definition W_159c8 : bv 32 := 0x00008067.
Lemma F_159c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15a68 : word) = Some W_159c8.
Proof. vm_refl. Qed.
Lemma D_159c8 : decode_any W_159c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15a90 : bv 32 := 0x00050067.
Lemma F_15a90 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b30 : word) = Some W_15a90.
Proof. vm_refl. Qed.
Lemma D_15a90 : decode_any W_15a90 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15a94 : bv 32 := 0x00008067.
Lemma F_15a94 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b34 : word) = Some W_15a94.
Proof. vm_refl. Qed.
Lemma D_15a94 : decode_any W_15a94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15a98 : bv 32 := 0xfe010113.
Lemma F_15a98 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b38 : word) = Some W_15a98.
Proof. vm_refl. Qed.
Lemma D_15a98 : decode_any W_15a98 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_15a9c : bv 32 := 0x00113c23.
Lemma F_15a9c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b3c : word) = Some W_15a9c.
Proof. vm_refl. Qed.
Lemma D_15a9c : decode_any W_15a9c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15aa0 : bv 32 := 0x00813823.
Lemma F_15aa0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b40 : word) = Some W_15aa0.
Proof. vm_refl. Qed.
Lemma D_15aa0 : decode_any W_15aa0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15aa4 : bv 32 := 0x00913423.
Lemma F_15aa4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b44 : word) = Some W_15aa4.
Proof. vm_refl. Qed.
Lemma D_15aa4 : decode_any W_15aa4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15aa8 : bv 32 := 0x00009517.
Lemma F_15aa8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b48 : word) = Some W_15aa8.
Proof. vm_refl. Qed.
Lemma D_15aa8 : decode_any W_15aa8 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15aac : bv 32 := 0x00009597.
Lemma F_15aac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b4c : word) = Some W_15aac.
Proof. vm_refl. Qed.
Lemma D_15aac : decode_any W_15aac = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ab0 : bv 32 := 0xc4053503.
Lemma F_15ab0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b50 : word) = Some W_15ab0.
Proof. vm_refl. Qed.
Lemma D_15ab0 : decode_any W_15ab0 = Some (Load SZ8 true 10 10 3136, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ab4 : bv 32 := 0xc445b403.
Lemma F_15ab4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b54 : word) = Some W_15ab4.
Proof. vm_refl. Qed.
Lemma D_15ab4 : decode_any W_15ab4 = Some (Load SZ8 true 8 11 3140, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ab8 : bv 32 := 0x00a47c63.
Lemma F_15ab8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b58 : word) = Some W_15ab8.
Proof. vm_refl. Qed.
Lemma D_15ab8 : decode_any W_15ab8 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15abc : bv 32 := 0xff853583.
Lemma F_15abc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b5c : word) = Some W_15abc.
Proof. vm_refl. Qed.
Lemma D_15abc : decode_any W_15abc = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ac0 : bv 32 := 0xff850493.
Lemma F_15ac0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b60 : word) = Some W_15ac0.
Proof. vm_refl. Qed.
Lemma D_15ac0 : decode_any W_15ac0 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ac4 : bv 32 := 0x000580e7.
Lemma F_15ac4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b64 : word) = Some W_15ac4.
Proof. vm_refl. Qed.
Lemma D_15ac4 : decode_any W_15ac4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ac8 : bv 32 := 0x00048513.
Lemma F_15ac8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b68 : word) = Some W_15ac8.
Proof. vm_refl. Qed.
Lemma D_15ac8 : decode_any W_15ac8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15acc : bv 32 := 0xfe9468e3.
Lemma F_15acc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b6c : word) = Some W_15acc.
Proof. vm_refl. Qed.
Lemma D_15acc : decode_any W_15acc = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ad0 : bv 32 := 0x01813083.
Lemma F_15ad0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b70 : word) = Some W_15ad0.
Proof. vm_refl. Qed.
Lemma D_15ad0 : decode_any W_15ad0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ad4 : bv 32 := 0x01013403.
Lemma F_15ad4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b74 : word) = Some W_15ad4.
Proof. vm_refl. Qed.
Lemma D_15ad4 : decode_any W_15ad4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ad8 : bv 32 := 0x00813483.
Lemma F_15ad8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b78 : word) = Some W_15ad8.
Proof. vm_refl. Qed.
Lemma D_15ad8 : decode_any W_15ad8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15adc : bv 32 := 0x02010113.
Lemma F_15adc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b7c : word) = Some W_15adc.
Proof. vm_refl. Qed.
Lemma D_15adc : decode_any W_15adc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ae0 : bv 32 := 0xfb5ff06f.
Lemma F_15ae0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b80 : word) = Some W_15ae0.
Proof. vm_refl. Qed.
Lemma D_15ae0 : decode_any W_15ae0 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ae4 : bv 32 := 0xff010113.
Lemma F_15ae4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b84 : word) = Some W_15ae4.
Proof. vm_refl. Qed.
Lemma D_15ae4 : decode_any W_15ae4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ae8 : bv 32 := 0x00113423.
Lemma F_15ae8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b88 : word) = Some W_15ae8.
Proof. vm_refl. Qed.
Lemma D_15ae8 : decode_any W_15ae8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15aec : bv 32 := 0x00813023.
Lemma F_15aec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b8c : word) = Some W_15aec.
Proof. vm_refl. Qed.
Lemma D_15aec : decode_any W_15aec = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15af0 : bv 32 := 0x00000593.
Lemma F_15af0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b90 : word) = Some W_15af0.
Proof. vm_refl. Qed.
Lemma D_15af0 : decode_any W_15af0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15af4 : bv 32 := 0x00020613.
Lemma F_15af4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b94 : word) = Some W_15af4.
Proof. vm_refl. Qed.
Lemma D_15af4 : decode_any W_15af4 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15af8 : bv 32 := 0xf5862603.
Lemma F_15af8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b98 : word) = Some W_15af8.
Proof. vm_refl. Qed.
Lemma D_15af8 : decode_any W_15af8 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_15afc : bv 32 := 0x0003a697.
Lemma F_15afc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15b9c : word) = Some W_15afc.
Proof. vm_refl. Qed.
Lemma D_15afc : decode_any W_15afc = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b00 : bv 32 := 0x1cc68693.
Lemma F_15b00 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ba0 : word) = Some W_15b00.
Proof. vm_refl. Qed.
Lemma D_15b00 : decode_any W_15b00 = Some (OpImm ALU_ADD 13 13 460, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b04 : bv 32 := 0x1606a72f.
Lemma F_15b04 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ba4 : word) = Some W_15b04.
Proof. vm_refl. Qed.
Lemma D_15b04 : decode_any W_15b04 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b08 : bv 32 := 0x00b71663.
Lemma F_15b08 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ba8 : word) = Some W_15b08.
Proof. vm_refl. Qed.
Lemma D_15b08 : decode_any W_15b08 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b0c : bv 32 := 0x1ec6a7af.
Lemma F_15b0c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bac : word) = Some W_15b0c.
Proof. vm_refl. Qed.
Lemma D_15b0c : decode_any W_15b0c = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b10 : bv 32 := 0xfe079ae3.
Lemma F_15b10 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bb0 : word) = Some W_15b10.
Proof. vm_refl. Qed.
Lemma D_15b10 : decode_any W_15b10 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b14 : bv 32 := 0x0007059b.
Lemma F_15b14 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bb4 : word) = Some W_15b14.
Proof. vm_refl. Qed.
Lemma D_15b14 : decode_any W_15b14 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b18 : bv 32 := 0x02c58263.
Lemma F_15b18 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bb8 : word) = Some W_15b18.
Proof. vm_refl. Qed.
Lemma D_15b18 : decode_any W_15b18 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b1c : bv 32 := 0x02058263.
Lemma F_15b1c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bbc : word) = Some W_15b1c.
Proof. vm_refl. Qed.
Lemma D_15b1c : decode_any W_15b1c = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b20 : bv 32 := 0x04900893.
Lemma F_15b20 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bc0 : word) = Some W_15b20.
Proof. vm_refl. Qed.
Lemma D_15b20 : decode_any W_15b20 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b24 : bv 32 := 0x00000593.
Lemma F_15b24 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bc4 : word) = Some W_15b24.
Proof. vm_refl. Qed.
Lemma D_15b24 : decode_any W_15b24 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b28 : bv 32 := 0x00000613.
Lemma F_15b28 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bc8 : word) = Some W_15b28.
Proof. vm_refl. Qed.
Lemma D_15b28 : decode_any W_15b28 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b2c : bv 32 := 0x00000693.
Lemma F_15b2c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bcc : word) = Some W_15b2c.
Proof. vm_refl. Qed.
Lemma D_15b2c : decode_any W_15b2c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b30 : bv 32 := 0x00000513.
Lemma F_15b30 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bd0 : word) = Some W_15b30.
Proof. vm_refl. Qed.
Lemma D_15b30 : decode_any W_15b30 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b34 : bv 32 := 0x00000073.
Lemma F_15b34 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bd4 : word) = Some W_15b34.
Proof. vm_refl. Qed.
Lemma D_15b34 : decode_any W_15b34 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_15b34 : is_ecall W_15b34 = true.
Proof. reflexivity. Qed.

Definition W_15b38 : bv 32 := 0xff9ff06f.
Lemma F_15b38 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bd8 : word) = Some W_15b38.
Proof. vm_refl. Qed.
Lemma D_15b38 : decode_any W_15b38 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b3c : bv 32 := 0x00000023.
Lemma F_15b3c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bdc : word) = Some W_15b3c.
Proof. vm_refl. Qed.
Lemma D_15b3c : decode_any W_15b3c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b40 : bv 32 := 0x00050413.
Lemma F_15b40 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15be0 : word) = Some W_15b40.
Proof. vm_refl. Qed.
Lemma D_15b40 : decode_any W_15b40 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b44 : bv 32 := 0xdbdff0ef.
Lemma F_15b44 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15be4 : word) = Some W_15b44.
Proof. vm_refl. Qed.
Lemma D_15b44 : decode_any W_15b44 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b48 : bv 32 := 0xf51ff0ef.
Lemma F_15b48 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15be8 : word) = Some W_15b48.
Proof. vm_refl. Qed.
Lemma D_15b48 : decode_any W_15b48 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b4c : bv 32 := 0x310020ef.
Lemma F_15b4c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bec : word) = Some W_15b4c.
Proof. vm_refl. Qed.
Lemma D_15b4c : decode_any W_15b4c = Some (Jal 1 8976, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b50 : bv 32 := 0x00040513.
Lemma F_15b50 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bf0 : word) = Some W_15b50.
Proof. vm_refl. Qed.
Lemma D_15b50 : decode_any W_15b50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b54 : bv 32 := 0xd91ff0ef.
Lemma F_15b54 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15bf4 : word) = Some W_15b54.
Proof. vm_refl. Qed.
Lemma D_15b54 : decode_any W_15b54 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c3c : bv 32 := 0xff010113.
Lemma F_15c3c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15cdc : word) = Some W_15c3c.
Proof. vm_refl. Qed.
Lemma D_15c3c : decode_any W_15c3c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c40 : bv 32 := 0x00113423.
Lemma F_15c40 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ce0 : word) = Some W_15c40.
Proof. vm_refl. Qed.
Lemma D_15c40 : decode_any W_15c40 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c44 : bv 32 := 0x00050e63.
Lemma F_15c44 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ce4 : word) = Some W_15c44.
Proof. vm_refl. Qed.
Lemma D_15c44 : decode_any W_15c44 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c48 : bv 32 := 0x00050593.
Lemma F_15c48 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ce8 : word) = Some W_15c48.
Proof. vm_refl. Qed.
Lemma D_15c48 : decode_any W_15c48 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c4c : bv 32 := 0x00009517.
Lemma F_15c4c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15cec : word) = Some W_15c4c.
Proof. vm_refl. Qed.
Lemma D_15c4c : decode_any W_15c4c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c50 : bv 32 := 0xa9453503.
Lemma F_15c50 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15cf0 : word) = Some W_15c50.
Proof. vm_refl. Qed.
Lemma D_15c50 : decode_any W_15c50 = Some (Load SZ8 true 10 10 2708, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c54 : bv 32 := 0x00800613.
Lemma F_15c54 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15cf4 : word) = Some W_15c54.
Proof. vm_refl. Qed.
Lemma D_15c54 : decode_any W_15c54 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c58 : bv 32 := 0x00c070ef.
Lemma F_15c58 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15cf8 : word) = Some W_15c58.
Proof. vm_refl. Qed.
Lemma D_15c58 : decode_any W_15c58 = Some (Jal 1 28684, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c5c : bv 32 := 0x01c0006f.
Lemma F_15c5c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15cfc : word) = Some W_15c5c.
Proof. vm_refl. Qed.
Lemma D_15c5c : decode_any W_15c5c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c60 : bv 32 := 0x00009517.
Lemma F_15c60 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d00 : word) = Some W_15c60.
Proof. vm_refl. Qed.
Lemma D_15c60 : decode_any W_15c60 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c64 : bv 32 := 0xa8053503.
Lemma F_15c64 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d04 : word) = Some W_15c64.
Proof. vm_refl. Qed.
Lemma D_15c64 : decode_any W_15c64 = Some (Load SZ8 true 10 10 2688, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c68 : bv 32 := 0x41c655b7.
Lemma F_15c68 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d08 : word) = Some W_15c68.
Proof. vm_refl. Qed.
Lemma D_15c68 : decode_any W_15c68 = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c6c : bv 32 := 0xe6d5859b.
Lemma F_15c6c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d0c : word) = Some W_15c6c.
Proof. vm_refl. Qed.
Lemma D_15c6c : decode_any W_15c6c = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c70 : bv 32 := 0x02b505b3.
Lemma F_15c70 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d10 : word) = Some W_15c70.
Proof. vm_refl. Qed.
Lemma D_15c70 : decode_any W_15c70 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c74 : bv 32 := 0x00b53023.
Lemma F_15c74 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d14 : word) = Some W_15c74.
Proof. vm_refl. Qed.
Lemma D_15c74 : decode_any W_15c74 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c78 : bv 32 := 0x00009517.
Lemma F_15c78 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d18 : word) = Some W_15c78.
Proof. vm_refl. Qed.
Lemma D_15c78 : decode_any W_15c78 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c7c : bv 32 := 0xa6853503.
Lemma F_15c7c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d1c : word) = Some W_15c7c.
Proof. vm_refl. Qed.
Lemma D_15c7c : decode_any W_15c7c = Some (Load SZ8 true 10 10 2664, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c80 : bv 32 := 0x000500a3.
Lemma F_15c80 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d20 : word) = Some W_15c80.
Proof. vm_refl. Qed.
Lemma D_15c80 : decode_any W_15c80 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c84 : bv 32 := 0x00053503.
Lemma F_15c84 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d24 : word) = Some W_15c84.
Proof. vm_refl. Qed.
Lemma D_15c84 : decode_any W_15c84 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c88 : bv 32 := 0x00020593.
Lemma F_15c88 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d28 : word) = Some W_15c88.
Proof. vm_refl. Qed.
Lemma D_15c88 : decode_any W_15c88 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c8c : bv 32 := 0xfea5b823.
Lemma F_15c8c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d2c : word) = Some W_15c8c.
Proof. vm_refl. Qed.
Lemma D_15c8c : decode_any W_15c8c = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c90 : bv 32 := 0x00813083.
Lemma F_15c90 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d30 : word) = Some W_15c90.
Proof. vm_refl. Qed.
Lemma D_15c90 : decode_any W_15c90 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c94 : bv 32 := 0x01010113.
Lemma F_15c94 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d34 : word) = Some W_15c94.
Proof. vm_refl. Qed.
Lemma D_15c94 : decode_any W_15c94 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c98 : bv 32 := 0x00008067.
Lemma F_15c98 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d38 : word) = Some W_15c98.
Proof. vm_refl. Qed.
Lemma D_15c98 : decode_any W_15c98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ca4 : bv 32 := 0xfffff5b7.
Lemma F_15ca4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d44 : word) = Some W_15ca4.
Proof. vm_refl. Qed.
Lemma D_15ca4 : decode_any W_15ca4 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ca8 : bv 32 := 0x0015859b.
Lemma F_15ca8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d48 : word) = Some W_15ca8.
Proof. vm_refl. Qed.
Lemma D_15ca8 : decode_any W_15ca8 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15cac : bv 32 := 0x02b56663.
Lemma F_15cac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d4c : word) = Some W_15cac.
Proof. vm_refl. Qed.
Lemma D_15cac : decode_any W_15cac = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_15cd8 : bv 32 := 0x00008067.
Lemma F_15cd8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15d78 : word) = Some W_15cd8.
Proof. vm_refl. Qed.
Lemma D_15cd8 : decode_any W_15cd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e2c : bv 32 := 0x1c050463.
Lemma F_15e2c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ecc : word) = Some W_15e2c.
Proof. vm_refl. Qed.
Lemma D_15e2c : decode_any W_15e2c = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e30 : bv 32 := 0xfd010113.
Lemma F_15e30 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ed0 : word) = Some W_15e30.
Proof. vm_refl. Qed.
Lemma D_15e30 : decode_any W_15e30 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e34 : bv 32 := 0x02113423.
Lemma F_15e34 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ed4 : word) = Some W_15e34.
Proof. vm_refl. Qed.
Lemma D_15e34 : decode_any W_15e34 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e38 : bv 32 := 0x02813023.
Lemma F_15e38 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ed8 : word) = Some W_15e38.
Proof. vm_refl. Qed.
Lemma D_15e38 : decode_any W_15e38 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e3c : bv 32 := 0x00913c23.
Lemma F_15e3c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15edc : word) = Some W_15e3c.
Proof. vm_refl. Qed.
Lemma D_15e3c : decode_any W_15e3c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e40 : bv 32 := 0x01213823.
Lemma F_15e40 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ee0 : word) = Some W_15e40.
Proof. vm_refl. Qed.
Lemma D_15e40 : decode_any W_15e40 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e44 : bv 32 := 0x01313423.
Lemma F_15e44 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ee4 : word) = Some W_15e44.
Proof. vm_refl. Qed.
Lemma D_15e44 : decode_any W_15e44 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e48 : bv 32 := 0x00050493.
Lemma F_15e48 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ee8 : word) = Some W_15e48.
Proof. vm_refl. Qed.
Lemma D_15e48 : decode_any W_15e48 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e4c : bv 32 := 0x1ac000ef.
Lemma F_15e4c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15eec : word) = Some W_15e4c.
Proof. vm_refl. Qed.
Lemma D_15e4c : decode_any W_15e4c = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e50 : bv 32 := 0x02053583.
Lemma F_15e50 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ef0 : word) = Some W_15e50.
Proof. vm_refl. Qed.
Lemma D_15e50 : decode_any W_15e50 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e54 : bv 32 := 0xffd4c683.
Lemma F_15e54 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ef4 : word) = Some W_15e54.
Proof. vm_refl. Qed.
Lemma D_15e54 : decode_any W_15e54 = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e58 : bv 32 := 0x00c5d613.
Lemma F_15e58 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15ef8 : word) = Some W_15e58.
Proof. vm_refl. Qed.
Lemma D_15e58 : decode_any W_15e58 = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e5c : bv 32 := 0x01f6f413.
Lemma F_15e5c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15efc : word) = Some W_15e5c.
Proof. vm_refl. Qed.
Lemma D_15e5c : decode_any W_15e5c = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e60 : bv 32 := 0x00060e63.
Lemma F_15e60 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f00 : word) = Some W_15e60.
Proof. vm_refl. Qed.
Lemma D_15e60 : decode_any W_15e60 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e64 : bv 32 := 0x01f5f613.
Lemma F_15e64 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f04 : word) = Some W_15e64.
Proof. vm_refl. Qed.
Lemma D_15e64 : decode_any W_15e64 = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e68 : bv 32 := 0x00061a63.
Lemma F_15e68 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f08 : word) = Some W_15e68.
Proof. vm_refl. Qed.
Lemma D_15e68 : decode_any W_15e68 = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e6c : bv 32 := 0xfffff637.
Lemma F_15e6c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f0c : word) = Some W_15e6c.
Proof. vm_refl. Qed.
Lemma D_15e6c : decode_any W_15e6c = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e70 : bv 32 := 0x00c5f633.
Lemma F_15e70 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f10 : word) = Some W_15e70.
Proof. vm_refl. Qed.
Lemma D_15e70 : decode_any W_15e70 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e74 : bv 32 := 0xff060613.
Lemma F_15e74 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f14 : word) = Some W_15e74.
Proof. vm_refl. Qed.
Lemma D_15e74 : decode_any W_15e74 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e78 : bv 32 := 0x0200006f.
Lemma F_15e78 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f18 : word) = Some W_15e78.
Proof. vm_refl. Qed.
Lemma D_15e78 : decode_any W_15e78 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e7c : bv 32 := 0x0055d613.
Lemma F_15e7c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f1c : word) = Some W_15e7c.
Proof. vm_refl. Qed.
Lemma D_15e7c : decode_any W_15e7c = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e80 : bv 32 := 0xffffc717.
Lemma F_15e80 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f20 : word) = Some W_15e80.
Proof. vm_refl. Qed.
Lemma D_15e80 : decode_any W_15e80 = Some (Auipc 14 1048572, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e84 : bv 32 := 0x07e67613.
Lemma F_15e84 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f24 : word) = Some W_15e84.
Proof. vm_refl. Qed.
Lemma D_15e84 : decode_any W_15e84 = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e88 : bv 32 := 0xb8c70713.
Lemma F_15e88 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f28 : word) = Some W_15e88.
Proof. vm_refl. Qed.
Lemma D_15e88 : decode_any W_15e88 = Some (OpImm ALU_ADD 14 14 2956, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e8c : bv 32 := 0x00c70633.
Lemma F_15e8c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f2c : word) = Some W_15e8c.
Proof. vm_refl. Qed.
Lemma D_15e8c : decode_any W_15e8c = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e90 : bv 32 := 0x00065603.
Lemma F_15e90 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f30 : word) = Some W_15e90.
Proof. vm_refl. Qed.
Lemma D_15e90 : decode_any W_15e90 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e94 : bv 32 := 0x00461613.
Lemma F_15e94 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f34 : word) = Some W_15e94.
Proof. vm_refl. Qed.
Lemma D_15e94 : decode_any W_15e94 = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e98 : bv 32 := 0x01053703.
Lemma F_15e98 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f38 : word) = Some W_15e98.
Proof. vm_refl. Qed.
Lemma D_15e98 : decode_any W_15e98 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15e9c : bv 32 := 0x028607b3.
Lemma F_15e9c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f3c : word) = Some W_15e9c.
Proof. vm_refl. Qed.
Lemma D_15e9c : decode_any W_15e9c = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ea0 : bv 32 := 0x0a000813.
Lemma F_15ea0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f40 : word) = Some W_15ea0.
Proof. vm_refl. Qed.
Lemma D_15ea0 : decode_any W_15ea0 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ea4 : bv 32 := 0x00c70633.
Lemma F_15ea4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f44 : word) = Some W_15ea4.
Proof. vm_refl. Qed.
Lemma D_15ea4 : decode_any W_15ea4 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ea8 : bv 32 := 0x00f607b3.
Lemma F_15ea8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f48 : word) = Some W_15ea8.
Proof. vm_refl. Qed.
Lemma D_15ea8 : decode_any W_15ea8 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eac : bv 32 := 0x00c78613.
Lemma F_15eac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f4c : word) = Some W_15eac.
Proof. vm_refl. Qed.
Lemma D_15eac : decode_any W_15eac = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eb0 : bv 32 := 0x0056d713.
Lemma F_15eb0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f50 : word) = Some W_15eb0.
Proof. vm_refl. Qed.
Lemma D_15eb0 : decode_any W_15eb0 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eb4 : bv 32 := 0x0306e663.
Lemma F_15eb4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f54 : word) = Some W_15eb4.
Proof. vm_refl. Qed.
Lemma D_15eb4 : decode_any W_15eb4 = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eb8 : bv 32 := 0x00500693.
Lemma F_15eb8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f58 : word) = Some W_15eb8.
Proof. vm_refl. Qed.
Lemma D_15eb8 : decode_any W_15eb8 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ebc : bv 32 := 0x00d70463.
Lemma F_15ebc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f5c : word) = Some W_15ebc.
Proof. vm_refl. Qed.
Lemma D_15ebc : decode_any W_15ebc = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ec4 : bv 32 := 0x0087e703.
Lemma F_15ec4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f64 : word) = Some W_15ec4.
Proof. vm_refl. Qed.
Lemma D_15ec4 : decode_any W_15ec4 = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ec8 : bv 32 := 0x00400693.
Lemma F_15ec8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f68 : word) = Some W_15ec8.
Proof. vm_refl. Qed.
Lemma D_15ec8 : decode_any W_15ec8 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ecc : bv 32 := 0x00e6e463.
Lemma F_15ecc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f6c : word) = Some W_15ecc.
Proof. vm_refl. Qed.
Lemma D_15ecc : decode_any W_15ecc = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ed4 : bv 32 := 0x0077c683.
Lemma F_15ed4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f74 : word) = Some W_15ed4.
Proof. vm_refl. Qed.
Lemma D_15ed4 : decode_any W_15ed4 = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ed8 : bv 32 := 0x00068463.
Lemma F_15ed8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f78 : word) = Some W_15ed8.
Proof. vm_refl. Qed.
Lemma D_15ed8 : decode_any W_15ed8 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ee0 : bv 32 := 0x409606b3.
Lemma F_15ee0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f80 : word) = Some W_15ee0.
Proof. vm_refl. Qed.
Lemma D_15ee0 : decode_any W_15ee0 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ee4 : bv 32 := 0x00e6f463.
Lemma F_15ee4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f84 : word) = Some W_15ee4.
Proof. vm_refl. Qed.
Lemma D_15ee4 : decode_any W_15ee4 = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eec : bv 32 := 0x40e606b3.
Lemma F_15eec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f8c : word) = Some W_15eec.
Proof. vm_refl. Qed.
Lemma D_15eec : decode_any W_15eec = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ef0 : bv 32 := 0x0006c683.
Lemma F_15ef0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f90 : word) = Some W_15ef0.
Proof. vm_refl. Qed.
Lemma D_15ef0 : decode_any W_15ef0 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ef4 : bv 32 := 0x00068463.
Lemma F_15ef4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f94 : word) = Some W_15ef4.
Proof. vm_refl. Qed.
Lemma D_15ef4 : decode_any W_15ef4 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15efc : bv 32 := 0x00064603.
Lemma F_15efc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15f9c : word) = Some W_15efc.
Proof. vm_refl. Qed.
Lemma D_15efc : decode_any W_15efc = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f00 : bv 32 := 0x00060463.
Lemma F_15f00 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x15fa0 : word) = Some W_15f00.
Proof. vm_refl. Qed.
Lemma D_15f00 : decode_any W_15f00 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ff8 : bv 32 := 0x00f57593.
Lemma F_15ff8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x16098 : word) = Some W_15ff8.
Proof. vm_refl. Qed.
Lemma D_15ff8 : decode_any W_15ff8 = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ffc : bv 32 := 0x00058463.
Lemma F_15ffc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1609c : word) = Some W_15ffc.
Proof. vm_refl. Qed.
Lemma D_15ffc : decode_any W_15ffc = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.
