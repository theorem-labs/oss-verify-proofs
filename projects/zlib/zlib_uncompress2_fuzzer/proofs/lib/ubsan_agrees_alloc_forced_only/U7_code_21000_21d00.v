(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_21324 : bv 32 := 0x0035f693.
Lemma F_21324 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21470 : word) = Some W_21324.
Proof. vm_refl. Qed.
Lemma D_21324 : decode_any W_21324 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21328 : bv 32 := 0x10068863.
Lemma F_21328 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21474 : word) = Some W_21328.
Proof. vm_refl. Qed.
Lemma D_21328 : decode_any W_21328 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_2132c : bv 32 := 0x02060e63.
Lemma F_2132c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21478 : word) = Some W_2132c.
Proof. vm_refl. Qed.
Lemma D_2132c : decode_any W_2132c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_21330 : bv 32 := 0x00158713.
Lemma F_21330 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2147c : word) = Some W_21330.
Proof. vm_refl. Qed.
Lemma D_21330 : decode_any W_21330 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21334 : bv 32 := 0x00100793.
Lemma F_21334 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21480 : word) = Some W_21334.
Proof. vm_refl. Qed.
Lemma D_21334 : decode_any W_21334 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21338 : bv 32 := 0x00050693.
Lemma F_21338 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21484 : word) = Some W_21338.
Proof. vm_refl. Qed.
Lemma D_21338 : decode_any W_21338 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2133c : bv 32 := 0x0005c883.
Lemma F_2133c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21488 : word) = Some W_2133c.
Proof. vm_refl. Qed.
Lemma D_2133c : decode_any W_2133c = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21340 : bv 32 := 0x00060813.
Lemma F_21340 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2148c : word) = Some W_21340.
Proof. vm_refl. Qed.
Lemma D_21340 : decode_any W_21340 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21344 : bv 32 := 0x00158593.
Lemma F_21344 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21490 : word) = Some W_21344.
Proof. vm_refl. Qed.
Lemma D_21344 : decode_any W_21344 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21348 : bv 32 := 0x00377293.
Lemma F_21348 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21494 : word) = Some W_21348.
Proof. vm_refl. Qed.
Lemma D_21348 : decode_any W_21348 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_2134c : bv 32 := 0x01168023.
Lemma F_2134c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21498 : word) = Some W_2134c.
Proof. vm_refl. Qed.
Lemma D_2134c : decode_any W_2134c = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21350 : bv 32 := 0x00168693.
Lemma F_21350 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2149c : word) = Some W_21350.
Proof. vm_refl. Qed.
Lemma D_21350 : decode_any W_21350 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21354 : bv 32 := 0xfff60613.
Lemma F_21354 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214a0 : word) = Some W_21354.
Proof. vm_refl. Qed.
Lemma D_21354 : decode_any W_21354 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_21358 : bv 32 := 0x00028a63.
Lemma F_21358 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214a4 : word) = Some W_21358.
Proof. vm_refl. Qed.
Lemma D_21358 : decode_any W_21358 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_2135c : bv 32 := 0x00170713.
Lemma F_2135c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214a8 : word) = Some W_2135c.
Proof. vm_refl. Qed.
Lemma D_2135c : decode_any W_2135c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21360 : bv 32 := 0xfcf81ee3.
Lemma F_21360 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214ac : word) = Some W_21360.
Proof. vm_refl. Qed.
Lemma D_21360 : decode_any W_21360 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_21364 : bv 32 := 0x0080006f.
Lemma F_21364 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214b0 : word) = Some W_21364.
Proof. vm_refl. Qed.
Lemma D_21364 : decode_any W_21364 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21368 : bv 32 := 0x00050693.
Lemma F_21368 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214b4 : word) = Some W_21368.
Proof. vm_refl. Qed.
Lemma D_21368 : decode_any W_21368 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2136c : bv 32 := 0x0036f793.
Lemma F_2136c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214b8 : word) = Some W_2136c.
Proof. vm_refl. Qed.
Lemma D_2136c : decode_any W_2136c = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21370 : bv 32 := 0x0c078a63.
Lemma F_21370 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214bc : word) = Some W_21370.
Proof. vm_refl. Qed.
Lemma D_21370 : decode_any W_21370 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_21374 : bv 32 := 0x02000713.
Lemma F_21374 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214c0 : word) = Some W_21374.
Proof. vm_refl. Qed.
Lemma D_21374 : decode_any W_21374 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_21378 : bv 32 := 0x02e67063.
Lemma F_21378 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214c4 : word) = Some W_21378.
Proof. vm_refl. Qed.
Lemma D_21378 : decode_any W_21378 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_2137c : bv 32 := 0x01000713.
Lemma F_2137c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214c8 : word) = Some W_2137c.
Proof. vm_refl. Qed.
Lemma D_2137c : decode_any W_2137c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21380 : bv 32 := 0x24e67863.
Lemma F_21380 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214cc : word) = Some W_21380.
Proof. vm_refl. Qed.
Lemma D_21380 : decode_any W_21380 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_21384 : bv 32 := 0x00867713.
Lemma F_21384 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214d0 : word) = Some W_21384.
Proof. vm_refl. Qed.
Lemma D_21384 : decode_any W_21384 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21388 : bv 32 := 0x2c071e63.
Lemma F_21388 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214d4 : word) = Some W_21388.
Proof. vm_refl. Qed.
Lemma D_21388 : decode_any W_21388 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_2138c : bv 32 := 0x00467713.
Lemma F_2138c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214d8 : word) = Some W_2138c.
Proof. vm_refl. Qed.
Lemma D_2138c : decode_any W_2138c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21390 : bv 32 := 0x32071463.
Lemma F_21390 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214dc : word) = Some W_21390.
Proof. vm_refl. Qed.
Lemma D_21390 : decode_any W_21390 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_21394 : bv 32 := 0x3500006f.
Lemma F_21394 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214e0 : word) = Some W_21394.
Proof. vm_refl. Qed.
Lemma D_21394 : decode_any W_21394 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_21398 : bv 32 := 0x0005a703.
Lemma F_21398 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214e4 : word) = Some W_21398.
Proof. vm_refl. Qed.
Lemma D_21398 : decode_any W_21398 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2139c : bv 32 := 0x00300813.
Lemma F_2139c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214e8 : word) = Some W_2139c.
Proof. vm_refl. Qed.
Lemma D_2139c : decode_any W_2139c = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_213a0 : bv 32 := 0x11078e63.
Lemma F_213a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214ec : word) = Some W_213a0.
Proof. vm_refl. Qed.
Lemma D_213a0 : decode_any W_213a0 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_213a4 : bv 32 := 0x00200813.
Lemma F_213a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214f0 : word) = Some W_213a4.
Proof. vm_refl. Qed.
Lemma D_213a4 : decode_any W_213a4 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_213a8 : bv 32 := 0x19079c63.
Lemma F_213a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214f4 : word) = Some W_213a8.
Proof. vm_refl. Qed.
Lemma D_213a8 : decode_any W_213a8 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_213ac : bv 32 := 0x00875793.
Lemma F_213ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214f8 : word) = Some W_213ac.
Proof. vm_refl. Qed.
Lemma D_213ac : decode_any W_213ac = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_213b0 : bv 32 := 0xffe60613.
Lemma F_213b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x214fc : word) = Some W_213b0.
Proof. vm_refl. Qed.
Lemma D_213b0 : decode_any W_213b0 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_213b4 : bv 32 := 0x00e68023.
Lemma F_213b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21500 : word) = Some W_213b4.
Proof. vm_refl. Qed.
Lemma D_213b4 : decode_any W_213b4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_213b8 : bv 32 := 0x00f680a3.
Lemma F_213b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21504 : word) = Some W_213b8.
Proof. vm_refl. Qed.
Lemma D_213b8 : decode_any W_213b8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_213bc : bv 32 := 0x00268693.
Lemma F_213bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21508 : word) = Some W_213bc.
Proof. vm_refl. Qed.
Lemma D_213bc : decode_any W_213bc = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_213c0 : bv 32 := 0x01058593.
Lemma F_213c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2150c : word) = Some W_213c0.
Proof. vm_refl. Qed.
Lemma D_213c0 : decode_any W_213c0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_213c4 : bv 32 := 0x01100793.
Lemma F_213c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21510 : word) = Some W_213c4.
Proof. vm_refl. Qed.
Lemma D_213c4 : decode_any W_213c4 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_213c8 : bv 32 := 0x0107581b.
Lemma F_213c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21514 : word) = Some W_213c8.
Proof. vm_refl. Qed.
Lemma D_213c8 : decode_any W_213c8 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_213cc : bv 32 := 0xff45a883.
Lemma F_213cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21518 : word) = Some W_213cc.
Proof. vm_refl. Qed.
Lemma D_213cc : decode_any W_213cc = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_213d0 : bv 32 := 0xff85a283.
Lemma F_213d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2151c : word) = Some W_213d0.
Proof. vm_refl. Qed.
Lemma D_213d0 : decode_any W_213d0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_213d4 : bv 32 := 0xffc5a303.
Lemma F_213d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21520 : word) = Some W_213d4.
Proof. vm_refl. Qed.
Lemma D_213d4 : decode_any W_213d4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_213d8 : bv 32 := 0x0005a703.
Lemma F_213d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21524 : word) = Some W_213d8.
Proof. vm_refl. Qed.
Lemma D_213d8 : decode_any W_213d8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_213dc : bv 32 := 0x01089393.
Lemma F_213dc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21528 : word) = Some W_213dc.
Proof. vm_refl. Qed.
Lemma D_213dc : decode_any W_213dc = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_213e0 : bv 32 := 0x0108d89b.
Lemma F_213e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2152c : word) = Some W_213e0.
Proof. vm_refl. Qed.
Lemma D_213e0 : decode_any W_213e0 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_213e4 : bv 32 := 0x0103e833.
Lemma F_213e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21530 : word) = Some W_213e4.
Proof. vm_refl. Qed.
Lemma D_213e4 : decode_any W_213e4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_213e8 : bv 32 := 0x01029393.
Lemma F_213e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21534 : word) = Some W_213e8.
Proof. vm_refl. Qed.
Lemma D_213e8 : decode_any W_213e8 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_213ec : bv 32 := 0x0102d29b.
Lemma F_213ec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21538 : word) = Some W_213ec.
Proof. vm_refl. Qed.
Lemma D_213ec : decode_any W_213ec = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_213f0 : bv 32 := 0x0113e8b3.
Lemma F_213f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2153c : word) = Some W_213f0.
Proof. vm_refl. Qed.
Lemma D_213f0 : decode_any W_213f0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_213f4 : bv 32 := 0x01031393.
Lemma F_213f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21540 : word) = Some W_213f4.
Proof. vm_refl. Qed.
Lemma D_213f4 : decode_any W_213f4 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_213f8 : bv 32 := 0x0103531b.
Lemma F_213f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21544 : word) = Some W_213f8.
Proof. vm_refl. Qed.
Lemma D_213f8 : decode_any W_213f8 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_213fc : bv 32 := 0x0053e2b3.
Lemma F_213fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21548 : word) = Some W_213fc.
Proof. vm_refl. Qed.
Lemma D_213fc : decode_any W_213fc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_21400 : bv 32 := 0x01071393.
Lemma F_21400 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2154c : word) = Some W_21400.
Proof. vm_refl. Qed.
Lemma D_21400 : decode_any W_21400 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21404 : bv 32 := 0x0063e333.
Lemma F_21404 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21550 : word) = Some W_21404.
Proof. vm_refl. Qed.
Lemma D_21404 : decode_any W_21404 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_21408 : bv 32 := 0xff060613.
Lemma F_21408 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21554 : word) = Some W_21408.
Proof. vm_refl. Qed.
Lemma D_21408 : decode_any W_21408 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_2140c : bv 32 := 0x0106a023.
Lemma F_2140c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21558 : word) = Some W_2140c.
Proof. vm_refl. Qed.
Lemma D_2140c : decode_any W_2140c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21410 : bv 32 := 0x0116a223.
Lemma F_21410 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2155c : word) = Some W_21410.
Proof. vm_refl. Qed.
Lemma D_21410 : decode_any W_21410 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21414 : bv 32 := 0x0056a423.
Lemma F_21414 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21560 : word) = Some W_21414.
Proof. vm_refl. Qed.
Lemma D_21414 : decode_any W_21414 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21418 : bv 32 := 0x0066a623.
Lemma F_21418 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21564 : word) = Some W_21418.
Proof. vm_refl. Qed.
Lemma D_21418 : decode_any W_21418 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_2141c : bv 32 := 0x01068693.
Lemma F_2141c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21568 : word) = Some W_2141c.
Proof. vm_refl. Qed.
Lemma D_2141c : decode_any W_2141c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21420 : bv 32 := 0x01058593.
Lemma F_21420 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2156c : word) = Some W_21420.
Proof. vm_refl. Qed.
Lemma D_21420 : decode_any W_21420 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21424 : bv 32 := 0xfac7e2e3.
Lemma F_21424 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21570 : word) = Some W_21424.
Proof. vm_refl. Qed.
Lemma D_21424 : decode_any W_21424 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_21428 : bv 32 := 0xff258593.
Lemma F_21428 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21574 : word) = Some W_21428.
Proof. vm_refl. Qed.
Lemma D_21428 : decode_any W_21428 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_2142c : bv 32 := 0x01000713.
Lemma F_2142c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21578 : word) = Some W_2142c.
Proof. vm_refl. Qed.
Lemma D_2142c : decode_any W_2142c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21430 : bv 32 := 0xf4e66ae3.
Lemma F_21430 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2157c : word) = Some W_21430.
Proof. vm_refl. Qed.
Lemma D_21430 : decode_any W_21430 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_21434 : bv 32 := 0x19c0006f.
Lemma F_21434 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21580 : word) = Some W_21434.
Proof. vm_refl. Qed.
Lemma D_21434 : decode_any W_21434 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_21438 : bv 32 := 0x00050693.
Lemma F_21438 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21584 : word) = Some W_21438.
Proof. vm_refl. Qed.
Lemma D_21438 : decode_any W_21438 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2143c : bv 32 := 0x00357793.
Lemma F_2143c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21588 : word) = Some W_2143c.
Proof. vm_refl. Qed.
Lemma D_2143c : decode_any W_2143c = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21440 : bv 32 := 0xf2079ae3.
Lemma F_21440 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2158c : word) = Some W_21440.
Proof. vm_refl. Qed.
Lemma D_21440 : decode_any W_21440 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_21444 : bv 32 := 0x01000713.
Lemma F_21444 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21590 : word) = Some W_21444.
Proof. vm_refl. Qed.
Lemma D_21444 : decode_any W_21444 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21448 : bv 32 := 0x02e66c63.
Lemma F_21448 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21594 : word) = Some W_21448.
Proof. vm_refl. Qed.
Lemma D_21448 : decode_any W_21448 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_2144c : bv 32 := 0x00f00713.
Lemma F_2144c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21598 : word) = Some W_2144c.
Proof. vm_refl. Qed.
Lemma D_2144c : decode_any W_2144c = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_21450 : bv 32 := 0x0005a783.
Lemma F_21450 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2159c : word) = Some W_21450.
Proof. vm_refl. Qed.
Lemma D_21450 : decode_any W_21450 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21454 : bv 32 := 0x0045a803.
Lemma F_21454 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215a0 : word) = Some W_21454.
Proof. vm_refl. Qed.
Lemma D_21454 : decode_any W_21454 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21458 : bv 32 := 0x0085a883.
Lemma F_21458 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215a4 : word) = Some W_21458.
Proof. vm_refl. Qed.
Lemma D_21458 : decode_any W_21458 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2145c : bv 32 := 0x00c5a283.
Lemma F_2145c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215a8 : word) = Some W_2145c.
Proof. vm_refl. Qed.
Lemma D_2145c : decode_any W_2145c = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21460 : bv 32 := 0x01058593.
Lemma F_21460 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215ac : word) = Some W_21460.
Proof. vm_refl. Qed.
Lemma D_21460 : decode_any W_21460 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21464 : bv 32 := 0xff060613.
Lemma F_21464 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215b0 : word) = Some W_21464.
Proof. vm_refl. Qed.
Lemma D_21464 : decode_any W_21464 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_21468 : bv 32 := 0x00f6a023.
Lemma F_21468 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215b4 : word) = Some W_21468.
Proof. vm_refl. Qed.
Lemma D_21468 : decode_any W_21468 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2146c : bv 32 := 0x0106a223.
Lemma F_2146c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215b8 : word) = Some W_2146c.
Proof. vm_refl. Qed.
Lemma D_2146c : decode_any W_2146c = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21470 : bv 32 := 0x0116a423.
Lemma F_21470 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215bc : word) = Some W_21470.
Proof. vm_refl. Qed.
Lemma D_21470 : decode_any W_21470 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21474 : bv 32 := 0x0056a623.
Lemma F_21474 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215c0 : word) = Some W_21474.
Proof. vm_refl. Qed.
Lemma D_21474 : decode_any W_21474 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21478 : bv 32 := 0x01068693.
Lemma F_21478 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215c4 : word) = Some W_21478.
Proof. vm_refl. Qed.
Lemma D_21478 : decode_any W_21478 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2147c : bv 32 := 0xfcc76ae3.
Lemma F_2147c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215c8 : word) = Some W_2147c.
Proof. vm_refl. Qed.
Lemma D_2147c : decode_any W_2147c = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_21480 : bv 32 := 0x00800713.
Lemma F_21480 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215cc : word) = Some W_21480.
Proof. vm_refl. Qed.
Lemma D_21480 : decode_any W_21480 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21484 : bv 32 := 0x00e66e63.
Lemma F_21484 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215d0 : word) = Some W_21484.
Proof. vm_refl. Qed.
Lemma D_21484 : decode_any W_21484 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_21488 : bv 32 := 0x0005a703.
Lemma F_21488 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215d4 : word) = Some W_21488.
Proof. vm_refl. Qed.
Lemma D_21488 : decode_any W_21488 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2148c : bv 32 := 0x0045a783.
Lemma F_2148c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215d8 : word) = Some W_2148c.
Proof. vm_refl. Qed.
Lemma D_2148c : decode_any W_2148c = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21490 : bv 32 := 0x00e6a023.
Lemma F_21490 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215dc : word) = Some W_21490.
Proof. vm_refl. Qed.
Lemma D_21490 : decode_any W_21490 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21494 : bv 32 := 0x00f6a223.
Lemma F_21494 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215e0 : word) = Some W_21494.
Proof. vm_refl. Qed.
Lemma D_21494 : decode_any W_21494 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21498 : bv 32 := 0x00868693.
Lemma F_21498 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215e4 : word) = Some W_21498.
Proof. vm_refl. Qed.
Lemma D_21498 : decode_any W_21498 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2149c : bv 32 := 0x00858593.
Lemma F_2149c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215e8 : word) = Some W_2149c.
Proof. vm_refl. Qed.
Lemma D_2149c : decode_any W_2149c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_214a0 : bv 32 := 0x00467713.
Lemma F_214a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215ec : word) = Some W_214a0.
Proof. vm_refl. Qed.
Lemma D_214a0 : decode_any W_214a0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_214a4 : bv 32 := 0x24070063.
Lemma F_214a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215f0 : word) = Some W_214a4.
Proof. vm_refl. Qed.
Lemma D_214a4 : decode_any W_214a4 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_214a8 : bv 32 := 0x0005a703.
Lemma F_214a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215f4 : word) = Some W_214a8.
Proof. vm_refl. Qed.
Lemma D_214a8 : decode_any W_214a8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_214ac : bv 32 := 0x00458593.
Lemma F_214ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215f8 : word) = Some W_214ac.
Proof. vm_refl. Qed.
Lemma D_214ac : decode_any W_214ac = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_214b0 : bv 32 := 0x00e6a023.
Lemma F_214b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x215fc : word) = Some W_214b0.
Proof. vm_refl. Qed.
Lemma D_214b0 : decode_any W_214b0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_214b4 : bv 32 := 0x00468693.
Lemma F_214b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21600 : word) = Some W_214b4.
Proof. vm_refl. Qed.
Lemma D_214b4 : decode_any W_214b4 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_214b8 : bv 32 := 0x22c0006f.
Lemma F_214b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21604 : word) = Some W_214b8.
Proof. vm_refl. Qed.
Lemma D_214b8 : decode_any W_214b8 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_214bc : bv 32 := 0x00e68023.
Lemma F_214bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21608 : word) = Some W_214bc.
Proof. vm_refl. Qed.
Lemma D_214bc : decode_any W_214bc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_214c0 : bv 32 := 0x00168693.
Lemma F_214c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2160c : word) = Some W_214c0.
Proof. vm_refl. Qed.
Lemma D_214c0 : decode_any W_214c0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_214c4 : bv 32 := 0xfff60613.
Lemma F_214c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21610 : word) = Some W_214c4.
Proof. vm_refl. Qed.
Lemma D_214c4 : decode_any W_214c4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_214c8 : bv 32 := 0x01058593.
Lemma F_214c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21614 : word) = Some W_214c8.
Proof. vm_refl. Qed.
Lemma D_214c8 : decode_any W_214c8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_214cc : bv 32 := 0x01200793.
Lemma F_214cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21618 : word) = Some W_214cc.
Proof. vm_refl. Qed.
Lemma D_214cc : decode_any W_214cc = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_214d0 : bv 32 := 0x0087581b.
Lemma F_214d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2161c : word) = Some W_214d0.
Proof. vm_refl. Qed.
Lemma D_214d0 : decode_any W_214d0 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_214d4 : bv 32 := 0xff45a883.
Lemma F_214d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21620 : word) = Some W_214d4.
Proof. vm_refl. Qed.
Lemma D_214d4 : decode_any W_214d4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_214d8 : bv 32 := 0xff85a283.
Lemma F_214d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21624 : word) = Some W_214d8.
Proof. vm_refl. Qed.
Lemma D_214d8 : decode_any W_214d8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_214dc : bv 32 := 0xffc5a303.
Lemma F_214dc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21628 : word) = Some W_214dc.
Proof. vm_refl. Qed.
Lemma D_214dc : decode_any W_214dc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_214e0 : bv 32 := 0x0005a703.
Lemma F_214e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2162c : word) = Some W_214e0.
Proof. vm_refl. Qed.
Lemma D_214e0 : decode_any W_214e0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_214e4 : bv 32 := 0x01889393.
Lemma F_214e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21630 : word) = Some W_214e4.
Proof. vm_refl. Qed.
Lemma D_214e4 : decode_any W_214e4 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_214e8 : bv 32 := 0x0088d89b.
Lemma F_214e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21634 : word) = Some W_214e8.
Proof. vm_refl. Qed.
Lemma D_214e8 : decode_any W_214e8 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_214ec : bv 32 := 0x0103e833.
Lemma F_214ec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21638 : word) = Some W_214ec.
Proof. vm_refl. Qed.
Lemma D_214ec : decode_any W_214ec = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_214f0 : bv 32 := 0x01829393.
Lemma F_214f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2163c : word) = Some W_214f0.
Proof. vm_refl. Qed.
Lemma D_214f0 : decode_any W_214f0 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_214f4 : bv 32 := 0x0082d29b.
Lemma F_214f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21640 : word) = Some W_214f4.
Proof. vm_refl. Qed.
Lemma D_214f4 : decode_any W_214f4 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_214f8 : bv 32 := 0x0113e8b3.
Lemma F_214f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21644 : word) = Some W_214f8.
Proof. vm_refl. Qed.
Lemma D_214f8 : decode_any W_214f8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_214fc : bv 32 := 0x01831393.
Lemma F_214fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21648 : word) = Some W_214fc.
Proof. vm_refl. Qed.
Lemma D_214fc : decode_any W_214fc = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21500 : bv 32 := 0x0083531b.
Lemma F_21500 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2164c : word) = Some W_21500.
Proof. vm_refl. Qed.
Lemma D_21500 : decode_any W_21500 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21504 : bv 32 := 0x0053e2b3.
Lemma F_21504 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21650 : word) = Some W_21504.
Proof. vm_refl. Qed.
Lemma D_21504 : decode_any W_21504 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_21508 : bv 32 := 0x01871393.
Lemma F_21508 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21654 : word) = Some W_21508.
Proof. vm_refl. Qed.
Lemma D_21508 : decode_any W_21508 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_2150c : bv 32 := 0x0063e333.
Lemma F_2150c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21658 : word) = Some W_2150c.
Proof. vm_refl. Qed.
Lemma D_2150c : decode_any W_2150c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_21510 : bv 32 := 0xff060613.
Lemma F_21510 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2165c : word) = Some W_21510.
Proof. vm_refl. Qed.
Lemma D_21510 : decode_any W_21510 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_21514 : bv 32 := 0x0106a023.
Lemma F_21514 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21660 : word) = Some W_21514.
Proof. vm_refl. Qed.
Lemma D_21514 : decode_any W_21514 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21518 : bv 32 := 0x0116a223.
Lemma F_21518 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21664 : word) = Some W_21518.
Proof. vm_refl. Qed.
Lemma D_21518 : decode_any W_21518 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_2151c : bv 32 := 0x0056a423.
Lemma F_2151c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21668 : word) = Some W_2151c.
Proof. vm_refl. Qed.
Lemma D_2151c : decode_any W_2151c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21520 : bv 32 := 0x0066a623.
Lemma F_21520 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2166c : word) = Some W_21520.
Proof. vm_refl. Qed.
Lemma D_21520 : decode_any W_21520 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21524 : bv 32 := 0x01068693.
Lemma F_21524 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21670 : word) = Some W_21524.
Proof. vm_refl. Qed.
Lemma D_21524 : decode_any W_21524 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21528 : bv 32 := 0x01058593.
Lemma F_21528 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21674 : word) = Some W_21528.
Proof. vm_refl. Qed.
Lemma D_21528 : decode_any W_21528 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2152c : bv 32 := 0xfac7e2e3.
Lemma F_2152c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21678 : word) = Some W_2152c.
Proof. vm_refl. Qed.
Lemma D_2152c : decode_any W_2152c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_21530 : bv 32 := 0xff158593.
Lemma F_21530 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2167c : word) = Some W_21530.
Proof. vm_refl. Qed.
Lemma D_21530 : decode_any W_21530 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_21534 : bv 32 := 0x01000713.
Lemma F_21534 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21680 : word) = Some W_21534.
Proof. vm_refl. Qed.
Lemma D_21534 : decode_any W_21534 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21538 : bv 32 := 0xe4e666e3.
Lemma F_21538 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21684 : word) = Some W_21538.
Proof. vm_refl. Qed.
Lemma D_21538 : decode_any W_21538 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_2153c : bv 32 := 0x0940006f.
Lemma F_2153c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21688 : word) = Some W_2153c.
Proof. vm_refl. Qed.
Lemma D_2153c : decode_any W_2153c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_21540 : bv 32 := 0x00875793.
Lemma F_21540 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2168c : word) = Some W_21540.
Proof. vm_refl. Qed.
Lemma D_21540 : decode_any W_21540 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21544 : bv 32 := 0x01075813.
Lemma F_21544 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21690 : word) = Some W_21544.
Proof. vm_refl. Qed.
Lemma D_21544 : decode_any W_21544 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21548 : bv 32 := 0xffd60613.
Lemma F_21548 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21694 : word) = Some W_21548.
Proof. vm_refl. Qed.
Lemma D_21548 : decode_any W_21548 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_2154c : bv 32 := 0x00e68023.
Lemma F_2154c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21698 : word) = Some W_2154c.
Proof. vm_refl. Qed.
Lemma D_2154c : decode_any W_2154c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21550 : bv 32 := 0x00f680a3.
Lemma F_21550 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2169c : word) = Some W_21550.
Proof. vm_refl. Qed.
Lemma D_21550 : decode_any W_21550 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21554 : bv 32 := 0x01068123.
Lemma F_21554 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216a0 : word) = Some W_21554.
Proof. vm_refl. Qed.
Lemma D_21554 : decode_any W_21554 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21558 : bv 32 := 0x00368693.
Lemma F_21558 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216a4 : word) = Some W_21558.
Proof. vm_refl. Qed.
Lemma D_21558 : decode_any W_21558 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_2155c : bv 32 := 0x01058593.
Lemma F_2155c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216a8 : word) = Some W_2155c.
Proof. vm_refl. Qed.
Lemma D_2155c : decode_any W_2155c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21560 : bv 32 := 0x01000793.
Lemma F_21560 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216ac : word) = Some W_21560.
Proof. vm_refl. Qed.
Lemma D_21560 : decode_any W_21560 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21564 : bv 32 := 0x0187581b.
Lemma F_21564 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216b0 : word) = Some W_21564.
Proof. vm_refl. Qed.
Lemma D_21564 : decode_any W_21564 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21568 : bv 32 := 0xff45a883.
Lemma F_21568 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216b4 : word) = Some W_21568.
Proof. vm_refl. Qed.
Lemma D_21568 : decode_any W_21568 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_2156c : bv 32 := 0xff85a283.
Lemma F_2156c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216b8 : word) = Some W_2156c.
Proof. vm_refl. Qed.
Lemma D_2156c : decode_any W_2156c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_21570 : bv 32 := 0xffc5a303.
Lemma F_21570 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216bc : word) = Some W_21570.
Proof. vm_refl. Qed.
Lemma D_21570 : decode_any W_21570 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_21574 : bv 32 := 0x0005a703.
Lemma F_21574 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216c0 : word) = Some W_21574.
Proof. vm_refl. Qed.
Lemma D_21574 : decode_any W_21574 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21578 : bv 32 := 0x00889393.
Lemma F_21578 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216c4 : word) = Some W_21578.
Proof. vm_refl. Qed.
Lemma D_21578 : decode_any W_21578 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2157c : bv 32 := 0x0188d89b.
Lemma F_2157c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216c8 : word) = Some W_2157c.
Proof. vm_refl. Qed.
Lemma D_2157c : decode_any W_2157c = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21580 : bv 32 := 0x0103e833.
Lemma F_21580 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216cc : word) = Some W_21580.
Proof. vm_refl. Qed.
Lemma D_21580 : decode_any W_21580 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21584 : bv 32 := 0x00829393.
Lemma F_21584 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216d0 : word) = Some W_21584.
Proof. vm_refl. Qed.
Lemma D_21584 : decode_any W_21584 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21588 : bv 32 := 0x0182d29b.
Lemma F_21588 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216d4 : word) = Some W_21588.
Proof. vm_refl. Qed.
Lemma D_21588 : decode_any W_21588 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_2158c : bv 32 := 0x0113e8b3.
Lemma F_2158c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216d8 : word) = Some W_2158c.
Proof. vm_refl. Qed.
Lemma D_2158c : decode_any W_2158c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_21590 : bv 32 := 0x00831393.
Lemma F_21590 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216dc : word) = Some W_21590.
Proof. vm_refl. Qed.
Lemma D_21590 : decode_any W_21590 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21594 : bv 32 := 0x0183531b.
Lemma F_21594 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216e0 : word) = Some W_21594.
Proof. vm_refl. Qed.
Lemma D_21594 : decode_any W_21594 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21598 : bv 32 := 0x0053e2b3.
Lemma F_21598 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216e4 : word) = Some W_21598.
Proof. vm_refl. Qed.
Lemma D_21598 : decode_any W_21598 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_2159c : bv 32 := 0x00871393.
Lemma F_2159c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216e8 : word) = Some W_2159c.
Proof. vm_refl. Qed.
Lemma D_2159c : decode_any W_2159c = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_215a0 : bv 32 := 0x0063e333.
Lemma F_215a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216ec : word) = Some W_215a0.
Proof. vm_refl. Qed.
Lemma D_215a0 : decode_any W_215a0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_215a4 : bv 32 := 0xff060613.
Lemma F_215a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216f0 : word) = Some W_215a4.
Proof. vm_refl. Qed.
Lemma D_215a4 : decode_any W_215a4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_215a8 : bv 32 := 0x0106a023.
Lemma F_215a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216f4 : word) = Some W_215a8.
Proof. vm_refl. Qed.
Lemma D_215a8 : decode_any W_215a8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_215ac : bv 32 := 0x0116a223.
Lemma F_215ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216f8 : word) = Some W_215ac.
Proof. vm_refl. Qed.
Lemma D_215ac : decode_any W_215ac = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_215b0 : bv 32 := 0x0056a423.
Lemma F_215b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x216fc : word) = Some W_215b0.
Proof. vm_refl. Qed.
Lemma D_215b0 : decode_any W_215b0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_215b4 : bv 32 := 0x0066a623.
Lemma F_215b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21700 : word) = Some W_215b4.
Proof. vm_refl. Qed.
Lemma D_215b4 : decode_any W_215b4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_215b8 : bv 32 := 0x01068693.
Lemma F_215b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21704 : word) = Some W_215b8.
Proof. vm_refl. Qed.
Lemma D_215b8 : decode_any W_215b8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_215bc : bv 32 := 0x01058593.
Lemma F_215bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21708 : word) = Some W_215bc.
Proof. vm_refl. Qed.
Lemma D_215bc : decode_any W_215bc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_215c0 : bv 32 := 0xfac7e2e3.
Lemma F_215c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2170c : word) = Some W_215c0.
Proof. vm_refl. Qed.
Lemma D_215c0 : decode_any W_215c0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_215c4 : bv 32 := 0xff358593.
Lemma F_215c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21710 : word) = Some W_215c4.
Proof. vm_refl. Qed.
Lemma D_215c4 : decode_any W_215c4 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_215c8 : bv 32 := 0x01000713.
Lemma F_215c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21714 : word) = Some W_215c8.
Proof. vm_refl. Qed.
Lemma D_215c8 : decode_any W_215c8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_215cc : bv 32 := 0xdae66ce3.
Lemma F_215cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21718 : word) = Some W_215cc.
Proof. vm_refl. Qed.
Lemma D_215cc : decode_any W_215cc = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_215d0 : bv 32 := 0x0005c703.
Lemma F_215d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2171c : word) = Some W_215d0.
Proof. vm_refl. Qed.
Lemma D_215d0 : decode_any W_215d0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_215d4 : bv 32 := 0x0015c783.
Lemma F_215d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21720 : word) = Some W_215d4.
Proof. vm_refl. Qed.
Lemma D_215d4 : decode_any W_215d4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_215d8 : bv 32 := 0x0025c803.
Lemma F_215d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21724 : word) = Some W_215d8.
Proof. vm_refl. Qed.
Lemma D_215d8 : decode_any W_215d8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_215dc : bv 32 := 0x0035c883.
Lemma F_215dc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21728 : word) = Some W_215dc.
Proof. vm_refl. Qed.
Lemma D_215dc : decode_any W_215dc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_215e0 : bv 32 := 0x0045c283.
Lemma F_215e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2172c : word) = Some W_215e0.
Proof. vm_refl. Qed.
Lemma D_215e0 : decode_any W_215e0 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_215e4 : bv 32 := 0x0055c303.
Lemma F_215e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21730 : word) = Some W_215e4.
Proof. vm_refl. Qed.
Lemma D_215e4 : decode_any W_215e4 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_215e8 : bv 32 := 0x0065c383.
Lemma F_215e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21734 : word) = Some W_215e8.
Proof. vm_refl. Qed.
Lemma D_215e8 : decode_any W_215e8 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_215ec : bv 32 := 0x0075ce03.
Lemma F_215ec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21738 : word) = Some W_215ec.
Proof. vm_refl. Qed.
Lemma D_215ec : decode_any W_215ec = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_215f0 : bv 32 := 0x00e68023.
Lemma F_215f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2173c : word) = Some W_215f0.
Proof. vm_refl. Qed.
Lemma D_215f0 : decode_any W_215f0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_215f4 : bv 32 := 0x00f680a3.
Lemma F_215f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21740 : word) = Some W_215f4.
Proof. vm_refl. Qed.
Lemma D_215f4 : decode_any W_215f4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_215f8 : bv 32 := 0x01068123.
Lemma F_215f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21744 : word) = Some W_215f8.
Proof. vm_refl. Qed.
Lemma D_215f8 : decode_any W_215f8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_215fc : bv 32 := 0x011681a3.
Lemma F_215fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21748 : word) = Some W_215fc.
Proof. vm_refl. Qed.
Lemma D_215fc : decode_any W_215fc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21600 : bv 32 := 0x0085c703.
Lemma F_21600 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2174c : word) = Some W_21600.
Proof. vm_refl. Qed.
Lemma D_21600 : decode_any W_21600 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21604 : bv 32 := 0x0095c783.
Lemma F_21604 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21750 : word) = Some W_21604.
Proof. vm_refl. Qed.
Lemma D_21604 : decode_any W_21604 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_21608 : bv 32 := 0x00a5c803.
Lemma F_21608 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21754 : word) = Some W_21608.
Proof. vm_refl. Qed.
Lemma D_21608 : decode_any W_21608 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_2160c : bv 32 := 0x00b5c883.
Lemma F_2160c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21758 : word) = Some W_2160c.
Proof. vm_refl. Qed.
Lemma D_2160c : decode_any W_2160c = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_21610 : bv 32 := 0x00568223.
Lemma F_21610 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2175c : word) = Some W_21610.
Proof. vm_refl. Qed.
Lemma D_21610 : decode_any W_21610 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21614 : bv 32 := 0x006682a3.
Lemma F_21614 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21760 : word) = Some W_21614.
Proof. vm_refl. Qed.
Lemma D_21614 : decode_any W_21614 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_21618 : bv 32 := 0x00768323.
Lemma F_21618 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21764 : word) = Some W_21618.
Proof. vm_refl. Qed.
Lemma D_21618 : decode_any W_21618 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_2161c : bv 32 := 0x01c683a3.
Lemma F_2161c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21768 : word) = Some W_2161c.
Proof. vm_refl. Qed.
Lemma D_2161c : decode_any W_2161c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_21620 : bv 32 := 0x00c5c283.
Lemma F_21620 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2176c : word) = Some W_21620.
Proof. vm_refl. Qed.
Lemma D_21620 : decode_any W_21620 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21624 : bv 32 := 0x00d5c303.
Lemma F_21624 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21770 : word) = Some W_21624.
Proof. vm_refl. Qed.
Lemma D_21624 : decode_any W_21624 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_21628 : bv 32 := 0x00e5c383.
Lemma F_21628 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21774 : word) = Some W_21628.
Proof. vm_refl. Qed.
Lemma D_21628 : decode_any W_21628 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_2162c : bv 32 := 0x00f5ce03.
Lemma F_2162c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21778 : word) = Some W_2162c.
Proof. vm_refl. Qed.
Lemma D_2162c : decode_any W_2162c = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_21630 : bv 32 := 0x01058593.
Lemma F_21630 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2177c : word) = Some W_21630.
Proof. vm_refl. Qed.
Lemma D_21630 : decode_any W_21630 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21634 : bv 32 := 0x00e68423.
Lemma F_21634 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21780 : word) = Some W_21634.
Proof. vm_refl. Qed.
Lemma D_21634 : decode_any W_21634 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21638 : bv 32 := 0x00f684a3.
Lemma F_21638 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21784 : word) = Some W_21638.
Proof. vm_refl. Qed.
Lemma D_21638 : decode_any W_21638 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_2163c : bv 32 := 0x01068523.
Lemma F_2163c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21788 : word) = Some W_2163c.
Proof. vm_refl. Qed.
Lemma D_2163c : decode_any W_2163c = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_21640 : bv 32 := 0x011685a3.
Lemma F_21640 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2178c : word) = Some W_21640.
Proof. vm_refl. Qed.
Lemma D_21640 : decode_any W_21640 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_21644 : bv 32 := 0x01068713.
Lemma F_21644 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21790 : word) = Some W_21644.
Proof. vm_refl. Qed.
Lemma D_21644 : decode_any W_21644 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21648 : bv 32 := 0x00568623.
Lemma F_21648 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21794 : word) = Some W_21648.
Proof. vm_refl. Qed.
Lemma D_21648 : decode_any W_21648 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_2164c : bv 32 := 0x006686a3.
Lemma F_2164c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21798 : word) = Some W_2164c.
Proof. vm_refl. Qed.
Lemma D_2164c : decode_any W_2164c = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_21650 : bv 32 := 0x00768723.
Lemma F_21650 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2179c : word) = Some W_21650.
Proof. vm_refl. Qed.
Lemma D_21650 : decode_any W_21650 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_21654 : bv 32 := 0x01c687a3.
Lemma F_21654 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217a0 : word) = Some W_21654.
Proof. vm_refl. Qed.
Lemma D_21654 : decode_any W_21654 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_21658 : bv 32 := 0x00070693.
Lemma F_21658 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217a4 : word) = Some W_21658.
Proof. vm_refl. Qed.
Lemma D_21658 : decode_any W_21658 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2165c : bv 32 := 0x00867713.
Lemma F_2165c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217a8 : word) = Some W_2165c.
Proof. vm_refl. Qed.
Lemma D_2165c : decode_any W_2165c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21660 : bv 32 := 0xd20706e3.
Lemma F_21660 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217ac : word) = Some W_21660.
Proof. vm_refl. Qed.
Lemma D_21660 : decode_any W_21660 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_21664 : bv 32 := 0x0005c703.
Lemma F_21664 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217b0 : word) = Some W_21664.
Proof. vm_refl. Qed.
Lemma D_21664 : decode_any W_21664 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21668 : bv 32 := 0x0015c783.
Lemma F_21668 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217b4 : word) = Some W_21668.
Proof. vm_refl. Qed.
Lemma D_21668 : decode_any W_21668 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2166c : bv 32 := 0x0025c803.
Lemma F_2166c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217b8 : word) = Some W_2166c.
Proof. vm_refl. Qed.
Lemma D_2166c : decode_any W_2166c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21670 : bv 32 := 0x0035c883.
Lemma F_21670 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217bc : word) = Some W_21670.
Proof. vm_refl. Qed.
Lemma D_21670 : decode_any W_21670 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21674 : bv 32 := 0x0045c283.
Lemma F_21674 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217c0 : word) = Some W_21674.
Proof. vm_refl. Qed.
Lemma D_21674 : decode_any W_21674 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21678 : bv 32 := 0x0055c303.
Lemma F_21678 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217c4 : word) = Some W_21678.
Proof. vm_refl. Qed.
Lemma D_21678 : decode_any W_21678 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_2167c : bv 32 := 0x0065c383.
Lemma F_2167c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217c8 : word) = Some W_2167c.
Proof. vm_refl. Qed.
Lemma D_2167c : decode_any W_2167c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_21680 : bv 32 := 0x0075ce03.
Lemma F_21680 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217cc : word) = Some W_21680.
Proof. vm_refl. Qed.
Lemma D_21680 : decode_any W_21680 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_21684 : bv 32 := 0x00858593.
Lemma F_21684 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217d0 : word) = Some W_21684.
Proof. vm_refl. Qed.
Lemma D_21684 : decode_any W_21684 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21688 : bv 32 := 0x00e68023.
Lemma F_21688 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217d4 : word) = Some W_21688.
Proof. vm_refl. Qed.
Lemma D_21688 : decode_any W_21688 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2168c : bv 32 := 0x00f680a3.
Lemma F_2168c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217d8 : word) = Some W_2168c.
Proof. vm_refl. Qed.
Lemma D_2168c : decode_any W_2168c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21690 : bv 32 := 0x01068123.
Lemma F_21690 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217dc : word) = Some W_21690.
Proof. vm_refl. Qed.
Lemma D_21690 : decode_any W_21690 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21694 : bv 32 := 0x011681a3.
Lemma F_21694 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217e0 : word) = Some W_21694.
Proof. vm_refl. Qed.
Lemma D_21694 : decode_any W_21694 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21698 : bv 32 := 0x00868713.
Lemma F_21698 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217e4 : word) = Some W_21698.
Proof. vm_refl. Qed.
Lemma D_21698 : decode_any W_21698 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2169c : bv 32 := 0x00568223.
Lemma F_2169c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217e8 : word) = Some W_2169c.
Proof. vm_refl. Qed.
Lemma D_2169c : decode_any W_2169c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_216a0 : bv 32 := 0x006682a3.
Lemma F_216a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217ec : word) = Some W_216a0.
Proof. vm_refl. Qed.
Lemma D_216a0 : decode_any W_216a0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_216a4 : bv 32 := 0x00768323.
Lemma F_216a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217f0 : word) = Some W_216a4.
Proof. vm_refl. Qed.
Lemma D_216a4 : decode_any W_216a4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_216a8 : bv 32 := 0x01c683a3.
Lemma F_216a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217f4 : word) = Some W_216a8.
Proof. vm_refl. Qed.
Lemma D_216a8 : decode_any W_216a8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_216ac : bv 32 := 0x00070693.
Lemma F_216ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217f8 : word) = Some W_216ac.
Proof. vm_refl. Qed.
Lemma D_216ac : decode_any W_216ac = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_216b0 : bv 32 := 0x00467713.
Lemma F_216b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x217fc : word) = Some W_216b0.
Proof. vm_refl. Qed.
Lemma D_216b0 : decode_any W_216b0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_216b4 : bv 32 := 0x02070863.
Lemma F_216b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21800 : word) = Some W_216b4.
Proof. vm_refl. Qed.
Lemma D_216b4 : decode_any W_216b4 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_216b8 : bv 32 := 0x0005c703.
Lemma F_216b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21804 : word) = Some W_216b8.
Proof. vm_refl. Qed.
Lemma D_216b8 : decode_any W_216b8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_216bc : bv 32 := 0x0015c783.
Lemma F_216bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21808 : word) = Some W_216bc.
Proof. vm_refl. Qed.
Lemma D_216bc : decode_any W_216bc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_216c0 : bv 32 := 0x0025c803.
Lemma F_216c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2180c : word) = Some W_216c0.
Proof. vm_refl. Qed.
Lemma D_216c0 : decode_any W_216c0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_216c4 : bv 32 := 0x0035c883.
Lemma F_216c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21810 : word) = Some W_216c4.
Proof. vm_refl. Qed.
Lemma D_216c4 : decode_any W_216c4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_216c8 : bv 32 := 0x00458593.
Lemma F_216c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21814 : word) = Some W_216c8.
Proof. vm_refl. Qed.
Lemma D_216c8 : decode_any W_216c8 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_216cc : bv 32 := 0x00468293.
Lemma F_216cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21818 : word) = Some W_216cc.
Proof. vm_refl. Qed.
Lemma D_216cc : decode_any W_216cc = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_216d0 : bv 32 := 0x00e68023.
Lemma F_216d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2181c : word) = Some W_216d0.
Proof. vm_refl. Qed.
Lemma D_216d0 : decode_any W_216d0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_216d4 : bv 32 := 0x00f680a3.
Lemma F_216d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21820 : word) = Some W_216d4.
Proof. vm_refl. Qed.
Lemma D_216d4 : decode_any W_216d4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_216d8 : bv 32 := 0x01068123.
Lemma F_216d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21824 : word) = Some W_216d8.
Proof. vm_refl. Qed.
Lemma D_216d8 : decode_any W_216d8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_216dc : bv 32 := 0x011681a3.
Lemma F_216dc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21828 : word) = Some W_216dc.
Proof. vm_refl. Qed.
Lemma D_216dc : decode_any W_216dc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_216e0 : bv 32 := 0x00028693.
Lemma F_216e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2182c : word) = Some W_216e0.
Proof. vm_refl. Qed.
Lemma D_216e0 : decode_any W_216e0 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_216e4 : bv 32 := 0x00267713.
Lemma F_216e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21830 : word) = Some W_216e4.
Proof. vm_refl. Qed.
Lemma D_216e4 : decode_any W_216e4 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_216e8 : bv 32 := 0x00071863.
Lemma F_216e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21834 : word) = Some W_216e8.
Proof. vm_refl. Qed.
Lemma D_216e8 : decode_any W_216e8 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_216ec : bv 32 := 0x00167613.
Lemma F_216ec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21838 : word) = Some W_216ec.
Proof. vm_refl. Qed.
Lemma D_216ec : decode_any W_216ec = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_216f0 : bv 32 := 0x02061663.
Lemma F_216f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2183c : word) = Some W_216f0.
Proof. vm_refl. Qed.
Lemma D_216f0 : decode_any W_216f0 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_216f4 : bv 32 := 0x00008067.
Lemma F_216f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21840 : word) = Some W_216f4.
Proof. vm_refl. Qed.
Lemma D_216f4 : decode_any W_216f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_216f8 : bv 32 := 0x0005c703.
Lemma F_216f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21844 : word) = Some W_216f8.
Proof. vm_refl. Qed.
Lemma D_216f8 : decode_any W_216f8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_216fc : bv 32 := 0x0015c783.
Lemma F_216fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21848 : word) = Some W_216fc.
Proof. vm_refl. Qed.
Lemma D_216fc : decode_any W_216fc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21700 : bv 32 := 0x00258593.
Lemma F_21700 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2184c : word) = Some W_21700.
Proof. vm_refl. Qed.
Lemma D_21700 : decode_any W_21700 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21704 : bv 32 := 0x00268813.
Lemma F_21704 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21850 : word) = Some W_21704.
Proof. vm_refl. Qed.
Lemma D_21704 : decode_any W_21704 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21708 : bv 32 := 0x00e68023.
Lemma F_21708 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21854 : word) = Some W_21708.
Proof. vm_refl. Qed.
Lemma D_21708 : decode_any W_21708 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2170c : bv 32 := 0x00f680a3.
Lemma F_2170c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21858 : word) = Some W_2170c.
Proof. vm_refl. Qed.
Lemma D_2170c : decode_any W_2170c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21710 : bv 32 := 0x00080693.
Lemma F_21710 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2185c : word) = Some W_21710.
Proof. vm_refl. Qed.
Lemma D_21710 : decode_any W_21710 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21714 : bv 32 := 0x00167613.
Lemma F_21714 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21860 : word) = Some W_21714.
Proof. vm_refl. Qed.
Lemma D_21714 : decode_any W_21714 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21718 : bv 32 := 0xfc060ee3.
Lemma F_21718 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21864 : word) = Some W_21718.
Proof. vm_refl. Qed.
Lemma D_21718 : decode_any W_21718 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_2171c : bv 32 := 0x0005c583.
Lemma F_2171c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21868 : word) = Some W_2171c.
Proof. vm_refl. Qed.
Lemma D_2171c : decode_any W_2171c = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21720 : bv 32 := 0x00b68023.
Lemma F_21720 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2186c : word) = Some W_21720.
Proof. vm_refl. Qed.
Lemma D_21720 : decode_any W_21720 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21724 : bv 32 := 0x00008067.
Lemma F_21724 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21870 : word) = Some W_21724.
Proof. vm_refl. Qed.
Lemma D_21724 : decode_any W_21724 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21728 : bv 32 := 0x0e060a63.
Lemma F_21728 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21874 : word) = Some W_21728.
Proof. vm_refl. Qed.
Lemma D_21728 : decode_any W_21728 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_2172c : bv 32 := 0x00b50023.
Lemma F_2172c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21878 : word) = Some W_2172c.
Proof. vm_refl. Qed.
Lemma D_2172c : decode_any W_2172c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21730 : bv 32 := 0x00c506b3.
Lemma F_21730 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2187c : word) = Some W_21730.
Proof. vm_refl. Qed.
Lemma D_21730 : decode_any W_21730 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21734 : bv 32 := 0x00300713.
Lemma F_21734 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21880 : word) = Some W_21734.
Proof. vm_refl. Qed.
Lemma D_21734 : decode_any W_21734 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21738 : bv 32 := 0xfeb68fa3.
Lemma F_21738 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21884 : word) = Some W_21738.
Proof. vm_refl. Qed.
Lemma D_21738 : decode_any W_21738 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_2173c : bv 32 := 0x0ee66063.
Lemma F_2173c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21888 : word) = Some W_2173c.
Proof. vm_refl. Qed.
Lemma D_2173c : decode_any W_2173c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_21740 : bv 32 := 0x00b500a3.
Lemma F_21740 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2188c : word) = Some W_21740.
Proof. vm_refl. Qed.
Lemma D_21740 : decode_any W_21740 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21744 : bv 32 := 0x00b50123.
Lemma F_21744 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21890 : word) = Some W_21744.
Proof. vm_refl. Qed.
Lemma D_21744 : decode_any W_21744 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21748 : bv 32 := 0x00700713.
Lemma F_21748 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21894 : word) = Some W_21748.
Proof. vm_refl. Qed.
Lemma D_21748 : decode_any W_21748 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_2174c : bv 32 := 0xfeb68ea3.
Lemma F_2174c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21898 : word) = Some W_2174c.
Proof. vm_refl. Qed.
Lemma D_2174c : decode_any W_2174c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_21750 : bv 32 := 0xfeb68f23.
Lemma F_21750 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2189c : word) = Some W_21750.
Proof. vm_refl. Qed.
Lemma D_21750 : decode_any W_21750 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_21754 : bv 32 := 0x0ce66463.
Lemma F_21754 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218a0 : word) = Some W_21754.
Proof. vm_refl. Qed.
Lemma D_21754 : decode_any W_21754 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_21758 : bv 32 := 0x00b501a3.
Lemma F_21758 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218a4 : word) = Some W_21758.
Proof. vm_refl. Qed.
Lemma D_21758 : decode_any W_21758 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_2175c : bv 32 := 0x00900793.
Lemma F_2175c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218a8 : word) = Some W_2175c.
Proof. vm_refl. Qed.
Lemma D_2175c : decode_any W_2175c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_21760 : bv 32 := 0xfeb68e23.
Lemma F_21760 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218ac : word) = Some W_21760.
Proof. vm_refl. Qed.
Lemma D_21760 : decode_any W_21760 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_21764 : bv 32 := 0x0af66c63.
Lemma F_21764 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218b0 : word) = Some W_21764.
Proof. vm_refl. Qed.
Lemma D_21764 : decode_any W_21764 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_21768 : bv 32 := 0x40a006bb.
Lemma F_21768 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218b4 : word) = Some W_21768.
Proof. vm_refl. Qed.
Lemma D_21768 : decode_any W_21768 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_2176c : bv 32 := 0x03859813.
Lemma F_2176c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218b8 : word) = Some W_2176c.
Proof. vm_refl. Qed.
Lemma D_2176c : decode_any W_2176c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_21770 : bv 32 := 0x101015b7.
Lemma F_21770 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218bc : word) = Some W_21770.
Proof. vm_refl. Qed.
Lemma D_21770 : decode_any W_21770 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_21774 : bv 32 := 0x0036f693.
Lemma F_21774 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218c0 : word) = Some W_21774.
Proof. vm_refl. Qed.
Lemma D_21774 : decode_any W_21774 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21778 : bv 32 := 0x00459713.
Lemma F_21778 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218c4 : word) = Some W_21778.
Proof. vm_refl. Qed.
Lemma D_21778 : decode_any W_21778 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_2177c : bv 32 := 0x40d60633.
Lemma F_2177c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218c8 : word) = Some W_2177c.
Proof. vm_refl. Qed.
Lemma D_2177c : decode_any W_2177c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_21780 : bv 32 := 0x00d505b3.
Lemma F_21780 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218cc : word) = Some W_21780.
Proof. vm_refl. Qed.
Lemma D_21780 : decode_any W_21780 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_21784 : bv 32 := 0x10070693.
Lemma F_21784 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218d0 : word) = Some W_21784.
Proof. vm_refl. Qed.
Lemma D_21784 : decode_any W_21784 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_21788 : bv 32 := 0xffc67713.
Lemma F_21788 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218d4 : word) = Some W_21788.
Proof. vm_refl. Qed.
Lemma D_21788 : decode_any W_21788 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_2178c : bv 32 := 0x02d83633.
Lemma F_2178c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218d8 : word) = Some W_2178c.
Proof. vm_refl. Qed.
Lemma D_2178c : decode_any W_2178c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_21790 : bv 32 := 0x00c5a023.
Lemma F_21790 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218dc : word) = Some W_21790.
Proof. vm_refl. Qed.
Lemma D_21790 : decode_any W_21790 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21794 : bv 32 := 0x00e586b3.
Lemma F_21794 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218e0 : word) = Some W_21794.
Proof. vm_refl. Qed.
Lemma D_21794 : decode_any W_21794 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_21798 : bv 32 := 0xfec6ae23.
Lemma F_21798 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218e4 : word) = Some W_21798.
Proof. vm_refl. Qed.
Lemma D_21798 : decode_any W_21798 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_2179c : bv 32 := 0x08f76063.
Lemma F_2179c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218e8 : word) = Some W_2179c.
Proof. vm_refl. Qed.
Lemma D_2179c : decode_any W_2179c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_217a0 : bv 32 := 0x00c5a223.
Lemma F_217a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218ec : word) = Some W_217a0.
Proof. vm_refl. Qed.
Lemma D_217a0 : decode_any W_217a0 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_217a4 : bv 32 := 0x00c5a423.
Lemma F_217a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218f0 : word) = Some W_217a4.
Proof. vm_refl. Qed.
Lemma D_217a4 : decode_any W_217a4 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_217a8 : bv 32 := 0x01900793.
Lemma F_217a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218f4 : word) = Some W_217a8.
Proof. vm_refl. Qed.
Lemma D_217a8 : decode_any W_217a8 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_217ac : bv 32 := 0xfec6aa23.
Lemma F_217ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218f8 : word) = Some W_217ac.
Proof. vm_refl. Qed.
Lemma D_217ac : decode_any W_217ac = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_217b0 : bv 32 := 0xfec6ac23.
Lemma F_217b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x218fc : word) = Some W_217b0.
Proof. vm_refl. Qed.
Lemma D_217b0 : decode_any W_217b0 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_217b4 : bv 32 := 0x06f76463.
Lemma F_217b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21900 : word) = Some W_217b4.
Proof. vm_refl. Qed.
Lemma D_217b4 : decode_any W_217b4 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_217b8 : bv 32 := 0x00c5a623.
Lemma F_217b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21904 : word) = Some W_217b8.
Proof. vm_refl. Qed.
Lemma D_217b8 : decode_any W_217b8 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_217bc : bv 32 := 0x00c5a823.
Lemma F_217bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21908 : word) = Some W_217bc.
Proof. vm_refl. Qed.
Lemma D_217bc : decode_any W_217bc = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_217c0 : bv 32 := 0x00c5aa23.
Lemma F_217c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2190c : word) = Some W_217c0.
Proof. vm_refl. Qed.
Lemma D_217c0 : decode_any W_217c0 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_217c4 : bv 32 := 0x00c5ac23.
Lemma F_217c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21910 : word) = Some W_217c4.
Proof. vm_refl. Qed.
Lemma D_217c4 : decode_any W_217c4 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_217c8 : bv 32 := 0x0045f793.
Lemma F_217c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21914 : word) = Some W_217c8.
Proof. vm_refl. Qed.
Lemma D_217c8 : decode_any W_217c8 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_217cc : bv 32 := 0x02000813.
Lemma F_217cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21918 : word) = Some W_217cc.
Proof. vm_refl. Qed.
Lemma D_217cc : decode_any W_217cc = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_217d0 : bv 32 := 0x01878793.
Lemma F_217d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2191c : word) = Some W_217d0.
Proof. vm_refl. Qed.
Lemma D_217d0 : decode_any W_217d0 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_217d4 : bv 32 := 0x40f70733.
Lemma F_217d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21920 : word) = Some W_217d4.
Proof. vm_refl. Qed.
Lemma D_217d4 : decode_any W_217d4 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_217d8 : bv 32 := 0xfec6a223.
Lemma F_217d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21924 : word) = Some W_217d8.
Proof. vm_refl. Qed.
Lemma D_217d8 : decode_any W_217d8 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_217dc : bv 32 := 0xfec6a423.
Lemma F_217dc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21928 : word) = Some W_217dc.
Proof. vm_refl. Qed.
Lemma D_217dc : decode_any W_217dc = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_217e0 : bv 32 := 0xfec6a623.
Lemma F_217e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2192c : word) = Some W_217e0.
Proof. vm_refl. Qed.
Lemma D_217e0 : decode_any W_217e0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_217e4 : bv 32 := 0xfec6a823.
Lemma F_217e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21930 : word) = Some W_217e4.
Proof. vm_refl. Qed.
Lemma D_217e4 : decode_any W_217e4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_217e8 : bv 32 := 0x03076a63.
Lemma F_217e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21934 : word) = Some W_217e8.
Proof. vm_refl. Qed.
Lemma D_217e8 : decode_any W_217e8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_217ec : bv 32 := 0x02061613.
Lemma F_217ec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21938 : word) = Some W_217ec.
Proof. vm_refl. Qed.
Lemma D_217ec : decode_any W_217ec = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_217f0 : bv 32 := 0x00f585b3.
Lemma F_217f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2193c : word) = Some W_217f0.
Proof. vm_refl. Qed.
Lemma D_217f0 : decode_any W_217f0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_217f4 : bv 32 := 0x02065693.
Lemma F_217f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21940 : word) = Some W_217f4.
Proof. vm_refl. Qed.
Lemma D_217f4 : decode_any W_217f4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_217f8 : bv 32 := 0x00d66633.
Lemma F_217f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21944 : word) = Some W_217f8.
Proof. vm_refl. Qed.
Lemma D_217f8 : decode_any W_217f8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_217fc : bv 32 := 0x01f00693.
Lemma F_217fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21948 : word) = Some W_217fc.
Proof. vm_refl. Qed.
Lemma D_217fc : decode_any W_217fc = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_21800 : bv 32 := 0x00c5b023.
Lemma F_21800 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2194c : word) = Some W_21800.
Proof. vm_refl. Qed.
Lemma D_21800 : decode_any W_21800 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21804 : bv 32 := 0x00c5b423.
Lemma F_21804 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21950 : word) = Some W_21804.
Proof. vm_refl. Qed.
Lemma D_21804 : decode_any W_21804 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21808 : bv 32 := 0x00c5b823.
Lemma F_21808 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21954 : word) = Some W_21808.
Proof. vm_refl. Qed.
Lemma D_21808 : decode_any W_21808 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2180c : bv 32 := 0x00c5bc23.
Lemma F_2180c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21958 : word) = Some W_2180c.
Proof. vm_refl. Qed.
Lemma D_2180c : decode_any W_2180c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21810 : bv 32 := 0xfe070713.
Lemma F_21810 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2195c : word) = Some W_21810.
Proof. vm_refl. Qed.
Lemma D_21810 : decode_any W_21810 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_21814 : bv 32 := 0x02058593.
Lemma F_21814 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21960 : word) = Some W_21814.
Proof. vm_refl. Qed.
Lemma D_21814 : decode_any W_21814 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_21818 : bv 32 := 0xfee6e4e3.
Lemma F_21818 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21964 : word) = Some W_21818.
Proof. vm_refl. Qed.
Lemma D_21818 : decode_any W_21818 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_2181c : bv 32 := 0x00008067.
Lemma F_2181c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21968 : word) = Some W_2181c.
Proof. vm_refl. Qed.
Lemma D_2181c : decode_any W_2181c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21820 : bv 32 := 0xfe010113.
Lemma F_21820 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2196c : word) = Some W_21820.
Proof. vm_refl. Qed.
Lemma D_21820 : decode_any W_21820 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_21824 : bv 32 := 0x00113c23.
Lemma F_21824 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21970 : word) = Some W_21824.
Proof. vm_refl. Qed.
Lemma D_21824 : decode_any W_21824 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21828 : bv 32 := 0x00813823.
Lemma F_21828 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21974 : word) = Some W_21828.
Proof. vm_refl. Qed.
Lemma D_21828 : decode_any W_21828 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2182c : bv 32 := 0x00913423.
Lemma F_2182c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21978 : word) = Some W_2182c.
Proof. vm_refl. Qed.
Lemma D_2182c : decode_any W_2182c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21830 : bv 32 := 0x00058413.
Lemma F_21830 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2197c : word) = Some W_21830.
Proof. vm_refl. Qed.
Lemma D_21830 : decode_any W_21830 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21834 : bv 32 := 0x00050493.
Lemma F_21834 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21980 : word) = Some W_21834.
Proof. vm_refl. Qed.
Lemma D_21834 : decode_any W_21834 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21838 : bv 32 := 0x00000593.
Lemma F_21838 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21984 : word) = Some W_21838.
Proof. vm_refl. Qed.
Lemma D_21838 : decode_any W_21838 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2183c : bv 32 := 0x00040613.
Lemma F_2183c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21988 : word) = Some W_2183c.
Proof. vm_refl. Qed.
Lemma D_2183c : decode_any W_2183c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21840 : bv 32 := 0x024000ef.
Lemma F_21840 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2198c : word) = Some W_21840.
Proof. vm_refl. Qed.
Lemma D_21840 : decode_any W_21840 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_21844 : bv 32 := 0x00050463.
Lemma F_21844 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21990 : word) = Some W_21844.
Proof. vm_refl. Qed.
Lemma D_21844 : decode_any W_21844 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21848 : bv 32 := 0x40950433.
Lemma F_21848 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21994 : word) = Some W_21848.
Proof. vm_refl. Qed.
Lemma D_21848 : decode_any W_21848 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_2184c : bv 32 := 0x00040513.
Lemma F_2184c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21998 : word) = Some W_2184c.
Proof. vm_refl. Qed.
Lemma D_2184c : decode_any W_2184c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21850 : bv 32 := 0x01813083.
Lemma F_21850 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x2199c : word) = Some W_21850.
Proof. vm_refl. Qed.
Lemma D_21850 : decode_any W_21850 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21854 : bv 32 := 0x01013403.
Lemma F_21854 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219a0 : word) = Some W_21854.
Proof. vm_refl. Qed.
Lemma D_21854 : decode_any W_21854 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21858 : bv 32 := 0x00813483.
Lemma F_21858 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219a4 : word) = Some W_21858.
Proof. vm_refl. Qed.
Lemma D_21858 : decode_any W_21858 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2185c : bv 32 := 0x02010113.
Lemma F_2185c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219a8 : word) = Some W_2185c.
Proof. vm_refl. Qed.
Lemma D_2185c : decode_any W_2185c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_21860 : bv 32 := 0x00008067.
Lemma F_21860 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219ac : word) = Some W_21860.
Proof. vm_refl. Qed.
Lemma D_21860 : decode_any W_21860 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21864 : bv 32 := 0x0ff5f593.
Lemma F_21864 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219b0 : word) = Some W_21864.
Proof. vm_refl. Qed.
Lemma D_21864 : decode_any W_21864 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_21868 : bv 32 := 0x00757693.
Lemma F_21868 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219b4 : word) = Some W_21868.
Proof. vm_refl. Qed.
Lemma D_21868 : decode_any W_21868 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_2186c : bv 32 := 0x00c03733.
Lemma F_2186c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219b8 : word) = Some W_2186c.
Proof. vm_refl. Qed.
Lemma D_2186c : decode_any W_2186c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21870 : bv 32 := 0x02068c63.
Lemma F_21870 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219bc : word) = Some W_21870.
Proof. vm_refl. Qed.
Lemma D_21870 : decode_any W_21870 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_21874 : bv 32 := 0x02060a63.
Lemma F_21874 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219c0 : word) = Some W_21874.
Proof. vm_refl. Qed.
Lemma D_21874 : decode_any W_21874 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_21878 : bv 32 := 0x00150793.
Lemma F_21878 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219c4 : word) = Some W_21878.
Proof. vm_refl. Qed.
Lemma D_21878 : decode_any W_21878 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2187c : bv 32 := 0x00100813.
Lemma F_2187c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219c8 : word) = Some W_2187c.
Proof. vm_refl. Qed.
Lemma D_2187c : decode_any W_2187c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21880 : bv 32 := 0x00054703.
Lemma F_21880 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219cc : word) = Some W_21880.
Proof. vm_refl. Qed.
Lemma D_21880 : decode_any W_21880 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21884 : bv 32 := 0x00060693.
Lemma F_21884 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219d0 : word) = Some W_21884.
Proof. vm_refl. Qed.
Lemma D_21884 : decode_any W_21884 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21888 : bv 32 := 0x06b70e63.
Lemma F_21888 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219d4 : word) = Some W_21888.
Proof. vm_refl. Qed.
Lemma D_21888 : decode_any W_21888 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_2188c : bv 32 := 0x00150513.
Lemma F_2188c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219d8 : word) = Some W_2188c.
Proof. vm_refl. Qed.
Lemma D_2188c : decode_any W_2188c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21890 : bv 32 := 0xfff68613.
Lemma F_21890 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219dc : word) = Some W_21890.
Proof. vm_refl. Qed.
Lemma D_21890 : decode_any W_21890 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_21894 : bv 32 := 0x0077f893.
Lemma F_21894 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219e0 : word) = Some W_21894.
Proof. vm_refl. Qed.
Lemma D_21894 : decode_any W_21894 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_21898 : bv 32 := 0x00c03733.
Lemma F_21898 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219e4 : word) = Some W_21898.
Proof. vm_refl. Qed.
Lemma D_21898 : decode_any W_21898 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_2189c : bv 32 := 0x00088663.
Lemma F_2189c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219e8 : word) = Some W_2189c.
Proof. vm_refl. Qed.
Lemma D_2189c : decode_any W_2189c = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_218a0 : bv 32 := 0x00178793.
Lemma F_218a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219ec : word) = Some W_218a0.
Proof. vm_refl. Qed.
Lemma D_218a0 : decode_any W_218a0 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_218a4 : bv 32 := 0xfd069ee3.
Lemma F_218a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219f0 : word) = Some W_218a4.
Proof. vm_refl. Qed.
Lemma D_218a4 : decode_any W_218a4 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_218a8 : bv 32 := 0x06070863.
Lemma F_218a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219f4 : word) = Some W_218a8.
Proof. vm_refl. Qed.
Lemma D_218a8 : decode_any W_218a8 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_218ac : bv 32 := 0x00054683.
Lemma F_218ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219f8 : word) = Some W_218ac.
Proof. vm_refl. Qed.
Lemma D_218ac : decode_any W_218ac = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_218b0 : bv 32 := 0x04b68663.
Lemma F_218b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x219fc : word) = Some W_218b0.
Proof. vm_refl. Qed.
Lemma D_218b0 : decode_any W_218b0 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_218b4 : bv 32 := 0x00800693.
Lemma F_218b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a00 : word) = Some W_218b4.
Proof. vm_refl. Qed.
Lemma D_218b4 : decode_any W_218b4 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_218b8 : bv 32 := 0x04d66263.
Lemma F_218b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a04 : word) = Some W_218b8.
Proof. vm_refl. Qed.
Lemma D_218b8 : decode_any W_218b8 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_218bc : bv 32 := 0xfffef697.
Lemma F_218bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a08 : word) = Some W_218bc.
Proof. vm_refl. Qed.
Lemma D_218bc : decode_any W_218bc = Some (Auipc 13 1048559, 4%Z).
Proof. vm_refl. Qed.

Definition W_218c0 : bv 32 := 0xb886b683.
Lemma F_218c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a0c : word) = Some W_218c0.
Proof. vm_refl. Qed.
Lemma D_218c0 : decode_any W_218c0 = Some (Load SZ8 true 13 13 2952, 4%Z).
Proof. vm_refl. Qed.

Definition W_218c4 : bv 32 := 0xfffef717.
Lemma F_218c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a10 : word) = Some W_218c4.
Proof. vm_refl. Qed.
Lemma D_218c4 : decode_any W_218c4 = Some (Auipc 14 1048559, 4%Z).
Proof. vm_refl. Qed.

Definition W_218c8 : bv 32 := 0xb7073703.
Lemma F_218c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a14 : word) = Some W_218c8.
Proof. vm_refl. Qed.
Lemma D_218c8 : decode_any W_218c8 = Some (Load SZ8 true 14 14 2928, 4%Z).
Proof. vm_refl. Qed.

Definition W_218cc : bv 32 := 0x00168793.
Lemma F_218cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a18 : word) = Some W_218cc.
Proof. vm_refl. Qed.
Lemma D_218cc : decode_any W_218cc = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_218d0 : bv 32 := 0x02f587b3.
Lemma F_218d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a1c : word) = Some W_218d0.
Proof. vm_refl. Qed.
Lemma D_218d0 : decode_any W_218d0 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_218d4 : bv 32 := 0x00700813.
Lemma F_218d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a20 : word) = Some W_218d4.
Proof. vm_refl. Qed.
Lemma D_218d4 : decode_any W_218d4 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_218d8 : bv 32 := 0x00053883.
Lemma F_218d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a24 : word) = Some W_218d8.
Proof. vm_refl. Qed.
Lemma D_218d8 : decode_any W_218d8 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_218dc : bv 32 := 0x00f8c8b3.
Lemma F_218dc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a28 : word) = Some W_218dc.
Proof. vm_refl. Qed.
Lemma D_218dc : decode_any W_218dc = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_218e0 : bv 32 := 0x411682b3.
Lemma F_218e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a2c : word) = Some W_218e0.
Proof. vm_refl. Qed.
Lemma D_218e0 : decode_any W_218e0 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_218e4 : bv 32 := 0x0112e8b3.
Lemma F_218e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a30 : word) = Some W_218e4.
Proof. vm_refl. Qed.
Lemma D_218e4 : decode_any W_218e4 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_218e8 : bv 32 := 0x00e8f8b3.
Lemma F_218e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a34 : word) = Some W_218e8.
Proof. vm_refl. Qed.
Lemma D_218e8 : decode_any W_218e8 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_218ec : bv 32 := 0x02e89a63.
Lemma F_218ec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a38 : word) = Some W_218ec.
Proof. vm_refl. Qed.
Lemma D_218ec : decode_any W_218ec = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_218f0 : bv 32 := 0xff860613.
Lemma F_218f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a3c : word) = Some W_218f0.
Proof. vm_refl. Qed.
Lemma D_218f0 : decode_any W_218f0 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_218f4 : bv 32 := 0x00850513.
Lemma F_218f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a40 : word) = Some W_218f4.
Proof. vm_refl. Qed.
Lemma D_218f4 : decode_any W_218f4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_218f8 : bv 32 := 0xfec860e3.
Lemma F_218f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a44 : word) = Some W_218f8.
Proof. vm_refl. Qed.
Lemma D_218f8 : decode_any W_218f8 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_218fc : bv 32 := 0x00060693.
Lemma F_218fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a48 : word) = Some W_218fc.
Proof. vm_refl. Qed.
Lemma D_218fc : decode_any W_218fc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21900 : bv 32 := 0x00060c63.
Lemma F_21900 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a4c : word) = Some W_21900.
Proof. vm_refl. Qed.
Lemma D_21900 : decode_any W_21900 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21904 : bv 32 := 0x00054603.
Lemma F_21904 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a50 : word) = Some W_21904.
Proof. vm_refl. Qed.
Lemma D_21904 : decode_any W_21904 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21908 : bv 32 := 0x00b60a63.
Lemma F_21908 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a54 : word) = Some W_21908.
Proof. vm_refl. Qed.
Lemma D_21908 : decode_any W_21908 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_2190c : bv 32 := 0xfff68693.
Lemma F_2190c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a58 : word) = Some W_2190c.
Proof. vm_refl. Qed.
Lemma D_2190c : decode_any W_2190c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_21910 : bv 32 := 0x00150513.
Lemma F_21910 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a5c : word) = Some W_21910.
Proof. vm_refl. Qed.
Lemma D_21910 : decode_any W_21910 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21914 : bv 32 := 0xfe0698e3.
Lemma F_21914 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a60 : word) = Some W_21914.
Proof. vm_refl. Qed.
Lemma D_21914 : decode_any W_21914 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_2191c : bv 32 := 0x00008067.
Lemma F_2191c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a68 : word) = Some W_2191c.
Proof. vm_refl. Qed.
Lemma D_2191c : decode_any W_2191c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21920 : bv 32 := 0x00060693.
Lemma F_21920 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a6c : word) = Some W_21920.
Proof. vm_refl. Qed.
Lemma D_21920 : decode_any W_21920 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21924 : bv 32 := 0x00054603.
Lemma F_21924 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a70 : word) = Some W_21924.
Proof. vm_refl. Qed.
Lemma D_21924 : decode_any W_21924 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21928 : bv 32 := 0xfeb612e3.
Lemma F_21928 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a74 : word) = Some W_21928.
Proof. vm_refl. Qed.
Lemma D_21928 : decode_any W_21928 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_2192c : bv 32 := 0xff1ff06f.
Lemma F_2192c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a78 : word) = Some W_2192c.
Proof. vm_refl. Qed.
Lemma D_2192c : decode_any W_2192c = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_21930 : bv 32 := 0x00073597.
Lemma F_21930 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a7c : word) = Some W_21930.
Proof. vm_refl. Qed.
Lemma D_21930 : decode_any W_21930 = Some (Auipc 11 115, 4%Z).
Proof. vm_refl. Qed.

Definition W_21934 : bv 32 := 0xa7f58683.
Lemma F_21934 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a80 : word) = Some W_21934.
Proof. vm_refl. Qed.
Lemma D_21934 : decode_any W_21934 = Some (Load SZ1 true 13 11 2687, 4%Z).
Proof. vm_refl. Qed.

Definition W_21938 : bv 32 := 0x1e068863.
Lemma F_21938 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21a84 : word) = Some W_21938.
Proof. vm_refl. Qed.
Lemma D_21938 : decode_any W_21938 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_21b28 : bv 32 := 0x00008067.
Lemma F_21b28 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21c74 : word) = Some W_21b28.
Proof. vm_refl. Qed.
Lemma D_21b28 : decode_any W_21b28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bb8 : bv 32 := 0x00052583.
Lemma F_21bb8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d04 : word) = Some W_21bb8.
Proof. vm_refl. Qed.
Lemma D_21bb8 : decode_any W_21bb8 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bbc : bv 32 := 0x0005c463.
Lemma F_21bbc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d08 : word) = Some W_21bbc.
Proof. vm_refl. Qed.
Lemma D_21bbc : decode_any W_21bbc = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21bc0 : bv 32 := 0x00008067.
Lemma F_21bc0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d0c : word) = Some W_21bc0.
Proof. vm_refl. Qed.
Lemma D_21bc0 : decode_any W_21bc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c2c : bv 32 := 0x00050893.
Lemma F_21c2c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d78 : word) = Some W_21c2c.
Proof. vm_refl. Qed.
Lemma D_21c2c : decode_any W_21c2c = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c30 : bv 32 := 0x00058513.
Lemma F_21c30 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d7c : word) = Some W_21c30.
Proof. vm_refl. Qed.
Lemma D_21c30 : decode_any W_21c30 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c34 : bv 32 := 0x00060593.
Lemma F_21c34 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d80 : word) = Some W_21c34.
Proof. vm_refl. Qed.
Lemma D_21c34 : decode_any W_21c34 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c38 : bv 32 := 0x00068613.
Lemma F_21c38 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d84 : word) = Some W_21c38.
Proof. vm_refl. Qed.
Lemma D_21c38 : decode_any W_21c38 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c3c : bv 32 := 0x00070693.
Lemma F_21c3c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d88 : word) = Some W_21c3c.
Proof. vm_refl. Qed.
Lemma D_21c3c : decode_any W_21c3c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c40 : bv 32 := 0x00078713.
Lemma F_21c40 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d8c : word) = Some W_21c40.
Proof. vm_refl. Qed.
Lemma D_21c40 : decode_any W_21c40 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c44 : bv 32 := 0x00080793.
Lemma F_21c44 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d90 : word) = Some W_21c44.
Proof. vm_refl. Qed.
Lemma D_21c44 : decode_any W_21c44 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c48 : bv 32 := 0x00000073.
Lemma F_21c48 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d94 : word) = Some W_21c48.
Proof. vm_refl. Qed.
Lemma D_21c48 : decode_any W_21c48 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_21c48 : is_ecall W_21c48 = true.
Proof. reflexivity. Qed.

Definition W_21c4c : bv 32 := 0x00008067.
Lemma F_21c4c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d98 : word) = Some W_21c4c.
Proof. vm_refl. Qed.
Lemma D_21c4c : decode_any W_21c4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c50 : bv 32 := 0xfddff06f.
Lemma F_21c50 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21d9c : word) = Some W_21c50.
Proof. vm_refl. Qed.
Lemma D_21c50 : decode_any W_21c50 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c54 : bv 32 := 0x00050213.
Lemma F_21c54 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21da0 : word) = Some W_21c54.
Proof. vm_refl. Qed.
Lemma D_21c54 : decode_any W_21c54 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c58 : bv 32 := 0x00000513.
Lemma F_21c58 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21da4 : word) = Some W_21c58.
Proof. vm_refl. Qed.
Lemma D_21c58 : decode_any W_21c58 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c5c : bv 32 := 0x00008067.
Lemma F_21c5c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21da8 : word) = Some W_21c5c.
Proof. vm_refl. Qed.
Lemma D_21c5c : decode_any W_21c5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c6c : bv 32 := 0xff010113.
Lemma F_21c6c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21db8 : word) = Some W_21c6c.
Proof. vm_refl. Qed.
Lemma D_21c6c : decode_any W_21c6c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c70 : bv 32 := 0x00113423.
Lemma F_21c70 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21dbc : word) = Some W_21c70.
Proof. vm_refl. Qed.
Lemma D_21c70 : decode_any W_21c70 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c74 : bv 32 := 0xa89fa0ef.
Lemma F_21c74 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21dc0 : word) = Some W_21c74.
Proof. vm_refl. Qed.
Lemma D_21c74 : decode_any W_21c74 = Some (Jal 1 2075272, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c78 : bv 32 := 0x00050593.
Lemma F_21c78 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21dc4 : word) = Some W_21c78.
Proof. vm_refl. Qed.
Lemma D_21c78 : decode_any W_21c78 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c7c : bv 32 := 0x03900513.
Lemma F_21c7c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21dc8 : word) = Some W_21c7c.
Proof. vm_refl. Qed.
Lemma D_21c7c : decode_any W_21c7c = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c80 : bv 32 := 0x00000613.
Lemma F_21c80 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21dcc : word) = Some W_21c80.
Proof. vm_refl. Qed.
Lemma D_21c80 : decode_any W_21c80 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c84 : bv 32 := 0x00000693.
Lemma F_21c84 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21dd0 : word) = Some W_21c84.
Proof. vm_refl. Qed.
Lemma D_21c84 : decode_any W_21c84 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c88 : bv 32 := 0x00000713.
Lemma F_21c88 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21dd4 : word) = Some W_21c88.
Proof. vm_refl. Qed.
Lemma D_21c88 : decode_any W_21c88 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c8c : bv 32 := 0x00000793.
Lemma F_21c8c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21dd8 : word) = Some W_21c8c.
Proof. vm_refl. Qed.
Lemma D_21c8c : decode_any W_21c8c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c90 : bv 32 := 0x00000813.
Lemma F_21c90 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21ddc : word) = Some W_21c90.
Proof. vm_refl. Qed.
Lemma D_21c90 : decode_any W_21c90 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c94 : bv 32 := 0xfbdff0ef.
Lemma F_21c94 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21de0 : word) = Some W_21c94.
Proof. vm_refl. Qed.
Lemma D_21c94 : decode_any W_21c94 = Some (Jal 1 2097084, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c98 : bv 32 := 0x0005051b.
Lemma F_21c98 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21de4 : word) = Some W_21c98.
Proof. vm_refl. Qed.
Lemma D_21c98 : decode_any W_21c98 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21c9c : bv 32 := 0x00450593.
Lemma F_21c9c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21de8 : word) = Some W_21c9c.
Proof. vm_refl. Qed.
Lemma D_21c9c : decode_any W_21c9c = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ca0 : bv 32 := 0x0015b593.
Lemma F_21ca0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21dec : word) = Some W_21ca0.
Proof. vm_refl. Qed.
Lemma D_21ca0 : decode_any W_21ca0 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ca4 : bv 32 := 0xfff58593.
Lemma F_21ca4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21df0 : word) = Some W_21ca4.
Proof. vm_refl. Qed.
Lemma D_21ca4 : decode_any W_21ca4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ca8 : bv 32 := 0x00a5f533.
Lemma F_21ca8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21df4 : word) = Some W_21ca8.
Proof. vm_refl. Qed.
Lemma D_21ca8 : decode_any W_21ca8 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cac : bv 32 := 0xf8cf80ef.
Lemma F_21cac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21df8 : word) = Some W_21cac.
Proof. vm_refl. Qed.
Lemma D_21cac : decode_any W_21cac = Some (Jal 1 2066316, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cb0 : bv 32 := 0x0005051b.
Lemma F_21cb0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21dfc : word) = Some W_21cb0.
Proof. vm_refl. Qed.
Lemma D_21cb0 : decode_any W_21cb0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cb4 : bv 32 := 0x00813083.
Lemma F_21cb4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e00 : word) = Some W_21cb4.
Proof. vm_refl. Qed.
Lemma D_21cb4 : decode_any W_21cb4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cb8 : bv 32 := 0x01010113.
Lemma F_21cb8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e04 : word) = Some W_21cb8.
Proof. vm_refl. Qed.
Lemma D_21cb8 : decode_any W_21cb8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cbc : bv 32 := 0x00008067.
Lemma F_21cbc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e08 : word) = Some W_21cbc.
Proof. vm_refl. Qed.
Lemma D_21cbc : decode_any W_21cbc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ccc : bv 32 := 0xff010113.
Lemma F_21ccc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e18 : word) = Some W_21ccc.
Proof. vm_refl. Qed.
Lemma D_21ccc : decode_any W_21ccc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cd0 : bv 32 := 0x00113423.
Lemma F_21cd0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e1c : word) = Some W_21cd0.
Proof. vm_refl. Qed.
Lemma D_21cd0 : decode_any W_21cd0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cd4 : bv 32 := 0x00060693.
Lemma F_21cd4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e20 : word) = Some W_21cd4.
Proof. vm_refl. Qed.
Lemma D_21cd4 : decode_any W_21cd4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cd8 : bv 32 := 0x00058613.
Lemma F_21cd8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e24 : word) = Some W_21cd8.
Proof. vm_refl. Qed.
Lemma D_21cd8 : decode_any W_21cd8 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cdc : bv 32 := 0x00050593.
Lemma F_21cdc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e28 : word) = Some W_21cdc.
Proof. vm_refl. Qed.
Lemma D_21cdc : decode_any W_21cdc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ce0 : bv 32 := 0x03f00513.
Lemma F_21ce0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e2c : word) = Some W_21ce0.
Proof. vm_refl. Qed.
Lemma D_21ce0 : decode_any W_21ce0 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ce4 : bv 32 := 0x00000713.
Lemma F_21ce4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e30 : word) = Some W_21ce4.
Proof. vm_refl. Qed.
Lemma D_21ce4 : decode_any W_21ce4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21ce8 : bv 32 := 0x00000793.
Lemma F_21ce8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e34 : word) = Some W_21ce8.
Proof. vm_refl. Qed.
Lemma D_21ce8 : decode_any W_21ce8 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cec : bv 32 := 0x00000813.
Lemma F_21cec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e38 : word) = Some W_21cec.
Proof. vm_refl. Qed.
Lemma D_21cec : decode_any W_21cec = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cf0 : bv 32 := 0xf61ff0ef.
Lemma F_21cf0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e3c : word) = Some W_21cf0.
Proof. vm_refl. Qed.
Lemma D_21cf0 : decode_any W_21cf0 = Some (Jal 1 2096992, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cf4 : bv 32 := 0x00813083.
Lemma F_21cf4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e40 : word) = Some W_21cf4.
Proof. vm_refl. Qed.
Lemma D_21cf4 : decode_any W_21cf4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cf8 : bv 32 := 0x01010113.
Lemma F_21cf8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e44 : word) = Some W_21cf8.
Proof. vm_refl. Qed.
Lemma D_21cf8 : decode_any W_21cf8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21cfc : bv 32 := 0xf3cf806f.
Lemma F_21cfc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x21e48 : word) = Some W_21cfc.
Proof. vm_refl. Qed.
Lemma D_21cfc : decode_any W_21cfc = Some (Jal 0 2066236, 4%Z).
Proof. vm_refl. Qed.
