(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No the author licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress3_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_213b4 : bv 32 := 0x0035f693.
Lemma F_213b4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21500 : word) = Some W_213b4.
Proof. vm_refl. Qed.
Lemma D_213b4 : decode_any W_213b4 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_213b8 : bv 32 := 0x10068863.
Lemma F_213b8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21504 : word) = Some W_213b8.
Proof. vm_refl. Qed.
Lemma D_213b8 : decode_any W_213b8 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_213bc : bv 32 := 0x02060e63.
Lemma F_213bc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21508 : word) = Some W_213bc.
Proof. vm_refl. Qed.
Lemma D_213bc : decode_any W_213bc = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_213c0 : bv 32 := 0x00158713.
Lemma F_213c0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2150c : word) = Some W_213c0.
Proof. vm_refl. Qed.
Lemma D_213c0 : decode_any W_213c0 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_213c4 : bv 32 := 0x00100793.
Lemma F_213c4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21510 : word) = Some W_213c4.
Proof. vm_refl. Qed.
Lemma D_213c4 : decode_any W_213c4 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_213c8 : bv 32 := 0x00050693.
Lemma F_213c8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21514 : word) = Some W_213c8.
Proof. vm_refl. Qed.
Lemma D_213c8 : decode_any W_213c8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_213cc : bv 32 := 0x0005c883.
Lemma F_213cc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21518 : word) = Some W_213cc.
Proof. vm_refl. Qed.
Lemma D_213cc : decode_any W_213cc = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_213d0 : bv 32 := 0x00060813.
Lemma F_213d0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2151c : word) = Some W_213d0.
Proof. vm_refl. Qed.
Lemma D_213d0 : decode_any W_213d0 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_213d4 : bv 32 := 0x00158593.
Lemma F_213d4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21520 : word) = Some W_213d4.
Proof. vm_refl. Qed.
Lemma D_213d4 : decode_any W_213d4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_213d8 : bv 32 := 0x00377293.
Lemma F_213d8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21524 : word) = Some W_213d8.
Proof. vm_refl. Qed.
Lemma D_213d8 : decode_any W_213d8 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_213dc : bv 32 := 0x01168023.
Lemma F_213dc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21528 : word) = Some W_213dc.
Proof. vm_refl. Qed.
Lemma D_213dc : decode_any W_213dc = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_213e0 : bv 32 := 0x00168693.
Lemma F_213e0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2152c : word) = Some W_213e0.
Proof. vm_refl. Qed.
Lemma D_213e0 : decode_any W_213e0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_213e4 : bv 32 := 0xfff60613.
Lemma F_213e4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21530 : word) = Some W_213e4.
Proof. vm_refl. Qed.
Lemma D_213e4 : decode_any W_213e4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_213e8 : bv 32 := 0x00028a63.
Lemma F_213e8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21534 : word) = Some W_213e8.
Proof. vm_refl. Qed.
Lemma D_213e8 : decode_any W_213e8 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_213ec : bv 32 := 0x00170713.
Lemma F_213ec : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21538 : word) = Some W_213ec.
Proof. vm_refl. Qed.
Lemma D_213ec : decode_any W_213ec = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_213f0 : bv 32 := 0xfcf81ee3.
Lemma F_213f0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2153c : word) = Some W_213f0.
Proof. vm_refl. Qed.
Lemma D_213f0 : decode_any W_213f0 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_213f4 : bv 32 := 0x0080006f.
Lemma F_213f4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21540 : word) = Some W_213f4.
Proof. vm_refl. Qed.
Lemma D_213f4 : decode_any W_213f4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_213f8 : bv 32 := 0x00050693.
Lemma F_213f8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21544 : word) = Some W_213f8.
Proof. vm_refl. Qed.
Lemma D_213f8 : decode_any W_213f8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_213fc : bv 32 := 0x0036f793.
Lemma F_213fc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21548 : word) = Some W_213fc.
Proof. vm_refl. Qed.
Lemma D_213fc : decode_any W_213fc = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21400 : bv 32 := 0x0c078a63.
Lemma F_21400 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2154c : word) = Some W_21400.
Proof. vm_refl. Qed.
Lemma D_21400 : decode_any W_21400 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_21404 : bv 32 := 0x02000713.
Lemma F_21404 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21550 : word) = Some W_21404.
Proof. vm_refl. Qed.
Lemma D_21404 : decode_any W_21404 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_21408 : bv 32 := 0x02e67063.
Lemma F_21408 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21554 : word) = Some W_21408.
Proof. vm_refl. Qed.
Lemma D_21408 : decode_any W_21408 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_2140c : bv 32 := 0x01000713.
Lemma F_2140c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21558 : word) = Some W_2140c.
Proof. vm_refl. Qed.
Lemma D_2140c : decode_any W_2140c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21410 : bv 32 := 0x24e67863.
Lemma F_21410 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2155c : word) = Some W_21410.
Proof. vm_refl. Qed.
Lemma D_21410 : decode_any W_21410 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_21414 : bv 32 := 0x00867713.
Lemma F_21414 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21560 : word) = Some W_21414.
Proof. vm_refl. Qed.
Lemma D_21414 : decode_any W_21414 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21418 : bv 32 := 0x2c071e63.
Lemma F_21418 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21564 : word) = Some W_21418.
Proof. vm_refl. Qed.
Lemma D_21418 : decode_any W_21418 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_2141c : bv 32 := 0x00467713.
Lemma F_2141c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21568 : word) = Some W_2141c.
Proof. vm_refl. Qed.
Lemma D_2141c : decode_any W_2141c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21420 : bv 32 := 0x32071463.
Lemma F_21420 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2156c : word) = Some W_21420.
Proof. vm_refl. Qed.
Lemma D_21420 : decode_any W_21420 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_21424 : bv 32 := 0x3500006f.
Lemma F_21424 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21570 : word) = Some W_21424.
Proof. vm_refl. Qed.
Lemma D_21424 : decode_any W_21424 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_21428 : bv 32 := 0x0005a703.
Lemma F_21428 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21574 : word) = Some W_21428.
Proof. vm_refl. Qed.
Lemma D_21428 : decode_any W_21428 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2142c : bv 32 := 0x00300813.
Lemma F_2142c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21578 : word) = Some W_2142c.
Proof. vm_refl. Qed.
Lemma D_2142c : decode_any W_2142c = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21430 : bv 32 := 0x11078e63.
Lemma F_21430 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2157c : word) = Some W_21430.
Proof. vm_refl. Qed.
Lemma D_21430 : decode_any W_21430 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_21434 : bv 32 := 0x00200813.
Lemma F_21434 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21580 : word) = Some W_21434.
Proof. vm_refl. Qed.
Lemma D_21434 : decode_any W_21434 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21438 : bv 32 := 0x19079c63.
Lemma F_21438 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21584 : word) = Some W_21438.
Proof. vm_refl. Qed.
Lemma D_21438 : decode_any W_21438 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_2143c : bv 32 := 0x00875793.
Lemma F_2143c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21588 : word) = Some W_2143c.
Proof. vm_refl. Qed.
Lemma D_2143c : decode_any W_2143c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21440 : bv 32 := 0xffe60613.
Lemma F_21440 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2158c : word) = Some W_21440.
Proof. vm_refl. Qed.
Lemma D_21440 : decode_any W_21440 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_21444 : bv 32 := 0x00e68023.
Lemma F_21444 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21590 : word) = Some W_21444.
Proof. vm_refl. Qed.
Lemma D_21444 : decode_any W_21444 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21448 : bv 32 := 0x00f680a3.
Lemma F_21448 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21594 : word) = Some W_21448.
Proof. vm_refl. Qed.
Lemma D_21448 : decode_any W_21448 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2144c : bv 32 := 0x00268693.
Lemma F_2144c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21598 : word) = Some W_2144c.
Proof. vm_refl. Qed.
Lemma D_2144c : decode_any W_2144c = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21450 : bv 32 := 0x01058593.
Lemma F_21450 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2159c : word) = Some W_21450.
Proof. vm_refl. Qed.
Lemma D_21450 : decode_any W_21450 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21454 : bv 32 := 0x01100793.
Lemma F_21454 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215a0 : word) = Some W_21454.
Proof. vm_refl. Qed.
Lemma D_21454 : decode_any W_21454 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_21458 : bv 32 := 0x0107581b.
Lemma F_21458 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215a4 : word) = Some W_21458.
Proof. vm_refl. Qed.
Lemma D_21458 : decode_any W_21458 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2145c : bv 32 := 0xff45a883.
Lemma F_2145c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215a8 : word) = Some W_2145c.
Proof. vm_refl. Qed.
Lemma D_2145c : decode_any W_2145c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_21460 : bv 32 := 0xff85a283.
Lemma F_21460 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215ac : word) = Some W_21460.
Proof. vm_refl. Qed.
Lemma D_21460 : decode_any W_21460 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_21464 : bv 32 := 0xffc5a303.
Lemma F_21464 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215b0 : word) = Some W_21464.
Proof. vm_refl. Qed.
Lemma D_21464 : decode_any W_21464 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_21468 : bv 32 := 0x0005a703.
Lemma F_21468 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215b4 : word) = Some W_21468.
Proof. vm_refl. Qed.
Lemma D_21468 : decode_any W_21468 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2146c : bv 32 := 0x01089393.
Lemma F_2146c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215b8 : word) = Some W_2146c.
Proof. vm_refl. Qed.
Lemma D_2146c : decode_any W_2146c = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21470 : bv 32 := 0x0108d89b.
Lemma F_21470 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215bc : word) = Some W_21470.
Proof. vm_refl. Qed.
Lemma D_21470 : decode_any W_21470 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21474 : bv 32 := 0x0103e833.
Lemma F_21474 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215c0 : word) = Some W_21474.
Proof. vm_refl. Qed.
Lemma D_21474 : decode_any W_21474 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21478 : bv 32 := 0x01029393.
Lemma F_21478 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215c4 : word) = Some W_21478.
Proof. vm_refl. Qed.
Lemma D_21478 : decode_any W_21478 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2147c : bv 32 := 0x0102d29b.
Lemma F_2147c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215c8 : word) = Some W_2147c.
Proof. vm_refl. Qed.
Lemma D_2147c : decode_any W_2147c = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21480 : bv 32 := 0x0113e8b3.
Lemma F_21480 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215cc : word) = Some W_21480.
Proof. vm_refl. Qed.
Lemma D_21480 : decode_any W_21480 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_21484 : bv 32 := 0x01031393.
Lemma F_21484 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215d0 : word) = Some W_21484.
Proof. vm_refl. Qed.
Lemma D_21484 : decode_any W_21484 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21488 : bv 32 := 0x0103531b.
Lemma F_21488 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215d4 : word) = Some W_21488.
Proof. vm_refl. Qed.
Lemma D_21488 : decode_any W_21488 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2148c : bv 32 := 0x0053e2b3.
Lemma F_2148c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215d8 : word) = Some W_2148c.
Proof. vm_refl. Qed.
Lemma D_2148c : decode_any W_2148c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_21490 : bv 32 := 0x01071393.
Lemma F_21490 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215dc : word) = Some W_21490.
Proof. vm_refl. Qed.
Lemma D_21490 : decode_any W_21490 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21494 : bv 32 := 0x0063e333.
Lemma F_21494 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215e0 : word) = Some W_21494.
Proof. vm_refl. Qed.
Lemma D_21494 : decode_any W_21494 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_21498 : bv 32 := 0xff060613.
Lemma F_21498 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215e4 : word) = Some W_21498.
Proof. vm_refl. Qed.
Lemma D_21498 : decode_any W_21498 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_2149c : bv 32 := 0x0106a023.
Lemma F_2149c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215e8 : word) = Some W_2149c.
Proof. vm_refl. Qed.
Lemma D_2149c : decode_any W_2149c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_214a0 : bv 32 := 0x0116a223.
Lemma F_214a0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215ec : word) = Some W_214a0.
Proof. vm_refl. Qed.
Lemma D_214a0 : decode_any W_214a0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_214a4 : bv 32 := 0x0056a423.
Lemma F_214a4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215f0 : word) = Some W_214a4.
Proof. vm_refl. Qed.
Lemma D_214a4 : decode_any W_214a4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_214a8 : bv 32 := 0x0066a623.
Lemma F_214a8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215f4 : word) = Some W_214a8.
Proof. vm_refl. Qed.
Lemma D_214a8 : decode_any W_214a8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_214ac : bv 32 := 0x01068693.
Lemma F_214ac : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215f8 : word) = Some W_214ac.
Proof. vm_refl. Qed.
Lemma D_214ac : decode_any W_214ac = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_214b0 : bv 32 := 0x01058593.
Lemma F_214b0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x215fc : word) = Some W_214b0.
Proof. vm_refl. Qed.
Lemma D_214b0 : decode_any W_214b0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_214b4 : bv 32 := 0xfac7e2e3.
Lemma F_214b4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21600 : word) = Some W_214b4.
Proof. vm_refl. Qed.
Lemma D_214b4 : decode_any W_214b4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_214b8 : bv 32 := 0xff258593.
Lemma F_214b8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21604 : word) = Some W_214b8.
Proof. vm_refl. Qed.
Lemma D_214b8 : decode_any W_214b8 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_214bc : bv 32 := 0x01000713.
Lemma F_214bc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21608 : word) = Some W_214bc.
Proof. vm_refl. Qed.
Lemma D_214bc : decode_any W_214bc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_214c0 : bv 32 := 0xf4e66ae3.
Lemma F_214c0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2160c : word) = Some W_214c0.
Proof. vm_refl. Qed.
Lemma D_214c0 : decode_any W_214c0 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_214c4 : bv 32 := 0x19c0006f.
Lemma F_214c4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21610 : word) = Some W_214c4.
Proof. vm_refl. Qed.
Lemma D_214c4 : decode_any W_214c4 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_214c8 : bv 32 := 0x00050693.
Lemma F_214c8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21614 : word) = Some W_214c8.
Proof. vm_refl. Qed.
Lemma D_214c8 : decode_any W_214c8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_214cc : bv 32 := 0x00357793.
Lemma F_214cc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21618 : word) = Some W_214cc.
Proof. vm_refl. Qed.
Lemma D_214cc : decode_any W_214cc = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_214d0 : bv 32 := 0xf2079ae3.
Lemma F_214d0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2161c : word) = Some W_214d0.
Proof. vm_refl. Qed.
Lemma D_214d0 : decode_any W_214d0 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_214d4 : bv 32 := 0x01000713.
Lemma F_214d4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21620 : word) = Some W_214d4.
Proof. vm_refl. Qed.
Lemma D_214d4 : decode_any W_214d4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_214d8 : bv 32 := 0x02e66c63.
Lemma F_214d8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21624 : word) = Some W_214d8.
Proof. vm_refl. Qed.
Lemma D_214d8 : decode_any W_214d8 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_214dc : bv 32 := 0x00f00713.
Lemma F_214dc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21628 : word) = Some W_214dc.
Proof. vm_refl. Qed.
Lemma D_214dc : decode_any W_214dc = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_214e0 : bv 32 := 0x0005a783.
Lemma F_214e0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2162c : word) = Some W_214e0.
Proof. vm_refl. Qed.
Lemma D_214e0 : decode_any W_214e0 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_214e4 : bv 32 := 0x0045a803.
Lemma F_214e4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21630 : word) = Some W_214e4.
Proof. vm_refl. Qed.
Lemma D_214e4 : decode_any W_214e4 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_214e8 : bv 32 := 0x0085a883.
Lemma F_214e8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21634 : word) = Some W_214e8.
Proof. vm_refl. Qed.
Lemma D_214e8 : decode_any W_214e8 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_214ec : bv 32 := 0x00c5a283.
Lemma F_214ec : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21638 : word) = Some W_214ec.
Proof. vm_refl. Qed.
Lemma D_214ec : decode_any W_214ec = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_214f0 : bv 32 := 0x01058593.
Lemma F_214f0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2163c : word) = Some W_214f0.
Proof. vm_refl. Qed.
Lemma D_214f0 : decode_any W_214f0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_214f4 : bv 32 := 0xff060613.
Lemma F_214f4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21640 : word) = Some W_214f4.
Proof. vm_refl. Qed.
Lemma D_214f4 : decode_any W_214f4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_214f8 : bv 32 := 0x00f6a023.
Lemma F_214f8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21644 : word) = Some W_214f8.
Proof. vm_refl. Qed.
Lemma D_214f8 : decode_any W_214f8 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_214fc : bv 32 := 0x0106a223.
Lemma F_214fc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21648 : word) = Some W_214fc.
Proof. vm_refl. Qed.
Lemma D_214fc : decode_any W_214fc = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21500 : bv 32 := 0x0116a423.
Lemma F_21500 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2164c : word) = Some W_21500.
Proof. vm_refl. Qed.
Lemma D_21500 : decode_any W_21500 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21504 : bv 32 := 0x0056a623.
Lemma F_21504 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21650 : word) = Some W_21504.
Proof. vm_refl. Qed.
Lemma D_21504 : decode_any W_21504 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21508 : bv 32 := 0x01068693.
Lemma F_21508 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21654 : word) = Some W_21508.
Proof. vm_refl. Qed.
Lemma D_21508 : decode_any W_21508 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2150c : bv 32 := 0xfcc76ae3.
Lemma F_2150c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21658 : word) = Some W_2150c.
Proof. vm_refl. Qed.
Lemma D_2150c : decode_any W_2150c = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_21510 : bv 32 := 0x00800713.
Lemma F_21510 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2165c : word) = Some W_21510.
Proof. vm_refl. Qed.
Lemma D_21510 : decode_any W_21510 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21514 : bv 32 := 0x00e66e63.
Lemma F_21514 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21660 : word) = Some W_21514.
Proof. vm_refl. Qed.
Lemma D_21514 : decode_any W_21514 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_21518 : bv 32 := 0x0005a703.
Lemma F_21518 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21664 : word) = Some W_21518.
Proof. vm_refl. Qed.
Lemma D_21518 : decode_any W_21518 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2151c : bv 32 := 0x0045a783.
Lemma F_2151c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21668 : word) = Some W_2151c.
Proof. vm_refl. Qed.
Lemma D_2151c : decode_any W_2151c = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21520 : bv 32 := 0x00e6a023.
Lemma F_21520 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2166c : word) = Some W_21520.
Proof. vm_refl. Qed.
Lemma D_21520 : decode_any W_21520 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21524 : bv 32 := 0x00f6a223.
Lemma F_21524 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21670 : word) = Some W_21524.
Proof. vm_refl. Qed.
Lemma D_21524 : decode_any W_21524 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21528 : bv 32 := 0x00868693.
Lemma F_21528 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21674 : word) = Some W_21528.
Proof. vm_refl. Qed.
Lemma D_21528 : decode_any W_21528 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2152c : bv 32 := 0x00858593.
Lemma F_2152c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21678 : word) = Some W_2152c.
Proof. vm_refl. Qed.
Lemma D_2152c : decode_any W_2152c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21530 : bv 32 := 0x00467713.
Lemma F_21530 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2167c : word) = Some W_21530.
Proof. vm_refl. Qed.
Lemma D_21530 : decode_any W_21530 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21534 : bv 32 := 0x24070063.
Lemma F_21534 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21680 : word) = Some W_21534.
Proof. vm_refl. Qed.
Lemma D_21534 : decode_any W_21534 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_21538 : bv 32 := 0x0005a703.
Lemma F_21538 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21684 : word) = Some W_21538.
Proof. vm_refl. Qed.
Lemma D_21538 : decode_any W_21538 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2153c : bv 32 := 0x00458593.
Lemma F_2153c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21688 : word) = Some W_2153c.
Proof. vm_refl. Qed.
Lemma D_2153c : decode_any W_2153c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21540 : bv 32 := 0x00e6a023.
Lemma F_21540 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2168c : word) = Some W_21540.
Proof. vm_refl. Qed.
Lemma D_21540 : decode_any W_21540 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21544 : bv 32 := 0x00468693.
Lemma F_21544 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21690 : word) = Some W_21544.
Proof. vm_refl. Qed.
Lemma D_21544 : decode_any W_21544 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21548 : bv 32 := 0x22c0006f.
Lemma F_21548 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21694 : word) = Some W_21548.
Proof. vm_refl. Qed.
Lemma D_21548 : decode_any W_21548 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_2154c : bv 32 := 0x00e68023.
Lemma F_2154c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21698 : word) = Some W_2154c.
Proof. vm_refl. Qed.
Lemma D_2154c : decode_any W_2154c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21550 : bv 32 := 0x00168693.
Lemma F_21550 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2169c : word) = Some W_21550.
Proof. vm_refl. Qed.
Lemma D_21550 : decode_any W_21550 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21554 : bv 32 := 0xfff60613.
Lemma F_21554 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216a0 : word) = Some W_21554.
Proof. vm_refl. Qed.
Lemma D_21554 : decode_any W_21554 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_21558 : bv 32 := 0x01058593.
Lemma F_21558 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216a4 : word) = Some W_21558.
Proof. vm_refl. Qed.
Lemma D_21558 : decode_any W_21558 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2155c : bv 32 := 0x01200793.
Lemma F_2155c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216a8 : word) = Some W_2155c.
Proof. vm_refl. Qed.
Lemma D_2155c : decode_any W_2155c = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_21560 : bv 32 := 0x0087581b.
Lemma F_21560 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216ac : word) = Some W_21560.
Proof. vm_refl. Qed.
Lemma D_21560 : decode_any W_21560 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21564 : bv 32 := 0xff45a883.
Lemma F_21564 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216b0 : word) = Some W_21564.
Proof. vm_refl. Qed.
Lemma D_21564 : decode_any W_21564 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_21568 : bv 32 := 0xff85a283.
Lemma F_21568 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216b4 : word) = Some W_21568.
Proof. vm_refl. Qed.
Lemma D_21568 : decode_any W_21568 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_2156c : bv 32 := 0xffc5a303.
Lemma F_2156c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216b8 : word) = Some W_2156c.
Proof. vm_refl. Qed.
Lemma D_2156c : decode_any W_2156c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_21570 : bv 32 := 0x0005a703.
Lemma F_21570 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216bc : word) = Some W_21570.
Proof. vm_refl. Qed.
Lemma D_21570 : decode_any W_21570 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21574 : bv 32 := 0x01889393.
Lemma F_21574 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216c0 : word) = Some W_21574.
Proof. vm_refl. Qed.
Lemma D_21574 : decode_any W_21574 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21578 : bv 32 := 0x0088d89b.
Lemma F_21578 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216c4 : word) = Some W_21578.
Proof. vm_refl. Qed.
Lemma D_21578 : decode_any W_21578 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2157c : bv 32 := 0x0103e833.
Lemma F_2157c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216c8 : word) = Some W_2157c.
Proof. vm_refl. Qed.
Lemma D_2157c : decode_any W_2157c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21580 : bv 32 := 0x01829393.
Lemma F_21580 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216cc : word) = Some W_21580.
Proof. vm_refl. Qed.
Lemma D_21580 : decode_any W_21580 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21584 : bv 32 := 0x0082d29b.
Lemma F_21584 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216d0 : word) = Some W_21584.
Proof. vm_refl. Qed.
Lemma D_21584 : decode_any W_21584 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21588 : bv 32 := 0x0113e8b3.
Lemma F_21588 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216d4 : word) = Some W_21588.
Proof. vm_refl. Qed.
Lemma D_21588 : decode_any W_21588 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_2158c : bv 32 := 0x01831393.
Lemma F_2158c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216d8 : word) = Some W_2158c.
Proof. vm_refl. Qed.
Lemma D_2158c : decode_any W_2158c = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21590 : bv 32 := 0x0083531b.
Lemma F_21590 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216dc : word) = Some W_21590.
Proof. vm_refl. Qed.
Lemma D_21590 : decode_any W_21590 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21594 : bv 32 := 0x0053e2b3.
Lemma F_21594 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216e0 : word) = Some W_21594.
Proof. vm_refl. Qed.
Lemma D_21594 : decode_any W_21594 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_21598 : bv 32 := 0x01871393.
Lemma F_21598 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216e4 : word) = Some W_21598.
Proof. vm_refl. Qed.
Lemma D_21598 : decode_any W_21598 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_2159c : bv 32 := 0x0063e333.
Lemma F_2159c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216e8 : word) = Some W_2159c.
Proof. vm_refl. Qed.
Lemma D_2159c : decode_any W_2159c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_215a0 : bv 32 := 0xff060613.
Lemma F_215a0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216ec : word) = Some W_215a0.
Proof. vm_refl. Qed.
Lemma D_215a0 : decode_any W_215a0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_215a4 : bv 32 := 0x0106a023.
Lemma F_215a4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216f0 : word) = Some W_215a4.
Proof. vm_refl. Qed.
Lemma D_215a4 : decode_any W_215a4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_215a8 : bv 32 := 0x0116a223.
Lemma F_215a8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216f4 : word) = Some W_215a8.
Proof. vm_refl. Qed.
Lemma D_215a8 : decode_any W_215a8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_215ac : bv 32 := 0x0056a423.
Lemma F_215ac : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216f8 : word) = Some W_215ac.
Proof. vm_refl. Qed.
Lemma D_215ac : decode_any W_215ac = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_215b0 : bv 32 := 0x0066a623.
Lemma F_215b0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x216fc : word) = Some W_215b0.
Proof. vm_refl. Qed.
Lemma D_215b0 : decode_any W_215b0 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_215b4 : bv 32 := 0x01068693.
Lemma F_215b4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21700 : word) = Some W_215b4.
Proof. vm_refl. Qed.
Lemma D_215b4 : decode_any W_215b4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_215b8 : bv 32 := 0x01058593.
Lemma F_215b8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21704 : word) = Some W_215b8.
Proof. vm_refl. Qed.
Lemma D_215b8 : decode_any W_215b8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_215bc : bv 32 := 0xfac7e2e3.
Lemma F_215bc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21708 : word) = Some W_215bc.
Proof. vm_refl. Qed.
Lemma D_215bc : decode_any W_215bc = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_215c0 : bv 32 := 0xff158593.
Lemma F_215c0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2170c : word) = Some W_215c0.
Proof. vm_refl. Qed.
Lemma D_215c0 : decode_any W_215c0 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_215c4 : bv 32 := 0x01000713.
Lemma F_215c4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21710 : word) = Some W_215c4.
Proof. vm_refl. Qed.
Lemma D_215c4 : decode_any W_215c4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_215c8 : bv 32 := 0xe4e666e3.
Lemma F_215c8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21714 : word) = Some W_215c8.
Proof. vm_refl. Qed.
Lemma D_215c8 : decode_any W_215c8 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_215cc : bv 32 := 0x0940006f.
Lemma F_215cc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21718 : word) = Some W_215cc.
Proof. vm_refl. Qed.
Lemma D_215cc : decode_any W_215cc = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_215d0 : bv 32 := 0x00875793.
Lemma F_215d0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2171c : word) = Some W_215d0.
Proof. vm_refl. Qed.
Lemma D_215d0 : decode_any W_215d0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_215d4 : bv 32 := 0x01075813.
Lemma F_215d4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21720 : word) = Some W_215d4.
Proof. vm_refl. Qed.
Lemma D_215d4 : decode_any W_215d4 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_215d8 : bv 32 := 0xffd60613.
Lemma F_215d8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21724 : word) = Some W_215d8.
Proof. vm_refl. Qed.
Lemma D_215d8 : decode_any W_215d8 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_215dc : bv 32 := 0x00e68023.
Lemma F_215dc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21728 : word) = Some W_215dc.
Proof. vm_refl. Qed.
Lemma D_215dc : decode_any W_215dc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_215e0 : bv 32 := 0x00f680a3.
Lemma F_215e0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2172c : word) = Some W_215e0.
Proof. vm_refl. Qed.
Lemma D_215e0 : decode_any W_215e0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_215e4 : bv 32 := 0x01068123.
Lemma F_215e4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21730 : word) = Some W_215e4.
Proof. vm_refl. Qed.
Lemma D_215e4 : decode_any W_215e4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_215e8 : bv 32 := 0x00368693.
Lemma F_215e8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21734 : word) = Some W_215e8.
Proof. vm_refl. Qed.
Lemma D_215e8 : decode_any W_215e8 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_215ec : bv 32 := 0x01058593.
Lemma F_215ec : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21738 : word) = Some W_215ec.
Proof. vm_refl. Qed.
Lemma D_215ec : decode_any W_215ec = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_215f0 : bv 32 := 0x01000793.
Lemma F_215f0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2173c : word) = Some W_215f0.
Proof. vm_refl. Qed.
Lemma D_215f0 : decode_any W_215f0 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_215f4 : bv 32 := 0x0187581b.
Lemma F_215f4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21740 : word) = Some W_215f4.
Proof. vm_refl. Qed.
Lemma D_215f4 : decode_any W_215f4 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_215f8 : bv 32 := 0xff45a883.
Lemma F_215f8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21744 : word) = Some W_215f8.
Proof. vm_refl. Qed.
Lemma D_215f8 : decode_any W_215f8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_215fc : bv 32 := 0xff85a283.
Lemma F_215fc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21748 : word) = Some W_215fc.
Proof. vm_refl. Qed.
Lemma D_215fc : decode_any W_215fc = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_21600 : bv 32 := 0xffc5a303.
Lemma F_21600 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2174c : word) = Some W_21600.
Proof. vm_refl. Qed.
Lemma D_21600 : decode_any W_21600 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_21604 : bv 32 := 0x0005a703.
Lemma F_21604 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21750 : word) = Some W_21604.
Proof. vm_refl. Qed.
Lemma D_21604 : decode_any W_21604 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21608 : bv 32 := 0x00889393.
Lemma F_21608 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21754 : word) = Some W_21608.
Proof. vm_refl. Qed.
Lemma D_21608 : decode_any W_21608 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2160c : bv 32 := 0x0188d89b.
Lemma F_2160c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21758 : word) = Some W_2160c.
Proof. vm_refl. Qed.
Lemma D_2160c : decode_any W_2160c = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21610 : bv 32 := 0x0103e833.
Lemma F_21610 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2175c : word) = Some W_21610.
Proof. vm_refl. Qed.
Lemma D_21610 : decode_any W_21610 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21614 : bv 32 := 0x00829393.
Lemma F_21614 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21760 : word) = Some W_21614.
Proof. vm_refl. Qed.
Lemma D_21614 : decode_any W_21614 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21618 : bv 32 := 0x0182d29b.
Lemma F_21618 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21764 : word) = Some W_21618.
Proof. vm_refl. Qed.
Lemma D_21618 : decode_any W_21618 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_2161c : bv 32 := 0x0113e8b3.
Lemma F_2161c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21768 : word) = Some W_2161c.
Proof. vm_refl. Qed.
Lemma D_2161c : decode_any W_2161c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_21620 : bv 32 := 0x00831393.
Lemma F_21620 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2176c : word) = Some W_21620.
Proof. vm_refl. Qed.
Lemma D_21620 : decode_any W_21620 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21624 : bv 32 := 0x0183531b.
Lemma F_21624 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21770 : word) = Some W_21624.
Proof. vm_refl. Qed.
Lemma D_21624 : decode_any W_21624 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_21628 : bv 32 := 0x0053e2b3.
Lemma F_21628 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21774 : word) = Some W_21628.
Proof. vm_refl. Qed.
Lemma D_21628 : decode_any W_21628 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_2162c : bv 32 := 0x00871393.
Lemma F_2162c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21778 : word) = Some W_2162c.
Proof. vm_refl. Qed.
Lemma D_2162c : decode_any W_2162c = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21630 : bv 32 := 0x0063e333.
Lemma F_21630 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2177c : word) = Some W_21630.
Proof. vm_refl. Qed.
Lemma D_21630 : decode_any W_21630 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_21634 : bv 32 := 0xff060613.
Lemma F_21634 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21780 : word) = Some W_21634.
Proof. vm_refl. Qed.
Lemma D_21634 : decode_any W_21634 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_21638 : bv 32 := 0x0106a023.
Lemma F_21638 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21784 : word) = Some W_21638.
Proof. vm_refl. Qed.
Lemma D_21638 : decode_any W_21638 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2163c : bv 32 := 0x0116a223.
Lemma F_2163c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21788 : word) = Some W_2163c.
Proof. vm_refl. Qed.
Lemma D_2163c : decode_any W_2163c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21640 : bv 32 := 0x0056a423.
Lemma F_21640 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2178c : word) = Some W_21640.
Proof. vm_refl. Qed.
Lemma D_21640 : decode_any W_21640 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21644 : bv 32 := 0x0066a623.
Lemma F_21644 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21790 : word) = Some W_21644.
Proof. vm_refl. Qed.
Lemma D_21644 : decode_any W_21644 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_21648 : bv 32 := 0x01068693.
Lemma F_21648 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21794 : word) = Some W_21648.
Proof. vm_refl. Qed.
Lemma D_21648 : decode_any W_21648 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2164c : bv 32 := 0x01058593.
Lemma F_2164c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21798 : word) = Some W_2164c.
Proof. vm_refl. Qed.
Lemma D_2164c : decode_any W_2164c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_21650 : bv 32 := 0xfac7e2e3.
Lemma F_21650 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2179c : word) = Some W_21650.
Proof. vm_refl. Qed.
Lemma D_21650 : decode_any W_21650 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_21654 : bv 32 := 0xff358593.
Lemma F_21654 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217a0 : word) = Some W_21654.
Proof. vm_refl. Qed.
Lemma D_21654 : decode_any W_21654 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_21658 : bv 32 := 0x01000713.
Lemma F_21658 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217a4 : word) = Some W_21658.
Proof. vm_refl. Qed.
Lemma D_21658 : decode_any W_21658 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2165c : bv 32 := 0xdae66ce3.
Lemma F_2165c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217a8 : word) = Some W_2165c.
Proof. vm_refl. Qed.
Lemma D_2165c : decode_any W_2165c = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_21660 : bv 32 := 0x0005c703.
Lemma F_21660 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217ac : word) = Some W_21660.
Proof. vm_refl. Qed.
Lemma D_21660 : decode_any W_21660 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21664 : bv 32 := 0x0015c783.
Lemma F_21664 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217b0 : word) = Some W_21664.
Proof. vm_refl. Qed.
Lemma D_21664 : decode_any W_21664 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21668 : bv 32 := 0x0025c803.
Lemma F_21668 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217b4 : word) = Some W_21668.
Proof. vm_refl. Qed.
Lemma D_21668 : decode_any W_21668 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_2166c : bv 32 := 0x0035c883.
Lemma F_2166c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217b8 : word) = Some W_2166c.
Proof. vm_refl. Qed.
Lemma D_2166c : decode_any W_2166c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21670 : bv 32 := 0x0045c283.
Lemma F_21670 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217bc : word) = Some W_21670.
Proof. vm_refl. Qed.
Lemma D_21670 : decode_any W_21670 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21674 : bv 32 := 0x0055c303.
Lemma F_21674 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217c0 : word) = Some W_21674.
Proof. vm_refl. Qed.
Lemma D_21674 : decode_any W_21674 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_21678 : bv 32 := 0x0065c383.
Lemma F_21678 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217c4 : word) = Some W_21678.
Proof. vm_refl. Qed.
Lemma D_21678 : decode_any W_21678 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_2167c : bv 32 := 0x0075ce03.
Lemma F_2167c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217c8 : word) = Some W_2167c.
Proof. vm_refl. Qed.
Lemma D_2167c : decode_any W_2167c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_21680 : bv 32 := 0x00e68023.
Lemma F_21680 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217cc : word) = Some W_21680.
Proof. vm_refl. Qed.
Lemma D_21680 : decode_any W_21680 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21684 : bv 32 := 0x00f680a3.
Lemma F_21684 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217d0 : word) = Some W_21684.
Proof. vm_refl. Qed.
Lemma D_21684 : decode_any W_21684 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21688 : bv 32 := 0x01068123.
Lemma F_21688 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217d4 : word) = Some W_21688.
Proof. vm_refl. Qed.
Lemma D_21688 : decode_any W_21688 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_2168c : bv 32 := 0x011681a3.
Lemma F_2168c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217d8 : word) = Some W_2168c.
Proof. vm_refl. Qed.
Lemma D_2168c : decode_any W_2168c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21690 : bv 32 := 0x0085c703.
Lemma F_21690 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217dc : word) = Some W_21690.
Proof. vm_refl. Qed.
Lemma D_21690 : decode_any W_21690 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21694 : bv 32 := 0x0095c783.
Lemma F_21694 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217e0 : word) = Some W_21694.
Proof. vm_refl. Qed.
Lemma D_21694 : decode_any W_21694 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_21698 : bv 32 := 0x00a5c803.
Lemma F_21698 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217e4 : word) = Some W_21698.
Proof. vm_refl. Qed.
Lemma D_21698 : decode_any W_21698 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_2169c : bv 32 := 0x00b5c883.
Lemma F_2169c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217e8 : word) = Some W_2169c.
Proof. vm_refl. Qed.
Lemma D_2169c : decode_any W_2169c = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_216a0 : bv 32 := 0x00568223.
Lemma F_216a0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217ec : word) = Some W_216a0.
Proof. vm_refl. Qed.
Lemma D_216a0 : decode_any W_216a0 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_216a4 : bv 32 := 0x006682a3.
Lemma F_216a4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217f0 : word) = Some W_216a4.
Proof. vm_refl. Qed.
Lemma D_216a4 : decode_any W_216a4 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_216a8 : bv 32 := 0x00768323.
Lemma F_216a8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217f4 : word) = Some W_216a8.
Proof. vm_refl. Qed.
Lemma D_216a8 : decode_any W_216a8 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_216ac : bv 32 := 0x01c683a3.
Lemma F_216ac : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217f8 : word) = Some W_216ac.
Proof. vm_refl. Qed.
Lemma D_216ac : decode_any W_216ac = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_216b0 : bv 32 := 0x00c5c283.
Lemma F_216b0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x217fc : word) = Some W_216b0.
Proof. vm_refl. Qed.
Lemma D_216b0 : decode_any W_216b0 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_216b4 : bv 32 := 0x00d5c303.
Lemma F_216b4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21800 : word) = Some W_216b4.
Proof. vm_refl. Qed.
Lemma D_216b4 : decode_any W_216b4 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_216b8 : bv 32 := 0x00e5c383.
Lemma F_216b8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21804 : word) = Some W_216b8.
Proof. vm_refl. Qed.
Lemma D_216b8 : decode_any W_216b8 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_216bc : bv 32 := 0x00f5ce03.
Lemma F_216bc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21808 : word) = Some W_216bc.
Proof. vm_refl. Qed.
Lemma D_216bc : decode_any W_216bc = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_216c0 : bv 32 := 0x01058593.
Lemma F_216c0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2180c : word) = Some W_216c0.
Proof. vm_refl. Qed.
Lemma D_216c0 : decode_any W_216c0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_216c4 : bv 32 := 0x00e68423.
Lemma F_216c4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21810 : word) = Some W_216c4.
Proof. vm_refl. Qed.
Lemma D_216c4 : decode_any W_216c4 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_216c8 : bv 32 := 0x00f684a3.
Lemma F_216c8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21814 : word) = Some W_216c8.
Proof. vm_refl. Qed.
Lemma D_216c8 : decode_any W_216c8 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_216cc : bv 32 := 0x01068523.
Lemma F_216cc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21818 : word) = Some W_216cc.
Proof. vm_refl. Qed.
Lemma D_216cc : decode_any W_216cc = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_216d0 : bv 32 := 0x011685a3.
Lemma F_216d0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2181c : word) = Some W_216d0.
Proof. vm_refl. Qed.
Lemma D_216d0 : decode_any W_216d0 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_216d4 : bv 32 := 0x01068713.
Lemma F_216d4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21820 : word) = Some W_216d4.
Proof. vm_refl. Qed.
Lemma D_216d4 : decode_any W_216d4 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_216d8 : bv 32 := 0x00568623.
Lemma F_216d8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21824 : word) = Some W_216d8.
Proof. vm_refl. Qed.
Lemma D_216d8 : decode_any W_216d8 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_216dc : bv 32 := 0x006686a3.
Lemma F_216dc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21828 : word) = Some W_216dc.
Proof. vm_refl. Qed.
Lemma D_216dc : decode_any W_216dc = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_216e0 : bv 32 := 0x00768723.
Lemma F_216e0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2182c : word) = Some W_216e0.
Proof. vm_refl. Qed.
Lemma D_216e0 : decode_any W_216e0 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_216e4 : bv 32 := 0x01c687a3.
Lemma F_216e4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21830 : word) = Some W_216e4.
Proof. vm_refl. Qed.
Lemma D_216e4 : decode_any W_216e4 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_216e8 : bv 32 := 0x00070693.
Lemma F_216e8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21834 : word) = Some W_216e8.
Proof. vm_refl. Qed.
Lemma D_216e8 : decode_any W_216e8 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_216ec : bv 32 := 0x00867713.
Lemma F_216ec : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21838 : word) = Some W_216ec.
Proof. vm_refl. Qed.
Lemma D_216ec : decode_any W_216ec = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_216f0 : bv 32 := 0xd20706e3.
Lemma F_216f0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2183c : word) = Some W_216f0.
Proof. vm_refl. Qed.
Lemma D_216f0 : decode_any W_216f0 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_216f4 : bv 32 := 0x0005c703.
Lemma F_216f4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21840 : word) = Some W_216f4.
Proof. vm_refl. Qed.
Lemma D_216f4 : decode_any W_216f4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_216f8 : bv 32 := 0x0015c783.
Lemma F_216f8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21844 : word) = Some W_216f8.
Proof. vm_refl. Qed.
Lemma D_216f8 : decode_any W_216f8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_216fc : bv 32 := 0x0025c803.
Lemma F_216fc : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21848 : word) = Some W_216fc.
Proof. vm_refl. Qed.
Lemma D_216fc : decode_any W_216fc = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21700 : bv 32 := 0x0035c883.
Lemma F_21700 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2184c : word) = Some W_21700.
Proof. vm_refl. Qed.
Lemma D_21700 : decode_any W_21700 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21704 : bv 32 := 0x0045c283.
Lemma F_21704 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21850 : word) = Some W_21704.
Proof. vm_refl. Qed.
Lemma D_21704 : decode_any W_21704 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21708 : bv 32 := 0x0055c303.
Lemma F_21708 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21854 : word) = Some W_21708.
Proof. vm_refl. Qed.
Lemma D_21708 : decode_any W_21708 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_2170c : bv 32 := 0x0065c383.
Lemma F_2170c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21858 : word) = Some W_2170c.
Proof. vm_refl. Qed.
Lemma D_2170c : decode_any W_2170c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_21710 : bv 32 := 0x0075ce03.
Lemma F_21710 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2185c : word) = Some W_21710.
Proof. vm_refl. Qed.
Lemma D_21710 : decode_any W_21710 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_21714 : bv 32 := 0x00858593.
Lemma F_21714 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21860 : word) = Some W_21714.
Proof. vm_refl. Qed.
Lemma D_21714 : decode_any W_21714 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_21718 : bv 32 := 0x00e68023.
Lemma F_21718 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21864 : word) = Some W_21718.
Proof. vm_refl. Qed.
Lemma D_21718 : decode_any W_21718 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2171c : bv 32 := 0x00f680a3.
Lemma F_2171c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21868 : word) = Some W_2171c.
Proof. vm_refl. Qed.
Lemma D_2171c : decode_any W_2171c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21720 : bv 32 := 0x01068123.
Lemma F_21720 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2186c : word) = Some W_21720.
Proof. vm_refl. Qed.
Lemma D_21720 : decode_any W_21720 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21724 : bv 32 := 0x011681a3.
Lemma F_21724 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21870 : word) = Some W_21724.
Proof. vm_refl. Qed.
Lemma D_21724 : decode_any W_21724 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21728 : bv 32 := 0x00868713.
Lemma F_21728 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21874 : word) = Some W_21728.
Proof. vm_refl. Qed.
Lemma D_21728 : decode_any W_21728 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_2172c : bv 32 := 0x00568223.
Lemma F_2172c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21878 : word) = Some W_2172c.
Proof. vm_refl. Qed.
Lemma D_2172c : decode_any W_2172c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21730 : bv 32 := 0x006682a3.
Lemma F_21730 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2187c : word) = Some W_21730.
Proof. vm_refl. Qed.
Lemma D_21730 : decode_any W_21730 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_21734 : bv 32 := 0x00768323.
Lemma F_21734 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21880 : word) = Some W_21734.
Proof. vm_refl. Qed.
Lemma D_21734 : decode_any W_21734 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_21738 : bv 32 := 0x01c683a3.
Lemma F_21738 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21884 : word) = Some W_21738.
Proof. vm_refl. Qed.
Lemma D_21738 : decode_any W_21738 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_2173c : bv 32 := 0x00070693.
Lemma F_2173c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21888 : word) = Some W_2173c.
Proof. vm_refl. Qed.
Lemma D_2173c : decode_any W_2173c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21740 : bv 32 := 0x00467713.
Lemma F_21740 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2188c : word) = Some W_21740.
Proof. vm_refl. Qed.
Lemma D_21740 : decode_any W_21740 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21744 : bv 32 := 0x02070863.
Lemma F_21744 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21890 : word) = Some W_21744.
Proof. vm_refl. Qed.
Lemma D_21744 : decode_any W_21744 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_21748 : bv 32 := 0x0005c703.
Lemma F_21748 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21894 : word) = Some W_21748.
Proof. vm_refl. Qed.
Lemma D_21748 : decode_any W_21748 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2174c : bv 32 := 0x0015c783.
Lemma F_2174c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21898 : word) = Some W_2174c.
Proof. vm_refl. Qed.
Lemma D_2174c : decode_any W_2174c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21750 : bv 32 := 0x0025c803.
Lemma F_21750 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x2189c : word) = Some W_21750.
Proof. vm_refl. Qed.
Lemma D_21750 : decode_any W_21750 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21754 : bv 32 := 0x0035c883.
Lemma F_21754 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218a0 : word) = Some W_21754.
Proof. vm_refl. Qed.
Lemma D_21754 : decode_any W_21754 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21758 : bv 32 := 0x00458593.
Lemma F_21758 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218a4 : word) = Some W_21758.
Proof. vm_refl. Qed.
Lemma D_21758 : decode_any W_21758 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_2175c : bv 32 := 0x00468293.
Lemma F_2175c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218a8 : word) = Some W_2175c.
Proof. vm_refl. Qed.
Lemma D_2175c : decode_any W_2175c = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_21760 : bv 32 := 0x00e68023.
Lemma F_21760 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218ac : word) = Some W_21760.
Proof. vm_refl. Qed.
Lemma D_21760 : decode_any W_21760 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21764 : bv 32 := 0x00f680a3.
Lemma F_21764 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218b0 : word) = Some W_21764.
Proof. vm_refl. Qed.
Lemma D_21764 : decode_any W_21764 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21768 : bv 32 := 0x01068123.
Lemma F_21768 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218b4 : word) = Some W_21768.
Proof. vm_refl. Qed.
Lemma D_21768 : decode_any W_21768 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_2176c : bv 32 := 0x011681a3.
Lemma F_2176c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218b8 : word) = Some W_2176c.
Proof. vm_refl. Qed.
Lemma D_2176c : decode_any W_2176c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_21770 : bv 32 := 0x00028693.
Lemma F_21770 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218bc : word) = Some W_21770.
Proof. vm_refl. Qed.
Lemma D_21770 : decode_any W_21770 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21774 : bv 32 := 0x00267713.
Lemma F_21774 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218c0 : word) = Some W_21774.
Proof. vm_refl. Qed.
Lemma D_21774 : decode_any W_21774 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21778 : bv 32 := 0x00071863.
Lemma F_21778 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218c4 : word) = Some W_21778.
Proof. vm_refl. Qed.
Lemma D_21778 : decode_any W_21778 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2177c : bv 32 := 0x00167613.
Lemma F_2177c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218c8 : word) = Some W_2177c.
Proof. vm_refl. Qed.
Lemma D_2177c : decode_any W_2177c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21780 : bv 32 := 0x02061663.
Lemma F_21780 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218cc : word) = Some W_21780.
Proof. vm_refl. Qed.
Lemma D_21780 : decode_any W_21780 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_21784 : bv 32 := 0x00008067.
Lemma F_21784 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218d0 : word) = Some W_21784.
Proof. vm_refl. Qed.
Lemma D_21784 : decode_any W_21784 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_21788 : bv 32 := 0x0005c703.
Lemma F_21788 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218d4 : word) = Some W_21788.
Proof. vm_refl. Qed.
Lemma D_21788 : decode_any W_21788 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2178c : bv 32 := 0x0015c783.
Lemma F_2178c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218d8 : word) = Some W_2178c.
Proof. vm_refl. Qed.
Lemma D_2178c : decode_any W_2178c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_21790 : bv 32 := 0x00258593.
Lemma F_21790 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218dc : word) = Some W_21790.
Proof. vm_refl. Qed.
Lemma D_21790 : decode_any W_21790 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21794 : bv 32 := 0x00268813.
Lemma F_21794 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218e0 : word) = Some W_21794.
Proof. vm_refl. Qed.
Lemma D_21794 : decode_any W_21794 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_21798 : bv 32 := 0x00e68023.
Lemma F_21798 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218e4 : word) = Some W_21798.
Proof. vm_refl. Qed.
Lemma D_21798 : decode_any W_21798 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2179c : bv 32 := 0x00f680a3.
Lemma F_2179c : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218e8 : word) = Some W_2179c.
Proof. vm_refl. Qed.
Lemma D_2179c : decode_any W_2179c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_217a0 : bv 32 := 0x00080693.
Lemma F_217a0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218ec : word) = Some W_217a0.
Proof. vm_refl. Qed.
Lemma D_217a0 : decode_any W_217a0 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_217a4 : bv 32 := 0x00167613.
Lemma F_217a4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218f0 : word) = Some W_217a4.
Proof. vm_refl. Qed.
Lemma D_217a4 : decode_any W_217a4 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_217a8 : bv 32 := 0xfc060ee3.
Lemma F_217a8 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218f4 : word) = Some W_217a8.
Proof. vm_refl. Qed.
Lemma D_217a8 : decode_any W_217a8 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_217ac : bv 32 := 0x0005c583.
Lemma F_217ac : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218f8 : word) = Some W_217ac.
Proof. vm_refl. Qed.
Lemma D_217ac : decode_any W_217ac = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_217b0 : bv 32 := 0x00b68023.
Lemma F_217b0 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x218fc : word) = Some W_217b0.
Proof. vm_refl. Qed.
Lemma D_217b0 : decode_any W_217b0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_217b4 : bv 32 := 0x00008067.
Lemma F_217b4 : fetch_word Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x21900 : word) = Some W_217b4.
Proof. vm_refl. Qed.
Lemma D_217b4 : decode_any W_217b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
