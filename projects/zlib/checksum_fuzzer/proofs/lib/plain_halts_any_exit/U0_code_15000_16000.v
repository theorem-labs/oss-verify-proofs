(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_154c4 : bv 32 := 0x00008067.
Lemma F_154c4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15570 : word) = Some W_154c4.
Proof. vm_refl. Qed.
Lemma D_154c4 : decode_any W_154c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154c8 : bv 32 := 0xe8010113.
Lemma F_154c8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15574 : word) = Some W_154c8.
Proof. vm_refl. Qed.
Lemma D_154c8 : decode_any W_154c8 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_154cc : bv 32 := 0x16113c23.
Lemma F_154cc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15578 : word) = Some W_154cc.
Proof. vm_refl. Qed.
Lemma D_154cc : decode_any W_154cc = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_154d0 : bv 32 := 0x16813823.
Lemma F_154d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1557c : word) = Some W_154d0.
Proof. vm_refl. Qed.
Lemma D_154d0 : decode_any W_154d0 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_154d4 : bv 32 := 0x16913423.
Lemma F_154d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15580 : word) = Some W_154d4.
Proof. vm_refl. Qed.
Lemma D_154d4 : decode_any W_154d4 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_154d8 : bv 32 := 0x17213023.
Lemma F_154d8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15584 : word) = Some W_154d8.
Proof. vm_refl. Qed.
Lemma D_154d8 : decode_any W_154d8 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_154dc : bv 32 := 0x00058413.
Lemma F_154dc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15588 : word) = Some W_154dc.
Proof. vm_refl. Qed.
Lemma D_154dc : decode_any W_154dc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154e0 : bv 32 := 0x00050493.
Lemma F_154e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1558c : word) = Some W_154e0.
Proof. vm_refl. Qed.
Lemma D_154e0 : decode_any W_154e0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154e4 : bv 32 := 0x03010513.
Lemma F_154e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15590 : word) = Some W_154e4.
Proof. vm_refl. Qed.
Lemma D_154e4 : decode_any W_154e4 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_154e8 : bv 32 := 0x13000613.
Lemma F_154e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15594 : word) = Some W_154e8.
Proof. vm_refl. Qed.
Lemma D_154e8 : decode_any W_154e8 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_154ec : bv 32 := 0x00000593.
Lemma F_154ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15598 : word) = Some W_154ec.
Proof. vm_refl. Qed.
Lemma D_154ec : decode_any W_154ec = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_154f0 : bv 32 := 0x5f1070ef.
Lemma F_154f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1559c : word) = Some W_154f0.
Proof. vm_refl. Qed.
Lemma D_154f0 : decode_any W_154f0 = Some (Jal 1 32240, 4%Z).
Proof. vm_refl. Qed.

Definition W_154f4 : bv 32 := 0x00009517.
Lemma F_154f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155a0 : word) = Some W_154f4.
Proof. vm_refl. Qed.
Lemma D_154f4 : decode_any W_154f4 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_154f8 : bv 32 := 0x44053503.
Lemma F_154f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155a4 : word) = Some W_154f8.
Proof. vm_refl. Qed.
Lemma D_154f8 : decode_any W_154f8 = Some (Load SZ8 true 10 10 1088, 4%Z).
Proof. vm_refl. Qed.

Definition W_154fc : bv 32 := 0x00953023.
Lemma F_154fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155a8 : word) = Some W_154fc.
Proof. vm_refl. Qed.
Lemma D_154fc : decode_any W_154fc = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15500 : bv 32 := 0x0004b503.
Lemma F_15500 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155ac : word) = Some W_15500.
Proof. vm_refl. Qed.
Lemma D_15500 : decode_any W_15500 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15504 : bv 32 := 0x00848493.
Lemma F_15504 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155b0 : word) = Some W_15504.
Proof. vm_refl. Qed.
Lemma D_15504 : decode_any W_15504 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15508 : bv 32 := 0xfe051ce3.
Lemma F_15508 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155b4 : word) = Some W_15508.
Proof. vm_refl. Qed.
Lemma D_15508 : decode_any W_15508 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_1550c : bv 32 := 0x0003b517.
Lemma F_1550c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155b8 : word) = Some W_1550c.
Proof. vm_refl. Qed.
Lemma D_1550c : decode_any W_1550c = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_15510 : bv 32 := 0xa5850913.
Lemma F_15510 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155bc : word) = Some W_15510.
Proof. vm_refl. Qed.
Lemma D_15510 : decode_any W_15510 = Some (OpImm ALU_ADD 18 10 2648, 4%Z).
Proof. vm_refl. Qed.

Definition W_15514 : bv 32 := 0x00993423.
Lemma F_15514 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155c0 : word) = Some W_15514.
Proof. vm_refl. Qed.
Lemma D_15514 : decode_any W_15514 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15518 : bv 32 := 0x0004b583.
Lemma F_15518 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155c4 : word) = Some W_15518.
Proof. vm_refl. Qed.
Lemma D_15518 : decode_any W_15518 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1551c : bv 32 := 0x04058c63.
Lemma F_1551c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155c8 : word) = Some W_1551c.
Proof. vm_refl. Qed.
Lemma D_1551c : decode_any W_1551c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_15520 : bv 32 := 0x01048493.
Lemma F_15520 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155cc : word) = Some W_15520.
Proof. vm_refl. Qed.
Lemma D_15520 : decode_any W_15520 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15524 : bv 32 := 0x02500513.
Lemma F_15524 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155d0 : word) = Some W_15524.
Proof. vm_refl. Qed.
Lemma D_15524 : decode_any W_15524 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_15528 : bv 32 := 0x03010613.
Lemma F_15528 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155d4 : word) = Some W_15528.
Proof. vm_refl. Qed.
Lemma D_15528 : decode_any W_15528 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1552c : bv 32 := 0x0100006f.
Lemma F_1552c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155d8 : word) = Some W_1552c.
Proof. vm_refl. Qed.
Lemma D_1552c : decode_any W_1552c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15530 : bv 32 := 0x0004b583.
Lemma F_15530 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155dc : word) = Some W_15530.
Proof. vm_refl. Qed.
Lemma D_15530 : decode_any W_15530 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15534 : bv 32 := 0x01048493.
Lemma F_15534 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155e0 : word) = Some W_15534.
Proof. vm_refl. Qed.
Lemma D_15534 : decode_any W_15534 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15538 : bv 32 := 0x00058e63.
Lemma F_15538 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155e4 : word) = Some W_15538.
Proof. vm_refl. Qed.
Lemma D_15538 : decode_any W_15538 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1553c : bv 32 := 0xfeb56ae3.
Lemma F_1553c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155e8 : word) = Some W_1553c.
Proof. vm_refl. Qed.
Lemma D_1553c : decode_any W_1553c = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_15540 : bv 32 := 0xff84b683.
Lemma F_15540 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155ec : word) = Some W_15540.
Proof. vm_refl. Qed.
Lemma D_15540 : decode_any W_15540 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_15544 : bv 32 := 0x00359593.
Lemma F_15544 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155f0 : word) = Some W_15544.
Proof. vm_refl. Qed.
Lemma D_15544 : decode_any W_15544 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_15548 : bv 32 := 0x00b605b3.
Lemma F_15548 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155f4 : word) = Some W_15548.
Proof. vm_refl. Qed.
Lemma D_15548 : decode_any W_15548 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1554c : bv 32 := 0x00d5b023.
Lemma F_1554c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155f8 : word) = Some W_1554c.
Proof. vm_refl. Qed.
Lemma D_1554c : decode_any W_1554c = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15550 : bv 32 := 0xfe1ff06f.
Lemma F_15550 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x155fc : word) = Some W_15550.
Proof. vm_refl. Qed.
Lemma D_15550 : decode_any W_15550 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_15554 : bv 32 := 0x0b013583.
Lemma F_15554 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15600 : word) = Some W_15554.
Proof. vm_refl. Qed.
Lemma D_15554 : decode_any W_15554 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_15558 : bv 32 := 0x13013503.
Lemma F_15558 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15604 : word) = Some W_15558.
Proof. vm_refl. Qed.
Lemma D_15558 : decode_any W_15558 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_1555c : bv 32 := 0x0003b617.
Lemma F_1555c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15608 : word) = Some W_1555c.
Proof. vm_refl. Qed.
Lemma D_1555c : decode_any W_1555c = Some (Auipc 12 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_15560 : bv 32 := 0xa6b63823.
Lemma F_15560 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1560c : word) = Some W_15560.
Proof. vm_refl. Qed.
Lemma D_15560 : decode_any W_15560 = Some (Store SZ8 12 11 2672, 4%Z).
Proof. vm_refl. Qed.

Definition W_15564 : bv 32 := 0x00050c63.
Lemma F_15564 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15610 : word) = Some W_15564.
Proof. vm_refl. Qed.
Lemma D_15564 : decode_any W_15564 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15568 : bv 32 := 0x0003b597.
Lemma F_15568 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15614 : word) = Some W_15568.
Proof. vm_refl. Qed.
Lemma D_15568 : decode_any W_15568 = Some (Auipc 11 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_1556c : bv 32 := 0x9ea5b223.
Lemma F_1556c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15618 : word) = Some W_1556c.
Proof. vm_refl. Qed.
Lemma D_1556c : decode_any W_1556c = Some (Store SZ8 11 10 2532, 4%Z).
Proof. vm_refl. Qed.

Definition W_15570 : bv 32 := 0x00c0006f.
Lemma F_15570 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1561c : word) = Some W_15570.
Proof. vm_refl. Qed.
Lemma D_15570 : decode_any W_15570 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15574 : bv 32 := 0x0003b517.
Lemma F_15574 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15620 : word) = Some W_15574.
Proof. vm_refl. Qed.
Lemma D_15574 : decode_any W_15574 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_15578 : bv 32 := 0xa4053c23.
Lemma F_15578 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15624 : word) = Some W_15578.
Proof. vm_refl. Qed.
Lemma D_15578 : decode_any W_15578 = Some (Store SZ8 10 0 2648, 4%Z).
Proof. vm_refl. Qed.

Definition W_1557c : bv 32 := 0x06013503.
Lemma F_1557c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15628 : word) = Some W_1557c.
Proof. vm_refl. Qed.
Lemma D_1557c : decode_any W_1557c = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_15580 : bv 32 := 0x02a93823.
Lemma F_15580 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1562c : word) = Some W_15580.
Proof. vm_refl. Qed.
Lemma D_15580 : decode_any W_15580 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_15584 : bv 32 := 0x00041463.
Lemma F_15584 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15630 : word) = Some W_15584.
Proof. vm_refl. Qed.
Lemma D_15584 : decode_any W_15584 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15588 : bv 32 := 0x12813403.
Lemma F_15588 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15634 : word) = Some W_15588.
Proof. vm_refl. Qed.
Lemma D_15588 : decode_any W_15588 = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_1558c : bv 32 := 0x00041663.
Lemma F_1558c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15638 : word) = Some W_1558c.
Proof. vm_refl. Qed.
Lemma D_1558c : decode_any W_1558c = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15590 : bv 32 := 0xffffb517.
Lemma F_15590 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1563c : word) = Some W_15590.
Proof. vm_refl. Qed.
Lemma D_15590 : decode_any W_15590 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

Definition W_15594 : bv 32 := 0xd3450413.
Lemma F_15594 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15640 : word) = Some W_15594.
Proof. vm_refl. Qed.
Lemma D_15594 : decode_any W_15594 = Some (OpImm ALU_ADD 8 10 3380, 4%Z).
Proof. vm_refl. Qed.

Definition W_15598 : bv 32 := 0x00009517.
Lemma F_15598 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15644 : word) = Some W_15598.
Proof. vm_refl. Qed.
Lemma D_15598 : decode_any W_15598 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1559c : bv 32 := 0x3a453583.
Lemma F_1559c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15648 : word) = Some W_1559c.
Proof. vm_refl. Qed.
Lemma D_1559c : decode_any W_1559c = Some (Load SZ8 true 11 10 932, 4%Z).
Proof. vm_refl. Qed.

Definition W_155a0 : bv 32 := 0x00009517.
Lemma F_155a0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1564c : word) = Some W_155a0.
Proof. vm_refl. Qed.
Lemma D_155a0 : decode_any W_155a0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_155a4 : bv 32 := 0x3a453503.
Lemma F_155a4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15650 : word) = Some W_155a4.
Proof. vm_refl. Qed.
Lemma D_155a4 : decode_any W_155a4 = Some (Load SZ8 true 10 10 932, 4%Z).
Proof. vm_refl. Qed.

Definition W_155a8 : bv 32 := 0x0085b023.
Lemma F_155a8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15654 : word) = Some W_155a8.
Proof. vm_refl. Qed.
Lemma D_155a8 : decode_any W_155a8 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_155ac : bv 32 := 0x00140593.
Lemma F_155ac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15658 : word) = Some W_155ac.
Proof. vm_refl. Qed.
Lemma D_155ac : decode_any W_155ac = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_155b0 : bv 32 := 0x00853023.
Lemma F_155b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1565c : word) = Some W_155b0.
Proof. vm_refl. Qed.
Lemma D_155b0 : decode_any W_155b0 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_155b4 : bv 32 := 0x02f00613.
Lemma F_155b4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15660 : word) = Some W_155b4.
Proof. vm_refl. Qed.
Lemma D_155b4 : decode_any W_155b4 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_155b8 : bv 32 := 0x00c0006f.
Lemma F_155b8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15664 : word) = Some W_155b8.
Proof. vm_refl. Qed.
Lemma D_155b8 : decode_any W_155b8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_155bc : bv 32 := 0x00b53023.
Lemma F_155bc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15668 : word) = Some W_155bc.
Proof. vm_refl. Qed.
Lemma D_155bc : decode_any W_155bc = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_155c0 : bv 32 := 0x00158593.
Lemma F_155c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1566c : word) = Some W_155c0.
Proof. vm_refl. Qed.
Lemma D_155c0 : decode_any W_155c0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_155c4 : bv 32 := 0xfff5c683.
Lemma F_155c4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15670 : word) = Some W_155c4.
Proof. vm_refl. Qed.
Lemma D_155c4 : decode_any W_155c4 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_155c8 : bv 32 := 0xfec68ae3.
Lemma F_155c8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15674 : word) = Some W_155c8.
Proof. vm_refl. Qed.
Lemma D_155c8 : decode_any W_155c8 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_155cc : bv 32 := 0xfe069ae3.
Lemma F_155cc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15678 : word) = Some W_155cc.
Proof. vm_refl. Qed.
Lemma D_155cc : decode_any W_155cc = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_155d0 : bv 32 := 0x03010513.
Lemma F_155d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1567c : word) = Some W_155d0.
Proof. vm_refl. Qed.
Lemma D_155d0 : decode_any W_155d0 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_155d4 : bv 32 := 0x214000ef.
Lemma F_155d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15680 : word) = Some W_155d4.
Proof. vm_refl. Qed.
Lemma D_155d4 : decode_any W_155d4 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_155d8 : bv 32 := 0x0f813503.
Lemma F_155d8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15684 : word) = Some W_155d8.
Proof. vm_refl. Qed.
Lemma D_155d8 : decode_any W_155d8 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_155dc : bv 32 := 0x0d9000ef.
Lemma F_155dc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15688 : word) = Some W_155dc.
Proof. vm_refl. Qed.
Lemma D_155dc : decode_any W_155dc = Some (Jal 1 2264, 4%Z).
Proof. vm_refl. Qed.

Definition W_155e0 : bv 32 := 0x08813503.
Lemma F_155e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1568c : word) = Some W_155e0.
Proof. vm_refl. Qed.
Lemma D_155e0 : decode_any W_155e0 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_155e4 : bv 32 := 0x09013583.
Lemma F_155e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15690 : word) = Some W_155e4.
Proof. vm_refl. Qed.
Lemma D_155e4 : decode_any W_155e4 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_155e8 : bv 32 := 0x00b51c63.
Lemma F_155e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15694 : word) = Some W_155e8.
Proof. vm_refl. Qed.
Lemma D_155e8 : decode_any W_155e8 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_155ec : bv 32 := 0x09813503.
Lemma F_155ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15698 : word) = Some W_155ec.
Proof. vm_refl. Qed.
Lemma D_155ec : decode_any W_155ec = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_155f0 : bv 32 := 0x0a013583.
Lemma F_155f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1569c : word) = Some W_155f0.
Proof. vm_refl. Qed.
Lemma D_155f0 : decode_any W_155f0 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_155f4 : bv 32 := 0x00b51663.
Lemma F_155f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156a0 : word) = Some W_155f4.
Proof. vm_refl. Qed.
Lemma D_155f4 : decode_any W_155f4 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_155f8 : bv 32 := 0x0e813503.
Lemma F_155f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156a4 : word) = Some W_155f8.
Proof. vm_refl. Qed.
Lemma D_155f8 : decode_any W_155f8 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_155fc : bv 32 := 0x0e050063.
Lemma F_155fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156a8 : word) = Some W_155fc.
Proof. vm_refl. Qed.
Lemma D_155fc : decode_any W_155fc = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_15600 : bv 32 := 0x00200693.
Lemma F_15600 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156ac : word) = Some W_15600.
Proof. vm_refl. Qed.
Lemma D_15600 : decode_any W_15600 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_15604 : bv 32 := 0x00100793.
Lemma F_15604 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156b0 : word) = Some W_15604.
Proof. vm_refl. Qed.
Lemma D_15604 : decode_any W_15604 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15608 : bv 32 := 0x00013423.
Lemma F_15608 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156b4 : word) = Some W_15608.
Proof. vm_refl. Qed.
Lemma D_15608 : decode_any W_15608 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1560c : bv 32 := 0x00013823.
Lemma F_1560c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156b8 : word) = Some W_1560c.
Proof. vm_refl. Qed.
Lemma D_1560c : decode_any W_1560c = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15610 : bv 32 := 0x04900893.
Lemma F_15610 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156bc : word) = Some W_15610.
Proof. vm_refl. Qed.
Lemma D_15610 : decode_any W_15610 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_15614 : bv 32 := 0x01810513.
Lemma F_15614 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156c0 : word) = Some W_15614.
Proof. vm_refl. Qed.
Lemma D_15614 : decode_any W_15614 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15618 : bv 32 := 0x00300593.
Lemma F_15618 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156c4 : word) = Some W_15618.
Proof. vm_refl. Qed.
Lemma D_15618 : decode_any W_15618 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1561c : bv 32 := 0x00810613.
Lemma F_1561c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156c8 : word) = Some W_1561c.
Proof. vm_refl. Qed.
Lemma D_1561c : decode_any W_1561c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15620 : bv 32 := 0x00800713.
Lemma F_15620 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156cc : word) = Some W_15620.
Proof. vm_refl. Qed.
Lemma D_15620 : decode_any W_15620 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15624 : bv 32 := 0x00013c23.
Lemma F_15624 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156d0 : word) = Some W_15624.
Proof. vm_refl. Qed.
Lemma D_15624 : decode_any W_15624 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15628 : bv 32 := 0x02f13023.
Lemma F_15628 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156d4 : word) = Some W_15628.
Proof. vm_refl. Qed.
Lemma D_15628 : decode_any W_15628 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1562c : bv 32 := 0x02d13423.
Lemma F_1562c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156d8 : word) = Some W_1562c.
Proof. vm_refl. Qed.
Lemma D_1562c : decode_any W_1562c = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15630 : bv 32 := 0x00000693.
Lemma F_15630 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156dc : word) = Some W_15630.
Proof. vm_refl. Qed.
Lemma D_15630 : decode_any W_15630 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15634 : bv 32 := 0x00000073.
Lemma F_15634 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156e0 : word) = Some W_15634.
Proof. vm_refl. Qed.
Lemma D_15634 : decode_any W_15634 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_15634 : is_ecall W_15634 = true.
Proof. reflexivity. Qed.

Definition W_15638 : bv 32 := 0x02051513.
Lemma F_15638 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156e4 : word) = Some W_15638.
Proof. vm_refl. Qed.
Lemma D_15638 : decode_any W_15638 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1563c : bv 32 := 0x00055463.
Lemma F_1563c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156e8 : word) = Some W_1563c.
Proof. vm_refl. Qed.
Lemma D_1563c : decode_any W_1563c = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15640 : bv 32 := 0x00000023.
Lemma F_15640 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156ec : word) = Some W_15640.
Proof. vm_refl. Qed.
Lemma D_15640 : decode_any W_15640 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15644 : bv 32 := 0x01e15503.
Lemma F_15644 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156f0 : word) = Some W_15644.
Proof. vm_refl. Qed.
Lemma D_15644 : decode_any W_15644 = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_15648 : bv 32 := 0x02057513.
Lemma F_15648 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156f4 : word) = Some W_15648.
Proof. vm_refl. Qed.
Lemma D_15648 : decode_any W_15648 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1564c : bv 32 := 0x02050463.
Lemma F_1564c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156f8 : word) = Some W_1564c.
Proof. vm_refl. Qed.
Lemma D_1564c : decode_any W_1564c = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15650 : bv 32 := 0xffffb517.
Lemma F_15650 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x156fc : word) = Some W_15650.
Proof. vm_refl. Qed.
Lemma D_15650 : decode_any W_15650 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

Definition W_15654 : bv 32 := 0x00008637.
Lemma F_15654 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15700 : word) = Some W_15654.
Proof. vm_refl. Qed.
Lemma D_15654 : decode_any W_15654 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15658 : bv 32 := 0x03800893.
Lemma F_15658 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15704 : word) = Some W_15658.
Proof. vm_refl. Qed.
Lemma D_15658 : decode_any W_15658 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1565c : bv 32 := 0xe4550593.
Lemma F_1565c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15708 : word) = Some W_1565c.
Proof. vm_refl. Qed.
Lemma D_1565c : decode_any W_1565c = Some (OpImm ALU_ADD 11 10 3653, 4%Z).
Proof. vm_refl. Qed.

Definition W_15660 : bv 32 := 0x0026061b.
Lemma F_15660 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1570c : word) = Some W_15660.
Proof. vm_refl. Qed.
Lemma D_15660 : decode_any W_15660 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_15664 : bv 32 := 0xf9c00513.
Lemma F_15664 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15710 : word) = Some W_15664.
Proof. vm_refl. Qed.
Lemma D_15664 : decode_any W_15664 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_15668 : bv 32 := 0x00000073.
Lemma F_15668 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15714 : word) = Some W_15668.
Proof. vm_refl. Qed.
Lemma D_15668 : decode_any W_15668 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_15668 : is_ecall W_15668 = true.
Proof. reflexivity. Qed.

Definition W_1566c : bv 32 := 0x00055463.
Lemma F_1566c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15718 : word) = Some W_1566c.
Proof. vm_refl. Qed.
Lemma D_1566c : decode_any W_1566c = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15670 : bv 32 := 0x00000023.
Lemma F_15670 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1571c : word) = Some W_15670.
Proof. vm_refl. Qed.
Lemma D_15670 : decode_any W_15670 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15674 : bv 32 := 0x02615503.
Lemma F_15674 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15720 : word) = Some W_15674.
Proof. vm_refl. Qed.
Lemma D_15674 : decode_any W_15674 = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

Definition W_15678 : bv 32 := 0x02057513.
Lemma F_15678 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15724 : word) = Some W_15678.
Proof. vm_refl. Qed.
Lemma D_15678 : decode_any W_15678 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1567c : bv 32 := 0x02050463.
Lemma F_1567c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15728 : word) = Some W_1567c.
Proof. vm_refl. Qed.
Lemma D_1567c : decode_any W_1567c = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15680 : bv 32 := 0xffffb517.
Lemma F_15680 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1572c : word) = Some W_15680.
Proof. vm_refl. Qed.
Lemma D_15680 : decode_any W_15680 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

Definition W_15684 : bv 32 := 0x00008637.
Lemma F_15684 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15730 : word) = Some W_15684.
Proof. vm_refl. Qed.
Lemma D_15684 : decode_any W_15684 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15688 : bv 32 := 0x03800893.
Lemma F_15688 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15734 : word) = Some W_15688.
Proof. vm_refl. Qed.
Lemma D_15688 : decode_any W_15688 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1568c : bv 32 := 0xe1550593.
Lemma F_1568c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15738 : word) = Some W_1568c.
Proof. vm_refl. Qed.
Lemma D_1568c : decode_any W_1568c = Some (OpImm ALU_ADD 11 10 3605, 4%Z).
Proof. vm_refl. Qed.

Definition W_15690 : bv 32 := 0x0026061b.
Lemma F_15690 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1573c : word) = Some W_15690.
Proof. vm_refl. Qed.
Lemma D_15690 : decode_any W_15690 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_15694 : bv 32 := 0xf9c00513.
Lemma F_15694 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15740 : word) = Some W_15694.
Proof. vm_refl. Qed.
Lemma D_15694 : decode_any W_15694 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_15698 : bv 32 := 0x00000073.
Lemma F_15698 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15744 : word) = Some W_15698.
Proof. vm_refl. Qed.
Lemma D_15698 : decode_any W_15698 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_15698 : is_ecall W_15698 = true.
Proof. reflexivity. Qed.

Definition W_1569c : bv 32 := 0x00055463.
Lemma F_1569c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15748 : word) = Some W_1569c.
Proof. vm_refl. Qed.
Lemma D_1569c : decode_any W_1569c = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_156a0 : bv 32 := 0x00000023.
Lemma F_156a0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1574c : word) = Some W_156a0.
Proof. vm_refl. Qed.
Lemma D_156a0 : decode_any W_156a0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_156a4 : bv 32 := 0x02e15503.
Lemma F_156a4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15750 : word) = Some W_156a4.
Proof. vm_refl. Qed.
Lemma D_156a4 : decode_any W_156a4 = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

Definition W_156a8 : bv 32 := 0x02057513.
Lemma F_156a8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15754 : word) = Some W_156a8.
Proof. vm_refl. Qed.
Lemma D_156a8 : decode_any W_156a8 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_156ac : bv 32 := 0x02050463.
Lemma F_156ac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15758 : word) = Some W_156ac.
Proof. vm_refl. Qed.
Lemma D_156ac : decode_any W_156ac = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_156b0 : bv 32 := 0xffffb517.
Lemma F_156b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1575c : word) = Some W_156b0.
Proof. vm_refl. Qed.
Lemma D_156b0 : decode_any W_156b0 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

Definition W_156b4 : bv 32 := 0x00008637.
Lemma F_156b4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15760 : word) = Some W_156b4.
Proof. vm_refl. Qed.
Lemma D_156b4 : decode_any W_156b4 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_156b8 : bv 32 := 0x03800893.
Lemma F_156b8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15764 : word) = Some W_156b8.
Proof. vm_refl. Qed.
Lemma D_156b8 : decode_any W_156b8 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_156bc : bv 32 := 0xde550593.
Lemma F_156bc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15768 : word) = Some W_156bc.
Proof. vm_refl. Qed.
Lemma D_156bc : decode_any W_156bc = Some (OpImm ALU_ADD 11 10 3557, 4%Z).
Proof. vm_refl. Qed.

Definition W_156c0 : bv 32 := 0x0026061b.
Lemma F_156c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1576c : word) = Some W_156c0.
Proof. vm_refl. Qed.
Lemma D_156c0 : decode_any W_156c0 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_156c4 : bv 32 := 0xf9c00513.
Lemma F_156c4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15770 : word) = Some W_156c4.
Proof. vm_refl. Qed.
Lemma D_156c4 : decode_any W_156c4 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_156c8 : bv 32 := 0x00000073.
Lemma F_156c8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15774 : word) = Some W_156c8.
Proof. vm_refl. Qed.
Lemma D_156c8 : decode_any W_156c8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_156c8 : is_ecall W_156c8 = true.
Proof. reflexivity. Qed.

Definition W_156cc : bv 32 := 0x00055463.
Lemma F_156cc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15778 : word) = Some W_156cc.
Proof. vm_refl. Qed.
Lemma D_156cc : decode_any W_156cc = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_156d0 : bv 32 := 0x00000023.
Lemma F_156d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1577c : word) = Some W_156d0.
Proof. vm_refl. Qed.
Lemma D_156d0 : decode_any W_156d0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_156d4 : bv 32 := 0x00100513.
Lemma F_156d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15780 : word) = Some W_156d4.
Proof. vm_refl. Qed.
Lemma D_156d4 : decode_any W_156d4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_156d8 : bv 32 := 0x00a90123.
Lemma F_156d8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15784 : word) = Some W_156d8.
Proof. vm_refl. Qed.
Lemma D_156d8 : decode_any W_156d8 = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_156dc : bv 32 := 0x17813083.
Lemma F_156dc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15788 : word) = Some W_156dc.
Proof. vm_refl. Qed.
Lemma D_156dc : decode_any W_156dc = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_156e0 : bv 32 := 0x17013403.
Lemma F_156e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1578c : word) = Some W_156e0.
Proof. vm_refl. Qed.
Lemma D_156e0 : decode_any W_156e0 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_156e4 : bv 32 := 0x16813483.
Lemma F_156e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15790 : word) = Some W_156e4.
Proof. vm_refl. Qed.
Lemma D_156e4 : decode_any W_156e4 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_156e8 : bv 32 := 0x16013903.
Lemma F_156e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15794 : word) = Some W_156e8.
Proof. vm_refl. Qed.
Lemma D_156e8 : decode_any W_156e8 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_156ec : bv 32 := 0x18010113.
Lemma F_156ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15798 : word) = Some W_156ec.
Proof. vm_refl. Qed.
Lemma D_156ec : decode_any W_156ec = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_156f0 : bv 32 := 0x00008067.
Lemma F_156f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1579c : word) = Some W_156f0.
Proof. vm_refl. Qed.
Lemma D_156f0 : decode_any W_156f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_156f4 : bv 32 := 0xfe010113.
Lemma F_156f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157a0 : word) = Some W_156f4.
Proof. vm_refl. Qed.
Lemma D_156f4 : decode_any W_156f4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_156f8 : bv 32 := 0x00113c23.
Lemma F_156f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157a4 : word) = Some W_156f8.
Proof. vm_refl. Qed.
Lemma D_156f8 : decode_any W_156f8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_156fc : bv 32 := 0x00813823.
Lemma F_156fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157a8 : word) = Some W_156fc.
Proof. vm_refl. Qed.
Lemma D_156fc : decode_any W_156fc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15700 : bv 32 := 0x00913423.
Lemma F_15700 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157ac : word) = Some W_15700.
Proof. vm_refl. Qed.
Lemma D_15700 : decode_any W_15700 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15704 : bv 32 := 0xdc1ff0ef.
Lemma F_15704 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157b0 : word) = Some W_15704.
Proof. vm_refl. Qed.
Lemma D_15704 : decode_any W_15704 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_15708 : bv 32 := 0x00009517.
Lemma F_15708 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157b4 : word) = Some W_15708.
Proof. vm_refl. Qed.
Lemma D_15708 : decode_any W_15708 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1570c : bv 32 := 0x00009597.
Lemma F_1570c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157b8 : word) = Some W_1570c.
Proof. vm_refl. Qed.
Lemma D_1570c : decode_any W_1570c = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15710 : bv 32 := 0x24453403.
Lemma F_15710 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157bc : word) = Some W_15710.
Proof. vm_refl. Qed.
Lemma D_15710 : decode_any W_15710 = Some (Load SZ8 true 8 10 580, 4%Z).
Proof. vm_refl. Qed.

Definition W_15714 : bv 32 := 0x2485b483.
Lemma F_15714 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157c0 : word) = Some W_15714.
Proof. vm_refl. Qed.
Lemma D_15714 : decode_any W_15714 = Some (Load SZ8 true 9 11 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_15718 : bv 32 := 0x0084fa63.
Lemma F_15718 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157c4 : word) = Some W_15718.
Proof. vm_refl. Qed.
Lemma D_15718 : decode_any W_15718 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1571c : bv 32 := 0x0004b503.
Lemma F_1571c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157c8 : word) = Some W_1571c.
Proof. vm_refl. Qed.
Lemma D_1571c : decode_any W_1571c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15720 : bv 32 := 0x000500e7.
Lemma F_15720 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157cc : word) = Some W_15720.
Proof. vm_refl. Qed.
Lemma D_15720 : decode_any W_15720 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15724 : bv 32 := 0x00848493.
Lemma F_15724 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157d0 : word) = Some W_15724.
Proof. vm_refl. Qed.
Lemma D_15724 : decode_any W_15724 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15728 : bv 32 := 0xfe84eae3.
Lemma F_15728 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157d4 : word) = Some W_15728.
Proof. vm_refl. Qed.
Lemma D_15728 : decode_any W_15728 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1572c : bv 32 := 0x01813083.
Lemma F_1572c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157d8 : word) = Some W_1572c.
Proof. vm_refl. Qed.
Lemma D_1572c : decode_any W_1572c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15730 : bv 32 := 0x01013403.
Lemma F_15730 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157dc : word) = Some W_15730.
Proof. vm_refl. Qed.
Lemma D_15730 : decode_any W_15730 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15734 : bv 32 := 0x00813483.
Lemma F_15734 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157e0 : word) = Some W_15734.
Proof. vm_refl. Qed.
Lemma D_15734 : decode_any W_15734 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15738 : bv 32 := 0x02010113.
Lemma F_15738 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157e4 : word) = Some W_15738.
Proof. vm_refl. Qed.
Lemma D_15738 : decode_any W_15738 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1573c : bv 32 := 0x00008067.
Lemma F_1573c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157e8 : word) = Some W_1573c.
Proof. vm_refl. Qed.
Lemma D_1573c : decode_any W_1573c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15740 : bv 32 := 0xfe010113.
Lemma F_15740 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157ec : word) = Some W_15740.
Proof. vm_refl. Qed.
Lemma D_15740 : decode_any W_15740 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_15744 : bv 32 := 0x00113c23.
Lemma F_15744 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157f0 : word) = Some W_15744.
Proof. vm_refl. Qed.
Lemma D_15744 : decode_any W_15744 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15748 : bv 32 := 0x00813823.
Lemma F_15748 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157f4 : word) = Some W_15748.
Proof. vm_refl. Qed.
Lemma D_15748 : decode_any W_15748 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1574c : bv 32 := 0x00913423.
Lemma F_1574c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157f8 : word) = Some W_1574c.
Proof. vm_refl. Qed.
Lemma D_1574c : decode_any W_1574c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15750 : bv 32 := 0x01213023.
Lemma F_15750 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x157fc : word) = Some W_15750.
Proof. vm_refl. Qed.
Lemma D_15750 : decode_any W_15750 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15754 : bv 32 := 0x00060413.
Lemma F_15754 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15800 : word) = Some W_15754.
Proof. vm_refl. Qed.
Lemma D_15754 : decode_any W_15754 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15758 : bv 32 := 0x00058493.
Lemma F_15758 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15804 : word) = Some W_15758.
Proof. vm_refl. Qed.
Lemma D_15758 : decode_any W_15758 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1575c : bv 32 := 0x00050913.
Lemma F_1575c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15808 : word) = Some W_1575c.
Proof. vm_refl. Qed.
Lemma D_1575c : decode_any W_1575c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15760 : bv 32 := 0x00063583.
Lemma F_15760 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1580c : word) = Some W_15760.
Proof. vm_refl. Qed.
Lemma D_15760 : decode_any W_15760 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15764 : bv 32 := 0x00349513.
Lemma F_15764 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15810 : word) = Some W_15764.
Proof. vm_refl. Qed.
Lemma D_15764 : decode_any W_15764 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_15768 : bv 32 := 0x00a60533.
Lemma F_15768 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15814 : word) = Some W_15768.
Proof. vm_refl. Qed.
Lemma D_15768 : decode_any W_15768 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1576c : bv 32 := 0x00850513.
Lemma F_1576c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15818 : word) = Some W_1576c.
Proof. vm_refl. Qed.
Lemma D_1576c : decode_any W_1576c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15770 : bv 32 := 0xd59ff0ef.
Lemma F_15770 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1581c : word) = Some W_15770.
Proof. vm_refl. Qed.
Lemma D_15770 : decode_any W_15770 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_15774 : bv 32 := 0x00000517.
Lemma F_15774 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15820 : word) = Some W_15774.
Proof. vm_refl. Qed.
Lemma D_15774 : decode_any W_15774 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15778 : bv 32 := 0x02c50313.
Lemma F_15778 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15824 : word) = Some W_15778.
Proof. vm_refl. Qed.
Lemma D_15778 : decode_any W_15778 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1577c : bv 32 := 0x00090513.
Lemma F_1577c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15828 : word) = Some W_1577c.
Proof. vm_refl. Qed.
Lemma D_1577c : decode_any W_1577c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15780 : bv 32 := 0x00048593.
Lemma F_15780 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1582c : word) = Some W_15780.
Proof. vm_refl. Qed.
Lemma D_15780 : decode_any W_15780 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15784 : bv 32 := 0x00040613.
Lemma F_15784 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15830 : word) = Some W_15784.
Proof. vm_refl. Qed.
Lemma D_15784 : decode_any W_15784 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15788 : bv 32 := 0x01813083.
Lemma F_15788 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15834 : word) = Some W_15788.
Proof. vm_refl. Qed.
Lemma D_15788 : decode_any W_15788 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1578c : bv 32 := 0x01013403.
Lemma F_1578c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15838 : word) = Some W_1578c.
Proof. vm_refl. Qed.
Lemma D_1578c : decode_any W_1578c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15790 : bv 32 := 0x00813483.
Lemma F_15790 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1583c : word) = Some W_15790.
Proof. vm_refl. Qed.
Lemma D_15790 : decode_any W_15790 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15794 : bv 32 := 0x00013903.
Lemma F_15794 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15840 : word) = Some W_15794.
Proof. vm_refl. Qed.
Lemma D_15794 : decode_any W_15794 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15798 : bv 32 := 0x02010113.
Lemma F_15798 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15844 : word) = Some W_15798.
Proof. vm_refl. Qed.
Lemma D_15798 : decode_any W_15798 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1579c : bv 32 := 0x00030067.
Lemma F_1579c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15848 : word) = Some W_1579c.
Proof. vm_refl. Qed.
Lemma D_1579c : decode_any W_1579c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157a0 : bv 32 := 0xfd010113.
Lemma F_157a0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1584c : word) = Some W_157a0.
Proof. vm_refl. Qed.
Lemma D_157a0 : decode_any W_157a0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_157a4 : bv 32 := 0x02113423.
Lemma F_157a4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15850 : word) = Some W_157a4.
Proof. vm_refl. Qed.
Lemma D_157a4 : decode_any W_157a4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_157a8 : bv 32 := 0x02813023.
Lemma F_157a8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15854 : word) = Some W_157a8.
Proof. vm_refl. Qed.
Lemma D_157a8 : decode_any W_157a8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_157ac : bv 32 := 0x00913c23.
Lemma F_157ac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15858 : word) = Some W_157ac.
Proof. vm_refl. Qed.
Lemma D_157ac : decode_any W_157ac = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_157b0 : bv 32 := 0x01213823.
Lemma F_157b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1585c : word) = Some W_157b0.
Proof. vm_refl. Qed.
Lemma D_157b0 : decode_any W_157b0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_157b4 : bv 32 := 0x01313423.
Lemma F_157b4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15860 : word) = Some W_157b4.
Proof. vm_refl. Qed.
Lemma D_157b4 : decode_any W_157b4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_157b8 : bv 32 := 0x00060413.
Lemma F_157b8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15864 : word) = Some W_157b8.
Proof. vm_refl. Qed.
Lemma D_157b8 : decode_any W_157b8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157bc : bv 32 := 0x00058493.
Lemma F_157bc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15868 : word) = Some W_157bc.
Proof. vm_refl. Qed.
Lemma D_157bc : decode_any W_157bc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157c0 : bv 32 := 0x00050913.
Lemma F_157c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1586c : word) = Some W_157c0.
Proof. vm_refl. Qed.
Lemma D_157c0 : decode_any W_157c0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157c4 : bv 32 := 0x00359513.
Lemma F_157c4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15870 : word) = Some W_157c4.
Proof. vm_refl. Qed.
Lemma D_157c4 : decode_any W_157c4 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_157c8 : bv 32 := 0x00a60533.
Lemma F_157c8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15874 : word) = Some W_157c8.
Proof. vm_refl. Qed.
Lemma D_157c8 : decode_any W_157c8 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_157cc : bv 32 := 0x00850993.
Lemma F_157cc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15878 : word) = Some W_157cc.
Proof. vm_refl. Qed.
Lemma D_157cc : decode_any W_157cc = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_157d0 : bv 32 := 0xf25ff0ef.
Lemma F_157d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1587c : word) = Some W_157d0.
Proof. vm_refl. Qed.
Lemma D_157d0 : decode_any W_157d0 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_157d4 : bv 32 := 0x00048513.
Lemma F_157d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15880 : word) = Some W_157d4.
Proof. vm_refl. Qed.
Lemma D_157d4 : decode_any W_157d4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157d8 : bv 32 := 0x00040593.
Lemma F_157d8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15884 : word) = Some W_157d8.
Proof. vm_refl. Qed.
Lemma D_157d8 : decode_any W_157d8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157dc : bv 32 := 0x00098613.
Lemma F_157dc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15888 : word) = Some W_157dc.
Proof. vm_refl. Qed.
Lemma D_157dc : decode_any W_157dc = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157e0 : bv 32 := 0x000900e7.
Lemma F_157e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1588c : word) = Some W_157e0.
Proof. vm_refl. Qed.
Lemma D_157e0 : decode_any W_157e0 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_157e4 : bv 32 := 0x578000ef.
Lemma F_157e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15890 : word) = Some W_157e4.
Proof. vm_refl. Qed.
Lemma D_157e4 : decode_any W_157e4 = Some (Jal 1 1400, 4%Z).
Proof. vm_refl. Qed.

Definition W_157e8 : bv 32 := 0xfc010113.
Lemma F_157e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15894 : word) = Some W_157e8.
Proof. vm_refl. Qed.
Lemma D_157e8 : decode_any W_157e8 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15898 : bv 32 := 0x02113c23.
Lemma TF_15898 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15898 : word) = Some TW_15898.
Proof. vm_refl. Qed.
Lemma TD_15898 : decode_any TW_15898 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1589c : bv 32 := 0x02813823.
Lemma TF_1589c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1589c : word) = Some TW_1589c.
Proof. vm_refl. Qed.
Lemma TD_1589c : decode_any TW_1589c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158a0 : bv 32 := 0x02913423.
Lemma TF_158a0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158a0 : word) = Some TW_158a0.
Proof. vm_refl. Qed.
Lemma TD_158a0 : decode_any TW_158a0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158a4 : bv 32 := 0x03213023.
Lemma TF_158a4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158a4 : word) = Some TW_158a4.
Proof. vm_refl. Qed.
Lemma TD_158a4 : decode_any TW_158a4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158a8 : bv 32 := 0x01313c23.
Lemma TF_158a8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158a8 : word) = Some TW_158a8.
Proof. vm_refl. Qed.
Lemma TD_158a8 : decode_any TW_158a8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158ac : bv 32 := 0x01413823.
Lemma TF_158ac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158ac : word) = Some TW_158ac.
Proof. vm_refl. Qed.
Lemma TD_158ac : decode_any TW_158ac = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158b0 : bv 32 := 0x01513423.
Lemma TF_158b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158b0 : word) = Some TW_158b0.
Proof. vm_refl. Qed.
Lemma TD_158b0 : decode_any TW_158b0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158b4 : bv 32 := 0x02853683.
Lemma TF_158b4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158b4 : word) = Some TW_158b4.
Proof. vm_refl. Qed.
Lemma TD_158b4 : decode_any TW_158b4 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158b8 : bv 32 := 0x0003a597.
Lemma TF_158b8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158b8 : word) = Some TW_158b8.
Proof. vm_refl. Qed.
Lemma TD_158b8 : decode_any TW_158b8 = Some (Auipc 11 58, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158bc : bv 32 := 0x4d058593.
Lemma TF_158bc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158bc : word) = Some TW_158bc.
Proof. vm_refl. Qed.
Lemma TD_158bc : decode_any TW_158bc = Some (OpImm ALU_ADD 11 11 1232, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158c0 : bv 32 := 0x0003a617.
Lemma TF_158c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158c0 : word) = Some TW_158c0.
Proof. vm_refl. Qed.
Lemma TD_158c0 : decode_any TW_158c0 = Some (Auipc 12 58, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158c4 : bv 32 := 0x75060493.
Lemma TF_158c4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158c4 : word) = Some TW_158c4.
Proof. vm_refl. Qed.
Lemma TD_158c4 : decode_any TW_158c4 = Some (OpImm ALU_ADD 9 12 1872, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158c8 : bv 32 := 0x0c068e63.
Lemma TF_158c8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158c8 : word) = Some TW_158c8.
Proof. vm_refl. Qed.
Lemma TD_158c8 : decode_any TW_158c8 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158cc : bv 32 := 0x00000613.
Lemma TF_158cc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158cc : word) = Some TW_158cc.
Proof. vm_refl. Qed.
Lemma TD_158cc : decode_any TW_158cc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158d0 : bv 32 := 0x00000893.
Lemma TF_158d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158d0 : word) = Some TW_158d0.
Proof. vm_refl. Qed.
Lemma TD_158d0 : decode_any TW_158d0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158d4 : bv 32 := 0x0000a717.
Lemma TF_158d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158d4 : word) = Some TW_158d4.
Proof. vm_refl. Qed.
Lemma TD_158d4 : decode_any TW_158d4 = Some (Auipc 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158d8 : bv 32 := 0x01853783.
Lemma TF_158d8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158d8 : word) = Some TW_158d8.
Proof. vm_refl. Qed.
Lemma TD_158d8 : decode_any TW_158d8 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158dc : bv 32 := 0x02053503.
Lemma TF_158dc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158dc : word) = Some TW_158dc.
Proof. vm_refl. Qed.
Lemma TD_158dc : decode_any TW_158dc = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158e0 : bv 32 := 0x00600813.
Lemma TF_158e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158e0 : word) = Some TW_158e0.
Proof. vm_refl. Qed.
Lemma TD_158e0 : decode_any TW_158e0 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158e4 : bv 32 := 0x00009297.
Lemma TF_158e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158e4 : word) = Some TW_158e4.
Proof. vm_refl. Qed.
Lemma TD_158e4 : decode_any TW_158e4 = Some (Auipc 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158e8 : bv 32 := 0x35476f03.
Lemma TF_158e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158e8 : word) = Some TW_158e8.
Proof. vm_refl. Qed.
Lemma TD_158e8 : decode_any TW_158e8 = Some (Load SZ4 false 30 14 852, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158ec : bv 32 := 0x0ac2b283.
Lemma TF_158ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158ec : word) = Some TW_158ec.
Proof. vm_refl. Qed.
Lemma TD_158ec : decode_any TW_158ec = Some (Load SZ8 true 5 5 172, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158f0 : bv 32 := 0x00200313.
Lemma TF_158f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158f0 : word) = Some TW_158f0.
Proof. vm_refl. Qed.
Lemma TD_158f0 : decode_any TW_158f0 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158f4 : bv 32 := 0x00700393.
Lemma TF_158f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158f4 : word) = Some TW_158f4.
Proof. vm_refl. Qed.
Lemma TD_158f4 : decode_any TW_158f4 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158f8 : bv 32 := 0x6474ee37.
Lemma TF_158f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158f8 : word) = Some TW_158f8.
Proof. vm_refl. Qed.
Lemma TD_158f8 : decode_any TW_158f8 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition TW_158fc : bv 32 := 0x551e0e1b.
Lemma TF_158fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x158fc : word) = Some TW_158fc.
Proof. vm_refl. Qed.
Lemma TD_158fc : decode_any TW_158fc = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15900 : bv 32 := 0x00078e93.
Lemma TF_15900 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15900 : word) = Some TW_15900.
Proof. vm_refl. Qed.
Lemma TD_15900 : decode_any TW_15900 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15904 : bv 32 := 0x0180006f.
Lemma TF_15904 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15904 : word) = Some TW_15904.
Proof. vm_refl. Qed.
Lemma TD_15904 : decode_any TW_15904 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15908 : bv 32 := 0x010eb603.
Lemma TF_15908 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15908 : word) = Some TW_15908.
Proof. vm_refl. Qed.
Lemma TD_15908 : decode_any TW_15908 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1590c : bv 32 := 0x40c78633.
Lemma TF_1590c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1590c : word) = Some TW_1590c.
Proof. vm_refl. Qed.
Lemma TD_1590c : decode_any TW_1590c = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15910 : bv 32 := 0xfff68693.
Lemma TF_15910 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15910 : word) = Some TW_15910.
Proof. vm_refl. Qed.
Lemma TD_15910 : decode_any TW_15910 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15914 : bv 32 := 0x00ae8eb3.
Lemma TF_15914 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15914 : word) = Some TW_15914.
Proof. vm_refl. Qed.
Lemma TD_15914 : decode_any TW_15914 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15918 : bv 32 := 0x04068a63.
Lemma TF_15918 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15918 : word) = Some TW_15918.
Proof. vm_refl. Qed.
Lemma TD_15918 : decode_any TW_15918 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1591c : bv 32 := 0x000ea403.
Lemma TF_1591c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1591c : word) = Some TW_1591c.
Proof. vm_refl. Qed.
Lemma TD_1591c : decode_any TW_1591c = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15920 : bv 32 := 0xff0404e3.
Lemma TF_15920 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15920 : word) = Some TW_15920.
Proof. vm_refl. Qed.
Lemma TD_15920 : decode_any TW_15920 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15924 : bv 32 := 0x00028a63.
Lemma TF_15924 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15924 : word) = Some TW_15924.
Proof. vm_refl. Qed.
Lemma TD_15924 : decode_any TW_15924 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15928 : bv 32 := 0x00641863.
Lemma TF_15928 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15928 : word) = Some TW_15928.
Proof. vm_refl. Qed.
Lemma TD_15928 : decode_any TW_15928 = Some (Branch BC_NE 8 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1592c : bv 32 := 0x010eb603.
Lemma TF_1592c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1592c : word) = Some TW_1592c.
Proof. vm_refl. Qed.
Lemma TD_1592c : decode_any TW_1592c = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15930 : bv 32 := 0x40c28633.
Lemma TF_15930 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15930 : word) = Some TW_15930.
Proof. vm_refl. Qed.
Lemma TD_15930 : decode_any TW_15930 = Some (Op ALU_SUB 12 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15934 : bv 32 := 0xfddff06f.
Lemma TF_15934 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15934 : word) = Some TW_15934.
Proof. vm_refl. Qed.
Lemma TD_15934 : decode_any TW_15934 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15938 : bv 32 := 0x000e8f93.
Lemma TF_15938 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15938 : word) = Some TW_15938.
Proof. vm_refl. Qed.
Lemma TD_15938 : decode_any TW_15938 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1593c : bv 32 := 0x00740463.
Lemma TF_1593c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1593c : word) = Some TW_1593c.
Proof. vm_refl. Qed.
Lemma TD_1593c : decode_any TW_1593c = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15940 : bv 32 := 0x00088f93.
Lemma TF_15940 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15940 : word) = Some TW_15940.
Proof. vm_refl. Qed.
Lemma TD_15940 : decode_any TW_15940 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15944 : bv 32 := 0x03c41063.
Lemma TF_15944 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15944 : word) = Some TW_15944.
Proof. vm_refl. Qed.
Lemma TD_15944 : decode_any TW_15944 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15948 : bv 32 := 0x028eb883.
Lemma TF_15948 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15948 : word) = Some TW_15948.
Proof. vm_refl. Qed.
Lemma TD_15948 : decode_any TW_15948 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1594c : bv 32 := 0x011f7c63.
Lemma TF_1594c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1594c : word) = Some TW_1594c.
Proof. vm_refl. Qed.
Lemma TD_1594c : decode_any TW_1594c = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15950 : bv 32 := 0x00800f37.
Lemma TF_15950 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15950 : word) = Some TW_15950.
Proof. vm_refl. Qed.
Lemma TD_15950 : decode_any TW_15950 = Some (Lui 30 2048, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15954 : bv 32 := 0x01e8e463.
Lemma TF_15954 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15954 : word) = Some TW_15954.
Proof. vm_refl. Qed.
Lemma TD_15954 : decode_any TW_15954 = Some (Branch BC_LTU 17 30 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15958 : bv 32 := 0x008008b7.
Lemma TF_15958 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15958 : word) = Some TW_15958.
Proof. vm_refl. Qed.
Lemma TD_15958 : decode_any TW_15958 = Some (Lui 17 2048, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1595c : bv 32 := 0x35172a23.
Lemma TF_1595c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1595c : word) = Some TW_1595c.
Proof. vm_refl. Qed.
Lemma TD_1595c : decode_any TW_1595c = Some (Store SZ4 14 17 852, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15960 : bv 32 := 0x00088f13.
Lemma TF_15960 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15960 : word) = Some TW_15960.
Proof. vm_refl. Qed.
Lemma TD_15960 : decode_any TW_15960 = Some (OpImm ALU_ADD 30 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15964 : bv 32 := 0x000f8893.
Lemma TF_15964 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15964 : word) = Some TW_15964.
Proof. vm_refl. Qed.
Lemma TD_15964 : decode_any TW_15964 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15968 : bv 32 := 0xfa9ff06f.
Lemma TF_15968 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15968 : word) = Some TW_15968.
Proof. vm_refl. Qed.
Lemma TD_15968 : decode_any TW_15968 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1596c : bv 32 := 0x02088c63.
Lemma TF_1596c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1596c : word) = Some TW_1596c.
Proof. vm_refl. Qed.
Lemma TD_1596c : decode_any TW_1596c = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15970 : bv 32 := 0x00858713.
Lemma TF_15970 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15970 : word) = Some TW_15970.
Proof. vm_refl. Qed.
Lemma TD_15970 : decode_any TW_15970 = Some (OpImm ALU_ADD 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15974 : bv 32 := 0x0108b783.
Lemma TF_15974 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15974 : word) = Some TW_15974.
Proof. vm_refl. Qed.
Lemma TD_15974 : decode_any TW_15974 = Some (Load SZ8 true 15 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15978 : bv 32 := 0x0208b803.
Lemma TF_15978 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15978 : word) = Some TW_15978.
Proof. vm_refl. Qed.
Lemma TD_15978 : decode_any TW_15978 = Some (Load SZ8 true 16 17 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1597c : bv 32 := 0x0288b683.
Lemma TF_1597c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1597c : word) = Some TW_1597c.
Proof. vm_refl. Qed.
Lemma TD_1597c : decode_any TW_1597c = Some (Load SZ8 true 13 17 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15980 : bv 32 := 0x0308b503.
Lemma TF_15980 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15980 : word) = Some TW_15980.
Proof. vm_refl. Qed.
Lemma TD_15980 : decode_any TW_15980 = Some (Load SZ8 true 10 17 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15984 : bv 32 := 0x00c78633.
Lemma TF_15984 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15984 : word) = Some TW_15984.
Proof. vm_refl. Qed.
Lemma TD_15984 : decode_any TW_15984 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15988 : bv 32 := 0x00100793.
Lemma TF_15988 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15988 : word) = Some TW_15988.
Proof. vm_refl. Qed.
Lemma TD_15988 : decode_any TW_15988 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1598c : bv 32 := 0x00c5b823.
Lemma TF_1598c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1598c : word) = Some TW_1598c.
Proof. vm_refl. Qed.
Lemma TD_1598c : decode_any TW_1598c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15990 : bv 32 := 0x0105bc23.
Lemma TF_15990 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15990 : word) = Some TW_15990.
Proof. vm_refl. Qed.
Lemma TD_15990 : decode_any TW_15990 = Some (Store SZ8 11 16 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15994 : bv 32 := 0x02a5b423.
Lemma TF_15994 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15994 : word) = Some TW_15994.
Proof. vm_refl. Qed.
Lemma TD_15994 : decode_any TW_15994 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15998 : bv 32 := 0x00e4b823.
Lemma TF_15998 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15998 : word) = Some TW_15998.
Proof. vm_refl. Qed.
Lemma TD_15998 : decode_any TW_15998 = Some (Store SZ8 9 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1599c : bv 32 := 0x02f4b423.
Lemma TF_1599c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1599c : word) = Some TW_1599c.
Proof. vm_refl. Qed.
Lemma TD_1599c : decode_any TW_1599c = Some (Store SZ8 9 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159a0 : bv 32 := 0x0100006f.
Lemma TF_159a0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159a0 : word) = Some TW_159a0.
Proof. vm_refl. Qed.
Lemma TD_159a0 : decode_any TW_159a0 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159a4 : bv 32 := 0x0105b603.
Lemma TF_159a4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159a4 : word) = Some TW_159a4.
Proof. vm_refl. Qed.
Lemma TD_159a4 : decode_any TW_159a4 = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159a8 : bv 32 := 0x0205b683.
Lemma TF_159a8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159a8 : word) = Some TW_159a8.
Proof. vm_refl. Qed.
Lemma TD_159a8 : decode_any TW_159a8 = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159ac : bv 32 := 0x0285b503.
Lemma TF_159ac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159ac : word) = Some TW_159ac.
Proof. vm_refl. Qed.
Lemma TD_159ac : decode_any TW_159ac = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159b0 : bv 32 := 0x00c68733.
Lemma TF_159b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159b0 : word) = Some TW_159b0.
Proof. vm_refl. Qed.
Lemma TD_159b0 : decode_any TW_159b0 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159b4 : bv 32 := 0xfff50793.
Lemma TF_159b4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159b4 : word) = Some TW_159b4.
Proof. vm_refl. Qed.
Lemma TD_159b4 : decode_any TW_159b4 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159b8 : bv 32 := 0x40e00733.
Lemma TF_159b8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159b8 : word) = Some TW_159b8.
Proof. vm_refl. Qed.
Lemma TD_159b8 : decode_any TW_159b8 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159bc : bv 32 := 0x00c7f633.
Lemma TF_159bc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159bc : word) = Some TW_159bc.
Proof. vm_refl. Qed.
Lemma TD_159bc : decode_any TW_159bc = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159c0 : bv 32 := 0x00e7f733.
Lemma TF_159c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159c0 : word) = Some TW_159c0.
Proof. vm_refl. Qed.
Lemma TD_159c0 : decode_any TW_159c0 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159c4 : bv 32 := 0x00700793.
Lemma TF_159c4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159c4 : word) = Some TW_159c4.
Proof. vm_refl. Qed.
Lemma TD_159c4 : decode_any TW_159c4 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159c8 : bv 32 := 0x00d706b3.
Lemma TF_159c8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159c8 : word) = Some TW_159c8.
Proof. vm_refl. Qed.
Lemma TD_159c8 : decode_any TW_159c8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159cc : bv 32 := 0x02d5b023.
Lemma TF_159cc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159cc : word) = Some TW_159cc.
Proof. vm_refl. Qed.
Lemma TD_159cc : decode_any TW_159cc = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159d0 : bv 32 := 0x02c5b823.
Lemma TF_159d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159d0 : word) = Some TW_159d0.
Proof. vm_refl. Qed.
Lemma TD_159d0 : decode_any TW_159d0 = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159d4 : bv 32 := 0x00a7e663.
Lemma TF_159d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159d4 : word) = Some TW_159d4.
Proof. vm_refl. Qed.
Lemma TD_159d4 : decode_any TW_159d4 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159d8 : bv 32 := 0x00800513.
Lemma TF_159d8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159d8 : word) = Some TW_159d8.
Proof. vm_refl. Qed.
Lemma TD_159d8 : decode_any TW_159d8 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159dc : bv 32 := 0x02a5b423.
Lemma TF_159dc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159dc : word) = Some TW_159dc.
Proof. vm_refl. Qed.
Lemma TD_159dc : decode_any TW_159dc = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159e0 : bv 32 := 0x00d60633.
Lemma TF_159e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159e0 : word) = Some TW_159e0.
Proof. vm_refl. Qed.
Lemma TD_159e0 : decode_any TW_159e0 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159e4 : bv 32 := 0x000205b7.
Lemma TF_159e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159e4 : word) = Some TW_159e4.
Proof. vm_refl. Qed.
Lemma TD_159e4 : decode_any TW_159e4 = Some (Lui 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159e8 : bv 32 := 0x00a60633.
Lemma TF_159e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159e8 : word) = Some TW_159e8.
Proof. vm_refl. Qed.
Lemma TD_159e8 : decode_any TW_159e8 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159ec : bv 32 := 0x0d15869b.
Lemma TF_159ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159ec : word) = Some TW_159ec.
Proof. vm_refl. Qed.
Lemma TD_159ec : decode_any TW_159ec = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159f0 : bv 32 := 0x0df60593.
Lemma TF_159f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159f0 : word) = Some TW_159f0.
Proof. vm_refl. Qed.
Lemma TD_159f0 : decode_any TW_159f0 = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159f4 : bv 32 := 0xff85f593.
Lemma TF_159f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159f4 : word) = Some TW_159f4.
Proof. vm_refl. Qed.
Lemma TD_159f4 : decode_any TW_159f4 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159f8 : bv 32 := 0x00b4bc23.
Lemma TF_159f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159f8 : word) = Some TW_159f8.
Proof. vm_refl. Qed.
Lemma TD_159f8 : decode_any TW_159f8 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_159fc : bv 32 := 0x02a4b023.
Lemma TF_159fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x159fc : word) = Some TW_159fc.
Proof. vm_refl. Qed.
Lemma TD_159fc : decode_any TW_159fc = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a00 : bv 32 := 0x02d5ea63.
Lemma TF_15a00 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a00 : word) = Some TW_15a00.
Proof. vm_refl. Qed.
Lemma TD_15a00 : decode_any TW_15a00 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a04 : bv 32 := 0xffffc597.
Lemma TF_15a04 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a04 : word) = Some TW_15a04.
Proof. vm_refl. Qed.
Lemma TD_15a04 : decode_any TW_15a04 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a08 : bv 32 := 0x04000893.
Lemma TF_15a08 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a08 : word) = Some TW_15a08.
Proof. vm_refl. Qed.
Lemma TD_15a08 : decode_any TW_15a08 = Some (OpImm ALU_ADD 17 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a0c : bv 32 := 0x00200513.
Lemma TF_15a0c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a0c : word) = Some TW_15a0c.
Proof. vm_refl. Qed.
Lemma TD_15a0c : decode_any TW_15a0c = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a10 : bv 32 := 0x02c58593.
Lemma TF_15a10 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a10 : word) = Some TW_15a10.
Proof. vm_refl. Qed.
Lemma TD_15a10 : decode_any TW_15a10 = Some (OpImm ALU_ADD 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a14 : bv 32 := 0x05b00613.
Lemma TF_15a14 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a14 : word) = Some TW_15a14.
Proof. vm_refl. Qed.
Lemma TD_15a14 : decode_any TW_15a14 = Some (OpImm ALU_ADD 12 0 91, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a18 : bv 32 := 0x00000073.
Lemma TF_15a18 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a18 : word) = Some TW_15a18.
Proof. vm_refl. Qed.
Lemma TD_15a18 : decode_any TW_15a18 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_15a18 : is_ecall TW_15a18 = true.
Proof. reflexivity. Qed.

Definition TW_15a1c : bv 32 := 0x00000023.
Lemma TF_15a1c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a1c : word) = Some TW_15a1c.
Proof. vm_refl. Qed.
Lemma TD_15a1c : decode_any TW_15a1c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a20 : bv 32 := 0x05e00893.
Lemma TF_15a20 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a20 : word) = Some TW_15a20.
Proof. vm_refl. Qed.
Lemma TD_15a20 : decode_any TW_15a20 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a24 : bv 32 := 0x07f00513.
Lemma TF_15a24 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a24 : word) = Some TW_15a24.
Proof. vm_refl. Qed.
Lemma TD_15a24 : decode_any TW_15a24 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a28 : bv 32 := 0x00000073.
Lemma TF_15a28 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a28 : word) = Some TW_15a28.
Proof. vm_refl. Qed.
Lemma TD_15a28 : decode_any TW_15a28 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_15a28 : is_ecall TW_15a28 = true.
Proof. reflexivity. Qed.

Definition TW_15a2c : bv 32 := 0x0184b583.
Lemma TF_15a2c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a2c : word) = Some TW_15a2c.
Proof. vm_refl. Qed.
Lemma TD_15a2c : decode_any TW_15a2c = Some (Load SZ8 true 11 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a30 : bv 32 := 0x0204b503.
Lemma TF_15a30 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a30 : word) = Some TW_15a30.
Proof. vm_refl. Qed.
Lemma TD_15a30 : decode_any TW_15a30 = Some (Load SZ8 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a34 : bv 32 := 0x0001a697.
Lemma TF_15a34 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a34 : word) = Some TW_15a34.
Proof. vm_refl. Qed.
Lemma TD_15a34 : decode_any TW_15a34 = Some (Auipc 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a38 : bv 32 := 0x0104b983.
Lemma TF_15a38 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a38 : word) = Some TW_15a38.
Proof. vm_refl. Qed.
Lemma TD_15a38 : decode_any TW_15a38 = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a3c : bv 32 := 0x0284b603.
Lemma TF_15a3c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a3c : word) = Some TW_15a3c.
Proof. vm_refl. Qed.
Lemma TD_15a3c : decode_any TW_15a3c = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a40 : bv 32 := 0xfff50713.
Lemma TF_15a40 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a40 : word) = Some TW_15a40.
Proof. vm_refl. Qed.
Lemma TD_15a40 : decode_any TW_15a40 = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a44 : bv 32 := 0xf3800793.
Lemma TF_15a44 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a44 : word) = Some TW_15a44.
Proof. vm_refl. Qed.
Lemma TD_15a44 : decode_any TW_15a44 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a48 : bv 32 := 0x28468513.
Lemma TF_15a48 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a48 : word) = Some TW_15a48.
Proof. vm_refl. Qed.
Lemma TD_15a48 : decode_any TW_15a48 = Some (OpImm ALU_ADD 10 13 644, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a4c : bv 32 := 0x40a787b3.
Lemma TF_15a4c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a4c : word) = Some TW_15a4c.
Proof. vm_refl. Qed.
Lemma TD_15a4c : decode_any TW_15a4c = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a50 : bv 32 := 0x00f77733.
Lemma TF_15a50 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a50 : word) = Some TW_15a50.
Proof. vm_refl. Qed.
Lemma TD_15a50 : decode_any TW_15a50 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a54 : bv 32 := 0xfff64693.
Lemma TF_15a54 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a54 : word) = Some TW_15a54.
Proof. vm_refl. Qed.
Lemma TD_15a54 : decode_any TW_15a54 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a58 : bv 32 := 0x00e50933.
Lemma TF_15a58 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a58 : word) = Some TW_15a58.
Proof. vm_refl. Qed.
Lemma TD_15a58 : decode_any TW_15a58 = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a5c : bv 32 := 0x00369693.
Lemma TF_15a5c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a5c : word) = Some TW_15a5c.
Proof. vm_refl. Qed.
Lemma TD_15a5c : decode_any TW_15a5c = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a60 : bv 32 := 0x00d506b3.
Lemma TF_15a60 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a60 : word) = Some TW_15a60.
Proof. vm_refl. Qed.
Lemma TD_15a60 : decode_any TW_15a60 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a64 : bv 32 := 0x00b68a33.
Lemma TF_15a64 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a64 : word) = Some TW_15a64.
Proof. vm_refl. Qed.
Lemma TD_15a64 : decode_any TW_15a64 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a68 : bv 32 := 0x0c890413.
Lemma TF_15a68 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a68 : word) = Some TW_15a68.
Proof. vm_refl. Qed.
Lemma TD_15a68 : decode_any TW_15a68 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a6c : bv 32 := 0x04098463.
Lemma TF_15a6c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a6c : word) = Some TW_15a6c.
Proof. vm_refl. Qed.
Lemma TD_15a6c : decode_any TW_15a6c = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a70 : bv 32 := 0x00361613.
Lemma TF_15a70 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a70 : word) = Some TW_15a70.
Proof. vm_refl. Qed.
Lemma TD_15a70 : decode_any TW_15a70 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a74 : bv 32 := 0x40c50533.
Lemma TF_15a74 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a74 : word) = Some TW_15a74.
Proof. vm_refl. Qed.
Lemma TD_15a74 : decode_any TW_15a74 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a78 : bv 32 := 0x00b50ab3.
Lemma TF_15a78 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a78 : word) = Some TW_15a78.
Proof. vm_refl. Qed.
Lemma TD_15a78 : decode_any TW_15a78 = Some (Op ALU_ADD 21 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a7c : bv 32 := 0x0289b503.
Lemma TF_15a7c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a7c : word) = Some TW_15a7c.
Proof. vm_refl. Qed.
Lemma TD_15a7c : decode_any TW_15a7c = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a80 : bv 32 := 0x00a40533.
Lemma TF_15a80 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a80 : word) = Some TW_15a80.
Proof. vm_refl. Qed.
Lemma TD_15a80 : decode_any TW_15a80 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a84 : bv 32 := 0x7ff50513.
Lemma TF_15a84 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a84 : word) = Some TW_15a84.
Proof. vm_refl. Qed.
Lemma TD_15a84 : decode_any TW_15a84 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a88 : bv 32 := 0x00150513.
Lemma TF_15a88 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a88 : word) = Some TW_15a88.
Proof. vm_refl. Qed.
Lemma TD_15a88 : decode_any TW_15a88 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a8c : bv 32 := 0x00aab023.
Lemma TF_15a8c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a8c : word) = Some TW_15a8c.
Proof. vm_refl. Qed.
Lemma TD_15a8c : decode_any TW_15a8c = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a90 : bv 32 := 0x0289b503.
Lemma TF_15a90 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a90 : word) = Some TW_15a90.
Proof. vm_refl. Qed.
Lemma TD_15a90 : decode_any TW_15a90 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a94 : bv 32 := 0x0089b583.
Lemma TF_15a94 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a94 : word) = Some TW_15a94.
Proof. vm_refl. Qed.
Lemma TD_15a94 : decode_any TW_15a94 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a98 : bv 32 := 0x0109b603.
Lemma TF_15a98 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a98 : word) = Some TW_15a98.
Proof. vm_refl. Qed.
Lemma TD_15a98 : decode_any TW_15a98 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15a9c : bv 32 := 0x00a40533.
Lemma TF_15a9c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15a9c : word) = Some TW_15a9c.
Proof. vm_refl. Qed.
Lemma TD_15a9c : decode_any TW_15a9c = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15aa0 : bv 32 := 0x4e8070ef.
Lemma TF_15aa0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15aa0 : word) = Some TW_15aa0.
Proof. vm_refl. Qed.
Lemma TD_15aa0 : decode_any TW_15aa0 = Some (Jal 1 29928, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15aa4 : bv 32 := 0x0009b983.
Lemma TF_15aa4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15aa4 : word) = Some TW_15aa4.
Proof. vm_refl. Qed.
Lemma TD_15aa4 : decode_any TW_15aa4 = Some (Load SZ8 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15aa8 : bv 32 := 0x008a8a93.
Lemma TF_15aa8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15aa8 : word) = Some TW_15aa8.
Proof. vm_refl. Qed.
Lemma TD_15aa8 : decode_any TW_15aa8 = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15aac : bv 32 := 0xfc0998e3.
Lemma TF_15aac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15aac : word) = Some TW_15aac.
Proof. vm_refl. Qed.
Lemma TD_15aac : decode_any TW_15aac = Some (Branch BC_NE 19 0 8144, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ab0 : bv 32 := 0x0284b603.
Lemma TF_15ab0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ab0 : word) = Some TW_15ab0.
Proof. vm_refl. Qed.
Lemma TD_15ab0 : decode_any TW_15ab0 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ab4 : bv 32 := 0x00ca3023.
Lemma TF_15ab4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ab4 : word) = Some TW_15ab4.
Proof. vm_refl. Qed.
Lemma TD_15ab4 : decode_any TW_15ab4 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ab8 : bv 32 := 0x0d493023.
Lemma TF_15ab8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ab8 : word) = Some TW_15ab8.
Proof. vm_refl. Qed.
Lemma TD_15ab8 : decode_any TW_15ab8 = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15abc : bv 32 := 0x01293023.
Lemma TF_15abc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15abc : word) = Some TW_15abc.
Proof. vm_refl. Qed.
Lemma TD_15abc : decode_any TW_15abc = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ac0 : bv 32 := 0x00040513.
Lemma TF_15ac0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ac0 : word) = Some TW_15ac0.
Proof. vm_refl. Qed.
Lemma TD_15ac0 : decode_any TW_15ac0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ac4 : bv 32 := 0x5f5070ef.
Lemma TF_15ac4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ac4 : word) = Some TW_15ac4.
Proof. vm_refl. Qed.
Lemma TD_15ac4 : decode_any TW_15ac4 = Some (Jal 1 32244, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ac8 : bv 32 := 0x04054a63.
Lemma TF_15ac8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ac8 : word) = Some TW_15ac8.
Proof. vm_refl. Qed.
Lemma TD_15ac8 : decode_any TW_15ac8 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15acc : bv 32 := 0x00051663.
Lemma TF_15acc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15acc : word) = Some TW_15acc.
Proof. vm_refl. Qed.
Lemma TD_15acc : decode_any TW_15acc = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ad0 : bv 32 := 0x00100513.
Lemma TF_15ad0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ad0 : word) = Some TW_15ad0.
Proof. vm_refl. Qed.
Lemma TD_15ad0 : decode_any TW_15ad0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ad4 : bv 32 := 0x00a48023.
Lemma TF_15ad4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ad4 : word) = Some TW_15ad4.
Proof. vm_refl. Qed.
Lemma TD_15ad4 : decode_any TW_15ad4 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ad8 : bv 32 := 0x00200513.
Lemma TF_15ad8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ad8 : word) = Some TW_15ad8.
Proof. vm_refl. Qed.
Lemma TD_15ad8 : decode_any TW_15ad8 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15adc : bv 32 := 0x0003a597.
Lemma TF_15adc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15adc : word) = Some TW_15adc.
Proof. vm_refl. Qed.
Lemma TD_15adc : decode_any TW_15adc = Some (Auipc 11 58, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ae0 : bv 32 := 0x02a92423.
Lemma TF_15ae0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ae0 : word) = Some TW_15ae0.
Proof. vm_refl. Qed.
Lemma TD_15ae0 : decode_any TW_15ae0 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ae4 : bv 32 := 0x06000893.
Lemma TF_15ae4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ae4 : word) = Some TW_15ae4.
Proof. vm_refl. Qed.
Lemma TD_15ae4 : decode_any TW_15ae4 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15ae8 : bv 32 := 0x2ac58513.
Lemma TF_15ae8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ae8 : word) = Some TW_15ae8.
Proof. vm_refl. Qed.
Lemma TD_15ae8 : decode_any TW_15ae8 = Some (OpImm ALU_ADD 10 11 684, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15aec : bv 32 := 0x03848593.
Lemma TF_15aec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15aec : word) = Some TW_15aec.
Proof. vm_refl. Qed.
Lemma TD_15aec : decode_any TW_15aec = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15af0 : bv 32 := 0x00000073.
Lemma TF_15af0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15af0 : word) = Some TW_15af0.
Proof. vm_refl. Qed.
Lemma TD_15af0 : decode_any TW_15af0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_15af0 : is_ecall TW_15af0 = true.
Proof. reflexivity. Qed.

Definition TW_15af4 : bv 32 := 0x07890613.
Lemma TF_15af4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15af4 : word) = Some TW_15af4.
Proof. vm_refl. Qed.
Lemma TD_15af4 : decode_any TW_15af4 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15af8 : bv 32 := 0x02a92023.
Lemma TF_15af8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15af8 : word) = Some TW_15af8.
Proof. vm_refl. Qed.
Lemma TD_15af8 : decode_any TW_15af8 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15afc : bv 32 := 0x08b93c23.
Lemma TF_15afc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15afc : word) = Some TW_15afc.
Proof. vm_refl. Qed.
Lemma TD_15afc : decode_any TW_15afc = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b00 : bv 32 := 0x06c93c23.
Lemma TF_15b00 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b00 : word) = Some TW_15b00.
Proof. vm_refl. Qed.
Lemma TD_15b00 : decode_any TW_15b00 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b04 : bv 32 := 0x0003a517.
Lemma TF_15b04 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b04 : word) = Some TW_15b04.
Proof. vm_refl. Qed.
Lemma TD_15b04 : decode_any TW_15b04 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b08 : bv 32 := 0x4f453503.
Lemma TF_15b08 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b08 : word) = Some TW_15b08.
Proof. vm_refl. Qed.
Lemma TD_15b08 : decode_any TW_15b08 = Some (Load SZ8 true 10 10 1268, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b0c : bv 32 := 0x01293423.
Lemma TF_15b0c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b0c : word) = Some TW_15b0c.
Proof. vm_refl. Qed.
Lemma TD_15b0c : decode_any TW_15b0c = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b10 : bv 32 := 0x01293823.
Lemma TF_15b10 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b10 : word) = Some TW_15b10.
Proof. vm_refl. Qed.
Lemma TD_15b10 : decode_any TW_15b10 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b14 : bv 32 := 0x00a93c23.
Lemma TF_15b14 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b14 : word) = Some TW_15b14.
Proof. vm_refl. Qed.
Lemma TD_15b14 : decode_any TW_15b14 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b18 : bv 32 := 0x0080006f.
Lemma TF_15b18 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b18 : word) = Some TW_15b18.
Proof. vm_refl. Qed.
Lemma TD_15b18 : decode_any TW_15b18 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b1c : bv 32 := 0x00000023.
Lemma TF_15b1c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b1c : word) = Some TW_15b1c.
Proof. vm_refl. Qed.
Lemma TD_15b1c : decode_any TW_15b1c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b20 : bv 32 := 0x03813083.
Lemma TF_15b20 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b20 : word) = Some TW_15b20.
Proof. vm_refl. Qed.
Lemma TD_15b20 : decode_any TW_15b20 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b24 : bv 32 := 0x03013403.
Lemma TF_15b24 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b24 : word) = Some TW_15b24.
Proof. vm_refl. Qed.
Lemma TD_15b24 : decode_any TW_15b24 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b28 : bv 32 := 0x02813483.
Lemma TF_15b28 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b28 : word) = Some TW_15b28.
Proof. vm_refl. Qed.
Lemma TD_15b28 : decode_any TW_15b28 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b2c : bv 32 := 0x02013903.
Lemma TF_15b2c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b2c : word) = Some TW_15b2c.
Proof. vm_refl. Qed.
Lemma TD_15b2c : decode_any TW_15b2c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b30 : bv 32 := 0x01813983.
Lemma TF_15b30 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b30 : word) = Some TW_15b30.
Proof. vm_refl. Qed.
Lemma TD_15b30 : decode_any TW_15b30 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b34 : bv 32 := 0x01013a03.
Lemma TF_15b34 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b34 : word) = Some TW_15b34.
Proof. vm_refl. Qed.
Lemma TD_15b34 : decode_any TW_15b34 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b38 : bv 32 := 0x00813a83.
Lemma TF_15b38 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b38 : word) = Some TW_15b38.
Proof. vm_refl. Qed.
Lemma TD_15b38 : decode_any TW_15b38 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b3c : bv 32 := 0x04010113.
Lemma TF_15b3c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b3c : word) = Some TW_15b3c.
Proof. vm_refl. Qed.
Lemma TD_15b3c : decode_any TW_15b3c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition TW_15b40 : bv 32 := 0x00008067.
Lemma TF_15b40 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15b40 : word) = Some TW_15b40.
Proof. vm_refl. Qed.
Lemma TD_15b40 : decode_any TW_15b40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b68 : bv 32 := 0x00050593.
Lemma F_15b68 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c08 : word) = Some W_15b68.
Proof. vm_refl. Qed.
Lemma D_15b68 : decode_any W_15b68 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b6c : bv 32 := 0x05e00893.
Lemma F_15b6c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c0c : word) = Some W_15b6c.
Proof. vm_refl. Qed.
Lemma D_15b6c : decode_any W_15b6c = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b70 : bv 32 := 0x00000073.
Lemma F_15b70 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c10 : word) = Some W_15b70.
Proof. vm_refl. Qed.
Lemma D_15b70 : decode_any W_15b70 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_15b70 : is_ecall W_15b70 = true.
Proof. reflexivity. Qed.

Definition W_15b84 : bv 32 := 0xfd010113.
Lemma F_15b84 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c24 : word) = Some W_15b84.
Proof. vm_refl. Qed.
Lemma D_15b84 : decode_any W_15b84 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b88 : bv 32 := 0x02113423.
Lemma F_15b88 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c28 : word) = Some W_15b88.
Proof. vm_refl. Qed.
Lemma D_15b88 : decode_any W_15b88 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b8c : bv 32 := 0x02813023.
Lemma F_15b8c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c2c : word) = Some W_15b8c.
Proof. vm_refl. Qed.
Lemma D_15b8c : decode_any W_15b8c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b90 : bv 32 := 0x00913c23.
Lemma F_15b90 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c30 : word) = Some W_15b90.
Proof. vm_refl. Qed.
Lemma D_15b90 : decode_any W_15b90 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b94 : bv 32 := 0x01213823.
Lemma F_15b94 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c34 : word) = Some W_15b94.
Proof. vm_refl. Qed.
Lemma D_15b94 : decode_any W_15b94 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b98 : bv 32 := 0x01313423.
Lemma F_15b98 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c38 : word) = Some W_15b98.
Proof. vm_refl. Qed.
Lemma D_15b98 : decode_any W_15b98 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15b9c : bv 32 := 0x0003a517.
Lemma F_15b9c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c3c : word) = Some W_15b9c.
Proof. vm_refl. Qed.
Lemma D_15b9c : decode_any W_15b9c = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ba0 : bv 32 := 0x18c50913.
Lemma F_15ba0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c40 : word) = Some W_15ba0.
Proof. vm_refl. Qed.
Lemma D_15ba0 : decode_any W_15ba0 = Some (OpImm ALU_ADD 18 10 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ba4 : bv 32 := 0x00490413.
Lemma F_15ba4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c44 : word) = Some W_15ba4.
Proof. vm_refl. Qed.
Lemma D_15ba4 : decode_any W_15ba4 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ba8 : bv 32 := 0x00040513.
Lemma F_15ba8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c48 : word) = Some W_15ba8.
Proof. vm_refl. Qed.
Lemma D_15ba8 : decode_any W_15ba8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bac : bv 32 := 0x149070ef.
Lemma F_15bac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c4c : word) = Some W_15bac.
Proof. vm_refl. Qed.
Lemma D_15bac : decode_any W_15bac = Some (Jal 1 31048, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bb0 : bv 32 := 0x01093503.
Lemma F_15bb0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c50 : word) = Some W_15bb0.
Proof. vm_refl. Qed.
Lemma D_15bb0 : decode_any W_15bb0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bb4 : bv 32 := 0x06050863.
Lemma F_15bb4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c54 : word) = Some W_15bb4.
Proof. vm_refl. Qed.
Lemma D_15bb4 : decode_any W_15bb4 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bb8 : bv 32 := 0x00892583.
Lemma F_15bb8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c58 : word) = Some W_15bb8.
Proof. vm_refl. Qed.
Lemma D_15bb8 : decode_any W_15bb8 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bbc : bv 32 := 0x0180006f.
Lemma F_15bbc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c5c : word) = Some W_15bbc.
Proof. vm_refl. Qed.
Lemma D_15bbc : decode_any W_15bbc = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bc0 : bv 32 := 0x00053503.
Lemma F_15bc0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c60 : word) = Some W_15bc0.
Proof. vm_refl. Qed.
Lemma D_15bc0 : decode_any W_15bc0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bc4 : bv 32 := 0x02000593.
Lemma F_15bc4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c64 : word) = Some W_15bc4.
Proof. vm_refl. Qed.
Lemma D_15bc4 : decode_any W_15bc4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bc8 : bv 32 := 0x00b92423.
Lemma F_15bc8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c68 : word) = Some W_15bc8.
Proof. vm_refl. Qed.
Lemma D_15bc8 : decode_any W_15bc8 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bcc : bv 32 := 0x00a93823.
Lemma F_15bcc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c6c : word) = Some W_15bcc.
Proof. vm_refl. Qed.
Lemma D_15bcc : decode_any W_15bcc = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bd0 : bv 32 := 0x04050a63.
Lemma F_15bd0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c70 : word) = Some W_15bd0.
Proof. vm_refl. Qed.
Lemma D_15bd0 : decode_any W_15bd0 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bd4 : bv 32 := 0xfff5861b.
Lemma F_15bd4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c74 : word) = Some W_15bd4.
Proof. vm_refl. Qed.
Lemma D_15bd4 : decode_any W_15bd4 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bd8 : bv 32 := 0x00c92423.
Lemma F_15bd8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c78 : word) = Some W_15bd8.
Proof. vm_refl. Qed.
Lemma D_15bd8 : decode_any W_15bd8 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bdc : bv 32 := 0xfeb052e3.
Lemma F_15bdc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c7c : word) = Some W_15bdc.
Proof. vm_refl. Qed.
Lemma D_15bdc : decode_any W_15bdc = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_15be0 : bv 32 := 0x01093503.
Lemma F_15be0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c80 : word) = Some W_15be0.
Proof. vm_refl. Qed.
Lemma D_15be0 : decode_any W_15be0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15be4 : bv 32 := 0x00361613.
Lemma F_15be4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c84 : word) = Some W_15be4.
Proof. vm_refl. Qed.
Lemma D_15be4 : decode_any W_15be4 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_15be8 : bv 32 := 0x00c50533.
Lemma F_15be8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c88 : word) = Some W_15be8.
Proof. vm_refl. Qed.
Lemma D_15be8 : decode_any W_15be8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bec : bv 32 := 0x00853983.
Lemma F_15bec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c8c : word) = Some W_15bec.
Proof. vm_refl. Qed.
Lemma D_15bec : decode_any W_15bec = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bf0 : bv 32 := 0x10853483.
Lemma F_15bf0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c90 : word) = Some W_15bf0.
Proof. vm_refl. Qed.
Lemma D_15bf0 : decode_any W_15bf0 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bf4 : bv 32 := 0x00040513.
Lemma F_15bf4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c94 : word) = Some W_15bf4.
Proof. vm_refl. Qed.
Lemma D_15bf4 : decode_any W_15bf4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bf8 : bv 32 := 0x385070ef.
Lemma F_15bf8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c98 : word) = Some W_15bf8.
Proof. vm_refl. Qed.
Lemma D_15bf8 : decode_any W_15bf8 = Some (Jal 1 31620, 4%Z).
Proof. vm_refl. Qed.

Definition W_15bfc : bv 32 := 0x00048513.
Lemma F_15bfc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15c9c : word) = Some W_15bfc.
Proof. vm_refl. Qed.
Lemma D_15bfc : decode_any W_15bfc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c00 : bv 32 := 0x000980e7.
Lemma F_15c00 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ca0 : word) = Some W_15c00.
Proof. vm_refl. Qed.
Lemma D_15c00 : decode_any W_15c00 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c04 : bv 32 := 0x00040513.
Lemma F_15c04 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ca4 : word) = Some W_15c04.
Proof. vm_refl. Qed.
Lemma D_15c04 : decode_any W_15c04 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c08 : bv 32 := 0x0ed070ef.
Lemma F_15c08 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ca8 : word) = Some W_15c08.
Proof. vm_refl. Qed.
Lemma D_15c08 : decode_any W_15c08 = Some (Jal 1 30956, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c0c : bv 32 := 0x00892503.
Lemma F_15c0c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cac : word) = Some W_15c0c.
Proof. vm_refl. Qed.
Lemma D_15c0c : decode_any W_15c0c = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c10 : bv 32 := 0xfff5061b.
Lemma F_15c10 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cb0 : word) = Some W_15c10.
Proof. vm_refl. Qed.
Lemma D_15c10 : decode_any W_15c10 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c14 : bv 32 := 0x00c92423.
Lemma F_15c14 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cb4 : word) = Some W_15c14.
Proof. vm_refl. Qed.
Lemma D_15c14 : decode_any W_15c14 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c18 : bv 32 := 0xfca044e3.
Lemma F_15c18 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cb8 : word) = Some W_15c18.
Proof. vm_refl. Qed.
Lemma D_15c18 : decode_any W_15c18 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c1c : bv 32 := 0x01093503.
Lemma F_15c1c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cbc : word) = Some W_15c1c.
Proof. vm_refl. Qed.
Lemma D_15c1c : decode_any W_15c1c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c20 : bv 32 := 0xfa1ff06f.
Lemma F_15c20 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cc0 : word) = Some W_15c20.
Proof. vm_refl. Qed.
Lemma D_15c20 : decode_any W_15c20 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c24 : bv 32 := 0x00100513.
Lemma F_15c24 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cc4 : word) = Some W_15c24.
Proof. vm_refl. Qed.
Lemma D_15c24 : decode_any W_15c24 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c28 : bv 32 := 0x00a90023.
Lemma F_15c28 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cc8 : word) = Some W_15c28.
Proof. vm_refl. Qed.
Lemma D_15c28 : decode_any W_15c28 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c2c : bv 32 := 0x00040513.
Lemma F_15c2c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ccc : word) = Some W_15c2c.
Proof. vm_refl. Qed.
Lemma D_15c2c : decode_any W_15c2c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c30 : bv 32 := 0x02813083.
Lemma F_15c30 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cd0 : word) = Some W_15c30.
Proof. vm_refl. Qed.
Lemma D_15c30 : decode_any W_15c30 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c34 : bv 32 := 0x02013403.
Lemma F_15c34 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cd4 : word) = Some W_15c34.
Proof. vm_refl. Qed.
Lemma D_15c34 : decode_any W_15c34 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c38 : bv 32 := 0x01813483.
Lemma F_15c38 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cd8 : word) = Some W_15c38.
Proof. vm_refl. Qed.
Lemma D_15c38 : decode_any W_15c38 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c3c : bv 32 := 0x01013903.
Lemma F_15c3c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cdc : word) = Some W_15c3c.
Proof. vm_refl. Qed.
Lemma D_15c3c : decode_any W_15c3c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c40 : bv 32 := 0x00813983.
Lemma F_15c40 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ce0 : word) = Some W_15c40.
Proof. vm_refl. Qed.
Lemma D_15c40 : decode_any W_15c40 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c44 : bv 32 := 0x03010113.
Lemma F_15c44 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ce4 : word) = Some W_15c44.
Proof. vm_refl. Qed.
Lemma D_15c44 : decode_any W_15c44 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c48 : bv 32 := 0x3350706f.
Lemma F_15c48 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ce8 : word) = Some W_15c48.
Proof. vm_refl. Qed.
Lemma D_15c48 : decode_any W_15c48 = Some (Jal 0 31540, 4%Z).
Proof. vm_refl. Qed.

Definition W_15c4c : bv 32 := 0x00008067.
Lemma F_15c4c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15cec : word) = Some W_15c4c.
Proof. vm_refl. Qed.
Lemma D_15c4c : decode_any W_15c4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d14 : bv 32 := 0x00050067.
Lemma F_15d14 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15db4 : word) = Some W_15d14.
Proof. vm_refl. Qed.
Lemma D_15d14 : decode_any W_15d14 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d18 : bv 32 := 0x00008067.
Lemma F_15d18 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15db8 : word) = Some W_15d18.
Proof. vm_refl. Qed.
Lemma D_15d18 : decode_any W_15d18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d1c : bv 32 := 0xfe010113.
Lemma F_15d1c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15dbc : word) = Some W_15d1c.
Proof. vm_refl. Qed.
Lemma D_15d1c : decode_any W_15d1c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d20 : bv 32 := 0x00113c23.
Lemma F_15d20 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15dc0 : word) = Some W_15d20.
Proof. vm_refl. Qed.
Lemma D_15d20 : decode_any W_15d20 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d24 : bv 32 := 0x00813823.
Lemma F_15d24 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15dc4 : word) = Some W_15d24.
Proof. vm_refl. Qed.
Lemma D_15d24 : decode_any W_15d24 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d28 : bv 32 := 0x00913423.
Lemma F_15d28 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15dc8 : word) = Some W_15d28.
Proof. vm_refl. Qed.
Lemma D_15d28 : decode_any W_15d28 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d2c : bv 32 := 0x00009517.
Lemma F_15d2c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15dcc : word) = Some W_15d2c.
Proof. vm_refl. Qed.
Lemma D_15d2c : decode_any W_15d2c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d30 : bv 32 := 0x00009597.
Lemma F_15d30 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15dd0 : word) = Some W_15d30.
Proof. vm_refl. Qed.
Lemma D_15d30 : decode_any W_15d30 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d34 : bv 32 := 0xc4453503.
Lemma F_15d34 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15dd4 : word) = Some W_15d34.
Proof. vm_refl. Qed.
Lemma D_15d34 : decode_any W_15d34 = Some (Load SZ8 true 10 10 3140, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d38 : bv 32 := 0xc485b403.
Lemma F_15d38 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15dd8 : word) = Some W_15d38.
Proof. vm_refl. Qed.
Lemma D_15d38 : decode_any W_15d38 = Some (Load SZ8 true 8 11 3144, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d3c : bv 32 := 0x00a47c63.
Lemma F_15d3c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ddc : word) = Some W_15d3c.
Proof. vm_refl. Qed.
Lemma D_15d3c : decode_any W_15d3c = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d40 : bv 32 := 0xff853583.
Lemma F_15d40 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15de0 : word) = Some W_15d40.
Proof. vm_refl. Qed.
Lemma D_15d40 : decode_any W_15d40 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d44 : bv 32 := 0xff850493.
Lemma F_15d44 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15de4 : word) = Some W_15d44.
Proof. vm_refl. Qed.
Lemma D_15d44 : decode_any W_15d44 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d48 : bv 32 := 0x000580e7.
Lemma F_15d48 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15de8 : word) = Some W_15d48.
Proof. vm_refl. Qed.
Lemma D_15d48 : decode_any W_15d48 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d4c : bv 32 := 0x00048513.
Lemma F_15d4c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15dec : word) = Some W_15d4c.
Proof. vm_refl. Qed.
Lemma D_15d4c : decode_any W_15d4c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d50 : bv 32 := 0xfe9468e3.
Lemma F_15d50 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15df0 : word) = Some W_15d50.
Proof. vm_refl. Qed.
Lemma D_15d50 : decode_any W_15d50 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d54 : bv 32 := 0x01813083.
Lemma F_15d54 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15df4 : word) = Some W_15d54.
Proof. vm_refl. Qed.
Lemma D_15d54 : decode_any W_15d54 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d58 : bv 32 := 0x01013403.
Lemma F_15d58 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15df8 : word) = Some W_15d58.
Proof. vm_refl. Qed.
Lemma D_15d58 : decode_any W_15d58 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d5c : bv 32 := 0x00813483.
Lemma F_15d5c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15dfc : word) = Some W_15d5c.
Proof. vm_refl. Qed.
Lemma D_15d5c : decode_any W_15d5c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d60 : bv 32 := 0x02010113.
Lemma F_15d60 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e00 : word) = Some W_15d60.
Proof. vm_refl. Qed.
Lemma D_15d60 : decode_any W_15d60 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d64 : bv 32 := 0xfb5ff06f.
Lemma F_15d64 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e04 : word) = Some W_15d64.
Proof. vm_refl. Qed.
Lemma D_15d64 : decode_any W_15d64 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d68 : bv 32 := 0xff010113.
Lemma F_15d68 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e08 : word) = Some W_15d68.
Proof. vm_refl. Qed.
Lemma D_15d68 : decode_any W_15d68 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d6c : bv 32 := 0x00113423.
Lemma F_15d6c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e0c : word) = Some W_15d6c.
Proof. vm_refl. Qed.
Lemma D_15d6c : decode_any W_15d6c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d70 : bv 32 := 0x00813023.
Lemma F_15d70 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e10 : word) = Some W_15d70.
Proof. vm_refl. Qed.
Lemma D_15d70 : decode_any W_15d70 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d74 : bv 32 := 0x00000593.
Lemma F_15d74 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e14 : word) = Some W_15d74.
Proof. vm_refl. Qed.
Lemma D_15d74 : decode_any W_15d74 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d78 : bv 32 := 0x00020613.
Lemma F_15d78 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e18 : word) = Some W_15d78.
Proof. vm_refl. Qed.
Lemma D_15d78 : decode_any W_15d78 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d7c : bv 32 := 0xf5862603.
Lemma F_15d7c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e1c : word) = Some W_15d7c.
Proof. vm_refl. Qed.
Lemma D_15d7c : decode_any W_15d7c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d80 : bv 32 := 0x0003a697.
Lemma F_15d80 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e20 : word) = Some W_15d80.
Proof. vm_refl. Qed.
Lemma D_15d80 : decode_any W_15d80 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d84 : bv 32 := 0x1c868693.
Lemma F_15d84 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e24 : word) = Some W_15d84.
Proof. vm_refl. Qed.
Lemma D_15d84 : decode_any W_15d84 = Some (OpImm ALU_ADD 13 13 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d88 : bv 32 := 0x1606a72f.
Lemma F_15d88 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e28 : word) = Some W_15d88.
Proof. vm_refl. Qed.
Lemma D_15d88 : decode_any W_15d88 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d8c : bv 32 := 0x00b71663.
Lemma F_15d8c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e2c : word) = Some W_15d8c.
Proof. vm_refl. Qed.
Lemma D_15d8c : decode_any W_15d8c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d90 : bv 32 := 0x1ec6a7af.
Lemma F_15d90 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e30 : word) = Some W_15d90.
Proof. vm_refl. Qed.
Lemma D_15d90 : decode_any W_15d90 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d94 : bv 32 := 0xfe079ae3.
Lemma F_15d94 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e34 : word) = Some W_15d94.
Proof. vm_refl. Qed.
Lemma D_15d94 : decode_any W_15d94 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d98 : bv 32 := 0x0007059b.
Lemma F_15d98 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e38 : word) = Some W_15d98.
Proof. vm_refl. Qed.
Lemma D_15d98 : decode_any W_15d98 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15d9c : bv 32 := 0x02c58263.
Lemma F_15d9c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e3c : word) = Some W_15d9c.
Proof. vm_refl. Qed.
Lemma D_15d9c : decode_any W_15d9c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_15da0 : bv 32 := 0x02058263.
Lemma F_15da0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e40 : word) = Some W_15da0.
Proof. vm_refl. Qed.
Lemma D_15da0 : decode_any W_15da0 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_15da4 : bv 32 := 0x04900893.
Lemma F_15da4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e44 : word) = Some W_15da4.
Proof. vm_refl. Qed.
Lemma D_15da4 : decode_any W_15da4 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_15da8 : bv 32 := 0x00000593.
Lemma F_15da8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e48 : word) = Some W_15da8.
Proof. vm_refl. Qed.
Lemma D_15da8 : decode_any W_15da8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dac : bv 32 := 0x00000613.
Lemma F_15dac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e4c : word) = Some W_15dac.
Proof. vm_refl. Qed.
Lemma D_15dac : decode_any W_15dac = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15db0 : bv 32 := 0x00000693.
Lemma F_15db0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e50 : word) = Some W_15db0.
Proof. vm_refl. Qed.
Lemma D_15db0 : decode_any W_15db0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15db4 : bv 32 := 0x00000513.
Lemma F_15db4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e54 : word) = Some W_15db4.
Proof. vm_refl. Qed.
Lemma D_15db4 : decode_any W_15db4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15db8 : bv 32 := 0x00000073.
Lemma F_15db8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e58 : word) = Some W_15db8.
Proof. vm_refl. Qed.
Lemma D_15db8 : decode_any W_15db8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_15db8 : is_ecall W_15db8 = true.
Proof. reflexivity. Qed.

Definition W_15dbc : bv 32 := 0xff9ff06f.
Lemma F_15dbc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e5c : word) = Some W_15dbc.
Proof. vm_refl. Qed.
Lemma D_15dbc : decode_any W_15dbc = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dc0 : bv 32 := 0x00000023.
Lemma F_15dc0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e60 : word) = Some W_15dc0.
Proof. vm_refl. Qed.
Lemma D_15dc0 : decode_any W_15dc0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dc4 : bv 32 := 0x00050413.
Lemma F_15dc4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e64 : word) = Some W_15dc4.
Proof. vm_refl. Qed.
Lemma D_15dc4 : decode_any W_15dc4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dc8 : bv 32 := 0xdbdff0ef.
Lemma F_15dc8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e68 : word) = Some W_15dc8.
Proof. vm_refl. Qed.
Lemma D_15dc8 : decode_any W_15dc8 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dcc : bv 32 := 0xf51ff0ef.
Lemma F_15dcc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e6c : word) = Some W_15dcc.
Proof. vm_refl. Qed.
Lemma D_15dcc : decode_any W_15dcc = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dd0 : bv 32 := 0x310020ef.
Lemma F_15dd0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e70 : word) = Some W_15dd0.
Proof. vm_refl. Qed.
Lemma D_15dd0 : decode_any W_15dd0 = Some (Jal 1 8976, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dd4 : bv 32 := 0x00040513.
Lemma F_15dd4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e74 : word) = Some W_15dd4.
Proof. vm_refl. Qed.
Lemma D_15dd4 : decode_any W_15dd4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15dd8 : bv 32 := 0xd91ff0ef.
Lemma F_15dd8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15e78 : word) = Some W_15dd8.
Proof. vm_refl. Qed.
Lemma D_15dd8 : decode_any W_15dd8 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ec0 : bv 32 := 0xff010113.
Lemma F_15ec0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f60 : word) = Some W_15ec0.
Proof. vm_refl. Qed.
Lemma D_15ec0 : decode_any W_15ec0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ec4 : bv 32 := 0x00113423.
Lemma F_15ec4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f64 : word) = Some W_15ec4.
Proof. vm_refl. Qed.
Lemma D_15ec4 : decode_any W_15ec4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ec8 : bv 32 := 0x00050e63.
Lemma F_15ec8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f68 : word) = Some W_15ec8.
Proof. vm_refl. Qed.
Lemma D_15ec8 : decode_any W_15ec8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ecc : bv 32 := 0x00050593.
Lemma F_15ecc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f6c : word) = Some W_15ecc.
Proof. vm_refl. Qed.
Lemma D_15ecc : decode_any W_15ecc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ed0 : bv 32 := 0x00009517.
Lemma F_15ed0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f70 : word) = Some W_15ed0.
Proof. vm_refl. Qed.
Lemma D_15ed0 : decode_any W_15ed0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ed4 : bv 32 := 0xa9853503.
Lemma F_15ed4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f74 : word) = Some W_15ed4.
Proof. vm_refl. Qed.
Lemma D_15ed4 : decode_any W_15ed4 = Some (Load SZ8 true 10 10 2712, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ed8 : bv 32 := 0x00800613.
Lemma F_15ed8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f78 : word) = Some W_15ed8.
Proof. vm_refl. Qed.
Lemma D_15ed8 : decode_any W_15ed8 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15edc : bv 32 := 0x00c070ef.
Lemma F_15edc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f7c : word) = Some W_15edc.
Proof. vm_refl. Qed.
Lemma D_15edc : decode_any W_15edc = Some (Jal 1 28684, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ee0 : bv 32 := 0x01c0006f.
Lemma F_15ee0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f80 : word) = Some W_15ee0.
Proof. vm_refl. Qed.
Lemma D_15ee0 : decode_any W_15ee0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ee4 : bv 32 := 0x00009517.
Lemma F_15ee4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f84 : word) = Some W_15ee4.
Proof. vm_refl. Qed.
Lemma D_15ee4 : decode_any W_15ee4 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ee8 : bv 32 := 0xa8453503.
Lemma F_15ee8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f88 : word) = Some W_15ee8.
Proof. vm_refl. Qed.
Lemma D_15ee8 : decode_any W_15ee8 = Some (Load SZ8 true 10 10 2692, 4%Z).
Proof. vm_refl. Qed.

Definition W_15eec : bv 32 := 0x41c655b7.
Lemma F_15eec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f8c : word) = Some W_15eec.
Proof. vm_refl. Qed.
Lemma D_15eec : decode_any W_15eec = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ef0 : bv 32 := 0xe6d5859b.
Lemma F_15ef0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f90 : word) = Some W_15ef0.
Proof. vm_refl. Qed.
Lemma D_15ef0 : decode_any W_15ef0 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ef4 : bv 32 := 0x02b505b3.
Lemma F_15ef4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f94 : word) = Some W_15ef4.
Proof. vm_refl. Qed.
Lemma D_15ef4 : decode_any W_15ef4 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_15ef8 : bv 32 := 0x00b53023.
Lemma F_15ef8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f98 : word) = Some W_15ef8.
Proof. vm_refl. Qed.
Lemma D_15ef8 : decode_any W_15ef8 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15efc : bv 32 := 0x00009517.
Lemma F_15efc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15f9c : word) = Some W_15efc.
Proof. vm_refl. Qed.
Lemma D_15efc : decode_any W_15efc = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f00 : bv 32 := 0xa6c53503.
Lemma F_15f00 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fa0 : word) = Some W_15f00.
Proof. vm_refl. Qed.
Lemma D_15f00 : decode_any W_15f00 = Some (Load SZ8 true 10 10 2668, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f04 : bv 32 := 0x000500a3.
Lemma F_15f04 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fa4 : word) = Some W_15f04.
Proof. vm_refl. Qed.
Lemma D_15f04 : decode_any W_15f04 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f08 : bv 32 := 0x00053503.
Lemma F_15f08 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fa8 : word) = Some W_15f08.
Proof. vm_refl. Qed.
Lemma D_15f08 : decode_any W_15f08 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f0c : bv 32 := 0x00020593.
Lemma F_15f0c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fac : word) = Some W_15f0c.
Proof. vm_refl. Qed.
Lemma D_15f0c : decode_any W_15f0c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f10 : bv 32 := 0xfea5b823.
Lemma F_15f10 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fb0 : word) = Some W_15f10.
Proof. vm_refl. Qed.
Lemma D_15f10 : decode_any W_15f10 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f14 : bv 32 := 0x00813083.
Lemma F_15f14 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fb4 : word) = Some W_15f14.
Proof. vm_refl. Qed.
Lemma D_15f14 : decode_any W_15f14 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f18 : bv 32 := 0x01010113.
Lemma F_15f18 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fb8 : word) = Some W_15f18.
Proof. vm_refl. Qed.
Lemma D_15f18 : decode_any W_15f18 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f1c : bv 32 := 0x00008067.
Lemma F_15f1c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fbc : word) = Some W_15f1c.
Proof. vm_refl. Qed.
Lemma D_15f1c : decode_any W_15f1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f28 : bv 32 := 0xfffff5b7.
Lemma F_15f28 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fc8 : word) = Some W_15f28.
Proof. vm_refl. Qed.
Lemma D_15f28 : decode_any W_15f28 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f2c : bv 32 := 0x0015859b.
Lemma F_15f2c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fcc : word) = Some W_15f2c.
Proof. vm_refl. Qed.
Lemma D_15f2c : decode_any W_15f2c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f30 : bv 32 := 0x02b56663.
Lemma F_15f30 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15fd0 : word) = Some W_15f30.
Proof. vm_refl. Qed.
Lemma D_15f30 : decode_any W_15f30 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_15f5c : bv 32 := 0x00008067.
Lemma F_15f5c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x15ffc : word) = Some W_15f5c.
Proof. vm_refl. Qed.
Lemma D_15f5c : decode_any W_15f5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
