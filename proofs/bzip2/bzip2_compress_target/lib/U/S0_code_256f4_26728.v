(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_26534 : bv 32 := 0x0035f693.
Lemma F_26534 : fetch_word Ubsan.M.loaded_segments (0x306ac : word) = Some W_26534.
Proof. vm_refl. Qed.
Lemma D_26534 : decode_any W_26534 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26538 : bv 32 := 0x10068863.
Lemma F_26538 : fetch_word Ubsan.M.loaded_segments (0x306b0 : word) = Some W_26538.
Proof. vm_refl. Qed.
Lemma D_26538 : decode_any W_26538 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2653c : bv 32 := 0x02060e63.
Lemma F_2653c : fetch_word Ubsan.M.loaded_segments (0x306b4 : word) = Some W_2653c.
Proof. vm_refl. Qed.
Lemma D_2653c : decode_any W_2653c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26540 : bv 32 := 0x00158713.
Lemma F_26540 : fetch_word Ubsan.M.loaded_segments (0x306b8 : word) = Some W_26540.
Proof. vm_refl. Qed.
Lemma D_26540 : decode_any W_26540 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26544 : bv 32 := 0x00100793.
Lemma F_26544 : fetch_word Ubsan.M.loaded_segments (0x306bc : word) = Some W_26544.
Proof. vm_refl. Qed.
Lemma D_26544 : decode_any W_26544 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26548 : bv 32 := 0x00050693.
Lemma F_26548 : fetch_word Ubsan.M.loaded_segments (0x306c0 : word) = Some W_26548.
Proof. vm_refl. Qed.
Lemma D_26548 : decode_any W_26548 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2654c : bv 32 := 0x0005c883.
Lemma F_2654c : fetch_word Ubsan.M.loaded_segments (0x306c4 : word) = Some W_2654c.
Proof. vm_refl. Qed.
Lemma D_2654c : decode_any W_2654c = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26550 : bv 32 := 0x00060813.
Lemma F_26550 : fetch_word Ubsan.M.loaded_segments (0x306c8 : word) = Some W_26550.
Proof. vm_refl. Qed.
Lemma D_26550 : decode_any W_26550 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26554 : bv 32 := 0x00158593.
Lemma F_26554 : fetch_word Ubsan.M.loaded_segments (0x306cc : word) = Some W_26554.
Proof. vm_refl. Qed.
Lemma D_26554 : decode_any W_26554 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26558 : bv 32 := 0x00377293.
Lemma F_26558 : fetch_word Ubsan.M.loaded_segments (0x306d0 : word) = Some W_26558.
Proof. vm_refl. Qed.
Lemma D_26558 : decode_any W_26558 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2655c : bv 32 := 0x01168023.
Lemma F_2655c : fetch_word Ubsan.M.loaded_segments (0x306d4 : word) = Some W_2655c.
Proof. vm_refl. Qed.
Lemma D_2655c : decode_any W_2655c = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26560 : bv 32 := 0x00168693.
Lemma F_26560 : fetch_word Ubsan.M.loaded_segments (0x306d8 : word) = Some W_26560.
Proof. vm_refl. Qed.
Lemma D_26560 : decode_any W_26560 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26564 : bv 32 := 0xfff60613.
Lemma F_26564 : fetch_word Ubsan.M.loaded_segments (0x306dc : word) = Some W_26564.
Proof. vm_refl. Qed.
Lemma D_26564 : decode_any W_26564 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26568 : bv 32 := 0x00028a63.
Lemma F_26568 : fetch_word Ubsan.M.loaded_segments (0x306e0 : word) = Some W_26568.
Proof. vm_refl. Qed.
Lemma D_26568 : decode_any W_26568 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2656c : bv 32 := 0x00170713.
Lemma F_2656c : fetch_word Ubsan.M.loaded_segments (0x306e4 : word) = Some W_2656c.
Proof. vm_refl. Qed.
Lemma D_2656c : decode_any W_2656c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26570 : bv 32 := 0xfcf81ee3.
Lemma F_26570 : fetch_word Ubsan.M.loaded_segments (0x306e8 : word) = Some W_26570.
Proof. vm_refl. Qed.
Lemma D_26570 : decode_any W_26570 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26574 : bv 32 := 0x0080006f.
Lemma F_26574 : fetch_word Ubsan.M.loaded_segments (0x306ec : word) = Some W_26574.
Proof. vm_refl. Qed.
Lemma D_26574 : decode_any W_26574 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26578 : bv 32 := 0x00050693.
Lemma F_26578 : fetch_word Ubsan.M.loaded_segments (0x306f0 : word) = Some W_26578.
Proof. vm_refl. Qed.
Lemma D_26578 : decode_any W_26578 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2657c : bv 32 := 0x0036f793.
Lemma F_2657c : fetch_word Ubsan.M.loaded_segments (0x306f4 : word) = Some W_2657c.
Proof. vm_refl. Qed.
Lemma D_2657c : decode_any W_2657c = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26580 : bv 32 := 0x0c078a63.
Lemma F_26580 : fetch_word Ubsan.M.loaded_segments (0x306f8 : word) = Some W_26580.
Proof. vm_refl. Qed.
Lemma D_26580 : decode_any W_26580 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26584 : bv 32 := 0x02000713.
Lemma F_26584 : fetch_word Ubsan.M.loaded_segments (0x306fc : word) = Some W_26584.
Proof. vm_refl. Qed.
Lemma D_26584 : decode_any W_26584 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26588 : bv 32 := 0x02e67063.
Lemma F_26588 : fetch_word Ubsan.M.loaded_segments (0x30700 : word) = Some W_26588.
Proof. vm_refl. Qed.
Lemma D_26588 : decode_any W_26588 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2658c : bv 32 := 0x01000713.
Lemma F_2658c : fetch_word Ubsan.M.loaded_segments (0x30704 : word) = Some W_2658c.
Proof. vm_refl. Qed.
Lemma D_2658c : decode_any W_2658c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26590 : bv 32 := 0x24e67863.
Lemma F_26590 : fetch_word Ubsan.M.loaded_segments (0x30708 : word) = Some W_26590.
Proof. vm_refl. Qed.
Lemma D_26590 : decode_any W_26590 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26594 : bv 32 := 0x00867713.
Lemma F_26594 : fetch_word Ubsan.M.loaded_segments (0x3070c : word) = Some W_26594.
Proof. vm_refl. Qed.
Lemma D_26594 : decode_any W_26594 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26598 : bv 32 := 0x2c071e63.
Lemma F_26598 : fetch_word Ubsan.M.loaded_segments (0x30710 : word) = Some W_26598.
Proof. vm_refl. Qed.
Lemma D_26598 : decode_any W_26598 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2659c : bv 32 := 0x00467713.
Lemma F_2659c : fetch_word Ubsan.M.loaded_segments (0x30714 : word) = Some W_2659c.
Proof. vm_refl. Qed.
Lemma D_2659c : decode_any W_2659c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265a0 : bv 32 := 0x32071463.
Lemma F_265a0 : fetch_word Ubsan.M.loaded_segments (0x30718 : word) = Some W_265a0.
Proof. vm_refl. Qed.
Lemma D_265a0 : decode_any W_265a0 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265a4 : bv 32 := 0x3500006f.
Lemma F_265a4 : fetch_word Ubsan.M.loaded_segments (0x3071c : word) = Some W_265a4.
Proof. vm_refl. Qed.
Lemma D_265a4 : decode_any W_265a4 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265a8 : bv 32 := 0x0005a703.
Lemma F_265a8 : fetch_word Ubsan.M.loaded_segments (0x30720 : word) = Some W_265a8.
Proof. vm_refl. Qed.
Lemma D_265a8 : decode_any W_265a8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265ac : bv 32 := 0x00300813.
Lemma F_265ac : fetch_word Ubsan.M.loaded_segments (0x30724 : word) = Some W_265ac.
Proof. vm_refl. Qed.
Lemma D_265ac : decode_any W_265ac = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265b0 : bv 32 := 0x11078e63.
Lemma F_265b0 : fetch_word Ubsan.M.loaded_segments (0x30728 : word) = Some W_265b0.
Proof. vm_refl. Qed.
Lemma D_265b0 : decode_any W_265b0 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265b4 : bv 32 := 0x00200813.
Lemma F_265b4 : fetch_word Ubsan.M.loaded_segments (0x3072c : word) = Some W_265b4.
Proof. vm_refl. Qed.
Lemma D_265b4 : decode_any W_265b4 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265b8 : bv 32 := 0x19079c63.
Lemma F_265b8 : fetch_word Ubsan.M.loaded_segments (0x30730 : word) = Some W_265b8.
Proof. vm_refl. Qed.
Lemma D_265b8 : decode_any W_265b8 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265bc : bv 32 := 0x00875793.
Lemma F_265bc : fetch_word Ubsan.M.loaded_segments (0x30734 : word) = Some W_265bc.
Proof. vm_refl. Qed.
Lemma D_265bc : decode_any W_265bc = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265c0 : bv 32 := 0xffe60613.
Lemma F_265c0 : fetch_word Ubsan.M.loaded_segments (0x30738 : word) = Some W_265c0.
Proof. vm_refl. Qed.
Lemma D_265c0 : decode_any W_265c0 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265c4 : bv 32 := 0x00e68023.
Lemma F_265c4 : fetch_word Ubsan.M.loaded_segments (0x3073c : word) = Some W_265c4.
Proof. vm_refl. Qed.
Lemma D_265c4 : decode_any W_265c4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265c8 : bv 32 := 0x00f680a3.
Lemma F_265c8 : fetch_word Ubsan.M.loaded_segments (0x30740 : word) = Some W_265c8.
Proof. vm_refl. Qed.
Lemma D_265c8 : decode_any W_265c8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265cc : bv 32 := 0x00268693.
Lemma F_265cc : fetch_word Ubsan.M.loaded_segments (0x30744 : word) = Some W_265cc.
Proof. vm_refl. Qed.
Lemma D_265cc : decode_any W_265cc = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265d0 : bv 32 := 0x01058593.
Lemma F_265d0 : fetch_word Ubsan.M.loaded_segments (0x30748 : word) = Some W_265d0.
Proof. vm_refl. Qed.
Lemma D_265d0 : decode_any W_265d0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265d4 : bv 32 := 0x01100793.
Lemma F_265d4 : fetch_word Ubsan.M.loaded_segments (0x3074c : word) = Some W_265d4.
Proof. vm_refl. Qed.
Lemma D_265d4 : decode_any W_265d4 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265d8 : bv 32 := 0x0107581b.
Lemma F_265d8 : fetch_word Ubsan.M.loaded_segments (0x30750 : word) = Some W_265d8.
Proof. vm_refl. Qed.
Lemma D_265d8 : decode_any W_265d8 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265dc : bv 32 := 0xff45a883.
Lemma F_265dc : fetch_word Ubsan.M.loaded_segments (0x30754 : word) = Some W_265dc.
Proof. vm_refl. Qed.
Lemma D_265dc : decode_any W_265dc = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265e0 : bv 32 := 0xff85a283.
Lemma F_265e0 : fetch_word Ubsan.M.loaded_segments (0x30758 : word) = Some W_265e0.
Proof. vm_refl. Qed.
Lemma D_265e0 : decode_any W_265e0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265e4 : bv 32 := 0xffc5a303.
Lemma F_265e4 : fetch_word Ubsan.M.loaded_segments (0x3075c : word) = Some W_265e4.
Proof. vm_refl. Qed.
Lemma D_265e4 : decode_any W_265e4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265e8 : bv 32 := 0x0005a703.
Lemma F_265e8 : fetch_word Ubsan.M.loaded_segments (0x30760 : word) = Some W_265e8.
Proof. vm_refl. Qed.
Lemma D_265e8 : decode_any W_265e8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265ec : bv 32 := 0x01089393.
Lemma F_265ec : fetch_word Ubsan.M.loaded_segments (0x30764 : word) = Some W_265ec.
Proof. vm_refl. Qed.
Lemma D_265ec : decode_any W_265ec = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265f0 : bv 32 := 0x0108d89b.
Lemma F_265f0 : fetch_word Ubsan.M.loaded_segments (0x30768 : word) = Some W_265f0.
Proof. vm_refl. Qed.
Lemma D_265f0 : decode_any W_265f0 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265f4 : bv 32 := 0x0103e833.
Lemma F_265f4 : fetch_word Ubsan.M.loaded_segments (0x3076c : word) = Some W_265f4.
Proof. vm_refl. Qed.
Lemma D_265f4 : decode_any W_265f4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265f8 : bv 32 := 0x01029393.
Lemma F_265f8 : fetch_word Ubsan.M.loaded_segments (0x30770 : word) = Some W_265f8.
Proof. vm_refl. Qed.
Lemma D_265f8 : decode_any W_265f8 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265fc : bv 32 := 0x0102d29b.
Lemma F_265fc : fetch_word Ubsan.M.loaded_segments (0x30774 : word) = Some W_265fc.
Proof. vm_refl. Qed.
Lemma D_265fc : decode_any W_265fc = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26600 : bv 32 := 0x0113e8b3.
Lemma F_26600 : fetch_word Ubsan.M.loaded_segments (0x30778 : word) = Some W_26600.
Proof. vm_refl. Qed.
Lemma D_26600 : decode_any W_26600 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26604 : bv 32 := 0x01031393.
Lemma F_26604 : fetch_word Ubsan.M.loaded_segments (0x3077c : word) = Some W_26604.
Proof. vm_refl. Qed.
Lemma D_26604 : decode_any W_26604 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26608 : bv 32 := 0x0103531b.
Lemma F_26608 : fetch_word Ubsan.M.loaded_segments (0x30780 : word) = Some W_26608.
Proof. vm_refl. Qed.
Lemma D_26608 : decode_any W_26608 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2660c : bv 32 := 0x0053e2b3.
Lemma F_2660c : fetch_word Ubsan.M.loaded_segments (0x30784 : word) = Some W_2660c.
Proof. vm_refl. Qed.
Lemma D_2660c : decode_any W_2660c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26610 : bv 32 := 0x01071393.
Lemma F_26610 : fetch_word Ubsan.M.loaded_segments (0x30788 : word) = Some W_26610.
Proof. vm_refl. Qed.
Lemma D_26610 : decode_any W_26610 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26614 : bv 32 := 0x0063e333.
Lemma F_26614 : fetch_word Ubsan.M.loaded_segments (0x3078c : word) = Some W_26614.
Proof. vm_refl. Qed.
Lemma D_26614 : decode_any W_26614 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26618 : bv 32 := 0xff060613.
Lemma F_26618 : fetch_word Ubsan.M.loaded_segments (0x30790 : word) = Some W_26618.
Proof. vm_refl. Qed.
Lemma D_26618 : decode_any W_26618 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2661c : bv 32 := 0x0106a023.
Lemma F_2661c : fetch_word Ubsan.M.loaded_segments (0x30794 : word) = Some W_2661c.
Proof. vm_refl. Qed.
Lemma D_2661c : decode_any W_2661c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26620 : bv 32 := 0x0116a223.
Lemma F_26620 : fetch_word Ubsan.M.loaded_segments (0x30798 : word) = Some W_26620.
Proof. vm_refl. Qed.
Lemma D_26620 : decode_any W_26620 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26624 : bv 32 := 0x0056a423.
Lemma F_26624 : fetch_word Ubsan.M.loaded_segments (0x3079c : word) = Some W_26624.
Proof. vm_refl. Qed.
Lemma D_26624 : decode_any W_26624 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26628 : bv 32 := 0x0066a623.
Lemma F_26628 : fetch_word Ubsan.M.loaded_segments (0x307a0 : word) = Some W_26628.
Proof. vm_refl. Qed.
Lemma D_26628 : decode_any W_26628 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2662c : bv 32 := 0x01068693.
Lemma F_2662c : fetch_word Ubsan.M.loaded_segments (0x307a4 : word) = Some W_2662c.
Proof. vm_refl. Qed.
Lemma D_2662c : decode_any W_2662c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26630 : bv 32 := 0x01058593.
Lemma F_26630 : fetch_word Ubsan.M.loaded_segments (0x307a8 : word) = Some W_26630.
Proof. vm_refl. Qed.
Lemma D_26630 : decode_any W_26630 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26634 : bv 32 := 0xfac7e2e3.
Lemma F_26634 : fetch_word Ubsan.M.loaded_segments (0x307ac : word) = Some W_26634.
Proof. vm_refl. Qed.
Lemma D_26634 : decode_any W_26634 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26638 : bv 32 := 0xff258593.
Lemma F_26638 : fetch_word Ubsan.M.loaded_segments (0x307b0 : word) = Some W_26638.
Proof. vm_refl. Qed.
Lemma D_26638 : decode_any W_26638 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2663c : bv 32 := 0x01000713.
Lemma F_2663c : fetch_word Ubsan.M.loaded_segments (0x307b4 : word) = Some W_2663c.
Proof. vm_refl. Qed.
Lemma D_2663c : decode_any W_2663c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26640 : bv 32 := 0xf4e66ae3.
Lemma F_26640 : fetch_word Ubsan.M.loaded_segments (0x307b8 : word) = Some W_26640.
Proof. vm_refl. Qed.
Lemma D_26640 : decode_any W_26640 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26644 : bv 32 := 0x19c0006f.
Lemma F_26644 : fetch_word Ubsan.M.loaded_segments (0x307bc : word) = Some W_26644.
Proof. vm_refl. Qed.
Lemma D_26644 : decode_any W_26644 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26648 : bv 32 := 0x00050693.
Lemma F_26648 : fetch_word Ubsan.M.loaded_segments (0x307c0 : word) = Some W_26648.
Proof. vm_refl. Qed.
Lemma D_26648 : decode_any W_26648 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2664c : bv 32 := 0x00357793.
Lemma F_2664c : fetch_word Ubsan.M.loaded_segments (0x307c4 : word) = Some W_2664c.
Proof. vm_refl. Qed.
Lemma D_2664c : decode_any W_2664c = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26650 : bv 32 := 0xf2079ae3.
Lemma F_26650 : fetch_word Ubsan.M.loaded_segments (0x307c8 : word) = Some W_26650.
Proof. vm_refl. Qed.
Lemma D_26650 : decode_any W_26650 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26654 : bv 32 := 0x01000713.
Lemma F_26654 : fetch_word Ubsan.M.loaded_segments (0x307cc : word) = Some W_26654.
Proof. vm_refl. Qed.
Lemma D_26654 : decode_any W_26654 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26658 : bv 32 := 0x02e66c63.
Lemma F_26658 : fetch_word Ubsan.M.loaded_segments (0x307d0 : word) = Some W_26658.
Proof. vm_refl. Qed.
Lemma D_26658 : decode_any W_26658 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2665c : bv 32 := 0x00f00713.
Lemma F_2665c : fetch_word Ubsan.M.loaded_segments (0x307d4 : word) = Some W_2665c.
Proof. vm_refl. Qed.
Lemma D_2665c : decode_any W_2665c = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26660 : bv 32 := 0x0005a783.
Lemma F_26660 : fetch_word Ubsan.M.loaded_segments (0x307d8 : word) = Some W_26660.
Proof. vm_refl. Qed.
Lemma D_26660 : decode_any W_26660 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26664 : bv 32 := 0x0045a803.
Lemma F_26664 : fetch_word Ubsan.M.loaded_segments (0x307dc : word) = Some W_26664.
Proof. vm_refl. Qed.
Lemma D_26664 : decode_any W_26664 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26668 : bv 32 := 0x0085a883.
Lemma F_26668 : fetch_word Ubsan.M.loaded_segments (0x307e0 : word) = Some W_26668.
Proof. vm_refl. Qed.
Lemma D_26668 : decode_any W_26668 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2666c : bv 32 := 0x00c5a283.
Lemma F_2666c : fetch_word Ubsan.M.loaded_segments (0x307e4 : word) = Some W_2666c.
Proof. vm_refl. Qed.
Lemma D_2666c : decode_any W_2666c = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26670 : bv 32 := 0x01058593.
Lemma F_26670 : fetch_word Ubsan.M.loaded_segments (0x307e8 : word) = Some W_26670.
Proof. vm_refl. Qed.
Lemma D_26670 : decode_any W_26670 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26674 : bv 32 := 0xff060613.
Lemma F_26674 : fetch_word Ubsan.M.loaded_segments (0x307ec : word) = Some W_26674.
Proof. vm_refl. Qed.
Lemma D_26674 : decode_any W_26674 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26678 : bv 32 := 0x00f6a023.
Lemma F_26678 : fetch_word Ubsan.M.loaded_segments (0x307f0 : word) = Some W_26678.
Proof. vm_refl. Qed.
Lemma D_26678 : decode_any W_26678 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2667c : bv 32 := 0x0106a223.
Lemma F_2667c : fetch_word Ubsan.M.loaded_segments (0x307f4 : word) = Some W_2667c.
Proof. vm_refl. Qed.
Lemma D_2667c : decode_any W_2667c = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26680 : bv 32 := 0x0116a423.
Lemma F_26680 : fetch_word Ubsan.M.loaded_segments (0x307f8 : word) = Some W_26680.
Proof. vm_refl. Qed.
Lemma D_26680 : decode_any W_26680 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26684 : bv 32 := 0x0056a623.
Lemma F_26684 : fetch_word Ubsan.M.loaded_segments (0x307fc : word) = Some W_26684.
Proof. vm_refl. Qed.
Lemma D_26684 : decode_any W_26684 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26688 : bv 32 := 0x01068693.
Lemma F_26688 : fetch_word Ubsan.M.loaded_segments (0x30800 : word) = Some W_26688.
Proof. vm_refl. Qed.
Lemma D_26688 : decode_any W_26688 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2668c : bv 32 := 0xfcc76ae3.
Lemma F_2668c : fetch_word Ubsan.M.loaded_segments (0x30804 : word) = Some W_2668c.
Proof. vm_refl. Qed.
Lemma D_2668c : decode_any W_2668c = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26690 : bv 32 := 0x00800713.
Lemma F_26690 : fetch_word Ubsan.M.loaded_segments (0x30808 : word) = Some W_26690.
Proof. vm_refl. Qed.
Lemma D_26690 : decode_any W_26690 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26694 : bv 32 := 0x00e66e63.
Lemma F_26694 : fetch_word Ubsan.M.loaded_segments (0x3080c : word) = Some W_26694.
Proof. vm_refl. Qed.
Lemma D_26694 : decode_any W_26694 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26698 : bv 32 := 0x0005a703.
Lemma F_26698 : fetch_word Ubsan.M.loaded_segments (0x30810 : word) = Some W_26698.
Proof. vm_refl. Qed.
Lemma D_26698 : decode_any W_26698 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2669c : bv 32 := 0x0045a783.
Lemma F_2669c : fetch_word Ubsan.M.loaded_segments (0x30814 : word) = Some W_2669c.
Proof. vm_refl. Qed.
Lemma D_2669c : decode_any W_2669c = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266a0 : bv 32 := 0x00e6a023.
Lemma F_266a0 : fetch_word Ubsan.M.loaded_segments (0x30818 : word) = Some W_266a0.
Proof. vm_refl. Qed.
Lemma D_266a0 : decode_any W_266a0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266a4 : bv 32 := 0x00f6a223.
Lemma F_266a4 : fetch_word Ubsan.M.loaded_segments (0x3081c : word) = Some W_266a4.
Proof. vm_refl. Qed.
Lemma D_266a4 : decode_any W_266a4 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266a8 : bv 32 := 0x00868693.
Lemma F_266a8 : fetch_word Ubsan.M.loaded_segments (0x30820 : word) = Some W_266a8.
Proof. vm_refl. Qed.
Lemma D_266a8 : decode_any W_266a8 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266ac : bv 32 := 0x00858593.
Lemma F_266ac : fetch_word Ubsan.M.loaded_segments (0x30824 : word) = Some W_266ac.
Proof. vm_refl. Qed.
Lemma D_266ac : decode_any W_266ac = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266b0 : bv 32 := 0x00467713.
Lemma F_266b0 : fetch_word Ubsan.M.loaded_segments (0x30828 : word) = Some W_266b0.
Proof. vm_refl. Qed.
Lemma D_266b0 : decode_any W_266b0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266b4 : bv 32 := 0x24070063.
Lemma F_266b4 : fetch_word Ubsan.M.loaded_segments (0x3082c : word) = Some W_266b4.
Proof. vm_refl. Qed.
Lemma D_266b4 : decode_any W_266b4 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266b8 : bv 32 := 0x0005a703.
Lemma F_266b8 : fetch_word Ubsan.M.loaded_segments (0x30830 : word) = Some W_266b8.
Proof. vm_refl. Qed.
Lemma D_266b8 : decode_any W_266b8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266bc : bv 32 := 0x00458593.
Lemma F_266bc : fetch_word Ubsan.M.loaded_segments (0x30834 : word) = Some W_266bc.
Proof. vm_refl. Qed.
Lemma D_266bc : decode_any W_266bc = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266c0 : bv 32 := 0x00e6a023.
Lemma F_266c0 : fetch_word Ubsan.M.loaded_segments (0x30838 : word) = Some W_266c0.
Proof. vm_refl. Qed.
Lemma D_266c0 : decode_any W_266c0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266c4 : bv 32 := 0x00468693.
Lemma F_266c4 : fetch_word Ubsan.M.loaded_segments (0x3083c : word) = Some W_266c4.
Proof. vm_refl. Qed.
Lemma D_266c4 : decode_any W_266c4 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266c8 : bv 32 := 0x22c0006f.
Lemma F_266c8 : fetch_word Ubsan.M.loaded_segments (0x30840 : word) = Some W_266c8.
Proof. vm_refl. Qed.
Lemma D_266c8 : decode_any W_266c8 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266cc : bv 32 := 0x00e68023.
Lemma F_266cc : fetch_word Ubsan.M.loaded_segments (0x30844 : word) = Some W_266cc.
Proof. vm_refl. Qed.
Lemma D_266cc : decode_any W_266cc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266d0 : bv 32 := 0x00168693.
Lemma F_266d0 : fetch_word Ubsan.M.loaded_segments (0x30848 : word) = Some W_266d0.
Proof. vm_refl. Qed.
Lemma D_266d0 : decode_any W_266d0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266d4 : bv 32 := 0xfff60613.
Lemma F_266d4 : fetch_word Ubsan.M.loaded_segments (0x3084c : word) = Some W_266d4.
Proof. vm_refl. Qed.
Lemma D_266d4 : decode_any W_266d4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266d8 : bv 32 := 0x01058593.
Lemma F_266d8 : fetch_word Ubsan.M.loaded_segments (0x30850 : word) = Some W_266d8.
Proof. vm_refl. Qed.
Lemma D_266d8 : decode_any W_266d8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266dc : bv 32 := 0x01200793.
Lemma F_266dc : fetch_word Ubsan.M.loaded_segments (0x30854 : word) = Some W_266dc.
Proof. vm_refl. Qed.
Lemma D_266dc : decode_any W_266dc = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266e0 : bv 32 := 0x0087581b.
Lemma F_266e0 : fetch_word Ubsan.M.loaded_segments (0x30858 : word) = Some W_266e0.
Proof. vm_refl. Qed.
Lemma D_266e0 : decode_any W_266e0 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266e4 : bv 32 := 0xff45a883.
Lemma F_266e4 : fetch_word Ubsan.M.loaded_segments (0x3085c : word) = Some W_266e4.
Proof. vm_refl. Qed.
Lemma D_266e4 : decode_any W_266e4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266e8 : bv 32 := 0xff85a283.
Lemma F_266e8 : fetch_word Ubsan.M.loaded_segments (0x30860 : word) = Some W_266e8.
Proof. vm_refl. Qed.
Lemma D_266e8 : decode_any W_266e8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266ec : bv 32 := 0xffc5a303.
Lemma F_266ec : fetch_word Ubsan.M.loaded_segments (0x30864 : word) = Some W_266ec.
Proof. vm_refl. Qed.
Lemma D_266ec : decode_any W_266ec = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266f0 : bv 32 := 0x0005a703.
Lemma F_266f0 : fetch_word Ubsan.M.loaded_segments (0x30868 : word) = Some W_266f0.
Proof. vm_refl. Qed.
Lemma D_266f0 : decode_any W_266f0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266f4 : bv 32 := 0x01889393.
Lemma F_266f4 : fetch_word Ubsan.M.loaded_segments (0x3086c : word) = Some W_266f4.
Proof. vm_refl. Qed.
Lemma D_266f4 : decode_any W_266f4 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266f8 : bv 32 := 0x0088d89b.
Lemma F_266f8 : fetch_word Ubsan.M.loaded_segments (0x30870 : word) = Some W_266f8.
Proof. vm_refl. Qed.
Lemma D_266f8 : decode_any W_266f8 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_266fc : bv 32 := 0x0103e833.
Lemma F_266fc : fetch_word Ubsan.M.loaded_segments (0x30874 : word) = Some W_266fc.
Proof. vm_refl. Qed.
Lemma D_266fc : decode_any W_266fc = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26700 : bv 32 := 0x01829393.
Lemma F_26700 : fetch_word Ubsan.M.loaded_segments (0x30878 : word) = Some W_26700.
Proof. vm_refl. Qed.
Lemma D_26700 : decode_any W_26700 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26704 : bv 32 := 0x0082d29b.
Lemma F_26704 : fetch_word Ubsan.M.loaded_segments (0x3087c : word) = Some W_26704.
Proof. vm_refl. Qed.
Lemma D_26704 : decode_any W_26704 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26708 : bv 32 := 0x0113e8b3.
Lemma F_26708 : fetch_word Ubsan.M.loaded_segments (0x30880 : word) = Some W_26708.
Proof. vm_refl. Qed.
Lemma D_26708 : decode_any W_26708 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2670c : bv 32 := 0x01831393.
Lemma F_2670c : fetch_word Ubsan.M.loaded_segments (0x30884 : word) = Some W_2670c.
Proof. vm_refl. Qed.
Lemma D_2670c : decode_any W_2670c = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26710 : bv 32 := 0x0083531b.
Lemma F_26710 : fetch_word Ubsan.M.loaded_segments (0x30888 : word) = Some W_26710.
Proof. vm_refl. Qed.
Lemma D_26710 : decode_any W_26710 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26714 : bv 32 := 0x0053e2b3.
Lemma F_26714 : fetch_word Ubsan.M.loaded_segments (0x3088c : word) = Some W_26714.
Proof. vm_refl. Qed.
Lemma D_26714 : decode_any W_26714 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26718 : bv 32 := 0x01871393.
Lemma F_26718 : fetch_word Ubsan.M.loaded_segments (0x30890 : word) = Some W_26718.
Proof. vm_refl. Qed.
Lemma D_26718 : decode_any W_26718 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2671c : bv 32 := 0x0063e333.
Lemma F_2671c : fetch_word Ubsan.M.loaded_segments (0x30894 : word) = Some W_2671c.
Proof. vm_refl. Qed.
Lemma D_2671c : decode_any W_2671c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26720 : bv 32 := 0xff060613.
Lemma F_26720 : fetch_word Ubsan.M.loaded_segments (0x30898 : word) = Some W_26720.
Proof. vm_refl. Qed.
Lemma D_26720 : decode_any W_26720 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26724 : bv 32 := 0x0106a023.
Lemma F_26724 : fetch_word Ubsan.M.loaded_segments (0x3089c : word) = Some W_26724.
Proof. vm_refl. Qed.
Lemma D_26724 : decode_any W_26724 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.
