(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_160b0 : bv 32 := 0x1c050463.
Lemma F_160b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16150 : word) = Some W_160b0.
Proof. vm_refl. Qed.
Lemma D_160b0 : decode_any W_160b0 = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_160b4 : bv 32 := 0xfd010113.
Lemma F_160b4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16154 : word) = Some W_160b4.
Proof. vm_refl. Qed.
Lemma D_160b4 : decode_any W_160b4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_160b8 : bv 32 := 0x02113423.
Lemma F_160b8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16158 : word) = Some W_160b8.
Proof. vm_refl. Qed.
Lemma D_160b8 : decode_any W_160b8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_160bc : bv 32 := 0x02813023.
Lemma F_160bc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1615c : word) = Some W_160bc.
Proof. vm_refl. Qed.
Lemma D_160bc : decode_any W_160bc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_160c0 : bv 32 := 0x00913c23.
Lemma F_160c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16160 : word) = Some W_160c0.
Proof. vm_refl. Qed.
Lemma D_160c0 : decode_any W_160c0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_160c4 : bv 32 := 0x01213823.
Lemma F_160c4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16164 : word) = Some W_160c4.
Proof. vm_refl. Qed.
Lemma D_160c4 : decode_any W_160c4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_160c8 : bv 32 := 0x01313423.
Lemma F_160c8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16168 : word) = Some W_160c8.
Proof. vm_refl. Qed.
Lemma D_160c8 : decode_any W_160c8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_160cc : bv 32 := 0x00050493.
Lemma F_160cc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1616c : word) = Some W_160cc.
Proof. vm_refl. Qed.
Lemma D_160cc : decode_any W_160cc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_160d0 : bv 32 := 0x1ac000ef.
Lemma F_160d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16170 : word) = Some W_160d0.
Proof. vm_refl. Qed.
Lemma D_160d0 : decode_any W_160d0 = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

Definition W_160d4 : bv 32 := 0x02053583.
Lemma F_160d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16174 : word) = Some W_160d4.
Proof. vm_refl. Qed.
Lemma D_160d4 : decode_any W_160d4 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_160d8 : bv 32 := 0xffd4c683.
Lemma F_160d8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16178 : word) = Some W_160d8.
Proof. vm_refl. Qed.
Lemma D_160d8 : decode_any W_160d8 = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_160dc : bv 32 := 0x00c5d613.
Lemma F_160dc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1617c : word) = Some W_160dc.
Proof. vm_refl. Qed.
Lemma D_160dc : decode_any W_160dc = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_160e0 : bv 32 := 0x01f6f413.
Lemma F_160e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16180 : word) = Some W_160e0.
Proof. vm_refl. Qed.
Lemma D_160e0 : decode_any W_160e0 = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_160e4 : bv 32 := 0x00060e63.
Lemma F_160e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16184 : word) = Some W_160e4.
Proof. vm_refl. Qed.
Lemma D_160e4 : decode_any W_160e4 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_160e8 : bv 32 := 0x01f5f613.
Lemma F_160e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16188 : word) = Some W_160e8.
Proof. vm_refl. Qed.
Lemma D_160e8 : decode_any W_160e8 = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_160ec : bv 32 := 0x00061a63.
Lemma F_160ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1618c : word) = Some W_160ec.
Proof. vm_refl. Qed.
Lemma D_160ec : decode_any W_160ec = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_160f0 : bv 32 := 0xfffff637.
Lemma F_160f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16190 : word) = Some W_160f0.
Proof. vm_refl. Qed.
Lemma D_160f0 : decode_any W_160f0 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_160f4 : bv 32 := 0x00c5f633.
Lemma F_160f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16194 : word) = Some W_160f4.
Proof. vm_refl. Qed.
Lemma D_160f4 : decode_any W_160f4 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_160f8 : bv 32 := 0xff060613.
Lemma F_160f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16198 : word) = Some W_160f8.
Proof. vm_refl. Qed.
Lemma D_160f8 : decode_any W_160f8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_160fc : bv 32 := 0x0200006f.
Lemma F_160fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1619c : word) = Some W_160fc.
Proof. vm_refl. Qed.
Lemma D_160fc : decode_any W_160fc = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16100 : bv 32 := 0x0055d613.
Lemma F_16100 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161a0 : word) = Some W_16100.
Proof. vm_refl. Qed.
Lemma D_16100 : decode_any W_16100 = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_16104 : bv 32 := 0xffffc717.
Lemma F_16104 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161a4 : word) = Some W_16104.
Proof. vm_refl. Qed.
Lemma D_16104 : decode_any W_16104 = Some (Auipc 14 1048572, 4%Z).
Proof. vm_refl. Qed.

Definition W_16108 : bv 32 := 0x07e67613.
Lemma F_16108 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161a8 : word) = Some W_16108.
Proof. vm_refl. Qed.
Lemma D_16108 : decode_any W_16108 = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_1610c : bv 32 := 0x90870713.
Lemma F_1610c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161ac : word) = Some W_1610c.
Proof. vm_refl. Qed.
Lemma D_1610c : decode_any W_1610c = Some (OpImm ALU_ADD 14 14 2312, 4%Z).
Proof. vm_refl. Qed.

Definition W_16110 : bv 32 := 0x00c70633.
Lemma F_16110 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161b0 : word) = Some W_16110.
Proof. vm_refl. Qed.
Lemma D_16110 : decode_any W_16110 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16114 : bv 32 := 0x00065603.
Lemma F_16114 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161b4 : word) = Some W_16114.
Proof. vm_refl. Qed.
Lemma D_16114 : decode_any W_16114 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16118 : bv 32 := 0x00461613.
Lemma F_16118 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161b8 : word) = Some W_16118.
Proof. vm_refl. Qed.
Lemma D_16118 : decode_any W_16118 = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1611c : bv 32 := 0x01053703.
Lemma F_1611c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161bc : word) = Some W_1611c.
Proof. vm_refl. Qed.
Lemma D_1611c : decode_any W_1611c = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16120 : bv 32 := 0x028607b3.
Lemma F_16120 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161c0 : word) = Some W_16120.
Proof. vm_refl. Qed.
Lemma D_16120 : decode_any W_16120 = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16124 : bv 32 := 0x0a000813.
Lemma F_16124 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161c4 : word) = Some W_16124.
Proof. vm_refl. Qed.
Lemma D_16124 : decode_any W_16124 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_16128 : bv 32 := 0x00c70633.
Lemma F_16128 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161c8 : word) = Some W_16128.
Proof. vm_refl. Qed.
Lemma D_16128 : decode_any W_16128 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1612c : bv 32 := 0x00f607b3.
Lemma F_1612c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161cc : word) = Some W_1612c.
Proof. vm_refl. Qed.
Lemma D_1612c : decode_any W_1612c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_16130 : bv 32 := 0x00c78613.
Lemma F_16130 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161d0 : word) = Some W_16130.
Proof. vm_refl. Qed.
Lemma D_16130 : decode_any W_16130 = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16134 : bv 32 := 0x0056d713.
Lemma F_16134 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161d4 : word) = Some W_16134.
Proof. vm_refl. Qed.
Lemma D_16134 : decode_any W_16134 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_16138 : bv 32 := 0x0306e663.
Lemma F_16138 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161d8 : word) = Some W_16138.
Proof. vm_refl. Qed.
Lemma D_16138 : decode_any W_16138 = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1613c : bv 32 := 0x00500693.
Lemma F_1613c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161dc : word) = Some W_1613c.
Proof. vm_refl. Qed.
Lemma D_1613c : decode_any W_1613c = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_16140 : bv 32 := 0x00d70463.
Lemma F_16140 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161e0 : word) = Some W_16140.
Proof. vm_refl. Qed.
Lemma D_16140 : decode_any W_16140 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16148 : bv 32 := 0x0087e703.
Lemma F_16148 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161e8 : word) = Some W_16148.
Proof. vm_refl. Qed.
Lemma D_16148 : decode_any W_16148 = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1614c : bv 32 := 0x00400693.
Lemma F_1614c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161ec : word) = Some W_1614c.
Proof. vm_refl. Qed.
Lemma D_1614c : decode_any W_1614c = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_16150 : bv 32 := 0x00e6e463.
Lemma F_16150 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161f0 : word) = Some W_16150.
Proof. vm_refl. Qed.
Lemma D_16150 : decode_any W_16150 = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16158 : bv 32 := 0x0077c683.
Lemma F_16158 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161f8 : word) = Some W_16158.
Proof. vm_refl. Qed.
Lemma D_16158 : decode_any W_16158 = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1615c : bv 32 := 0x00068463.
Lemma F_1615c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x161fc : word) = Some W_1615c.
Proof. vm_refl. Qed.
Lemma D_1615c : decode_any W_1615c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16164 : bv 32 := 0x409606b3.
Lemma F_16164 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16204 : word) = Some W_16164.
Proof. vm_refl. Qed.
Lemma D_16164 : decode_any W_16164 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_16168 : bv 32 := 0x00e6f463.
Lemma F_16168 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16208 : word) = Some W_16168.
Proof. vm_refl. Qed.
Lemma D_16168 : decode_any W_16168 = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16170 : bv 32 := 0x40e606b3.
Lemma F_16170 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16210 : word) = Some W_16170.
Proof. vm_refl. Qed.
Lemma D_16170 : decode_any W_16170 = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_16174 : bv 32 := 0x0006c683.
Lemma F_16174 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16214 : word) = Some W_16174.
Proof. vm_refl. Qed.
Lemma D_16174 : decode_any W_16174 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16178 : bv 32 := 0x00068463.
Lemma F_16178 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16218 : word) = Some W_16178.
Proof. vm_refl. Qed.
Lemma D_16178 : decode_any W_16178 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16180 : bv 32 := 0x00064603.
Lemma F_16180 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16220 : word) = Some W_16180.
Proof. vm_refl. Qed.
Lemma D_16180 : decode_any W_16180 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16184 : bv 32 := 0x00060463.
Lemma F_16184 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16224 : word) = Some W_16184.
Proof. vm_refl. Qed.
Lemma D_16184 : decode_any W_16184 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1627c : bv 32 := 0x00f57593.
Lemma F_1627c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1631c : word) = Some W_1627c.
Proof. vm_refl. Qed.
Lemma D_1627c : decode_any W_1627c = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_16280 : bv 32 := 0x00058463.
Lemma F_16280 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16320 : word) = Some W_16280.
Proof. vm_refl. Qed.
Lemma D_16280 : decode_any W_16280 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16288 : bv 32 := 0xffc54603.
Lemma F_16288 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16328 : word) = Some W_16288.
Proof. vm_refl. Qed.
Lemma D_16288 : decode_any W_16288 = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1628c : bv 32 := 0xffd54683.
Lemma F_1628c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1632c : word) = Some W_1628c.
Proof. vm_refl. Qed.
Lemma D_1628c : decode_any W_1628c = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_16290 : bv 32 := 0xffe55583.
Lemma F_16290 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16330 : word) = Some W_16290.
Proof. vm_refl. Qed.
Lemma D_16290 : decode_any W_16290 = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_16294 : bv 32 := 0x00060e63.
Lemma F_16294 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16334 : word) = Some W_16294.
Proof. vm_refl. Qed.
Lemma D_16294 : decode_any W_16294 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_162b0 : bv 32 := 0x00459613.
Lemma F_162b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16350 : word) = Some W_162b0.
Proof. vm_refl. Qed.
Lemma D_162b0 : decode_any W_162b0 = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_162b4 : bv 32 := 0x40c50633.
Lemma F_162b4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16354 : word) = Some W_162b4.
Proof. vm_refl. Qed.
Lemma D_162b4 : decode_any W_162b4 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_162b8 : bv 32 := 0xff063503.
Lemma F_162b8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16358 : word) = Some W_162b8.
Proof. vm_refl. Qed.
Lemma D_162b8 : decode_any W_162b8 = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_162bc : bv 32 := 0x01053703.
Lemma F_162bc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1635c : word) = Some W_162bc.
Proof. vm_refl. Qed.
Lemma D_162bc : decode_any W_162bc = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_162c0 : bv 32 := 0xff060613.
Lemma F_162c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16360 : word) = Some W_162c0.
Proof. vm_refl. Qed.
Lemma D_162c0 : decode_any W_162c0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_162c4 : bv 32 := 0x01f6f693.
Lemma F_162c4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16364 : word) = Some W_162c4.
Proof. vm_refl. Qed.
Lemma D_162c4 : decode_any W_162c4 = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_162c8 : bv 32 := 0x00c70463.
Lemma F_162c8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16368 : word) = Some W_162c8.
Proof. vm_refl. Qed.
Lemma D_162c8 : decode_any W_162c8 = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_162d0 : bv 32 := 0x02053603.
Lemma F_162d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16370 : word) = Some W_162d0.
Proof. vm_refl. Qed.
Lemma D_162d0 : decode_any W_162d0 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_162d4 : bv 32 := 0x01f67713.
Lemma F_162d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16374 : word) = Some W_162d4.
Proof. vm_refl. Qed.
Lemma D_162d4 : decode_any W_162d4 = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_162d8 : bv 32 := 0x00d77463.
Lemma F_162d8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16378 : word) = Some W_162d8.
Proof. vm_refl. Qed.
Lemma D_162d8 : decode_any W_162d8 = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_162e0 : bv 32 := 0x01852783.
Lemma F_162e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16380 : word) = Some W_162e0.
Proof. vm_refl. Qed.
Lemma D_162e0 : decode_any W_162e0 = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_162e4 : bv 32 := 0x00100713.
Lemma F_162e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16384 : word) = Some W_162e4.
Proof. vm_refl. Qed.
Lemma D_162e4 : decode_any W_162e4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_162e8 : bv 32 := 0x00d7173b.
Lemma F_162e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16388 : word) = Some W_162e8.
Proof. vm_refl. Qed.
Lemma D_162e8 : decode_any W_162e8 = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_162ec : bv 32 := 0x00e7f7b3.
Lemma F_162ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1638c : word) = Some W_162ec.
Proof. vm_refl. Qed.
Lemma D_162ec : decode_any W_162ec = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_162f0 : bv 32 := 0x00078463.
Lemma F_162f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16390 : word) = Some W_162f0.
Proof. vm_refl. Qed.
Lemma D_162f0 : decode_any W_162f0 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_162f8 : bv 32 := 0x01c52783.
Lemma F_162f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16398 : word) = Some W_162f8.
Proof. vm_refl. Qed.
Lemma D_162f8 : decode_any W_162f8 = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_162fc : bv 32 := 0x00e7f733.
Lemma F_162fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1639c : word) = Some W_162fc.
Proof. vm_refl. Qed.
Lemma D_162fc : decode_any W_162fc = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_16300 : bv 32 := 0x00070463.
Lemma F_16300 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163a0 : word) = Some W_16300.
Proof. vm_refl. Qed.
Lemma D_16300 : decode_any W_16300 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16308 : bv 32 := 0xfffff737.
Lemma F_16308 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163a8 : word) = Some W_16308.
Proof. vm_refl. Qed.
Lemma D_16308 : decode_any W_16308 = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_1630c : bv 32 := 0x0003a797.
Lemma F_1630c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163ac : word) = Some W_1630c.
Proof. vm_refl. Qed.
Lemma D_1630c : decode_any W_1630c = Some (Auipc 15 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_16310 : bv 32 := 0x00e57733.
Lemma F_16310 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163b0 : word) = Some W_16310.
Proof. vm_refl. Qed.
Lemma D_16310 : decode_any W_16310 = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_16314 : bv 32 := 0x00073703.
Lemma F_16314 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163b4 : word) = Some W_16314.
Proof. vm_refl. Qed.
Lemma D_16314 : decode_any W_16314 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16318 : bv 32 := 0xcdc7b783.
Lemma F_16318 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163b8 : word) = Some W_16318.
Proof. vm_refl. Qed.
Lemma D_16318 : decode_any W_16318 = Some (Load SZ8 true 15 15 3292, 4%Z).
Proof. vm_refl. Qed.

Definition W_1631c : bv 32 := 0x00f70463.
Lemma F_1631c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163bc : word) = Some W_1631c.
Proof. vm_refl. Qed.
Lemma D_1631c : decode_any W_1631c = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16324 : bv 32 := 0x03461713.
Lemma F_16324 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163c4 : word) = Some W_16324.
Proof. vm_refl. Qed.
Lemma D_16324 : decode_any W_16324 = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_16328 : bv 32 := 0x03a75713.
Lemma F_16328 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163c8 : word) = Some W_16328.
Proof. vm_refl. Qed.
Lemma D_16328 : decode_any W_16328 = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_1632c : bv 32 := 0x02f00793.
Lemma F_1632c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163cc : word) = Some W_1632c.
Proof. vm_refl. Qed.
Lemma D_1632c : decode_any W_1632c = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_16330 : bv 32 := 0x02e7ea63.
Lemma F_16330 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163d0 : word) = Some W_16330.
Proof. vm_refl. Qed.
Lemma D_16330 : decode_any W_16330 = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_16334 : bv 32 := 0x00171713.
Lemma F_16334 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163d4 : word) = Some W_16334.
Proof. vm_refl. Qed.
Lemma D_16334 : decode_any W_16334 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16338 : bv 32 := 0xffffb797.
Lemma F_16338 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163d8 : word) = Some W_16338.
Proof. vm_refl. Qed.
Lemma D_16338 : decode_any W_16338 = Some (Auipc 15 1048571, 4%Z).
Proof. vm_refl. Qed.

Definition W_1633c : bv 32 := 0x6d478793.
Lemma F_1633c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163dc : word) = Some W_1633c.
Proof. vm_refl. Qed.
Lemma D_1633c : decode_any W_1633c = Some (OpImm ALU_ADD 15 15 1748, 4%Z).
Proof. vm_refl. Qed.

Definition W_16340 : bv 32 := 0x00e78733.
Lemma F_16340 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163e0 : word) = Some W_16340.
Proof. vm_refl. Qed.
Lemma D_16340 : decode_any W_16340 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_16344 : bv 32 := 0x00075703.
Lemma F_16344 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163e4 : word) = Some W_16344.
Proof. vm_refl. Qed.
Lemma D_16344 : decode_any W_16344 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16348 : bv 32 := 0x02d707b3.
Lemma F_16348 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163e8 : word) = Some W_16348.
Proof. vm_refl. Qed.
Lemma D_16348 : decode_any W_16348 = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1634c : bv 32 := 0x00f5f463.
Lemma F_1634c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163ec : word) = Some W_1634c.
Proof. vm_refl. Qed.
Lemma D_1634c : decode_any W_1634c = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16354 : bv 32 := 0x00168693.
Lemma F_16354 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163f4 : word) = Some W_16354.
Proof. vm_refl. Qed.
Lemma D_16354 : decode_any W_16354 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16358 : bv 32 := 0x02e686b3.
Lemma F_16358 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163f8 : word) = Some W_16358.
Proof. vm_refl. Qed.
Lemma D_16358 : decode_any W_16358 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1635c : bv 32 := 0x00d5f863.
Lemma F_1635c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x163fc : word) = Some W_1635c.
Proof. vm_refl. Qed.
Lemma D_1635c : decode_any W_1635c = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16360 : bv 32 := 0x0100006f.
Lemma F_16360 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16400 : word) = Some W_16360.
Proof. vm_refl. Qed.
Lemma D_16360 : decode_any W_16360 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16364 : bv 32 := 0x03f00693.
Lemma F_16364 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16404 : word) = Some W_16364.
Proof. vm_refl. Qed.
Lemma D_16364 : decode_any W_16364 = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_16368 : bv 32 := 0x00d70463.
Lemma F_16368 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16408 : word) = Some W_16368.
Proof. vm_refl. Qed.
Lemma D_16368 : decode_any W_16368 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16370 : bv 32 := 0x00c65613.
Lemma F_16370 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16410 : word) = Some W_16370.
Proof. vm_refl. Qed.
Lemma D_16370 : decode_any W_16370 = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16374 : bv 32 := 0x00060a63.
Lemma F_16374 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16414 : word) = Some W_16374.
Proof. vm_refl. Qed.
Lemma D_16374 : decode_any W_16374 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_16378 : bv 32 := 0x00861613.
Lemma F_16378 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16418 : word) = Some W_16378.
Proof. vm_refl. Qed.
Lemma D_16378 : decode_any W_16378 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1637c : bv 32 := 0xfff60613.
Lemma F_1637c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1641c : word) = Some W_1637c.
Proof. vm_refl. Qed.
Lemma D_1637c : decode_any W_1637c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_16380 : bv 32 := 0x00b67463.
Lemma F_16380 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16420 : word) = Some W_16380.
Proof. vm_refl. Qed.
Lemma D_16380 : decode_any W_16380 = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16388 : bv 32 := 0x00008067.
Lemma F_16388 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16428 : word) = Some W_16388.
Proof. vm_refl. Qed.
Lemma D_16388 : decode_any W_16388 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1670c : bv 32 := 0x00072503.
Lemma F_1670c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x167ac : word) = Some W_1670c.
Proof. vm_refl. Qed.
Lemma D_1670c : decode_any W_1670c = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16710 : bv 32 := 0x00b56633.
Lemma F_16710 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x167b0 : word) = Some W_16710.
Proof. vm_refl. Qed.
Lemma D_16710 : decode_any W_16710 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_16714 : bv 32 := 0x160726af.
Lemma F_16714 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x167b4 : word) = Some W_16714.
Proof. vm_refl. Qed.
Lemma D_16714 : decode_any W_16714 = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_16718 : bv 32 := 0x00a69663.
Lemma F_16718 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x167b8 : word) = Some W_16718.
Proof. vm_refl. Qed.
Lemma D_16718 : decode_any W_16718 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1671c : bv 32 := 0x1ec727af.
Lemma F_1671c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x167bc : word) = Some W_1671c.
Proof. vm_refl. Qed.
Lemma D_1671c : decode_any W_1671c = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16720 : bv 32 := 0xfe079ae3.
Lemma F_16720 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x167c0 : word) = Some W_16720.
Proof. vm_refl. Qed.
Lemma D_16720 : decode_any W_16720 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_16724 : bv 32 := 0x0006869b.
Lemma F_16724 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x167c4 : word) = Some W_16724.
Proof. vm_refl. Qed.
Lemma D_16724 : decode_any W_16724 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16728 : bv 32 := 0xfea692e3.
Lemma F_16728 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x167c8 : word) = Some W_16728.
Proof. vm_refl. Qed.
Lemma D_16728 : decode_any W_16728 = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_16eec : bv 32 := 0x00062703.
Lemma F_16eec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16f8c : word) = Some W_16eec.
Proof. vm_refl. Qed.
Lemma D_16eec : decode_any W_16eec = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ef0 : bv 32 := 0x00d777b3.
Lemma F_16ef0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16f90 : word) = Some W_16ef0.
Proof. vm_refl. Qed.
Lemma D_16ef0 : decode_any W_16ef0 = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ef4 : bv 32 := 0x1606282f.
Lemma F_16ef4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16f94 : word) = Some W_16ef4.
Proof. vm_refl. Qed.
Lemma D_16ef4 : decode_any W_16ef4 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ef8 : bv 32 := 0x00e81663.
Lemma F_16ef8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16f98 : word) = Some W_16ef8.
Proof. vm_refl. Qed.
Lemma D_16ef8 : decode_any W_16ef8 = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16efc : bv 32 := 0x1ef628af.
Lemma F_16efc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16f9c : word) = Some W_16efc.
Proof. vm_refl. Qed.
Lemma D_16efc : decode_any W_16efc = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f00 : bv 32 := 0xfe089ae3.
Lemma F_16f00 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16fa0 : word) = Some W_16f00.
Proof. vm_refl. Qed.
Lemma D_16f00 : decode_any W_16f00 = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f04 : bv 32 := 0x0008081b.
Lemma F_16f04 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16fa4 : word) = Some W_16f04.
Proof. vm_refl. Qed.
Lemma D_16f04 : decode_any W_16f04 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f08 : bv 32 := 0xfee812e3.
Lemma F_16f08 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x16fa8 : word) = Some W_16f08.
Proof. vm_refl. Qed.
Lemma D_16f08 : decode_any W_16f08 = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.
