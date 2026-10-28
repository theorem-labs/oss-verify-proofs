(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_390ac : bv 32 := 0xf9010113.
Lemma F_390ac : fetch_word Ubsan.M.loaded_segments (0x390ac : word) = Some W_390ac.
Proof. vm_refl. Qed.
Lemma D_390ac : decode_any W_390ac = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_390b0 : bv 32 := 0x06113423.
Lemma F_390b0 : fetch_word Ubsan.M.loaded_segments (0x390b0 : word) = Some W_390b0.
Proof. vm_refl. Qed.
Lemma D_390b0 : decode_any W_390b0 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_390b4 : bv 32 := 0x06813023.
Lemma F_390b4 : fetch_word Ubsan.M.loaded_segments (0x390b4 : word) = Some W_390b4.
Proof. vm_refl. Qed.
Lemma D_390b4 : decode_any W_390b4 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_390b8 : bv 32 := 0x04913c23.
Lemma F_390b8 : fetch_word Ubsan.M.loaded_segments (0x390b8 : word) = Some W_390b8.
Proof. vm_refl. Qed.
Lemma D_390b8 : decode_any W_390b8 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_390bc : bv 32 := 0x05213823.
Lemma F_390bc : fetch_word Ubsan.M.loaded_segments (0x390bc : word) = Some W_390bc.
Proof. vm_refl. Qed.
Lemma D_390bc : decode_any W_390bc = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_390c0 : bv 32 := 0x05313423.
Lemma F_390c0 : fetch_word Ubsan.M.loaded_segments (0x390c0 : word) = Some W_390c0.
Proof. vm_refl. Qed.
Lemma D_390c0 : decode_any W_390c0 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_390c4 : bv 32 := 0x05413023.
Lemma F_390c4 : fetch_word Ubsan.M.loaded_segments (0x390c4 : word) = Some W_390c4.
Proof. vm_refl. Qed.
Lemma D_390c4 : decode_any W_390c4 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_390c8 : bv 32 := 0x03513c23.
Lemma F_390c8 : fetch_word Ubsan.M.loaded_segments (0x390c8 : word) = Some W_390c8.
Proof. vm_refl. Qed.
Lemma D_390c8 : decode_any W_390c8 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_390cc : bv 32 := 0x03613823.
Lemma F_390cc : fetch_word Ubsan.M.loaded_segments (0x390cc : word) = Some W_390cc.
Proof. vm_refl. Qed.
Lemma D_390cc : decode_any W_390cc = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_390d0 : bv 32 := 0x03713423.
Lemma F_390d0 : fetch_word Ubsan.M.loaded_segments (0x390d0 : word) = Some W_390d0.
Proof. vm_refl. Qed.
Lemma D_390d0 : decode_any W_390d0 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_390d4 : bv 32 := 0x03813023.
Lemma F_390d4 : fetch_word Ubsan.M.loaded_segments (0x390d4 : word) = Some W_390d4.
Proof. vm_refl. Qed.
Lemma D_390d4 : decode_any W_390d4 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_390d8 : bv 32 := 0x01913c23.
Lemma F_390d8 : fetch_word Ubsan.M.loaded_segments (0x390d8 : word) = Some W_390d8.
Proof. vm_refl. Qed.
Lemma D_390d8 : decode_any W_390d8 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_390dc : bv 32 := 0x00813827.
Lemma F_390dc : fetch_word Ubsan.M.loaded_segments (0x390dc : word) = Some W_390dc.
Proof. vm_refl. Qed.
Lemma D_390dc : decode_any W_390dc = Some (FStore FMT_D 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_390e0 : bv 32 := 0x00913427.
Lemma F_390e0 : fetch_word Ubsan.M.loaded_segments (0x390e0 : word) = Some W_390e0.
Proof. vm_refl. Qed.
Lemma D_390e0 : decode_any W_390e0 = Some (FStore FMT_D 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_390e4 : bv 32 := 0x00058413.
Lemma F_390e4 : fetch_word Ubsan.M.loaded_segments (0x390e4 : word) = Some W_390e4.
Proof. vm_refl. Qed.
Lemma D_390e4 : decode_any W_390e4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_390e8 : bv 32 := 0x400005b7.
Lemma F_390e8 : fetch_word Ubsan.M.loaded_segments (0x390e8 : word) = Some W_390e8.
Proof. vm_refl. Qed.
Lemma D_390e8 : decode_any W_390e8 = Some (Lui 11 262144, 4%Z).
Proof. vm_refl. Qed.

Definition W_390ec : bv 32 := 0x00b4063b.
Lemma F_390ec : fetch_word Ubsan.M.loaded_segments (0x390ec : word) = Some W_390ec.
Proof. vm_refl. Qed.
Lemma D_390ec : decode_any W_390ec = Some (Op32 ALU_ADD 12 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_390f0 : bv 32 := 0x1a064463.
Lemma F_390f0 : fetch_word Ubsan.M.loaded_segments (0x390f0 : word) = Some W_390f0.
Proof. vm_refl. Qed.
Lemma D_390f0 : decode_any W_390f0 = Some (Branch BC_LT 12 0 424, 4%Z).
Proof. vm_refl. Qed.

Definition W_390f4 : bv 32 := 0x00050493.
Lemma F_390f4 : fetch_word Ubsan.M.loaded_segments (0x390f4 : word) = Some W_390f4.
Proof. vm_refl. Qed.
Lemma D_390f4 : decode_any W_390f4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_390f8 : bv 32 := 0x00b505bb.
Lemma F_390f8 : fetch_word Ubsan.M.loaded_segments (0x390f8 : word) = Some W_390f8.
Proof. vm_refl. Qed.
Lemma D_390f8 : decode_any W_390f8 = Some (Op32 ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_390fc : bv 32 := 0x1805ce63.
Lemma F_390fc : fetch_word Ubsan.M.loaded_segments (0x390fc : word) = Some W_390fc.
Proof. vm_refl. Qed.
Lemma D_390fc : decode_any W_390fc = Some (Branch BC_LT 11 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_39100 : bv 32 := 0x20b58453.
Lemma F_39100 : fetch_word Ubsan.M.loaded_segments (0x39100 : word) = Some W_39100.
Proof. vm_refl. Qed.
Lemma D_39100 : decode_any W_39100 = Some (Fsgnj F_SGNJ FMT_S 8 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_39104 : bv 32 := 0x20a504d3.
Lemma F_39104 : fetch_word Ubsan.M.loaded_segments (0x39104 : word) = Some W_39104.
Proof. vm_refl. Qed.
Lemma D_39104 : decode_any W_39104 = Some (Fsgnj F_SGNJ FMT_S 9 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_39108 : bv 32 := 0x00141b1b.
Lemma F_39108 : fetch_word Ubsan.M.loaded_segments (0x39108 : word) = Some W_39108.
Proof. vm_refl. Qed.
Lemma D_39108 : decode_any W_39108 = Some (ShiftImm32 ALU_SLL 22 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3910c : bv 32 := 0x00149a9b.
Lemma F_3910c : fetch_word Ubsan.M.loaded_segments (0x3910c : word) = Some W_3910c.
Proof. vm_refl. Qed.
Lemma D_3910c : decode_any W_3910c = Some (ShiftImm32 ALU_SLL 21 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_39110 : bv 32 := 0x001b6593.
Lemma F_39110 : fetch_word Ubsan.M.loaded_segments (0x39110 : word) = Some W_39110.
Proof. vm_refl. Qed.
Lemma D_39110 : decode_any W_39110 = Some (OpImm ALU_OR 11 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_39114 : bv 32 := 0x001a8513.
Lemma F_39114 : fetch_word Ubsan.M.loaded_segments (0x39114 : word) = Some W_39114.
Proof. vm_refl. Qed.
Lemma D_39114 : decode_any W_39114 = Some (OpImm ALU_ADD 10 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_39118 : bv 32 := 0x9b8ff0ef.
Lemma F_39118 : fetch_word Ubsan.M.loaded_segments (0x39118 : word) = Some W_39118.
Proof. vm_refl. Qed.
Lemma D_39118 : decode_any W_39118 = Some (Jal 1 2093496, 4%Z).
Proof. vm_refl. Qed.

Definition W_3911c : bv 32 := 0x0c050a63.
Lemma F_3911c : fetch_word Ubsan.M.loaded_segments (0x3911c : word) = Some W_3911c.
Proof. vm_refl. Qed.
Lemma D_3911c : decode_any W_3911c = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_39120 : bv 32 := 0x00050913.
Lemma F_39120 : fetch_word Ubsan.M.loaded_segments (0x39120 : word) = Some W_39120.
Proof. vm_refl. Qed.
Lemma D_39120 : decode_any W_39120 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39124 : bv 32 := 0x00757513.
Lemma F_39124 : fetch_word Ubsan.M.loaded_segments (0x39124 : word) = Some W_39124.
Proof. vm_refl. Qed.
Lemma D_39124 : decode_any W_39124 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_39128 : bv 32 := 0x16051863.
Lemma F_39128 : fetch_word Ubsan.M.loaded_segments (0x39128 : word) = Some W_39128.
Proof. vm_refl. Qed.
Lemma D_39128 : decode_any W_39128 = Some (Branch BC_NE 10 0 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_3912c : bv 32 := 0x00992423.
Lemma F_3912c : fetch_word Ubsan.M.loaded_segments (0x3912c : word) = Some W_3912c.
Proof. vm_refl. Qed.
Lemma D_3912c : decode_any W_3912c = Some (Store SZ4 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39130 : bv 32 := 0x00892623.
Lemma F_39130 : fetch_word Ubsan.M.loaded_segments (0x39130 : word) = Some W_39130.
Proof. vm_refl. Qed.
Lemma D_39130 : decode_any W_39130 = Some (Store SZ4 18 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_39134 : bv 32 := 0x1204c263.
Lemma F_39134 : fetch_word Ubsan.M.loaded_segments (0x39134 : word) = Some W_39134.
Proof. vm_refl. Qed.
Lemma D_39134 : decode_any W_39134 = Some (Branch BC_LT 9 0 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_39138 : bv 32 := 0x420487d3.
Lemma F_39138 : fetch_word Ubsan.M.loaded_segments (0x39138 : word) = Some W_39138.
Proof. vm_refl. Qed.
Lemma D_39138 : decode_any W_39138 = Some (Fcvt FC_D FC_S 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3913c : bv 32 := 0x001b0b1b.
Lemma F_3913c : fetch_word Ubsan.M.loaded_segments (0x3913c : word) = Some W_3913c.
Proof. vm_refl. Qed.
Lemma D_3913c : decode_any W_3913c = Some (OpImm32 22 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_39140 : bv 32 := 0x02f7f753.
Lemma F_39140 : fetch_word Ubsan.M.loaded_segments (0x39140 : word) = Some W_39140.
Proof. vm_refl. Qed.
Lemma D_39140 : decode_any W_39140 = Some (Fari F_ADD FMT_D 14 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_39144 : bv 32 := 0x01604463.
Lemma F_39144 : fetch_word Ubsan.M.loaded_segments (0x39144 : word) = Some W_39144.
Proof. vm_refl. Qed.
Lemma D_39144 : decode_any W_39144 = Some (Branch BC_LT 0 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39148 : bv 32 := 0x00100b13.
Lemma F_39148 : fetch_word Ubsan.M.loaded_segments (0x39148 : word) = Some W_39148.
Proof. vm_refl. Qed.
Lemma D_39148 : decode_any W_39148 = Some (OpImm ALU_ADD 22 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3914c : bv 32 := 0x00000993.
Lemma F_3914c : fetch_word Ubsan.M.loaded_segments (0x3914c : word) = Some W_3914c.
Proof. vm_refl. Qed.
Lemma D_3914c : decode_any W_3914c = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39150 : bv 32 := 0x12f774d3.
Lemma F_39150 : fetch_word Ubsan.M.loaded_segments (0x39150 : word) = Some W_39150.
Proof. vm_refl. Qed.
Lemma D_39150 : decode_any W_39150 = Some (Fari F_MUL FMT_D 9 14 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_39154 : bv 32 := 0x40800bbb.
Lemma F_39154 : fetch_word Ubsan.M.loaded_segments (0x39154 : word) = Some W_39154.
Proof. vm_refl. Qed.
Lemma D_39154 : decode_any W_39154 = Some (Op32 ALU_SUB 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39158 : bv 32 := 0x08044263.
Lemma F_39158 : fetch_word Ubsan.M.loaded_segments (0x39158 : word) = Some W_39158.
Proof. vm_refl. Qed.
Lemma D_39158 : decode_any W_39158 = Some (Branch BC_LT 8 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_3915c : bv 32 := 0x409985b3.
Lemma F_3915c : fetch_word Ubsan.M.loaded_segments (0x3915c : word) = Some W_3915c.
Proof. vm_refl. Qed.
Lemma D_3915c : decode_any W_3915c = Some (Op ALU_SUB 11 19 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_39160 : bv 32 := 0x4099853b.
Lemma F_39160 : fetch_word Ubsan.M.loaded_segments (0x39160 : word) = Some W_39160.
Proof. vm_refl. Qed.
Lemma D_39160 : decode_any W_39160 = Some (Op32 ALU_SUB 10 19 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_39164 : bv 32 := 0x12b51a63.
Lemma F_39164 : fetch_word Ubsan.M.loaded_segments (0x39164 : word) = Some W_39164.
Proof. vm_refl. Qed.
Lemma D_39164 : decode_any W_39164 = Some (Branch BC_NE 10 11 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_39168 : bv 32 := 0x02a50c33.
Lemma F_39168 : fetch_word Ubsan.M.loaded_segments (0x39168 : word) = Some W_39168.
Proof. vm_refl. Qed.
Lemma D_39168 : decode_any W_39168 = Some (Mul M_MUL 24 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3916c : bv 32 := 0x02a5053b.
Lemma F_3916c : fetch_word Ubsan.M.loaded_segments (0x3916c : word) = Some W_3916c.
Proof. vm_refl. Qed.
Lemma D_3916c : decode_any W_3916c = Some (Mul32 M_MUL 10 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_39170 : bv 32 := 0x01854533.
Lemma F_39170 : fetch_word Ubsan.M.loaded_segments (0x39170 : word) = Some W_39170.
Proof. vm_refl. Qed.
Lemma D_39170 : decode_any W_39170 = Some (Op ALU_XOR 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_39174 : bv 32 := 0x00a03533.
Lemma F_39174 : fetch_word Ubsan.M.loaded_segments (0x39174 : word) = Some W_39174.
Proof. vm_refl. Qed.
Lemma D_39174 : decode_any W_39174 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_39178 : bv 32 := 0x12051063.
Lemma F_39178 : fetch_word Ubsan.M.loaded_segments (0x39178 : word) = Some W_39178.
Proof. vm_refl. Qed.
Lemma D_39178 : decode_any W_39178 = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_3917c : bv 32 := 0x00000a13.
Lemma F_3917c : fetch_word Ubsan.M.loaded_segments (0x3917c : word) = Some W_3917c.
Proof. vm_refl. Qed.
Lemma D_3917c : decode_any W_3917c = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39180 : bv 32 := 0x000c0c1b.
Lemma F_39180 : fetch_word Ubsan.M.loaded_segments (0x39180 : word) = Some W_39180.
Proof. vm_refl. Qed.
Lemma D_39180 : decode_any W_39180 = Some (OpImm32 24 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39184 : bv 32 := 0x000b8c93.
Lemma F_39184 : fetch_word Ubsan.M.loaded_segments (0x39184 : word) = Some W_39184.
Proof. vm_refl. Qed.
Lemma D_39184 : decode_any W_39184 = Some (OpImm ALU_ADD 25 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39188 : bv 32 := 0x039c8533.
Lemma F_39188 : fetch_word Ubsan.M.loaded_segments (0x39188 : word) = Some W_39188.
Proof. vm_refl. Qed.
Lemma D_39188 : decode_any W_39188 = Some (Mul M_MUL 10 25 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_3918c : bv 32 := 0x039c85bb.
Lemma F_3918c : fetch_word Ubsan.M.loaded_segments (0x3918c : word) = Some W_3918c.
Proof. vm_refl. Qed.
Lemma D_3918c : decode_any W_3918c = Some (Mul32 M_MUL 11 25 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_39190 : bv 32 := 0x10a59463.
Lemma F_39190 : fetch_word Ubsan.M.loaded_segments (0x39190 : word) = Some W_39190.
Proof. vm_refl. Qed.
Lemma D_39190 : decode_any W_39190 = Some (Branch BC_NE 11 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_39194 : bv 32 := 0x0005059b.
Lemma F_39194 : fetch_word Ubsan.M.loaded_segments (0x39194 : word) = Some W_39194.
Proof. vm_refl. Qed.
Lemma D_39194 : decode_any W_39194 = Some (OpImm32 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39198 : bv 32 := 0x00bc0533.
Lemma F_39198 : fetch_word Ubsan.M.loaded_segments (0x39198 : word) = Some W_39198.
Proof. vm_refl. Qed.
Lemma D_39198 : decode_any W_39198 = Some (Op ALU_ADD 10 24 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3919c : bv 32 := 0x00bc05bb.
Lemma F_3919c : fetch_word Ubsan.M.loaded_segments (0x3919c : word) = Some W_3919c.
Proof. vm_refl. Qed.
Lemma D_3919c : decode_any W_3919c = Some (Op32 ALU_ADD 11 24 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_391a0 : bv 32 := 0x0ea59c63.
Lemma F_391a0 : fetch_word Ubsan.M.loaded_segments (0x391a0 : word) = Some W_391a0.
Proof. vm_refl. Qed.
Lemma D_391a0 : decode_any W_391a0 = Some (Branch BC_NE 11 10 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_391a4 : bv 32 := 0xd00577d3.
Lemma F_391a4 : fetch_word Ubsan.M.loaded_segments (0x391a4 : word) = Some W_391a4.
Proof. vm_refl. Qed.
Lemma D_391a4 : decode_any W_391a4 = Some (Fcvt FC_S FC_W 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_391a8 : bv 32 := 0x20f797d3.
Lemma F_391a8 : fetch_word Ubsan.M.loaded_segments (0x391a8 : word) = Some W_391a8.
Proof. vm_refl. Qed.
Lemma D_391a8 : decode_any W_391a8 = Some (Fsgnj F_SGNJN FMT_S 15 15 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_391ac : bv 32 := 0x420787d3.
Lemma F_391ac : fetch_word Ubsan.M.loaded_segments (0x391ac : word) = Some W_391ac.
Proof. vm_refl. Qed.
Lemma D_391ac : decode_any W_391ac = Some (Fcvt FC_D FC_S 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_391b0 : bv 32 := 0x1a97f7d3.
Lemma F_391b0 : fetch_word Ubsan.M.loaded_segments (0x391b0 : word) = Some W_391b0.
Proof. vm_refl. Qed.
Lemma D_391b0 : decode_any W_391b0 = Some (Fari F_DIV FMT_D 15 15 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_391b4 : bv 32 := 0x4017f553.
Lemma F_391b4 : fetch_word Ubsan.M.loaded_segments (0x391b4 : word) = Some W_391b4.
Proof. vm_refl. Qed.
Lemma D_391b4 : decode_any W_391b4 = Some (Fcvt FC_S FC_D 10 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_391b8 : bv 32 := 0x225040ef.
Lemma F_391b8 : fetch_word Ubsan.M.loaded_segments (0x391b8 : word) = Some W_391b8.
Proof. vm_refl. Qed.
Lemma D_391b8 : decode_any W_391b8 = Some (Jal 1 18980, 4%Z).
Proof. vm_refl. Qed.

Definition W_391bc : bv 32 := 0x10a47553.
Lemma F_391bc : fetch_word Ubsan.M.loaded_segments (0x391bc : word) = Some W_391bc.
Proof. vm_refl. Qed.
Lemma D_391bc : decode_any W_391bc = Some (Fari F_MUL FMT_S 10 8 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_391c0 : bv 32 := 0x00090513.
Lemma F_391c0 : fetch_word Ubsan.M.loaded_segments (0x391c0 : word) = Some W_391c0.
Proof. vm_refl. Qed.
Lemma D_391c0 : decode_any W_391c0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_391c4 : bv 32 := 0x00098593.
Lemma F_391c4 : fetch_word Ubsan.M.loaded_segments (0x391c4 : word) = Some W_391c4.
Proof. vm_refl. Qed.
Lemma D_391c4 : decode_any W_391c4 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_391c8 : bv 32 := 0x000a0613.
Lemma F_391c8 : fetch_word Ubsan.M.loaded_segments (0x391c8 : word) = Some W_391c8.
Proof. vm_refl. Qed.
Lemma D_391c8 : decode_any W_391c8 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_391cc : bv 32 := 0xf74ff0ef.
Lemma F_391cc : fetch_word Ubsan.M.loaded_segments (0x391cc : word) = Some W_391cc.
Proof. vm_refl. Qed.
Lemma D_391cc : decode_any W_391cc = Some (Jal 1 2094964, 4%Z).
Proof. vm_refl. Qed.

Definition W_391d0 : bv 32 := 0x001a0a1b.
Lemma F_391d0 : fetch_word Ubsan.M.loaded_segments (0x391d0 : word) = Some W_391d0.
Proof. vm_refl. Qed.
Lemma D_391d0 : decode_any W_391d0 = Some (OpImm32 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_391d4 : bv 32 := 0x001c8c9b.
Lemma F_391d4 : fetch_word Ubsan.M.loaded_segments (0x391d4 : word) = Some W_391d4.
Proof. vm_refl. Qed.
Lemma D_391d4 : decode_any W_391d4 = Some (OpImm32 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_391d8 : bv 32 := 0xfb4b18e3.
Lemma F_391d8 : fetch_word Ubsan.M.loaded_segments (0x391d8 : word) = Some W_391d8.
Proof. vm_refl. Qed.
Lemma D_391d8 : decode_any W_391d8 = Some (Branch BC_NE 22 20 8112, 4%Z).
Proof. vm_refl. Qed.

Definition W_391dc : bv 32 := 0x0019851b.
Lemma F_391dc : fetch_word Ubsan.M.loaded_segments (0x391dc : word) = Some W_391dc.
Proof. vm_refl. Qed.
Lemma D_391dc : decode_any W_391dc = Some (OpImm32 10 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_391e0 : bv 32 := 0x0b354c63.
Lemma F_391e0 : fetch_word Ubsan.M.loaded_segments (0x391e0 : word) = Some W_391e0.
Proof. vm_refl. Qed.
Lemma D_391e0 : decode_any W_391e0 = Some (Branch BC_LT 10 19 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_391e4 : bv 32 := 0x00050993.
Lemma F_391e4 : fetch_word Ubsan.M.loaded_segments (0x391e4 : word) = Some W_391e4.
Proof. vm_refl. Qed.
Lemma D_391e4 : decode_any W_391e4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_391e8 : bv 32 := 0xf6aad8e3.
Lemma F_391e8 : fetch_word Ubsan.M.loaded_segments (0x391e8 : word) = Some W_391e8.
Proof. vm_refl. Qed.
Lemma D_391e8 : decode_any W_391e8 = Some (Branch BC_GE 21 10 8048, 4%Z).
Proof. vm_refl. Qed.

Definition W_391ec : bv 32 := 0x06c0006f.
Lemma F_391ec : fetch_word Ubsan.M.loaded_segments (0x391ec : word) = Some W_391ec.
Proof. vm_refl. Qed.
Lemma D_391ec : decode_any W_391ec = Some (Jal 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_391f0 : bv 32 := 0x0000c517.
Lemma F_391f0 : fetch_word Ubsan.M.loaded_segments (0x391f0 : word) = Some W_391f0.
Proof. vm_refl. Qed.
Lemma D_391f0 : decode_any W_391f0 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_391f4 : bv 32 := 0xca853503.
Lemma F_391f4 : fetch_word Ubsan.M.loaded_segments (0x391f4 : word) = Some W_391f4.
Proof. vm_refl. Qed.
Lemma D_391f4 : decode_any W_391f4 = Some (Load SZ8 true 10 10 3240, 4%Z).
Proof. vm_refl. Qed.

Definition W_391f8 : bv 32 := 0x00052503.
Lemma F_391f8 : fetch_word Ubsan.M.loaded_segments (0x391f8 : word) = Some W_391f8.
Proof. vm_refl. Qed.
Lemma D_391f8 : decode_any W_391f8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_391fc : bv 32 := 0x00500593.
Lemma F_391fc : fetch_word Ubsan.M.loaded_segments (0x391fc : word) = Some W_391fc.
Proof. vm_refl. Qed.
Lemma D_391fc : decode_any W_391fc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_39200 : bv 32 := 0x04a5ca63.
Lemma F_39200 : fetch_word Ubsan.M.loaded_segments (0x39200 : word) = Some W_39200.
Proof. vm_refl. Qed.
Lemma D_39200 : decode_any W_39200 = Some (Branch BC_LT 11 10 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_39204 : bv 32 := 0xfffd8517.
Lemma F_39204 : fetch_word Ubsan.M.loaded_segments (0x39204 : word) = Some W_39204.
Proof. vm_refl. Qed.
Lemma D_39204 : decode_any W_39204 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_39208 : bv 32 := 0xfffd7597.
Lemma F_39208 : fetch_word Ubsan.M.loaded_segments (0x39208 : word) = Some W_39208.
Proof. vm_refl. Qed.
Lemma D_39208 : decode_any W_39208 = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3920c : bv 32 := 0x5d750513.
Lemma F_3920c : fetch_word Ubsan.M.loaded_segments (0x3920c : word) = Some W_3920c.
Proof. vm_refl. Qed.
Lemma D_3920c : decode_any W_3920c = Some (OpImm ALU_ADD 10 10 1495, 4%Z).
Proof. vm_refl. Qed.

Definition W_39210 : bv 32 := 0x31a58593.
Lemma F_39210 : fetch_word Ubsan.M.loaded_segments (0x39210 : word) = Some W_39210.
Proof. vm_refl. Qed.
Lemma D_39210 : decode_any W_39210 = Some (OpImm ALU_ADD 11 11 794, 4%Z).
Proof. vm_refl. Qed.

Definition W_39214 : bv 32 := 0x00000613.
Lemma F_39214 : fetch_word Ubsan.M.loaded_segments (0x39214 : word) = Some W_39214.
Proof. vm_refl. Qed.
Lemma D_39214 : decode_any W_39214 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39218 : bv 32 := 0x06813083.
Lemma F_39218 : fetch_word Ubsan.M.loaded_segments (0x39218 : word) = Some W_39218.
Proof. vm_refl. Qed.
Lemma D_39218 : decode_any W_39218 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3921c : bv 32 := 0x06013403.
Lemma F_3921c : fetch_word Ubsan.M.loaded_segments (0x3921c : word) = Some W_3921c.
Proof. vm_refl. Qed.
Lemma D_3921c : decode_any W_3921c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_39220 : bv 32 := 0x05813483.
Lemma F_39220 : fetch_word Ubsan.M.loaded_segments (0x39220 : word) = Some W_39220.
Proof. vm_refl. Qed.
Lemma D_39220 : decode_any W_39220 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_39224 : bv 32 := 0x05013903.
Lemma F_39224 : fetch_word Ubsan.M.loaded_segments (0x39224 : word) = Some W_39224.
Proof. vm_refl. Qed.
Lemma D_39224 : decode_any W_39224 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_39228 : bv 32 := 0x04813983.
Lemma F_39228 : fetch_word Ubsan.M.loaded_segments (0x39228 : word) = Some W_39228.
Proof. vm_refl. Qed.
Lemma D_39228 : decode_any W_39228 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3922c : bv 32 := 0x04013a03.
Lemma F_3922c : fetch_word Ubsan.M.loaded_segments (0x3922c : word) = Some W_3922c.
Proof. vm_refl. Qed.
Lemma D_3922c : decode_any W_3922c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_39230 : bv 32 := 0x03813a83.
Lemma F_39230 : fetch_word Ubsan.M.loaded_segments (0x39230 : word) = Some W_39230.
Proof. vm_refl. Qed.
Lemma D_39230 : decode_any W_39230 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_39234 : bv 32 := 0x03013b03.
Lemma F_39234 : fetch_word Ubsan.M.loaded_segments (0x39234 : word) = Some W_39234.
Proof. vm_refl. Qed.
Lemma D_39234 : decode_any W_39234 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_39238 : bv 32 := 0x02813b83.
Lemma F_39238 : fetch_word Ubsan.M.loaded_segments (0x39238 : word) = Some W_39238.
Proof. vm_refl. Qed.
Lemma D_39238 : decode_any W_39238 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3923c : bv 32 := 0x02013c03.
Lemma F_3923c : fetch_word Ubsan.M.loaded_segments (0x3923c : word) = Some W_3923c.
Proof. vm_refl. Qed.
Lemma D_3923c : decode_any W_3923c = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_39240 : bv 32 := 0x01813c83.
Lemma F_39240 : fetch_word Ubsan.M.loaded_segments (0x39240 : word) = Some W_39240.
Proof. vm_refl. Qed.
Lemma D_39240 : decode_any W_39240 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_39244 : bv 32 := 0x01013407.
Lemma F_39244 : fetch_word Ubsan.M.loaded_segments (0x39244 : word) = Some W_39244.
Proof. vm_refl. Qed.
Lemma D_39244 : decode_any W_39244 = Some (FLoad FMT_D 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_39248 : bv 32 := 0x00813487.
Lemma F_39248 : fetch_word Ubsan.M.loaded_segments (0x39248 : word) = Some W_39248.
Proof. vm_refl. Qed.
Lemma D_39248 : decode_any W_39248 = Some (FLoad FMT_D 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3924c : bv 32 := 0x07010113.
Lemma F_3924c : fetch_word Ubsan.M.loaded_segments (0x3924c : word) = Some W_3924c.
Proof. vm_refl. Qed.
Lemma D_3924c : decode_any W_3924c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_39250 : bv 32 := 0xc75de06f.
Lemma F_39250 : fetch_word Ubsan.M.loaded_segments (0x39250 : word) = Some W_39250.
Proof. vm_refl. Qed.
Lemma D_39250 : decode_any W_39250 = Some (Jal 0 1961076, 4%Z).
Proof. vm_refl. Qed.

Definition W_39254 : bv 32 := 0x00000913.
Lemma F_39254 : fetch_word Ubsan.M.loaded_segments (0x39254 : word) = Some W_39254.
Proof. vm_refl. Qed.
Lemma D_39254 : decode_any W_39254 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39258 : bv 32 := 0x00090513.
Lemma F_39258 : fetch_word Ubsan.M.loaded_segments (0x39258 : word) = Some W_39258.
Proof. vm_refl. Qed.
Lemma D_39258 : decode_any W_39258 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3925c : bv 32 := 0x06813083.
Lemma F_3925c : fetch_word Ubsan.M.loaded_segments (0x3925c : word) = Some W_3925c.
Proof. vm_refl. Qed.
Lemma D_3925c : decode_any W_3925c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_39260 : bv 32 := 0x06013403.
Lemma F_39260 : fetch_word Ubsan.M.loaded_segments (0x39260 : word) = Some W_39260.
Proof. vm_refl. Qed.
Lemma D_39260 : decode_any W_39260 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_39264 : bv 32 := 0x05813483.
Lemma F_39264 : fetch_word Ubsan.M.loaded_segments (0x39264 : word) = Some W_39264.
Proof. vm_refl. Qed.
Lemma D_39264 : decode_any W_39264 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_39268 : bv 32 := 0x05013903.
Lemma F_39268 : fetch_word Ubsan.M.loaded_segments (0x39268 : word) = Some W_39268.
Proof. vm_refl. Qed.
Lemma D_39268 : decode_any W_39268 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3926c : bv 32 := 0x04813983.
Lemma F_3926c : fetch_word Ubsan.M.loaded_segments (0x3926c : word) = Some W_3926c.
Proof. vm_refl. Qed.
Lemma D_3926c : decode_any W_3926c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_39270 : bv 32 := 0x04013a03.
Lemma F_39270 : fetch_word Ubsan.M.loaded_segments (0x39270 : word) = Some W_39270.
Proof. vm_refl. Qed.
Lemma D_39270 : decode_any W_39270 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_39274 : bv 32 := 0x03813a83.
Lemma F_39274 : fetch_word Ubsan.M.loaded_segments (0x39274 : word) = Some W_39274.
Proof. vm_refl. Qed.
Lemma D_39274 : decode_any W_39274 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_39278 : bv 32 := 0x03013b03.
Lemma F_39278 : fetch_word Ubsan.M.loaded_segments (0x39278 : word) = Some W_39278.
Proof. vm_refl. Qed.
Lemma D_39278 : decode_any W_39278 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3927c : bv 32 := 0x02813b83.
Lemma F_3927c : fetch_word Ubsan.M.loaded_segments (0x3927c : word) = Some W_3927c.
Proof. vm_refl. Qed.
Lemma D_3927c : decode_any W_3927c = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_39280 : bv 32 := 0x02013c03.
Lemma F_39280 : fetch_word Ubsan.M.loaded_segments (0x39280 : word) = Some W_39280.
Proof. vm_refl. Qed.
Lemma D_39280 : decode_any W_39280 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_39284 : bv 32 := 0x01813c83.
Lemma F_39284 : fetch_word Ubsan.M.loaded_segments (0x39284 : word) = Some W_39284.
Proof. vm_refl. Qed.
Lemma D_39284 : decode_any W_39284 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_39288 : bv 32 := 0x01013407.
Lemma F_39288 : fetch_word Ubsan.M.loaded_segments (0x39288 : word) = Some W_39288.
Proof. vm_refl. Qed.
Lemma D_39288 : decode_any W_39288 = Some (FLoad FMT_D 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3928c : bv 32 := 0x00813487.
Lemma F_3928c : fetch_word Ubsan.M.loaded_segments (0x3928c : word) = Some W_3928c.
Proof. vm_refl. Qed.
Lemma D_3928c : decode_any W_3928c = Some (FLoad FMT_D 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39290 : bv 32 := 0x07010113.
Lemma F_39290 : fetch_word Ubsan.M.loaded_segments (0x39290 : word) = Some W_39290.
Proof. vm_refl. Qed.
Lemma D_39290 : decode_any W_39290 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_39294 : bv 32 := 0x00008067.
Lemma F_39294 : fetch_word Ubsan.M.loaded_segments (0x39294 : word) = Some W_39294.
Proof. vm_refl. Qed.
Lemma D_39294 : decode_any W_39294 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39298 : bv 32 := 0xc0001073.
Lemma F_39298 : fetch_word Ubsan.M.loaded_segments (0x39298 : word) = Some W_39298.
Proof. vm_refl. Qed.
Lemma D_39298 : decode_any W_39298 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
