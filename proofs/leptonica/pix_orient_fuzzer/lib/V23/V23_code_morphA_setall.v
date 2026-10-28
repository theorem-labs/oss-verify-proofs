(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6f238 : bv 32 := 0x00050a63.
Lemma F_6f238 : fetch_word Ubsan.M.loaded_segments (0x6f238 : word) = Some W_6f238.
Proof. vm_refl. Qed.
Lemma D_6f238 : decode_any W_6f238 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f23c : bv 32 := 0x00757593.
Lemma F_6f23c : fetch_word Ubsan.M.loaded_segments (0x6f23c : word) = Some W_6f23c.
Proof. vm_refl. Qed.
Lemma D_6f23c : decode_any W_6f23c = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f240 : bv 32 := 0x04059063.
Lemma F_6f240 : fetch_word Ubsan.M.loaded_segments (0x6f240 : word) = Some W_6f240.
Proof. vm_refl. Qed.
Lemma D_6f240 : decode_any W_6f240 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f244 : bv 32 := 0x03053503.
Lemma F_6f244 : fetch_word Ubsan.M.loaded_segments (0x6f244 : word) = Some W_6f244.
Proof. vm_refl. Qed.
Lemma D_6f244 : decode_any W_6f244 = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f248 : bv 32 := 0x00008067.
Lemma F_6f248 : fetch_word Ubsan.M.loaded_segments (0x6f248 : word) = Some W_6f248.
Proof. vm_refl. Qed.
Lemma D_6f248 : decode_any W_6f248 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f24c : bv 32 := 0x000b8517.
Lemma F_6f24c : fetch_word Ubsan.M.loaded_segments (0x6f24c : word) = Some W_6f24c.
Proof. vm_refl. Qed.
Lemma D_6f24c : decode_any W_6f24c = Some (Auipc 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f250 : bv 32 := 0x82453503.
Lemma F_6f250 : fetch_word Ubsan.M.loaded_segments (0x6f250 : word) = Some W_6f250.
Proof. vm_refl. Qed.
Lemma D_6f250 : decode_any W_6f250 = Some (Load SZ8 true 10 10 2084, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f254 : bv 32 := 0x00052503.
Lemma F_6f254 : fetch_word Ubsan.M.loaded_segments (0x6f254 : word) = Some W_6f254.
Proof. vm_refl. Qed.
Lemma D_6f254 : decode_any W_6f254 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f258 : bv 32 := 0x00500593.
Lemma F_6f258 : fetch_word Ubsan.M.loaded_segments (0x6f258 : word) = Some W_6f258.
Proof. vm_refl. Qed.
Lemma D_6f258 : decode_any W_6f258 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f25c : bv 32 := 0x00a5ce63.
Lemma F_6f25c : fetch_word Ubsan.M.loaded_segments (0x6f25c : word) = Some W_6f25c.
Proof. vm_refl. Qed.
Lemma D_6f25c : decode_any W_6f25c = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f260 : bv 32 := 0xfffa2517.
Lemma F_6f260 : fetch_word Ubsan.M.loaded_segments (0x6f260 : word) = Some W_6f260.
Proof. vm_refl. Qed.
Lemma D_6f260 : decode_any W_6f260 = Some (Auipc 10 1048482, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f264 : bv 32 := 0xfffa3597.
Lemma F_6f264 : fetch_word Ubsan.M.loaded_segments (0x6f264 : word) = Some W_6f264.
Proof. vm_refl. Qed.
Lemma D_6f264 : decode_any W_6f264 = Some (Auipc 11 1048483, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f268 : bv 32 := 0xdeb50513.
Lemma F_6f268 : fetch_word Ubsan.M.loaded_segments (0x6f268 : word) = Some W_6f268.
Proof. vm_refl. Qed.
Lemma D_6f268 : decode_any W_6f268 = Some (OpImm ALU_ADD 10 10 3563, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f26c : bv 32 := 0xd7258593.
Lemma F_6f26c : fetch_word Ubsan.M.loaded_segments (0x6f26c : word) = Some W_6f26c.
Proof. vm_refl. Qed.
Lemma D_6f26c : decode_any W_6f26c = Some (OpImm ALU_ADD 11 11 3442, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f270 : bv 32 := 0x00000613.
Lemma F_6f270 : fetch_word Ubsan.M.loaded_segments (0x6f270 : word) = Some W_6f270.
Proof. vm_refl. Qed.
Lemma D_6f270 : decode_any W_6f270 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f274 : bv 32 := 0xcccf406f.
Lemma F_6f274 : fetch_word Ubsan.M.loaded_segments (0x6f274 : word) = Some W_6f274.
Proof. vm_refl. Qed.
Lemma D_6f274 : decode_any W_6f274 = Some (Jal 0 2049228, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f278 : bv 32 := 0x00000513.
Lemma F_6f278 : fetch_word Ubsan.M.loaded_segments (0x6f278 : word) = Some W_6f278.
Proof. vm_refl. Qed.
Lemma D_6f278 : decode_any W_6f278 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f27c : bv 32 := 0x00008067.
Lemma F_6f27c : fetch_word Ubsan.M.loaded_segments (0x6f27c : word) = Some W_6f27c.
Proof. vm_refl. Qed.
Lemma D_6f27c : decode_any W_6f27c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffb4 : bv 32 := 0xfe010113.
Lemma F_6ffb4 : fetch_word Ubsan.M.loaded_segments (0x6ffb4 : word) = Some W_6ffb4.
Proof. vm_refl. Qed.
Lemma D_6ffb4 : decode_any W_6ffb4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffb8 : bv 32 := 0x00113c23.
Lemma F_6ffb8 : fetch_word Ubsan.M.loaded_segments (0x6ffb8 : word) = Some W_6ffb8.
Proof. vm_refl. Qed.
Lemma D_6ffb8 : decode_any W_6ffb8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffbc : bv 32 := 0x00813823.
Lemma F_6ffbc : fetch_word Ubsan.M.loaded_segments (0x6ffbc : word) = Some W_6ffbc.
Proof. vm_refl. Qed.
Lemma D_6ffbc : decode_any W_6ffbc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffc0 : bv 32 := 0x00913423.
Lemma F_6ffc0 : fetch_word Ubsan.M.loaded_segments (0x6ffc0 : word) = Some W_6ffc0.
Proof. vm_refl. Qed.
Lemma D_6ffc0 : decode_any W_6ffc0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffc4 : bv 32 := 0x08050463.
Lemma F_6ffc4 : fetch_word Ubsan.M.loaded_segments (0x6ffc4 : word) = Some W_6ffc4.
Proof. vm_refl. Qed.
Lemma D_6ffc4 : decode_any W_6ffc4 = Some (Branch BC_EQ 10 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffc8 : bv 32 := 0x00050413.
Lemma F_6ffc8 : fetch_word Ubsan.M.loaded_segments (0x6ffc8 : word) = Some W_6ffc8.
Proof. vm_refl. Qed.
Lemma D_6ffc8 : decode_any W_6ffc8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffcc : bv 32 := 0xa6cff0ef.
Lemma F_6ffcc : fetch_word Ubsan.M.loaded_segments (0x6ffcc : word) = Some W_6ffcc.
Proof. vm_refl. Qed.
Lemma D_6ffcc : decode_any W_6ffcc = Some (Jal 1 2093676, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffd0 : bv 32 := 0x04050263.
Lemma F_6ffd0 : fetch_word Ubsan.M.loaded_segments (0x6ffd0 : word) = Some W_6ffd0.
Proof. vm_refl. Qed.
Lemma D_6ffd0 : decode_any W_6ffd0 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffd4 : bv 32 := 0x00050493.
Lemma F_6ffd4 : fetch_word Ubsan.M.loaded_segments (0x6ffd4 : word) = Some W_6ffd4.
Proof. vm_refl. Qed.
Lemma D_6ffd4 : decode_any W_6ffd4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffd8 : bv 32 := 0x6c4030ef.
Lemma F_6ffd8 : fetch_word Ubsan.M.loaded_segments (0x6ffd8 : word) = Some W_6ffd8.
Proof. vm_refl. Qed.
Lemma D_6ffd8 : decode_any W_6ffd8 = Some (Jal 1 14020, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffdc : bv 32 := 0x0074f593.
Lemma F_6ffdc : fetch_word Ubsan.M.loaded_segments (0x6ffdc : word) = Some W_6ffdc.
Proof. vm_refl. Qed.
Lemma D_6ffdc : decode_any W_6ffdc = Some (OpImm ALU_AND 11 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffe0 : bv 32 := 0x0c059063.
Lemma F_6ffe0 : fetch_word Ubsan.M.loaded_segments (0x6ffe0 : word) = Some W_6ffe0.
Proof. vm_refl. Qed.
Lemma D_6ffe0 : decode_any W_6ffe0 = Some (Branch BC_NE 11 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffe4 : bv 32 := 0x00c4a583.
Lemma F_6ffe4 : fetch_word Ubsan.M.loaded_segments (0x6ffe4 : word) = Some W_6ffe4.
Proof. vm_refl. Qed.
Lemma D_6ffe4 : decode_any W_6ffe4 = Some (Load SZ4 true 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffe8 : bv 32 := 0x02b55663.
Lemma F_6ffe8 : fetch_word Ubsan.M.loaded_segments (0x6ffe8 : word) = Some W_6ffe8.
Proof. vm_refl. Qed.
Lemma D_6ffe8 : decode_any W_6ffe8 = Some (Branch BC_GE 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffec : bv 32 := 0x000b7517.
Lemma F_6ffec : fetch_word Ubsan.M.loaded_segments (0x6ffec : word) = Some W_6ffec.
Proof. vm_refl. Qed.
Lemma D_6ffec : decode_any W_6ffec = Some (Auipc 10 183, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fff0 : bv 32 := 0xa8453503.
Lemma F_6fff0 : fetch_word Ubsan.M.loaded_segments (0x6fff0 : word) = Some W_6fff0.
Proof. vm_refl. Qed.
Lemma D_6fff0 : decode_any W_6fff0 = Some (Load SZ8 true 10 10 2692, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fff4 : bv 32 := 0x00052503.
Lemma F_6fff4 : fetch_word Ubsan.M.loaded_segments (0x6fff4 : word) = Some W_6fff4.
Proof. vm_refl. Qed.
Lemma D_6fff4 : decode_any W_6fff4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fff8 : bv 32 := 0x00500593.
Lemma F_6fff8 : fetch_word Ubsan.M.loaded_segments (0x6fff8 : word) = Some W_6fff8.
Proof. vm_refl. Qed.
Lemma D_6fff8 : decode_any W_6fff8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fffc : bv 32 := 0x08a5c663.
Lemma F_6fffc : fetch_word Ubsan.M.loaded_segments (0x6fffc : word) = Some W_6fffc.
Proof. vm_refl. Qed.
Lemma D_6fffc : decode_any W_6fffc = Some (Branch BC_LT 11 10 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_70000 : bv 32 := 0xfffad517.
Lemma F_70000 : fetch_word Ubsan.M.loaded_segments (0x70000 : word) = Some W_70000.
Proof. vm_refl. Qed.
Lemma D_70000 : decode_any W_70000 = Some (Auipc 10 1048493, 4%Z).
Proof. vm_refl. Qed.

Definition W_70004 : bv 32 := 0xfffa5597.
Lemma F_70004 : fetch_word Ubsan.M.loaded_segments (0x70004 : word) = Some W_70004.
Proof. vm_refl. Qed.
Lemma D_70004 : decode_any W_70004 = Some (Auipc 11 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_70008 : bv 32 := 0x5f450513.
Lemma F_70008 : fetch_word Ubsan.M.loaded_segments (0x70008 : word) = Some W_70008.
Proof. vm_refl. Qed.
Lemma D_70008 : decode_any W_70008 = Some (OpImm ALU_ADD 10 10 1524, 4%Z).
Proof. vm_refl. Qed.

Definition W_7000c : bv 32 := 0xaeb58593.
Lemma F_7000c : fetch_word Ubsan.M.loaded_segments (0x7000c : word) = Some W_7000c.
Proof. vm_refl. Qed.
Lemma D_7000c : decode_any W_7000c = Some (OpImm ALU_ADD 11 11 2795, 4%Z).
Proof. vm_refl. Qed.

Definition W_70010 : bv 32 := 0x0600006f.
Lemma F_70010 : fetch_word Ubsan.M.loaded_segments (0x70010 : word) = Some W_70010.
Proof. vm_refl. Qed.
Lemma D_70010 : decode_any W_70010 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_70014 : bv 32 := 0x00747513.
Lemma F_70014 : fetch_word Ubsan.M.loaded_segments (0x70014 : word) = Some W_70014.
Proof. vm_refl. Qed.
Lemma D_70014 : decode_any W_70014 = Some (OpImm ALU_AND 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_70018 : bv 32 := 0x08051463.
Lemma F_70018 : fetch_word Ubsan.M.loaded_segments (0x70018 : word) = Some W_70018.
Proof. vm_refl. Qed.
Lemma D_70018 : decode_any W_70018 = Some (Branch BC_NE 10 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_7001c : bv 32 := 0x01046503.
Lemma F_7001c : fetch_word Ubsan.M.loaded_segments (0x7001c : word) = Some W_7001c.
Proof. vm_refl. Qed.
Lemma D_7001c : decode_any W_7001c = Some (Load SZ4 false 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_70020 : bv 32 := 0x00446583.
Lemma F_70020 : fetch_word Ubsan.M.loaded_segments (0x70020 : word) = Some W_70020.
Proof. vm_refl. Qed.
Lemma D_70020 : decode_any W_70020 = Some (Load SZ4 false 11 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_70024 : bv 32 := 0x00251513.
Lemma F_70024 : fetch_word Ubsan.M.loaded_segments (0x70024 : word) = Some W_70024.
Proof. vm_refl. Qed.
Lemma D_70024 : decode_any W_70024 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_70028 : bv 32 := 0x02b516b3.
Lemma F_70028 : fetch_word Ubsan.M.loaded_segments (0x70028 : word) = Some W_70028.
Proof. vm_refl. Qed.
Lemma D_70028 : decode_any W_70028 = Some (Mul M_MULH 13 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7002c : bv 32 := 0x02b50633.
Lemma F_7002c : fetch_word Ubsan.M.loaded_segments (0x7002c : word) = Some W_7002c.
Proof. vm_refl. Qed.
Lemma D_7002c : decode_any W_7002c = Some (Mul M_MUL 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70030 : bv 32 := 0x43f65513.
Lemma F_70030 : fetch_word Ubsan.M.loaded_segments (0x70030 : word) = Some W_70030.
Proof. vm_refl. Qed.
Lemma D_70030 : decode_any W_70030 = Some (ShiftImm ALU_SRA 10 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_70034 : bv 32 := 0x06a69663.
Lemma F_70034 : fetch_word Ubsan.M.loaded_segments (0x70034 : word) = Some W_70034.
Proof. vm_refl. Qed.
Lemma D_70034 : decode_any W_70034 = Some (Branch BC_NE 13 10 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_70038 : bv 32 := 0x03843503.
Lemma F_70038 : fetch_word Ubsan.M.loaded_segments (0x70038 : word) = Some W_70038.
Proof. vm_refl. Qed.
Lemma D_70038 : decode_any W_70038 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7003c : bv 32 := 0x0ff00593.
Lemma F_7003c : fetch_word Ubsan.M.loaded_segments (0x7003c : word) = Some W_7003c.
Proof. vm_refl. Qed.
Lemma D_7003c : decode_any W_7003c = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_70040 : bv 32 := 0x694ae0ef.
Lemma F_70040 : fetch_word Ubsan.M.loaded_segments (0x70040 : word) = Some W_70040.
Proof. vm_refl. Qed.
Lemma D_70040 : decode_any W_70040 = Some (Jal 1 714388, 4%Z).
Proof. vm_refl. Qed.

Definition W_70044 : bv 32 := 0x00000513.
Lemma F_70044 : fetch_word Ubsan.M.loaded_segments (0x70044 : word) = Some W_70044.
Proof. vm_refl. Qed.
Lemma D_70044 : decode_any W_70044 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70048 : bv 32 := 0x0440006f.
Lemma F_70048 : fetch_word Ubsan.M.loaded_segments (0x70048 : word) = Some W_70048.
Proof. vm_refl. Qed.
Lemma D_70048 : decode_any W_70048 = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7004c : bv 32 := 0x000b7517.
Lemma F_7004c : fetch_word Ubsan.M.loaded_segments (0x7004c : word) = Some W_7004c.
Proof. vm_refl. Qed.
Lemma D_7004c : decode_any W_7004c = Some (Auipc 10 183, 4%Z).
Proof. vm_refl. Qed.

Definition W_70050 : bv 32 := 0xa2453503.
Lemma F_70050 : fetch_word Ubsan.M.loaded_segments (0x70050 : word) = Some W_70050.
Proof. vm_refl. Qed.
Lemma D_70050 : decode_any W_70050 = Some (Load SZ8 true 10 10 2596, 4%Z).
Proof. vm_refl. Qed.

Definition W_70054 : bv 32 := 0x00052503.
Lemma F_70054 : fetch_word Ubsan.M.loaded_segments (0x70054 : word) = Some W_70054.
Proof. vm_refl. Qed.
Lemma D_70054 : decode_any W_70054 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70058 : bv 32 := 0x00500593.
Lemma F_70058 : fetch_word Ubsan.M.loaded_segments (0x70058 : word) = Some W_70058.
Proof. vm_refl. Qed.
Lemma D_70058 : decode_any W_70058 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7005c : bv 32 := 0x02a5c663.
Lemma F_7005c : fetch_word Ubsan.M.loaded_segments (0x7005c : word) = Some W_7005c.
Proof. vm_refl. Qed.
Lemma D_7005c : decode_any W_7005c = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_70060 : bv 32 := 0xfffa1517.
Lemma F_70060 : fetch_word Ubsan.M.loaded_segments (0x70060 : word) = Some W_70060.
Proof. vm_refl. Qed.
Lemma D_70060 : decode_any W_70060 = Some (Auipc 10 1048481, 4%Z).
Proof. vm_refl. Qed.

Definition W_70064 : bv 32 := 0xfffa5597.
Lemma F_70064 : fetch_word Ubsan.M.loaded_segments (0x70064 : word) = Some W_70064.
Proof. vm_refl. Qed.
Lemma D_70064 : decode_any W_70064 = Some (Auipc 11 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_70068 : bv 32 := 0xfeb50513.
Lemma F_70068 : fetch_word Ubsan.M.loaded_segments (0x70068 : word) = Some W_70068.
Proof. vm_refl. Qed.
Lemma D_70068 : decode_any W_70068 = Some (OpImm ALU_ADD 10 10 4075, 4%Z).
Proof. vm_refl. Qed.

Definition W_7006c : bv 32 := 0xa8b58593.
Lemma F_7006c : fetch_word Ubsan.M.loaded_segments (0x7006c : word) = Some W_7006c.
Proof. vm_refl. Qed.
Lemma D_7006c : decode_any W_7006c = Some (OpImm ALU_ADD 11 11 2699, 4%Z).
Proof. vm_refl. Qed.

Definition W_70070 : bv 32 := 0x00100613.
Lemma F_70070 : fetch_word Ubsan.M.loaded_segments (0x70070 : word) = Some W_70070.
Proof. vm_refl. Qed.
Lemma D_70070 : decode_any W_70070 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70074 : bv 32 := 0x01813083.
Lemma F_70074 : fetch_word Ubsan.M.loaded_segments (0x70074 : word) = Some W_70074.
Proof. vm_refl. Qed.
Lemma D_70074 : decode_any W_70074 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_70078 : bv 32 := 0x01013403.
Lemma F_70078 : fetch_word Ubsan.M.loaded_segments (0x70078 : word) = Some W_70078.
Proof. vm_refl. Qed.
Lemma D_70078 : decode_any W_70078 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7007c : bv 32 := 0x00813483.
Lemma F_7007c : fetch_word Ubsan.M.loaded_segments (0x7007c : word) = Some W_7007c.
Proof. vm_refl. Qed.
Lemma D_7007c : decode_any W_7007c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70080 : bv 32 := 0x02010113.
Lemma F_70080 : fetch_word Ubsan.M.loaded_segments (0x70080 : word) = Some W_70080.
Proof. vm_refl. Qed.
Lemma D_70080 : decode_any W_70080 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70084 : bv 32 := 0xdecf306f.
Lemma F_70084 : fetch_word Ubsan.M.loaded_segments (0x70084 : word) = Some W_70084.
Proof. vm_refl. Qed.
Lemma D_70084 : decode_any W_70084 = Some (Jal 0 2045420, 4%Z).
Proof. vm_refl. Qed.

Definition W_70088 : bv 32 := 0x00100513.
Lemma F_70088 : fetch_word Ubsan.M.loaded_segments (0x70088 : word) = Some W_70088.
Proof. vm_refl. Qed.
Lemma D_70088 : decode_any W_70088 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7008c : bv 32 := 0x01813083.
Lemma F_7008c : fetch_word Ubsan.M.loaded_segments (0x7008c : word) = Some W_7008c.
Proof. vm_refl. Qed.
Lemma D_7008c : decode_any W_7008c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_70090 : bv 32 := 0x01013403.
Lemma F_70090 : fetch_word Ubsan.M.loaded_segments (0x70090 : word) = Some W_70090.
Proof. vm_refl. Qed.
Lemma D_70090 : decode_any W_70090 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_70094 : bv 32 := 0x00813483.
Lemma F_70094 : fetch_word Ubsan.M.loaded_segments (0x70094 : word) = Some W_70094.
Proof. vm_refl. Qed.
Lemma D_70094 : decode_any W_70094 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70098 : bv 32 := 0x02010113.
Lemma F_70098 : fetch_word Ubsan.M.loaded_segments (0x70098 : word) = Some W_70098.
Proof. vm_refl. Qed.
Lemma D_70098 : decode_any W_70098 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7009c : bv 32 := 0x00008067.
Lemma F_7009c : fetch_word Ubsan.M.loaded_segments (0x7009c : word) = Some W_7009c.
Proof. vm_refl. Qed.
Lemma D_7009c : decode_any W_7009c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7369c : bv 32 := 0x00050a63.
Lemma F_7369c : fetch_word Ubsan.M.loaded_segments (0x7369c : word) = Some W_7369c.
Proof. vm_refl. Qed.
Lemma D_7369c : decode_any W_7369c = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_736a0 : bv 32 := 0x00757593.
Lemma F_736a0 : fetch_word Ubsan.M.loaded_segments (0x736a0 : word) = Some W_736a0.
Proof. vm_refl. Qed.
Lemma D_736a0 : decode_any W_736a0 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_736a4 : bv 32 := 0x04059063.
Lemma F_736a4 : fetch_word Ubsan.M.loaded_segments (0x736a4 : word) = Some W_736a4.
Proof. vm_refl. Qed.
Lemma D_736a4 : decode_any W_736a4 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_736a8 : bv 32 := 0x01052503.
Lemma F_736a8 : fetch_word Ubsan.M.loaded_segments (0x736a8 : word) = Some W_736a8.
Proof. vm_refl. Qed.
Lemma D_736a8 : decode_any W_736a8 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_736ac : bv 32 := 0x00008067.
Lemma F_736ac : fetch_word Ubsan.M.loaded_segments (0x736ac : word) = Some W_736ac.
Proof. vm_refl. Qed.
Lemma D_736ac : decode_any W_736ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736b0 : bv 32 := 0x000b3517.
Lemma F_736b0 : fetch_word Ubsan.M.loaded_segments (0x736b0 : word) = Some W_736b0.
Proof. vm_refl. Qed.
Lemma D_736b0 : decode_any W_736b0 = Some (Auipc 10 179, 4%Z).
Proof. vm_refl. Qed.

Definition W_736b4 : bv 32 := 0x3c053503.
Lemma F_736b4 : fetch_word Ubsan.M.loaded_segments (0x736b4 : word) = Some W_736b4.
Proof. vm_refl. Qed.
Lemma D_736b4 : decode_any W_736b4 = Some (Load SZ8 true 10 10 960, 4%Z).
Proof. vm_refl. Qed.

Definition W_736b8 : bv 32 := 0x00052503.
Lemma F_736b8 : fetch_word Ubsan.M.loaded_segments (0x736b8 : word) = Some W_736b8.
Proof. vm_refl. Qed.
Lemma D_736b8 : decode_any W_736b8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736bc : bv 32 := 0x00500593.
Lemma F_736bc : fetch_word Ubsan.M.loaded_segments (0x736bc : word) = Some W_736bc.
Proof. vm_refl. Qed.
Lemma D_736bc : decode_any W_736bc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_736c0 : bv 32 := 0x00a5ce63.
Lemma F_736c0 : fetch_word Ubsan.M.loaded_segments (0x736c0 : word) = Some W_736c0.
Proof. vm_refl. Qed.
Lemma D_736c0 : decode_any W_736c0 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_736c4 : bv 32 := 0xfff9d517.
Lemma F_736c4 : fetch_word Ubsan.M.loaded_segments (0x736c4 : word) = Some W_736c4.
Proof. vm_refl. Qed.
Lemma D_736c4 : decode_any W_736c4 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_736c8 : bv 32 := 0xfffab597.
Lemma F_736c8 : fetch_word Ubsan.M.loaded_segments (0x736c8 : word) = Some W_736c8.
Proof. vm_refl. Qed.
Lemma D_736c8 : decode_any W_736c8 = Some (Auipc 11 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_736cc : bv 32 := 0xd4a50513.
Lemma F_736cc : fetch_word Ubsan.M.loaded_segments (0x736cc : word) = Some W_736cc.
Proof. vm_refl. Qed.
Lemma D_736cc : decode_any W_736cc = Some (OpImm ALU_ADD 10 10 3402, 4%Z).
Proof. vm_refl. Qed.

Definition W_736d0 : bv 32 := 0xdc058593.
Lemma F_736d0 : fetch_word Ubsan.M.loaded_segments (0x736d0 : word) = Some W_736d0.
Proof. vm_refl. Qed.
Lemma D_736d0 : decode_any W_736d0 = Some (OpImm ALU_ADD 11 11 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_736d4 : bv 32 := 0x00000613.
Lemma F_736d4 : fetch_word Ubsan.M.loaded_segments (0x736d4 : word) = Some W_736d4.
Proof. vm_refl. Qed.
Lemma D_736d4 : decode_any W_736d4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736d8 : bv 32 := 0xf99ef06f.
Lemma F_736d8 : fetch_word Ubsan.M.loaded_segments (0x736d8 : word) = Some W_736d8.
Proof. vm_refl. Qed.
Lemma D_736d8 : decode_any W_736d8 = Some (Jal 0 2031512, 4%Z).
Proof. vm_refl. Qed.

Definition W_736dc : bv 32 := 0x00000513.
Lemma F_736dc : fetch_word Ubsan.M.loaded_segments (0x736dc : word) = Some W_736dc.
Proof. vm_refl. Qed.
Lemma D_736dc : decode_any W_736dc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736e0 : bv 32 := 0x00008067.
Lemma F_736e0 : fetch_word Ubsan.M.loaded_segments (0x736e0 : word) = Some W_736e0.
Proof. vm_refl. Qed.
Lemma D_736e0 : decode_any W_736e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
