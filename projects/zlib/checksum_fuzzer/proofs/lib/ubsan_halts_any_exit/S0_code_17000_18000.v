(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_173cc : bv 32 := 0x02053703.
Lemma F_173cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1746c : word) = Some W_173cc.
Proof. vm_refl. Qed.
Lemma D_173cc : decode_any W_173cc = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_173d0 : bv 32 := 0x00c75793.
Lemma F_173d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17470 : word) = Some W_173d0.
Proof. vm_refl. Qed.
Lemma D_173d0 : decode_any W_173d0 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_173d4 : bv 32 := 0x00078e63.
Lemma F_173d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17474 : word) = Some W_173d4.
Proof. vm_refl. Qed.
Lemma D_173d4 : decode_any W_173d4 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_173d8 : bv 32 := 0x01f77793.
Lemma F_173d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17478 : word) = Some W_173d8.
Proof. vm_refl. Qed.
Lemma D_173d8 : decode_any W_173d8 = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_173dc : bv 32 := 0x00079a63.
Lemma F_173dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1747c : word) = Some W_173dc.
Proof. vm_refl. Qed.
Lemma D_173dc : decode_any W_173dc = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_173e0 : bv 32 := 0xfffff7b7.
Lemma F_173e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17480 : word) = Some W_173e0.
Proof. vm_refl. Qed.
Lemma D_173e0 : decode_any W_173e0 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_173e4 : bv 32 := 0x00f77733.
Lemma F_173e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17484 : word) = Some W_173e4.
Proof. vm_refl. Qed.
Lemma D_173e4 : decode_any W_173e4 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_173e8 : bv 32 := 0xff070713.
Lemma F_173e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17488 : word) = Some W_173e8.
Proof. vm_refl. Qed.
Lemma D_173e8 : decode_any W_173e8 = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_173ec : bv 32 := 0x0200006f.
Lemma F_173ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1748c : word) = Some W_173ec.
Proof. vm_refl. Qed.
Lemma D_173ec : decode_any W_173ec = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_173f0 : bv 32 := 0x00575713.
Lemma F_173f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17490 : word) = Some W_173f0.
Proof. vm_refl. Qed.
Lemma D_173f0 : decode_any W_173f0 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_173f4 : bv 32 := 0xffffa797.
Lemma F_173f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17494 : word) = Some W_173f4.
Proof. vm_refl. Qed.
Lemma D_173f4 : decode_any W_173f4 = Some (Auipc 15 1048570, 4%Z).
Proof. vm_refl. Qed.

Definition W_173f8 : bv 32 := 0x07e77713.
Lemma F_173f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17498 : word) = Some W_173f8.
Proof. vm_refl. Qed.
Lemma D_173f8 : decode_any W_173f8 = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_173fc : bv 32 := 0x61878793.
Lemma F_173fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1749c : word) = Some W_173fc.
Proof. vm_refl. Qed.
Lemma D_173fc : decode_any W_173fc = Some (OpImm ALU_ADD 15 15 1560, 4%Z).
Proof. vm_refl. Qed.

Definition W_17400 : bv 32 := 0x00e78733.
Lemma F_17400 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174a0 : word) = Some W_17400.
Proof. vm_refl. Qed.
Lemma D_17400 : decode_any W_17400 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17404 : bv 32 := 0x00075703.
Lemma F_17404 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174a4 : word) = Some W_17404.
Proof. vm_refl. Qed.
Lemma D_17404 : decode_any W_17404 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17408 : bv 32 := 0x00471713.
Lemma F_17408 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174a8 : word) = Some W_17408.
Proof. vm_refl. Qed.
Lemma D_17408 : decode_any W_17408 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1740c : bv 32 := 0x01053803.
Lemma F_1740c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174ac : word) = Some W_1740c.
Proof. vm_refl. Qed.
Lemma D_1740c : decode_any W_1740c = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17410 : bv 32 := 0x02b707b3.
Lemma F_17410 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174b0 : word) = Some W_17410.
Proof. vm_refl. Qed.
Lemma D_17410 : decode_any W_17410 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17414 : bv 32 := 0x00f807b3.
Lemma F_17414 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174b4 : word) = Some W_17414.
Proof. vm_refl. Qed.
Lemma D_17414 : decode_any W_17414 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17418 : bv 32 := 0x00d7c883.
Lemma F_17418 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174b8 : word) = Some W_17418.
Proof. vm_refl. Qed.
Lemma D_17418 : decode_any W_17418 = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1741c : bv 32 := 0x40c702b3.
Lemma F_1741c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174bc : word) = Some W_1741c.
Proof. vm_refl. Qed.
Lemma D_1741c : decode_any W_1741c = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17420 : bv 32 := 0xffc28293.
Lemma F_17420 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174c0 : word) = Some W_17420.
Proof. vm_refl. Qed.
Lemma D_17420 : decode_any W_17420 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_17424 : bv 32 := 0x01078793.
Lemma F_17424 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174c4 : word) = Some W_17424.
Proof. vm_refl. Qed.
Lemma D_17424 : decode_any W_17424 = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17428 : bv 32 := 0x00088663.
Lemma F_17428 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174c8 : word) = Some W_17428.
Proof. vm_refl. Qed.
Lemma D_17428 : decode_any W_17428 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1742c : bv 32 := 0xffe7d683.
Lemma F_1742c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174cc : word) = Some W_1742c.
Proof. vm_refl. Qed.
Lemma D_1742c : decode_any W_1742c = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_17430 : bv 32 := 0x00168693.
Lemma F_17430 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174d0 : word) = Some W_17430.
Proof. vm_refl. Qed.
Lemma D_17430 : decode_any W_17430 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17434 : bv 32 := 0xffc7c383.
Lemma F_17434 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174d4 : word) = Some W_17434.
Proof. vm_refl. Qed.
Lemma D_17434 : decode_any W_17434 = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_17438 : bv 32 := 0x0042d313.
Lemma F_17438 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174d8 : word) = Some W_17438.
Proof. vm_refl. Qed.
Lemma D_17438 : decode_any W_17438 = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1743c : bv 32 := 0x0ff6f893.
Lemma F_1743c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174dc : word) = Some W_1743c.
Proof. vm_refl. Qed.
Lemma D_1743c : decode_any W_1743c = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_17440 : bv 32 := 0x00038463.
Lemma F_17440 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174e0 : word) = Some W_17440.
Proof. vm_refl. Qed.
Lemma D_17440 : decode_any W_17440 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17448 : bv 32 := 0x03137e63.
Lemma F_17448 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174e8 : word) = Some W_17448.
Proof. vm_refl. Qed.
Lemma D_17448 : decode_any W_17448 = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_1744c : bv 32 := 0x0052d693.
Lemma F_1744c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174ec : word) = Some W_1744c.
Proof. vm_refl. Qed.
Lemma D_1744c : decode_any W_1744c = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_17450 : bv 32 := 0x00d366b3.
Lemma F_17450 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174f0 : word) = Some W_17450.
Proof. vm_refl. Qed.
Lemma D_17450 : decode_any W_17450 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17454 : bv 32 := 0x0026d293.
Lemma F_17454 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174f4 : word) = Some W_17454.
Proof. vm_refl. Qed.
Lemma D_17454 : decode_any W_17454 = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_17458 : bv 32 := 0x00d2e6b3.
Lemma F_17458 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174f8 : word) = Some W_17458.
Proof. vm_refl. Qed.
Lemma D_17458 : decode_any W_17458 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1745c : bv 32 := 0x0046d293.
Lemma F_1745c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x174fc : word) = Some W_1745c.
Proof. vm_refl. Qed.
Lemma D_1745c : decode_any W_1745c = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17460 : bv 32 := 0x00d2e6b3.
Lemma F_17460 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17500 : word) = Some W_17460.
Proof. vm_refl. Qed.
Lemma D_17460 : decode_any W_17460 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17464 : bv 32 := 0x00d8f6b3.
Lemma F_17464 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17504 : word) = Some W_17464.
Proof. vm_refl. Qed.
Lemma D_17464 : decode_any W_17464 = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17468 : bv 32 := 0x00d338b3.
Lemma F_17468 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17508 : word) = Some W_17468.
Proof. vm_refl. Qed.
Lemma D_17468 : decode_any W_17468 = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1746c : bv 32 := 0xfff34293.
Lemma F_1746c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1750c : word) = Some W_1746c.
Proof. vm_refl. Qed.
Lemma D_1746c : decode_any W_1746c = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17470 : bv 32 := 0x411008bb.
Lemma F_17470 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17510 : word) = Some W_17470.
Proof. vm_refl. Qed.
Lemma D_17470 : decode_any W_17470 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_17474 : bv 32 := 0x0058f8b3.
Lemma F_17474 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17514 : word) = Some W_17474.
Proof. vm_refl. Qed.
Lemma D_17474 : decode_any W_17474 = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_17478 : bv 32 := 0x00d888bb.
Lemma F_17478 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17518 : word) = Some W_17478.
Proof. vm_refl. Qed.
Lemma D_17478 : decode_any W_17478 = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1747c : bv 32 := 0x01137463.
Lemma F_1747c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1751c : word) = Some W_1747c.
Proof. vm_refl. Qed.
Lemma D_1747c : decode_any W_1747c = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17484 : bv 32 := 0x00078693.
Lemma F_17484 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17524 : word) = Some W_17484.
Proof. vm_refl. Qed.
Lemma D_17484 : decode_any W_17484 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17488 : bv 32 := 0x02088063.
Lemma F_17488 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17528 : word) = Some W_17488.
Proof. vm_refl. Qed.
Lemma D_17488 : decode_any W_17488 = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1748c : bv 32 := 0xfe000813.
Lemma F_1748c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1752c : word) = Some W_1748c.
Proof. vm_refl. Qed.
Lemma D_1748c : decode_any W_1748c = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_17490 : bv 32 := 0x0048969b.
Lemma F_17490 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17530 : word) = Some W_17490.
Proof. vm_refl. Qed.
Lemma D_17490 : decode_any W_17490 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17494 : bv 32 := 0x00d786b3.
Lemma F_17494 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17534 : word) = Some W_17494.
Proof. vm_refl. Qed.
Lemma D_17494 : decode_any W_17494 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17498 : bv 32 := 0xff078ea3.
Lemma F_17498 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17538 : word) = Some W_17498.
Proof. vm_refl. Qed.
Lemma D_17498 : decode_any W_17498 = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1749c : bv 32 := 0xff179f23.
Lemma F_1749c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1753c : word) = Some W_1749c.
Proof. vm_refl. Qed.
Lemma D_1749c : decode_any W_1749c = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_174a0 : bv 32 := 0xfe068e23.
Lemma F_174a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17540 : word) = Some W_174a0.
Proof. vm_refl. Qed.
Lemma D_174a0 : decode_any W_174a0 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_174a4 : bv 32 := 0x01053803.
Lemma F_174a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17544 : word) = Some W_174a4.
Proof. vm_refl. Qed.
Lemma D_174a4 : decode_any W_174a4 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_174a8 : bv 32 := 0x00e78733.
Lemma F_174a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17548 : word) = Some W_174a8.
Proof. vm_refl. Qed.
Lemma D_174a8 : decode_any W_174a8 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_174ac : bv 32 := 0x410687bb.
Lemma F_174ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1754c : word) = Some W_174ac.
Proof. vm_refl. Qed.
Lemma D_174ac : decode_any W_174ac = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_174b0 : bv 32 := 0x00d60633.
Lemma F_174b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17550 : word) = Some W_174b0.
Proof. vm_refl. Qed.
Lemma D_174b0 : decode_any W_174b0 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_174b4 : bv 32 := 0xffc70513.
Lemma F_174b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17554 : word) = Some W_174b4.
Proof. vm_refl. Qed.
Lemma D_174b4 : decode_any W_174b4 = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_174b8 : bv 32 := 0xff078793.
Lemma F_174b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17558 : word) = Some W_174b8.
Proof. vm_refl. Qed.
Lemma D_174b8 : decode_any W_174b8 = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_174bc : bv 32 := 0x0047d793.
Lemma F_174bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1755c : word) = Some W_174bc.
Proof. vm_refl. Qed.
Lemma D_174bc : decode_any W_174bc = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_174c0 : bv 32 := 0x40c5083b.
Lemma F_174c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17560 : word) = Some W_174c0.
Proof. vm_refl. Qed.
Lemma D_174c0 : decode_any W_174c0 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_174c4 : bv 32 := 0xfeb68ea3.
Lemma F_174c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17564 : word) = Some W_174c4.
Proof. vm_refl. Qed.
Lemma D_174c4 : decode_any W_174c4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_174c8 : bv 32 := 0xfef69f23.
Lemma F_174c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17568 : word) = Some W_174c8.
Proof. vm_refl. Qed.
Lemma D_174c8 : decode_any W_174c8 = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_174cc : bv 32 := 0x02080463.
Lemma F_174cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1756c : word) = Some W_174cc.
Proof. vm_refl. Qed.
Lemma D_174cc : decode_any W_174cc = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_174d0 : bv 32 := 0x40c505bb.
Lemma F_174d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17570 : word) = Some W_174d0.
Proof. vm_refl. Qed.
Lemma D_174d0 : decode_any W_174d0 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_174d4 : bv 32 := 0x40b0063b.
Lemma F_174d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17574 : word) = Some W_174d4.
Proof. vm_refl. Qed.
Lemma D_174d4 : decode_any W_174d4 = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_174d8 : bv 32 := 0x00c50633.
Lemma F_174d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17578 : word) = Some W_174d8.
Proof. vm_refl. Qed.
Lemma D_174d8 : decode_any W_174d8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_174dc : bv 32 := 0x00500513.
Lemma F_174dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1757c : word) = Some W_174dc.
Proof. vm_refl. Qed.
Lemma D_174dc : decode_any W_174dc = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_174e0 : bv 32 := 0x00060023.
Lemma F_174e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17580 : word) = Some W_174e0.
Proof. vm_refl. Qed.
Lemma D_174e0 : decode_any W_174e0 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_174e4 : bv 32 := 0x00a5cc63.
Lemma F_174e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17584 : word) = Some W_174e4.
Proof. vm_refl. Qed.
Lemma D_174e4 : decode_any W_174e4 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_174e8 : bv 32 := 0xfe070ba3.
Lemma F_174e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17588 : word) = Some W_174e8.
Proof. vm_refl. Qed.
Lemma D_174e8 : decode_any W_174e8 = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_174ec : bv 32 := 0xfeb72c23.
Lemma F_174ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1758c : word) = Some W_174ec.
Proof. vm_refl. Qed.
Lemma D_174ec : decode_any W_174ec = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_174f0 : bv 32 := 0x0100006f.
Lemma F_174f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17590 : word) = Some W_174f0.
Proof. vm_refl. Qed.
Lemma D_174f0 : decode_any W_174f0 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_174f4 : bv 32 := 0x00000513.
Lemma F_174f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17594 : word) = Some W_174f4.
Proof. vm_refl. Qed.
Lemma D_174f4 : decode_any W_174f4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_174f8 : bv 32 := 0x0080006f.
Lemma F_174f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17598 : word) = Some W_174f8.
Proof. vm_refl. Qed.
Lemma D_174f8 : decode_any W_174f8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_174fc : bv 32 := 0x00058513.
Lemma F_174fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1759c : word) = Some W_174fc.
Proof. vm_refl. Qed.
Lemma D_174fc : decode_any W_174fc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17500 : bv 32 := 0xffd6c583.
Lemma F_17500 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x175a0 : word) = Some W_17500.
Proof. vm_refl. Qed.
Lemma D_17500 : decode_any W_17500 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_17504 : bv 32 := 0x01f5f593.
Lemma F_17504 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x175a4 : word) = Some W_17504.
Proof. vm_refl. Qed.
Lemma D_17504 : decode_any W_17504 = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_17508 : bv 32 := 0x00551513.
Lemma F_17508 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x175a8 : word) = Some W_17508.
Proof. vm_refl. Qed.
Lemma D_17508 : decode_any W_17508 = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750c : bv 32 := 0x00b56533.
Lemma F_1750c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x175ac : word) = Some W_1750c.
Proof. vm_refl. Qed.
Lemma D_1750c : decode_any W_1750c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17510 : bv 32 := 0xfea68ea3.
Lemma F_17510 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x175b0 : word) = Some W_17510.
Proof. vm_refl. Qed.
Lemma D_17510 : decode_any W_17510 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_17514 : bv 32 := 0x00068513.
Lemma F_17514 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x175b4 : word) = Some W_17514.
Proof. vm_refl. Qed.
Lemma D_17514 : decode_any W_17514 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17518 : bv 32 := 0x00008067.
Lemma F_17518 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x175b8 : word) = Some W_17518.
Proof. vm_refl. Qed.
Lemma D_17518 : decode_any W_17518 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e5c : bv 32 := 0xff010113.
Lemma F_17e5c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17efc : word) = Some W_17e5c.
Proof. vm_refl. Qed.
Lemma D_17e5c : decode_any W_17e5c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e60 : bv 32 := 0x00113423.
Lemma F_17e60 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f00 : word) = Some W_17e60.
Proof. vm_refl. Qed.
Lemma D_17e60 : decode_any W_17e60 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e64 : bv 32 := 0x00813023.
Lemma F_17e64 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f04 : word) = Some W_17e64.
Proof. vm_refl. Qed.
Lemma D_17e64 : decode_any W_17e64 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e68 : bv 32 := 0x198000ef.
Lemma F_17e68 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f08 : word) = Some W_17e68.
Proof. vm_refl. Qed.
Lemma D_17e68 : decode_any W_17e68 = Some (Jal 1 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e6c : bv 32 := 0x00053403.
Lemma F_17e6c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f0c : word) = Some W_17e6c.
Proof. vm_refl. Qed.
Lemma D_17e6c : decode_any W_17e6c = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e70 : bv 32 := 0x12041663.
Lemma F_17e70 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f10 : word) = Some W_17e70.
Proof. vm_refl. Qed.
Lemma D_17e70 : decode_any W_17e70 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e74 : bv 32 := 0x00038517.
Lemma F_17e74 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f14 : word) = Some W_17e74.
Proof. vm_refl. Qed.
Lemma D_17e74 : decode_any W_17e74 = Some (Auipc 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e78 : bv 32 := 0x29c53403.
Lemma F_17e78 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f18 : word) = Some W_17e78.
Proof. vm_refl. Qed.
Lemma D_17e78 : decode_any W_17e78 = Some (Load SZ8 true 8 10 668, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e7c : bv 32 := 0x04040a63.
Lemma F_17e7c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f1c : word) = Some W_17e7c.
Proof. vm_refl. Qed.
Lemma D_17e7c : decode_any W_17e7c = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ed0 : bv 32 := 0x00008517.
Lemma F_17ed0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f70 : word) = Some W_17ed0.
Proof. vm_refl. Qed.
Lemma D_17ed0 : decode_any W_17ed0 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ed4 : bv 32 := 0xa2853403.
Lemma F_17ed4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f74 : word) = Some W_17ed4.
Proof. vm_refl. Qed.
Lemma D_17ed4 : decode_any W_17ed4 = Some (Load SZ8 true 8 10 2600, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ed8 : bv 32 := 0x04040a63.
Lemma F_17ed8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f78 : word) = Some W_17ed8.
Proof. vm_refl. Qed.
Lemma D_17ed8 : decode_any W_17ed8 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_17edc : bv 32 := 0x08c42503.
Lemma F_17edc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f7c : word) = Some W_17edc.
Proof. vm_refl. Qed.
Lemma D_17edc : decode_any W_17edc = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ee0 : bv 32 := 0x00054663.
Lemma F_17ee0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f80 : word) = Some W_17ee0.
Proof. vm_refl. Qed.
Lemma D_17ee0 : decode_any W_17ee0 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eec : bv 32 := 0x02843503.
Lemma F_17eec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f8c : word) = Some W_17eec.
Proof. vm_refl. Qed.
Lemma D_17eec : decode_any W_17eec = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ef0 : bv 32 := 0x03843583.
Lemma F_17ef0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f90 : word) = Some W_17ef0.
Proof. vm_refl. Qed.
Lemma D_17ef0 : decode_any W_17ef0 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ef4 : bv 32 := 0x00b50c63.
Lemma F_17ef4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f94 : word) = Some W_17ef4.
Proof. vm_refl. Qed.
Lemma D_17ef4 : decode_any W_17ef4 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ef8 : bv 32 := 0x04843683.
Lemma F_17ef8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f98 : word) = Some W_17ef8.
Proof. vm_refl. Qed.
Lemma D_17ef8 : decode_any W_17ef8 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_17efc : bv 32 := 0x00040513.
Lemma F_17efc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17f9c : word) = Some W_17efc.
Proof. vm_refl. Qed.
Lemma D_17efc : decode_any W_17efc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f00 : bv 32 := 0x00000593.
Lemma F_17f00 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fa0 : word) = Some W_17f00.
Proof. vm_refl. Qed.
Lemma D_17f00 : decode_any W_17f00 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f04 : bv 32 := 0x00000613.
Lemma F_17f04 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fa4 : word) = Some W_17f04.
Proof. vm_refl. Qed.
Lemma D_17f04 : decode_any W_17f04 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f08 : bv 32 := 0x000680e7.
Lemma F_17f08 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fa8 : word) = Some W_17f08.
Proof. vm_refl. Qed.
Lemma D_17f08 : decode_any W_17f08 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f0c : bv 32 := 0x00843503.
Lemma F_17f0c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fac : word) = Some W_17f0c.
Proof. vm_refl. Qed.
Lemma D_17f0c : decode_any W_17f0c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f10 : bv 32 := 0x01043583.
Lemma F_17f10 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fb0 : word) = Some W_17f10.
Proof. vm_refl. Qed.
Lemma D_17f10 : decode_any W_17f10 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f14 : bv 32 := 0x00b50c63.
Lemma F_17f14 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fb4 : word) = Some W_17f14.
Proof. vm_refl. Qed.
Lemma D_17f14 : decode_any W_17f14 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f2c : bv 32 := 0x00008517.
Lemma F_17f2c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fcc : word) = Some W_17f2c.
Proof. vm_refl. Qed.
Lemma D_17f2c : decode_any W_17f2c = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f30 : bv 32 := 0x8dc53403.
Lemma F_17f30 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fd0 : word) = Some W_17f30.
Proof. vm_refl. Qed.
Lemma D_17f30 : decode_any W_17f30 = Some (Load SZ8 true 8 10 2268, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f34 : bv 32 := 0x0a040e63.
Lemma F_17f34 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fd4 : word) = Some W_17f34.
Proof. vm_refl. Qed.
Lemma D_17f34 : decode_any W_17f34 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f38 : bv 32 := 0x08c42503.
Lemma F_17f38 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fd8 : word) = Some W_17f38.
Proof. vm_refl. Qed.
Lemma D_17f38 : decode_any W_17f38 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f3c : bv 32 := 0x00054663.
Lemma F_17f3c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fdc : word) = Some W_17f3c.
Proof. vm_refl. Qed.
Lemma D_17f3c : decode_any W_17f3c = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f48 : bv 32 := 0x02843503.
Lemma F_17f48 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fe8 : word) = Some W_17f48.
Proof. vm_refl. Qed.
Lemma D_17f48 : decode_any W_17f48 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f4c : bv 32 := 0x03843583.
Lemma F_17f4c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17fec : word) = Some W_17f4c.
Proof. vm_refl. Qed.
Lemma D_17f4c : decode_any W_17f4c = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f50 : bv 32 := 0x00b50c63.
Lemma F_17f50 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x17ff0 : word) = Some W_17f50.
Proof. vm_refl. Qed.
Lemma D_17f50 : decode_any W_17f50 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f68 : bv 32 := 0x00843503.
Lemma F_17f68 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18008 : word) = Some W_17f68.
Proof. vm_refl. Qed.
Lemma D_17f68 : decode_any W_17f68 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f6c : bv 32 := 0x01043583.
Lemma F_17f6c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1800c : word) = Some W_17f6c.
Proof. vm_refl. Qed.
Lemma D_17f6c : decode_any W_17f6c = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f70 : bv 32 := 0x08b50063.
Lemma F_17f70 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18010 : word) = Some W_17f70.
Proof. vm_refl. Qed.
Lemma D_17f70 : decode_any W_17f70 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ff0 : bv 32 := 0x00813083.
Lemma F_17ff0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18090 : word) = Some W_17ff0.
Proof. vm_refl. Qed.
Lemma D_17ff0 : decode_any W_17ff0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ff4 : bv 32 := 0x00013403.
Lemma F_17ff4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18094 : word) = Some W_17ff4.
Proof. vm_refl. Qed.
Lemma D_17ff4 : decode_any W_17ff4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ff8 : bv 32 := 0x01010113.
Lemma F_17ff8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18098 : word) = Some W_17ff8.
Proof. vm_refl. Qed.
Lemma D_17ff8 : decode_any W_17ff8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ffc : bv 32 := 0x00008067.
Lemma F_17ffc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1809c : word) = Some W_17ffc.
Proof. vm_refl. Qed.
Lemma D_17ffc : decode_any W_17ffc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
