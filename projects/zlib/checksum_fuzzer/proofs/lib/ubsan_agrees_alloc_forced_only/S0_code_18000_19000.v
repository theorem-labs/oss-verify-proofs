(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_checksum_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_18000 : bv 32 := 0xff010113.
Lemma F_18000 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180a0 : word) = Some W_18000.
Proof. vm_refl. Qed.
Lemma D_18000 : decode_any W_18000 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18004 : bv 32 := 0x00113423.
Lemma F_18004 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180a4 : word) = Some W_18004.
Proof. vm_refl. Qed.
Lemma D_18004 : decode_any W_18004 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18008 : bv 32 := 0x00813023.
Lemma F_18008 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180a8 : word) = Some W_18008.
Proof. vm_refl. Qed.
Lemma D_18008 : decode_any W_18008 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1800c : bv 32 := 0x00038517.
Lemma F_1800c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180ac : word) = Some W_1800c.
Proof. vm_refl. Qed.
Lemma D_1800c : decode_any W_1800c = Some (Auipc 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18010 : bv 32 := 0x10c50413.
Lemma F_18010 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180b0 : word) = Some W_18010.
Proof. vm_refl. Qed.
Lemma D_18010 : decode_any W_18010 = Some (OpImm ALU_ADD 8 10 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_18014 : bv 32 := 0x00040513.
Lemma F_18014 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180b4 : word) = Some W_18014.
Proof. vm_refl. Qed.
Lemma D_18014 : decode_any W_18014 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18018 : bv 32 := 0x258050ef.
Lemma F_18018 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180b8 : word) = Some W_18018.
Proof. vm_refl. Qed.
Lemma D_18018 : decode_any W_18018 = Some (Jal 1 21080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1801c : bv 32 := 0x00840513.
Lemma F_1801c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180bc : word) = Some W_1801c.
Proof. vm_refl. Qed.
Lemma D_1801c : decode_any W_1801c = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18020 : bv 32 := 0x00813083.
Lemma F_18020 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180c0 : word) = Some W_18020.
Proof. vm_refl. Qed.
Lemma D_18020 : decode_any W_18020 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18024 : bv 32 := 0x00013403.
Lemma F_18024 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180c4 : word) = Some W_18024.
Proof. vm_refl. Qed.
Lemma D_18024 : decode_any W_18024 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18028 : bv 32 := 0x01010113.
Lemma F_18028 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180c8 : word) = Some W_18028.
Proof. vm_refl. Qed.
Lemma D_18028 : decode_any W_18028 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1802c : bv 32 := 0x00008067.
Lemma F_1802c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180cc : word) = Some W_1802c.
Proof. vm_refl. Qed.
Lemma D_1802c : decode_any W_1802c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1803c : bv 32 := 0x00008067.
Lemma F_1803c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x180dc : word) = Some W_1803c.
Proof. vm_refl. Qed.
Lemma D_1803c : decode_any W_1803c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1806c : bv 32 := 0xf9010113.
Lemma F_1806c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1810c : word) = Some W_1806c.
Proof. vm_refl. Qed.
Lemma D_1806c : decode_any W_1806c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_18070 : bv 32 := 0x06113423.
Lemma F_18070 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18110 : word) = Some W_18070.
Proof. vm_refl. Qed.
Lemma D_18070 : decode_any W_18070 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_18074 : bv 32 := 0x06813023.
Lemma F_18074 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18114 : word) = Some W_18074.
Proof. vm_refl. Qed.
Lemma D_18074 : decode_any W_18074 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_18078 : bv 32 := 0x04913c23.
Lemma F_18078 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18118 : word) = Some W_18078.
Proof. vm_refl. Qed.
Lemma D_18078 : decode_any W_18078 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1807c : bv 32 := 0x05213823.
Lemma F_1807c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1811c : word) = Some W_1807c.
Proof. vm_refl. Qed.
Lemma D_1807c : decode_any W_1807c = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_18080 : bv 32 := 0x05313423.
Lemma F_18080 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18120 : word) = Some W_18080.
Proof. vm_refl. Qed.
Lemma D_18080 : decode_any W_18080 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_18084 : bv 32 := 0x05413023.
Lemma F_18084 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18124 : word) = Some W_18084.
Proof. vm_refl. Qed.
Lemma D_18084 : decode_any W_18084 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_18088 : bv 32 := 0x03513c23.
Lemma F_18088 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18128 : word) = Some W_18088.
Proof. vm_refl. Qed.
Lemma D_18088 : decode_any W_18088 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1808c : bv 32 := 0x03613823.
Lemma F_1808c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1812c : word) = Some W_1808c.
Proof. vm_refl. Qed.
Lemma D_1808c : decode_any W_1808c = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18090 : bv 32 := 0x00060413.
Lemma F_18090 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18130 : word) = Some W_18090.
Proof. vm_refl. Qed.
Lemma D_18090 : decode_any W_18090 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18094 : bv 32 := 0x00050493.
Lemma F_18094 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18134 : word) = Some W_18094.
Proof. vm_refl. Qed.
Lemma D_18094 : decode_any W_18094 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18098 : bv 32 := 0x00006517.
Lemma F_18098 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18138 : word) = Some W_18098.
Proof. vm_refl. Qed.
Lemma D_18098 : decode_any W_18098 = Some (Auipc 10 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1809c : bv 32 := 0x64853a83.
Lemma F_1809c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1813c : word) = Some W_1809c.
Proof. vm_refl. Qed.
Lemma D_1809c : decode_any W_1809c = Some (Load SZ8 true 21 10 1608, 4%Z).
Proof. vm_refl. Qed.

Definition W_180a0 : bv 32 := 0x000ab503.
Lemma F_180a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18140 : word) = Some W_180a0.
Proof. vm_refl. Qed.
Lemma D_180a0 : decode_any W_180a0 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180a4 : bv 32 := 0x02a13423.
Lemma F_180a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18144 : word) = Some W_180a4.
Proof. vm_refl. Qed.
Lemma D_180a4 : decode_any W_180a4 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_180a8 : bv 32 := 0x0284b503.
Lemma F_180a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18148 : word) = Some W_180a8.
Proof. vm_refl. Qed.
Lemma D_180a8 : decode_any W_180a8 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_180ac : bv 32 := 0x0384b603.
Lemma F_180ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1814c : word) = Some W_180ac.
Proof. vm_refl. Qed.
Lemma D_180ac : decode_any W_180ac = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_180b0 : bv 32 := 0x40c50b33.
Lemma F_180b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18150 : word) = Some W_180b0.
Proof. vm_refl. Qed.
Lemma D_180b0 : decode_any W_180b0 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_180b4 : bv 32 := 0x00c546b3.
Lemma F_180b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18154 : word) = Some W_180b4.
Proof. vm_refl. Qed.
Lemma D_180b4 : decode_any W_180b4 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_180b8 : bv 32 := 0x00c13423.
Lemma F_180b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18158 : word) = Some W_180b8.
Proof. vm_refl. Qed.
Lemma D_180b8 : decode_any W_180b8 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_180bc : bv 32 := 0x01613823.
Lemma F_180bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1815c : word) = Some W_180bc.
Proof. vm_refl. Qed.
Lemma D_180bc : decode_any W_180bc = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_180c0 : bv 32 := 0x00b13c23.
Lemma F_180c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18160 : word) = Some W_180c0.
Proof. vm_refl. Qed.
Lemma D_180c0 : decode_any W_180c0 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_180c4 : bv 32 := 0x02813023.
Lemma F_180c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18164 : word) = Some W_180c4.
Proof. vm_refl. Qed.
Lemma D_180c4 : decode_any W_180c4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_180c8 : bv 32 := 0x008b0b33.
Lemma F_180c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18168 : word) = Some W_180c8.
Proof. vm_refl. Qed.
Lemma D_180c8 : decode_any W_180c8 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_180cc : bv 32 := 0x00d03933.
Lemma F_180cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1816c : word) = Some W_180cc.
Proof. vm_refl. Qed.
Lemma D_180cc : decode_any W_180cc = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_180d0 : bv 32 := 0x00c50663.
Lemma F_180d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18170 : word) = Some W_180d0.
Proof. vm_refl. Qed.
Lemma D_180d0 : decode_any W_180d0 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_180d4 : bv 32 := 0x00810993.
Lemma F_180d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18174 : word) = Some W_180d4.
Proof. vm_refl. Qed.
Lemma D_180d4 : decode_any W_180d4 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_180d8 : bv 32 := 0x0080006f.
Lemma F_180d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18178 : word) = Some W_180d8.
Proof. vm_refl. Qed.
Lemma D_180d8 : decode_any W_180d8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_180dc : bv 32 := 0x01810993.
Lemma F_180dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1817c : word) = Some W_180dc.
Proof. vm_refl. Qed.
Lemma D_180dc : decode_any W_180dc = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e0 : bv 32 := 0x0784a503.
Lemma F_180e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18180 : word) = Some W_180e0.
Proof. vm_refl. Qed.
Lemma D_180e0 : decode_any W_180e0 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e4 : bv 32 := 0x00190913.
Lemma F_180e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18184 : word) = Some W_180e4.
Proof. vm_refl. Qed.
Lemma D_180e4 : decode_any W_180e4 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e8 : bv 32 := 0x04200893.
Lemma F_180e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18188 : word) = Some W_180e8.
Proof. vm_refl. Qed.
Lemma D_180e8 : decode_any W_180e8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_180ec : bv 32 := 0x00098593.
Lemma F_180ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1818c : word) = Some W_180ec.
Proof. vm_refl. Qed.
Lemma D_180ec : decode_any W_180ec = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f0 : bv 32 := 0x00090613.
Lemma F_180f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18190 : word) = Some W_180f0.
Proof. vm_refl. Qed.
Lemma D_180f0 : decode_any W_180f0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f4 : bv 32 := 0x00000073.
Lemma F_180f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18194 : word) = Some W_180f4.
Proof. vm_refl. Qed.
Lemma D_180f4 : decode_any W_180f4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_180f4 : is_ecall W_180f4 = true.
Proof. reflexivity. Qed.

Definition W_180f8 : bv 32 := 0xbadfd0ef.
Lemma F_180f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18198 : word) = Some W_180f8.
Proof. vm_refl. Qed.
Lemma D_180f8 : decode_any W_180f8 = Some (Jal 1 2087852, 4%Z).
Proof. vm_refl. Qed.

Definition W_180fc : bv 32 := 0x09651863.
Lemma F_180fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1819c : word) = Some W_180fc.
Proof. vm_refl. Qed.
Lemma D_180fc : decode_any W_180fc = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_18100 : bv 32 := 0x0584b503.
Lemma F_18100 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181a0 : word) = Some W_18100.
Proof. vm_refl. Qed.
Lemma D_18100 : decode_any W_18100 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_18104 : bv 32 := 0x0604b583.
Lemma F_18104 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181a4 : word) = Some W_18104.
Proof. vm_refl. Qed.
Lemma D_18104 : decode_any W_18104 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_18108 : bv 32 := 0x00b505b3.
Lemma F_18108 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181a8 : word) = Some W_18108.
Proof. vm_refl. Qed.
Lemma D_18108 : decode_any W_18108 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1810c : bv 32 := 0x02b4b023.
Lemma F_1810c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181ac : word) = Some W_1810c.
Proof. vm_refl. Qed.
Lemma D_1810c : decode_any W_1810c = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18110 : bv 32 := 0x02a4b423.
Lemma F_18110 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181b0 : word) = Some W_18110.
Proof. vm_refl. Qed.
Lemma D_18110 : decode_any W_18110 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18114 : bv 32 := 0x02a4bc23.
Lemma F_18114 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181b4 : word) = Some W_18114.
Proof. vm_refl. Qed.
Lemma D_18114 : decode_any W_18114 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18118 : bv 32 := 0x00040513.
Lemma F_18118 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181b8 : word) = Some W_18118.
Proof. vm_refl. Qed.
Lemma D_18118 : decode_any W_18118 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1811c : bv 32 := 0x000ab583.
Lemma F_1811c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181bc : word) = Some W_1811c.
Proof. vm_refl. Qed.
Lemma D_1811c : decode_any W_1811c = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18120 : bv 32 := 0x02813603.
Lemma F_18120 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181c0 : word) = Some W_18120.
Proof. vm_refl. Qed.
Lemma D_18120 : decode_any W_18120 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18124 : bv 32 := 0x0cc59a63.
Lemma F_18124 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181c4 : word) = Some W_18124.
Proof. vm_refl. Qed.
Lemma D_18124 : decode_any W_18124 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_18128 : bv 32 := 0x06813083.
Lemma F_18128 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181c8 : word) = Some W_18128.
Proof. vm_refl. Qed.
Lemma D_18128 : decode_any W_18128 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1812c : bv 32 := 0x06013403.
Lemma F_1812c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181cc : word) = Some W_1812c.
Proof. vm_refl. Qed.
Lemma D_1812c : decode_any W_1812c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_18130 : bv 32 := 0x05813483.
Lemma F_18130 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181d0 : word) = Some W_18130.
Proof. vm_refl. Qed.
Lemma D_18130 : decode_any W_18130 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_18134 : bv 32 := 0x05013903.
Lemma F_18134 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181d4 : word) = Some W_18134.
Proof. vm_refl. Qed.
Lemma D_18134 : decode_any W_18134 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_18138 : bv 32 := 0x04813983.
Lemma F_18138 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181d8 : word) = Some W_18138.
Proof. vm_refl. Qed.
Lemma D_18138 : decode_any W_18138 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1813c : bv 32 := 0x04013a03.
Lemma F_1813c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181dc : word) = Some W_1813c.
Proof. vm_refl. Qed.
Lemma D_1813c : decode_any W_1813c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_18140 : bv 32 := 0x03813a83.
Lemma F_18140 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181e0 : word) = Some W_18140.
Proof. vm_refl. Qed.
Lemma D_18140 : decode_any W_18140 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18144 : bv 32 := 0x03013b03.
Lemma F_18144 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181e4 : word) = Some W_18144.
Proof. vm_refl. Qed.
Lemma D_18144 : decode_any W_18144 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18148 : bv 32 := 0x07010113.
Lemma F_18148 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181e8 : word) = Some W_18148.
Proof. vm_refl. Qed.
Lemma D_18148 : decode_any W_18148 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1814c : bv 32 := 0x00008067.
Lemma F_1814c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181ec : word) = Some W_1814c.
Proof. vm_refl. Qed.
Lemma D_1814c : decode_any W_1814c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18150 : bv 32 := 0x00800713.
Lemma F_18150 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181f0 : word) = Some W_18150.
Proof. vm_refl. Qed.
Lemma D_18150 : decode_any W_18150 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18154 : bv 32 := 0x000a0593.
Lemma F_18154 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181f4 : word) = Some W_18154.
Proof. vm_refl. Qed.
Lemma D_18154 : decode_any W_18154 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18158 : bv 32 := 0x00e98733.
Lemma F_18158 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181f8 : word) = Some W_18158.
Proof. vm_refl. Qed.
Lemma D_18158 : decode_any W_18158 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1815c : bv 32 := 0x00073783.
Lemma F_1815c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x181fc : word) = Some W_1815c.
Proof. vm_refl. Qed.
Lemma D_1815c : decode_any W_1815c = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18160 : bv 32 := 0x40ab0b33.
Lemma F_18160 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18200 : word) = Some W_18160.
Proof. vm_refl. Qed.
Lemma D_18160 : decode_any W_18160 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18164 : bv 32 := 0x0784a503.
Lemma F_18164 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18204 : word) = Some W_18164.
Proof. vm_refl. Qed.
Lemma D_18164 : decode_any W_18164 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_18168 : bv 32 := 0x40c9093b.
Lemma F_18168 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18208 : word) = Some W_18168.
Proof. vm_refl. Qed.
Lemma D_18168 : decode_any W_18168 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1816c : bv 32 := 0x40d787b3.
Lemma F_1816c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1820c : word) = Some W_1816c.
Proof. vm_refl. Qed.
Lemma D_1816c : decode_any W_1816c = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18170 : bv 32 := 0x00f73023.
Lemma F_18170 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18210 : word) = Some W_18170.
Proof. vm_refl. Qed.
Lemma D_18170 : decode_any W_18170 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18174 : bv 32 := 0x04200893.
Lemma F_18174 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18214 : word) = Some W_18174.
Proof. vm_refl. Qed.
Lemma D_18174 : decode_any W_18174 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_18178 : bv 32 := 0x00090613.
Lemma F_18178 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18218 : word) = Some W_18178.
Proof. vm_refl. Qed.
Lemma D_18178 : decode_any W_18178 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1817c : bv 32 := 0x00000073.
Lemma F_1817c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1821c : word) = Some W_1817c.
Proof. vm_refl. Qed.
Lemma D_1817c : decode_any W_1817c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1817c : is_ecall W_1817c = true.
Proof. reflexivity. Qed.

Definition W_18180 : bv 32 := 0xb25fd0ef.
Lemma F_18180 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18220 : word) = Some W_18180.
Proof. vm_refl. Qed.
Lemma D_18180 : decode_any W_18180 = Some (Jal 1 2087716, 4%Z).
Proof. vm_refl. Qed.

Definition W_18184 : bv 32 := 0x000a0993.
Lemma F_18184 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18224 : word) = Some W_18184.
Proof. vm_refl. Qed.
Lemma D_18184 : decode_any W_18184 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18188 : bv 32 := 0xf7650ce3.
Lemma F_18188 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18228 : word) = Some W_18188.
Proof. vm_refl. Qed.
Lemma D_18188 : decode_any W_18188 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_1818c : bv 32 := 0x02054c63.
Lemma F_1818c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1822c : word) = Some W_1818c.
Proof. vm_refl. Qed.
Lemma D_1818c : decode_any W_1818c = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18190 : bv 32 := 0x0089b583.
Lemma F_18190 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18230 : word) = Some W_18190.
Proof. vm_refl. Qed.
Lemma D_18190 : decode_any W_18190 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18194 : bv 32 := 0x00a5b633.
Lemma F_18194 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18234 : word) = Some W_18194.
Proof. vm_refl. Qed.
Lemma D_18194 : decode_any W_18194 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18198 : bv 32 := 0x00461a13.
Lemma F_18198 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18238 : word) = Some W_18198.
Proof. vm_refl. Qed.
Lemma D_18198 : decode_any W_18198 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1819c : bv 32 := 0x01498a33.
Lemma F_1819c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1823c : word) = Some W_1819c.
Proof. vm_refl. Qed.
Lemma D_1819c : decode_any W_1819c = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_181a0 : bv 32 := 0x000a3703.
Lemma F_181a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18240 : word) = Some W_181a0.
Proof. vm_refl. Qed.
Lemma D_181a0 : decode_any W_181a0 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_181a4 : bv 32 := 0x40c006b3.
Lemma F_181a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18244 : word) = Some W_181a4.
Proof. vm_refl. Qed.
Lemma D_181a4 : decode_any W_181a4 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_181a8 : bv 32 := 0x00b6f6b3.
Lemma F_181a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18248 : word) = Some W_181a8.
Proof. vm_refl. Qed.
Lemma D_181a8 : decode_any W_181a8 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_181ac : bv 32 := 0x40d506b3.
Lemma F_181ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1824c : word) = Some W_181ac.
Proof. vm_refl. Qed.
Lemma D_181ac : decode_any W_181ac = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_181b0 : bv 32 := 0x00d70733.
Lemma F_181b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18250 : word) = Some W_181b0.
Proof. vm_refl. Qed.
Lemma D_181b0 : decode_any W_181b0 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_181b4 : bv 32 := 0x00ea3023.
Lemma F_181b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18254 : word) = Some W_181b4.
Proof. vm_refl. Qed.
Lemma D_181b4 : decode_any W_181b4 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_181b8 : bv 32 := 0xf8a5fce3.
Lemma F_181b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18258 : word) = Some W_181b8.
Proof. vm_refl. Qed.
Lemma D_181b8 : decode_any W_181b8 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_181bc : bv 32 := 0x01800713.
Lemma F_181bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1825c : word) = Some W_181bc.
Proof. vm_refl. Qed.
Lemma D_181bc : decode_any W_181bc = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_181c0 : bv 32 := 0xf95ff06f.
Lemma F_181c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x18260 : word) = Some W_181c0.
Proof. vm_refl. Qed.
Lemma D_181c0 : decode_any W_181c0 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
