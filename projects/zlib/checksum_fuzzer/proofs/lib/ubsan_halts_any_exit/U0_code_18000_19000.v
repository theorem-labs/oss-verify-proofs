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

Definition W_180e0 : bv 32 := 0xff010113.
Lemma F_180e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18180 : word) = Some W_180e0.
Proof. vm_refl. Qed.
Lemma D_180e0 : decode_any W_180e0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e4 : bv 32 := 0x00113423.
Lemma F_180e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18184 : word) = Some W_180e4.
Proof. vm_refl. Qed.
Lemma D_180e4 : decode_any W_180e4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e8 : bv 32 := 0x00813023.
Lemma F_180e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18188 : word) = Some W_180e8.
Proof. vm_refl. Qed.
Lemma D_180e8 : decode_any W_180e8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180ec : bv 32 := 0x198000ef.
Lemma F_180ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1818c : word) = Some W_180ec.
Proof. vm_refl. Qed.
Lemma D_180ec : decode_any W_180ec = Some (Jal 1 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f0 : bv 32 := 0x00053403.
Lemma F_180f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18190 : word) = Some W_180f0.
Proof. vm_refl. Qed.
Lemma D_180f0 : decode_any W_180f0 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f4 : bv 32 := 0x12041663.
Lemma F_180f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18194 : word) = Some W_180f4.
Proof. vm_refl. Qed.
Lemma D_180f4 : decode_any W_180f4 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f8 : bv 32 := 0x00038517.
Lemma F_180f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18198 : word) = Some W_180f8.
Proof. vm_refl. Qed.
Lemma D_180f8 : decode_any W_180f8 = Some (Auipc 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_180fc : bv 32 := 0x29853403.
Lemma F_180fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1819c : word) = Some W_180fc.
Proof. vm_refl. Qed.
Lemma D_180fc : decode_any W_180fc = Some (Load SZ8 true 8 10 664, 4%Z).
Proof. vm_refl. Qed.

Definition W_18100 : bv 32 := 0x04040a63.
Lemma F_18100 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x181a0 : word) = Some W_18100.
Proof. vm_refl. Qed.
Lemma D_18100 : decode_any W_18100 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_18154 : bv 32 := 0x00008517.
Lemma F_18154 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x181f4 : word) = Some W_18154.
Proof. vm_refl. Qed.
Lemma D_18154 : decode_any W_18154 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18158 : bv 32 := 0xa2c53403.
Lemma F_18158 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x181f8 : word) = Some W_18158.
Proof. vm_refl. Qed.
Lemma D_18158 : decode_any W_18158 = Some (Load SZ8 true 8 10 2604, 4%Z).
Proof. vm_refl. Qed.

Definition W_1815c : bv 32 := 0x04040a63.
Lemma F_1815c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x181fc : word) = Some W_1815c.
Proof. vm_refl. Qed.
Lemma D_1815c : decode_any W_1815c = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_18160 : bv 32 := 0x08c42503.
Lemma F_18160 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18200 : word) = Some W_18160.
Proof. vm_refl. Qed.
Lemma D_18160 : decode_any W_18160 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_18164 : bv 32 := 0x00054663.
Lemma F_18164 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18204 : word) = Some W_18164.
Proof. vm_refl. Qed.
Lemma D_18164 : decode_any W_18164 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18170 : bv 32 := 0x02843503.
Lemma F_18170 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18210 : word) = Some W_18170.
Proof. vm_refl. Qed.
Lemma D_18170 : decode_any W_18170 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18174 : bv 32 := 0x03843583.
Lemma F_18174 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18214 : word) = Some W_18174.
Proof. vm_refl. Qed.
Lemma D_18174 : decode_any W_18174 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18178 : bv 32 := 0x00b50c63.
Lemma F_18178 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18218 : word) = Some W_18178.
Proof. vm_refl. Qed.
Lemma D_18178 : decode_any W_18178 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1817c : bv 32 := 0x04843683.
Lemma F_1817c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1821c : word) = Some W_1817c.
Proof. vm_refl. Qed.
Lemma D_1817c : decode_any W_1817c = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_18180 : bv 32 := 0x00040513.
Lemma F_18180 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18220 : word) = Some W_18180.
Proof. vm_refl. Qed.
Lemma D_18180 : decode_any W_18180 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18184 : bv 32 := 0x00000593.
Lemma F_18184 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18224 : word) = Some W_18184.
Proof. vm_refl. Qed.
Lemma D_18184 : decode_any W_18184 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18188 : bv 32 := 0x00000613.
Lemma F_18188 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18228 : word) = Some W_18188.
Proof. vm_refl. Qed.
Lemma D_18188 : decode_any W_18188 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1818c : bv 32 := 0x000680e7.
Lemma F_1818c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1822c : word) = Some W_1818c.
Proof. vm_refl. Qed.
Lemma D_1818c : decode_any W_1818c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18190 : bv 32 := 0x00843503.
Lemma F_18190 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18230 : word) = Some W_18190.
Proof. vm_refl. Qed.
Lemma D_18190 : decode_any W_18190 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18194 : bv 32 := 0x01043583.
Lemma F_18194 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18234 : word) = Some W_18194.
Proof. vm_refl. Qed.
Lemma D_18194 : decode_any W_18194 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18198 : bv 32 := 0x00b50c63.
Lemma F_18198 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18238 : word) = Some W_18198.
Proof. vm_refl. Qed.
Lemma D_18198 : decode_any W_18198 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_181b0 : bv 32 := 0x00008517.
Lemma F_181b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18250 : word) = Some W_181b0.
Proof. vm_refl. Qed.
Lemma D_181b0 : decode_any W_181b0 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_181b4 : bv 32 := 0x8e053403.
Lemma F_181b4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18254 : word) = Some W_181b4.
Proof. vm_refl. Qed.
Lemma D_181b4 : decode_any W_181b4 = Some (Load SZ8 true 8 10 2272, 4%Z).
Proof. vm_refl. Qed.

Definition W_181b8 : bv 32 := 0x0a040e63.
Lemma F_181b8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18258 : word) = Some W_181b8.
Proof. vm_refl. Qed.
Lemma D_181b8 : decode_any W_181b8 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_181bc : bv 32 := 0x08c42503.
Lemma F_181bc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1825c : word) = Some W_181bc.
Proof. vm_refl. Qed.
Lemma D_181bc : decode_any W_181bc = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_181c0 : bv 32 := 0x00054663.
Lemma F_181c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18260 : word) = Some W_181c0.
Proof. vm_refl. Qed.
Lemma D_181c0 : decode_any W_181c0 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_181cc : bv 32 := 0x02843503.
Lemma F_181cc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1826c : word) = Some W_181cc.
Proof. vm_refl. Qed.
Lemma D_181cc : decode_any W_181cc = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_181d0 : bv 32 := 0x03843583.
Lemma F_181d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18270 : word) = Some W_181d0.
Proof. vm_refl. Qed.
Lemma D_181d0 : decode_any W_181d0 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_181d4 : bv 32 := 0x00b50c63.
Lemma F_181d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18274 : word) = Some W_181d4.
Proof. vm_refl. Qed.
Lemma D_181d4 : decode_any W_181d4 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_181ec : bv 32 := 0x00843503.
Lemma F_181ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1828c : word) = Some W_181ec.
Proof. vm_refl. Qed.
Lemma D_181ec : decode_any W_181ec = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_181f0 : bv 32 := 0x01043583.
Lemma F_181f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18290 : word) = Some W_181f0.
Proof. vm_refl. Qed.
Lemma D_181f0 : decode_any W_181f0 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_181f4 : bv 32 := 0x08b50063.
Lemma F_181f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18294 : word) = Some W_181f4.
Proof. vm_refl. Qed.
Lemma D_181f4 : decode_any W_181f4 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_18274 : bv 32 := 0x00813083.
Lemma F_18274 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18314 : word) = Some W_18274.
Proof. vm_refl. Qed.
Lemma D_18274 : decode_any W_18274 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18278 : bv 32 := 0x00013403.
Lemma F_18278 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18318 : word) = Some W_18278.
Proof. vm_refl. Qed.
Lemma D_18278 : decode_any W_18278 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1827c : bv 32 := 0x01010113.
Lemma F_1827c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1831c : word) = Some W_1827c.
Proof. vm_refl. Qed.
Lemma D_1827c : decode_any W_1827c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18280 : bv 32 := 0x00008067.
Lemma F_18280 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18320 : word) = Some W_18280.
Proof. vm_refl. Qed.
Lemma D_18280 : decode_any W_18280 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18284 : bv 32 := 0xff010113.
Lemma F_18284 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18324 : word) = Some W_18284.
Proof. vm_refl. Qed.
Lemma D_18284 : decode_any W_18284 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18288 : bv 32 := 0x00113423.
Lemma F_18288 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18328 : word) = Some W_18288.
Proof. vm_refl. Qed.
Lemma D_18288 : decode_any W_18288 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1828c : bv 32 := 0x00813023.
Lemma F_1828c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1832c : word) = Some W_1828c.
Proof. vm_refl. Qed.
Lemma D_1828c : decode_any W_1828c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18290 : bv 32 := 0x00038517.
Lemma F_18290 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18330 : word) = Some W_18290.
Proof. vm_refl. Qed.
Lemma D_18290 : decode_any W_18290 = Some (Auipc 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18294 : bv 32 := 0x10850413.
Lemma F_18294 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18334 : word) = Some W_18294.
Proof. vm_refl. Qed.
Lemma D_18294 : decode_any W_18294 = Some (OpImm ALU_ADD 8 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_18298 : bv 32 := 0x00040513.
Lemma F_18298 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18338 : word) = Some W_18298.
Proof. vm_refl. Qed.
Lemma D_18298 : decode_any W_18298 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1829c : bv 32 := 0x258050ef.
Lemma F_1829c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1833c : word) = Some W_1829c.
Proof. vm_refl. Qed.
Lemma D_1829c : decode_any W_1829c = Some (Jal 1 21080, 4%Z).
Proof. vm_refl. Qed.

Definition W_182a0 : bv 32 := 0x00840513.
Lemma F_182a0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18340 : word) = Some W_182a0.
Proof. vm_refl. Qed.
Lemma D_182a0 : decode_any W_182a0 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_182a4 : bv 32 := 0x00813083.
Lemma F_182a4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18344 : word) = Some W_182a4.
Proof. vm_refl. Qed.
Lemma D_182a4 : decode_any W_182a4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_182a8 : bv 32 := 0x00013403.
Lemma F_182a8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18348 : word) = Some W_182a8.
Proof. vm_refl. Qed.
Lemma D_182a8 : decode_any W_182a8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_182ac : bv 32 := 0x01010113.
Lemma F_182ac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1834c : word) = Some W_182ac.
Proof. vm_refl. Qed.
Lemma D_182ac : decode_any W_182ac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_182b0 : bv 32 := 0x00008067.
Lemma F_182b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18350 : word) = Some W_182b0.
Proof. vm_refl. Qed.
Lemma D_182b0 : decode_any W_182b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_182c0 : bv 32 := 0x00008067.
Lemma F_182c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18360 : word) = Some W_182c0.
Proof. vm_refl. Qed.
Lemma D_182c0 : decode_any W_182c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_182f0 : bv 32 := 0xf9010113.
Lemma F_182f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18390 : word) = Some W_182f0.
Proof. vm_refl. Qed.
Lemma D_182f0 : decode_any W_182f0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_182f4 : bv 32 := 0x06113423.
Lemma F_182f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18394 : word) = Some W_182f4.
Proof. vm_refl. Qed.
Lemma D_182f4 : decode_any W_182f4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_182f8 : bv 32 := 0x06813023.
Lemma F_182f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18398 : word) = Some W_182f8.
Proof. vm_refl. Qed.
Lemma D_182f8 : decode_any W_182f8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_182fc : bv 32 := 0x04913c23.
Lemma F_182fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1839c : word) = Some W_182fc.
Proof. vm_refl. Qed.
Lemma D_182fc : decode_any W_182fc = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_18300 : bv 32 := 0x05213823.
Lemma F_18300 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183a0 : word) = Some W_18300.
Proof. vm_refl. Qed.
Lemma D_18300 : decode_any W_18300 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_18304 : bv 32 := 0x05313423.
Lemma F_18304 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183a4 : word) = Some W_18304.
Proof. vm_refl. Qed.
Lemma D_18304 : decode_any W_18304 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_18308 : bv 32 := 0x05413023.
Lemma F_18308 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183a8 : word) = Some W_18308.
Proof. vm_refl. Qed.
Lemma D_18308 : decode_any W_18308 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1830c : bv 32 := 0x03513c23.
Lemma F_1830c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183ac : word) = Some W_1830c.
Proof. vm_refl. Qed.
Lemma D_1830c : decode_any W_1830c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18310 : bv 32 := 0x03613823.
Lemma F_18310 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183b0 : word) = Some W_18310.
Proof. vm_refl. Qed.
Lemma D_18310 : decode_any W_18310 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18314 : bv 32 := 0x00060413.
Lemma F_18314 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183b4 : word) = Some W_18314.
Proof. vm_refl. Qed.
Lemma D_18314 : decode_any W_18314 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18318 : bv 32 := 0x00050493.
Lemma F_18318 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183b8 : word) = Some W_18318.
Proof. vm_refl. Qed.
Lemma D_18318 : decode_any W_18318 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1831c : bv 32 := 0x00006517.
Lemma F_1831c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183bc : word) = Some W_1831c.
Proof. vm_refl. Qed.
Lemma D_1831c : decode_any W_1831c = Some (Auipc 10 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_18320 : bv 32 := 0x64c53a83.
Lemma F_18320 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183c0 : word) = Some W_18320.
Proof. vm_refl. Qed.
Lemma D_18320 : decode_any W_18320 = Some (Load SZ8 true 21 10 1612, 4%Z).
Proof. vm_refl. Qed.

Definition W_18324 : bv 32 := 0x000ab503.
Lemma F_18324 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183c4 : word) = Some W_18324.
Proof. vm_refl. Qed.
Lemma D_18324 : decode_any W_18324 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18328 : bv 32 := 0x02a13423.
Lemma F_18328 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183c8 : word) = Some W_18328.
Proof. vm_refl. Qed.
Lemma D_18328 : decode_any W_18328 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1832c : bv 32 := 0x0284b503.
Lemma F_1832c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183cc : word) = Some W_1832c.
Proof. vm_refl. Qed.
Lemma D_1832c : decode_any W_1832c = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18330 : bv 32 := 0x0384b603.
Lemma F_18330 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183d0 : word) = Some W_18330.
Proof. vm_refl. Qed.
Lemma D_18330 : decode_any W_18330 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18334 : bv 32 := 0x40c50b33.
Lemma F_18334 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183d4 : word) = Some W_18334.
Proof. vm_refl. Qed.
Lemma D_18334 : decode_any W_18334 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18338 : bv 32 := 0x00c546b3.
Lemma F_18338 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183d8 : word) = Some W_18338.
Proof. vm_refl. Qed.
Lemma D_18338 : decode_any W_18338 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1833c : bv 32 := 0x00c13423.
Lemma F_1833c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183dc : word) = Some W_1833c.
Proof. vm_refl. Qed.
Lemma D_1833c : decode_any W_1833c = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18340 : bv 32 := 0x01613823.
Lemma F_18340 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183e0 : word) = Some W_18340.
Proof. vm_refl. Qed.
Lemma D_18340 : decode_any W_18340 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18344 : bv 32 := 0x00b13c23.
Lemma F_18344 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183e4 : word) = Some W_18344.
Proof. vm_refl. Qed.
Lemma D_18344 : decode_any W_18344 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18348 : bv 32 := 0x02813023.
Lemma F_18348 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183e8 : word) = Some W_18348.
Proof. vm_refl. Qed.
Lemma D_18348 : decode_any W_18348 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1834c : bv 32 := 0x008b0b33.
Lemma F_1834c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183ec : word) = Some W_1834c.
Proof. vm_refl. Qed.
Lemma D_1834c : decode_any W_1834c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18350 : bv 32 := 0x00d03933.
Lemma F_18350 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183f0 : word) = Some W_18350.
Proof. vm_refl. Qed.
Lemma D_18350 : decode_any W_18350 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18354 : bv 32 := 0x00c50663.
Lemma F_18354 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183f4 : word) = Some W_18354.
Proof. vm_refl. Qed.
Lemma D_18354 : decode_any W_18354 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18358 : bv 32 := 0x00810993.
Lemma F_18358 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183f8 : word) = Some W_18358.
Proof. vm_refl. Qed.
Lemma D_18358 : decode_any W_18358 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1835c : bv 32 := 0x0080006f.
Lemma F_1835c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x183fc : word) = Some W_1835c.
Proof. vm_refl. Qed.
Lemma D_1835c : decode_any W_1835c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18360 : bv 32 := 0x01810993.
Lemma F_18360 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18400 : word) = Some W_18360.
Proof. vm_refl. Qed.
Lemma D_18360 : decode_any W_18360 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18364 : bv 32 := 0x0784a503.
Lemma F_18364 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18404 : word) = Some W_18364.
Proof. vm_refl. Qed.
Lemma D_18364 : decode_any W_18364 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_18368 : bv 32 := 0x00190913.
Lemma F_18368 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18408 : word) = Some W_18368.
Proof. vm_refl. Qed.
Lemma D_18368 : decode_any W_18368 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1836c : bv 32 := 0x04200893.
Lemma F_1836c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1840c : word) = Some W_1836c.
Proof. vm_refl. Qed.
Lemma D_1836c : decode_any W_1836c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_18370 : bv 32 := 0x00098593.
Lemma F_18370 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18410 : word) = Some W_18370.
Proof. vm_refl. Qed.
Lemma D_18370 : decode_any W_18370 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18374 : bv 32 := 0x00090613.
Lemma F_18374 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18414 : word) = Some W_18374.
Proof. vm_refl. Qed.
Lemma D_18374 : decode_any W_18374 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18378 : bv 32 := 0x00000073.
Lemma F_18378 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18418 : word) = Some W_18378.
Proof. vm_refl. Qed.
Lemma D_18378 : decode_any W_18378 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_18378 : is_ecall W_18378 = true.
Proof. reflexivity. Qed.

Definition W_1837c : bv 32 := 0xbadfd0ef.
Lemma F_1837c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1841c : word) = Some W_1837c.
Proof. vm_refl. Qed.
Lemma D_1837c : decode_any W_1837c = Some (Jal 1 2087852, 4%Z).
Proof. vm_refl. Qed.

Definition W_18380 : bv 32 := 0x09651863.
Lemma F_18380 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18420 : word) = Some W_18380.
Proof. vm_refl. Qed.
Lemma D_18380 : decode_any W_18380 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_18384 : bv 32 := 0x0584b503.
Lemma F_18384 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18424 : word) = Some W_18384.
Proof. vm_refl. Qed.
Lemma D_18384 : decode_any W_18384 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_18388 : bv 32 := 0x0604b583.
Lemma F_18388 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18428 : word) = Some W_18388.
Proof. vm_refl. Qed.
Lemma D_18388 : decode_any W_18388 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1838c : bv 32 := 0x00b505b3.
Lemma F_1838c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1842c : word) = Some W_1838c.
Proof. vm_refl. Qed.
Lemma D_1838c : decode_any W_1838c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18390 : bv 32 := 0x02b4b023.
Lemma F_18390 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18430 : word) = Some W_18390.
Proof. vm_refl. Qed.
Lemma D_18390 : decode_any W_18390 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18394 : bv 32 := 0x02a4b423.
Lemma F_18394 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18434 : word) = Some W_18394.
Proof. vm_refl. Qed.
Lemma D_18394 : decode_any W_18394 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18398 : bv 32 := 0x02a4bc23.
Lemma F_18398 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18438 : word) = Some W_18398.
Proof. vm_refl. Qed.
Lemma D_18398 : decode_any W_18398 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1839c : bv 32 := 0x00040513.
Lemma F_1839c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1843c : word) = Some W_1839c.
Proof. vm_refl. Qed.
Lemma D_1839c : decode_any W_1839c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183a0 : bv 32 := 0x000ab583.
Lemma F_183a0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18440 : word) = Some W_183a0.
Proof. vm_refl. Qed.
Lemma D_183a0 : decode_any W_183a0 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183a4 : bv 32 := 0x02813603.
Lemma F_183a4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18444 : word) = Some W_183a4.
Proof. vm_refl. Qed.
Lemma D_183a4 : decode_any W_183a4 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_183a8 : bv 32 := 0x0cc59a63.
Lemma F_183a8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18448 : word) = Some W_183a8.
Proof. vm_refl. Qed.
Lemma D_183a8 : decode_any W_183a8 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_183ac : bv 32 := 0x06813083.
Lemma F_183ac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1844c : word) = Some W_183ac.
Proof. vm_refl. Qed.
Lemma D_183ac : decode_any W_183ac = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_183b0 : bv 32 := 0x06013403.
Lemma F_183b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18450 : word) = Some W_183b0.
Proof. vm_refl. Qed.
Lemma D_183b0 : decode_any W_183b0 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_183b4 : bv 32 := 0x05813483.
Lemma F_183b4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18454 : word) = Some W_183b4.
Proof. vm_refl. Qed.
Lemma D_183b4 : decode_any W_183b4 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_183b8 : bv 32 := 0x05013903.
Lemma F_183b8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18458 : word) = Some W_183b8.
Proof. vm_refl. Qed.
Lemma D_183b8 : decode_any W_183b8 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_183bc : bv 32 := 0x04813983.
Lemma F_183bc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1845c : word) = Some W_183bc.
Proof. vm_refl. Qed.
Lemma D_183bc : decode_any W_183bc = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_183c0 : bv 32 := 0x04013a03.
Lemma F_183c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18460 : word) = Some W_183c0.
Proof. vm_refl. Qed.
Lemma D_183c0 : decode_any W_183c0 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_183c4 : bv 32 := 0x03813a83.
Lemma F_183c4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18464 : word) = Some W_183c4.
Proof. vm_refl. Qed.
Lemma D_183c4 : decode_any W_183c4 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_183c8 : bv 32 := 0x03013b03.
Lemma F_183c8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18468 : word) = Some W_183c8.
Proof. vm_refl. Qed.
Lemma D_183c8 : decode_any W_183c8 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_183cc : bv 32 := 0x07010113.
Lemma F_183cc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1846c : word) = Some W_183cc.
Proof. vm_refl. Qed.
Lemma D_183cc : decode_any W_183cc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_183d0 : bv 32 := 0x00008067.
Lemma F_183d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18470 : word) = Some W_183d0.
Proof. vm_refl. Qed.
Lemma D_183d0 : decode_any W_183d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183d4 : bv 32 := 0x00800713.
Lemma F_183d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18474 : word) = Some W_183d4.
Proof. vm_refl. Qed.
Lemma D_183d4 : decode_any W_183d4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_183d8 : bv 32 := 0x000a0593.
Lemma F_183d8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18478 : word) = Some W_183d8.
Proof. vm_refl. Qed.
Lemma D_183d8 : decode_any W_183d8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183dc : bv 32 := 0x00e98733.
Lemma F_183dc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1847c : word) = Some W_183dc.
Proof. vm_refl. Qed.
Lemma D_183dc : decode_any W_183dc = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_183e0 : bv 32 := 0x00073783.
Lemma F_183e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18480 : word) = Some W_183e0.
Proof. vm_refl. Qed.
Lemma D_183e0 : decode_any W_183e0 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183e4 : bv 32 := 0x40ab0b33.
Lemma F_183e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18484 : word) = Some W_183e4.
Proof. vm_refl. Qed.
Lemma D_183e4 : decode_any W_183e4 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_183e8 : bv 32 := 0x0784a503.
Lemma F_183e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18488 : word) = Some W_183e8.
Proof. vm_refl. Qed.
Lemma D_183e8 : decode_any W_183e8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_183ec : bv 32 := 0x40c9093b.
Lemma F_183ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1848c : word) = Some W_183ec.
Proof. vm_refl. Qed.
Lemma D_183ec : decode_any W_183ec = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_183f0 : bv 32 := 0x40d787b3.
Lemma F_183f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18490 : word) = Some W_183f0.
Proof. vm_refl. Qed.
Lemma D_183f0 : decode_any W_183f0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_183f4 : bv 32 := 0x00f73023.
Lemma F_183f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18494 : word) = Some W_183f4.
Proof. vm_refl. Qed.
Lemma D_183f4 : decode_any W_183f4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_183f8 : bv 32 := 0x04200893.
Lemma F_183f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x18498 : word) = Some W_183f8.
Proof. vm_refl. Qed.
Lemma D_183f8 : decode_any W_183f8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_183fc : bv 32 := 0x00090613.
Lemma F_183fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1849c : word) = Some W_183fc.
Proof. vm_refl. Qed.
Lemma D_183fc : decode_any W_183fc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18400 : bv 32 := 0x00000073.
Lemma F_18400 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184a0 : word) = Some W_18400.
Proof. vm_refl. Qed.
Lemma D_18400 : decode_any W_18400 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_18400 : is_ecall W_18400 = true.
Proof. reflexivity. Qed.

Definition W_18404 : bv 32 := 0xb25fd0ef.
Lemma F_18404 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184a4 : word) = Some W_18404.
Proof. vm_refl. Qed.
Lemma D_18404 : decode_any W_18404 = Some (Jal 1 2087716, 4%Z).
Proof. vm_refl. Qed.

Definition W_18408 : bv 32 := 0x000a0993.
Lemma F_18408 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184a8 : word) = Some W_18408.
Proof. vm_refl. Qed.
Lemma D_18408 : decode_any W_18408 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1840c : bv 32 := 0xf7650ce3.
Lemma F_1840c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184ac : word) = Some W_1840c.
Proof. vm_refl. Qed.
Lemma D_1840c : decode_any W_1840c = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_18410 : bv 32 := 0x02054c63.
Lemma F_18410 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184b0 : word) = Some W_18410.
Proof. vm_refl. Qed.
Lemma D_18410 : decode_any W_18410 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18414 : bv 32 := 0x0089b583.
Lemma F_18414 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184b4 : word) = Some W_18414.
Proof. vm_refl. Qed.
Lemma D_18414 : decode_any W_18414 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18418 : bv 32 := 0x00a5b633.
Lemma F_18418 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184b8 : word) = Some W_18418.
Proof. vm_refl. Qed.
Lemma D_18418 : decode_any W_18418 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1841c : bv 32 := 0x00461a13.
Lemma F_1841c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184bc : word) = Some W_1841c.
Proof. vm_refl. Qed.
Lemma D_1841c : decode_any W_1841c = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18420 : bv 32 := 0x01498a33.
Lemma F_18420 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184c0 : word) = Some W_18420.
Proof. vm_refl. Qed.
Lemma D_18420 : decode_any W_18420 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_18424 : bv 32 := 0x000a3703.
Lemma F_18424 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184c4 : word) = Some W_18424.
Proof. vm_refl. Qed.
Lemma D_18424 : decode_any W_18424 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18428 : bv 32 := 0x40c006b3.
Lemma F_18428 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184c8 : word) = Some W_18428.
Proof. vm_refl. Qed.
Lemma D_18428 : decode_any W_18428 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1842c : bv 32 := 0x00b6f6b3.
Lemma F_1842c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184cc : word) = Some W_1842c.
Proof. vm_refl. Qed.
Lemma D_1842c : decode_any W_1842c = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18430 : bv 32 := 0x40d506b3.
Lemma F_18430 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184d0 : word) = Some W_18430.
Proof. vm_refl. Qed.
Lemma D_18430 : decode_any W_18430 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18434 : bv 32 := 0x00d70733.
Lemma F_18434 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184d4 : word) = Some W_18434.
Proof. vm_refl. Qed.
Lemma D_18434 : decode_any W_18434 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18438 : bv 32 := 0x00ea3023.
Lemma F_18438 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184d8 : word) = Some W_18438.
Proof. vm_refl. Qed.
Lemma D_18438 : decode_any W_18438 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1843c : bv 32 := 0xf8a5fce3.
Lemma F_1843c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184dc : word) = Some W_1843c.
Proof. vm_refl. Qed.
Lemma D_1843c : decode_any W_1843c = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_18440 : bv 32 := 0x01800713.
Lemma F_18440 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184e0 : word) = Some W_18440.
Proof. vm_refl. Qed.
Lemma D_18440 : decode_any W_18440 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18444 : bv 32 := 0xf95ff06f.
Lemma F_18444 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x184e4 : word) = Some W_18444.
Proof. vm_refl. Qed.
Lemma D_18444 : decode_any W_18444 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
