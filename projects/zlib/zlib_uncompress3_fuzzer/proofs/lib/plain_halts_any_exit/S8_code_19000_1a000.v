(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_19000 : bv 32 := 0x00000593.
Lemma F_19000 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19130 : word) = Some W_19000.
Proof. vm_refl. Qed.
Lemma D_19000 : decode_any W_19000 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19004 : bv 32 := 0x00020613.
Lemma F_19004 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19134 : word) = Some W_19004.
Proof. vm_refl. Qed.
Lemma D_19004 : decode_any W_19004 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19008 : bv 32 := 0xf5862603.
Lemma F_19008 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19138 : word) = Some W_19008.
Proof. vm_refl. Qed.
Lemma D_19008 : decode_any W_19008 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_1900c : bv 32 := 0x0007a697.
Lemma F_1900c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1913c : word) = Some W_1900c.
Proof. vm_refl. Qed.
Lemma D_1900c : decode_any W_1900c = Some (Auipc 13 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_19010 : bv 32 := 0x10468693.
Lemma F_19010 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19140 : word) = Some W_19010.
Proof. vm_refl. Qed.
Lemma D_19010 : decode_any W_19010 = Some (OpImm ALU_ADD 13 13 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_19014 : bv 32 := 0x1606a72f.
Lemma F_19014 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19144 : word) = Some W_19014.
Proof. vm_refl. Qed.
Lemma D_19014 : decode_any W_19014 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_19018 : bv 32 := 0x00b71663.
Lemma F_19018 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19148 : word) = Some W_19018.
Proof. vm_refl. Qed.
Lemma D_19018 : decode_any W_19018 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1901c : bv 32 := 0x1ec6a7af.
Lemma F_1901c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1914c : word) = Some W_1901c.
Proof. vm_refl. Qed.
Lemma D_1901c : decode_any W_1901c = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19020 : bv 32 := 0xfe079ae3.
Lemma F_19020 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19150 : word) = Some W_19020.
Proof. vm_refl. Qed.
Lemma D_19020 : decode_any W_19020 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_19024 : bv 32 := 0x0007059b.
Lemma F_19024 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19154 : word) = Some W_19024.
Proof. vm_refl. Qed.
Lemma D_19024 : decode_any W_19024 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19028 : bv 32 := 0x02c58263.
Lemma F_19028 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19158 : word) = Some W_19028.
Proof. vm_refl. Qed.
Lemma D_19028 : decode_any W_19028 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1902c : bv 32 := 0x02058263.
Lemma F_1902c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1915c : word) = Some W_1902c.
Proof. vm_refl. Qed.
Lemma D_1902c : decode_any W_1902c = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_19030 : bv 32 := 0x04900893.
Lemma F_19030 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19160 : word) = Some W_19030.
Proof. vm_refl. Qed.
Lemma D_19030 : decode_any W_19030 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_19034 : bv 32 := 0x00000593.
Lemma F_19034 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19164 : word) = Some W_19034.
Proof. vm_refl. Qed.
Lemma D_19034 : decode_any W_19034 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19038 : bv 32 := 0x00000613.
Lemma F_19038 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19168 : word) = Some W_19038.
Proof. vm_refl. Qed.
Lemma D_19038 : decode_any W_19038 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1903c : bv 32 := 0x00000693.
Lemma F_1903c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1916c : word) = Some W_1903c.
Proof. vm_refl. Qed.
Lemma D_1903c : decode_any W_1903c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19040 : bv 32 := 0x00000513.
Lemma F_19040 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19170 : word) = Some W_19040.
Proof. vm_refl. Qed.
Lemma D_19040 : decode_any W_19040 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19044 : bv 32 := 0x00000073.
Lemma F_19044 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19174 : word) = Some W_19044.
Proof. vm_refl. Qed.
Lemma D_19044 : decode_any W_19044 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_19044 : is_ecall W_19044 = true.
Proof. reflexivity. Qed.

Definition W_19048 : bv 32 := 0xff9ff06f.
Lemma F_19048 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19178 : word) = Some W_19048.
Proof. vm_refl. Qed.
Lemma D_19048 : decode_any W_19048 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_1904c : bv 32 := 0x00000023.
Lemma F_1904c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1917c : word) = Some W_1904c.
Proof. vm_refl. Qed.
Lemma D_1904c : decode_any W_1904c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19050 : bv 32 := 0x00050413.
Lemma F_19050 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19180 : word) = Some W_19050.
Proof. vm_refl. Qed.
Lemma D_19050 : decode_any W_19050 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19054 : bv 32 := 0xdbdff0ef.
Lemma F_19054 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19184 : word) = Some W_19054.
Proof. vm_refl. Qed.
Lemma D_19054 : decode_any W_19054 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_19058 : bv 32 := 0xf51ff0ef.
Lemma F_19058 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19188 : word) = Some W_19058.
Proof. vm_refl. Qed.
Lemma D_19058 : decode_any W_19058 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_1905c : bv 32 := 0x258020ef.
Lemma F_1905c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1918c : word) = Some W_1905c.
Proof. vm_refl. Qed.
Lemma D_1905c : decode_any W_1905c = Some (Jal 1 8792, 4%Z).
Proof. vm_refl. Qed.

Definition W_19060 : bv 32 := 0x00040513.
Lemma F_19060 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19190 : word) = Some W_19060.
Proof. vm_refl. Qed.
Lemma D_19060 : decode_any W_19060 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19064 : bv 32 := 0x004000ef.
Lemma F_19064 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19194 : word) = Some W_19064.
Proof. vm_refl. Qed.
Lemma D_19064 : decode_any W_19064 = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_19068 : bv 32 := 0x00050593.
Lemma F_19068 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19198 : word) = Some W_19068.
Proof. vm_refl. Qed.
Lemma D_19068 : decode_any W_19068 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1906c : bv 32 := 0x05e00893.
Lemma F_1906c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1919c : word) = Some W_1906c.
Proof. vm_refl. Qed.
Lemma D_1906c : decode_any W_1906c = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_19070 : bv 32 := 0x00000073.
Lemma F_19070 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x191a0 : word) = Some W_19070.
Proof. vm_refl. Qed.
Lemma D_19070 : decode_any W_19070 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_19070 : is_ecall W_19070 = true.
Proof. reflexivity. Qed.

Definition W_19168 : bv 32 := 0xff010113.
Lemma F_19168 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19298 : word) = Some W_19168.
Proof. vm_refl. Qed.
Lemma D_19168 : decode_any W_19168 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1916c : bv 32 := 0x00113423.
Lemma F_1916c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1929c : word) = Some W_1916c.
Proof. vm_refl. Qed.
Lemma D_1916c : decode_any W_1916c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19170 : bv 32 := 0x00050e63.
Lemma F_19170 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192a0 : word) = Some W_19170.
Proof. vm_refl. Qed.
Lemma D_19170 : decode_any W_19170 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_19174 : bv 32 := 0x00050593.
Lemma F_19174 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192a4 : word) = Some W_19174.
Proof. vm_refl. Qed.
Lemma D_19174 : decode_any W_19174 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19178 : bv 32 := 0x00009517.
Lemma F_19178 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192a8 : word) = Some W_19178.
Proof. vm_refl. Qed.
Lemma D_19178 : decode_any W_19178 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1917c : bv 32 := 0x9c053503.
Lemma F_1917c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192ac : word) = Some W_1917c.
Proof. vm_refl. Qed.
Lemma D_1917c : decode_any W_1917c = Some (Load SZ8 true 10 10 2496, 4%Z).
Proof. vm_refl. Qed.

Definition W_19180 : bv 32 := 0x00800613.
Lemma F_19180 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192b0 : word) = Some W_19180.
Proof. vm_refl. Qed.
Lemma D_19180 : decode_any W_19180 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19184 : bv 32 := 0x739060ef.
Lemma F_19184 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192b4 : word) = Some W_19184.
Proof. vm_refl. Qed.
Lemma D_19184 : decode_any W_19184 = Some (Jal 1 28472, 4%Z).
Proof. vm_refl. Qed.

Definition W_19188 : bv 32 := 0x01c0006f.
Lemma F_19188 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192b8 : word) = Some W_19188.
Proof. vm_refl. Qed.
Lemma D_19188 : decode_any W_19188 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1918c : bv 32 := 0x00009517.
Lemma F_1918c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192bc : word) = Some W_1918c.
Proof. vm_refl. Qed.
Lemma D_1918c : decode_any W_1918c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_19190 : bv 32 := 0x9ac53503.
Lemma F_19190 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192c0 : word) = Some W_19190.
Proof. vm_refl. Qed.
Lemma D_19190 : decode_any W_19190 = Some (Load SZ8 true 10 10 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_19194 : bv 32 := 0x41c655b7.
Lemma F_19194 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192c4 : word) = Some W_19194.
Proof. vm_refl. Qed.
Lemma D_19194 : decode_any W_19194 = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

Definition W_19198 : bv 32 := 0xe6d5859b.
Lemma F_19198 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192c8 : word) = Some W_19198.
Proof. vm_refl. Qed.
Lemma D_19198 : decode_any W_19198 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

Definition W_1919c : bv 32 := 0x02b505b3.
Lemma F_1919c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192cc : word) = Some W_1919c.
Proof. vm_refl. Qed.
Lemma D_1919c : decode_any W_1919c = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_191a0 : bv 32 := 0x00b53023.
Lemma F_191a0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192d0 : word) = Some W_191a0.
Proof. vm_refl. Qed.
Lemma D_191a0 : decode_any W_191a0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_191a4 : bv 32 := 0x00009517.
Lemma F_191a4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192d4 : word) = Some W_191a4.
Proof. vm_refl. Qed.
Lemma D_191a4 : decode_any W_191a4 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_191a8 : bv 32 := 0x99453503.
Lemma F_191a8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192d8 : word) = Some W_191a8.
Proof. vm_refl. Qed.
Lemma D_191a8 : decode_any W_191a8 = Some (Load SZ8 true 10 10 2452, 4%Z).
Proof. vm_refl. Qed.

Definition W_191ac : bv 32 := 0x000500a3.
Lemma F_191ac : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192dc : word) = Some W_191ac.
Proof. vm_refl. Qed.
Lemma D_191ac : decode_any W_191ac = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_191b0 : bv 32 := 0x00053503.
Lemma F_191b0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192e0 : word) = Some W_191b0.
Proof. vm_refl. Qed.
Lemma D_191b0 : decode_any W_191b0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_191b4 : bv 32 := 0x00020593.
Lemma F_191b4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192e4 : word) = Some W_191b4.
Proof. vm_refl. Qed.
Lemma D_191b4 : decode_any W_191b4 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_191b8 : bv 32 := 0xfea5b823.
Lemma F_191b8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192e8 : word) = Some W_191b8.
Proof. vm_refl. Qed.
Lemma D_191b8 : decode_any W_191b8 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_191bc : bv 32 := 0x00813083.
Lemma F_191bc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192ec : word) = Some W_191bc.
Proof. vm_refl. Qed.
Lemma D_191bc : decode_any W_191bc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_191c0 : bv 32 := 0x01010113.
Lemma F_191c0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192f0 : word) = Some W_191c0.
Proof. vm_refl. Qed.
Lemma D_191c0 : decode_any W_191c0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_191c4 : bv 32 := 0x00008067.
Lemma F_191c4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x192f4 : word) = Some W_191c4.
Proof. vm_refl. Qed.
Lemma D_191c4 : decode_any W_191c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_191d0 : bv 32 := 0xfffff5b7.
Lemma F_191d0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19300 : word) = Some W_191d0.
Proof. vm_refl. Qed.
Lemma D_191d0 : decode_any W_191d0 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_191d4 : bv 32 := 0x0015859b.
Lemma F_191d4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19304 : word) = Some W_191d4.
Proof. vm_refl. Qed.
Lemma D_191d4 : decode_any W_191d4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_191d8 : bv 32 := 0x02b56663.
Lemma F_191d8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19308 : word) = Some W_191d8.
Proof. vm_refl. Qed.
Lemma D_191d8 : decode_any W_191d8 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_19204 : bv 32 := 0x00008067.
Lemma F_19204 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19334 : word) = Some W_19204.
Proof. vm_refl. Qed.
Lemma D_19204 : decode_any W_19204 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19358 : bv 32 := 0x1c050463.
Lemma F_19358 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19488 : word) = Some W_19358.
Proof. vm_refl. Qed.
Lemma D_19358 : decode_any W_19358 = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_1935c : bv 32 := 0xfd010113.
Lemma F_1935c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1948c : word) = Some W_1935c.
Proof. vm_refl. Qed.
Lemma D_1935c : decode_any W_1935c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_19360 : bv 32 := 0x02113423.
Lemma F_19360 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19490 : word) = Some W_19360.
Proof. vm_refl. Qed.
Lemma D_19360 : decode_any W_19360 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_19364 : bv 32 := 0x02813023.
Lemma F_19364 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19494 : word) = Some W_19364.
Proof. vm_refl. Qed.
Lemma D_19364 : decode_any W_19364 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19368 : bv 32 := 0x00913c23.
Lemma F_19368 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19498 : word) = Some W_19368.
Proof. vm_refl. Qed.
Lemma D_19368 : decode_any W_19368 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1936c : bv 32 := 0x01213823.
Lemma F_1936c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1949c : word) = Some W_1936c.
Proof. vm_refl. Qed.
Lemma D_1936c : decode_any W_1936c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19370 : bv 32 := 0x01313423.
Lemma F_19370 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194a0 : word) = Some W_19370.
Proof. vm_refl. Qed.
Lemma D_19370 : decode_any W_19370 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19374 : bv 32 := 0x00050493.
Lemma F_19374 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194a4 : word) = Some W_19374.
Proof. vm_refl. Qed.
Lemma D_19374 : decode_any W_19374 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19378 : bv 32 := 0x1ac000ef.
Lemma F_19378 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194a8 : word) = Some W_19378.
Proof. vm_refl. Qed.
Lemma D_19378 : decode_any W_19378 = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

Definition W_1937c : bv 32 := 0x02053583.
Lemma F_1937c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194ac : word) = Some W_1937c.
Proof. vm_refl. Qed.
Lemma D_1937c : decode_any W_1937c = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_19380 : bv 32 := 0xffd4c683.
Lemma F_19380 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194b0 : word) = Some W_19380.
Proof. vm_refl. Qed.
Lemma D_19380 : decode_any W_19380 = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_19384 : bv 32 := 0x00c5d613.
Lemma F_19384 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194b4 : word) = Some W_19384.
Proof. vm_refl. Qed.
Lemma D_19384 : decode_any W_19384 = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19388 : bv 32 := 0x01f6f413.
Lemma F_19388 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194b8 : word) = Some W_19388.
Proof. vm_refl. Qed.
Lemma D_19388 : decode_any W_19388 = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1938c : bv 32 := 0x00060e63.
Lemma F_1938c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194bc : word) = Some W_1938c.
Proof. vm_refl. Qed.
Lemma D_1938c : decode_any W_1938c = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_19390 : bv 32 := 0x01f5f613.
Lemma F_19390 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194c0 : word) = Some W_19390.
Proof. vm_refl. Qed.
Lemma D_19390 : decode_any W_19390 = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_19394 : bv 32 := 0x00061a63.
Lemma F_19394 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194c4 : word) = Some W_19394.
Proof. vm_refl. Qed.
Lemma D_19394 : decode_any W_19394 = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_19398 : bv 32 := 0xfffff637.
Lemma F_19398 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194c8 : word) = Some W_19398.
Proof. vm_refl. Qed.
Lemma D_19398 : decode_any W_19398 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_1939c : bv 32 := 0x00c5f633.
Lemma F_1939c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194cc : word) = Some W_1939c.
Proof. vm_refl. Qed.
Lemma D_1939c : decode_any W_1939c = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_193a0 : bv 32 := 0xff060613.
Lemma F_193a0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194d0 : word) = Some W_193a0.
Proof. vm_refl. Qed.
Lemma D_193a0 : decode_any W_193a0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_193a4 : bv 32 := 0x0200006f.
Lemma F_193a4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194d4 : word) = Some W_193a4.
Proof. vm_refl. Qed.
Lemma D_193a4 : decode_any W_193a4 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_193a8 : bv 32 := 0x0055d613.
Lemma F_193a8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194d8 : word) = Some W_193a8.
Proof. vm_refl. Qed.
Lemma D_193a8 : decode_any W_193a8 = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_193ac : bv 32 := 0xffff9717.
Lemma F_193ac : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194dc : word) = Some W_193ac.
Proof. vm_refl. Qed.
Lemma D_193ac : decode_any W_193ac = Some (Auipc 14 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_193b0 : bv 32 := 0x07e67613.
Lemma F_193b0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194e0 : word) = Some W_193b0.
Proof. vm_refl. Qed.
Lemma D_193b0 : decode_any W_193b0 = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_193b4 : bv 32 := 0xf8070713.
Lemma F_193b4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194e4 : word) = Some W_193b4.
Proof. vm_refl. Qed.
Lemma D_193b4 : decode_any W_193b4 = Some (OpImm ALU_ADD 14 14 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_193b8 : bv 32 := 0x00c70633.
Lemma F_193b8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194e8 : word) = Some W_193b8.
Proof. vm_refl. Qed.
Lemma D_193b8 : decode_any W_193b8 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_193bc : bv 32 := 0x00065603.
Lemma F_193bc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194ec : word) = Some W_193bc.
Proof. vm_refl. Qed.
Lemma D_193bc : decode_any W_193bc = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_193c0 : bv 32 := 0x00461613.
Lemma F_193c0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194f0 : word) = Some W_193c0.
Proof. vm_refl. Qed.
Lemma D_193c0 : decode_any W_193c0 = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_193c4 : bv 32 := 0x01053703.
Lemma F_193c4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194f4 : word) = Some W_193c4.
Proof. vm_refl. Qed.
Lemma D_193c4 : decode_any W_193c4 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_193c8 : bv 32 := 0x028607b3.
Lemma F_193c8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194f8 : word) = Some W_193c8.
Proof. vm_refl. Qed.
Lemma D_193c8 : decode_any W_193c8 = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_193cc : bv 32 := 0x0a000813.
Lemma F_193cc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x194fc : word) = Some W_193cc.
Proof. vm_refl. Qed.
Lemma D_193cc : decode_any W_193cc = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_193d0 : bv 32 := 0x00c70633.
Lemma F_193d0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19500 : word) = Some W_193d0.
Proof. vm_refl. Qed.
Lemma D_193d0 : decode_any W_193d0 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_193d4 : bv 32 := 0x00f607b3.
Lemma F_193d4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19504 : word) = Some W_193d4.
Proof. vm_refl. Qed.
Lemma D_193d4 : decode_any W_193d4 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_193d8 : bv 32 := 0x00c78613.
Lemma F_193d8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19508 : word) = Some W_193d8.
Proof. vm_refl. Qed.
Lemma D_193d8 : decode_any W_193d8 = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_193dc : bv 32 := 0x0056d713.
Lemma F_193dc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1950c : word) = Some W_193dc.
Proof. vm_refl. Qed.
Lemma D_193dc : decode_any W_193dc = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_193e0 : bv 32 := 0x0306e663.
Lemma F_193e0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19510 : word) = Some W_193e0.
Proof. vm_refl. Qed.
Lemma D_193e0 : decode_any W_193e0 = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_193e4 : bv 32 := 0x00500693.
Lemma F_193e4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19514 : word) = Some W_193e4.
Proof. vm_refl. Qed.
Lemma D_193e4 : decode_any W_193e4 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_193e8 : bv 32 := 0x00d70463.
Lemma F_193e8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19518 : word) = Some W_193e8.
Proof. vm_refl. Qed.
Lemma D_193e8 : decode_any W_193e8 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_193f0 : bv 32 := 0x0087e703.
Lemma F_193f0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19520 : word) = Some W_193f0.
Proof. vm_refl. Qed.
Lemma D_193f0 : decode_any W_193f0 = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_193f4 : bv 32 := 0x00400693.
Lemma F_193f4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19524 : word) = Some W_193f4.
Proof. vm_refl. Qed.
Lemma D_193f4 : decode_any W_193f4 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_193f8 : bv 32 := 0x00e6e463.
Lemma F_193f8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19528 : word) = Some W_193f8.
Proof. vm_refl. Qed.
Lemma D_193f8 : decode_any W_193f8 = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19400 : bv 32 := 0x0077c683.
Lemma F_19400 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19530 : word) = Some W_19400.
Proof. vm_refl. Qed.
Lemma D_19400 : decode_any W_19400 = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_19404 : bv 32 := 0x00068463.
Lemma F_19404 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19534 : word) = Some W_19404.
Proof. vm_refl. Qed.
Lemma D_19404 : decode_any W_19404 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1940c : bv 32 := 0x409606b3.
Lemma F_1940c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1953c : word) = Some W_1940c.
Proof. vm_refl. Qed.
Lemma D_1940c : decode_any W_1940c = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_19410 : bv 32 := 0x00e6f463.
Lemma F_19410 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19540 : word) = Some W_19410.
Proof. vm_refl. Qed.
Lemma D_19410 : decode_any W_19410 = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19418 : bv 32 := 0x40e606b3.
Lemma F_19418 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19548 : word) = Some W_19418.
Proof. vm_refl. Qed.
Lemma D_19418 : decode_any W_19418 = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1941c : bv 32 := 0x0006c683.
Lemma F_1941c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1954c : word) = Some W_1941c.
Proof. vm_refl. Qed.
Lemma D_1941c : decode_any W_1941c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19420 : bv 32 := 0x00068463.
Lemma F_19420 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19550 : word) = Some W_19420.
Proof. vm_refl. Qed.
Lemma D_19420 : decode_any W_19420 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19428 : bv 32 := 0x00064603.
Lemma F_19428 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19558 : word) = Some W_19428.
Proof. vm_refl. Qed.
Lemma D_19428 : decode_any W_19428 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1942c : bv 32 := 0x00060463.
Lemma F_1942c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1955c : word) = Some W_1942c.
Proof. vm_refl. Qed.
Lemma D_1942c : decode_any W_1942c = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19524 : bv 32 := 0x00f57593.
Lemma F_19524 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19654 : word) = Some W_19524.
Proof. vm_refl. Qed.
Lemma D_19524 : decode_any W_19524 = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_19528 : bv 32 := 0x00058463.
Lemma F_19528 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19658 : word) = Some W_19528.
Proof. vm_refl. Qed.
Lemma D_19528 : decode_any W_19528 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19530 : bv 32 := 0xffc54603.
Lemma F_19530 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19660 : word) = Some W_19530.
Proof. vm_refl. Qed.
Lemma D_19530 : decode_any W_19530 = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_19534 : bv 32 := 0xffd54683.
Lemma F_19534 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19664 : word) = Some W_19534.
Proof. vm_refl. Qed.
Lemma D_19534 : decode_any W_19534 = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_19538 : bv 32 := 0xffe55583.
Lemma F_19538 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19668 : word) = Some W_19538.
Proof. vm_refl. Qed.
Lemma D_19538 : decode_any W_19538 = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_1953c : bv 32 := 0x00060e63.
Lemma F_1953c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1966c : word) = Some W_1953c.
Proof. vm_refl. Qed.
Lemma D_1953c : decode_any W_1953c = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_19558 : bv 32 := 0x00459613.
Lemma F_19558 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19688 : word) = Some W_19558.
Proof. vm_refl. Qed.
Lemma D_19558 : decode_any W_19558 = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1955c : bv 32 := 0x40c50633.
Lemma F_1955c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1968c : word) = Some W_1955c.
Proof. vm_refl. Qed.
Lemma D_1955c : decode_any W_1955c = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19560 : bv 32 := 0xff063503.
Lemma F_19560 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19690 : word) = Some W_19560.
Proof. vm_refl. Qed.
Lemma D_19560 : decode_any W_19560 = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_19564 : bv 32 := 0x01053703.
Lemma F_19564 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19694 : word) = Some W_19564.
Proof. vm_refl. Qed.
Lemma D_19564 : decode_any W_19564 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19568 : bv 32 := 0xff060613.
Lemma F_19568 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19698 : word) = Some W_19568.
Proof. vm_refl. Qed.
Lemma D_19568 : decode_any W_19568 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1956c : bv 32 := 0x01f6f693.
Lemma F_1956c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1969c : word) = Some W_1956c.
Proof. vm_refl. Qed.
Lemma D_1956c : decode_any W_1956c = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_19570 : bv 32 := 0x00c70463.
Lemma F_19570 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196a0 : word) = Some W_19570.
Proof. vm_refl. Qed.
Lemma D_19570 : decode_any W_19570 = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19578 : bv 32 := 0x02053603.
Lemma F_19578 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196a8 : word) = Some W_19578.
Proof. vm_refl. Qed.
Lemma D_19578 : decode_any W_19578 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1957c : bv 32 := 0x01f67713.
Lemma F_1957c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196ac : word) = Some W_1957c.
Proof. vm_refl. Qed.
Lemma D_1957c : decode_any W_1957c = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_19580 : bv 32 := 0x00d77463.
Lemma F_19580 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196b0 : word) = Some W_19580.
Proof. vm_refl. Qed.
Lemma D_19580 : decode_any W_19580 = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19588 : bv 32 := 0x01852783.
Lemma F_19588 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196b8 : word) = Some W_19588.
Proof. vm_refl. Qed.
Lemma D_19588 : decode_any W_19588 = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1958c : bv 32 := 0x00100713.
Lemma F_1958c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196bc : word) = Some W_1958c.
Proof. vm_refl. Qed.
Lemma D_1958c : decode_any W_1958c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19590 : bv 32 := 0x00d7173b.
Lemma F_19590 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196c0 : word) = Some W_19590.
Proof. vm_refl. Qed.
Lemma D_19590 : decode_any W_19590 = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_19594 : bv 32 := 0x00e7f7b3.
Lemma F_19594 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196c4 : word) = Some W_19594.
Proof. vm_refl. Qed.
Lemma D_19594 : decode_any W_19594 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_19598 : bv 32 := 0x00078463.
Lemma F_19598 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196c8 : word) = Some W_19598.
Proof. vm_refl. Qed.
Lemma D_19598 : decode_any W_19598 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_195a0 : bv 32 := 0x01c52783.
Lemma F_195a0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196d0 : word) = Some W_195a0.
Proof. vm_refl. Qed.
Lemma D_195a0 : decode_any W_195a0 = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_195a4 : bv 32 := 0x00e7f733.
Lemma F_195a4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196d4 : word) = Some W_195a4.
Proof. vm_refl. Qed.
Lemma D_195a4 : decode_any W_195a4 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_195a8 : bv 32 := 0x00070463.
Lemma F_195a8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196d8 : word) = Some W_195a8.
Proof. vm_refl. Qed.
Lemma D_195a8 : decode_any W_195a8 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_195b0 : bv 32 := 0xfffff737.
Lemma F_195b0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196e0 : word) = Some W_195b0.
Proof. vm_refl. Qed.
Lemma D_195b0 : decode_any W_195b0 = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_195b4 : bv 32 := 0x0007a797.
Lemma F_195b4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196e4 : word) = Some W_195b4.
Proof. vm_refl. Qed.
Lemma D_195b4 : decode_any W_195b4 = Some (Auipc 15 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_195b8 : bv 32 := 0x00e57733.
Lemma F_195b8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196e8 : word) = Some W_195b8.
Proof. vm_refl. Qed.
Lemma D_195b8 : decode_any W_195b8 = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_195bc : bv 32 := 0x00073703.
Lemma F_195bc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196ec : word) = Some W_195bc.
Proof. vm_refl. Qed.
Lemma D_195bc : decode_any W_195bc = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_195c0 : bv 32 := 0xbfc7b783.
Lemma F_195c0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196f0 : word) = Some W_195c0.
Proof. vm_refl. Qed.
Lemma D_195c0 : decode_any W_195c0 = Some (Load SZ8 true 15 15 3068, 4%Z).
Proof. vm_refl. Qed.

Definition W_195c4 : bv 32 := 0x00f70463.
Lemma F_195c4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196f4 : word) = Some W_195c4.
Proof. vm_refl. Qed.
Lemma D_195c4 : decode_any W_195c4 = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_195cc : bv 32 := 0x03461713.
Lemma F_195cc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x196fc : word) = Some W_195cc.
Proof. vm_refl. Qed.
Lemma D_195cc : decode_any W_195cc = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_195d0 : bv 32 := 0x03a75713.
Lemma F_195d0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19700 : word) = Some W_195d0.
Proof. vm_refl. Qed.
Lemma D_195d0 : decode_any W_195d0 = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_195d4 : bv 32 := 0x02f00793.
Lemma F_195d4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19704 : word) = Some W_195d4.
Proof. vm_refl. Qed.
Lemma D_195d4 : decode_any W_195d4 = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_195d8 : bv 32 := 0x02e7ea63.
Lemma F_195d8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19708 : word) = Some W_195d8.
Proof. vm_refl. Qed.
Lemma D_195d8 : decode_any W_195d8 = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_195dc : bv 32 := 0x00171713.
Lemma F_195dc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1970c : word) = Some W_195dc.
Proof. vm_refl. Qed.
Lemma D_195dc : decode_any W_195dc = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_195e0 : bv 32 := 0xffff9797.
Lemma F_195e0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19710 : word) = Some W_195e0.
Proof. vm_refl. Qed.
Lemma D_195e0 : decode_any W_195e0 = Some (Auipc 15 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_195e4 : bv 32 := 0xd4c78793.
Lemma F_195e4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19714 : word) = Some W_195e4.
Proof. vm_refl. Qed.
Lemma D_195e4 : decode_any W_195e4 = Some (OpImm ALU_ADD 15 15 3404, 4%Z).
Proof. vm_refl. Qed.

Definition W_195e8 : bv 32 := 0x00e78733.
Lemma F_195e8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19718 : word) = Some W_195e8.
Proof. vm_refl. Qed.
Lemma D_195e8 : decode_any W_195e8 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_195ec : bv 32 := 0x00075703.
Lemma F_195ec : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1971c : word) = Some W_195ec.
Proof. vm_refl. Qed.
Lemma D_195ec : decode_any W_195ec = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_195f0 : bv 32 := 0x02d707b3.
Lemma F_195f0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19720 : word) = Some W_195f0.
Proof. vm_refl. Qed.
Lemma D_195f0 : decode_any W_195f0 = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_195f4 : bv 32 := 0x00f5f463.
Lemma F_195f4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19724 : word) = Some W_195f4.
Proof. vm_refl. Qed.
Lemma D_195f4 : decode_any W_195f4 = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_195fc : bv 32 := 0x00168693.
Lemma F_195fc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1972c : word) = Some W_195fc.
Proof. vm_refl. Qed.
Lemma D_195fc : decode_any W_195fc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19600 : bv 32 := 0x02e686b3.
Lemma F_19600 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19730 : word) = Some W_19600.
Proof. vm_refl. Qed.
Lemma D_19600 : decode_any W_19600 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_19604 : bv 32 := 0x00d5f863.
Lemma F_19604 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19734 : word) = Some W_19604.
Proof. vm_refl. Qed.
Lemma D_19604 : decode_any W_19604 = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19608 : bv 32 := 0x0100006f.
Lemma F_19608 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19738 : word) = Some W_19608.
Proof. vm_refl. Qed.
Lemma D_19608 : decode_any W_19608 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1960c : bv 32 := 0x03f00693.
Lemma F_1960c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1973c : word) = Some W_1960c.
Proof. vm_refl. Qed.
Lemma D_1960c : decode_any W_1960c = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_19610 : bv 32 := 0x00d70463.
Lemma F_19610 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19740 : word) = Some W_19610.
Proof. vm_refl. Qed.
Lemma D_19610 : decode_any W_19610 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19618 : bv 32 := 0x00c65613.
Lemma F_19618 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19748 : word) = Some W_19618.
Proof. vm_refl. Qed.
Lemma D_19618 : decode_any W_19618 = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1961c : bv 32 := 0x00060a63.
Lemma F_1961c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1974c : word) = Some W_1961c.
Proof. vm_refl. Qed.
Lemma D_1961c : decode_any W_1961c = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_19620 : bv 32 := 0x00861613.
Lemma F_19620 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19750 : word) = Some W_19620.
Proof. vm_refl. Qed.
Lemma D_19620 : decode_any W_19620 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19624 : bv 32 := 0xfff60613.
Lemma F_19624 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19754 : word) = Some W_19624.
Proof. vm_refl. Qed.
Lemma D_19624 : decode_any W_19624 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_19628 : bv 32 := 0x00b67463.
Lemma F_19628 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19758 : word) = Some W_19628.
Proof. vm_refl. Qed.
Lemma D_19628 : decode_any W_19628 = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19630 : bv 32 := 0x00008067.
Lemma F_19630 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19760 : word) = Some W_19630.
Proof. vm_refl. Qed.
Lemma D_19630 : decode_any W_19630 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_199b4 : bv 32 := 0x00072503.
Lemma F_199b4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19ae4 : word) = Some W_199b4.
Proof. vm_refl. Qed.
Lemma D_199b4 : decode_any W_199b4 = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_199b8 : bv 32 := 0x00b56633.
Lemma F_199b8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19ae8 : word) = Some W_199b8.
Proof. vm_refl. Qed.
Lemma D_199b8 : decode_any W_199b8 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_199bc : bv 32 := 0x160726af.
Lemma F_199bc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19aec : word) = Some W_199bc.
Proof. vm_refl. Qed.
Lemma D_199bc : decode_any W_199bc = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_199c0 : bv 32 := 0x00a69663.
Lemma F_199c0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19af0 : word) = Some W_199c0.
Proof. vm_refl. Qed.
Lemma D_199c0 : decode_any W_199c0 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_199c4 : bv 32 := 0x1ec727af.
Lemma F_199c4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19af4 : word) = Some W_199c4.
Proof. vm_refl. Qed.
Lemma D_199c4 : decode_any W_199c4 = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_199c8 : bv 32 := 0xfe079ae3.
Lemma F_199c8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19af8 : word) = Some W_199c8.
Proof. vm_refl. Qed.
Lemma D_199c8 : decode_any W_199c8 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_199cc : bv 32 := 0x0006869b.
Lemma F_199cc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19afc : word) = Some W_199cc.
Proof. vm_refl. Qed.
Lemma D_199cc : decode_any W_199cc = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_199d0 : bv 32 := 0xfea692e3.
Lemma F_199d0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x19b00 : word) = Some W_199d0.
Proof. vm_refl. Qed.
Lemma D_199d0 : decode_any W_199d0 = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.
