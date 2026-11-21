(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_14000 : bv 32 := 0x00050993.
Lemma F_14000 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14060 : word) = Some W_14000.
Proof. vm_refl. Qed.
Lemma D_14000 : decode_any W_14000 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14004 : bv 32 := 0x02058e63.
Lemma F_14004 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14064 : word) = Some W_14004.
Proof. vm_refl. Qed.
Lemma D_14004 : decode_any W_14004 = Some (Branch BC_EQ 11 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_14008 : bv 32 := 0x04090c63.
Lemma F_14008 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14068 : word) = Some W_14008.
Proof. vm_refl. Qed.
Lemma D_14008 : decode_any W_14008 = Some (Branch BC_EQ 18 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1400c : bv 32 := 0x0009c503.
Lemma F_1400c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1406c : word) = Some W_1400c.
Proof. vm_refl. Qed.
Lemma D_1400c : decode_any W_1400c = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14010 : bv 32 := 0x00357513.
Lemma F_14010 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14070 : word) = Some W_14010.
Proof. vm_refl. Qed.
Lemma D_14010 : decode_any W_14010 = Some (OpImm ALU_AND 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_14014 : bv 32 := 0x00150a93.
Lemma F_14014 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14074 : word) = Some W_14014.
Proof. vm_refl. Qed.
Lemma D_14014 : decode_any W_14014 = Some (OpImm ALU_ADD 21 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14018 : bv 32 := 0x04040863.
Lemma F_14018 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14078 : word) = Some W_14018.
Proof. vm_refl. Qed.
Lemma D_14018 : decode_any W_14018 = Some (Branch BC_EQ 8 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1401c : bv 32 := 0x00040513.
Lemma F_1401c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1407c : word) = Some W_1401c.
Proof. vm_refl. Qed.
Lemma D_1401c : decode_any W_1401c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14020 : bv 32 := 0x649010ef.
Lemma F_14020 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14080 : word) = Some W_14020.
Proof. vm_refl. Qed.
Lemma D_14020 : decode_any W_14020 = Some (Jal 1 7752, 4%Z).
Proof. vm_refl. Qed.

Definition W_14024 : bv 32 := 0x02050a63.
Lemma F_14024 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14084 : word) = Some W_14024.
Proof. vm_refl. Qed.
Lemma D_14024 : decode_any W_14024 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_14028 : bv 32 := 0x00050913.
Lemma F_14028 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14088 : word) = Some W_14028.
Proof. vm_refl. Qed.
Lemma D_14028 : decode_any W_14028 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1402c : bv 32 := 0x00048593.
Lemma F_1402c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1408c : word) = Some W_1402c.
Proof. vm_refl. Qed.
Lemma D_1402c : decode_any W_1402c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14030 : bv 32 := 0x00040613.
Lemma F_14030 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14090 : word) = Some W_14030.
Proof. vm_refl. Qed.
Lemma D_14030 : decode_any W_14030 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14034 : bv 32 := 0x471080ef.
Lemma F_14034 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14094 : word) = Some W_14034.
Proof. vm_refl. Qed.
Lemma D_14034 : decode_any W_14034 = Some (Jal 1 35952, 4%Z).
Proof. vm_refl. Qed.

Definition W_14038 : bv 32 := 0x00090493.
Lemma F_14038 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14098 : word) = Some W_14038.
Proof. vm_refl. Qed.
Lemma D_14038 : decode_any W_14038 = Some (OpImm ALU_ADD 9 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1403c : bv 32 := 0x0340006f.
Lemma F_1403c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1409c : word) = Some W_1403c.
Proof. vm_refl. Qed.
Lemma D_1403c : decode_any W_1403c = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_14040 : bv 32 := 0x00100513.
Lemma F_14040 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140a0 : word) = Some W_14040.
Proof. vm_refl. Qed.
Lemma D_14040 : decode_any W_14040 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14044 : bv 32 := 0x00aa0023.
Lemma F_14044 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140a4 : word) = Some W_14044.
Proof. vm_refl. Qed.
Lemma D_14044 : decode_any W_14044 = Some (Store SZ1 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14048 : bv 32 := 0x00000517.
Lemma F_14048 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140a8 : word) = Some W_14048.
Proof. vm_refl. Qed.
Lemma D_14048 : decode_any W_14048 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1404c : bv 32 := 0x0d050513.
Lemma F_1404c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140ac : word) = Some W_1404c.
Proof. vm_refl. Qed.
Lemma D_1404c : decode_any W_1404c = Some (OpImm ALU_ADD 10 10 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_14050 : bv 32 := 0x1bd010ef.
Lemma F_14050 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140b0 : word) = Some W_14050.
Proof. vm_refl. Qed.
Lemma D_14050 : decode_any W_14050 = Some (Jal 1 6588, 4%Z).
Proof. vm_refl. Qed.

Definition W_14054 : bv 32 := 0x08050e63.
Lemma F_14054 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140b4 : word) = Some W_14054.
Proof. vm_refl. Qed.
Lemma D_14054 : decode_any W_14054 = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_14058 : bv 32 := 0x00200513.
Lemma F_14058 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140b8 : word) = Some W_14058.
Proof. vm_refl. Qed.
Lemma D_14058 : decode_any W_14058 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1405c : bv 32 := 0x0680006f.
Lemma F_1405c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140bc : word) = Some W_1405c.
Proof. vm_refl. Qed.
Lemma D_1405c : decode_any W_1405c = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_14060 : bv 32 := 0x00100a93.
Lemma F_14060 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140c0 : word) = Some W_14060.
Proof. vm_refl. Qed.
Lemma D_14060 : decode_any W_14060 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14064 : bv 32 := 0xfa041ce3.
Lemma F_14064 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140c4 : word) = Some W_14064.
Proof. vm_refl. Qed.
Lemma D_14064 : decode_any W_14064 = Some (Branch BC_NE 8 0 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_14068 : bv 32 := 0x00000913.
Lemma F_14068 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140c8 : word) = Some W_14068.
Proof. vm_refl. Qed.
Lemma D_14068 : decode_any W_14068 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1406c : bv 32 := 0x010a0493.
Lemma F_1406c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140cc : word) = Some W_1406c.
Proof. vm_refl. Qed.
Lemma D_1406c : decode_any W_1406c = Some (OpImm ALU_ADD 9 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14070 : bv 32 := 0x00000b13.
Lemma F_14070 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140d0 : word) = Some W_14070.
Proof. vm_refl. Qed.
Lemma D_14070 : decode_any W_14070 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14074 : bv 32 := 0xffe00b93.
Lemma F_14074 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140d4 : word) = Some W_14074.
Proof. vm_refl. Qed.
Lemma D_14074 : decode_any W_14074 = Some (OpImm ALU_ADD 23 0 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_14078 : bv 32 := 0x00100513.
Lemma F_14078 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140d8 : word) = Some W_14078.
Proof. vm_refl. Qed.
Lemma D_14078 : decode_any W_14078 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1407c : bv 32 := 0x00aa0223.
Lemma F_1407c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140dc : word) = Some W_1407c.
Proof. vm_refl. Qed.
Lemma D_1407c : decode_any W_1407c = Some (Store SZ1 20 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14080 : bv 32 := 0x00048513.
Lemma F_14080 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140e0 : word) = Some W_14080.
Proof. vm_refl. Qed.
Lemma D_14080 : decode_any W_14080 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14084 : bv 32 := 0x00040593.
Lemma F_14084 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140e4 : word) = Some W_14084.
Proof. vm_refl. Qed.
Lemma D_14084 : decode_any W_14084 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14088 : bv 32 := 0x108000ef.
Lemma F_14088 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140e8 : word) = Some W_14088.
Proof. vm_refl. Qed.
Lemma D_14088 : decode_any W_14088 = Some (Jal 1 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_1408c : bv 32 := 0x00050993.
Lemma F_1408c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140ec : word) = Some W_1408c.
Proof. vm_refl. Qed.
Lemma D_1408c : decode_any W_1408c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14090 : bv 32 := 0x000a0223.
Lemma F_14090 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140f0 : word) = Some W_14090.
Proof. vm_refl. Qed.
Lemma D_14090 : decode_any W_14090 = Some (Store SZ1 20 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14094 : bv 32 := 0x00050593.
Lemma F_14094 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140f4 : word) = Some W_14094.
Proof. vm_refl. Qed.
Lemma D_14094 : decode_any W_14094 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14098 : bv 32 := 0x0b0000ef.
Lemma F_14098 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140f8 : word) = Some W_14098.
Proof. vm_refl. Qed.
Lemma D_14098 : decode_any W_14098 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_1409c : bv 32 := 0xfff9899b.
Lemma F_1409c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x140fc : word) = Some W_1409c.
Proof. vm_refl. Qed.
Lemma D_1409c : decode_any W_1409c = Some (OpImm32 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_140a0 : bv 32 := 0x0179f463.
Lemma F_140a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14100 : word) = Some W_140a0.
Proof. vm_refl. Qed.
Lemma D_140a0 : decode_any W_140a0 = Some (Branch BC_GEU 19 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_140a4 : bv 32 := 0x00100b13.
Lemma F_140a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14104 : word) = Some W_140a4.
Proof. vm_refl. Qed.
Lemma D_140a4 : decode_any W_140a4 = Some (OpImm ALU_ADD 22 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_140a8 : bv 32 := 0xfffa8a9b.
Lemma F_140a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14108 : word) = Some W_140a8.
Proof. vm_refl. Qed.
Lemma D_140a8 : decode_any W_140a8 = Some (OpImm32 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_140ac : bv 32 := 0xfc0a96e3.
Lemma F_140ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1410c : word) = Some W_140ac.
Proof. vm_refl. Qed.
Lemma D_140ac : decode_any W_140ac = Some (Branch BC_NE 21 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_140b0 : bv 32 := 0x00090513.
Lemma F_140b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14110 : word) = Some W_140b0.
Proof. vm_refl. Qed.
Lemma D_140b0 : decode_any W_140b0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_140b4 : bv 32 := 0x475010ef.
Lemma F_140b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14114 : word) = Some W_140b4.
Proof. vm_refl. Qed.
Lemma D_140b4 : decode_any W_140b4 = Some (Jal 1 7284, 4%Z).
Proof. vm_refl. Qed.

Definition W_140b8 : bv 32 := 0x001b3513.
Lemma F_140b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14118 : word) = Some W_140b8.
Proof. vm_refl. Qed.
Lemma D_140b8 : decode_any W_140b8 = Some (OpImm ALU_SLTU 10 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_140bc : bv 32 := 0xfff50513.
Lemma F_140bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1411c : word) = Some W_140bc.
Proof. vm_refl. Qed.
Lemma D_140bc : decode_any W_140bc = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_140c0 : bv 32 := 0x04e57513.
Lemma F_140c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14120 : word) = Some W_140c0.
Proof. vm_refl. Qed.
Lemma D_140c0 : decode_any W_140c0 = Some (OpImm ALU_AND 10 10 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_140c4 : bv 32 := 0x04813083.
Lemma F_140c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14124 : word) = Some W_140c4.
Proof. vm_refl. Qed.
Lemma D_140c4 : decode_any W_140c4 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_140c8 : bv 32 := 0x04013403.
Lemma F_140c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14128 : word) = Some W_140c8.
Proof. vm_refl. Qed.
Lemma D_140c8 : decode_any W_140c8 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_140cc : bv 32 := 0x03813483.
Lemma F_140cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1412c : word) = Some W_140cc.
Proof. vm_refl. Qed.
Lemma D_140cc : decode_any W_140cc = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_140d0 : bv 32 := 0x03013903.
Lemma F_140d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14130 : word) = Some W_140d0.
Proof. vm_refl. Qed.
Lemma D_140d0 : decode_any W_140d0 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_140d4 : bv 32 := 0x02813983.
Lemma F_140d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14134 : word) = Some W_140d4.
Proof. vm_refl. Qed.
Lemma D_140d4 : decode_any W_140d4 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_140d8 : bv 32 := 0x02013a03.
Lemma F_140d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14138 : word) = Some W_140d8.
Proof. vm_refl. Qed.
Lemma D_140d8 : decode_any W_140d8 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_140dc : bv 32 := 0x01813a83.
Lemma F_140dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1413c : word) = Some W_140dc.
Proof. vm_refl. Qed.
Lemma D_140dc : decode_any W_140dc = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_140e0 : bv 32 := 0x01013b03.
Lemma F_140e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14140 : word) = Some W_140e0.
Proof. vm_refl. Qed.
Lemma D_140e0 : decode_any W_140e0 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_140e4 : bv 32 := 0x00813b83.
Lemma F_140e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14144 : word) = Some W_140e4.
Proof. vm_refl. Qed.
Lemma D_140e4 : decode_any W_140e4 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_140e8 : bv 32 := 0x05010113.
Lemma F_140e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14148 : word) = Some W_140e8.
Proof. vm_refl. Qed.
Lemma D_140e8 : decode_any W_140e8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_140ec : bv 32 := 0x00008067.
Lemma F_140ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1414c : word) = Some W_140ec.
Proof. vm_refl. Qed.
Lemma D_140ec : decode_any W_140ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_140f0 : bv 32 := 0x0000a517.
Lemma F_140f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14150 : word) = Some W_140f0.
Proof. vm_refl. Qed.
Lemma D_140f0 : decode_any W_140f0 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_140f4 : bv 32 := 0x5f853503.
Lemma F_140f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14154 : word) = Some W_140f4.
Proof. vm_refl. Qed.
Lemma D_140f4 : decode_any W_140f4 = Some (Load SZ8 true 10 10 1528, 4%Z).
Proof. vm_refl. Qed.

Definition W_140f8 : bv 32 := 0xf00508e3.
Lemma F_140f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14158 : word) = Some W_140f8.
Proof. vm_refl. Qed.
Lemma D_140f8 : decode_any W_140f8 = Some (Branch BC_EQ 10 0 7952, 4%Z).
Proof. vm_refl. Qed.

Definition W_140fc : bv 32 := 0x0000b517.
Lemma F_140fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1415c : word) = Some W_140fc.
Proof. vm_refl. Qed.
Lemma D_140fc : decode_any W_140fc = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_14100 : bv 32 := 0x64c50513.
Lemma F_14100 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14160 : word) = Some W_14100.
Proof. vm_refl. Qed.
Lemma D_14100 : decode_any W_14100 = Some (OpImm ALU_ADD 10 10 1612, 4%Z).
Proof. vm_refl. Qed.

Definition W_14104 : bv 32 := 0x00850593.
Lemma F_14104 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14164 : word) = Some W_14104.
Proof. vm_refl. Qed.
Lemma D_14104 : decode_any W_14104 = Some (OpImm ALU_ADD 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14108 : bv 32 := 0x00b13023.
Lemma F_14108 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14168 : word) = Some W_14108.
Proof. vm_refl. Qed.
Lemma D_14108 : decode_any W_14108 = Some (Store SZ8 2 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1410c : bv 32 := 0x00010593.
Lemma F_1410c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1416c : word) = Some W_1410c.
Proof. vm_refl. Qed.
Lemma D_1410c : decode_any W_1410c = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14110 : bv 32 := 0x000000ef.
Lemma F_14110 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14170 : word) = Some W_14110.
Proof. vm_refl. Qed.
Lemma D_14110 : decode_any W_14110 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14114 : bv 32 := 0xef5ff06f.
Lemma F_14114 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14174 : word) = Some W_14114.
Proof. vm_refl. Qed.
Lemma D_14114 : decode_any W_14114 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_14118 : bv 32 := 0x0001c517.
Lemma F_14118 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14178 : word) = Some W_14118.
Proof. vm_refl. Qed.
Lemma D_14118 : decode_any W_14118 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1411c : bv 32 := 0x88c54503.
Lemma F_1411c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1417c : word) = Some W_1411c.
Proof. vm_refl. Qed.
Lemma D_1411c : decode_any W_1411c = Some (Load SZ1 false 10 10 2188, 4%Z).
Proof. vm_refl. Qed.

Definition W_14120 : bv 32 := 0x00051463.
Lemma F_14120 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14180 : word) = Some W_14120.
Proof. vm_refl. Qed.
Lemma D_14120 : decode_any W_14120 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14124 : bv 32 := 0x00008067.
Lemma F_14124 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14184 : word) = Some W_14124.
Proof. vm_refl. Qed.
Lemma D_14124 : decode_any W_14124 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14128 : bv 32 := 0xff010113.
Lemma F_14128 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14188 : word) = Some W_14128.
Proof. vm_refl. Qed.
Lemma D_14128 : decode_any W_14128 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1412c : bv 32 := 0x00113423.
Lemma F_1412c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1418c : word) = Some W_1412c.
Proof. vm_refl. Qed.
Lemma D_1412c : decode_any W_1412c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14130 : bv 32 := 0x0000a517.
Lemma F_14130 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14190 : word) = Some W_14130.
Proof. vm_refl. Qed.
Lemma D_14130 : decode_any W_14130 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_14134 : bv 32 := 0x5c053503.
Lemma F_14134 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14194 : word) = Some W_14134.
Proof. vm_refl. Qed.
Lemma D_14134 : decode_any W_14134 = Some (Load SZ8 true 10 10 1472, 4%Z).
Proof. vm_refl. Qed.

Definition W_14138 : bv 32 := 0x00053503.
Lemma F_14138 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x14198 : word) = Some W_14138.
Proof. vm_refl. Qed.
Lemma D_14138 : decode_any W_14138 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1413c : bv 32 := 0x7ec030ef.
Lemma F_1413c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1419c : word) = Some W_1413c.
Proof. vm_refl. Qed.
Lemma D_1413c : decode_any W_1413c = Some (Jal 1 14316, 4%Z).
Proof. vm_refl. Qed.

Definition W_14140 : bv 32 := 0x04d00513.
Lemma F_14140 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x141a0 : word) = Some W_14140.
Proof. vm_refl. Qed.
Lemma D_14140 : decode_any W_14140 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_14144 : bv 32 := 0x49c090ef.
Lemma F_14144 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x141a4 : word) = Some W_14144.
Proof. vm_refl. Qed.
Lemma D_14144 : decode_any W_14144 = Some (Jal 1 38044, 4%Z).
Proof. vm_refl. Qed.
