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

Definition W_1b2b4 : bv 32 := 0xff010113.
Lemma F_1b2b4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b3e4 : word) = Some W_1b2b4.
Proof. vm_refl. Qed.
Lemma D_1b2b4 : decode_any W_1b2b4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b2b8 : bv 32 := 0x00113423.
Lemma F_1b2b8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b3e8 : word) = Some W_1b2b8.
Proof. vm_refl. Qed.
Lemma D_1b2b8 : decode_any W_1b2b8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b2bc : bv 32 := 0x00813023.
Lemma F_1b2bc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b3ec : word) = Some W_1b2bc.
Proof. vm_refl. Qed.
Lemma D_1b2bc : decode_any W_1b2bc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b2c0 : bv 32 := 0x198000ef.
Lemma F_1b2c0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b3f0 : word) = Some W_1b2c0.
Proof. vm_refl. Qed.
Lemma D_1b2c0 : decode_any W_1b2c0 = Some (Jal 1 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b2c4 : bv 32 := 0x00053403.
Lemma F_1b2c4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b3f4 : word) = Some W_1b2c4.
Proof. vm_refl. Qed.
Lemma D_1b2c4 : decode_any W_1b2c4 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b2c8 : bv 32 := 0x12041663.
Lemma F_1b2c8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b3f8 : word) = Some W_1b2c8.
Proof. vm_refl. Qed.
Lemma D_1b2c8 : decode_any W_1b2c8 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b2cc : bv 32 := 0x00078517.
Lemma F_1b2cc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b3fc : word) = Some W_1b2cc.
Proof. vm_refl. Qed.
Lemma D_1b2cc : decode_any W_1b2cc = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b2d0 : bv 32 := 0x28c53403.
Lemma F_1b2d0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b400 : word) = Some W_1b2d0.
Proof. vm_refl. Qed.
Lemma D_1b2d0 : decode_any W_1b2d0 = Some (Load SZ8 true 8 10 652, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b2d4 : bv 32 := 0x04040a63.
Lemma F_1b2d4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b404 : word) = Some W_1b2d4.
Proof. vm_refl. Qed.
Lemma D_1b2d4 : decode_any W_1b2d4 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b328 : bv 32 := 0x00008517.
Lemma F_1b328 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b458 : word) = Some W_1b328.
Proof. vm_refl. Qed.
Lemma D_1b328 : decode_any W_1b328 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b32c : bv 32 := 0xa2853403.
Lemma F_1b32c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b45c : word) = Some W_1b32c.
Proof. vm_refl. Qed.
Lemma D_1b32c : decode_any W_1b32c = Some (Load SZ8 true 8 10 2600, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b330 : bv 32 := 0x04040a63.
Lemma F_1b330 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b460 : word) = Some W_1b330.
Proof. vm_refl. Qed.
Lemma D_1b330 : decode_any W_1b330 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b334 : bv 32 := 0x08c42503.
Lemma F_1b334 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b464 : word) = Some W_1b334.
Proof. vm_refl. Qed.
Lemma D_1b334 : decode_any W_1b334 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b338 : bv 32 := 0x00054663.
Lemma F_1b338 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b468 : word) = Some W_1b338.
Proof. vm_refl. Qed.
Lemma D_1b338 : decode_any W_1b338 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b344 : bv 32 := 0x02843503.
Lemma F_1b344 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b474 : word) = Some W_1b344.
Proof. vm_refl. Qed.
Lemma D_1b344 : decode_any W_1b344 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b348 : bv 32 := 0x03843583.
Lemma F_1b348 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b478 : word) = Some W_1b348.
Proof. vm_refl. Qed.
Lemma D_1b348 : decode_any W_1b348 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b34c : bv 32 := 0x00b50c63.
Lemma F_1b34c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b47c : word) = Some W_1b34c.
Proof. vm_refl. Qed.
Lemma D_1b34c : decode_any W_1b34c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b350 : bv 32 := 0x04843683.
Lemma F_1b350 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b480 : word) = Some W_1b350.
Proof. vm_refl. Qed.
Lemma D_1b350 : decode_any W_1b350 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b354 : bv 32 := 0x00040513.
Lemma F_1b354 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b484 : word) = Some W_1b354.
Proof. vm_refl. Qed.
Lemma D_1b354 : decode_any W_1b354 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b358 : bv 32 := 0x00000593.
Lemma F_1b358 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b488 : word) = Some W_1b358.
Proof. vm_refl. Qed.
Lemma D_1b358 : decode_any W_1b358 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b35c : bv 32 := 0x00000613.
Lemma F_1b35c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b48c : word) = Some W_1b35c.
Proof. vm_refl. Qed.
Lemma D_1b35c : decode_any W_1b35c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b360 : bv 32 := 0x000680e7.
Lemma F_1b360 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b490 : word) = Some W_1b360.
Proof. vm_refl. Qed.
Lemma D_1b360 : decode_any W_1b360 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b364 : bv 32 := 0x00843503.
Lemma F_1b364 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b494 : word) = Some W_1b364.
Proof. vm_refl. Qed.
Lemma D_1b364 : decode_any W_1b364 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b368 : bv 32 := 0x01043583.
Lemma F_1b368 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b498 : word) = Some W_1b368.
Proof. vm_refl. Qed.
Lemma D_1b368 : decode_any W_1b368 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b36c : bv 32 := 0x00b50c63.
Lemma F_1b36c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b49c : word) = Some W_1b36c.
Proof. vm_refl. Qed.
Lemma D_1b36c : decode_any W_1b36c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b384 : bv 32 := 0x00008517.
Lemma F_1b384 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4b4 : word) = Some W_1b384.
Proof. vm_refl. Qed.
Lemma D_1b384 : decode_any W_1b384 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b388 : bv 32 := 0x8dc53403.
Lemma F_1b388 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4b8 : word) = Some W_1b388.
Proof. vm_refl. Qed.
Lemma D_1b388 : decode_any W_1b388 = Some (Load SZ8 true 8 10 2268, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b38c : bv 32 := 0x0a040e63.
Lemma F_1b38c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4bc : word) = Some W_1b38c.
Proof. vm_refl. Qed.
Lemma D_1b38c : decode_any W_1b38c = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b390 : bv 32 := 0x08c42503.
Lemma F_1b390 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4c0 : word) = Some W_1b390.
Proof. vm_refl. Qed.
Lemma D_1b390 : decode_any W_1b390 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b394 : bv 32 := 0x00054663.
Lemma F_1b394 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4c4 : word) = Some W_1b394.
Proof. vm_refl. Qed.
Lemma D_1b394 : decode_any W_1b394 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b3a0 : bv 32 := 0x02843503.
Lemma F_1b3a0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4d0 : word) = Some W_1b3a0.
Proof. vm_refl. Qed.
Lemma D_1b3a0 : decode_any W_1b3a0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b3a4 : bv 32 := 0x03843583.
Lemma F_1b3a4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4d4 : word) = Some W_1b3a4.
Proof. vm_refl. Qed.
Lemma D_1b3a4 : decode_any W_1b3a4 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b3a8 : bv 32 := 0x00b50c63.
Lemma F_1b3a8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4d8 : word) = Some W_1b3a8.
Proof. vm_refl. Qed.
Lemma D_1b3a8 : decode_any W_1b3a8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b3c0 : bv 32 := 0x00843503.
Lemma F_1b3c0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4f0 : word) = Some W_1b3c0.
Proof. vm_refl. Qed.
Lemma D_1b3c0 : decode_any W_1b3c0 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b3c4 : bv 32 := 0x01043583.
Lemma F_1b3c4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4f4 : word) = Some W_1b3c4.
Proof. vm_refl. Qed.
Lemma D_1b3c4 : decode_any W_1b3c4 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b3c8 : bv 32 := 0x08b50063.
Lemma F_1b3c8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b4f8 : word) = Some W_1b3c8.
Proof. vm_refl. Qed.
Lemma D_1b3c8 : decode_any W_1b3c8 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b448 : bv 32 := 0x00813083.
Lemma F_1b448 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b578 : word) = Some W_1b448.
Proof. vm_refl. Qed.
Lemma D_1b448 : decode_any W_1b448 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b44c : bv 32 := 0x00013403.
Lemma F_1b44c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b57c : word) = Some W_1b44c.
Proof. vm_refl. Qed.
Lemma D_1b44c : decode_any W_1b44c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b450 : bv 32 := 0x01010113.
Lemma F_1b450 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b580 : word) = Some W_1b450.
Proof. vm_refl. Qed.
Lemma D_1b450 : decode_any W_1b450 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b454 : bv 32 := 0x00008067.
Lemma F_1b454 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b584 : word) = Some W_1b454.
Proof. vm_refl. Qed.
Lemma D_1b454 : decode_any W_1b454 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b458 : bv 32 := 0xff010113.
Lemma F_1b458 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b588 : word) = Some W_1b458.
Proof. vm_refl. Qed.
Lemma D_1b458 : decode_any W_1b458 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b45c : bv 32 := 0x00113423.
Lemma F_1b45c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b58c : word) = Some W_1b45c.
Proof. vm_refl. Qed.
Lemma D_1b45c : decode_any W_1b45c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b460 : bv 32 := 0x00813023.
Lemma F_1b460 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b590 : word) = Some W_1b460.
Proof. vm_refl. Qed.
Lemma D_1b460 : decode_any W_1b460 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b464 : bv 32 := 0x00078517.
Lemma F_1b464 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b594 : word) = Some W_1b464.
Proof. vm_refl. Qed.
Lemma D_1b464 : decode_any W_1b464 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b468 : bv 32 := 0x0fc50413.
Lemma F_1b468 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b598 : word) = Some W_1b468.
Proof. vm_refl. Qed.
Lemma D_1b468 : decode_any W_1b468 = Some (OpImm ALU_ADD 8 10 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b46c : bv 32 := 0x00040513.
Lemma F_1b46c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b59c : word) = Some W_1b46c.
Proof. vm_refl. Qed.
Lemma D_1b46c : decode_any W_1b46c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b470 : bv 32 := 0x258050ef.
Lemma F_1b470 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b5a0 : word) = Some W_1b470.
Proof. vm_refl. Qed.
Lemma D_1b470 : decode_any W_1b470 = Some (Jal 1 21080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b474 : bv 32 := 0x00840513.
Lemma F_1b474 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b5a4 : word) = Some W_1b474.
Proof. vm_refl. Qed.
Lemma D_1b474 : decode_any W_1b474 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b478 : bv 32 := 0x00813083.
Lemma F_1b478 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b5a8 : word) = Some W_1b478.
Proof. vm_refl. Qed.
Lemma D_1b478 : decode_any W_1b478 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b47c : bv 32 := 0x00013403.
Lemma F_1b47c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b5ac : word) = Some W_1b47c.
Proof. vm_refl. Qed.
Lemma D_1b47c : decode_any W_1b47c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b480 : bv 32 := 0x01010113.
Lemma F_1b480 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b5b0 : word) = Some W_1b480.
Proof. vm_refl. Qed.
Lemma D_1b480 : decode_any W_1b480 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b484 : bv 32 := 0x00008067.
Lemma F_1b484 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b5b4 : word) = Some W_1b484.
Proof. vm_refl. Qed.
Lemma D_1b484 : decode_any W_1b484 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b494 : bv 32 := 0x00008067.
Lemma F_1b494 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b5c4 : word) = Some W_1b494.
Proof. vm_refl. Qed.
Lemma D_1b494 : decode_any W_1b494 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4c4 : bv 32 := 0xf9010113.
Lemma F_1b4c4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b5f4 : word) = Some W_1b4c4.
Proof. vm_refl. Qed.
Lemma D_1b4c4 : decode_any W_1b4c4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4c8 : bv 32 := 0x06113423.
Lemma F_1b4c8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b5f8 : word) = Some W_1b4c8.
Proof. vm_refl. Qed.
Lemma D_1b4c8 : decode_any W_1b4c8 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4cc : bv 32 := 0x06813023.
Lemma F_1b4cc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b5fc : word) = Some W_1b4cc.
Proof. vm_refl. Qed.
Lemma D_1b4cc : decode_any W_1b4cc = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4d0 : bv 32 := 0x04913c23.
Lemma F_1b4d0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b600 : word) = Some W_1b4d0.
Proof. vm_refl. Qed.
Lemma D_1b4d0 : decode_any W_1b4d0 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4d4 : bv 32 := 0x05213823.
Lemma F_1b4d4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b604 : word) = Some W_1b4d4.
Proof. vm_refl. Qed.
Lemma D_1b4d4 : decode_any W_1b4d4 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4d8 : bv 32 := 0x05313423.
Lemma F_1b4d8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b608 : word) = Some W_1b4d8.
Proof. vm_refl. Qed.
Lemma D_1b4d8 : decode_any W_1b4d8 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4dc : bv 32 := 0x05413023.
Lemma F_1b4dc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b60c : word) = Some W_1b4dc.
Proof. vm_refl. Qed.
Lemma D_1b4dc : decode_any W_1b4dc = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4e0 : bv 32 := 0x03513c23.
Lemma F_1b4e0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b610 : word) = Some W_1b4e0.
Proof. vm_refl. Qed.
Lemma D_1b4e0 : decode_any W_1b4e0 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4e4 : bv 32 := 0x03613823.
Lemma F_1b4e4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b614 : word) = Some W_1b4e4.
Proof. vm_refl. Qed.
Lemma D_1b4e4 : decode_any W_1b4e4 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4e8 : bv 32 := 0x00060413.
Lemma F_1b4e8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b618 : word) = Some W_1b4e8.
Proof. vm_refl. Qed.
Lemma D_1b4e8 : decode_any W_1b4e8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4ec : bv 32 := 0x00050493.
Lemma F_1b4ec : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b61c : word) = Some W_1b4ec.
Proof. vm_refl. Qed.
Lemma D_1b4ec : decode_any W_1b4ec = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4f0 : bv 32 := 0x00006517.
Lemma F_1b4f0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b620 : word) = Some W_1b4f0.
Proof. vm_refl. Qed.
Lemma D_1b4f0 : decode_any W_1b4f0 = Some (Auipc 10 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4f4 : bv 32 := 0x64853a83.
Lemma F_1b4f4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b624 : word) = Some W_1b4f4.
Proof. vm_refl. Qed.
Lemma D_1b4f4 : decode_any W_1b4f4 = Some (Load SZ8 true 21 10 1608, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4f8 : bv 32 := 0x000ab503.
Lemma F_1b4f8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b628 : word) = Some W_1b4f8.
Proof. vm_refl. Qed.
Lemma D_1b4f8 : decode_any W_1b4f8 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b4fc : bv 32 := 0x02a13423.
Lemma F_1b4fc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b62c : word) = Some W_1b4fc.
Proof. vm_refl. Qed.
Lemma D_1b4fc : decode_any W_1b4fc = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b500 : bv 32 := 0x0284b503.
Lemma F_1b500 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b630 : word) = Some W_1b500.
Proof. vm_refl. Qed.
Lemma D_1b500 : decode_any W_1b500 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b504 : bv 32 := 0x0384b603.
Lemma F_1b504 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b634 : word) = Some W_1b504.
Proof. vm_refl. Qed.
Lemma D_1b504 : decode_any W_1b504 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b508 : bv 32 := 0x40c50b33.
Lemma F_1b508 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b638 : word) = Some W_1b508.
Proof. vm_refl. Qed.
Lemma D_1b508 : decode_any W_1b508 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b50c : bv 32 := 0x00c546b3.
Lemma F_1b50c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b63c : word) = Some W_1b50c.
Proof. vm_refl. Qed.
Lemma D_1b50c : decode_any W_1b50c = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b510 : bv 32 := 0x00c13423.
Lemma F_1b510 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b640 : word) = Some W_1b510.
Proof. vm_refl. Qed.
Lemma D_1b510 : decode_any W_1b510 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b514 : bv 32 := 0x01613823.
Lemma F_1b514 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b644 : word) = Some W_1b514.
Proof. vm_refl. Qed.
Lemma D_1b514 : decode_any W_1b514 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b518 : bv 32 := 0x00b13c23.
Lemma F_1b518 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b648 : word) = Some W_1b518.
Proof. vm_refl. Qed.
Lemma D_1b518 : decode_any W_1b518 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b51c : bv 32 := 0x02813023.
Lemma F_1b51c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b64c : word) = Some W_1b51c.
Proof. vm_refl. Qed.
Lemma D_1b51c : decode_any W_1b51c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b520 : bv 32 := 0x008b0b33.
Lemma F_1b520 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b650 : word) = Some W_1b520.
Proof. vm_refl. Qed.
Lemma D_1b520 : decode_any W_1b520 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b524 : bv 32 := 0x00d03933.
Lemma F_1b524 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b654 : word) = Some W_1b524.
Proof. vm_refl. Qed.
Lemma D_1b524 : decode_any W_1b524 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b528 : bv 32 := 0x00c50663.
Lemma F_1b528 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b658 : word) = Some W_1b528.
Proof. vm_refl. Qed.
Lemma D_1b528 : decode_any W_1b528 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b52c : bv 32 := 0x00810993.
Lemma F_1b52c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b65c : word) = Some W_1b52c.
Proof. vm_refl. Qed.
Lemma D_1b52c : decode_any W_1b52c = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b530 : bv 32 := 0x0080006f.
Lemma F_1b530 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b660 : word) = Some W_1b530.
Proof. vm_refl. Qed.
Lemma D_1b530 : decode_any W_1b530 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b534 : bv 32 := 0x01810993.
Lemma F_1b534 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b664 : word) = Some W_1b534.
Proof. vm_refl. Qed.
Lemma D_1b534 : decode_any W_1b534 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b538 : bv 32 := 0x0784a503.
Lemma F_1b538 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b668 : word) = Some W_1b538.
Proof. vm_refl. Qed.
Lemma D_1b538 : decode_any W_1b538 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b53c : bv 32 := 0x00190913.
Lemma F_1b53c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b66c : word) = Some W_1b53c.
Proof. vm_refl. Qed.
Lemma D_1b53c : decode_any W_1b53c = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b540 : bv 32 := 0x04200893.
Lemma F_1b540 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b670 : word) = Some W_1b540.
Proof. vm_refl. Qed.
Lemma D_1b540 : decode_any W_1b540 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b544 : bv 32 := 0x00098593.
Lemma F_1b544 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b674 : word) = Some W_1b544.
Proof. vm_refl. Qed.
Lemma D_1b544 : decode_any W_1b544 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b548 : bv 32 := 0x00090613.
Lemma F_1b548 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b678 : word) = Some W_1b548.
Proof. vm_refl. Qed.
Lemma D_1b548 : decode_any W_1b548 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b54c : bv 32 := 0x00000073.
Lemma F_1b54c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b67c : word) = Some W_1b54c.
Proof. vm_refl. Qed.
Lemma D_1b54c : decode_any W_1b54c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1b54c : is_ecall W_1b54c = true.
Proof. reflexivity. Qed.

Definition W_1b550 : bv 32 := 0xc81fd0ef.
Lemma F_1b550 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b680 : word) = Some W_1b550.
Proof. vm_refl. Qed.
Lemma D_1b550 : decode_any W_1b550 = Some (Jal 1 2088064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b554 : bv 32 := 0x09651863.
Lemma F_1b554 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b684 : word) = Some W_1b554.
Proof. vm_refl. Qed.
Lemma D_1b554 : decode_any W_1b554 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b558 : bv 32 := 0x0584b503.
Lemma F_1b558 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b688 : word) = Some W_1b558.
Proof. vm_refl. Qed.
Lemma D_1b558 : decode_any W_1b558 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b55c : bv 32 := 0x0604b583.
Lemma F_1b55c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b68c : word) = Some W_1b55c.
Proof. vm_refl. Qed.
Lemma D_1b55c : decode_any W_1b55c = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b560 : bv 32 := 0x00b505b3.
Lemma F_1b560 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b690 : word) = Some W_1b560.
Proof. vm_refl. Qed.
Lemma D_1b560 : decode_any W_1b560 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b564 : bv 32 := 0x02b4b023.
Lemma F_1b564 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b694 : word) = Some W_1b564.
Proof. vm_refl. Qed.
Lemma D_1b564 : decode_any W_1b564 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b568 : bv 32 := 0x02a4b423.
Lemma F_1b568 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b698 : word) = Some W_1b568.
Proof. vm_refl. Qed.
Lemma D_1b568 : decode_any W_1b568 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b56c : bv 32 := 0x02a4bc23.
Lemma F_1b56c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b69c : word) = Some W_1b56c.
Proof. vm_refl. Qed.
Lemma D_1b56c : decode_any W_1b56c = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b570 : bv 32 := 0x00040513.
Lemma F_1b570 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6a0 : word) = Some W_1b570.
Proof. vm_refl. Qed.
Lemma D_1b570 : decode_any W_1b570 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b574 : bv 32 := 0x000ab583.
Lemma F_1b574 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6a4 : word) = Some W_1b574.
Proof. vm_refl. Qed.
Lemma D_1b574 : decode_any W_1b574 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b578 : bv 32 := 0x02813603.
Lemma F_1b578 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6a8 : word) = Some W_1b578.
Proof. vm_refl. Qed.
Lemma D_1b578 : decode_any W_1b578 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b57c : bv 32 := 0x0cc59a63.
Lemma F_1b57c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6ac : word) = Some W_1b57c.
Proof. vm_refl. Qed.
Lemma D_1b57c : decode_any W_1b57c = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b580 : bv 32 := 0x06813083.
Lemma F_1b580 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6b0 : word) = Some W_1b580.
Proof. vm_refl. Qed.
Lemma D_1b580 : decode_any W_1b580 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b584 : bv 32 := 0x06013403.
Lemma F_1b584 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6b4 : word) = Some W_1b584.
Proof. vm_refl. Qed.
Lemma D_1b584 : decode_any W_1b584 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b588 : bv 32 := 0x05813483.
Lemma F_1b588 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6b8 : word) = Some W_1b588.
Proof. vm_refl. Qed.
Lemma D_1b588 : decode_any W_1b588 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b58c : bv 32 := 0x05013903.
Lemma F_1b58c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6bc : word) = Some W_1b58c.
Proof. vm_refl. Qed.
Lemma D_1b58c : decode_any W_1b58c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b590 : bv 32 := 0x04813983.
Lemma F_1b590 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6c0 : word) = Some W_1b590.
Proof. vm_refl. Qed.
Lemma D_1b590 : decode_any W_1b590 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b594 : bv 32 := 0x04013a03.
Lemma F_1b594 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6c4 : word) = Some W_1b594.
Proof. vm_refl. Qed.
Lemma D_1b594 : decode_any W_1b594 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b598 : bv 32 := 0x03813a83.
Lemma F_1b598 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6c8 : word) = Some W_1b598.
Proof. vm_refl. Qed.
Lemma D_1b598 : decode_any W_1b598 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b59c : bv 32 := 0x03013b03.
Lemma F_1b59c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6cc : word) = Some W_1b59c.
Proof. vm_refl. Qed.
Lemma D_1b59c : decode_any W_1b59c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5a0 : bv 32 := 0x07010113.
Lemma F_1b5a0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6d0 : word) = Some W_1b5a0.
Proof. vm_refl. Qed.
Lemma D_1b5a0 : decode_any W_1b5a0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5a4 : bv 32 := 0x00008067.
Lemma F_1b5a4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6d4 : word) = Some W_1b5a4.
Proof. vm_refl. Qed.
Lemma D_1b5a4 : decode_any W_1b5a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5a8 : bv 32 := 0x00800713.
Lemma F_1b5a8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6d8 : word) = Some W_1b5a8.
Proof. vm_refl. Qed.
Lemma D_1b5a8 : decode_any W_1b5a8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5ac : bv 32 := 0x000a0593.
Lemma F_1b5ac : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6dc : word) = Some W_1b5ac.
Proof. vm_refl. Qed.
Lemma D_1b5ac : decode_any W_1b5ac = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5b0 : bv 32 := 0x00e98733.
Lemma F_1b5b0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6e0 : word) = Some W_1b5b0.
Proof. vm_refl. Qed.
Lemma D_1b5b0 : decode_any W_1b5b0 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5b4 : bv 32 := 0x00073783.
Lemma F_1b5b4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6e4 : word) = Some W_1b5b4.
Proof. vm_refl. Qed.
Lemma D_1b5b4 : decode_any W_1b5b4 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5b8 : bv 32 := 0x40ab0b33.
Lemma F_1b5b8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6e8 : word) = Some W_1b5b8.
Proof. vm_refl. Qed.
Lemma D_1b5b8 : decode_any W_1b5b8 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5bc : bv 32 := 0x0784a503.
Lemma F_1b5bc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6ec : word) = Some W_1b5bc.
Proof. vm_refl. Qed.
Lemma D_1b5bc : decode_any W_1b5bc = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5c0 : bv 32 := 0x40c9093b.
Lemma F_1b5c0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6f0 : word) = Some W_1b5c0.
Proof. vm_refl. Qed.
Lemma D_1b5c0 : decode_any W_1b5c0 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5c4 : bv 32 := 0x40d787b3.
Lemma F_1b5c4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6f4 : word) = Some W_1b5c4.
Proof. vm_refl. Qed.
Lemma D_1b5c4 : decode_any W_1b5c4 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5c8 : bv 32 := 0x00f73023.
Lemma F_1b5c8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6f8 : word) = Some W_1b5c8.
Proof. vm_refl. Qed.
Lemma D_1b5c8 : decode_any W_1b5c8 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5cc : bv 32 := 0x04200893.
Lemma F_1b5cc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b6fc : word) = Some W_1b5cc.
Proof. vm_refl. Qed.
Lemma D_1b5cc : decode_any W_1b5cc = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5d0 : bv 32 := 0x00090613.
Lemma F_1b5d0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b700 : word) = Some W_1b5d0.
Proof. vm_refl. Qed.
Lemma D_1b5d0 : decode_any W_1b5d0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5d4 : bv 32 := 0x00000073.
Lemma F_1b5d4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b704 : word) = Some W_1b5d4.
Proof. vm_refl. Qed.
Lemma D_1b5d4 : decode_any W_1b5d4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1b5d4 : is_ecall W_1b5d4 = true.
Proof. reflexivity. Qed.

Definition W_1b5d8 : bv 32 := 0xbf9fd0ef.
Lemma F_1b5d8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b708 : word) = Some W_1b5d8.
Proof. vm_refl. Qed.
Lemma D_1b5d8 : decode_any W_1b5d8 = Some (Jal 1 2087928, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5dc : bv 32 := 0x000a0993.
Lemma F_1b5dc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b70c : word) = Some W_1b5dc.
Proof. vm_refl. Qed.
Lemma D_1b5dc : decode_any W_1b5dc = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5e0 : bv 32 := 0xf7650ce3.
Lemma F_1b5e0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b710 : word) = Some W_1b5e0.
Proof. vm_refl. Qed.
Lemma D_1b5e0 : decode_any W_1b5e0 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5e4 : bv 32 := 0x02054c63.
Lemma F_1b5e4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b714 : word) = Some W_1b5e4.
Proof. vm_refl. Qed.
Lemma D_1b5e4 : decode_any W_1b5e4 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5e8 : bv 32 := 0x0089b583.
Lemma F_1b5e8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b718 : word) = Some W_1b5e8.
Proof. vm_refl. Qed.
Lemma D_1b5e8 : decode_any W_1b5e8 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5ec : bv 32 := 0x00a5b633.
Lemma F_1b5ec : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b71c : word) = Some W_1b5ec.
Proof. vm_refl. Qed.
Lemma D_1b5ec : decode_any W_1b5ec = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5f0 : bv 32 := 0x00461a13.
Lemma F_1b5f0 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b720 : word) = Some W_1b5f0.
Proof. vm_refl. Qed.
Lemma D_1b5f0 : decode_any W_1b5f0 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5f4 : bv 32 := 0x01498a33.
Lemma F_1b5f4 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b724 : word) = Some W_1b5f4.
Proof. vm_refl. Qed.
Lemma D_1b5f4 : decode_any W_1b5f4 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5f8 : bv 32 := 0x000a3703.
Lemma F_1b5f8 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b728 : word) = Some W_1b5f8.
Proof. vm_refl. Qed.
Lemma D_1b5f8 : decode_any W_1b5f8 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b5fc : bv 32 := 0x40c006b3.
Lemma F_1b5fc : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b72c : word) = Some W_1b5fc.
Proof. vm_refl. Qed.
Lemma D_1b5fc : decode_any W_1b5fc = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b600 : bv 32 := 0x00b6f6b3.
Lemma F_1b600 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b730 : word) = Some W_1b600.
Proof. vm_refl. Qed.
Lemma D_1b600 : decode_any W_1b600 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b604 : bv 32 := 0x40d506b3.
Lemma F_1b604 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b734 : word) = Some W_1b604.
Proof. vm_refl. Qed.
Lemma D_1b604 : decode_any W_1b604 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b608 : bv 32 := 0x00d70733.
Lemma F_1b608 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b738 : word) = Some W_1b608.
Proof. vm_refl. Qed.
Lemma D_1b608 : decode_any W_1b608 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b60c : bv 32 := 0x00ea3023.
Lemma F_1b60c : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b73c : word) = Some W_1b60c.
Proof. vm_refl. Qed.
Lemma D_1b60c : decode_any W_1b60c = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b610 : bv 32 := 0xf8a5fce3.
Lemma F_1b610 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b740 : word) = Some W_1b610.
Proof. vm_refl. Qed.
Lemma D_1b610 : decode_any W_1b610 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b614 : bv 32 := 0x01800713.
Lemma F_1b614 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b744 : word) = Some W_1b614.
Proof. vm_refl. Qed.
Lemma D_1b614 : decode_any W_1b614 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b618 : bv 32 := 0xf95ff06f.
Lemma F_1b618 : fetch_word Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments (0x1b748 : word) = Some W_1b618.
Proof. vm_refl. Qed.
Lemma D_1b618 : decode_any W_1b618 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
