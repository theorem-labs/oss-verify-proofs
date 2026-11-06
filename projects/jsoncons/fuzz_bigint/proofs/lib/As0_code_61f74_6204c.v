(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_61f74 : bv 32 := 0xfb010113.
Lemma F_61f74 : fetch_word Asan.M.loaded_segments (0x61f74 : word) = Some W_61f74.
Proof. vm_refl. Qed.
Lemma D_61f74 : decode_any W_61f74 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_61f78 : bv 32 := 0x04113423.
Lemma F_61f78 : fetch_word Asan.M.loaded_segments (0x61f78 : word) = Some W_61f78.
Proof. vm_refl. Qed.
Lemma D_61f78 : decode_any W_61f78 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_61f7c : bv 32 := 0x04813023.
Lemma F_61f7c : fetch_word Asan.M.loaded_segments (0x61f7c : word) = Some W_61f7c.
Proof. vm_refl. Qed.
Lemma D_61f7c : decode_any W_61f7c = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_61f80 : bv 32 := 0x00074517.
Lemma F_61f80 : fetch_word Asan.M.loaded_segments (0x61f80 : word) = Some W_61f80.
Proof. vm_refl. Qed.
Lemma D_61f80 : decode_any W_61f80 = Some (Auipc 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61f84 : bv 32 := 0x97853503.
Lemma F_61f84 : fetch_word Asan.M.loaded_segments (0x61f84 : word) = Some W_61f84.
Proof. vm_refl. Qed.
Lemma D_61f84 : decode_any W_61f84 = Some (Load SZ8 true 10 10 2424, 4%Z).
Proof. vm_refl. Qed.

Definition W_61f88 : bv 32 := 0x0a051463.
Lemma F_61f88 : fetch_word Asan.M.loaded_segments (0x61f88 : word) = Some W_61f88.
Proof. vm_refl. Qed.
Lemma D_61f88 : decode_any W_61f88 = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_61f8c : bv 32 := 0xfffae517.
Lemma F_61f8c : fetch_word Asan.M.loaded_segments (0x61f8c : word) = Some W_61f8c.
Proof. vm_refl. Qed.
Lemma D_61f8c : decode_any W_61f8c = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

Definition W_61f90 : bv 32 := 0x47c53403.
Lemma F_61f90 : fetch_word Asan.M.loaded_segments (0x61f90 : word) = Some W_61f90.
Proof. vm_refl. Qed.
Lemma D_61f90 : decode_any W_61f90 = Some (Load SZ8 true 8 10 1148, 4%Z).
Proof. vm_refl. Qed.

Definition W_61f94 : bv 32 := 0x02813423.
Lemma F_61f94 : fetch_word Asan.M.loaded_segments (0x61f94 : word) = Some W_61f94.
Proof. vm_refl. Qed.
Lemma D_61f94 : decode_any W_61f94 = Some (Store SZ8 2 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61f98 : bv 32 := 0x02813823.
Lemma F_61f98 : fetch_word Asan.M.loaded_segments (0x61f98 : word) = Some W_61f98.
Proof. vm_refl. Qed.
Lemma D_61f98 : decode_any W_61f98 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61f9c : bv 32 := 0x02813c23.
Lemma F_61f9c : fetch_word Asan.M.loaded_segments (0x61f9c : word) = Some W_61f9c.
Proof. vm_refl. Qed.
Lemma D_61f9c : decode_any W_61f9c = Some (Store SZ8 2 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fa0 : bv 32 := 0x02810593.
Lemma F_61fa0 : fetch_word Asan.M.loaded_segments (0x61fa0 : word) = Some W_61fa0.
Proof. vm_refl. Qed.
Lemma D_61fa0 : decode_any W_61fa0 = Some (OpImm ALU_ADD 11 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fa4 : bv 32 := 0x00000513.
Lemma F_61fa4 : fetch_word Asan.M.loaded_segments (0x61fa4 : word) = Some W_61fa4.
Proof. vm_refl. Qed.
Lemma D_61fa4 : decode_any W_61fa4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fa8 : bv 32 := 0xc9deb0ef.
Lemma F_61fa8 : fetch_word Asan.M.loaded_segments (0x61fa8 : word) = Some W_61fa8.
Proof. vm_refl. Qed.
Lemma D_61fa8 : decode_any W_61fa8 = Some (Jal 1 2014364, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fac : bv 32 := 0x08051c63.
Lemma F_61fac : fetch_word Asan.M.loaded_segments (0x61fac : word) = Some W_61fac.
Proof. vm_refl. Qed.
Lemma D_61fac : decode_any W_61fac = Some (Branch BC_NE 10 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fb0 : bv 32 := 0x03012503.
Lemma F_61fb0 : fetch_word Asan.M.loaded_segments (0x61fb0 : word) = Some W_61fb0.
Proof. vm_refl. Qed.
Lemma D_61fb0 : decode_any W_61fb0 = Some (Load SZ4 true 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fb4 : bv 32 := 0x00200593.
Lemma F_61fb4 : fetch_word Asan.M.loaded_segments (0x61fb4 : word) = Some W_61fb4.
Proof. vm_refl. Qed.
Lemma D_61fb4 : decode_any W_61fb4 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fb8 : bv 32 := 0x06b50c63.
Lemma F_61fb8 : fetch_word Asan.M.loaded_segments (0x61fb8 : word) = Some W_61fb8.
Proof. vm_refl. Qed.
Lemma D_61fb8 : decode_any W_61fb8 = Some (Branch BC_EQ 10 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fbc : bv 32 := 0x02813503.
Lemma F_61fbc : fetch_word Asan.M.loaded_segments (0x61fbc : word) = Some W_61fbc.
Proof. vm_refl. Qed.
Lemma D_61fbc : decode_any W_61fbc = Some (Load SZ8 true 10 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fc0 : bv 32 := 0x03813583.
Lemma F_61fc0 : fetch_word Asan.M.loaded_segments (0x61fc0 : word) = Some W_61fc0.
Proof. vm_refl. Qed.
Lemma D_61fc0 : decode_any W_61fc0 = Some (Load SZ8 true 11 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fc4 : bv 32 := 0x00b505b3.
Lemma F_61fc4 : fetch_word Asan.M.loaded_segments (0x61fc4 : word) = Some W_61fc4.
Proof. vm_refl. Qed.
Lemma D_61fc4 : decode_any W_61fc4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fc8 : bv 32 := 0xfffbd617.
Lemma F_61fc8 : fetch_word Asan.M.loaded_segments (0x61fc8 : word) = Some W_61fc8.
Proof. vm_refl. Qed.
Lemma D_61fc8 : decode_any W_61fc8 = Some (Auipc 12 1048509, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fcc : bv 32 := 0x6d360613.
Lemma F_61fcc : fetch_word Asan.M.loaded_segments (0x61fcc : word) = Some W_61fcc.
Proof. vm_refl. Qed.
Lemma D_61fcc : decode_any W_61fcc = Some (OpImm ALU_ADD 12 12 1747, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fd0 : bv 32 := 0x0b4050ef.
Lemma F_61fd0 : fetch_word Asan.M.loaded_segments (0x61fd0 : word) = Some W_61fd0.
Proof. vm_refl. Qed.
Lemma D_61fd0 : decode_any W_61fd0 = Some (Jal 1 20660, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fd4 : bv 32 := 0x03012503.
Lemma F_61fd4 : fetch_word Asan.M.loaded_segments (0x61fd4 : word) = Some W_61fd4.
Proof. vm_refl. Qed.
Lemma D_61fd4 : decode_any W_61fd4 = Some (Load SZ4 true 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fd8 : bv 32 := 0x00100593.
Lemma F_61fd8 : fetch_word Asan.M.loaded_segments (0x61fd8 : word) = Some W_61fd8.
Proof. vm_refl. Qed.
Lemma D_61fd8 : decode_any W_61fd8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fdc : bv 32 := 0x04b51a63.
Lemma F_61fdc : fetch_word Asan.M.loaded_segments (0x61fdc : word) = Some W_61fdc.
Proof. vm_refl. Qed.
Lemma D_61fdc : decode_any W_61fdc = Some (Branch BC_NE 10 11 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fe0 : bv 32 := 0x02813023.
Lemma F_61fe0 : fetch_word Asan.M.loaded_segments (0x61fe0 : word) = Some W_61fe0.
Proof. vm_refl. Qed.
Lemma D_61fe0 : decode_any W_61fe0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fe4 : bv 32 := 0x00813c23.
Lemma F_61fe4 : fetch_word Asan.M.loaded_segments (0x61fe4 : word) = Some W_61fe4.
Proof. vm_refl. Qed.
Lemma D_61fe4 : decode_any W_61fe4 = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fe8 : bv 32 := 0x00813823.
Lemma F_61fe8 : fetch_word Asan.M.loaded_segments (0x61fe8 : word) = Some W_61fe8.
Proof. vm_refl. Qed.
Lemma D_61fe8 : decode_any W_61fe8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61fec : bv 32 := 0x00813423.
Lemma F_61fec : fetch_word Asan.M.loaded_segments (0x61fec : word) = Some W_61fec.
Proof. vm_refl. Qed.
Lemma D_61fec : decode_any W_61fec = Some (Store SZ8 2 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ff0 : bv 32 := 0x02010593.
Lemma F_61ff0 : fetch_word Asan.M.loaded_segments (0x61ff0 : word) = Some W_61ff0.
Proof. vm_refl. Qed.
Lemma D_61ff0 : decode_any W_61ff0 = Some (OpImm ALU_ADD 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ff4 : bv 32 := 0x01810613.
Lemma F_61ff4 : fetch_word Asan.M.loaded_segments (0x61ff4 : word) = Some W_61ff4.
Proof. vm_refl. Qed.
Lemma D_61ff4 : decode_any W_61ff4 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ff8 : bv 32 := 0x01010693.
Lemma F_61ff8 : fetch_word Asan.M.loaded_segments (0x61ff8 : word) = Some W_61ff8.
Proof. vm_refl. Qed.
Lemma D_61ff8 : decode_any W_61ff8 = Some (OpImm ALU_ADD 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61ffc : bv 32 := 0x00810713.
Lemma F_61ffc : fetch_word Asan.M.loaded_segments (0x61ffc : word) = Some W_61ffc.
Proof. vm_refl. Qed.
Lemma D_61ffc : decode_any W_61ffc = Some (OpImm ALU_ADD 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_62000 : bv 32 := 0x00000513.
Lemma F_62000 : fetch_word Asan.M.loaded_segments (0x62000 : word) = Some W_62000.
Proof. vm_refl. Qed.
Lemma D_62000 : decode_any W_62000 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_62004 : bv 32 := 0x34c180ef.
Lemma F_62004 : fetch_word Asan.M.loaded_segments (0x62004 : word) = Some W_62004.
Proof. vm_refl. Qed.
Lemma D_62004 : decode_any W_62004 = Some (Jal 1 99148, 4%Z).
Proof. vm_refl. Qed.

Definition W_62008 : bv 32 := 0x02013503.
Lemma F_62008 : fetch_word Asan.M.loaded_segments (0x62008 : word) = Some W_62008.
Proof. vm_refl. Qed.
Lemma D_62008 : decode_any W_62008 = Some (Load SZ8 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6200c : bv 32 := 0x01813583.
Lemma F_6200c : fetch_word Asan.M.loaded_segments (0x6200c : word) = Some W_6200c.
Proof. vm_refl. Qed.
Lemma D_6200c : decode_any W_6200c = Some (Load SZ8 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_62010 : bv 32 := 0xfffb9617.
Lemma F_62010 : fetch_word Asan.M.loaded_segments (0x62010 : word) = Some W_62010.
Proof. vm_refl. Qed.
Lemma D_62010 : decode_any W_62010 = Some (Auipc 12 1048505, 4%Z).
Proof. vm_refl. Qed.

Definition W_62014 : bv 32 := 0xa8060613.
Lemma F_62014 : fetch_word Asan.M.loaded_segments (0x62014 : word) = Some W_62014.
Proof. vm_refl. Qed.
Lemma D_62014 : decode_any W_62014 = Some (OpImm ALU_ADD 12 12 2688, 4%Z).
Proof. vm_refl. Qed.

Definition W_62018 : bv 32 := 0x06c050ef.
Lemma F_62018 : fetch_word Asan.M.loaded_segments (0x62018 : word) = Some W_62018.
Proof. vm_refl. Qed.
Lemma D_62018 : decode_any W_62018 = Some (Jal 1 20588, 4%Z).
Proof. vm_refl. Qed.

Definition W_6201c : bv 32 := 0x00100513.
Lemma F_6201c : fetch_word Asan.M.loaded_segments (0x6201c : word) = Some W_6201c.
Proof. vm_refl. Qed.
Lemma D_6201c : decode_any W_6201c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_62020 : bv 32 := 0x04813083.
Lemma F_62020 : fetch_word Asan.M.loaded_segments (0x62020 : word) = Some W_62020.
Proof. vm_refl. Qed.
Lemma D_62020 : decode_any W_62020 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_62024 : bv 32 := 0x04013403.
Lemma F_62024 : fetch_word Asan.M.loaded_segments (0x62024 : word) = Some W_62024.
Proof. vm_refl. Qed.
Lemma D_62024 : decode_any W_62024 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_62028 : bv 32 := 0x05010113.
Lemma F_62028 : fetch_word Asan.M.loaded_segments (0x62028 : word) = Some W_62028.
Proof. vm_refl. Qed.
Lemma D_62028 : decode_any W_62028 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6202c : bv 32 := 0x00008067.
Lemma F_6202c : fetch_word Asan.M.loaded_segments (0x6202c : word) = Some W_6202c.
Proof. vm_refl. Qed.
Lemma D_6202c : decode_any W_6202c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_62030 : bv 32 := 0x00000513.
Lemma F_62030 : fetch_word Asan.M.loaded_segments (0x62030 : word) = Some W_62030.
Proof. vm_refl. Qed.
Lemma D_62030 : decode_any W_62030 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_62034 : bv 32 := 0x04813083.
Lemma F_62034 : fetch_word Asan.M.loaded_segments (0x62034 : word) = Some W_62034.
Proof. vm_refl. Qed.
Lemma D_62034 : decode_any W_62034 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_62038 : bv 32 := 0x04013403.
Lemma F_62038 : fetch_word Asan.M.loaded_segments (0x62038 : word) = Some W_62038.
Proof. vm_refl. Qed.
Lemma D_62038 : decode_any W_62038 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6203c : bv 32 := 0x05010113.
Lemma F_6203c : fetch_word Asan.M.loaded_segments (0x6203c : word) = Some W_6203c.
Proof. vm_refl. Qed.
Lemma D_6203c : decode_any W_6203c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_62040 : bv 32 := 0x00008067.
Lemma F_62040 : fetch_word Asan.M.loaded_segments (0x62040 : word) = Some W_62040.
Proof. vm_refl. Qed.
Lemma D_62040 : decode_any W_62040 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_62044 : bv 32 := 0x00050713.
Lemma F_62044 : fetch_word Asan.M.loaded_segments (0x62044 : word) = Some W_62044.
Proof. vm_refl. Qed.
Lemma D_62044 : decode_any W_62044 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_62048 : bv 32 := 0xfffba517.
Lemma F_62048 : fetch_word Asan.M.loaded_segments (0x62048 : word) = Some W_62048.
Proof. vm_refl. Qed.
Lemma D_62048 : decode_any W_62048 = Some (Auipc 10 1048506, 4%Z).
Proof. vm_refl. Qed.
