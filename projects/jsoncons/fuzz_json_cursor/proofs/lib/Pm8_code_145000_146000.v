(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_145000 : bv 32 := 0xff060613.
Lemma F_145000 : fetch_word Asan.M.loaded_segments (0x145044 : word) = Some W_145000.
Proof. vm_refl. Qed.
Lemma D_145000 : decode_any W_145000 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_145004 : bv 32 := 0x00f6a023.
Lemma F_145004 : fetch_word Asan.M.loaded_segments (0x145048 : word) = Some W_145004.
Proof. vm_refl. Qed.
Lemma D_145004 : decode_any W_145004 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145008 : bv 32 := 0x0106a223.
Lemma F_145008 : fetch_word Asan.M.loaded_segments (0x14504c : word) = Some W_145008.
Proof. vm_refl. Qed.
Lemma D_145008 : decode_any W_145008 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14500c : bv 32 := 0x0116a423.
Lemma F_14500c : fetch_word Asan.M.loaded_segments (0x145050 : word) = Some W_14500c.
Proof. vm_refl. Qed.
Lemma D_14500c : decode_any W_14500c = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145010 : bv 32 := 0x0056a623.
Lemma F_145010 : fetch_word Asan.M.loaded_segments (0x145054 : word) = Some W_145010.
Proof. vm_refl. Qed.
Lemma D_145010 : decode_any W_145010 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_145014 : bv 32 := 0x01068693.
Lemma F_145014 : fetch_word Asan.M.loaded_segments (0x145058 : word) = Some W_145014.
Proof. vm_refl. Qed.
Lemma D_145014 : decode_any W_145014 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_145018 : bv 32 := 0xfcc76ae3.
Lemma F_145018 : fetch_word Asan.M.loaded_segments (0x14505c : word) = Some W_145018.
Proof. vm_refl. Qed.
Lemma D_145018 : decode_any W_145018 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_14501c : bv 32 := 0x00800713.
Lemma F_14501c : fetch_word Asan.M.loaded_segments (0x145060 : word) = Some W_14501c.
Proof. vm_refl. Qed.
Lemma D_14501c : decode_any W_14501c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145020 : bv 32 := 0x00e66e63.
Lemma F_145020 : fetch_word Asan.M.loaded_segments (0x145064 : word) = Some W_145020.
Proof. vm_refl. Qed.
Lemma D_145020 : decode_any W_145020 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_145024 : bv 32 := 0x0005a703.
Lemma F_145024 : fetch_word Asan.M.loaded_segments (0x145068 : word) = Some W_145024.
Proof. vm_refl. Qed.
Lemma D_145024 : decode_any W_145024 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145028 : bv 32 := 0x0045a783.
Lemma F_145028 : fetch_word Asan.M.loaded_segments (0x14506c : word) = Some W_145028.
Proof. vm_refl. Qed.
Lemma D_145028 : decode_any W_145028 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14502c : bv 32 := 0x00e6a023.
Lemma F_14502c : fetch_word Asan.M.loaded_segments (0x145070 : word) = Some W_14502c.
Proof. vm_refl. Qed.
Lemma D_14502c : decode_any W_14502c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145030 : bv 32 := 0x00f6a223.
Lemma F_145030 : fetch_word Asan.M.loaded_segments (0x145074 : word) = Some W_145030.
Proof. vm_refl. Qed.
Lemma D_145030 : decode_any W_145030 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_145034 : bv 32 := 0x00868693.
Lemma F_145034 : fetch_word Asan.M.loaded_segments (0x145078 : word) = Some W_145034.
Proof. vm_refl. Qed.
Lemma D_145034 : decode_any W_145034 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145038 : bv 32 := 0x00858593.
Lemma F_145038 : fetch_word Asan.M.loaded_segments (0x14507c : word) = Some W_145038.
Proof. vm_refl. Qed.
Lemma D_145038 : decode_any W_145038 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14503c : bv 32 := 0x00467713.
Lemma F_14503c : fetch_word Asan.M.loaded_segments (0x145080 : word) = Some W_14503c.
Proof. vm_refl. Qed.
Lemma D_14503c : decode_any W_14503c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_145040 : bv 32 := 0x24070063.
Lemma F_145040 : fetch_word Asan.M.loaded_segments (0x145084 : word) = Some W_145040.
Proof. vm_refl. Qed.
Lemma D_145040 : decode_any W_145040 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_145044 : bv 32 := 0x0005a703.
Lemma F_145044 : fetch_word Asan.M.loaded_segments (0x145088 : word) = Some W_145044.
Proof. vm_refl. Qed.
Lemma D_145044 : decode_any W_145044 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145048 : bv 32 := 0x00458593.
Lemma F_145048 : fetch_word Asan.M.loaded_segments (0x14508c : word) = Some W_145048.
Proof. vm_refl. Qed.
Lemma D_145048 : decode_any W_145048 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14504c : bv 32 := 0x00e6a023.
Lemma F_14504c : fetch_word Asan.M.loaded_segments (0x145090 : word) = Some W_14504c.
Proof. vm_refl. Qed.
Lemma D_14504c : decode_any W_14504c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145050 : bv 32 := 0x00468693.
Lemma F_145050 : fetch_word Asan.M.loaded_segments (0x145094 : word) = Some W_145050.
Proof. vm_refl. Qed.
Lemma D_145050 : decode_any W_145050 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_145054 : bv 32 := 0x22c0006f.
Lemma F_145054 : fetch_word Asan.M.loaded_segments (0x145098 : word) = Some W_145054.
Proof. vm_refl. Qed.
Lemma D_145054 : decode_any W_145054 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_145058 : bv 32 := 0x00e68023.
Lemma F_145058 : fetch_word Asan.M.loaded_segments (0x14509c : word) = Some W_145058.
Proof. vm_refl. Qed.
Lemma D_145058 : decode_any W_145058 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14505c : bv 32 := 0x00168693.
Lemma F_14505c : fetch_word Asan.M.loaded_segments (0x1450a0 : word) = Some W_14505c.
Proof. vm_refl. Qed.
Lemma D_14505c : decode_any W_14505c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_145060 : bv 32 := 0xfff60613.
Lemma F_145060 : fetch_word Asan.M.loaded_segments (0x1450a4 : word) = Some W_145060.
Proof. vm_refl. Qed.
Lemma D_145060 : decode_any W_145060 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_145064 : bv 32 := 0x01058593.
Lemma F_145064 : fetch_word Asan.M.loaded_segments (0x1450a8 : word) = Some W_145064.
Proof. vm_refl. Qed.
Lemma D_145064 : decode_any W_145064 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_145068 : bv 32 := 0x01200793.
Lemma F_145068 : fetch_word Asan.M.loaded_segments (0x1450ac : word) = Some W_145068.
Proof. vm_refl. Qed.
Lemma D_145068 : decode_any W_145068 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_14506c : bv 32 := 0x0087581b.
Lemma F_14506c : fetch_word Asan.M.loaded_segments (0x1450b0 : word) = Some W_14506c.
Proof. vm_refl. Qed.
Lemma D_14506c : decode_any W_14506c = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145070 : bv 32 := 0xff45a883.
Lemma F_145070 : fetch_word Asan.M.loaded_segments (0x1450b4 : word) = Some W_145070.
Proof. vm_refl. Qed.
Lemma D_145070 : decode_any W_145070 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_145074 : bv 32 := 0xff85a283.
Lemma F_145074 : fetch_word Asan.M.loaded_segments (0x1450b8 : word) = Some W_145074.
Proof. vm_refl. Qed.
Lemma D_145074 : decode_any W_145074 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_145078 : bv 32 := 0xffc5a303.
Lemma F_145078 : fetch_word Asan.M.loaded_segments (0x1450bc : word) = Some W_145078.
Proof. vm_refl. Qed.
Lemma D_145078 : decode_any W_145078 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_14507c : bv 32 := 0x0005a703.
Lemma F_14507c : fetch_word Asan.M.loaded_segments (0x1450c0 : word) = Some W_14507c.
Proof. vm_refl. Qed.
Lemma D_14507c : decode_any W_14507c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145080 : bv 32 := 0x01889393.
Lemma F_145080 : fetch_word Asan.M.loaded_segments (0x1450c4 : word) = Some W_145080.
Proof. vm_refl. Qed.
Lemma D_145080 : decode_any W_145080 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_145084 : bv 32 := 0x0088d89b.
Lemma F_145084 : fetch_word Asan.M.loaded_segments (0x1450c8 : word) = Some W_145084.
Proof. vm_refl. Qed.
Lemma D_145084 : decode_any W_145084 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145088 : bv 32 := 0x0103e833.
Lemma F_145088 : fetch_word Asan.M.loaded_segments (0x1450cc : word) = Some W_145088.
Proof. vm_refl. Qed.
Lemma D_145088 : decode_any W_145088 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14508c : bv 32 := 0x01829393.
Lemma F_14508c : fetch_word Asan.M.loaded_segments (0x1450d0 : word) = Some W_14508c.
Proof. vm_refl. Qed.
Lemma D_14508c : decode_any W_14508c = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_145090 : bv 32 := 0x0082d29b.
Lemma F_145090 : fetch_word Asan.M.loaded_segments (0x1450d4 : word) = Some W_145090.
Proof. vm_refl. Qed.
Lemma D_145090 : decode_any W_145090 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145094 : bv 32 := 0x0113e8b3.
Lemma F_145094 : fetch_word Asan.M.loaded_segments (0x1450d8 : word) = Some W_145094.
Proof. vm_refl. Qed.
Lemma D_145094 : decode_any W_145094 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_145098 : bv 32 := 0x01831393.
Lemma F_145098 : fetch_word Asan.M.loaded_segments (0x1450dc : word) = Some W_145098.
Proof. vm_refl. Qed.
Lemma D_145098 : decode_any W_145098 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_14509c : bv 32 := 0x0083531b.
Lemma F_14509c : fetch_word Asan.M.loaded_segments (0x1450e0 : word) = Some W_14509c.
Proof. vm_refl. Qed.
Lemma D_14509c : decode_any W_14509c = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450a0 : bv 32 := 0x0053e2b3.
Lemma F_1450a0 : fetch_word Asan.M.loaded_segments (0x1450e4 : word) = Some W_1450a0.
Proof. vm_refl. Qed.
Lemma D_1450a0 : decode_any W_1450a0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450a4 : bv 32 := 0x01871393.
Lemma F_1450a4 : fetch_word Asan.M.loaded_segments (0x1450e8 : word) = Some W_1450a4.
Proof. vm_refl. Qed.
Lemma D_1450a4 : decode_any W_1450a4 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450a8 : bv 32 := 0x0063e333.
Lemma F_1450a8 : fetch_word Asan.M.loaded_segments (0x1450ec : word) = Some W_1450a8.
Proof. vm_refl. Qed.
Lemma D_1450a8 : decode_any W_1450a8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450ac : bv 32 := 0xff060613.
Lemma F_1450ac : fetch_word Asan.M.loaded_segments (0x1450f0 : word) = Some W_1450ac.
Proof. vm_refl. Qed.
Lemma D_1450ac : decode_any W_1450ac = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450b0 : bv 32 := 0x0106a023.
Lemma F_1450b0 : fetch_word Asan.M.loaded_segments (0x1450f4 : word) = Some W_1450b0.
Proof. vm_refl. Qed.
Lemma D_1450b0 : decode_any W_1450b0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450b4 : bv 32 := 0x0116a223.
Lemma F_1450b4 : fetch_word Asan.M.loaded_segments (0x1450f8 : word) = Some W_1450b4.
Proof. vm_refl. Qed.
Lemma D_1450b4 : decode_any W_1450b4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450b8 : bv 32 := 0x0056a423.
Lemma F_1450b8 : fetch_word Asan.M.loaded_segments (0x1450fc : word) = Some W_1450b8.
Proof. vm_refl. Qed.
Lemma D_1450b8 : decode_any W_1450b8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450bc : bv 32 := 0x0066a623.
Lemma F_1450bc : fetch_word Asan.M.loaded_segments (0x145100 : word) = Some W_1450bc.
Proof. vm_refl. Qed.
Lemma D_1450bc : decode_any W_1450bc = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450c0 : bv 32 := 0x01068693.
Lemma F_1450c0 : fetch_word Asan.M.loaded_segments (0x145104 : word) = Some W_1450c0.
Proof. vm_refl. Qed.
Lemma D_1450c0 : decode_any W_1450c0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450c4 : bv 32 := 0x01058593.
Lemma F_1450c4 : fetch_word Asan.M.loaded_segments (0x145108 : word) = Some W_1450c4.
Proof. vm_refl. Qed.
Lemma D_1450c4 : decode_any W_1450c4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450c8 : bv 32 := 0xfac7e2e3.
Lemma F_1450c8 : fetch_word Asan.M.loaded_segments (0x14510c : word) = Some W_1450c8.
Proof. vm_refl. Qed.
Lemma D_1450c8 : decode_any W_1450c8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450cc : bv 32 := 0xff158593.
Lemma F_1450cc : fetch_word Asan.M.loaded_segments (0x145110 : word) = Some W_1450cc.
Proof. vm_refl. Qed.
Lemma D_1450cc : decode_any W_1450cc = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450d0 : bv 32 := 0x01000713.
Lemma F_1450d0 : fetch_word Asan.M.loaded_segments (0x145114 : word) = Some W_1450d0.
Proof. vm_refl. Qed.
Lemma D_1450d0 : decode_any W_1450d0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450d4 : bv 32 := 0xe4e666e3.
Lemma F_1450d4 : fetch_word Asan.M.loaded_segments (0x145118 : word) = Some W_1450d4.
Proof. vm_refl. Qed.
Lemma D_1450d4 : decode_any W_1450d4 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450d8 : bv 32 := 0x0940006f.
Lemma F_1450d8 : fetch_word Asan.M.loaded_segments (0x14511c : word) = Some W_1450d8.
Proof. vm_refl. Qed.
Lemma D_1450d8 : decode_any W_1450d8 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450dc : bv 32 := 0x00875793.
Lemma F_1450dc : fetch_word Asan.M.loaded_segments (0x145120 : word) = Some W_1450dc.
Proof. vm_refl. Qed.
Lemma D_1450dc : decode_any W_1450dc = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450e0 : bv 32 := 0x01075813.
Lemma F_1450e0 : fetch_word Asan.M.loaded_segments (0x145124 : word) = Some W_1450e0.
Proof. vm_refl. Qed.
Lemma D_1450e0 : decode_any W_1450e0 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450e4 : bv 32 := 0xffd60613.
Lemma F_1450e4 : fetch_word Asan.M.loaded_segments (0x145128 : word) = Some W_1450e4.
Proof. vm_refl. Qed.
Lemma D_1450e4 : decode_any W_1450e4 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450e8 : bv 32 := 0x00e68023.
Lemma F_1450e8 : fetch_word Asan.M.loaded_segments (0x14512c : word) = Some W_1450e8.
Proof. vm_refl. Qed.
Lemma D_1450e8 : decode_any W_1450e8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450ec : bv 32 := 0x00f680a3.
Lemma F_1450ec : fetch_word Asan.M.loaded_segments (0x145130 : word) = Some W_1450ec.
Proof. vm_refl. Qed.
Lemma D_1450ec : decode_any W_1450ec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450f0 : bv 32 := 0x01068123.
Lemma F_1450f0 : fetch_word Asan.M.loaded_segments (0x145134 : word) = Some W_1450f0.
Proof. vm_refl. Qed.
Lemma D_1450f0 : decode_any W_1450f0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450f4 : bv 32 := 0x00368693.
Lemma F_1450f4 : fetch_word Asan.M.loaded_segments (0x145138 : word) = Some W_1450f4.
Proof. vm_refl. Qed.
Lemma D_1450f4 : decode_any W_1450f4 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450f8 : bv 32 := 0x01058593.
Lemma F_1450f8 : fetch_word Asan.M.loaded_segments (0x14513c : word) = Some W_1450f8.
Proof. vm_refl. Qed.
Lemma D_1450f8 : decode_any W_1450f8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1450fc : bv 32 := 0x01000793.
Lemma F_1450fc : fetch_word Asan.M.loaded_segments (0x145140 : word) = Some W_1450fc.
Proof. vm_refl. Qed.
Lemma D_1450fc : decode_any W_1450fc = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_145100 : bv 32 := 0x0187581b.
Lemma F_145100 : fetch_word Asan.M.loaded_segments (0x145144 : word) = Some W_145100.
Proof. vm_refl. Qed.
Lemma D_145100 : decode_any W_145100 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_145104 : bv 32 := 0xff45a883.
Lemma F_145104 : fetch_word Asan.M.loaded_segments (0x145148 : word) = Some W_145104.
Proof. vm_refl. Qed.
Lemma D_145104 : decode_any W_145104 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_145108 : bv 32 := 0xff85a283.
Lemma F_145108 : fetch_word Asan.M.loaded_segments (0x14514c : word) = Some W_145108.
Proof. vm_refl. Qed.
Lemma D_145108 : decode_any W_145108 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_14510c : bv 32 := 0xffc5a303.
Lemma F_14510c : fetch_word Asan.M.loaded_segments (0x145150 : word) = Some W_14510c.
Proof. vm_refl. Qed.
Lemma D_14510c : decode_any W_14510c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_145110 : bv 32 := 0x0005a703.
Lemma F_145110 : fetch_word Asan.M.loaded_segments (0x145154 : word) = Some W_145110.
Proof. vm_refl. Qed.
Lemma D_145110 : decode_any W_145110 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145114 : bv 32 := 0x00889393.
Lemma F_145114 : fetch_word Asan.M.loaded_segments (0x145158 : word) = Some W_145114.
Proof. vm_refl. Qed.
Lemma D_145114 : decode_any W_145114 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145118 : bv 32 := 0x0188d89b.
Lemma F_145118 : fetch_word Asan.M.loaded_segments (0x14515c : word) = Some W_145118.
Proof. vm_refl. Qed.
Lemma D_145118 : decode_any W_145118 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_14511c : bv 32 := 0x0103e833.
Lemma F_14511c : fetch_word Asan.M.loaded_segments (0x145160 : word) = Some W_14511c.
Proof. vm_refl. Qed.
Lemma D_14511c : decode_any W_14511c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_145120 : bv 32 := 0x00829393.
Lemma F_145120 : fetch_word Asan.M.loaded_segments (0x145164 : word) = Some W_145120.
Proof. vm_refl. Qed.
Lemma D_145120 : decode_any W_145120 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145124 : bv 32 := 0x0182d29b.
Lemma F_145124 : fetch_word Asan.M.loaded_segments (0x145168 : word) = Some W_145124.
Proof. vm_refl. Qed.
Lemma D_145124 : decode_any W_145124 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_145128 : bv 32 := 0x0113e8b3.
Lemma F_145128 : fetch_word Asan.M.loaded_segments (0x14516c : word) = Some W_145128.
Proof. vm_refl. Qed.
Lemma D_145128 : decode_any W_145128 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_14512c : bv 32 := 0x00831393.
Lemma F_14512c : fetch_word Asan.M.loaded_segments (0x145170 : word) = Some W_14512c.
Proof. vm_refl. Qed.
Lemma D_14512c : decode_any W_14512c = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145130 : bv 32 := 0x0183531b.
Lemma F_145130 : fetch_word Asan.M.loaded_segments (0x145174 : word) = Some W_145130.
Proof. vm_refl. Qed.
Lemma D_145130 : decode_any W_145130 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_145134 : bv 32 := 0x0053e2b3.
Lemma F_145134 : fetch_word Asan.M.loaded_segments (0x145178 : word) = Some W_145134.
Proof. vm_refl. Qed.
Lemma D_145134 : decode_any W_145134 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_145138 : bv 32 := 0x00871393.
Lemma F_145138 : fetch_word Asan.M.loaded_segments (0x14517c : word) = Some W_145138.
Proof. vm_refl. Qed.
Lemma D_145138 : decode_any W_145138 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14513c : bv 32 := 0x0063e333.
Lemma F_14513c : fetch_word Asan.M.loaded_segments (0x145180 : word) = Some W_14513c.
Proof. vm_refl. Qed.
Lemma D_14513c : decode_any W_14513c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_145140 : bv 32 := 0xff060613.
Lemma F_145140 : fetch_word Asan.M.loaded_segments (0x145184 : word) = Some W_145140.
Proof. vm_refl. Qed.
Lemma D_145140 : decode_any W_145140 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_145144 : bv 32 := 0x0106a023.
Lemma F_145144 : fetch_word Asan.M.loaded_segments (0x145188 : word) = Some W_145144.
Proof. vm_refl. Qed.
Lemma D_145144 : decode_any W_145144 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145148 : bv 32 := 0x0116a223.
Lemma F_145148 : fetch_word Asan.M.loaded_segments (0x14518c : word) = Some W_145148.
Proof. vm_refl. Qed.
Lemma D_145148 : decode_any W_145148 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14514c : bv 32 := 0x0056a423.
Lemma F_14514c : fetch_word Asan.M.loaded_segments (0x145190 : word) = Some W_14514c.
Proof. vm_refl. Qed.
Lemma D_14514c : decode_any W_14514c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145150 : bv 32 := 0x0066a623.
Lemma F_145150 : fetch_word Asan.M.loaded_segments (0x145194 : word) = Some W_145150.
Proof. vm_refl. Qed.
Lemma D_145150 : decode_any W_145150 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_145154 : bv 32 := 0x01068693.
Lemma F_145154 : fetch_word Asan.M.loaded_segments (0x145198 : word) = Some W_145154.
Proof. vm_refl. Qed.
Lemma D_145154 : decode_any W_145154 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_145158 : bv 32 := 0x01058593.
Lemma F_145158 : fetch_word Asan.M.loaded_segments (0x14519c : word) = Some W_145158.
Proof. vm_refl. Qed.
Lemma D_145158 : decode_any W_145158 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14515c : bv 32 := 0xfac7e2e3.
Lemma F_14515c : fetch_word Asan.M.loaded_segments (0x1451a0 : word) = Some W_14515c.
Proof. vm_refl. Qed.
Lemma D_14515c : decode_any W_14515c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_145160 : bv 32 := 0xff358593.
Lemma F_145160 : fetch_word Asan.M.loaded_segments (0x1451a4 : word) = Some W_145160.
Proof. vm_refl. Qed.
Lemma D_145160 : decode_any W_145160 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_145164 : bv 32 := 0x01000713.
Lemma F_145164 : fetch_word Asan.M.loaded_segments (0x1451a8 : word) = Some W_145164.
Proof. vm_refl. Qed.
Lemma D_145164 : decode_any W_145164 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_145168 : bv 32 := 0xdae66ce3.
Lemma F_145168 : fetch_word Asan.M.loaded_segments (0x1451ac : word) = Some W_145168.
Proof. vm_refl. Qed.
Lemma D_145168 : decode_any W_145168 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_14516c : bv 32 := 0x0005c703.
Lemma F_14516c : fetch_word Asan.M.loaded_segments (0x1451b0 : word) = Some W_14516c.
Proof. vm_refl. Qed.
Lemma D_14516c : decode_any W_14516c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145170 : bv 32 := 0x0015c783.
Lemma F_145170 : fetch_word Asan.M.loaded_segments (0x1451b4 : word) = Some W_145170.
Proof. vm_refl. Qed.
Lemma D_145170 : decode_any W_145170 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_145174 : bv 32 := 0x0025c803.
Lemma F_145174 : fetch_word Asan.M.loaded_segments (0x1451b8 : word) = Some W_145174.
Proof. vm_refl. Qed.
Lemma D_145174 : decode_any W_145174 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_145178 : bv 32 := 0x0035c883.
Lemma F_145178 : fetch_word Asan.M.loaded_segments (0x1451bc : word) = Some W_145178.
Proof. vm_refl. Qed.
Lemma D_145178 : decode_any W_145178 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_14517c : bv 32 := 0x0045c283.
Lemma F_14517c : fetch_word Asan.M.loaded_segments (0x1451c0 : word) = Some W_14517c.
Proof. vm_refl. Qed.
Lemma D_14517c : decode_any W_14517c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_145180 : bv 32 := 0x0055c303.
Lemma F_145180 : fetch_word Asan.M.loaded_segments (0x1451c4 : word) = Some W_145180.
Proof. vm_refl. Qed.
Lemma D_145180 : decode_any W_145180 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_145184 : bv 32 := 0x0065c383.
Lemma F_145184 : fetch_word Asan.M.loaded_segments (0x1451c8 : word) = Some W_145184.
Proof. vm_refl. Qed.
Lemma D_145184 : decode_any W_145184 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_145188 : bv 32 := 0x0075ce03.
Lemma F_145188 : fetch_word Asan.M.loaded_segments (0x1451cc : word) = Some W_145188.
Proof. vm_refl. Qed.
Lemma D_145188 : decode_any W_145188 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_14518c : bv 32 := 0x00e68023.
Lemma F_14518c : fetch_word Asan.M.loaded_segments (0x1451d0 : word) = Some W_14518c.
Proof. vm_refl. Qed.
Lemma D_14518c : decode_any W_14518c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145190 : bv 32 := 0x00f680a3.
Lemma F_145190 : fetch_word Asan.M.loaded_segments (0x1451d4 : word) = Some W_145190.
Proof. vm_refl. Qed.
Lemma D_145190 : decode_any W_145190 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_145194 : bv 32 := 0x01068123.
Lemma F_145194 : fetch_word Asan.M.loaded_segments (0x1451d8 : word) = Some W_145194.
Proof. vm_refl. Qed.
Lemma D_145194 : decode_any W_145194 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_145198 : bv 32 := 0x011681a3.
Lemma F_145198 : fetch_word Asan.M.loaded_segments (0x1451dc : word) = Some W_145198.
Proof. vm_refl. Qed.
Lemma D_145198 : decode_any W_145198 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_14519c : bv 32 := 0x0085c703.
Lemma F_14519c : fetch_word Asan.M.loaded_segments (0x1451e0 : word) = Some W_14519c.
Proof. vm_refl. Qed.
Lemma D_14519c : decode_any W_14519c = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451a0 : bv 32 := 0x0095c783.
Lemma F_1451a0 : fetch_word Asan.M.loaded_segments (0x1451e4 : word) = Some W_1451a0.
Proof. vm_refl. Qed.
Lemma D_1451a0 : decode_any W_1451a0 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451a4 : bv 32 := 0x00a5c803.
Lemma F_1451a4 : fetch_word Asan.M.loaded_segments (0x1451e8 : word) = Some W_1451a4.
Proof. vm_refl. Qed.
Lemma D_1451a4 : decode_any W_1451a4 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451a8 : bv 32 := 0x00b5c883.
Lemma F_1451a8 : fetch_word Asan.M.loaded_segments (0x1451ec : word) = Some W_1451a8.
Proof. vm_refl. Qed.
Lemma D_1451a8 : decode_any W_1451a8 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451ac : bv 32 := 0x00568223.
Lemma F_1451ac : fetch_word Asan.M.loaded_segments (0x1451f0 : word) = Some W_1451ac.
Proof. vm_refl. Qed.
Lemma D_1451ac : decode_any W_1451ac = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451b0 : bv 32 := 0x006682a3.
Lemma F_1451b0 : fetch_word Asan.M.loaded_segments (0x1451f4 : word) = Some W_1451b0.
Proof. vm_refl. Qed.
Lemma D_1451b0 : decode_any W_1451b0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451b4 : bv 32 := 0x00768323.
Lemma F_1451b4 : fetch_word Asan.M.loaded_segments (0x1451f8 : word) = Some W_1451b4.
Proof. vm_refl. Qed.
Lemma D_1451b4 : decode_any W_1451b4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451b8 : bv 32 := 0x01c683a3.
Lemma F_1451b8 : fetch_word Asan.M.loaded_segments (0x1451fc : word) = Some W_1451b8.
Proof. vm_refl. Qed.
Lemma D_1451b8 : decode_any W_1451b8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451bc : bv 32 := 0x00c5c283.
Lemma F_1451bc : fetch_word Asan.M.loaded_segments (0x145200 : word) = Some W_1451bc.
Proof. vm_refl. Qed.
Lemma D_1451bc : decode_any W_1451bc = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451c0 : bv 32 := 0x00d5c303.
Lemma F_1451c0 : fetch_word Asan.M.loaded_segments (0x145204 : word) = Some W_1451c0.
Proof. vm_refl. Qed.
Lemma D_1451c0 : decode_any W_1451c0 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451c4 : bv 32 := 0x00e5c383.
Lemma F_1451c4 : fetch_word Asan.M.loaded_segments (0x145208 : word) = Some W_1451c4.
Proof. vm_refl. Qed.
Lemma D_1451c4 : decode_any W_1451c4 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451c8 : bv 32 := 0x00f5ce03.
Lemma F_1451c8 : fetch_word Asan.M.loaded_segments (0x14520c : word) = Some W_1451c8.
Proof. vm_refl. Qed.
Lemma D_1451c8 : decode_any W_1451c8 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451cc : bv 32 := 0x01058593.
Lemma F_1451cc : fetch_word Asan.M.loaded_segments (0x145210 : word) = Some W_1451cc.
Proof. vm_refl. Qed.
Lemma D_1451cc : decode_any W_1451cc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451d0 : bv 32 := 0x00e68423.
Lemma F_1451d0 : fetch_word Asan.M.loaded_segments (0x145214 : word) = Some W_1451d0.
Proof. vm_refl. Qed.
Lemma D_1451d0 : decode_any W_1451d0 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451d4 : bv 32 := 0x00f684a3.
Lemma F_1451d4 : fetch_word Asan.M.loaded_segments (0x145218 : word) = Some W_1451d4.
Proof. vm_refl. Qed.
Lemma D_1451d4 : decode_any W_1451d4 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451d8 : bv 32 := 0x01068523.
Lemma F_1451d8 : fetch_word Asan.M.loaded_segments (0x14521c : word) = Some W_1451d8.
Proof. vm_refl. Qed.
Lemma D_1451d8 : decode_any W_1451d8 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451dc : bv 32 := 0x011685a3.
Lemma F_1451dc : fetch_word Asan.M.loaded_segments (0x145220 : word) = Some W_1451dc.
Proof. vm_refl. Qed.
Lemma D_1451dc : decode_any W_1451dc = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451e0 : bv 32 := 0x01068713.
Lemma F_1451e0 : fetch_word Asan.M.loaded_segments (0x145224 : word) = Some W_1451e0.
Proof. vm_refl. Qed.
Lemma D_1451e0 : decode_any W_1451e0 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451e4 : bv 32 := 0x00568623.
Lemma F_1451e4 : fetch_word Asan.M.loaded_segments (0x145228 : word) = Some W_1451e4.
Proof. vm_refl. Qed.
Lemma D_1451e4 : decode_any W_1451e4 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451e8 : bv 32 := 0x006686a3.
Lemma F_1451e8 : fetch_word Asan.M.loaded_segments (0x14522c : word) = Some W_1451e8.
Proof. vm_refl. Qed.
Lemma D_1451e8 : decode_any W_1451e8 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451ec : bv 32 := 0x00768723.
Lemma F_1451ec : fetch_word Asan.M.loaded_segments (0x145230 : word) = Some W_1451ec.
Proof. vm_refl. Qed.
Lemma D_1451ec : decode_any W_1451ec = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451f0 : bv 32 := 0x01c687a3.
Lemma F_1451f0 : fetch_word Asan.M.loaded_segments (0x145234 : word) = Some W_1451f0.
Proof. vm_refl. Qed.
Lemma D_1451f0 : decode_any W_1451f0 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451f4 : bv 32 := 0x00070693.
Lemma F_1451f4 : fetch_word Asan.M.loaded_segments (0x145238 : word) = Some W_1451f4.
Proof. vm_refl. Qed.
Lemma D_1451f4 : decode_any W_1451f4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451f8 : bv 32 := 0x00867713.
Lemma F_1451f8 : fetch_word Asan.M.loaded_segments (0x14523c : word) = Some W_1451f8.
Proof. vm_refl. Qed.
Lemma D_1451f8 : decode_any W_1451f8 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1451fc : bv 32 := 0xd20706e3.
Lemma F_1451fc : fetch_word Asan.M.loaded_segments (0x145240 : word) = Some W_1451fc.
Proof. vm_refl. Qed.
Lemma D_1451fc : decode_any W_1451fc = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_145200 : bv 32 := 0x0005c703.
Lemma F_145200 : fetch_word Asan.M.loaded_segments (0x145244 : word) = Some W_145200.
Proof. vm_refl. Qed.
Lemma D_145200 : decode_any W_145200 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145204 : bv 32 := 0x0015c783.
Lemma F_145204 : fetch_word Asan.M.loaded_segments (0x145248 : word) = Some W_145204.
Proof. vm_refl. Qed.
Lemma D_145204 : decode_any W_145204 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_145208 : bv 32 := 0x0025c803.
Lemma F_145208 : fetch_word Asan.M.loaded_segments (0x14524c : word) = Some W_145208.
Proof. vm_refl. Qed.
Lemma D_145208 : decode_any W_145208 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_14520c : bv 32 := 0x0035c883.
Lemma F_14520c : fetch_word Asan.M.loaded_segments (0x145250 : word) = Some W_14520c.
Proof. vm_refl. Qed.
Lemma D_14520c : decode_any W_14520c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_145210 : bv 32 := 0x0045c283.
Lemma F_145210 : fetch_word Asan.M.loaded_segments (0x145254 : word) = Some W_145210.
Proof. vm_refl. Qed.
Lemma D_145210 : decode_any W_145210 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_145214 : bv 32 := 0x0055c303.
Lemma F_145214 : fetch_word Asan.M.loaded_segments (0x145258 : word) = Some W_145214.
Proof. vm_refl. Qed.
Lemma D_145214 : decode_any W_145214 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_145218 : bv 32 := 0x0065c383.
Lemma F_145218 : fetch_word Asan.M.loaded_segments (0x14525c : word) = Some W_145218.
Proof. vm_refl. Qed.
Lemma D_145218 : decode_any W_145218 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_14521c : bv 32 := 0x0075ce03.
Lemma F_14521c : fetch_word Asan.M.loaded_segments (0x145260 : word) = Some W_14521c.
Proof. vm_refl. Qed.
Lemma D_14521c : decode_any W_14521c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_145220 : bv 32 := 0x00858593.
Lemma F_145220 : fetch_word Asan.M.loaded_segments (0x145264 : word) = Some W_145220.
Proof. vm_refl. Qed.
Lemma D_145220 : decode_any W_145220 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145224 : bv 32 := 0x00e68023.
Lemma F_145224 : fetch_word Asan.M.loaded_segments (0x145268 : word) = Some W_145224.
Proof. vm_refl. Qed.
Lemma D_145224 : decode_any W_145224 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145228 : bv 32 := 0x00f680a3.
Lemma F_145228 : fetch_word Asan.M.loaded_segments (0x14526c : word) = Some W_145228.
Proof. vm_refl. Qed.
Lemma D_145228 : decode_any W_145228 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14522c : bv 32 := 0x01068123.
Lemma F_14522c : fetch_word Asan.M.loaded_segments (0x145270 : word) = Some W_14522c.
Proof. vm_refl. Qed.
Lemma D_14522c : decode_any W_14522c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_145230 : bv 32 := 0x011681a3.
Lemma F_145230 : fetch_word Asan.M.loaded_segments (0x145274 : word) = Some W_145230.
Proof. vm_refl. Qed.
Lemma D_145230 : decode_any W_145230 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_145234 : bv 32 := 0x00868713.
Lemma F_145234 : fetch_word Asan.M.loaded_segments (0x145278 : word) = Some W_145234.
Proof. vm_refl. Qed.
Lemma D_145234 : decode_any W_145234 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145238 : bv 32 := 0x00568223.
Lemma F_145238 : fetch_word Asan.M.loaded_segments (0x14527c : word) = Some W_145238.
Proof. vm_refl. Qed.
Lemma D_145238 : decode_any W_145238 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14523c : bv 32 := 0x006682a3.
Lemma F_14523c : fetch_word Asan.M.loaded_segments (0x145280 : word) = Some W_14523c.
Proof. vm_refl. Qed.
Lemma D_14523c : decode_any W_14523c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_145240 : bv 32 := 0x00768323.
Lemma F_145240 : fetch_word Asan.M.loaded_segments (0x145284 : word) = Some W_145240.
Proof. vm_refl. Qed.
Lemma D_145240 : decode_any W_145240 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_145244 : bv 32 := 0x01c683a3.
Lemma F_145244 : fetch_word Asan.M.loaded_segments (0x145288 : word) = Some W_145244.
Proof. vm_refl. Qed.
Lemma D_145244 : decode_any W_145244 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_145248 : bv 32 := 0x00070693.
Lemma F_145248 : fetch_word Asan.M.loaded_segments (0x14528c : word) = Some W_145248.
Proof. vm_refl. Qed.
Lemma D_145248 : decode_any W_145248 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14524c : bv 32 := 0x00467713.
Lemma F_14524c : fetch_word Asan.M.loaded_segments (0x145290 : word) = Some W_14524c.
Proof. vm_refl. Qed.
Lemma D_14524c : decode_any W_14524c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_145250 : bv 32 := 0x02070863.
Lemma F_145250 : fetch_word Asan.M.loaded_segments (0x145294 : word) = Some W_145250.
Proof. vm_refl. Qed.
Lemma D_145250 : decode_any W_145250 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_145254 : bv 32 := 0x0005c703.
Lemma F_145254 : fetch_word Asan.M.loaded_segments (0x145298 : word) = Some W_145254.
Proof. vm_refl. Qed.
Lemma D_145254 : decode_any W_145254 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145258 : bv 32 := 0x0015c783.
Lemma F_145258 : fetch_word Asan.M.loaded_segments (0x14529c : word) = Some W_145258.
Proof. vm_refl. Qed.
Lemma D_145258 : decode_any W_145258 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14525c : bv 32 := 0x0025c803.
Lemma F_14525c : fetch_word Asan.M.loaded_segments (0x1452a0 : word) = Some W_14525c.
Proof. vm_refl. Qed.
Lemma D_14525c : decode_any W_14525c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_145260 : bv 32 := 0x0035c883.
Lemma F_145260 : fetch_word Asan.M.loaded_segments (0x1452a4 : word) = Some W_145260.
Proof. vm_refl. Qed.
Lemma D_145260 : decode_any W_145260 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_145264 : bv 32 := 0x00458593.
Lemma F_145264 : fetch_word Asan.M.loaded_segments (0x1452a8 : word) = Some W_145264.
Proof. vm_refl. Qed.
Lemma D_145264 : decode_any W_145264 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_145268 : bv 32 := 0x00468293.
Lemma F_145268 : fetch_word Asan.M.loaded_segments (0x1452ac : word) = Some W_145268.
Proof. vm_refl. Qed.
Lemma D_145268 : decode_any W_145268 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14526c : bv 32 := 0x00e68023.
Lemma F_14526c : fetch_word Asan.M.loaded_segments (0x1452b0 : word) = Some W_14526c.
Proof. vm_refl. Qed.
Lemma D_14526c : decode_any W_14526c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145270 : bv 32 := 0x00f680a3.
Lemma F_145270 : fetch_word Asan.M.loaded_segments (0x1452b4 : word) = Some W_145270.
Proof. vm_refl. Qed.
Lemma D_145270 : decode_any W_145270 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_145274 : bv 32 := 0x01068123.
Lemma F_145274 : fetch_word Asan.M.loaded_segments (0x1452b8 : word) = Some W_145274.
Proof. vm_refl. Qed.
Lemma D_145274 : decode_any W_145274 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_145278 : bv 32 := 0x011681a3.
Lemma F_145278 : fetch_word Asan.M.loaded_segments (0x1452bc : word) = Some W_145278.
Proof. vm_refl. Qed.
Lemma D_145278 : decode_any W_145278 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_14527c : bv 32 := 0x00028693.
Lemma F_14527c : fetch_word Asan.M.loaded_segments (0x1452c0 : word) = Some W_14527c.
Proof. vm_refl. Qed.
Lemma D_14527c : decode_any W_14527c = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145280 : bv 32 := 0x00267713.
Lemma F_145280 : fetch_word Asan.M.loaded_segments (0x1452c4 : word) = Some W_145280.
Proof. vm_refl. Qed.
Lemma D_145280 : decode_any W_145280 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_145284 : bv 32 := 0x00071863.
Lemma F_145284 : fetch_word Asan.M.loaded_segments (0x1452c8 : word) = Some W_145284.
Proof. vm_refl. Qed.
Lemma D_145284 : decode_any W_145284 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_145288 : bv 32 := 0x00167613.
Lemma F_145288 : fetch_word Asan.M.loaded_segments (0x1452cc : word) = Some W_145288.
Proof. vm_refl. Qed.
Lemma D_145288 : decode_any W_145288 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14528c : bv 32 := 0x02061663.
Lemma F_14528c : fetch_word Asan.M.loaded_segments (0x1452d0 : word) = Some W_14528c.
Proof. vm_refl. Qed.
Lemma D_14528c : decode_any W_14528c = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_145290 : bv 32 := 0x00008067.
Lemma F_145290 : fetch_word Asan.M.loaded_segments (0x1452d4 : word) = Some W_145290.
Proof. vm_refl. Qed.
Lemma D_145290 : decode_any W_145290 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145294 : bv 32 := 0x0005c703.
Lemma F_145294 : fetch_word Asan.M.loaded_segments (0x1452d8 : word) = Some W_145294.
Proof. vm_refl. Qed.
Lemma D_145294 : decode_any W_145294 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145298 : bv 32 := 0x0015c783.
Lemma F_145298 : fetch_word Asan.M.loaded_segments (0x1452dc : word) = Some W_145298.
Proof. vm_refl. Qed.
Lemma D_145298 : decode_any W_145298 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14529c : bv 32 := 0x00258593.
Lemma F_14529c : fetch_word Asan.M.loaded_segments (0x1452e0 : word) = Some W_14529c.
Proof. vm_refl. Qed.
Lemma D_14529c : decode_any W_14529c = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452a0 : bv 32 := 0x00268813.
Lemma F_1452a0 : fetch_word Asan.M.loaded_segments (0x1452e4 : word) = Some W_1452a0.
Proof. vm_refl. Qed.
Lemma D_1452a0 : decode_any W_1452a0 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452a4 : bv 32 := 0x00e68023.
Lemma F_1452a4 : fetch_word Asan.M.loaded_segments (0x1452e8 : word) = Some W_1452a4.
Proof. vm_refl. Qed.
Lemma D_1452a4 : decode_any W_1452a4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452a8 : bv 32 := 0x00f680a3.
Lemma F_1452a8 : fetch_word Asan.M.loaded_segments (0x1452ec : word) = Some W_1452a8.
Proof. vm_refl. Qed.
Lemma D_1452a8 : decode_any W_1452a8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452ac : bv 32 := 0x00080693.
Lemma F_1452ac : fetch_word Asan.M.loaded_segments (0x1452f0 : word) = Some W_1452ac.
Proof. vm_refl. Qed.
Lemma D_1452ac : decode_any W_1452ac = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452b0 : bv 32 := 0x00167613.
Lemma F_1452b0 : fetch_word Asan.M.loaded_segments (0x1452f4 : word) = Some W_1452b0.
Proof. vm_refl. Qed.
Lemma D_1452b0 : decode_any W_1452b0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452b4 : bv 32 := 0xfc060ee3.
Lemma F_1452b4 : fetch_word Asan.M.loaded_segments (0x1452f8 : word) = Some W_1452b4.
Proof. vm_refl. Qed.
Lemma D_1452b4 : decode_any W_1452b4 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452b8 : bv 32 := 0x0005c583.
Lemma F_1452b8 : fetch_word Asan.M.loaded_segments (0x1452fc : word) = Some W_1452b8.
Proof. vm_refl. Qed.
Lemma D_1452b8 : decode_any W_1452b8 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452bc : bv 32 := 0x00b68023.
Lemma F_1452bc : fetch_word Asan.M.loaded_segments (0x145300 : word) = Some W_1452bc.
Proof. vm_refl. Qed.
Lemma D_1452bc : decode_any W_1452bc = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452c0 : bv 32 := 0x00008067.
Lemma F_1452c0 : fetch_word Asan.M.loaded_segments (0x145304 : word) = Some W_1452c0.
Proof. vm_refl. Qed.
Lemma D_1452c0 : decode_any W_1452c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452c4 : bv 32 := 0x0e060a63.
Lemma F_1452c4 : fetch_word Asan.M.loaded_segments (0x145308 : word) = Some W_1452c4.
Proof. vm_refl. Qed.
Lemma D_1452c4 : decode_any W_1452c4 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452c8 : bv 32 := 0x00b50023.
Lemma F_1452c8 : fetch_word Asan.M.loaded_segments (0x14530c : word) = Some W_1452c8.
Proof. vm_refl. Qed.
Lemma D_1452c8 : decode_any W_1452c8 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452cc : bv 32 := 0x00c506b3.
Lemma F_1452cc : fetch_word Asan.M.loaded_segments (0x145310 : word) = Some W_1452cc.
Proof. vm_refl. Qed.
Lemma D_1452cc : decode_any W_1452cc = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452d0 : bv 32 := 0x00300713.
Lemma F_1452d0 : fetch_word Asan.M.loaded_segments (0x145314 : word) = Some W_1452d0.
Proof. vm_refl. Qed.
Lemma D_1452d0 : decode_any W_1452d0 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452d4 : bv 32 := 0xfeb68fa3.
Lemma F_1452d4 : fetch_word Asan.M.loaded_segments (0x145318 : word) = Some W_1452d4.
Proof. vm_refl. Qed.
Lemma D_1452d4 : decode_any W_1452d4 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452d8 : bv 32 := 0x0ee66063.
Lemma F_1452d8 : fetch_word Asan.M.loaded_segments (0x14531c : word) = Some W_1452d8.
Proof. vm_refl. Qed.
Lemma D_1452d8 : decode_any W_1452d8 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452dc : bv 32 := 0x00b500a3.
Lemma F_1452dc : fetch_word Asan.M.loaded_segments (0x145320 : word) = Some W_1452dc.
Proof. vm_refl. Qed.
Lemma D_1452dc : decode_any W_1452dc = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452e0 : bv 32 := 0x00b50123.
Lemma F_1452e0 : fetch_word Asan.M.loaded_segments (0x145324 : word) = Some W_1452e0.
Proof. vm_refl. Qed.
Lemma D_1452e0 : decode_any W_1452e0 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452e4 : bv 32 := 0x00700713.
Lemma F_1452e4 : fetch_word Asan.M.loaded_segments (0x145328 : word) = Some W_1452e4.
Proof. vm_refl. Qed.
Lemma D_1452e4 : decode_any W_1452e4 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452e8 : bv 32 := 0xfeb68ea3.
Lemma F_1452e8 : fetch_word Asan.M.loaded_segments (0x14532c : word) = Some W_1452e8.
Proof. vm_refl. Qed.
Lemma D_1452e8 : decode_any W_1452e8 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452ec : bv 32 := 0xfeb68f23.
Lemma F_1452ec : fetch_word Asan.M.loaded_segments (0x145330 : word) = Some W_1452ec.
Proof. vm_refl. Qed.
Lemma D_1452ec : decode_any W_1452ec = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452f0 : bv 32 := 0x0ce66463.
Lemma F_1452f0 : fetch_word Asan.M.loaded_segments (0x145334 : word) = Some W_1452f0.
Proof. vm_refl. Qed.
Lemma D_1452f0 : decode_any W_1452f0 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452f4 : bv 32 := 0x00b501a3.
Lemma F_1452f4 : fetch_word Asan.M.loaded_segments (0x145338 : word) = Some W_1452f4.
Proof. vm_refl. Qed.
Lemma D_1452f4 : decode_any W_1452f4 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452f8 : bv 32 := 0x00900793.
Lemma F_1452f8 : fetch_word Asan.M.loaded_segments (0x14533c : word) = Some W_1452f8.
Proof. vm_refl. Qed.
Lemma D_1452f8 : decode_any W_1452f8 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1452fc : bv 32 := 0xfeb68e23.
Lemma F_1452fc : fetch_word Asan.M.loaded_segments (0x145340 : word) = Some W_1452fc.
Proof. vm_refl. Qed.
Lemma D_1452fc : decode_any W_1452fc = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_145300 : bv 32 := 0x0af66c63.
Lemma F_145300 : fetch_word Asan.M.loaded_segments (0x145344 : word) = Some W_145300.
Proof. vm_refl. Qed.
Lemma D_145300 : decode_any W_145300 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_145304 : bv 32 := 0x40a006bb.
Lemma F_145304 : fetch_word Asan.M.loaded_segments (0x145348 : word) = Some W_145304.
Proof. vm_refl. Qed.
Lemma D_145304 : decode_any W_145304 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_145308 : bv 32 := 0x03859813.
Lemma F_145308 : fetch_word Asan.M.loaded_segments (0x14534c : word) = Some W_145308.
Proof. vm_refl. Qed.
Lemma D_145308 : decode_any W_145308 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_14530c : bv 32 := 0x101015b7.
Lemma F_14530c : fetch_word Asan.M.loaded_segments (0x145350 : word) = Some W_14530c.
Proof. vm_refl. Qed.
Lemma D_14530c : decode_any W_14530c = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_145310 : bv 32 := 0x0036f693.
Lemma F_145310 : fetch_word Asan.M.loaded_segments (0x145354 : word) = Some W_145310.
Proof. vm_refl. Qed.
Lemma D_145310 : decode_any W_145310 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_145314 : bv 32 := 0x00459713.
Lemma F_145314 : fetch_word Asan.M.loaded_segments (0x145358 : word) = Some W_145314.
Proof. vm_refl. Qed.
Lemma D_145314 : decode_any W_145314 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_145318 : bv 32 := 0x40d60633.
Lemma F_145318 : fetch_word Asan.M.loaded_segments (0x14535c : word) = Some W_145318.
Proof. vm_refl. Qed.
Lemma D_145318 : decode_any W_145318 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_14531c : bv 32 := 0x00d505b3.
Lemma F_14531c : fetch_word Asan.M.loaded_segments (0x145360 : word) = Some W_14531c.
Proof. vm_refl. Qed.
Lemma D_14531c : decode_any W_14531c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_145320 : bv 32 := 0x10070693.
Lemma F_145320 : fetch_word Asan.M.loaded_segments (0x145364 : word) = Some W_145320.
Proof. vm_refl. Qed.
Lemma D_145320 : decode_any W_145320 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_145324 : bv 32 := 0xffc67713.
Lemma F_145324 : fetch_word Asan.M.loaded_segments (0x145368 : word) = Some W_145324.
Proof. vm_refl. Qed.
Lemma D_145324 : decode_any W_145324 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_145328 : bv 32 := 0x02d83633.
Lemma F_145328 : fetch_word Asan.M.loaded_segments (0x14536c : word) = Some W_145328.
Proof. vm_refl. Qed.
Lemma D_145328 : decode_any W_145328 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_14532c : bv 32 := 0x00c5a023.
Lemma F_14532c : fetch_word Asan.M.loaded_segments (0x145370 : word) = Some W_14532c.
Proof. vm_refl. Qed.
Lemma D_14532c : decode_any W_14532c = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145330 : bv 32 := 0x00e586b3.
Lemma F_145330 : fetch_word Asan.M.loaded_segments (0x145374 : word) = Some W_145330.
Proof. vm_refl. Qed.
Lemma D_145330 : decode_any W_145330 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_145334 : bv 32 := 0xfec6ae23.
Lemma F_145334 : fetch_word Asan.M.loaded_segments (0x145378 : word) = Some W_145334.
Proof. vm_refl. Qed.
Lemma D_145334 : decode_any W_145334 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_145338 : bv 32 := 0x08f76063.
Lemma F_145338 : fetch_word Asan.M.loaded_segments (0x14537c : word) = Some W_145338.
Proof. vm_refl. Qed.
Lemma D_145338 : decode_any W_145338 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_14533c : bv 32 := 0x00c5a223.
Lemma F_14533c : fetch_word Asan.M.loaded_segments (0x145380 : word) = Some W_14533c.
Proof. vm_refl. Qed.
Lemma D_14533c : decode_any W_14533c = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_145340 : bv 32 := 0x00c5a423.
Lemma F_145340 : fetch_word Asan.M.loaded_segments (0x145384 : word) = Some W_145340.
Proof. vm_refl. Qed.
Lemma D_145340 : decode_any W_145340 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145344 : bv 32 := 0x01900793.
Lemma F_145344 : fetch_word Asan.M.loaded_segments (0x145388 : word) = Some W_145344.
Proof. vm_refl. Qed.
Lemma D_145344 : decode_any W_145344 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_145348 : bv 32 := 0xfec6aa23.
Lemma F_145348 : fetch_word Asan.M.loaded_segments (0x14538c : word) = Some W_145348.
Proof. vm_refl. Qed.
Lemma D_145348 : decode_any W_145348 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_14534c : bv 32 := 0xfec6ac23.
Lemma F_14534c : fetch_word Asan.M.loaded_segments (0x145390 : word) = Some W_14534c.
Proof. vm_refl. Qed.
Lemma D_14534c : decode_any W_14534c = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_145350 : bv 32 := 0x06f76463.
Lemma F_145350 : fetch_word Asan.M.loaded_segments (0x145394 : word) = Some W_145350.
Proof. vm_refl. Qed.
Lemma D_145350 : decode_any W_145350 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_145354 : bv 32 := 0x00c5a623.
Lemma F_145354 : fetch_word Asan.M.loaded_segments (0x145398 : word) = Some W_145354.
Proof. vm_refl. Qed.
Lemma D_145354 : decode_any W_145354 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_145358 : bv 32 := 0x00c5a823.
Lemma F_145358 : fetch_word Asan.M.loaded_segments (0x14539c : word) = Some W_145358.
Proof. vm_refl. Qed.
Lemma D_145358 : decode_any W_145358 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14535c : bv 32 := 0x00c5aa23.
Lemma F_14535c : fetch_word Asan.M.loaded_segments (0x1453a0 : word) = Some W_14535c.
Proof. vm_refl. Qed.
Lemma D_14535c : decode_any W_14535c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_145360 : bv 32 := 0x00c5ac23.
Lemma F_145360 : fetch_word Asan.M.loaded_segments (0x1453a4 : word) = Some W_145360.
Proof. vm_refl. Qed.
Lemma D_145360 : decode_any W_145360 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_145364 : bv 32 := 0x0045f793.
Lemma F_145364 : fetch_word Asan.M.loaded_segments (0x1453a8 : word) = Some W_145364.
Proof. vm_refl. Qed.
Lemma D_145364 : decode_any W_145364 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_145368 : bv 32 := 0x02000813.
Lemma F_145368 : fetch_word Asan.M.loaded_segments (0x1453ac : word) = Some W_145368.
Proof. vm_refl. Qed.
Lemma D_145368 : decode_any W_145368 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14536c : bv 32 := 0x01878793.
Lemma F_14536c : fetch_word Asan.M.loaded_segments (0x1453b0 : word) = Some W_14536c.
Proof. vm_refl. Qed.
Lemma D_14536c : decode_any W_14536c = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_145370 : bv 32 := 0x40f70733.
Lemma F_145370 : fetch_word Asan.M.loaded_segments (0x1453b4 : word) = Some W_145370.
Proof. vm_refl. Qed.
Lemma D_145370 : decode_any W_145370 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_145374 : bv 32 := 0xfec6a223.
Lemma F_145374 : fetch_word Asan.M.loaded_segments (0x1453b8 : word) = Some W_145374.
Proof. vm_refl. Qed.
Lemma D_145374 : decode_any W_145374 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_145378 : bv 32 := 0xfec6a423.
Lemma F_145378 : fetch_word Asan.M.loaded_segments (0x1453bc : word) = Some W_145378.
Proof. vm_refl. Qed.
Lemma D_145378 : decode_any W_145378 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_14537c : bv 32 := 0xfec6a623.
Lemma F_14537c : fetch_word Asan.M.loaded_segments (0x1453c0 : word) = Some W_14537c.
Proof. vm_refl. Qed.
Lemma D_14537c : decode_any W_14537c = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_145380 : bv 32 := 0xfec6a823.
Lemma F_145380 : fetch_word Asan.M.loaded_segments (0x1453c4 : word) = Some W_145380.
Proof. vm_refl. Qed.
Lemma D_145380 : decode_any W_145380 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_145384 : bv 32 := 0x03076a63.
Lemma F_145384 : fetch_word Asan.M.loaded_segments (0x1453c8 : word) = Some W_145384.
Proof. vm_refl. Qed.
Lemma D_145384 : decode_any W_145384 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_145388 : bv 32 := 0x02061613.
Lemma F_145388 : fetch_word Asan.M.loaded_segments (0x1453cc : word) = Some W_145388.
Proof. vm_refl. Qed.
Lemma D_145388 : decode_any W_145388 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14538c : bv 32 := 0x00f585b3.
Lemma F_14538c : fetch_word Asan.M.loaded_segments (0x1453d0 : word) = Some W_14538c.
Proof. vm_refl. Qed.
Lemma D_14538c : decode_any W_14538c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_145390 : bv 32 := 0x02065693.
Lemma F_145390 : fetch_word Asan.M.loaded_segments (0x1453d4 : word) = Some W_145390.
Proof. vm_refl. Qed.
Lemma D_145390 : decode_any W_145390 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_145394 : bv 32 := 0x00d66633.
Lemma F_145394 : fetch_word Asan.M.loaded_segments (0x1453d8 : word) = Some W_145394.
Proof. vm_refl. Qed.
Lemma D_145394 : decode_any W_145394 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_145398 : bv 32 := 0x01f00693.
Lemma F_145398 : fetch_word Asan.M.loaded_segments (0x1453dc : word) = Some W_145398.
Proof. vm_refl. Qed.
Lemma D_145398 : decode_any W_145398 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_14539c : bv 32 := 0x00c5b023.
Lemma F_14539c : fetch_word Asan.M.loaded_segments (0x1453e0 : word) = Some W_14539c.
Proof. vm_refl. Qed.
Lemma D_14539c : decode_any W_14539c = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1453a0 : bv 32 := 0x00c5b423.
Lemma F_1453a0 : fetch_word Asan.M.loaded_segments (0x1453e4 : word) = Some W_1453a0.
Proof. vm_refl. Qed.
Lemma D_1453a0 : decode_any W_1453a0 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1453a4 : bv 32 := 0x00c5b823.
Lemma F_1453a4 : fetch_word Asan.M.loaded_segments (0x1453e8 : word) = Some W_1453a4.
Proof. vm_refl. Qed.
Lemma D_1453a4 : decode_any W_1453a4 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1453a8 : bv 32 := 0x00c5bc23.
Lemma F_1453a8 : fetch_word Asan.M.loaded_segments (0x1453ec : word) = Some W_1453a8.
Proof. vm_refl. Qed.
Lemma D_1453a8 : decode_any W_1453a8 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1453ac : bv 32 := 0xfe070713.
Lemma F_1453ac : fetch_word Asan.M.loaded_segments (0x1453f0 : word) = Some W_1453ac.
Proof. vm_refl. Qed.
Lemma D_1453ac : decode_any W_1453ac = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1453b0 : bv 32 := 0x02058593.
Lemma F_1453b0 : fetch_word Asan.M.loaded_segments (0x1453f4 : word) = Some W_1453b0.
Proof. vm_refl. Qed.
Lemma D_1453b0 : decode_any W_1453b0 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1453b4 : bv 32 := 0xfee6e4e3.
Lemma F_1453b4 : fetch_word Asan.M.loaded_segments (0x1453f8 : word) = Some W_1453b4.
Proof. vm_refl. Qed.
Lemma D_1453b4 : decode_any W_1453b4 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_1453b8 : bv 32 := 0x00008067.
Lemma F_1453b8 : fetch_word Asan.M.loaded_segments (0x1453fc : word) = Some W_1453b8.
Proof. vm_refl. Qed.
Lemma D_1453b8 : decode_any W_1453b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457a8 : bv 32 := 0x00757593.
Lemma F_1457a8 : fetch_word Asan.M.loaded_segments (0x1457ec : word) = Some W_1457a8.
Proof. vm_refl. Qed.
Lemma D_1457a8 : decode_any W_1457a8 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457ac : bv 32 := 0x00050613.
Lemma F_1457ac : fetch_word Asan.M.loaded_segments (0x1457f0 : word) = Some W_1457ac.
Proof. vm_refl. Qed.
Lemma D_1457ac : decode_any W_1457ac = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457b0 : bv 32 := 0x02058a63.
Lemma F_1457b0 : fetch_word Asan.M.loaded_segments (0x1457f4 : word) = Some W_1457b0.
Proof. vm_refl. Qed.
Lemma D_1457b0 : decode_any W_1457b0 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457b4 : bv 32 := 0x00054583.
Lemma F_1457b4 : fetch_word Asan.M.loaded_segments (0x1457f8 : word) = Some W_1457b4.
Proof. vm_refl. Qed.
Lemma D_1457b4 : decode_any W_1457b4 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457b8 : bv 32 := 0x06058c63.
Lemma F_1457b8 : fetch_word Asan.M.loaded_segments (0x1457fc : word) = Some W_1457b8.
Proof. vm_refl. Qed.
Lemma D_1457b8 : decode_any W_1457b8 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457bc : bv 32 := 0x00150613.
Lemma F_1457bc : fetch_word Asan.M.loaded_segments (0x145800 : word) = Some W_1457bc.
Proof. vm_refl. Qed.
Lemma D_1457bc : decode_any W_1457bc = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457c0 : bv 32 := 0x00050593.
Lemma F_1457c0 : fetch_word Asan.M.loaded_segments (0x145804 : word) = Some W_1457c0.
Proof. vm_refl. Qed.
Lemma D_1457c0 : decode_any W_1457c0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457c4 : bv 32 := 0x00158693.
Lemma F_1457c4 : fetch_word Asan.M.loaded_segments (0x145808 : word) = Some W_1457c4.
Proof. vm_refl. Qed.
Lemma D_1457c4 : decode_any W_1457c4 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457c8 : bv 32 := 0x0076f693.
Lemma F_1457c8 : fetch_word Asan.M.loaded_segments (0x14580c : word) = Some W_1457c8.
Proof. vm_refl. Qed.
Lemma D_1457c8 : decode_any W_1457c8 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457cc : bv 32 := 0x00068c63.
Lemma F_1457cc : fetch_word Asan.M.loaded_segments (0x145810 : word) = Some W_1457cc.
Proof. vm_refl. Qed.
Lemma D_1457cc : decode_any W_1457cc = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457d0 : bv 32 := 0x00064683.
Lemma F_1457d0 : fetch_word Asan.M.loaded_segments (0x145814 : word) = Some W_1457d0.
Proof. vm_refl. Qed.
Lemma D_1457d0 : decode_any W_1457d0 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457d4 : bv 32 := 0x00160613.
Lemma F_1457d4 : fetch_word Asan.M.loaded_segments (0x145818 : word) = Some W_1457d4.
Proof. vm_refl. Qed.
Lemma D_1457d4 : decode_any W_1457d4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457d8 : bv 32 := 0x00158593.
Lemma F_1457d8 : fetch_word Asan.M.loaded_segments (0x14581c : word) = Some W_1457d8.
Proof. vm_refl. Qed.
Lemma D_1457d8 : decode_any W_1457d8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457dc : bv 32 := 0xfe0694e3.
Lemma F_1457dc : fetch_word Asan.M.loaded_segments (0x145820 : word) = Some W_1457dc.
Proof. vm_refl. Qed.
Lemma D_1457dc : decode_any W_1457dc = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457e0 : bv 32 := 0x0480006f.
Lemma F_1457e0 : fetch_word Asan.M.loaded_segments (0x145824 : word) = Some W_1457e0.
Proof. vm_refl. Qed.
Lemma D_1457e0 : decode_any W_1457e0 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457e4 : bv 32 := 0xffecb597.
Lemma F_1457e4 : fetch_word Asan.M.loaded_segments (0x145828 : word) = Some W_1457e4.
Proof. vm_refl. Qed.
Lemma D_1457e4 : decode_any W_1457e4 = Some (Auipc 11 1048267, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457e8 : bv 32 := 0xffecb717.
Lemma F_1457e8 : fetch_word Asan.M.loaded_segments (0x14582c : word) = Some W_1457e8.
Proof. vm_refl. Qed.
Lemma D_1457e8 : decode_any W_1457e8 = Some (Auipc 14 1048267, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457ec : bv 32 := 0xbb05b683.
Lemma F_1457ec : fetch_word Asan.M.loaded_segments (0x145830 : word) = Some W_1457ec.
Proof. vm_refl. Qed.
Lemma D_1457ec : decode_any W_1457ec = Some (Load SZ8 true 13 11 2992, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457f0 : bv 32 := 0xb9473703.
Lemma F_1457f0 : fetch_word Asan.M.loaded_segments (0x145834 : word) = Some W_1457f0.
Proof. vm_refl. Qed.
Lemma D_1457f0 : decode_any W_1457f0 = Some (Load SZ8 true 14 14 2964, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457f4 : bv 32 := 0xff760593.
Lemma F_1457f4 : fetch_word Asan.M.loaded_segments (0x145838 : word) = Some W_1457f4.
Proof. vm_refl. Qed.
Lemma D_1457f4 : decode_any W_1457f4 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457f8 : bv 32 := 0xff860613.
Lemma F_1457f8 : fetch_word Asan.M.loaded_segments (0x14583c : word) = Some W_1457f8.
Proof. vm_refl. Qed.
Lemma D_1457f8 : decode_any W_1457f8 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1457fc : bv 32 := 0x00863783.
Lemma F_1457fc : fetch_word Asan.M.loaded_segments (0x145840 : word) = Some W_1457fc.
Proof. vm_refl. Qed.
Lemma D_1457fc : decode_any W_1457fc = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145800 : bv 32 := 0x00860613.
Lemma F_145800 : fetch_word Asan.M.loaded_segments (0x145844 : word) = Some W_145800.
Proof. vm_refl. Qed.
Lemma D_145800 : decode_any W_145800 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145804 : bv 32 := 0x40f68833.
Lemma F_145804 : fetch_word Asan.M.loaded_segments (0x145848 : word) = Some W_145804.
Proof. vm_refl. Qed.
Lemma D_145804 : decode_any W_145804 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_145808 : bv 32 := 0x00f867b3.
Lemma F_145808 : fetch_word Asan.M.loaded_segments (0x14584c : word) = Some W_145808.
Proof. vm_refl. Qed.
Lemma D_145808 : decode_any W_145808 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_14580c : bv 32 := 0x00e7f7b3.
Lemma F_14580c : fetch_word Asan.M.loaded_segments (0x145850 : word) = Some W_14580c.
Proof. vm_refl. Qed.
Lemma D_14580c : decode_any W_14580c = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_145810 : bv 32 := 0x00858593.
Lemma F_145810 : fetch_word Asan.M.loaded_segments (0x145854 : word) = Some W_145810.
Proof. vm_refl. Qed.
Lemma D_145810 : decode_any W_145810 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145814 : bv 32 := 0xfee784e3.
Lemma F_145814 : fetch_word Asan.M.loaded_segments (0x145858 : word) = Some W_145814.
Proof. vm_refl. Qed.
Lemma D_145814 : decode_any W_145814 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_145818 : bv 32 := 0x00064683.
Lemma F_145818 : fetch_word Asan.M.loaded_segments (0x14585c : word) = Some W_145818.
Proof. vm_refl. Qed.
Lemma D_145818 : decode_any W_145818 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14581c : bv 32 := 0x00160613.
Lemma F_14581c : fetch_word Asan.M.loaded_segments (0x145860 : word) = Some W_14581c.
Proof. vm_refl. Qed.
Lemma D_14581c : decode_any W_14581c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_145820 : bv 32 := 0x00158593.
Lemma F_145820 : fetch_word Asan.M.loaded_segments (0x145864 : word) = Some W_145820.
Proof. vm_refl. Qed.
Lemma D_145820 : decode_any W_145820 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_145824 : bv 32 := 0xfe069ae3.
Lemma F_145824 : fetch_word Asan.M.loaded_segments (0x145868 : word) = Some W_145824.
Proof. vm_refl. Qed.
Lemma D_145824 : decode_any W_145824 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_145828 : bv 32 := 0x40a58533.
Lemma F_145828 : fetch_word Asan.M.loaded_segments (0x14586c : word) = Some W_145828.
Proof. vm_refl. Qed.
Lemma D_145828 : decode_any W_145828 = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_14582c : bv 32 := 0x00008067.
Lemma F_14582c : fetch_word Asan.M.loaded_segments (0x145870 : word) = Some W_14582c.
Proof. vm_refl. Qed.
Lemma D_14582c : decode_any W_14582c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145830 : bv 32 := 0x40a50533.
Lemma F_145830 : fetch_word Asan.M.loaded_segments (0x145874 : word) = Some W_145830.
Proof. vm_refl. Qed.
Lemma D_145830 : decode_any W_145830 = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_145834 : bv 32 := 0x00008067.
Lemma F_145834 : fetch_word Asan.M.loaded_segments (0x145878 : word) = Some W_145834.
Proof. vm_refl. Qed.
Lemma D_145834 : decode_any W_145834 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145b80 : bv 32 := 0x0056b597.
Lemma F_145b80 : fetch_word Asan.M.loaded_segments (0x145bc4 : word) = Some W_145b80.
Proof. vm_refl. Qed.
Lemma D_145b80 : decode_any W_145b80 = Some (Auipc 11 1387, 4%Z).
Proof. vm_refl. Qed.

Definition W_145b84 : bv 32 := 0x11f58683.
Lemma F_145b84 : fetch_word Asan.M.loaded_segments (0x145bc8 : word) = Some W_145b84.
Proof. vm_refl. Qed.
Lemma D_145b84 : decode_any W_145b84 = Some (Load SZ1 true 13 11 287, 4%Z).
Proof. vm_refl. Qed.

Definition W_145b88 : bv 32 := 0x1e068863.
Lemma F_145b88 : fetch_word Asan.M.loaded_segments (0x145bcc : word) = Some W_145b88.
Proof. vm_refl. Qed.
Lemma D_145b88 : decode_any W_145b88 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_145d78 : bv 32 := 0x00008067.
Lemma F_145d78 : fetch_word Asan.M.loaded_segments (0x145dbc : word) = Some W_145d78.
Proof. vm_refl. Qed.
Lemma D_145d78 : decode_any W_145d78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e08 : bv 32 := 0x00052583.
Lemma F_145e08 : fetch_word Asan.M.loaded_segments (0x145e4c : word) = Some W_145e08.
Proof. vm_refl. Qed.
Lemma D_145e08 : decode_any W_145e08 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e0c : bv 32 := 0x0005c463.
Lemma F_145e0c : fetch_word Asan.M.loaded_segments (0x145e50 : word) = Some W_145e0c.
Proof. vm_refl. Qed.
Lemma D_145e0c : decode_any W_145e0c = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e10 : bv 32 := 0x00008067.
Lemma F_145e10 : fetch_word Asan.M.loaded_segments (0x145e54 : word) = Some W_145e10.
Proof. vm_refl. Qed.
Lemma D_145e10 : decode_any W_145e10 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e7c : bv 32 := 0x00050893.
Lemma F_145e7c : fetch_word Asan.M.loaded_segments (0x145ec0 : word) = Some W_145e7c.
Proof. vm_refl. Qed.
Lemma D_145e7c : decode_any W_145e7c = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e80 : bv 32 := 0x00058513.
Lemma F_145e80 : fetch_word Asan.M.loaded_segments (0x145ec4 : word) = Some W_145e80.
Proof. vm_refl. Qed.
Lemma D_145e80 : decode_any W_145e80 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e84 : bv 32 := 0x00060593.
Lemma F_145e84 : fetch_word Asan.M.loaded_segments (0x145ec8 : word) = Some W_145e84.
Proof. vm_refl. Qed.
Lemma D_145e84 : decode_any W_145e84 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e88 : bv 32 := 0x00068613.
Lemma F_145e88 : fetch_word Asan.M.loaded_segments (0x145ecc : word) = Some W_145e88.
Proof. vm_refl. Qed.
Lemma D_145e88 : decode_any W_145e88 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e8c : bv 32 := 0x00070693.
Lemma F_145e8c : fetch_word Asan.M.loaded_segments (0x145ed0 : word) = Some W_145e8c.
Proof. vm_refl. Qed.
Lemma D_145e8c : decode_any W_145e8c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e90 : bv 32 := 0x00078713.
Lemma F_145e90 : fetch_word Asan.M.loaded_segments (0x145ed4 : word) = Some W_145e90.
Proof. vm_refl. Qed.
Lemma D_145e90 : decode_any W_145e90 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e94 : bv 32 := 0x00080793.
Lemma F_145e94 : fetch_word Asan.M.loaded_segments (0x145ed8 : word) = Some W_145e94.
Proof. vm_refl. Qed.
Lemma D_145e94 : decode_any W_145e94 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145e9c : bv 32 := 0x00008067.
Lemma F_145e9c : fetch_word Asan.M.loaded_segments (0x145ee0 : word) = Some W_145e9c.
Proof. vm_refl. Qed.
Lemma D_145e9c : decode_any W_145e9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145ea0 : bv 32 := 0xfddff06f.
Lemma F_145ea0 : fetch_word Asan.M.loaded_segments (0x145ee4 : word) = Some W_145ea0.
Proof. vm_refl. Qed.
Lemma D_145ea0 : decode_any W_145ea0 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition W_145ea4 : bv 32 := 0x00020593.
Lemma F_145ea4 : fetch_word Asan.M.loaded_segments (0x145ee8 : word) = Some W_145ea4.
Proof. vm_refl. Qed.
Lemma D_145ea4 : decode_any W_145ea4 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145ea8 : bv 32 := 0x00053603.
Lemma F_145ea8 : fetch_word Asan.M.loaded_segments (0x145eec : word) = Some W_145ea8.
Proof. vm_refl. Qed.
Lemma D_145ea8 : decode_any W_145ea8 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145eac : bv 32 := 0xff85b583.
Lemma F_145eac : fetch_word Asan.M.loaded_segments (0x145ef0 : word) = Some W_145eac.
Proof. vm_refl. Qed.
Lemma D_145eac : decode_any W_145eac = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_145eb0 : bv 32 := 0x00853503.
Lemma F_145eb0 : fetch_word Asan.M.loaded_segments (0x145ef4 : word) = Some W_145eb0.
Proof. vm_refl. Qed.
Lemma D_145eb0 : decode_any W_145eb0 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_145eb4 : bv 32 := 0x00361613.
Lemma F_145eb4 : fetch_word Asan.M.loaded_segments (0x145ef8 : word) = Some W_145eb4.
Proof. vm_refl. Qed.
Lemma D_145eb4 : decode_any W_145eb4 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_145eb8 : bv 32 := 0x00c585b3.
Lemma F_145eb8 : fetch_word Asan.M.loaded_segments (0x145efc : word) = Some W_145eb8.
Proof. vm_refl. Qed.
Lemma D_145eb8 : decode_any W_145eb8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_145ebc : bv 32 := 0x0005b583.
Lemma F_145ebc : fetch_word Asan.M.loaded_segments (0x145f00 : word) = Some W_145ebc.
Proof. vm_refl. Qed.
Lemma D_145ebc : decode_any W_145ebc = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_145ec0 : bv 32 := 0x00b50533.
Lemma F_145ec0 : fetch_word Asan.M.loaded_segments (0x145f04 : word) = Some W_145ec0.
Proof. vm_refl. Qed.
Lemma D_145ec0 : decode_any W_145ec0 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_145ec4 : bv 32 := 0x00008067.
Lemma F_145ec4 : fetch_word Asan.M.loaded_segments (0x145f08 : word) = Some W_145ec4.
Proof. vm_refl. Qed.
Lemma D_145ec4 : decode_any W_145ec4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

