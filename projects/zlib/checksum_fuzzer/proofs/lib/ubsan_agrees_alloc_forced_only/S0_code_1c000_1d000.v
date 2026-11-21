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

Definition W_1cc64 : bv 32 := 0x0035f693.
Lemma F_1cc64 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd04 : word) = Some W_1cc64.
Proof. vm_refl. Qed.
Lemma D_1cc64 : decode_any W_1cc64 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc68 : bv 32 := 0x10068863.
Lemma F_1cc68 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd08 : word) = Some W_1cc68.
Proof. vm_refl. Qed.
Lemma D_1cc68 : decode_any W_1cc68 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc6c : bv 32 := 0x02060e63.
Lemma F_1cc6c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd0c : word) = Some W_1cc6c.
Proof. vm_refl. Qed.
Lemma D_1cc6c : decode_any W_1cc6c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc70 : bv 32 := 0x00158713.
Lemma F_1cc70 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd10 : word) = Some W_1cc70.
Proof. vm_refl. Qed.
Lemma D_1cc70 : decode_any W_1cc70 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc74 : bv 32 := 0x00100793.
Lemma F_1cc74 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd14 : word) = Some W_1cc74.
Proof. vm_refl. Qed.
Lemma D_1cc74 : decode_any W_1cc74 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc78 : bv 32 := 0x00050693.
Lemma F_1cc78 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd18 : word) = Some W_1cc78.
Proof. vm_refl. Qed.
Lemma D_1cc78 : decode_any W_1cc78 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc7c : bv 32 := 0x0005c883.
Lemma F_1cc7c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd1c : word) = Some W_1cc7c.
Proof. vm_refl. Qed.
Lemma D_1cc7c : decode_any W_1cc7c = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc80 : bv 32 := 0x00060813.
Lemma F_1cc80 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd20 : word) = Some W_1cc80.
Proof. vm_refl. Qed.
Lemma D_1cc80 : decode_any W_1cc80 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc84 : bv 32 := 0x00158593.
Lemma F_1cc84 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd24 : word) = Some W_1cc84.
Proof. vm_refl. Qed.
Lemma D_1cc84 : decode_any W_1cc84 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc88 : bv 32 := 0x00377293.
Lemma F_1cc88 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd28 : word) = Some W_1cc88.
Proof. vm_refl. Qed.
Lemma D_1cc88 : decode_any W_1cc88 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc8c : bv 32 := 0x01168023.
Lemma F_1cc8c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd2c : word) = Some W_1cc8c.
Proof. vm_refl. Qed.
Lemma D_1cc8c : decode_any W_1cc8c = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc90 : bv 32 := 0x00168693.
Lemma F_1cc90 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd30 : word) = Some W_1cc90.
Proof. vm_refl. Qed.
Lemma D_1cc90 : decode_any W_1cc90 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc94 : bv 32 := 0xfff60613.
Lemma F_1cc94 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd34 : word) = Some W_1cc94.
Proof. vm_refl. Qed.
Lemma D_1cc94 : decode_any W_1cc94 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc98 : bv 32 := 0x00028a63.
Lemma F_1cc98 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd38 : word) = Some W_1cc98.
Proof. vm_refl. Qed.
Lemma D_1cc98 : decode_any W_1cc98 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cc9c : bv 32 := 0x00170713.
Lemma F_1cc9c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd3c : word) = Some W_1cc9c.
Proof. vm_refl. Qed.
Lemma D_1cc9c : decode_any W_1cc9c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cca0 : bv 32 := 0xfcf81ee3.
Lemma F_1cca0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd40 : word) = Some W_1cca0.
Proof. vm_refl. Qed.
Lemma D_1cca0 : decode_any W_1cca0 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cca4 : bv 32 := 0x0080006f.
Lemma F_1cca4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd44 : word) = Some W_1cca4.
Proof. vm_refl. Qed.
Lemma D_1cca4 : decode_any W_1cca4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cca8 : bv 32 := 0x00050693.
Lemma F_1cca8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd48 : word) = Some W_1cca8.
Proof. vm_refl. Qed.
Lemma D_1cca8 : decode_any W_1cca8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccac : bv 32 := 0x0036f793.
Lemma F_1ccac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd4c : word) = Some W_1ccac.
Proof. vm_refl. Qed.
Lemma D_1ccac : decode_any W_1ccac = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccb0 : bv 32 := 0x0c078a63.
Lemma F_1ccb0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd50 : word) = Some W_1ccb0.
Proof. vm_refl. Qed.
Lemma D_1ccb0 : decode_any W_1ccb0 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccb4 : bv 32 := 0x02000713.
Lemma F_1ccb4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd54 : word) = Some W_1ccb4.
Proof. vm_refl. Qed.
Lemma D_1ccb4 : decode_any W_1ccb4 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccb8 : bv 32 := 0x02e67063.
Lemma F_1ccb8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd58 : word) = Some W_1ccb8.
Proof. vm_refl. Qed.
Lemma D_1ccb8 : decode_any W_1ccb8 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccbc : bv 32 := 0x01000713.
Lemma F_1ccbc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd5c : word) = Some W_1ccbc.
Proof. vm_refl. Qed.
Lemma D_1ccbc : decode_any W_1ccbc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccc0 : bv 32 := 0x24e67863.
Lemma F_1ccc0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd60 : word) = Some W_1ccc0.
Proof. vm_refl. Qed.
Lemma D_1ccc0 : decode_any W_1ccc0 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccc4 : bv 32 := 0x00867713.
Lemma F_1ccc4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd64 : word) = Some W_1ccc4.
Proof. vm_refl. Qed.
Lemma D_1ccc4 : decode_any W_1ccc4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccc8 : bv 32 := 0x2c071e63.
Lemma F_1ccc8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd68 : word) = Some W_1ccc8.
Proof. vm_refl. Qed.
Lemma D_1ccc8 : decode_any W_1ccc8 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cccc : bv 32 := 0x00467713.
Lemma F_1cccc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd6c : word) = Some W_1cccc.
Proof. vm_refl. Qed.
Lemma D_1cccc : decode_any W_1cccc = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccd0 : bv 32 := 0x32071463.
Lemma F_1ccd0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd70 : word) = Some W_1ccd0.
Proof. vm_refl. Qed.
Lemma D_1ccd0 : decode_any W_1ccd0 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccd4 : bv 32 := 0x3500006f.
Lemma F_1ccd4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd74 : word) = Some W_1ccd4.
Proof. vm_refl. Qed.
Lemma D_1ccd4 : decode_any W_1ccd4 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccd8 : bv 32 := 0x0005a703.
Lemma F_1ccd8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd78 : word) = Some W_1ccd8.
Proof. vm_refl. Qed.
Lemma D_1ccd8 : decode_any W_1ccd8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccdc : bv 32 := 0x00300813.
Lemma F_1ccdc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd7c : word) = Some W_1ccdc.
Proof. vm_refl. Qed.
Lemma D_1ccdc : decode_any W_1ccdc = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cce0 : bv 32 := 0x11078e63.
Lemma F_1cce0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd80 : word) = Some W_1cce0.
Proof. vm_refl. Qed.
Lemma D_1cce0 : decode_any W_1cce0 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cce4 : bv 32 := 0x00200813.
Lemma F_1cce4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd84 : word) = Some W_1cce4.
Proof. vm_refl. Qed.
Lemma D_1cce4 : decode_any W_1cce4 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cce8 : bv 32 := 0x19079c63.
Lemma F_1cce8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd88 : word) = Some W_1cce8.
Proof. vm_refl. Qed.
Lemma D_1cce8 : decode_any W_1cce8 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccec : bv 32 := 0x00875793.
Lemma F_1ccec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd8c : word) = Some W_1ccec.
Proof. vm_refl. Qed.
Lemma D_1ccec : decode_any W_1ccec = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccf0 : bv 32 := 0xffe60613.
Lemma F_1ccf0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd90 : word) = Some W_1ccf0.
Proof. vm_refl. Qed.
Lemma D_1ccf0 : decode_any W_1ccf0 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccf4 : bv 32 := 0x00e68023.
Lemma F_1ccf4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd94 : word) = Some W_1ccf4.
Proof. vm_refl. Qed.
Lemma D_1ccf4 : decode_any W_1ccf4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccf8 : bv 32 := 0x00f680a3.
Lemma F_1ccf8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd98 : word) = Some W_1ccf8.
Proof. vm_refl. Qed.
Lemma D_1ccf8 : decode_any W_1ccf8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ccfc : bv 32 := 0x00268693.
Lemma F_1ccfc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cd9c : word) = Some W_1ccfc.
Proof. vm_refl. Qed.
Lemma D_1ccfc : decode_any W_1ccfc = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd00 : bv 32 := 0x01058593.
Lemma F_1cd00 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cda0 : word) = Some W_1cd00.
Proof. vm_refl. Qed.
Lemma D_1cd00 : decode_any W_1cd00 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd04 : bv 32 := 0x01100793.
Lemma F_1cd04 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cda4 : word) = Some W_1cd04.
Proof. vm_refl. Qed.
Lemma D_1cd04 : decode_any W_1cd04 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd08 : bv 32 := 0x0107581b.
Lemma F_1cd08 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cda8 : word) = Some W_1cd08.
Proof. vm_refl. Qed.
Lemma D_1cd08 : decode_any W_1cd08 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd0c : bv 32 := 0xff45a883.
Lemma F_1cd0c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdac : word) = Some W_1cd0c.
Proof. vm_refl. Qed.
Lemma D_1cd0c : decode_any W_1cd0c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd10 : bv 32 := 0xff85a283.
Lemma F_1cd10 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdb0 : word) = Some W_1cd10.
Proof. vm_refl. Qed.
Lemma D_1cd10 : decode_any W_1cd10 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd14 : bv 32 := 0xffc5a303.
Lemma F_1cd14 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdb4 : word) = Some W_1cd14.
Proof. vm_refl. Qed.
Lemma D_1cd14 : decode_any W_1cd14 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd18 : bv 32 := 0x0005a703.
Lemma F_1cd18 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdb8 : word) = Some W_1cd18.
Proof. vm_refl. Qed.
Lemma D_1cd18 : decode_any W_1cd18 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd1c : bv 32 := 0x01089393.
Lemma F_1cd1c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdbc : word) = Some W_1cd1c.
Proof. vm_refl. Qed.
Lemma D_1cd1c : decode_any W_1cd1c = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd20 : bv 32 := 0x0108d89b.
Lemma F_1cd20 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdc0 : word) = Some W_1cd20.
Proof. vm_refl. Qed.
Lemma D_1cd20 : decode_any W_1cd20 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd24 : bv 32 := 0x0103e833.
Lemma F_1cd24 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdc4 : word) = Some W_1cd24.
Proof. vm_refl. Qed.
Lemma D_1cd24 : decode_any W_1cd24 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd28 : bv 32 := 0x01029393.
Lemma F_1cd28 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdc8 : word) = Some W_1cd28.
Proof. vm_refl. Qed.
Lemma D_1cd28 : decode_any W_1cd28 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd2c : bv 32 := 0x0102d29b.
Lemma F_1cd2c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdcc : word) = Some W_1cd2c.
Proof. vm_refl. Qed.
Lemma D_1cd2c : decode_any W_1cd2c = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd30 : bv 32 := 0x0113e8b3.
Lemma F_1cd30 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdd0 : word) = Some W_1cd30.
Proof. vm_refl. Qed.
Lemma D_1cd30 : decode_any W_1cd30 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd34 : bv 32 := 0x01031393.
Lemma F_1cd34 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdd4 : word) = Some W_1cd34.
Proof. vm_refl. Qed.
Lemma D_1cd34 : decode_any W_1cd34 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd38 : bv 32 := 0x0103531b.
Lemma F_1cd38 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdd8 : word) = Some W_1cd38.
Proof. vm_refl. Qed.
Lemma D_1cd38 : decode_any W_1cd38 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd3c : bv 32 := 0x0053e2b3.
Lemma F_1cd3c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cddc : word) = Some W_1cd3c.
Proof. vm_refl. Qed.
Lemma D_1cd3c : decode_any W_1cd3c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd40 : bv 32 := 0x01071393.
Lemma F_1cd40 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cde0 : word) = Some W_1cd40.
Proof. vm_refl. Qed.
Lemma D_1cd40 : decode_any W_1cd40 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd44 : bv 32 := 0x0063e333.
Lemma F_1cd44 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cde4 : word) = Some W_1cd44.
Proof. vm_refl. Qed.
Lemma D_1cd44 : decode_any W_1cd44 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd48 : bv 32 := 0xff060613.
Lemma F_1cd48 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cde8 : word) = Some W_1cd48.
Proof. vm_refl. Qed.
Lemma D_1cd48 : decode_any W_1cd48 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd4c : bv 32 := 0x0106a023.
Lemma F_1cd4c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdec : word) = Some W_1cd4c.
Proof. vm_refl. Qed.
Lemma D_1cd4c : decode_any W_1cd4c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd50 : bv 32 := 0x0116a223.
Lemma F_1cd50 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdf0 : word) = Some W_1cd50.
Proof. vm_refl. Qed.
Lemma D_1cd50 : decode_any W_1cd50 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd54 : bv 32 := 0x0056a423.
Lemma F_1cd54 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdf4 : word) = Some W_1cd54.
Proof. vm_refl. Qed.
Lemma D_1cd54 : decode_any W_1cd54 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd58 : bv 32 := 0x0066a623.
Lemma F_1cd58 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdf8 : word) = Some W_1cd58.
Proof. vm_refl. Qed.
Lemma D_1cd58 : decode_any W_1cd58 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd5c : bv 32 := 0x01068693.
Lemma F_1cd5c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cdfc : word) = Some W_1cd5c.
Proof. vm_refl. Qed.
Lemma D_1cd5c : decode_any W_1cd5c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd60 : bv 32 := 0x01058593.
Lemma F_1cd60 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce00 : word) = Some W_1cd60.
Proof. vm_refl. Qed.
Lemma D_1cd60 : decode_any W_1cd60 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd64 : bv 32 := 0xfac7e2e3.
Lemma F_1cd64 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce04 : word) = Some W_1cd64.
Proof. vm_refl. Qed.
Lemma D_1cd64 : decode_any W_1cd64 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd68 : bv 32 := 0xff258593.
Lemma F_1cd68 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce08 : word) = Some W_1cd68.
Proof. vm_refl. Qed.
Lemma D_1cd68 : decode_any W_1cd68 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd6c : bv 32 := 0x01000713.
Lemma F_1cd6c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce0c : word) = Some W_1cd6c.
Proof. vm_refl. Qed.
Lemma D_1cd6c : decode_any W_1cd6c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd70 : bv 32 := 0xf4e66ae3.
Lemma F_1cd70 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce10 : word) = Some W_1cd70.
Proof. vm_refl. Qed.
Lemma D_1cd70 : decode_any W_1cd70 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd74 : bv 32 := 0x19c0006f.
Lemma F_1cd74 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce14 : word) = Some W_1cd74.
Proof. vm_refl. Qed.
Lemma D_1cd74 : decode_any W_1cd74 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd78 : bv 32 := 0x00050693.
Lemma F_1cd78 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce18 : word) = Some W_1cd78.
Proof. vm_refl. Qed.
Lemma D_1cd78 : decode_any W_1cd78 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd7c : bv 32 := 0x00357793.
Lemma F_1cd7c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce1c : word) = Some W_1cd7c.
Proof. vm_refl. Qed.
Lemma D_1cd7c : decode_any W_1cd7c = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd80 : bv 32 := 0xf2079ae3.
Lemma F_1cd80 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce20 : word) = Some W_1cd80.
Proof. vm_refl. Qed.
Lemma D_1cd80 : decode_any W_1cd80 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd84 : bv 32 := 0x01000713.
Lemma F_1cd84 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce24 : word) = Some W_1cd84.
Proof. vm_refl. Qed.
Lemma D_1cd84 : decode_any W_1cd84 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd88 : bv 32 := 0x02e66c63.
Lemma F_1cd88 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce28 : word) = Some W_1cd88.
Proof. vm_refl. Qed.
Lemma D_1cd88 : decode_any W_1cd88 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd8c : bv 32 := 0x00f00713.
Lemma F_1cd8c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce2c : word) = Some W_1cd8c.
Proof. vm_refl. Qed.
Lemma D_1cd8c : decode_any W_1cd8c = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd90 : bv 32 := 0x0005a783.
Lemma F_1cd90 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce30 : word) = Some W_1cd90.
Proof. vm_refl. Qed.
Lemma D_1cd90 : decode_any W_1cd90 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd94 : bv 32 := 0x0045a803.
Lemma F_1cd94 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce34 : word) = Some W_1cd94.
Proof. vm_refl. Qed.
Lemma D_1cd94 : decode_any W_1cd94 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd98 : bv 32 := 0x0085a883.
Lemma F_1cd98 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce38 : word) = Some W_1cd98.
Proof. vm_refl. Qed.
Lemma D_1cd98 : decode_any W_1cd98 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cd9c : bv 32 := 0x00c5a283.
Lemma F_1cd9c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce3c : word) = Some W_1cd9c.
Proof. vm_refl. Qed.
Lemma D_1cd9c : decode_any W_1cd9c = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cda0 : bv 32 := 0x01058593.
Lemma F_1cda0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce40 : word) = Some W_1cda0.
Proof. vm_refl. Qed.
Lemma D_1cda0 : decode_any W_1cda0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cda4 : bv 32 := 0xff060613.
Lemma F_1cda4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce44 : word) = Some W_1cda4.
Proof. vm_refl. Qed.
Lemma D_1cda4 : decode_any W_1cda4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cda8 : bv 32 := 0x00f6a023.
Lemma F_1cda8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce48 : word) = Some W_1cda8.
Proof. vm_refl. Qed.
Lemma D_1cda8 : decode_any W_1cda8 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdac : bv 32 := 0x0106a223.
Lemma F_1cdac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce4c : word) = Some W_1cdac.
Proof. vm_refl. Qed.
Lemma D_1cdac : decode_any W_1cdac = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdb0 : bv 32 := 0x0116a423.
Lemma F_1cdb0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce50 : word) = Some W_1cdb0.
Proof. vm_refl. Qed.
Lemma D_1cdb0 : decode_any W_1cdb0 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdb4 : bv 32 := 0x0056a623.
Lemma F_1cdb4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce54 : word) = Some W_1cdb4.
Proof. vm_refl. Qed.
Lemma D_1cdb4 : decode_any W_1cdb4 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdb8 : bv 32 := 0x01068693.
Lemma F_1cdb8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce58 : word) = Some W_1cdb8.
Proof. vm_refl. Qed.
Lemma D_1cdb8 : decode_any W_1cdb8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdbc : bv 32 := 0xfcc76ae3.
Lemma F_1cdbc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce5c : word) = Some W_1cdbc.
Proof. vm_refl. Qed.
Lemma D_1cdbc : decode_any W_1cdbc = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdc0 : bv 32 := 0x00800713.
Lemma F_1cdc0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce60 : word) = Some W_1cdc0.
Proof. vm_refl. Qed.
Lemma D_1cdc0 : decode_any W_1cdc0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdc4 : bv 32 := 0x00e66e63.
Lemma F_1cdc4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce64 : word) = Some W_1cdc4.
Proof. vm_refl. Qed.
Lemma D_1cdc4 : decode_any W_1cdc4 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdc8 : bv 32 := 0x0005a703.
Lemma F_1cdc8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce68 : word) = Some W_1cdc8.
Proof. vm_refl. Qed.
Lemma D_1cdc8 : decode_any W_1cdc8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdcc : bv 32 := 0x0045a783.
Lemma F_1cdcc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce6c : word) = Some W_1cdcc.
Proof. vm_refl. Qed.
Lemma D_1cdcc : decode_any W_1cdcc = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdd0 : bv 32 := 0x00e6a023.
Lemma F_1cdd0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce70 : word) = Some W_1cdd0.
Proof. vm_refl. Qed.
Lemma D_1cdd0 : decode_any W_1cdd0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdd4 : bv 32 := 0x00f6a223.
Lemma F_1cdd4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce74 : word) = Some W_1cdd4.
Proof. vm_refl. Qed.
Lemma D_1cdd4 : decode_any W_1cdd4 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdd8 : bv 32 := 0x00868693.
Lemma F_1cdd8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce78 : word) = Some W_1cdd8.
Proof. vm_refl. Qed.
Lemma D_1cdd8 : decode_any W_1cdd8 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cddc : bv 32 := 0x00858593.
Lemma F_1cddc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce7c : word) = Some W_1cddc.
Proof. vm_refl. Qed.
Lemma D_1cddc : decode_any W_1cddc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cde0 : bv 32 := 0x00467713.
Lemma F_1cde0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce80 : word) = Some W_1cde0.
Proof. vm_refl. Qed.
Lemma D_1cde0 : decode_any W_1cde0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cde4 : bv 32 := 0x24070063.
Lemma F_1cde4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce84 : word) = Some W_1cde4.
Proof. vm_refl. Qed.
Lemma D_1cde4 : decode_any W_1cde4 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cde8 : bv 32 := 0x0005a703.
Lemma F_1cde8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce88 : word) = Some W_1cde8.
Proof. vm_refl. Qed.
Lemma D_1cde8 : decode_any W_1cde8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdec : bv 32 := 0x00458593.
Lemma F_1cdec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce8c : word) = Some W_1cdec.
Proof. vm_refl. Qed.
Lemma D_1cdec : decode_any W_1cdec = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdf0 : bv 32 := 0x00e6a023.
Lemma F_1cdf0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce90 : word) = Some W_1cdf0.
Proof. vm_refl. Qed.
Lemma D_1cdf0 : decode_any W_1cdf0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdf4 : bv 32 := 0x00468693.
Lemma F_1cdf4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce94 : word) = Some W_1cdf4.
Proof. vm_refl. Qed.
Lemma D_1cdf4 : decode_any W_1cdf4 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdf8 : bv 32 := 0x22c0006f.
Lemma F_1cdf8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce98 : word) = Some W_1cdf8.
Proof. vm_refl. Qed.
Lemma D_1cdf8 : decode_any W_1cdf8 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cdfc : bv 32 := 0x00e68023.
Lemma F_1cdfc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ce9c : word) = Some W_1cdfc.
Proof. vm_refl. Qed.
Lemma D_1cdfc : decode_any W_1cdfc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce00 : bv 32 := 0x00168693.
Lemma F_1ce00 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cea0 : word) = Some W_1ce00.
Proof. vm_refl. Qed.
Lemma D_1ce00 : decode_any W_1ce00 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce04 : bv 32 := 0xfff60613.
Lemma F_1ce04 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cea4 : word) = Some W_1ce04.
Proof. vm_refl. Qed.
Lemma D_1ce04 : decode_any W_1ce04 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce08 : bv 32 := 0x01058593.
Lemma F_1ce08 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cea8 : word) = Some W_1ce08.
Proof. vm_refl. Qed.
Lemma D_1ce08 : decode_any W_1ce08 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce0c : bv 32 := 0x01200793.
Lemma F_1ce0c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ceac : word) = Some W_1ce0c.
Proof. vm_refl. Qed.
Lemma D_1ce0c : decode_any W_1ce0c = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce10 : bv 32 := 0x0087581b.
Lemma F_1ce10 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ceb0 : word) = Some W_1ce10.
Proof. vm_refl. Qed.
Lemma D_1ce10 : decode_any W_1ce10 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce14 : bv 32 := 0xff45a883.
Lemma F_1ce14 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ceb4 : word) = Some W_1ce14.
Proof. vm_refl. Qed.
Lemma D_1ce14 : decode_any W_1ce14 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce18 : bv 32 := 0xff85a283.
Lemma F_1ce18 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ceb8 : word) = Some W_1ce18.
Proof. vm_refl. Qed.
Lemma D_1ce18 : decode_any W_1ce18 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce1c : bv 32 := 0xffc5a303.
Lemma F_1ce1c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cebc : word) = Some W_1ce1c.
Proof. vm_refl. Qed.
Lemma D_1ce1c : decode_any W_1ce1c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce20 : bv 32 := 0x0005a703.
Lemma F_1ce20 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cec0 : word) = Some W_1ce20.
Proof. vm_refl. Qed.
Lemma D_1ce20 : decode_any W_1ce20 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce24 : bv 32 := 0x01889393.
Lemma F_1ce24 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cec4 : word) = Some W_1ce24.
Proof. vm_refl. Qed.
Lemma D_1ce24 : decode_any W_1ce24 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce28 : bv 32 := 0x0088d89b.
Lemma F_1ce28 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cec8 : word) = Some W_1ce28.
Proof. vm_refl. Qed.
Lemma D_1ce28 : decode_any W_1ce28 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce2c : bv 32 := 0x0103e833.
Lemma F_1ce2c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cecc : word) = Some W_1ce2c.
Proof. vm_refl. Qed.
Lemma D_1ce2c : decode_any W_1ce2c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce30 : bv 32 := 0x01829393.
Lemma F_1ce30 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ced0 : word) = Some W_1ce30.
Proof. vm_refl. Qed.
Lemma D_1ce30 : decode_any W_1ce30 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce34 : bv 32 := 0x0082d29b.
Lemma F_1ce34 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ced4 : word) = Some W_1ce34.
Proof. vm_refl. Qed.
Lemma D_1ce34 : decode_any W_1ce34 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce38 : bv 32 := 0x0113e8b3.
Lemma F_1ce38 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ced8 : word) = Some W_1ce38.
Proof. vm_refl. Qed.
Lemma D_1ce38 : decode_any W_1ce38 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce3c : bv 32 := 0x01831393.
Lemma F_1ce3c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cedc : word) = Some W_1ce3c.
Proof. vm_refl. Qed.
Lemma D_1ce3c : decode_any W_1ce3c = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce40 : bv 32 := 0x0083531b.
Lemma F_1ce40 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cee0 : word) = Some W_1ce40.
Proof. vm_refl. Qed.
Lemma D_1ce40 : decode_any W_1ce40 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce44 : bv 32 := 0x0053e2b3.
Lemma F_1ce44 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cee4 : word) = Some W_1ce44.
Proof. vm_refl. Qed.
Lemma D_1ce44 : decode_any W_1ce44 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce48 : bv 32 := 0x01871393.
Lemma F_1ce48 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cee8 : word) = Some W_1ce48.
Proof. vm_refl. Qed.
Lemma D_1ce48 : decode_any W_1ce48 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce4c : bv 32 := 0x0063e333.
Lemma F_1ce4c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1ceec : word) = Some W_1ce4c.
Proof. vm_refl. Qed.
Lemma D_1ce4c : decode_any W_1ce4c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce50 : bv 32 := 0xff060613.
Lemma F_1ce50 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cef0 : word) = Some W_1ce50.
Proof. vm_refl. Qed.
Lemma D_1ce50 : decode_any W_1ce50 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce54 : bv 32 := 0x0106a023.
Lemma F_1ce54 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cef4 : word) = Some W_1ce54.
Proof. vm_refl. Qed.
Lemma D_1ce54 : decode_any W_1ce54 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce58 : bv 32 := 0x0116a223.
Lemma F_1ce58 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cef8 : word) = Some W_1ce58.
Proof. vm_refl. Qed.
Lemma D_1ce58 : decode_any W_1ce58 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce5c : bv 32 := 0x0056a423.
Lemma F_1ce5c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cefc : word) = Some W_1ce5c.
Proof. vm_refl. Qed.
Lemma D_1ce5c : decode_any W_1ce5c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce60 : bv 32 := 0x0066a623.
Lemma F_1ce60 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf00 : word) = Some W_1ce60.
Proof. vm_refl. Qed.
Lemma D_1ce60 : decode_any W_1ce60 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce64 : bv 32 := 0x01068693.
Lemma F_1ce64 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf04 : word) = Some W_1ce64.
Proof. vm_refl. Qed.
Lemma D_1ce64 : decode_any W_1ce64 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce68 : bv 32 := 0x01058593.
Lemma F_1ce68 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf08 : word) = Some W_1ce68.
Proof. vm_refl. Qed.
Lemma D_1ce68 : decode_any W_1ce68 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce6c : bv 32 := 0xfac7e2e3.
Lemma F_1ce6c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf0c : word) = Some W_1ce6c.
Proof. vm_refl. Qed.
Lemma D_1ce6c : decode_any W_1ce6c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce70 : bv 32 := 0xff158593.
Lemma F_1ce70 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf10 : word) = Some W_1ce70.
Proof. vm_refl. Qed.
Lemma D_1ce70 : decode_any W_1ce70 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce74 : bv 32 := 0x01000713.
Lemma F_1ce74 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf14 : word) = Some W_1ce74.
Proof. vm_refl. Qed.
Lemma D_1ce74 : decode_any W_1ce74 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce78 : bv 32 := 0xe4e666e3.
Lemma F_1ce78 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf18 : word) = Some W_1ce78.
Proof. vm_refl. Qed.
Lemma D_1ce78 : decode_any W_1ce78 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce7c : bv 32 := 0x0940006f.
Lemma F_1ce7c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf1c : word) = Some W_1ce7c.
Proof. vm_refl. Qed.
Lemma D_1ce7c : decode_any W_1ce7c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce80 : bv 32 := 0x00875793.
Lemma F_1ce80 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf20 : word) = Some W_1ce80.
Proof. vm_refl. Qed.
Lemma D_1ce80 : decode_any W_1ce80 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce84 : bv 32 := 0x01075813.
Lemma F_1ce84 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf24 : word) = Some W_1ce84.
Proof. vm_refl. Qed.
Lemma D_1ce84 : decode_any W_1ce84 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce88 : bv 32 := 0xffd60613.
Lemma F_1ce88 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf28 : word) = Some W_1ce88.
Proof. vm_refl. Qed.
Lemma D_1ce88 : decode_any W_1ce88 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce8c : bv 32 := 0x00e68023.
Lemma F_1ce8c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf2c : word) = Some W_1ce8c.
Proof. vm_refl. Qed.
Lemma D_1ce8c : decode_any W_1ce8c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce90 : bv 32 := 0x00f680a3.
Lemma F_1ce90 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf30 : word) = Some W_1ce90.
Proof. vm_refl. Qed.
Lemma D_1ce90 : decode_any W_1ce90 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce94 : bv 32 := 0x01068123.
Lemma F_1ce94 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf34 : word) = Some W_1ce94.
Proof. vm_refl. Qed.
Lemma D_1ce94 : decode_any W_1ce94 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce98 : bv 32 := 0x00368693.
Lemma F_1ce98 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf38 : word) = Some W_1ce98.
Proof. vm_refl. Qed.
Lemma D_1ce98 : decode_any W_1ce98 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ce9c : bv 32 := 0x01058593.
Lemma F_1ce9c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf3c : word) = Some W_1ce9c.
Proof. vm_refl. Qed.
Lemma D_1ce9c : decode_any W_1ce9c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cea0 : bv 32 := 0x01000793.
Lemma F_1cea0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf40 : word) = Some W_1cea0.
Proof. vm_refl. Qed.
Lemma D_1cea0 : decode_any W_1cea0 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cea4 : bv 32 := 0x0187581b.
Lemma F_1cea4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf44 : word) = Some W_1cea4.
Proof. vm_refl. Qed.
Lemma D_1cea4 : decode_any W_1cea4 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cea8 : bv 32 := 0xff45a883.
Lemma F_1cea8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf48 : word) = Some W_1cea8.
Proof. vm_refl. Qed.
Lemma D_1cea8 : decode_any W_1cea8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ceac : bv 32 := 0xff85a283.
Lemma F_1ceac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf4c : word) = Some W_1ceac.
Proof. vm_refl. Qed.
Lemma D_1ceac : decode_any W_1ceac = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ceb0 : bv 32 := 0xffc5a303.
Lemma F_1ceb0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf50 : word) = Some W_1ceb0.
Proof. vm_refl. Qed.
Lemma D_1ceb0 : decode_any W_1ceb0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ceb4 : bv 32 := 0x0005a703.
Lemma F_1ceb4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf54 : word) = Some W_1ceb4.
Proof. vm_refl. Qed.
Lemma D_1ceb4 : decode_any W_1ceb4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ceb8 : bv 32 := 0x00889393.
Lemma F_1ceb8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf58 : word) = Some W_1ceb8.
Proof. vm_refl. Qed.
Lemma D_1ceb8 : decode_any W_1ceb8 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cebc : bv 32 := 0x0188d89b.
Lemma F_1cebc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf5c : word) = Some W_1cebc.
Proof. vm_refl. Qed.
Lemma D_1cebc : decode_any W_1cebc = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cec0 : bv 32 := 0x0103e833.
Lemma F_1cec0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf60 : word) = Some W_1cec0.
Proof. vm_refl. Qed.
Lemma D_1cec0 : decode_any W_1cec0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cec4 : bv 32 := 0x00829393.
Lemma F_1cec4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf64 : word) = Some W_1cec4.
Proof. vm_refl. Qed.
Lemma D_1cec4 : decode_any W_1cec4 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cec8 : bv 32 := 0x0182d29b.
Lemma F_1cec8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf68 : word) = Some W_1cec8.
Proof. vm_refl. Qed.
Lemma D_1cec8 : decode_any W_1cec8 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cecc : bv 32 := 0x0113e8b3.
Lemma F_1cecc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf6c : word) = Some W_1cecc.
Proof. vm_refl. Qed.
Lemma D_1cecc : decode_any W_1cecc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ced0 : bv 32 := 0x00831393.
Lemma F_1ced0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf70 : word) = Some W_1ced0.
Proof. vm_refl. Qed.
Lemma D_1ced0 : decode_any W_1ced0 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ced4 : bv 32 := 0x0183531b.
Lemma F_1ced4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf74 : word) = Some W_1ced4.
Proof. vm_refl. Qed.
Lemma D_1ced4 : decode_any W_1ced4 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ced8 : bv 32 := 0x0053e2b3.
Lemma F_1ced8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf78 : word) = Some W_1ced8.
Proof. vm_refl. Qed.
Lemma D_1ced8 : decode_any W_1ced8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cedc : bv 32 := 0x00871393.
Lemma F_1cedc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf7c : word) = Some W_1cedc.
Proof. vm_refl. Qed.
Lemma D_1cedc : decode_any W_1cedc = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cee0 : bv 32 := 0x0063e333.
Lemma F_1cee0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf80 : word) = Some W_1cee0.
Proof. vm_refl. Qed.
Lemma D_1cee0 : decode_any W_1cee0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cee4 : bv 32 := 0xff060613.
Lemma F_1cee4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf84 : word) = Some W_1cee4.
Proof. vm_refl. Qed.
Lemma D_1cee4 : decode_any W_1cee4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cee8 : bv 32 := 0x0106a023.
Lemma F_1cee8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf88 : word) = Some W_1cee8.
Proof. vm_refl. Qed.
Lemma D_1cee8 : decode_any W_1cee8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ceec : bv 32 := 0x0116a223.
Lemma F_1ceec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf8c : word) = Some W_1ceec.
Proof. vm_refl. Qed.
Lemma D_1ceec : decode_any W_1ceec = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cef0 : bv 32 := 0x0056a423.
Lemma F_1cef0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf90 : word) = Some W_1cef0.
Proof. vm_refl. Qed.
Lemma D_1cef0 : decode_any W_1cef0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cef4 : bv 32 := 0x0066a623.
Lemma F_1cef4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf94 : word) = Some W_1cef4.
Proof. vm_refl. Qed.
Lemma D_1cef4 : decode_any W_1cef4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cef8 : bv 32 := 0x01068693.
Lemma F_1cef8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf98 : word) = Some W_1cef8.
Proof. vm_refl. Qed.
Lemma D_1cef8 : decode_any W_1cef8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cefc : bv 32 := 0x01058593.
Lemma F_1cefc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cf9c : word) = Some W_1cefc.
Proof. vm_refl. Qed.
Lemma D_1cefc : decode_any W_1cefc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf00 : bv 32 := 0xfac7e2e3.
Lemma F_1cf00 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfa0 : word) = Some W_1cf00.
Proof. vm_refl. Qed.
Lemma D_1cf00 : decode_any W_1cf00 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf04 : bv 32 := 0xff358593.
Lemma F_1cf04 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfa4 : word) = Some W_1cf04.
Proof. vm_refl. Qed.
Lemma D_1cf04 : decode_any W_1cf04 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf08 : bv 32 := 0x01000713.
Lemma F_1cf08 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfa8 : word) = Some W_1cf08.
Proof. vm_refl. Qed.
Lemma D_1cf08 : decode_any W_1cf08 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf0c : bv 32 := 0xdae66ce3.
Lemma F_1cf0c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfac : word) = Some W_1cf0c.
Proof. vm_refl. Qed.
Lemma D_1cf0c : decode_any W_1cf0c = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf10 : bv 32 := 0x0005c703.
Lemma F_1cf10 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfb0 : word) = Some W_1cf10.
Proof. vm_refl. Qed.
Lemma D_1cf10 : decode_any W_1cf10 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf14 : bv 32 := 0x0015c783.
Lemma F_1cf14 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfb4 : word) = Some W_1cf14.
Proof. vm_refl. Qed.
Lemma D_1cf14 : decode_any W_1cf14 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf18 : bv 32 := 0x0025c803.
Lemma F_1cf18 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfb8 : word) = Some W_1cf18.
Proof. vm_refl. Qed.
Lemma D_1cf18 : decode_any W_1cf18 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf1c : bv 32 := 0x0035c883.
Lemma F_1cf1c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfbc : word) = Some W_1cf1c.
Proof. vm_refl. Qed.
Lemma D_1cf1c : decode_any W_1cf1c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf20 : bv 32 := 0x0045c283.
Lemma F_1cf20 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfc0 : word) = Some W_1cf20.
Proof. vm_refl. Qed.
Lemma D_1cf20 : decode_any W_1cf20 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf24 : bv 32 := 0x0055c303.
Lemma F_1cf24 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfc4 : word) = Some W_1cf24.
Proof. vm_refl. Qed.
Lemma D_1cf24 : decode_any W_1cf24 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf28 : bv 32 := 0x0065c383.
Lemma F_1cf28 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfc8 : word) = Some W_1cf28.
Proof. vm_refl. Qed.
Lemma D_1cf28 : decode_any W_1cf28 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf2c : bv 32 := 0x0075ce03.
Lemma F_1cf2c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfcc : word) = Some W_1cf2c.
Proof. vm_refl. Qed.
Lemma D_1cf2c : decode_any W_1cf2c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf30 : bv 32 := 0x00e68023.
Lemma F_1cf30 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfd0 : word) = Some W_1cf30.
Proof. vm_refl. Qed.
Lemma D_1cf30 : decode_any W_1cf30 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf34 : bv 32 := 0x00f680a3.
Lemma F_1cf34 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfd4 : word) = Some W_1cf34.
Proof. vm_refl. Qed.
Lemma D_1cf34 : decode_any W_1cf34 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf38 : bv 32 := 0x01068123.
Lemma F_1cf38 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfd8 : word) = Some W_1cf38.
Proof. vm_refl. Qed.
Lemma D_1cf38 : decode_any W_1cf38 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf3c : bv 32 := 0x011681a3.
Lemma F_1cf3c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfdc : word) = Some W_1cf3c.
Proof. vm_refl. Qed.
Lemma D_1cf3c : decode_any W_1cf3c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf40 : bv 32 := 0x0085c703.
Lemma F_1cf40 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfe0 : word) = Some W_1cf40.
Proof. vm_refl. Qed.
Lemma D_1cf40 : decode_any W_1cf40 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf44 : bv 32 := 0x0095c783.
Lemma F_1cf44 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfe4 : word) = Some W_1cf44.
Proof. vm_refl. Qed.
Lemma D_1cf44 : decode_any W_1cf44 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf48 : bv 32 := 0x00a5c803.
Lemma F_1cf48 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfe8 : word) = Some W_1cf48.
Proof. vm_refl. Qed.
Lemma D_1cf48 : decode_any W_1cf48 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf4c : bv 32 := 0x00b5c883.
Lemma F_1cf4c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cfec : word) = Some W_1cf4c.
Proof. vm_refl. Qed.
Lemma D_1cf4c : decode_any W_1cf4c = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf50 : bv 32 := 0x00568223.
Lemma F_1cf50 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cff0 : word) = Some W_1cf50.
Proof. vm_refl. Qed.
Lemma D_1cf50 : decode_any W_1cf50 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf54 : bv 32 := 0x006682a3.
Lemma F_1cf54 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cff4 : word) = Some W_1cf54.
Proof. vm_refl. Qed.
Lemma D_1cf54 : decode_any W_1cf54 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf58 : bv 32 := 0x00768323.
Lemma F_1cf58 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cff8 : word) = Some W_1cf58.
Proof. vm_refl. Qed.
Lemma D_1cf58 : decode_any W_1cf58 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf5c : bv 32 := 0x01c683a3.
Lemma F_1cf5c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1cffc : word) = Some W_1cf5c.
Proof. vm_refl. Qed.
Lemma D_1cf5c : decode_any W_1cf5c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf60 : bv 32 := 0x00c5c283.
Lemma F_1cf60 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d000 : word) = Some W_1cf60.
Proof. vm_refl. Qed.
Lemma D_1cf60 : decode_any W_1cf60 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf64 : bv 32 := 0x00d5c303.
Lemma F_1cf64 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d004 : word) = Some W_1cf64.
Proof. vm_refl. Qed.
Lemma D_1cf64 : decode_any W_1cf64 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf68 : bv 32 := 0x00e5c383.
Lemma F_1cf68 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d008 : word) = Some W_1cf68.
Proof. vm_refl. Qed.
Lemma D_1cf68 : decode_any W_1cf68 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf6c : bv 32 := 0x00f5ce03.
Lemma F_1cf6c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d00c : word) = Some W_1cf6c.
Proof. vm_refl. Qed.
Lemma D_1cf6c : decode_any W_1cf6c = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf70 : bv 32 := 0x01058593.
Lemma F_1cf70 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d010 : word) = Some W_1cf70.
Proof. vm_refl. Qed.
Lemma D_1cf70 : decode_any W_1cf70 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf74 : bv 32 := 0x00e68423.
Lemma F_1cf74 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d014 : word) = Some W_1cf74.
Proof. vm_refl. Qed.
Lemma D_1cf74 : decode_any W_1cf74 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf78 : bv 32 := 0x00f684a3.
Lemma F_1cf78 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d018 : word) = Some W_1cf78.
Proof. vm_refl. Qed.
Lemma D_1cf78 : decode_any W_1cf78 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf7c : bv 32 := 0x01068523.
Lemma F_1cf7c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d01c : word) = Some W_1cf7c.
Proof. vm_refl. Qed.
Lemma D_1cf7c : decode_any W_1cf7c = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf80 : bv 32 := 0x011685a3.
Lemma F_1cf80 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d020 : word) = Some W_1cf80.
Proof. vm_refl. Qed.
Lemma D_1cf80 : decode_any W_1cf80 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf84 : bv 32 := 0x01068713.
Lemma F_1cf84 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d024 : word) = Some W_1cf84.
Proof. vm_refl. Qed.
Lemma D_1cf84 : decode_any W_1cf84 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf88 : bv 32 := 0x00568623.
Lemma F_1cf88 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d028 : word) = Some W_1cf88.
Proof. vm_refl. Qed.
Lemma D_1cf88 : decode_any W_1cf88 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf8c : bv 32 := 0x006686a3.
Lemma F_1cf8c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d02c : word) = Some W_1cf8c.
Proof. vm_refl. Qed.
Lemma D_1cf8c : decode_any W_1cf8c = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf90 : bv 32 := 0x00768723.
Lemma F_1cf90 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d030 : word) = Some W_1cf90.
Proof. vm_refl. Qed.
Lemma D_1cf90 : decode_any W_1cf90 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf94 : bv 32 := 0x01c687a3.
Lemma F_1cf94 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d034 : word) = Some W_1cf94.
Proof. vm_refl. Qed.
Lemma D_1cf94 : decode_any W_1cf94 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf98 : bv 32 := 0x00070693.
Lemma F_1cf98 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d038 : word) = Some W_1cf98.
Proof. vm_refl. Qed.
Lemma D_1cf98 : decode_any W_1cf98 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf9c : bv 32 := 0x00867713.
Lemma F_1cf9c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d03c : word) = Some W_1cf9c.
Proof. vm_refl. Qed.
Lemma D_1cf9c : decode_any W_1cf9c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfa0 : bv 32 := 0xd20706e3.
Lemma F_1cfa0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d040 : word) = Some W_1cfa0.
Proof. vm_refl. Qed.
Lemma D_1cfa0 : decode_any W_1cfa0 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfa4 : bv 32 := 0x0005c703.
Lemma F_1cfa4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d044 : word) = Some W_1cfa4.
Proof. vm_refl. Qed.
Lemma D_1cfa4 : decode_any W_1cfa4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfa8 : bv 32 := 0x0015c783.
Lemma F_1cfa8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d048 : word) = Some W_1cfa8.
Proof. vm_refl. Qed.
Lemma D_1cfa8 : decode_any W_1cfa8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfac : bv 32 := 0x0025c803.
Lemma F_1cfac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d04c : word) = Some W_1cfac.
Proof. vm_refl. Qed.
Lemma D_1cfac : decode_any W_1cfac = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfb0 : bv 32 := 0x0035c883.
Lemma F_1cfb0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d050 : word) = Some W_1cfb0.
Proof. vm_refl. Qed.
Lemma D_1cfb0 : decode_any W_1cfb0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfb4 : bv 32 := 0x0045c283.
Lemma F_1cfb4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d054 : word) = Some W_1cfb4.
Proof. vm_refl. Qed.
Lemma D_1cfb4 : decode_any W_1cfb4 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfb8 : bv 32 := 0x0055c303.
Lemma F_1cfb8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d058 : word) = Some W_1cfb8.
Proof. vm_refl. Qed.
Lemma D_1cfb8 : decode_any W_1cfb8 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfbc : bv 32 := 0x0065c383.
Lemma F_1cfbc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d05c : word) = Some W_1cfbc.
Proof. vm_refl. Qed.
Lemma D_1cfbc : decode_any W_1cfbc = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfc0 : bv 32 := 0x0075ce03.
Lemma F_1cfc0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d060 : word) = Some W_1cfc0.
Proof. vm_refl. Qed.
Lemma D_1cfc0 : decode_any W_1cfc0 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfc4 : bv 32 := 0x00858593.
Lemma F_1cfc4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d064 : word) = Some W_1cfc4.
Proof. vm_refl. Qed.
Lemma D_1cfc4 : decode_any W_1cfc4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfc8 : bv 32 := 0x00e68023.
Lemma F_1cfc8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d068 : word) = Some W_1cfc8.
Proof. vm_refl. Qed.
Lemma D_1cfc8 : decode_any W_1cfc8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfcc : bv 32 := 0x00f680a3.
Lemma F_1cfcc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d06c : word) = Some W_1cfcc.
Proof. vm_refl. Qed.
Lemma D_1cfcc : decode_any W_1cfcc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfd0 : bv 32 := 0x01068123.
Lemma F_1cfd0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d070 : word) = Some W_1cfd0.
Proof. vm_refl. Qed.
Lemma D_1cfd0 : decode_any W_1cfd0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfd4 : bv 32 := 0x011681a3.
Lemma F_1cfd4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d074 : word) = Some W_1cfd4.
Proof. vm_refl. Qed.
Lemma D_1cfd4 : decode_any W_1cfd4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfd8 : bv 32 := 0x00868713.
Lemma F_1cfd8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d078 : word) = Some W_1cfd8.
Proof. vm_refl. Qed.
Lemma D_1cfd8 : decode_any W_1cfd8 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfdc : bv 32 := 0x00568223.
Lemma F_1cfdc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d07c : word) = Some W_1cfdc.
Proof. vm_refl. Qed.
Lemma D_1cfdc : decode_any W_1cfdc = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfe0 : bv 32 := 0x006682a3.
Lemma F_1cfe0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d080 : word) = Some W_1cfe0.
Proof. vm_refl. Qed.
Lemma D_1cfe0 : decode_any W_1cfe0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfe4 : bv 32 := 0x00768323.
Lemma F_1cfe4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d084 : word) = Some W_1cfe4.
Proof. vm_refl. Qed.
Lemma D_1cfe4 : decode_any W_1cfe4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfe8 : bv 32 := 0x01c683a3.
Lemma F_1cfe8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d088 : word) = Some W_1cfe8.
Proof. vm_refl. Qed.
Lemma D_1cfe8 : decode_any W_1cfe8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfec : bv 32 := 0x00070693.
Lemma F_1cfec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d08c : word) = Some W_1cfec.
Proof. vm_refl. Qed.
Lemma D_1cfec : decode_any W_1cfec = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cff0 : bv 32 := 0x00467713.
Lemma F_1cff0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d090 : word) = Some W_1cff0.
Proof. vm_refl. Qed.
Lemma D_1cff0 : decode_any W_1cff0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cff4 : bv 32 := 0x02070863.
Lemma F_1cff4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d094 : word) = Some W_1cff4.
Proof. vm_refl. Qed.
Lemma D_1cff4 : decode_any W_1cff4 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cff8 : bv 32 := 0x0005c703.
Lemma F_1cff8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d098 : word) = Some W_1cff8.
Proof. vm_refl. Qed.
Lemma D_1cff8 : decode_any W_1cff8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cffc : bv 32 := 0x0015c783.
Lemma F_1cffc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d09c : word) = Some W_1cffc.
Proof. vm_refl. Qed.
Lemma D_1cffc : decode_any W_1cffc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
