(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushU23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6e2a4 : bv 32 := 0x0035f713.
Lemma F_6e2a4 : fetch_word Ubsan.M.loaded_segments (0x6e2a4 : word) = Some W_6e2a4.
Proof. vm_refl. Qed.
Lemma D_6e2a4 : decode_any W_6e2a4 = Some (OpImm ALU_AND 14 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2a8 : bv 32 := 0x00058663.
Lemma F_6e2a8 : fetch_word Ubsan.M.loaded_segments (0x6e2a8 : word) = Some W_6e2a8.
Proof. vm_refl. Qed.
Lemma D_6e2a8 : decode_any W_6e2a8 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2ac : bv 32 := 0x0a071863.
Lemma F_6e2ac : fetch_word Ubsan.M.loaded_segments (0x6e2ac : word) = Some W_6e2ac.
Proof. vm_refl. Qed.
Lemma D_6e2ac : decode_any W_6e2ac = Some (Branch BC_NE 14 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2b0 : bv 32 := 0x0005a023.
Lemma F_6e2b0 : fetch_word Ubsan.M.loaded_segments (0x6e2b0 : word) = Some W_6e2b0.
Proof. vm_refl. Qed.
Lemma D_6e2b0 : decode_any W_6e2b0 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2b4 : bv 32 := 0x00367793.
Lemma F_6e2b4 : fetch_word Ubsan.M.loaded_segments (0x6e2b4 : word) = Some W_6e2b4.
Proof. vm_refl. Qed.
Lemma D_6e2b4 : decode_any W_6e2b4 = Some (OpImm ALU_AND 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2b8 : bv 32 := 0x00060663.
Lemma F_6e2b8 : fetch_word Ubsan.M.loaded_segments (0x6e2b8 : word) = Some W_6e2b8.
Proof. vm_refl. Qed.
Lemma D_6e2b8 : decode_any W_6e2b8 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2bc : bv 32 := 0x0a079063.
Lemma F_6e2bc : fetch_word Ubsan.M.loaded_segments (0x6e2bc : word) = Some W_6e2bc.
Proof. vm_refl. Qed.
Lemma D_6e2bc : decode_any W_6e2bc = Some (Branch BC_NE 15 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2c0 : bv 32 := 0x00062023.
Lemma F_6e2c0 : fetch_word Ubsan.M.loaded_segments (0x6e2c0 : word) = Some W_6e2c0.
Proof. vm_refl. Qed.
Lemma D_6e2c0 : decode_any W_6e2c0 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2c4 : bv 32 := 0x0036f813.
Lemma F_6e2c4 : fetch_word Ubsan.M.loaded_segments (0x6e2c4 : word) = Some W_6e2c4.
Proof. vm_refl. Qed.
Lemma D_6e2c4 : decode_any W_6e2c4 = Some (OpImm ALU_AND 16 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2c8 : bv 32 := 0x00068663.
Lemma F_6e2c8 : fetch_word Ubsan.M.loaded_segments (0x6e2c8 : word) = Some W_6e2c8.
Proof. vm_refl. Qed.
Lemma D_6e2c8 : decode_any W_6e2c8 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2cc : bv 32 := 0x08081863.
Lemma F_6e2cc : fetch_word Ubsan.M.loaded_segments (0x6e2cc : word) = Some W_6e2cc.
Proof. vm_refl. Qed.
Lemma D_6e2cc : decode_any W_6e2cc = Some (Branch BC_NE 16 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2d0 : bv 32 := 0x0006a023.
Lemma F_6e2d0 : fetch_word Ubsan.M.loaded_segments (0x6e2d0 : word) = Some W_6e2d0.
Proof. vm_refl. Qed.
Lemma D_6e2d0 : decode_any W_6e2d0 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2d4 : bv 32 := 0x04050663.
Lemma F_6e2d4 : fetch_word Ubsan.M.loaded_segments (0x6e2d4 : word) = Some W_6e2d4.
Proof. vm_refl. Qed.
Lemma D_6e2d4 : decode_any W_6e2d4 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2d8 : bv 32 := 0x00757893.
Lemma F_6e2d8 : fetch_word Ubsan.M.loaded_segments (0x6e2d8 : word) = Some W_6e2d8.
Proof. vm_refl. Qed.
Lemma D_6e2d8 : decode_any W_6e2d8 = Some (OpImm ALU_AND 17 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2dc : bv 32 := 0x00058a63.
Lemma F_6e2dc : fetch_word Ubsan.M.loaded_segments (0x6e2dc : word) = Some W_6e2dc.
Proof. vm_refl. Qed.
Lemma D_6e2dc : decode_any W_6e2dc = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2e0 : bv 32 := 0x00e8e733.
Lemma F_6e2e0 : fetch_word Ubsan.M.loaded_segments (0x6e2e0 : word) = Some W_6e2e0.
Proof. vm_refl. Qed.
Lemma D_6e2e0 : decode_any W_6e2e0 = Some (Op ALU_OR 14 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2e4 : bv 32 := 0x06071c63.
Lemma F_6e2e4 : fetch_word Ubsan.M.loaded_segments (0x6e2e4 : word) = Some W_6e2e4.
Proof. vm_refl. Qed.
Lemma D_6e2e4 : decode_any W_6e2e4 = Some (Branch BC_NE 14 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2e8 : bv 32 := 0x00052703.
Lemma F_6e2e8 : fetch_word Ubsan.M.loaded_segments (0x6e2e8 : word) = Some W_6e2e8.
Proof. vm_refl. Qed.
Lemma D_6e2e8 : decode_any W_6e2e8 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2ec : bv 32 := 0x00e5a023.
Lemma F_6e2ec : fetch_word Ubsan.M.loaded_segments (0x6e2ec : word) = Some W_6e2ec.
Proof. vm_refl. Qed.
Lemma D_6e2ec : decode_any W_6e2ec = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2f0 : bv 32 := 0x00060a63.
Lemma F_6e2f0 : fetch_word Ubsan.M.loaded_segments (0x6e2f0 : word) = Some W_6e2f0.
Proof. vm_refl. Qed.
Lemma D_6e2f0 : decode_any W_6e2f0 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2f4 : bv 32 := 0x00f8e5b3.
Lemma F_6e2f4 : fetch_word Ubsan.M.loaded_segments (0x6e2f4 : word) = Some W_6e2f4.
Proof. vm_refl. Qed.
Lemma D_6e2f4 : decode_any W_6e2f4 = Some (Op ALU_OR 11 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2f8 : bv 32 := 0x06059263.
Lemma F_6e2f8 : fetch_word Ubsan.M.loaded_segments (0x6e2f8 : word) = Some W_6e2f8.
Proof. vm_refl. Qed.
Lemma D_6e2f8 : decode_any W_6e2f8 = Some (Branch BC_NE 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2fc : bv 32 := 0x00452583.
Lemma F_6e2fc : fetch_word Ubsan.M.loaded_segments (0x6e2fc : word) = Some W_6e2fc.
Proof. vm_refl. Qed.
Lemma D_6e2fc : decode_any W_6e2fc = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e300 : bv 32 := 0x00b62023.
Lemma F_6e300 : fetch_word Ubsan.M.loaded_segments (0x6e300 : word) = Some W_6e300.
Proof. vm_refl. Qed.
Lemma D_6e300 : decode_any W_6e300 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e304 : bv 32 := 0x04068463.
Lemma F_6e304 : fetch_word Ubsan.M.loaded_segments (0x6e304 : word) = Some W_6e304.
Proof. vm_refl. Qed.
Lemma D_6e304 : decode_any W_6e304 = Some (Branch BC_EQ 13 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e308 : bv 32 := 0x0108e5b3.
Lemma F_6e308 : fetch_word Ubsan.M.loaded_segments (0x6e308 : word) = Some W_6e308.
Proof. vm_refl. Qed.
Lemma D_6e308 : decode_any W_6e308 = Some (Op ALU_OR 11 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e30c : bv 32 := 0x04059863.
Lemma F_6e30c : fetch_word Ubsan.M.loaded_segments (0x6e30c : word) = Some W_6e30c.
Proof. vm_refl. Qed.
Lemma D_6e30c : decode_any W_6e30c = Some (Branch BC_NE 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e310 : bv 32 := 0x00852503.
Lemma F_6e310 : fetch_word Ubsan.M.loaded_segments (0x6e310 : word) = Some W_6e310.
Proof. vm_refl. Qed.
Lemma D_6e310 : decode_any W_6e310 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e314 : bv 32 := 0x00a6a023.
Lemma F_6e314 : fetch_word Ubsan.M.loaded_segments (0x6e314 : word) = Some W_6e314.
Proof. vm_refl. Qed.
Lemma D_6e314 : decode_any W_6e314 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e318 : bv 32 := 0x00058513.
Lemma F_6e318 : fetch_word Ubsan.M.loaded_segments (0x6e318 : word) = Some W_6e318.
Proof. vm_refl. Qed.
Lemma D_6e318 : decode_any W_6e318 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e31c : bv 32 := 0x00008067.
Lemma F_6e31c : fetch_word Ubsan.M.loaded_segments (0x6e31c : word) = Some W_6e31c.
Proof. vm_refl. Qed.
Lemma D_6e31c : decode_any W_6e31c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f114 : bv 32 := 0x00050a63.
Lemma F_6f114 : fetch_word Ubsan.M.loaded_segments (0x6f114 : word) = Some W_6f114.
Proof. vm_refl. Qed.
Lemma D_6f114 : decode_any W_6f114 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f118 : bv 32 := 0x00757593.
Lemma F_6f118 : fetch_word Ubsan.M.loaded_segments (0x6f118 : word) = Some W_6f118.
Proof. vm_refl. Qed.
Lemma D_6f118 : decode_any W_6f118 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f11c : bv 32 := 0x04059063.
Lemma F_6f11c : fetch_word Ubsan.M.loaded_segments (0x6f11c : word) = Some W_6f11c.
Proof. vm_refl. Qed.
Lemma D_6f11c : decode_any W_6f11c = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f120 : bv 32 := 0x00852503.
Lemma F_6f120 : fetch_word Ubsan.M.loaded_segments (0x6f120 : word) = Some W_6f120.
Proof. vm_refl. Qed.
Lemma D_6f120 : decode_any W_6f120 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f124 : bv 32 := 0x00008067.
Lemma F_6f124 : fetch_word Ubsan.M.loaded_segments (0x6f124 : word) = Some W_6f124.
Proof. vm_refl. Qed.
Lemma D_6f124 : decode_any W_6f124 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ed8 : bv 32 := 0xf9010113.
Lemma F_70ed8 : fetch_word Ubsan.M.loaded_segments (0x70ed8 : word) = Some W_70ed8.
Proof. vm_refl. Qed.
Lemma D_70ed8 : decode_any W_70ed8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_70edc : bv 32 := 0x06113423.
Lemma F_70edc : fetch_word Ubsan.M.loaded_segments (0x70edc : word) = Some W_70edc.
Proof. vm_refl. Qed.
Lemma D_70edc : decode_any W_70edc = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ee0 : bv 32 := 0x06813023.
Lemma F_70ee0 : fetch_word Ubsan.M.loaded_segments (0x70ee0 : word) = Some W_70ee0.
Proof. vm_refl. Qed.
Lemma D_70ee0 : decode_any W_70ee0 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ee4 : bv 32 := 0x04913c23.
Lemma F_70ee4 : fetch_word Ubsan.M.loaded_segments (0x70ee4 : word) = Some W_70ee4.
Proof. vm_refl. Qed.
Lemma D_70ee4 : decode_any W_70ee4 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ee8 : bv 32 := 0x05213823.
Lemma F_70ee8 : fetch_word Ubsan.M.loaded_segments (0x70ee8 : word) = Some W_70ee8.
Proof. vm_refl. Qed.
Lemma D_70ee8 : decode_any W_70ee8 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_70eec : bv 32 := 0x05313423.
Lemma F_70eec : fetch_word Ubsan.M.loaded_segments (0x70eec : word) = Some W_70eec.
Proof. vm_refl. Qed.
Lemma D_70eec : decode_any W_70eec = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ef0 : bv 32 := 0x05413023.
Lemma F_70ef0 : fetch_word Ubsan.M.loaded_segments (0x70ef0 : word) = Some W_70ef0.
Proof. vm_refl. Qed.
Lemma D_70ef0 : decode_any W_70ef0 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ef4 : bv 32 := 0x03513c23.
Lemma F_70ef4 : fetch_word Ubsan.M.loaded_segments (0x70ef4 : word) = Some W_70ef4.
Proof. vm_refl. Qed.
Lemma D_70ef4 : decode_any W_70ef4 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ef8 : bv 32 := 0x03613823.
Lemma F_70ef8 : fetch_word Ubsan.M.loaded_segments (0x70ef8 : word) = Some W_70ef8.
Proof. vm_refl. Qed.
Lemma D_70ef8 : decode_any W_70ef8 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_70efc : bv 32 := 0x03713423.
Lemma F_70efc : fetch_word Ubsan.M.loaded_segments (0x70efc : word) = Some W_70efc.
Proof. vm_refl. Qed.
Lemma D_70efc : decode_any W_70efc = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f00 : bv 32 := 0x03813023.
Lemma F_70f00 : fetch_word Ubsan.M.loaded_segments (0x70f00 : word) = Some W_70f00.
Proof. vm_refl. Qed.
Lemma D_70f00 : decode_any W_70f00 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f04 : bv 32 := 0x0c050a63.
Lemma F_70f04 : fetch_word Ubsan.M.loaded_segments (0x70f04 : word) = Some W_70f04.
Proof. vm_refl. Qed.
Lemma D_70f04 : decode_any W_70f04 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f08 : bv 32 := 0x00070993.
Lemma F_70f08 : fetch_word Ubsan.M.loaded_segments (0x70f08 : word) = Some W_70f08.
Proof. vm_refl. Qed.
Lemma D_70f08 : decode_any W_70f08 = Some (OpImm ALU_ADD 19 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f0c : bv 32 := 0x00068493.
Lemma F_70f0c : fetch_word Ubsan.M.loaded_segments (0x70f0c : word) = Some W_70f0c.
Proof. vm_refl. Qed.
Lemma D_70f0c : decode_any W_70f0c = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f10 : bv 32 := 0x00060b13.
Lemma F_70f10 : fetch_word Ubsan.M.loaded_segments (0x70f10 : word) = Some W_70f10.
Proof. vm_refl. Qed.
Lemma D_70f10 : decode_any W_70f10 = Some (OpImm ALU_ADD 22 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f14 : bv 32 := 0x00058913.
Lemma F_70f14 : fetch_word Ubsan.M.loaded_segments (0x70f14 : word) = Some W_70f14.
Proof. vm_refl. Qed.
Lemma D_70f14 : decode_any W_70f14 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f18 : bv 32 := 0x00050413.
Lemma F_70f18 : fetch_word Ubsan.M.loaded_segments (0x70f18 : word) = Some W_70f18.
Proof. vm_refl. Qed.
Lemma D_70f18 : decode_any W_70f18 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f1c : bv 32 := 0x00b66533.
Lemma F_70f1c : fetch_word Ubsan.M.loaded_segments (0x70f1c : word) = Some W_70f1c.
Proof. vm_refl. Qed.
Lemma D_70f1c : decode_any W_70f1c = Some (Op ALU_OR 10 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f20 : bv 32 := 0x00e6e5b3.
Lemma F_70f20 : fetch_word Ubsan.M.loaded_segments (0x70f20 : word) = Some W_70f20.
Proof. vm_refl. Qed.
Lemma D_70f20 : decode_any W_70f20 = Some (Op ALU_OR 11 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f24 : bv 32 := 0x00b56533.
Lemma F_70f24 : fetch_word Ubsan.M.loaded_segments (0x70f24 : word) = Some W_70f24.
Proof. vm_refl. Qed.
Lemma D_70f24 : decode_any W_70f24 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f28 : bv 32 := 0x0c054c63.
Lemma F_70f28 : fetch_word Ubsan.M.loaded_segments (0x70f28 : word) = Some W_70f28.
Proof. vm_refl. Qed.
Lemma D_70f28 : decode_any W_70f28 = Some (Branch BC_LT 10 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f2c : bv 32 := 0x00078c13.
Lemma F_70f2c : fetch_word Ubsan.M.loaded_segments (0x70f2c : word) = Some W_70f2c.
Proof. vm_refl. Qed.
Lemma D_70f2c : decode_any W_70f2c = Some (OpImm ALU_ADD 24 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f30 : bv 32 := 0x01c10593.
Lemma F_70f30 : fetch_word Ubsan.M.loaded_segments (0x70f30 : word) = Some W_70f30.
Proof. vm_refl. Qed.
Lemma D_70f30 : decode_any W_70f30 = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f34 : bv 32 := 0x01810613.
Lemma F_70f34 : fetch_word Ubsan.M.loaded_segments (0x70f34 : word) = Some W_70f34.
Proof. vm_refl. Qed.
Lemma D_70f34 : decode_any W_70f34 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f38 : bv 32 := 0x01410693.
Lemma F_70f38 : fetch_word Ubsan.M.loaded_segments (0x70f38 : word) = Some W_70f38.
Proof. vm_refl. Qed.
Lemma D_70f38 : decode_any W_70f38 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f3c : bv 32 := 0x00040513.
Lemma F_70f3c : fetch_word Ubsan.M.loaded_segments (0x70f3c : word) = Some W_70f3c.
Proof. vm_refl. Qed.
Lemma D_70f3c : decode_any W_70f3c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f40 : bv 32 := 0xb64fd0ef.
Lemma F_70f40 : fetch_word Ubsan.M.loaded_segments (0x70f40 : word) = Some W_70f40.
Proof. vm_refl. Qed.
Lemma D_70f40 : decode_any W_70f40 = Some (Jal 1 2085732, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f44 : bv 32 := 0x01c12583.
Lemma F_70f44 : fetch_word Ubsan.M.loaded_segments (0x70f44 : word) = Some W_70f44.
Proof. vm_refl. Qed.
Lemma D_70f44 : decode_any W_70f44 = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f48 : bv 32 := 0x01258533.
Lemma F_70f48 : fetch_word Ubsan.M.loaded_segments (0x70f48 : word) = Some W_70f48.
Proof. vm_refl. Qed.
Lemma D_70f48 : decode_any W_70f48 = Some (Op ALU_ADD 10 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f4c : bv 32 := 0x012585bb.
Lemma F_70f4c : fetch_word Ubsan.M.loaded_segments (0x70f4c : word) = Some W_70f4c.
Proof. vm_refl. Qed.
Lemma D_70f4c : decode_any W_70f4c = Some (Op32 ALU_ADD 11 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f50 : bv 32 := 0x28a59063.
Lemma F_70f50 : fetch_word Ubsan.M.loaded_segments (0x70f50 : word) = Some W_70f50.
Proof. vm_refl. Qed.
Lemma D_70f50 : decode_any W_70f50 = Some (Branch BC_NE 11 10 640, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f54 : bv 32 := 0x0005051b.
Lemma F_70f54 : fetch_word Ubsan.M.loaded_segments (0x70f54 : word) = Some W_70f54.
Proof. vm_refl. Qed.
Lemma D_70f54 : decode_any W_70f54 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f58 : bv 32 := 0x01650abb.
Lemma F_70f58 : fetch_word Ubsan.M.loaded_segments (0x70f58 : word) = Some W_70f58.
Proof. vm_refl. Qed.
Lemma D_70f58 : decode_any W_70f58 = Some (Op32 ALU_ADD 21 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f5c : bv 32 := 0x01650533.
Lemma F_70f5c : fetch_word Ubsan.M.loaded_segments (0x70f5c : word) = Some W_70f5c.
Proof. vm_refl. Qed.
Lemma D_70f5c : decode_any W_70f5c = Some (Op ALU_ADD 10 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f60 : bv 32 := 0x26aa9863.
Lemma F_70f60 : fetch_word Ubsan.M.loaded_segments (0x70f60 : word) = Some W_70f60.
Proof. vm_refl. Qed.
Lemma D_70f60 : decode_any W_70f60 = Some (Branch BC_NE 21 10 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f64 : bv 32 := 0x01812583.
Lemma F_70f64 : fetch_word Ubsan.M.loaded_segments (0x70f64 : word) = Some W_70f64.
Proof. vm_refl. Qed.
Lemma D_70f64 : decode_any W_70f64 = Some (Load SZ4 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f68 : bv 32 := 0x00958533.
Lemma F_70f68 : fetch_word Ubsan.M.loaded_segments (0x70f68 : word) = Some W_70f68.
Proof. vm_refl. Qed.
Lemma D_70f68 : decode_any W_70f68 = Some (Op ALU_ADD 10 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f6c : bv 32 := 0x009585bb.
Lemma F_70f6c : fetch_word Ubsan.M.loaded_segments (0x70f6c : word) = Some W_70f6c.
Proof. vm_refl. Qed.
Lemma D_70f6c : decode_any W_70f6c = Some (Op32 ALU_ADD 11 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f70 : bv 32 := 0x26a59063.
Lemma F_70f70 : fetch_word Ubsan.M.loaded_segments (0x70f70 : word) = Some W_70f70.
Proof. vm_refl. Qed.
Lemma D_70f70 : decode_any W_70f70 = Some (Branch BC_NE 11 10 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f74 : bv 32 := 0x0005051b.
Lemma F_70f74 : fetch_word Ubsan.M.loaded_segments (0x70f74 : word) = Some W_70f74.
Proof. vm_refl. Qed.
Lemma D_70f74 : decode_any W_70f74 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f78 : bv 32 := 0x01350bbb.
Lemma F_70f78 : fetch_word Ubsan.M.loaded_segments (0x70f78 : word) = Some W_70f78.
Proof. vm_refl. Qed.
Lemma D_70f78 : decode_any W_70f78 = Some (Op32 ALU_ADD 23 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f7c : bv 32 := 0x01350533.
Lemma F_70f7c : fetch_word Ubsan.M.loaded_segments (0x70f7c : word) = Some W_70f7c.
Proof. vm_refl. Qed.
Lemma D_70f7c : decode_any W_70f7c = Some (Op ALU_ADD 10 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f80 : bv 32 := 0x24ab9863.
Lemma F_70f80 : fetch_word Ubsan.M.loaded_segments (0x70f80 : word) = Some W_70f80.
Proof. vm_refl. Qed.
Lemma D_70f80 : decode_any W_70f80 = Some (Branch BC_NE 23 10 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f84 : bv 32 := 0x01412603.
Lemma F_70f84 : fetch_word Ubsan.M.loaded_segments (0x70f84 : word) = Some W_70f84.
Proof. vm_refl. Qed.
Lemma D_70f84 : decode_any W_70f84 = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f88 : bv 32 := 0x000a8513.
Lemma F_70f88 : fetch_word Ubsan.M.loaded_segments (0x70f88 : word) = Some W_70f88.
Proof. vm_refl. Qed.
Lemma D_70f88 : decode_any W_70f88 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f8c : bv 32 := 0x000b8593.
Lemma F_70f8c : fetch_word Ubsan.M.loaded_segments (0x70f8c : word) = Some W_70f8c.
Proof. vm_refl. Qed.
Lemma D_70f8c : decode_any W_70f8c = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f90 : bv 32 := 0xaadfc0ef.
Lemma F_70f90 : fetch_word Ubsan.M.loaded_segments (0x70f90 : word) = Some W_70f90.
Proof. vm_refl. Qed.
Lemma D_70f90 : decode_any W_70f90 = Some (Jal 1 2083500, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f94 : bv 32 := 0x0c050263.
Lemma F_70f94 : fetch_word Ubsan.M.loaded_segments (0x70f94 : word) = Some W_70f94.
Proof. vm_refl. Qed.
Lemma D_70f94 : decode_any W_70f94 = Some (Branch BC_EQ 10 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f98 : bv 32 := 0x00050a13.
Lemma F_70f98 : fetch_word Ubsan.M.loaded_segments (0x70f98 : word) = Some W_70f98.
Proof. vm_refl. Qed.
Lemma D_70f98 : decode_any W_70f98 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f9c : bv 32 := 0x00040593.
Lemma F_70f9c : fetch_word Ubsan.M.loaded_segments (0x70f9c : word) = Some W_70f9c.
Proof. vm_refl. Qed.
Lemma D_70f9c : decode_any W_70f9c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fa0 : bv 32 := 0xc9cfd0ef.
Lemma F_70fa0 : fetch_word Ubsan.M.loaded_segments (0x70fa0 : word) = Some W_70fa0.
Proof. vm_refl. Qed.
Lemma D_70fa0 : decode_any W_70fa0 = Some (Jal 1 2086044, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fa4 : bv 32 := 0x000a0513.
Lemma F_70fa4 : fetch_word Ubsan.M.loaded_segments (0x70fa4 : word) = Some W_70fa4.
Proof. vm_refl. Qed.
Lemma D_70fa4 : decode_any W_70fa4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fa8 : bv 32 := 0x00040593.
Lemma F_70fa8 : fetch_word Ubsan.M.loaded_segments (0x70fa8 : word) = Some W_70fa8.
Proof. vm_refl. Qed.
Lemma D_70fa8 : decode_any W_70fa8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fac : bv 32 := 0xd20fd0ef.
Lemma F_70fac : fetch_word Ubsan.M.loaded_segments (0x70fac : word) = Some W_70fac.
Proof. vm_refl. Qed.
Lemma D_70fac : decode_any W_70fac = Some (Jal 1 2086176, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fb0 : bv 32 := 0x01412503.
Lemma F_70fb0 : fetch_word Ubsan.M.loaded_segments (0x70fb0 : word) = Some W_70fb0.
Proof. vm_refl. Qed.
Lemma D_70fb0 : decode_any W_70fb0 = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fb4 : bv 32 := 0x02000593.
Lemma F_70fb4 : fetch_word Ubsan.M.loaded_segments (0x70fb4 : word) = Some W_70fb4.
Proof. vm_refl. Qed.
Lemma D_70fb4 : decode_any W_70fb4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fb8 : bv 32 := 0x0cb51e63.
Lemma F_70fb8 : fetch_word Ubsan.M.loaded_segments (0x70fb8 : word) = Some W_70fb8.
Proof. vm_refl. Qed.
Lemma D_70fb8 : decode_any W_70fb8 = Some (Branch BC_NE 10 11 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fc8 : bv 32 := 0x0ea5f863.
Lemma F_70fc8 : fetch_word Ubsan.M.loaded_segments (0x70fc8 : word) = Some W_70fc8.
Proof. vm_refl. Qed.
Lemma D_70fc8 : decode_any W_70fc8 = Some (Branch BC_GEU 11 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_71058 : bv 32 := 0x000b6517.
Lemma F_71058 : fetch_word Ubsan.M.loaded_segments (0x71058 : word) = Some W_71058.
Proof. vm_refl. Qed.
Lemma D_71058 : decode_any W_71058 = Some (Auipc 10 182, 4%Z).
Proof. vm_refl. Qed.

Definition W_7105c : bv 32 := 0xa1853503.
Lemma F_7105c : fetch_word Ubsan.M.loaded_segments (0x7105c : word) = Some W_7105c.
Proof. vm_refl. Qed.
Lemma D_7105c : decode_any W_7105c = Some (Load SZ8 true 10 10 2584, 4%Z).
Proof. vm_refl. Qed.

Definition W_71060 : bv 32 := 0x00052503.
Lemma F_71060 : fetch_word Ubsan.M.loaded_segments (0x71060 : word) = Some W_71060.
Proof. vm_refl. Qed.
Lemma D_71060 : decode_any W_71060 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71064 : bv 32 := 0x00500593.
Lemma F_71064 : fetch_word Ubsan.M.loaded_segments (0x71064 : word) = Some W_71064.
Proof. vm_refl. Qed.
Lemma D_71064 : decode_any W_71064 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_71068 : bv 32 := 0x02a5c263.
Lemma F_71068 : fetch_word Ubsan.M.loaded_segments (0x71068 : word) = Some W_71068.
Proof. vm_refl. Qed.
Lemma D_71068 : decode_any W_71068 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_7106c : bv 32 := 0xfffa1517.
Lemma F_7106c : fetch_word Ubsan.M.loaded_segments (0x7106c : word) = Some W_7106c.
Proof. vm_refl. Qed.
Lemma D_7106c : decode_any W_7106c = Some (Auipc 10 1048481, 4%Z).
Proof. vm_refl. Qed.

Definition W_71070 : bv 32 := 0xfffa6597.
Lemma F_71070 : fetch_word Ubsan.M.loaded_segments (0x71070 : word) = Some W_71070.
Proof. vm_refl. Qed.
Lemma D_71070 : decode_any W_71070 = Some (Auipc 11 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_71074 : bv 32 := 0x66e50513.
Lemma F_71074 : fetch_word Ubsan.M.loaded_segments (0x71074 : word) = Some W_71074.
Proof. vm_refl. Qed.
Lemma D_71074 : decode_any W_71074 = Some (OpImm ALU_ADD 10 10 1646, 4%Z).
Proof. vm_refl. Qed.

Definition W_71078 : bv 32 := 0x0a658593.
Lemma F_71078 : fetch_word Ubsan.M.loaded_segments (0x71078 : word) = Some W_71078.
Proof. vm_refl. Qed.
Lemma D_71078 : decode_any W_71078 = Some (OpImm ALU_ADD 11 11 166, 4%Z).
Proof. vm_refl. Qed.

Definition W_7107c : bv 32 := 0x00000613.
Lemma F_7107c : fetch_word Ubsan.M.loaded_segments (0x7107c : word) = Some W_7107c.
Proof. vm_refl. Qed.
Lemma D_7107c : decode_any W_7107c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71080 : bv 32 := 0xec0f20ef.
Lemma F_71080 : fetch_word Ubsan.M.loaded_segments (0x71080 : word) = Some W_71080.
Proof. vm_refl. Qed.
Lemma D_71080 : decode_any W_71080 = Some (Jal 1 2041536, 4%Z).
Proof. vm_refl. Qed.

Definition W_71084 : bv 32 := 0x00050a13.
Lemma F_71084 : fetch_word Ubsan.M.loaded_segments (0x71084 : word) = Some W_71084.
Proof. vm_refl. Qed.
Lemma D_71084 : decode_any W_71084 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71088 : bv 32 := 0x1140006f.
Lemma F_71088 : fetch_word Ubsan.M.loaded_segments (0x71088 : word) = Some W_71088.
Proof. vm_refl. Qed.
Lemma D_71088 : decode_any W_71088 = Some (Jal 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_71094 : bv 32 := 0x01f00613.
Lemma F_71094 : fetch_word Ubsan.M.loaded_segments (0x71094 : word) = Some W_71094.
Proof. vm_refl. Qed.
Lemma D_71094 : decode_any W_71094 = Some (OpImm ALU_ADD 12 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_71098 : bv 32 := 0x12c57c63.
Lemma F_71098 : fetch_word Ubsan.M.loaded_segments (0x71098 : word) = Some W_71098.
Proof. vm_refl. Qed.
Lemma D_71098 : decode_any W_71098 = Some (Branch BC_GEU 10 12 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_7109c : bv 32 := 0x000c0593.
Lemma F_7109c : fetch_word Ubsan.M.loaded_segments (0x7109c : word) = Some W_7109c.
Proof. vm_refl. Qed.
Lemma D_7109c : decode_any W_7109c = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710a0 : bv 32 := 0xfff00613.
Lemma F_710a0 : fetch_word Ubsan.M.loaded_segments (0x710a0 : word) = Some W_710a0.
Proof. vm_refl. Qed.
Lemma D_710a0 : decode_any W_710a0 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_710a4 : bv 32 := 0x00a6153b.
Lemma F_710a4 : fetch_word Ubsan.M.loaded_segments (0x710a4 : word) = Some W_710a4.
Proof. vm_refl. Qed.
Lemma D_710a4 : decode_any W_710a4 = Some (Op32 ALU_SLL 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_710a8 : bv 32 := 0xfff54513.
Lemma F_710a8 : fetch_word Ubsan.M.loaded_segments (0x710a8 : word) = Some W_710a8.
Proof. vm_refl. Qed.
Lemma D_710a8 : decode_any W_710a8 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_710ac : bv 32 := 0xf00c1ee3.
Lemma F_710ac : fetch_word Ubsan.M.loaded_segments (0x710ac : word) = Some W_710ac.
Proof. vm_refl. Qed.
Lemma D_710ac : decode_any W_710ac = Some (Branch BC_NE 24 0 7964, 4%Z).
Proof. vm_refl. Qed.

Definition W_710b0 : bv 32 := 0x00000c13.
Lemma F_710b0 : fetch_word Ubsan.M.loaded_segments (0x710b0 : word) = Some W_710b0.
Proof. vm_refl. Qed.
Lemma D_710b0 : decode_any W_710b0 = Some (OpImm ALU_ADD 24 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710b4 : bv 32 := 0x0080006f.
Lemma F_710b4 : fetch_word Ubsan.M.loaded_segments (0x710b4 : word) = Some W_710b4.
Proof. vm_refl. Qed.
Lemma D_710b4 : decode_any W_710b4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_710b8 : bv 32 := 0x00f00c13.
Lemma F_710b8 : fetch_word Ubsan.M.loaded_segments (0x710b8 : word) = Some W_710b8.
Proof. vm_refl. Qed.
Lemma D_710b8 : decode_any W_710b8 = Some (OpImm ALU_ADD 24 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_710bc : bv 32 := 0x00013023.
Lemma F_710bc : fetch_word Ubsan.M.loaded_segments (0x710bc : word) = Some W_710bc.
Proof. vm_refl. Qed.
Lemma D_710bc : decode_any W_710bc = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710c0 : bv 32 := 0x000a0513.
Lemma F_710c0 : fetch_word Ubsan.M.loaded_segments (0x710c0 : word) = Some W_710c0.
Proof. vm_refl. Qed.
Lemma D_710c0 : decode_any W_710c0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710c4 : bv 32 := 0x00000593.
Lemma F_710c4 : fetch_word Ubsan.M.loaded_segments (0x710c4 : word) = Some W_710c4.
Proof. vm_refl. Qed.
Lemma D_710c4 : decode_any W_710c4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710c8 : bv 32 := 0x00000613.
Lemma F_710c8 : fetch_word Ubsan.M.loaded_segments (0x710c8 : word) = Some W_710c8.
Proof. vm_refl. Qed.
Lemma D_710c8 : decode_any W_710c8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710cc : bv 32 := 0x00090693.
Lemma F_710cc : fetch_word Ubsan.M.loaded_segments (0x710cc : word) = Some W_710cc.
Proof. vm_refl. Qed.
Lemma D_710cc : decode_any W_710cc = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710d0 : bv 32 := 0x000b8713.
Lemma F_710d0 : fetch_word Ubsan.M.loaded_segments (0x710d0 : word) = Some W_710d0.
Proof. vm_refl. Qed.
Lemma D_710d0 : decode_any W_710d0 = Some (OpImm ALU_ADD 14 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710d4 : bv 32 := 0x000c0793.
Lemma F_710d4 : fetch_word Ubsan.M.loaded_segments (0x710d4 : word) = Some W_710d4.
Proof. vm_refl. Qed.
Lemma D_710d4 : decode_any W_710d4 = Some (OpImm ALU_ADD 15 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710d8 : bv 32 := 0x00000813.
Lemma F_710d8 : fetch_word Ubsan.M.loaded_segments (0x710d8 : word) = Some W_710d8.
Proof. vm_refl. Qed.
Lemma D_710d8 : decode_any W_710d8 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710dc : bv 32 := 0x00000893.
Lemma F_710dc : fetch_word Ubsan.M.loaded_segments (0x710dc : word) = Some W_710dc.
Proof. vm_refl. Qed.
Lemma D_710dc : decode_any W_710dc = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710e0 : bv 32 := 0x05c0e0ef.
Lemma F_710e0 : fetch_word Ubsan.M.loaded_segments (0x710e0 : word) = Some W_710e0.
Proof. vm_refl. Qed.
Lemma D_710e0 : decode_any W_710e0 = Some (Jal 1 57436, 4%Z).
Proof. vm_refl. Qed.

Definition W_710e4 : bv 32 := 0x416a85b3.
Lemma F_710e4 : fetch_word Ubsan.M.loaded_segments (0x710e4 : word) = Some W_710e4.
Proof. vm_refl. Qed.
Lemma D_710e4 : decode_any W_710e4 = Some (Op ALU_SUB 11 21 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_710e8 : bv 32 := 0x416a853b.
Lemma F_710e8 : fetch_word Ubsan.M.loaded_segments (0x710e8 : word) = Some W_710e8.
Proof. vm_refl. Qed.
Lemma D_710e8 : decode_any W_710e8 = Some (Op32 ALU_SUB 10 21 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_710ec : bv 32 := 0x0eb51263.
Lemma F_710ec : fetch_word Ubsan.M.loaded_segments (0x710ec : word) = Some W_710ec.
Proof. vm_refl. Qed.
Lemma D_710ec : decode_any W_710ec = Some (Branch BC_NE 10 11 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_710f0 : bv 32 := 0x0005859b.
Lemma F_710f0 : fetch_word Ubsan.M.loaded_segments (0x710f0 : word) = Some W_710f0.
Proof. vm_refl. Qed.
Lemma D_710f0 : decode_any W_710f0 = Some (OpImm32 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710f4 : bv 32 := 0x00013023.
Lemma F_710f4 : fetch_word Ubsan.M.loaded_segments (0x710f4 : word) = Some W_710f4.
Proof. vm_refl. Qed.
Lemma D_710f4 : decode_any W_710f4 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710f8 : bv 32 := 0x000a0513.
Lemma F_710f8 : fetch_word Ubsan.M.loaded_segments (0x710f8 : word) = Some W_710f8.
Proof. vm_refl. Qed.
Lemma D_710f8 : decode_any W_710f8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_710fc : bv 32 := 0x00000613.
Lemma F_710fc : fetch_word Ubsan.M.loaded_segments (0x710fc : word) = Some W_710fc.
Proof. vm_refl. Qed.
Lemma D_710fc : decode_any W_710fc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71100 : bv 32 := 0x000b0693.
Lemma F_71100 : fetch_word Ubsan.M.loaded_segments (0x71100 : word) = Some W_71100.
Proof. vm_refl. Qed.
Lemma D_71100 : decode_any W_71100 = Some (OpImm ALU_ADD 13 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71104 : bv 32 := 0x000b8713.
Lemma F_71104 : fetch_word Ubsan.M.loaded_segments (0x71104 : word) = Some W_71104.
Proof. vm_refl. Qed.
Lemma D_71104 : decode_any W_71104 = Some (OpImm ALU_ADD 14 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71108 : bv 32 := 0x000c0793.
Lemma F_71108 : fetch_word Ubsan.M.loaded_segments (0x71108 : word) = Some W_71108.
Proof. vm_refl. Qed.
Lemma D_71108 : decode_any W_71108 = Some (OpImm ALU_ADD 15 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7110c : bv 32 := 0x00000813.
Lemma F_7110c : fetch_word Ubsan.M.loaded_segments (0x7110c : word) = Some W_7110c.
Proof. vm_refl. Qed.
Lemma D_7110c : decode_any W_7110c = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71110 : bv 32 := 0x00000893.
Lemma F_71110 : fetch_word Ubsan.M.loaded_segments (0x71110 : word) = Some W_71110.
Proof. vm_refl. Qed.
Lemma D_71110 : decode_any W_71110 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71114 : bv 32 := 0x0280e0ef.
Lemma F_71114 : fetch_word Ubsan.M.loaded_segments (0x71114 : word) = Some W_71114.
Proof. vm_refl. Qed.
Lemma D_71114 : decode_any W_71114 = Some (Jal 1 57384, 4%Z).
Proof. vm_refl. Qed.

Definition W_71118 : bv 32 := 0x00013023.
Lemma F_71118 : fetch_word Ubsan.M.loaded_segments (0x71118 : word) = Some W_71118.
Proof. vm_refl. Qed.
Lemma D_71118 : decode_any W_71118 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7111c : bv 32 := 0x000a0513.
Lemma F_7111c : fetch_word Ubsan.M.loaded_segments (0x7111c : word) = Some W_7111c.
Proof. vm_refl. Qed.
Lemma D_7111c : decode_any W_7111c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71120 : bv 32 := 0x00000593.
Lemma F_71120 : fetch_word Ubsan.M.loaded_segments (0x71120 : word) = Some W_71120.
Proof. vm_refl. Qed.
Lemma D_71120 : decode_any W_71120 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71124 : bv 32 := 0x00000613.
Lemma F_71124 : fetch_word Ubsan.M.loaded_segments (0x71124 : word) = Some W_71124.
Proof. vm_refl. Qed.
Lemma D_71124 : decode_any W_71124 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71128 : bv 32 := 0x000a8693.
Lemma F_71128 : fetch_word Ubsan.M.loaded_segments (0x71128 : word) = Some W_71128.
Proof. vm_refl. Qed.
Lemma D_71128 : decode_any W_71128 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7112c : bv 32 := 0x00048713.
Lemma F_7112c : fetch_word Ubsan.M.loaded_segments (0x7112c : word) = Some W_7112c.
Proof. vm_refl. Qed.
Lemma D_7112c : decode_any W_7112c = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71130 : bv 32 := 0x000c0793.
Lemma F_71130 : fetch_word Ubsan.M.loaded_segments (0x71130 : word) = Some W_71130.
Proof. vm_refl. Qed.
Lemma D_71130 : decode_any W_71130 = Some (OpImm ALU_ADD 15 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71134 : bv 32 := 0x00000813.
Lemma F_71134 : fetch_word Ubsan.M.loaded_segments (0x71134 : word) = Some W_71134.
Proof. vm_refl. Qed.
Lemma D_71134 : decode_any W_71134 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71138 : bv 32 := 0x00000893.
Lemma F_71138 : fetch_word Ubsan.M.loaded_segments (0x71138 : word) = Some W_71138.
Proof. vm_refl. Qed.
Lemma D_71138 : decode_any W_71138 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7113c : bv 32 := 0x0000e0ef.
Lemma F_7113c : fetch_word Ubsan.M.loaded_segments (0x7113c : word) = Some W_7113c.
Proof. vm_refl. Qed.
Lemma D_7113c : decode_any W_7113c = Some (Jal 1 57344, 4%Z).
Proof. vm_refl. Qed.

Definition W_71140 : bv 32 := 0x413b8633.
Lemma F_71140 : fetch_word Ubsan.M.loaded_segments (0x71140 : word) = Some W_71140.
Proof. vm_refl. Qed.
Lemma D_71140 : decode_any W_71140 = Some (Op ALU_SUB 12 23 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_71144 : bv 32 := 0x413b853b.
Lemma F_71144 : fetch_word Ubsan.M.loaded_segments (0x71144 : word) = Some W_71144.
Proof. vm_refl. Qed.
Lemma D_71144 : decode_any W_71144 = Some (Op32 ALU_SUB 10 23 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_71148 : bv 32 := 0x08c51463.
Lemma F_71148 : fetch_word Ubsan.M.loaded_segments (0x71148 : word) = Some W_71148.
Proof. vm_refl. Qed.
Lemma D_71148 : decode_any W_71148 = Some (Branch BC_NE 10 12 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_7114c : bv 32 := 0x0006061b.
Lemma F_7114c : fetch_word Ubsan.M.loaded_segments (0x7114c : word) = Some W_7114c.
Proof. vm_refl. Qed.
Lemma D_7114c : decode_any W_7114c = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71150 : bv 32 := 0x00013023.
Lemma F_71150 : fetch_word Ubsan.M.loaded_segments (0x71150 : word) = Some W_71150.
Proof. vm_refl. Qed.
Lemma D_71150 : decode_any W_71150 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71154 : bv 32 := 0x000a0513.
Lemma F_71154 : fetch_word Ubsan.M.loaded_segments (0x71154 : word) = Some W_71154.
Proof. vm_refl. Qed.
Lemma D_71154 : decode_any W_71154 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71158 : bv 32 := 0x00000593.
Lemma F_71158 : fetch_word Ubsan.M.loaded_segments (0x71158 : word) = Some W_71158.
Proof. vm_refl. Qed.
Lemma D_71158 : decode_any W_71158 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7115c : bv 32 := 0x000a8693.
Lemma F_7115c : fetch_word Ubsan.M.loaded_segments (0x7115c : word) = Some W_7115c.
Proof. vm_refl. Qed.
Lemma D_7115c : decode_any W_7115c = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71160 : bv 32 := 0x00098713.
Lemma F_71160 : fetch_word Ubsan.M.loaded_segments (0x71160 : word) = Some W_71160.
Proof. vm_refl. Qed.
Lemma D_71160 : decode_any W_71160 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71164 : bv 32 := 0x000c0793.
Lemma F_71164 : fetch_word Ubsan.M.loaded_segments (0x71164 : word) = Some W_71164.
Proof. vm_refl. Qed.
Lemma D_71164 : decode_any W_71164 = Some (OpImm ALU_ADD 15 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71168 : bv 32 := 0x00000813.
Lemma F_71168 : fetch_word Ubsan.M.loaded_segments (0x71168 : word) = Some W_71168.
Proof. vm_refl. Qed.
Lemma D_71168 : decode_any W_71168 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7116c : bv 32 := 0x00000893.
Lemma F_7116c : fetch_word Ubsan.M.loaded_segments (0x7116c : word) = Some W_7116c.
Proof. vm_refl. Qed.
Lemma D_7116c : decode_any W_7116c = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71170 : bv 32 := 0x7cd0d0ef.
Lemma F_71170 : fetch_word Ubsan.M.loaded_segments (0x71170 : word) = Some W_71170.
Proof. vm_refl. Qed.
Lemma D_71170 : decode_any W_71170 = Some (Jal 1 57292, 4%Z).
Proof. vm_refl. Qed.

Definition W_71174 : bv 32 := 0x01c12683.
Lemma F_71174 : fetch_word Ubsan.M.loaded_segments (0x71174 : word) = Some W_71174.
Proof. vm_refl. Qed.
Lemma D_71174 : decode_any W_71174 = Some (Load SZ4 true 13 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_71178 : bv 32 := 0x01812703.
Lemma F_71178 : fetch_word Ubsan.M.loaded_segments (0x71178 : word) = Some W_71178.
Proof. vm_refl. Qed.
Lemma D_71178 : decode_any W_71178 = Some (Load SZ4 true 14 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7117c : bv 32 := 0x00c00793.
Lemma F_7117c : fetch_word Ubsan.M.loaded_segments (0x7117c : word) = Some W_7117c.
Proof. vm_refl. Qed.
Lemma D_7117c : decode_any W_7117c = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71180 : bv 32 := 0x00013023.
Lemma F_71180 : fetch_word Ubsan.M.loaded_segments (0x71180 : word) = Some W_71180.
Proof. vm_refl. Qed.
Lemma D_71180 : decode_any W_71180 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71184 : bv 32 := 0x000a0513.
Lemma F_71184 : fetch_word Ubsan.M.loaded_segments (0x71184 : word) = Some W_71184.
Proof. vm_refl. Qed.
Lemma D_71184 : decode_any W_71184 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71188 : bv 32 := 0x00090593.
Lemma F_71188 : fetch_word Ubsan.M.loaded_segments (0x71188 : word) = Some W_71188.
Proof. vm_refl. Qed.
Lemma D_71188 : decode_any W_71188 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7118c : bv 32 := 0x00048613.
Lemma F_7118c : fetch_word Ubsan.M.loaded_segments (0x7118c : word) = Some W_7118c.
Proof. vm_refl. Qed.
Lemma D_7118c : decode_any W_7118c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71190 : bv 32 := 0x00040813.
Lemma F_71190 : fetch_word Ubsan.M.loaded_segments (0x71190 : word) = Some W_71190.
Proof. vm_refl. Qed.
Lemma D_71190 : decode_any W_71190 = Some (OpImm ALU_ADD 16 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71194 : bv 32 := 0x00000893.
Lemma F_71194 : fetch_word Ubsan.M.loaded_segments (0x71194 : word) = Some W_71194.
Proof. vm_refl. Qed.
Lemma D_71194 : decode_any W_71194 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71198 : bv 32 := 0x7a50d0ef.
Lemma F_71198 : fetch_word Ubsan.M.loaded_segments (0x71198 : word) = Some W_71198.
Proof. vm_refl. Qed.
Lemma D_71198 : decode_any W_71198 = Some (Jal 1 57252, 4%Z).
Proof. vm_refl. Qed.

Definition W_7119c : bv 32 := 0x000a0513.
Lemma F_7119c : fetch_word Ubsan.M.loaded_segments (0x7119c : word) = Some W_7119c.
Proof. vm_refl. Qed.
Lemma D_7119c : decode_any W_7119c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_711a0 : bv 32 := 0x06813083.
Lemma F_711a0 : fetch_word Ubsan.M.loaded_segments (0x711a0 : word) = Some W_711a0.
Proof. vm_refl. Qed.
Lemma D_711a0 : decode_any W_711a0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_711a4 : bv 32 := 0x06013403.
Lemma F_711a4 : fetch_word Ubsan.M.loaded_segments (0x711a4 : word) = Some W_711a4.
Proof. vm_refl. Qed.
Lemma D_711a4 : decode_any W_711a4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_711a8 : bv 32 := 0x05813483.
Lemma F_711a8 : fetch_word Ubsan.M.loaded_segments (0x711a8 : word) = Some W_711a8.
Proof. vm_refl. Qed.
Lemma D_711a8 : decode_any W_711a8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_711ac : bv 32 := 0x05013903.
Lemma F_711ac : fetch_word Ubsan.M.loaded_segments (0x711ac : word) = Some W_711ac.
Proof. vm_refl. Qed.
Lemma D_711ac : decode_any W_711ac = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_711b0 : bv 32 := 0x04813983.
Lemma F_711b0 : fetch_word Ubsan.M.loaded_segments (0x711b0 : word) = Some W_711b0.
Proof. vm_refl. Qed.
Lemma D_711b0 : decode_any W_711b0 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_711b4 : bv 32 := 0x04013a03.
Lemma F_711b4 : fetch_word Ubsan.M.loaded_segments (0x711b4 : word) = Some W_711b4.
Proof. vm_refl. Qed.
Lemma D_711b4 : decode_any W_711b4 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_711b8 : bv 32 := 0x03813a83.
Lemma F_711b8 : fetch_word Ubsan.M.loaded_segments (0x711b8 : word) = Some W_711b8.
Proof. vm_refl. Qed.
Lemma D_711b8 : decode_any W_711b8 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_711bc : bv 32 := 0x03013b03.
Lemma F_711bc : fetch_word Ubsan.M.loaded_segments (0x711bc : word) = Some W_711bc.
Proof. vm_refl. Qed.
Lemma D_711bc : decode_any W_711bc = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_711c0 : bv 32 := 0x02813b83.
Lemma F_711c0 : fetch_word Ubsan.M.loaded_segments (0x711c0 : word) = Some W_711c0.
Proof. vm_refl. Qed.
Lemma D_711c0 : decode_any W_711c0 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_711c4 : bv 32 := 0x02013c03.
Lemma F_711c4 : fetch_word Ubsan.M.loaded_segments (0x711c4 : word) = Some W_711c4.
Proof. vm_refl. Qed.
Lemma D_711c4 : decode_any W_711c4 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_711c8 : bv 32 := 0x07010113.
Lemma F_711c8 : fetch_word Ubsan.M.loaded_segments (0x711c8 : word) = Some W_711c8.
Proof. vm_refl. Qed.
Lemma D_711c8 : decode_any W_711c8 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_711cc : bv 32 := 0x00008067.
Lemma F_711cc : fetch_word Ubsan.M.loaded_segments (0x711cc : word) = Some W_711cc.
Proof. vm_refl. Qed.
Lemma D_711cc : decode_any W_711cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71224 : bv 32 := 0xfa010113.
Lemma F_71224 : fetch_word Ubsan.M.loaded_segments (0x71224 : word) = Some W_71224.
Proof. vm_refl. Qed.
Lemma D_71224 : decode_any W_71224 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_71228 : bv 32 := 0x04113c23.
Lemma F_71228 : fetch_word Ubsan.M.loaded_segments (0x71228 : word) = Some W_71228.
Proof. vm_refl. Qed.
Lemma D_71228 : decode_any W_71228 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7122c : bv 32 := 0x04813823.
Lemma F_7122c : fetch_word Ubsan.M.loaded_segments (0x7122c : word) = Some W_7122c.
Proof. vm_refl. Qed.
Lemma D_7122c : decode_any W_7122c = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_71230 : bv 32 := 0x04913423.
Lemma F_71230 : fetch_word Ubsan.M.loaded_segments (0x71230 : word) = Some W_71230.
Proof. vm_refl. Qed.
Lemma D_71230 : decode_any W_71230 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_71234 : bv 32 := 0x05213023.
Lemma F_71234 : fetch_word Ubsan.M.loaded_segments (0x71234 : word) = Some W_71234.
Proof. vm_refl. Qed.
Lemma D_71234 : decode_any W_71234 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_71238 : bv 32 := 0x03313c23.
Lemma F_71238 : fetch_word Ubsan.M.loaded_segments (0x71238 : word) = Some W_71238.
Proof. vm_refl. Qed.
Lemma D_71238 : decode_any W_71238 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7123c : bv 32 := 0x03413823.
Lemma F_7123c : fetch_word Ubsan.M.loaded_segments (0x7123c : word) = Some W_7123c.
Proof. vm_refl. Qed.
Lemma D_7123c : decode_any W_7123c = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_71240 : bv 32 := 0x03513423.
Lemma F_71240 : fetch_word Ubsan.M.loaded_segments (0x71240 : word) = Some W_71240.
Proof. vm_refl. Qed.
Lemma D_71240 : decode_any W_71240 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_71244 : bv 32 := 0x03713023.
Lemma F_71244 : fetch_word Ubsan.M.loaded_segments (0x71244 : word) = Some W_71244.
Proof. vm_refl. Qed.
Lemma D_71244 : decode_any W_71244 = Some (Store SZ8 2 23 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_71248 : bv 32 := 0x12050463.
Lemma F_71248 : fetch_word Ubsan.M.loaded_segments (0x71248 : word) = Some W_71248.
Proof. vm_refl. Qed.
Lemma D_71248 : decode_any W_71248 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_7124c : bv 32 := 0x00070a93.
Lemma F_7124c : fetch_word Ubsan.M.loaded_segments (0x7124c : word) = Some W_7124c.
Proof. vm_refl. Qed.
Lemma D_7124c : decode_any W_7124c = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71250 : bv 32 := 0x00068413.
Lemma F_71250 : fetch_word Ubsan.M.loaded_segments (0x71250 : word) = Some W_71250.
Proof. vm_refl. Qed.
Lemma D_71250 : decode_any W_71250 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71254 : bv 32 := 0x00060a13.
Lemma F_71254 : fetch_word Ubsan.M.loaded_segments (0x71254 : word) = Some W_71254.
Proof. vm_refl. Qed.
Lemma D_71254 : decode_any W_71254 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71258 : bv 32 := 0x00058493.
Lemma F_71258 : fetch_word Ubsan.M.loaded_segments (0x71258 : word) = Some W_71258.
Proof. vm_refl. Qed.
Lemma D_71258 : decode_any W_71258 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7125c : bv 32 := 0x00b665b3.
Lemma F_7125c : fetch_word Ubsan.M.loaded_segments (0x7125c : word) = Some W_7125c.
Proof. vm_refl. Qed.
Lemma D_7125c : decode_any W_7125c = Some (Op ALU_OR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_71260 : bv 32 := 0x00e6e633.
Lemma F_71260 : fetch_word Ubsan.M.loaded_segments (0x71260 : word) = Some W_71260.
Proof. vm_refl. Qed.
Lemma D_71260 : decode_any W_71260 = Some (Op ALU_OR 12 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_71264 : bv 32 := 0x00c5e5b3.
Lemma F_71264 : fetch_word Ubsan.M.loaded_segments (0x71264 : word) = Some W_71264.
Proof. vm_refl. Qed.
Lemma D_71264 : decode_any W_71264 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71268 : bv 32 := 0x1205c863.
Lemma F_71268 : fetch_word Ubsan.M.loaded_segments (0x71268 : word) = Some W_71268.
Proof. vm_refl. Qed.
Lemma D_71268 : decode_any W_71268 = Some (Branch BC_LT 11 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_7126c : bv 32 := 0x01c10593.
Lemma F_7126c : fetch_word Ubsan.M.loaded_segments (0x7126c : word) = Some W_7126c.
Proof. vm_refl. Qed.
Lemma D_7126c : decode_any W_7126c = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_71270 : bv 32 := 0x01810613.
Lemma F_71270 : fetch_word Ubsan.M.loaded_segments (0x71270 : word) = Some W_71270.
Proof. vm_refl. Qed.
Lemma D_71270 : decode_any W_71270 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_71274 : bv 32 := 0x01410693.
Lemma F_71274 : fetch_word Ubsan.M.loaded_segments (0x71274 : word) = Some W_71274.
Proof. vm_refl. Qed.
Lemma D_71274 : decode_any W_71274 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_71278 : bv 32 := 0x00050913.
Lemma F_71278 : fetch_word Ubsan.M.loaded_segments (0x71278 : word) = Some W_71278.
Proof. vm_refl. Qed.
Lemma D_71278 : decode_any W_71278 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7127c : bv 32 := 0x828fd0ef.
Lemma F_7127c : fetch_word Ubsan.M.loaded_segments (0x7127c : word) = Some W_7127c.
Proof. vm_refl. Qed.
Lemma D_7127c : decode_any W_7127c = Some (Jal 1 2084904, 4%Z).
Proof. vm_refl. Qed.

Definition W_71280 : bv 32 := 0x01c12583.
Lemma F_71280 : fetch_word Ubsan.M.loaded_segments (0x71280 : word) = Some W_71280.
Proof. vm_refl. Qed.
Lemma D_71280 : decode_any W_71280 = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_71284 : bv 32 := 0x40958533.
Lemma F_71284 : fetch_word Ubsan.M.loaded_segments (0x71284 : word) = Some W_71284.
Proof. vm_refl. Qed.
Lemma D_71284 : decode_any W_71284 = Some (Op ALU_SUB 10 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_71288 : bv 32 := 0x409585bb.
Lemma F_71288 : fetch_word Ubsan.M.loaded_segments (0x71288 : word) = Some W_71288.
Proof. vm_refl. Qed.
Lemma D_71288 : decode_any W_71288 = Some (Op32 ALU_SUB 11 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7128c : bv 32 := 0x20a59463.
Lemma F_7128c : fetch_word Ubsan.M.loaded_segments (0x7128c : word) = Some W_7128c.
Proof. vm_refl. Qed.
Lemma D_7128c : decode_any W_7128c = Some (Branch BC_NE 11 10 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_71290 : bv 32 := 0x0005051b.
Lemma F_71290 : fetch_word Ubsan.M.loaded_segments (0x71290 : word) = Some W_71290.
Proof. vm_refl. Qed.
Lemma D_71290 : decode_any W_71290 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71294 : bv 32 := 0x414509bb.
Lemma F_71294 : fetch_word Ubsan.M.loaded_segments (0x71294 : word) = Some W_71294.
Proof. vm_refl. Qed.
Lemma D_71294 : decode_any W_71294 = Some (Op32 ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_71298 : bv 32 := 0x41450533.
Lemma F_71298 : fetch_word Ubsan.M.loaded_segments (0x71298 : word) = Some W_71298.
Proof. vm_refl. Qed.
Lemma D_71298 : decode_any W_71298 = Some (Op ALU_SUB 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7129c : bv 32 := 0x1ea99c63.
Lemma F_7129c : fetch_word Ubsan.M.loaded_segments (0x7129c : word) = Some W_7129c.
Proof. vm_refl. Qed.
Lemma D_7129c : decode_any W_7129c = Some (Branch BC_NE 19 10 504, 4%Z).
Proof. vm_refl. Qed.

Definition W_712a0 : bv 32 := 0x01812583.
Lemma F_712a0 : fetch_word Ubsan.M.loaded_segments (0x712a0 : word) = Some W_712a0.
Proof. vm_refl. Qed.
Lemma D_712a0 : decode_any W_712a0 = Some (Load SZ4 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_712a4 : bv 32 := 0x40858533.
Lemma F_712a4 : fetch_word Ubsan.M.loaded_segments (0x712a4 : word) = Some W_712a4.
Proof. vm_refl. Qed.
Lemma D_712a4 : decode_any W_712a4 = Some (Op ALU_SUB 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_712a8 : bv 32 := 0x408585bb.
Lemma F_712a8 : fetch_word Ubsan.M.loaded_segments (0x712a8 : word) = Some W_712a8.
Proof. vm_refl. Qed.
Lemma D_712a8 : decode_any W_712a8 = Some (Op32 ALU_SUB 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_712ac : bv 32 := 0x1ea59463.
Lemma F_712ac : fetch_word Ubsan.M.loaded_segments (0x712ac : word) = Some W_712ac.
Proof. vm_refl. Qed.
Lemma D_712ac : decode_any W_712ac = Some (Branch BC_NE 11 10 488, 4%Z).
Proof. vm_refl. Qed.

Definition W_712b0 : bv 32 := 0x0005051b.
Lemma F_712b0 : fetch_word Ubsan.M.loaded_segments (0x712b0 : word) = Some W_712b0.
Proof. vm_refl. Qed.
Lemma D_712b0 : decode_any W_712b0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712b4 : bv 32 := 0x41550a3b.
Lemma F_712b4 : fetch_word Ubsan.M.loaded_segments (0x712b4 : word) = Some W_712b4.
Proof. vm_refl. Qed.
Lemma D_712b4 : decode_any W_712b4 = Some (Op32 ALU_SUB 20 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_712b8 : bv 32 := 0x41550533.
Lemma F_712b8 : fetch_word Ubsan.M.loaded_segments (0x712b8 : word) = Some W_712b8.
Proof. vm_refl. Qed.
Lemma D_712b8 : decode_any W_712b8 = Some (Op ALU_SUB 10 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_712bc : bv 32 := 0x1caa1c63.
Lemma F_712bc : fetch_word Ubsan.M.loaded_segments (0x712bc : word) = Some W_712bc.
Proof. vm_refl. Qed.
Lemma D_712bc : decode_any W_712bc = Some (Branch BC_NE 20 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_712c0 : bv 32 := 0x13305463.
Lemma F_712c0 : fetch_word Ubsan.M.loaded_segments (0x712c0 : word) = Some W_712c0.
Proof. vm_refl. Qed.
Lemma D_712c0 : decode_any W_712c0 = Some (Branch BC_GE 0 19 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_712c4 : bv 32 := 0x15405663.
Lemma F_712c4 : fetch_word Ubsan.M.loaded_segments (0x712c4 : word) = Some W_712c4.
Proof. vm_refl. Qed.
Lemma D_712c4 : decode_any W_712c4 = Some (Branch BC_GE 0 20 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_712c8 : bv 32 := 0x01412603.
Lemma F_712c8 : fetch_word Ubsan.M.loaded_segments (0x712c8 : word) = Some W_712c8.
Proof. vm_refl. Qed.
Lemma D_712c8 : decode_any W_712c8 = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_712cc : bv 32 := 0x00098513.
Lemma F_712cc : fetch_word Ubsan.M.loaded_segments (0x712cc : word) = Some W_712cc.
Proof. vm_refl. Qed.
Lemma D_712cc : decode_any W_712cc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712d0 : bv 32 := 0x000a0593.
Lemma F_712d0 : fetch_word Ubsan.M.loaded_segments (0x712d0 : word) = Some W_712d0.
Proof. vm_refl. Qed.
Lemma D_712d0 : decode_any W_712d0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712d4 : bv 32 := 0xf68fc0ef.
Lemma F_712d4 : fetch_word Ubsan.M.loaded_segments (0x712d4 : word) = Some W_712d4.
Proof. vm_refl. Qed.
Lemma D_712d4 : decode_any W_712d4 = Some (Jal 1 2082664, 4%Z).
Proof. vm_refl. Qed.

Definition W_712d8 : bv 32 := 0x16050063.
Lemma F_712d8 : fetch_word Ubsan.M.loaded_segments (0x712d8 : word) = Some W_712d8.
Proof. vm_refl. Qed.
Lemma D_712d8 : decode_any W_712d8 = Some (Branch BC_EQ 10 0 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_712dc : bv 32 := 0x00050a93.
Lemma F_712dc : fetch_word Ubsan.M.loaded_segments (0x712dc : word) = Some W_712dc.
Proof. vm_refl. Qed.
Lemma D_712dc : decode_any W_712dc = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712e0 : bv 32 := 0x00090593.
Lemma F_712e0 : fetch_word Ubsan.M.loaded_segments (0x712e0 : word) = Some W_712e0.
Proof. vm_refl. Qed.
Lemma D_712e0 : decode_any W_712e0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712e4 : bv 32 := 0x958fd0ef.
Lemma F_712e4 : fetch_word Ubsan.M.loaded_segments (0x712e4 : word) = Some W_712e4.
Proof. vm_refl. Qed.
Lemma D_712e4 : decode_any W_712e4 = Some (Jal 1 2085208, 4%Z).
Proof. vm_refl. Qed.

Definition W_712e8 : bv 32 := 0x000a8513.
Lemma F_712e8 : fetch_word Ubsan.M.loaded_segments (0x712e8 : word) = Some W_712e8.
Proof. vm_refl. Qed.
Lemma D_712e8 : decode_any W_712e8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712ec : bv 32 := 0x00090593.
Lemma F_712ec : fetch_word Ubsan.M.loaded_segments (0x712ec : word) = Some W_712ec.
Proof. vm_refl. Qed.
Lemma D_712ec : decode_any W_712ec = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712f0 : bv 32 := 0x870fd0ef.
Lemma F_712f0 : fetch_word Ubsan.M.loaded_segments (0x712f0 : word) = Some W_712f0.
Proof. vm_refl. Qed.
Lemma D_712f0 : decode_any W_712f0 = Some (Jal 1 2084976, 4%Z).
Proof. vm_refl. Qed.

Definition W_712f4 : bv 32 := 0x000a8513.
Lemma F_712f4 : fetch_word Ubsan.M.loaded_segments (0x712f4 : word) = Some W_712f4.
Proof. vm_refl. Qed.
Lemma D_712f4 : decode_any W_712f4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712f8 : bv 32 := 0x00090593.
Lemma F_712f8 : fetch_word Ubsan.M.loaded_segments (0x712f8 : word) = Some W_712f8.
Proof. vm_refl. Qed.
Lemma D_712f8 : decode_any W_712f8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712fc : bv 32 := 0x9d0fd0ef.
Lemma F_712fc : fetch_word Ubsan.M.loaded_segments (0x712fc : word) = Some W_712fc.
Proof. vm_refl. Qed.
Lemma D_712fc : decode_any W_712fc = Some (Jal 1 2085328, 4%Z).
Proof. vm_refl. Qed.

Definition W_71300 : bv 32 := 0x00c00793.
Lemma F_71300 : fetch_word Ubsan.M.loaded_segments (0x71300 : word) = Some W_71300.
Proof. vm_refl. Qed.
Lemma D_71300 : decode_any W_71300 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71304 : bv 32 := 0x00813023.
Lemma F_71304 : fetch_word Ubsan.M.loaded_segments (0x71304 : word) = Some W_71304.
Proof. vm_refl. Qed.
Lemma D_71304 : decode_any W_71304 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71308 : bv 32 := 0x000a8b93.
Lemma F_71308 : fetch_word Ubsan.M.loaded_segments (0x71308 : word) = Some W_71308.
Proof. vm_refl. Qed.
Lemma D_71308 : decode_any W_71308 = Some (OpImm ALU_ADD 23 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7130c : bv 32 := 0x000a8513.
Lemma F_7130c : fetch_word Ubsan.M.loaded_segments (0x7130c : word) = Some W_7130c.
Proof. vm_refl. Qed.
Lemma D_7130c : decode_any W_7130c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71310 : bv 32 := 0x00000593.
Lemma F_71310 : fetch_word Ubsan.M.loaded_segments (0x71310 : word) = Some W_71310.
Proof. vm_refl. Qed.
Lemma D_71310 : decode_any W_71310 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71314 : bv 32 := 0x00000613.
Lemma F_71314 : fetch_word Ubsan.M.loaded_segments (0x71314 : word) = Some W_71314.
Proof. vm_refl. Qed.
Lemma D_71314 : decode_any W_71314 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71318 : bv 32 := 0x00098693.
Lemma F_71318 : fetch_word Ubsan.M.loaded_segments (0x71318 : word) = Some W_71318.
Proof. vm_refl. Qed.
Lemma D_71318 : decode_any W_71318 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7131c : bv 32 := 0x000a0713.
Lemma F_7131c : fetch_word Ubsan.M.loaded_segments (0x7131c : word) = Some W_7131c.
Proof. vm_refl. Qed.
Lemma D_7131c : decode_any W_7131c = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71320 : bv 32 := 0x00090813.
Lemma F_71320 : fetch_word Ubsan.M.loaded_segments (0x71320 : word) = Some W_71320.
Proof. vm_refl. Qed.
Lemma D_71320 : decode_any W_71320 = Some (OpImm ALU_ADD 16 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71324 : bv 32 := 0x00048893.
Lemma F_71324 : fetch_word Ubsan.M.loaded_segments (0x71324 : word) = Some W_71324.
Proof. vm_refl. Qed.
Lemma D_71324 : decode_any W_71324 = Some (OpImm ALU_ADD 17 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71328 : bv 32 := 0x6150d0ef.
Lemma F_71328 : fetch_word Ubsan.M.loaded_segments (0x71328 : word) = Some W_71328.
Proof. vm_refl. Qed.
Lemma D_71328 : decode_any W_71328 = Some (Jal 1 56852, 4%Z).
Proof. vm_refl. Qed.

Definition W_7132c : bv 32 := 0x00090513.
Lemma F_7132c : fetch_word Ubsan.M.loaded_segments (0x7132c : word) = Some W_7132c.
Proof. vm_refl. Qed.
Lemma D_7132c : decode_any W_7132c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71330 : bv 32 := 0xde5fd0ef.
Lemma F_71330 : fetch_word Ubsan.M.loaded_segments (0x71330 : word) = Some W_71330.
Proof. vm_refl. Qed.
Lemma D_71330 : decode_any W_71330 = Some (Jal 1 2088420, 4%Z).
Proof. vm_refl. Qed.

Definition W_71334 : bv 32 := 0x02000593.
Lemma F_71334 : fetch_word Ubsan.M.loaded_segments (0x71334 : word) = Some W_71334.
Proof. vm_refl. Qed.
Lemma D_71334 : decode_any W_71334 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_71338 : bv 32 := 0x02b51863.
Lemma F_71338 : fetch_word Ubsan.M.loaded_segments (0x71338 : word) = Some W_71338.
Proof. vm_refl. Qed.
Lemma D_71338 : decode_any W_71338 = Some (Branch BC_NE 10 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_71368 : bv 32 := 0x000b8513.
Lemma F_71368 : fetch_word Ubsan.M.loaded_segments (0x71368 : word) = Some W_71368.
Proof. vm_refl. Qed.
Lemma D_71368 : decode_any W_71368 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7136c : bv 32 := 0x1000006f.
Lemma F_7136c : fetch_word Ubsan.M.loaded_segments (0x7136c : word) = Some W_7136c.
Proof. vm_refl. Qed.
Lemma D_7136c : decode_any W_7136c = Some (Jal 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_71370 : bv 32 := 0x000b5517.
Lemma F_71370 : fetch_word Ubsan.M.loaded_segments (0x71370 : word) = Some W_71370.
Proof. vm_refl. Qed.
Lemma D_71370 : decode_any W_71370 = Some (Auipc 10 181, 4%Z).
Proof. vm_refl. Qed.

Definition W_71374 : bv 32 := 0x70053503.
Lemma F_71374 : fetch_word Ubsan.M.loaded_segments (0x71374 : word) = Some W_71374.
Proof. vm_refl. Qed.
Lemma D_71374 : decode_any W_71374 = Some (Load SZ8 true 10 10 1792, 4%Z).
Proof. vm_refl. Qed.

Definition W_71378 : bv 32 := 0x00052503.
Lemma F_71378 : fetch_word Ubsan.M.loaded_segments (0x71378 : word) = Some W_71378.
Proof. vm_refl. Qed.
Lemma D_71378 : decode_any W_71378 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7137c : bv 32 := 0x00500593.
Lemma F_7137c : fetch_word Ubsan.M.loaded_segments (0x7137c : word) = Some W_7137c.
Proof. vm_refl. Qed.
Lemma D_7137c : decode_any W_7137c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_71380 : bv 32 := 0x0ea5c463.
Lemma F_71380 : fetch_word Ubsan.M.loaded_segments (0x71380 : word) = Some W_71380.
Proof. vm_refl. Qed.
Lemma D_71380 : decode_any W_71380 = Some (Branch BC_LT 11 10 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_71384 : bv 32 := 0xfff9f517.
Lemma F_71384 : fetch_word Ubsan.M.loaded_segments (0x71384 : word) = Some W_71384.
Proof. vm_refl. Qed.
Lemma D_71384 : decode_any W_71384 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_71388 : bv 32 := 0xfffa7597.
Lemma F_71388 : fetch_word Ubsan.M.loaded_segments (0x71388 : word) = Some W_71388.
Proof. vm_refl. Qed.
Lemma D_71388 : decode_any W_71388 = Some (Auipc 11 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_7138c : bv 32 := 0xfd150513.
Lemma F_7138c : fetch_word Ubsan.M.loaded_segments (0x7138c : word) = Some W_7138c.
Proof. vm_refl. Qed.
Lemma D_7138c : decode_any W_7138c = Some (OpImm ALU_ADD 10 10 4049, 4%Z).
Proof. vm_refl. Qed.

Definition W_71390 : bv 32 := 0x07458593.
Lemma F_71390 : fetch_word Ubsan.M.loaded_segments (0x71390 : word) = Some W_71390.
Proof. vm_refl. Qed.
Lemma D_71390 : decode_any W_71390 = Some (OpImm ALU_ADD 11 11 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_71394 : bv 32 := 0x0280006f.
Lemma F_71394 : fetch_word Ubsan.M.loaded_segments (0x71394 : word) = Some W_71394.
Proof. vm_refl. Qed.
Lemma D_71394 : decode_any W_71394 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_713bc : bv 32 := 0x00000613.
Lemma F_713bc : fetch_word Ubsan.M.loaded_segments (0x713bc : word) = Some W_713bc.
Proof. vm_refl. Qed.
Lemma D_713bc : decode_any W_713bc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_713c0 : bv 32 := 0x05813083.
Lemma F_713c0 : fetch_word Ubsan.M.loaded_segments (0x713c0 : word) = Some W_713c0.
Proof. vm_refl. Qed.
Lemma D_713c0 : decode_any W_713c0 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_713c4 : bv 32 := 0x05013403.
Lemma F_713c4 : fetch_word Ubsan.M.loaded_segments (0x713c4 : word) = Some W_713c4.
Proof. vm_refl. Qed.
Lemma D_713c4 : decode_any W_713c4 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_713c8 : bv 32 := 0x04813483.
Lemma F_713c8 : fetch_word Ubsan.M.loaded_segments (0x713c8 : word) = Some W_713c8.
Proof. vm_refl. Qed.
Lemma D_713c8 : decode_any W_713c8 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_713cc : bv 32 := 0x04013903.
Lemma F_713cc : fetch_word Ubsan.M.loaded_segments (0x713cc : word) = Some W_713cc.
Proof. vm_refl. Qed.
Lemma D_713cc : decode_any W_713cc = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_713d0 : bv 32 := 0x03813983.
Lemma F_713d0 : fetch_word Ubsan.M.loaded_segments (0x713d0 : word) = Some W_713d0.
Proof. vm_refl. Qed.
Lemma D_713d0 : decode_any W_713d0 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_713d4 : bv 32 := 0x03013a03.
Lemma F_713d4 : fetch_word Ubsan.M.loaded_segments (0x713d4 : word) = Some W_713d4.
Proof. vm_refl. Qed.
Lemma D_713d4 : decode_any W_713d4 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_713d8 : bv 32 := 0x02813a83.
Lemma F_713d8 : fetch_word Ubsan.M.loaded_segments (0x713d8 : word) = Some W_713d8.
Proof. vm_refl. Qed.
Lemma D_713d8 : decode_any W_713d8 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_713dc : bv 32 := 0x02013b83.
Lemma F_713dc : fetch_word Ubsan.M.loaded_segments (0x713dc : word) = Some W_713dc.
Proof. vm_refl. Qed.
Lemma D_713dc : decode_any W_713dc = Some (Load SZ8 true 23 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_713e0 : bv 32 := 0x06010113.
Lemma F_713e0 : fetch_word Ubsan.M.loaded_segments (0x713e0 : word) = Some W_713e0.
Proof. vm_refl. Qed.
Lemma D_713e0 : decode_any W_713e0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_713e4 : bv 32 := 0xb5cf206f.
Lemma F_713e4 : fetch_word Ubsan.M.loaded_segments (0x713e4 : word) = Some W_713e4.
Proof. vm_refl. Qed.
Lemma D_713e4 : decode_any W_713e4 = Some (Jal 0 2040668, 4%Z).
Proof. vm_refl. Qed.

Definition W_71438 : bv 32 := 0x000b5517.
Lemma F_71438 : fetch_word Ubsan.M.loaded_segments (0x71438 : word) = Some W_71438.
Proof. vm_refl. Qed.
Lemma D_71438 : decode_any W_71438 = Some (Auipc 10 181, 4%Z).
Proof. vm_refl. Qed.

Definition W_7143c : bv 32 := 0x63853503.
Lemma F_7143c : fetch_word Ubsan.M.loaded_segments (0x7143c : word) = Some W_7143c.
Proof. vm_refl. Qed.
Lemma D_7143c : decode_any W_7143c = Some (Load SZ8 true 10 10 1592, 4%Z).
Proof. vm_refl. Qed.

Definition W_71440 : bv 32 := 0x00052503.
Lemma F_71440 : fetch_word Ubsan.M.loaded_segments (0x71440 : word) = Some W_71440.
Proof. vm_refl. Qed.
Lemma D_71440 : decode_any W_71440 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71444 : bv 32 := 0x00500593.
Lemma F_71444 : fetch_word Ubsan.M.loaded_segments (0x71444 : word) = Some W_71444.
Proof. vm_refl. Qed.
Lemma D_71444 : decode_any W_71444 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_71448 : bv 32 := 0x02a5c063.
Lemma F_71448 : fetch_word Ubsan.M.loaded_segments (0x71448 : word) = Some W_71448.
Proof. vm_refl. Qed.
Lemma D_71448 : decode_any W_71448 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7144c : bv 32 := 0xfffa1517.
Lemma F_7144c : fetch_word Ubsan.M.loaded_segments (0x7144c : word) = Some W_7144c.
Proof. vm_refl. Qed.
Lemma D_7144c : decode_any W_7144c = Some (Auipc 10 1048481, 4%Z).
Proof. vm_refl. Qed.

Definition W_71450 : bv 32 := 0xfffa7597.
Lemma F_71450 : fetch_word Ubsan.M.loaded_segments (0x71450 : word) = Some W_71450.
Proof. vm_refl. Qed.
Lemma D_71450 : decode_any W_71450 = Some (Auipc 11 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_71454 : bv 32 := 0x28e50513.
Lemma F_71454 : fetch_word Ubsan.M.loaded_segments (0x71454 : word) = Some W_71454.
Proof. vm_refl. Qed.
Lemma D_71454 : decode_any W_71454 = Some (OpImm ALU_ADD 10 10 654, 4%Z).
Proof. vm_refl. Qed.

Definition W_71458 : bv 32 := 0xfac58593.
Lemma F_71458 : fetch_word Ubsan.M.loaded_segments (0x71458 : word) = Some W_71458.
Proof. vm_refl. Qed.
Lemma D_71458 : decode_any W_71458 = Some (OpImm ALU_ADD 11 11 4012, 4%Z).
Proof. vm_refl. Qed.

Definition W_7145c : bv 32 := 0x00000613.
Lemma F_7145c : fetch_word Ubsan.M.loaded_segments (0x7145c : word) = Some W_7145c.
Proof. vm_refl. Qed.
Lemma D_7145c : decode_any W_7145c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71460 : bv 32 := 0xae0f20ef.
Lemma F_71460 : fetch_word Ubsan.M.loaded_segments (0x71460 : word) = Some W_71460.
Proof. vm_refl. Qed.
Lemma D_71460 : decode_any W_71460 = Some (Jal 1 2040544, 4%Z).
Proof. vm_refl. Qed.

Definition W_71464 : bv 32 := 0x0080006f.
Lemma F_71464 : fetch_word Ubsan.M.loaded_segments (0x71464 : word) = Some W_71464.
Proof. vm_refl. Qed.
Lemma D_71464 : decode_any W_71464 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7146c : bv 32 := 0x05813083.
Lemma F_7146c : fetch_word Ubsan.M.loaded_segments (0x7146c : word) = Some W_7146c.
Proof. vm_refl. Qed.
Lemma D_7146c : decode_any W_7146c = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_71470 : bv 32 := 0x05013403.
Lemma F_71470 : fetch_word Ubsan.M.loaded_segments (0x71470 : word) = Some W_71470.
Proof. vm_refl. Qed.
Lemma D_71470 : decode_any W_71470 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_71474 : bv 32 := 0x04813483.
Lemma F_71474 : fetch_word Ubsan.M.loaded_segments (0x71474 : word) = Some W_71474.
Proof. vm_refl. Qed.
Lemma D_71474 : decode_any W_71474 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_71478 : bv 32 := 0x04013903.
Lemma F_71478 : fetch_word Ubsan.M.loaded_segments (0x71478 : word) = Some W_71478.
Proof. vm_refl. Qed.
Lemma D_71478 : decode_any W_71478 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7147c : bv 32 := 0x03813983.
Lemma F_7147c : fetch_word Ubsan.M.loaded_segments (0x7147c : word) = Some W_7147c.
Proof. vm_refl. Qed.
Lemma D_7147c : decode_any W_7147c = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_71480 : bv 32 := 0x03013a03.
Lemma F_71480 : fetch_word Ubsan.M.loaded_segments (0x71480 : word) = Some W_71480.
Proof. vm_refl. Qed.
Lemma D_71480 : decode_any W_71480 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_71484 : bv 32 := 0x02813a83.
Lemma F_71484 : fetch_word Ubsan.M.loaded_segments (0x71484 : word) = Some W_71484.
Proof. vm_refl. Qed.
Lemma D_71484 : decode_any W_71484 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_71488 : bv 32 := 0x02013b83.
Lemma F_71488 : fetch_word Ubsan.M.loaded_segments (0x71488 : word) = Some W_71488.
Proof. vm_refl. Qed.
Lemma D_71488 : decode_any W_71488 = Some (Load SZ8 true 23 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7148c : bv 32 := 0x06010113.
Lemma F_7148c : fetch_word Ubsan.M.loaded_segments (0x7148c : word) = Some W_7148c.
Proof. vm_refl. Qed.
Lemma D_7148c : decode_any W_7148c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_71490 : bv 32 := 0x00008067.
Lemma F_71490 : fetch_word Ubsan.M.loaded_segments (0x71490 : word) = Some W_71490.
Proof. vm_refl. Qed.
Lemma D_71490 : decode_any W_71490 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
