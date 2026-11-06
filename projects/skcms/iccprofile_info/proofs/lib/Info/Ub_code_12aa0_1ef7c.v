(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
Unset Nia Cache.
Unset Lia Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_12aa0 : bv 32 := 0x0040006f.
Lemma F_12aa0 : fetch_word Ubsan.M.loaded_segments (0x12aa0 : word) = Some W_12aa0.
Proof. vm_refl. Qed.
Lemma D_12aa0 : decode_any W_12aa0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_12aa4 : bv 32 := 0x0000e517.
Lemma F_12aa4 : fetch_word Ubsan.M.loaded_segments (0x12aa4 : word) = Some W_12aa4.
Proof. vm_refl. Qed.
Lemma D_12aa4 : decode_any W_12aa4 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_12aa8 : bv 32 := 0x6cc50513.
Lemma F_12aa8 : fetch_word Ubsan.M.loaded_segments (0x12aa8 : word) = Some W_12aa8.
Proof. vm_refl. Qed.
Lemma D_12aa8 : decode_any W_12aa8 = Some (OpImm ALU_ADD 10 10 1740, 4%Z).
Proof. vm_refl. Qed.

Definition W_12aac : bv 32 := 0x00053503.
Lemma F_12aac : fetch_word Ubsan.M.loaded_segments (0x12aac : word) = Some W_12aac.
Proof. vm_refl. Qed.
Lemma D_12aac : decode_any W_12aac = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ab0 : bv 32 := 0x191040ef.
Lemma F_12ab0 : fetch_word Ubsan.M.loaded_segments (0x12ab0 : word) = Some W_12ab0.
Proof. vm_refl. Qed.
Lemma D_12ab0 : decode_any W_12ab0 = Some (Jal 1 18832, 4%Z).
Proof. vm_refl. Qed.

Definition W_12ab4 : bv 32 := 0x0040006f.
Lemma F_12ab4 : fetch_word Ubsan.M.loaded_segments (0x12ab4 : word) = Some W_12ab4.
Proof. vm_refl. Qed.
Lemma D_12ab4 : decode_any W_12ab4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_12f10 : bv 32 := 0x0001e517.
Lemma F_12f10 : fetch_word Ubsan.M.loaded_segments (0x12f10 : word) = Some W_12f10.
Proof. vm_refl. Qed.
Lemma D_12f10 : decode_any W_12f10 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_12f14 : bv 32 := 0x4c454503.
Lemma F_12f14 : fetch_word Ubsan.M.loaded_segments (0x12f14 : word) = Some W_12f14.
Proof. vm_refl. Qed.
Lemma D_12f14 : decode_any W_12f14 = Some (Load SZ1 false 10 10 1220, 4%Z).
Proof. vm_refl. Qed.

Definition W_12f18 : bv 32 := 0x00051463.
Lemma F_12f18 : fetch_word Ubsan.M.loaded_segments (0x12f18 : word) = Some W_12f18.
Proof. vm_refl. Qed.
Lemma D_12f18 : decode_any W_12f18 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12f1c : bv 32 := 0x00008067.
Lemma F_12f1c : fetch_word Ubsan.M.loaded_segments (0x12f1c : word) = Some W_12f1c.
Proof. vm_refl. Qed.
Lemma D_12f1c : decode_any W_12f1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17378 : bv 32 := 0xfd010113.
Lemma F_17378 : fetch_word Ubsan.M.loaded_segments (0x17378 : word) = Some W_17378.
Proof. vm_refl. Qed.
Lemma D_17378 : decode_any W_17378 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_1737c : bv 32 := 0x02113423.
Lemma F_1737c : fetch_word Ubsan.M.loaded_segments (0x1737c : word) = Some W_1737c.
Proof. vm_refl. Qed.
Lemma D_1737c : decode_any W_1737c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17380 : bv 32 := 0x02813023.
Lemma F_17380 : fetch_word Ubsan.M.loaded_segments (0x17380 : word) = Some W_17380.
Proof. vm_refl. Qed.
Lemma D_17380 : decode_any W_17380 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17384 : bv 32 := 0x00913c23.
Lemma F_17384 : fetch_word Ubsan.M.loaded_segments (0x17384 : word) = Some W_17384.
Proof. vm_refl. Qed.
Lemma D_17384 : decode_any W_17384 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17388 : bv 32 := 0x01213823.
Lemma F_17388 : fetch_word Ubsan.M.loaded_segments (0x17388 : word) = Some W_17388.
Proof. vm_refl. Qed.
Lemma D_17388 : decode_any W_17388 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1738c : bv 32 := 0x01313423.
Lemma F_1738c : fetch_word Ubsan.M.loaded_segments (0x1738c : word) = Some W_1738c.
Proof. vm_refl. Qed.
Lemma D_1738c : decode_any W_1738c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17390 : bv 32 := 0x0003a517.
Lemma F_17390 : fetch_word Ubsan.M.loaded_segments (0x17390 : word) = Some W_17390.
Proof. vm_refl. Qed.
Lemma D_17390 : decode_any W_17390 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17394 : bv 32 := 0x19050913.
Lemma F_17394 : fetch_word Ubsan.M.loaded_segments (0x17394 : word) = Some W_17394.
Proof. vm_refl. Qed.
Lemma D_17394 : decode_any W_17394 = Some (OpImm ALU_ADD 18 10 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_17398 : bv 32 := 0x00490413.
Lemma F_17398 : fetch_word Ubsan.M.loaded_segments (0x17398 : word) = Some W_17398.
Proof. vm_refl. Qed.
Lemma D_17398 : decode_any W_17398 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1739c : bv 32 := 0x00040513.
Lemma F_1739c : fetch_word Ubsan.M.loaded_segments (0x1739c : word) = Some W_1739c.
Proof. vm_refl. Qed.
Lemma D_1739c : decode_any W_1739c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_173a0 : bv 32 := 0x149070ef.
Lemma F_173a0 : fetch_word Ubsan.M.loaded_segments (0x173a0 : word) = Some W_173a0.
Proof. vm_refl. Qed.
Lemma D_173a0 : decode_any W_173a0 = Some (Jal 1 31048, 4%Z).
Proof. vm_refl. Qed.

Definition W_173a4 : bv 32 := 0x01093503.
Lemma F_173a4 : fetch_word Ubsan.M.loaded_segments (0x173a4 : word) = Some W_173a4.
Proof. vm_refl. Qed.
Lemma D_173a4 : decode_any W_173a4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_173a8 : bv 32 := 0x06050863.
Lemma F_173a8 : fetch_word Ubsan.M.loaded_segments (0x173a8 : word) = Some W_173a8.
Proof. vm_refl. Qed.
Lemma D_173a8 : decode_any W_173a8 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_173ac : bv 32 := 0x00892583.
Lemma F_173ac : fetch_word Ubsan.M.loaded_segments (0x173ac : word) = Some W_173ac.
Proof. vm_refl. Qed.
Lemma D_173ac : decode_any W_173ac = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_173b0 : bv 32 := 0x0180006f.
Lemma F_173b0 : fetch_word Ubsan.M.loaded_segments (0x173b0 : word) = Some W_173b0.
Proof. vm_refl. Qed.
Lemma D_173b0 : decode_any W_173b0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_173b4 : bv 32 := 0x00053503.
Lemma F_173b4 : fetch_word Ubsan.M.loaded_segments (0x173b4 : word) = Some W_173b4.
Proof. vm_refl. Qed.
Lemma D_173b4 : decode_any W_173b4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_173b8 : bv 32 := 0x02000593.
Lemma F_173b8 : fetch_word Ubsan.M.loaded_segments (0x173b8 : word) = Some W_173b8.
Proof. vm_refl. Qed.
Lemma D_173b8 : decode_any W_173b8 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_173bc : bv 32 := 0x00b92423.
Lemma F_173bc : fetch_word Ubsan.M.loaded_segments (0x173bc : word) = Some W_173bc.
Proof. vm_refl. Qed.
Lemma D_173bc : decode_any W_173bc = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_173c0 : bv 32 := 0x00a93823.
Lemma F_173c0 : fetch_word Ubsan.M.loaded_segments (0x173c0 : word) = Some W_173c0.
Proof. vm_refl. Qed.
Lemma D_173c0 : decode_any W_173c0 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_173c4 : bv 32 := 0x04050a63.
Lemma F_173c4 : fetch_word Ubsan.M.loaded_segments (0x173c4 : word) = Some W_173c4.
Proof. vm_refl. Qed.
Lemma D_173c4 : decode_any W_173c4 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_173c8 : bv 32 := 0xfff5861b.
Lemma F_173c8 : fetch_word Ubsan.M.loaded_segments (0x173c8 : word) = Some W_173c8.
Proof. vm_refl. Qed.
Lemma D_173c8 : decode_any W_173c8 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_173cc : bv 32 := 0x00c92423.
Lemma F_173cc : fetch_word Ubsan.M.loaded_segments (0x173cc : word) = Some W_173cc.
Proof. vm_refl. Qed.
Lemma D_173cc : decode_any W_173cc = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_173d0 : bv 32 := 0xfeb052e3.
Lemma F_173d0 : fetch_word Ubsan.M.loaded_segments (0x173d0 : word) = Some W_173d0.
Proof. vm_refl. Qed.
Lemma D_173d0 : decode_any W_173d0 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_173d4 : bv 32 := 0x01093503.
Lemma F_173d4 : fetch_word Ubsan.M.loaded_segments (0x173d4 : word) = Some W_173d4.
Proof. vm_refl. Qed.
Lemma D_173d4 : decode_any W_173d4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_173d8 : bv 32 := 0x00361613.
Lemma F_173d8 : fetch_word Ubsan.M.loaded_segments (0x173d8 : word) = Some W_173d8.
Proof. vm_refl. Qed.
Lemma D_173d8 : decode_any W_173d8 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_173dc : bv 32 := 0x00c50533.
Lemma F_173dc : fetch_word Ubsan.M.loaded_segments (0x173dc : word) = Some W_173dc.
Proof. vm_refl. Qed.
Lemma D_173dc : decode_any W_173dc = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_173e0 : bv 32 := 0x00853983.
Lemma F_173e0 : fetch_word Ubsan.M.loaded_segments (0x173e0 : word) = Some W_173e0.
Proof. vm_refl. Qed.
Lemma D_173e0 : decode_any W_173e0 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_173e4 : bv 32 := 0x10853483.
Lemma F_173e4 : fetch_word Ubsan.M.loaded_segments (0x173e4 : word) = Some W_173e4.
Proof. vm_refl. Qed.
Lemma D_173e4 : decode_any W_173e4 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_173e8 : bv 32 := 0x00040513.
Lemma F_173e8 : fetch_word Ubsan.M.loaded_segments (0x173e8 : word) = Some W_173e8.
Proof. vm_refl. Qed.
Lemma D_173e8 : decode_any W_173e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_173ec : bv 32 := 0x385070ef.
Lemma F_173ec : fetch_word Ubsan.M.loaded_segments (0x173ec : word) = Some W_173ec.
Proof. vm_refl. Qed.
Lemma D_173ec : decode_any W_173ec = Some (Jal 1 31620, 4%Z).
Proof. vm_refl. Qed.

Definition W_173f0 : bv 32 := 0x00048513.
Lemma F_173f0 : fetch_word Ubsan.M.loaded_segments (0x173f0 : word) = Some W_173f0.
Proof. vm_refl. Qed.
Lemma D_173f0 : decode_any W_173f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_173f4 : bv 32 := 0x000980e7.
Lemma F_173f4 : fetch_word Ubsan.M.loaded_segments (0x173f4 : word) = Some W_173f4.
Proof. vm_refl. Qed.
Lemma D_173f4 : decode_any W_173f4 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_173f8 : bv 32 := 0x00040513.
Lemma F_173f8 : fetch_word Ubsan.M.loaded_segments (0x173f8 : word) = Some W_173f8.
Proof. vm_refl. Qed.
Lemma D_173f8 : decode_any W_173f8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_173fc : bv 32 := 0x0ed070ef.
Lemma F_173fc : fetch_word Ubsan.M.loaded_segments (0x173fc : word) = Some W_173fc.
Proof. vm_refl. Qed.
Lemma D_173fc : decode_any W_173fc = Some (Jal 1 30956, 4%Z).
Proof. vm_refl. Qed.

Definition W_17400 : bv 32 := 0x00892503.
Lemma F_17400 : fetch_word Ubsan.M.loaded_segments (0x17400 : word) = Some W_17400.
Proof. vm_refl. Qed.
Lemma D_17400 : decode_any W_17400 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17404 : bv 32 := 0xfff5061b.
Lemma F_17404 : fetch_word Ubsan.M.loaded_segments (0x17404 : word) = Some W_17404.
Proof. vm_refl. Qed.
Lemma D_17404 : decode_any W_17404 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17408 : bv 32 := 0x00c92423.
Lemma F_17408 : fetch_word Ubsan.M.loaded_segments (0x17408 : word) = Some W_17408.
Proof. vm_refl. Qed.
Lemma D_17408 : decode_any W_17408 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1740c : bv 32 := 0xfca044e3.
Lemma F_1740c : fetch_word Ubsan.M.loaded_segments (0x1740c : word) = Some W_1740c.
Proof. vm_refl. Qed.
Lemma D_1740c : decode_any W_1740c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_17410 : bv 32 := 0x01093503.
Lemma F_17410 : fetch_word Ubsan.M.loaded_segments (0x17410 : word) = Some W_17410.
Proof. vm_refl. Qed.
Lemma D_17410 : decode_any W_17410 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17414 : bv 32 := 0xfa1ff06f.
Lemma F_17414 : fetch_word Ubsan.M.loaded_segments (0x17414 : word) = Some W_17414.
Proof. vm_refl. Qed.
Lemma D_17414 : decode_any W_17414 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_17418 : bv 32 := 0x00100513.
Lemma F_17418 : fetch_word Ubsan.M.loaded_segments (0x17418 : word) = Some W_17418.
Proof. vm_refl. Qed.
Lemma D_17418 : decode_any W_17418 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1741c : bv 32 := 0x00a90023.
Lemma F_1741c : fetch_word Ubsan.M.loaded_segments (0x1741c : word) = Some W_1741c.
Proof. vm_refl. Qed.
Lemma D_1741c : decode_any W_1741c = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17420 : bv 32 := 0x00040513.
Lemma F_17420 : fetch_word Ubsan.M.loaded_segments (0x17420 : word) = Some W_17420.
Proof. vm_refl. Qed.
Lemma D_17420 : decode_any W_17420 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17424 : bv 32 := 0x02813083.
Lemma F_17424 : fetch_word Ubsan.M.loaded_segments (0x17424 : word) = Some W_17424.
Proof. vm_refl. Qed.
Lemma D_17424 : decode_any W_17424 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17428 : bv 32 := 0x02013403.
Lemma F_17428 : fetch_word Ubsan.M.loaded_segments (0x17428 : word) = Some W_17428.
Proof. vm_refl. Qed.
Lemma D_17428 : decode_any W_17428 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1742c : bv 32 := 0x01813483.
Lemma F_1742c : fetch_word Ubsan.M.loaded_segments (0x1742c : word) = Some W_1742c.
Proof. vm_refl. Qed.
Lemma D_1742c : decode_any W_1742c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17430 : bv 32 := 0x01013903.
Lemma F_17430 : fetch_word Ubsan.M.loaded_segments (0x17430 : word) = Some W_17430.
Proof. vm_refl. Qed.
Lemma D_17430 : decode_any W_17430 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17434 : bv 32 := 0x00813983.
Lemma F_17434 : fetch_word Ubsan.M.loaded_segments (0x17434 : word) = Some W_17434.
Proof. vm_refl. Qed.
Lemma D_17434 : decode_any W_17434 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17438 : bv 32 := 0x03010113.
Lemma F_17438 : fetch_word Ubsan.M.loaded_segments (0x17438 : word) = Some W_17438.
Proof. vm_refl. Qed.
Lemma D_17438 : decode_any W_17438 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1743c : bv 32 := 0x3350706f.
Lemma F_1743c : fetch_word Ubsan.M.loaded_segments (0x1743c : word) = Some W_1743c.
Proof. vm_refl. Qed.
Lemma D_1743c : decode_any W_1743c = Some (Jal 0 31540, 4%Z).
Proof. vm_refl. Qed.

Definition W_17440 : bv 32 := 0x00008067.
Lemma F_17440 : fetch_word Ubsan.M.loaded_segments (0x17440 : word) = Some W_17440.
Proof. vm_refl. Qed.
Lemma D_17440 : decode_any W_17440 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17508 : bv 32 := 0x00050067.
Lemma F_17508 : fetch_word Ubsan.M.loaded_segments (0x17508 : word) = Some W_17508.
Proof. vm_refl. Qed.
Lemma D_17508 : decode_any W_17508 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ef70 : bv 32 := 0x00052583.
Lemma F_1ef70 : fetch_word Ubsan.M.loaded_segments (0x1ef70 : word) = Some W_1ef70.
Proof. vm_refl. Qed.
Lemma D_1ef70 : decode_any W_1ef70 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ef74 : bv 32 := 0x0005c463.
Lemma F_1ef74 : fetch_word Ubsan.M.loaded_segments (0x1ef74 : word) = Some W_1ef74.
Proof. vm_refl. Qed.
Lemma D_1ef74 : decode_any W_1ef74 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ef78 : bv 32 := 0x00008067.
Lemma F_1ef78 : fetch_word Ubsan.M.loaded_segments (0x1ef78 : word) = Some W_1ef78.
Proof. vm_refl. Qed.
Lemma D_1ef78 : decode_any W_1ef78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
