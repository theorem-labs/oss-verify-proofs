(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_5d560 : bv 32 := 0x0ff5f593.
Lemma F_5d560 : fetch_word Ubsan.M.loaded_segments (0x5f33c : word) = Some W_5d560.
Proof. vm_refl. Qed.
Lemma D_5d560 : decode_any W_5d560 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d564 : bv 32 := 0x00757693.
Lemma F_5d564 : fetch_word Ubsan.M.loaded_segments (0x5f340 : word) = Some W_5d564.
Proof. vm_refl. Qed.
Lemma D_5d564 : decode_any W_5d564 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d568 : bv 32 := 0x00c03733.
Lemma F_5d568 : fetch_word Ubsan.M.loaded_segments (0x5f344 : word) = Some W_5d568.
Proof. vm_refl. Qed.
Lemma D_5d568 : decode_any W_5d568 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d56c : bv 32 := 0x02068c63.
Lemma F_5d56c : fetch_word Ubsan.M.loaded_segments (0x5f348 : word) = Some W_5d56c.
Proof. vm_refl. Qed.
Lemma D_5d56c : decode_any W_5d56c = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d570 : bv 32 := 0x02060a63.
Lemma F_5d570 : fetch_word Ubsan.M.loaded_segments (0x5f34c : word) = Some W_5d570.
Proof. vm_refl. Qed.
Lemma D_5d570 : decode_any W_5d570 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d574 : bv 32 := 0x00150793.
Lemma F_5d574 : fetch_word Ubsan.M.loaded_segments (0x5f350 : word) = Some W_5d574.
Proof. vm_refl. Qed.
Lemma D_5d574 : decode_any W_5d574 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d578 : bv 32 := 0x00100813.
Lemma F_5d578 : fetch_word Ubsan.M.loaded_segments (0x5f354 : word) = Some W_5d578.
Proof. vm_refl. Qed.
Lemma D_5d578 : decode_any W_5d578 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d57c : bv 32 := 0x00054703.
Lemma F_5d57c : fetch_word Ubsan.M.loaded_segments (0x5f358 : word) = Some W_5d57c.
Proof. vm_refl. Qed.
Lemma D_5d57c : decode_any W_5d57c = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d580 : bv 32 := 0x00060693.
Lemma F_5d580 : fetch_word Ubsan.M.loaded_segments (0x5f35c : word) = Some W_5d580.
Proof. vm_refl. Qed.
Lemma D_5d580 : decode_any W_5d580 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d584 : bv 32 := 0x06b70e63.
Lemma F_5d584 : fetch_word Ubsan.M.loaded_segments (0x5f360 : word) = Some W_5d584.
Proof. vm_refl. Qed.
Lemma D_5d584 : decode_any W_5d584 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d588 : bv 32 := 0x00150513.
Lemma F_5d588 : fetch_word Ubsan.M.loaded_segments (0x5f364 : word) = Some W_5d588.
Proof. vm_refl. Qed.
Lemma D_5d588 : decode_any W_5d588 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d58c : bv 32 := 0xfff68613.
Lemma F_5d58c : fetch_word Ubsan.M.loaded_segments (0x5f368 : word) = Some W_5d58c.
Proof. vm_refl. Qed.
Lemma D_5d58c : decode_any W_5d58c = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d590 : bv 32 := 0x0077f893.
Lemma F_5d590 : fetch_word Ubsan.M.loaded_segments (0x5f36c : word) = Some W_5d590.
Proof. vm_refl. Qed.
Lemma D_5d590 : decode_any W_5d590 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d594 : bv 32 := 0x00c03733.
Lemma F_5d594 : fetch_word Ubsan.M.loaded_segments (0x5f370 : word) = Some W_5d594.
Proof. vm_refl. Qed.
Lemma D_5d594 : decode_any W_5d594 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d598 : bv 32 := 0x00088663.
Lemma F_5d598 : fetch_word Ubsan.M.loaded_segments (0x5f374 : word) = Some W_5d598.
Proof. vm_refl. Qed.
Lemma D_5d598 : decode_any W_5d598 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d59c : bv 32 := 0x00178793.
Lemma F_5d59c : fetch_word Ubsan.M.loaded_segments (0x5f378 : word) = Some W_5d59c.
Proof. vm_refl. Qed.
Lemma D_5d59c : decode_any W_5d59c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5a0 : bv 32 := 0xfd069ee3.
Lemma F_5d5a0 : fetch_word Ubsan.M.loaded_segments (0x5f37c : word) = Some W_5d5a0.
Proof. vm_refl. Qed.
Lemma D_5d5a0 : decode_any W_5d5a0 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5a4 : bv 32 := 0x06070863.
Lemma F_5d5a4 : fetch_word Ubsan.M.loaded_segments (0x5f380 : word) = Some W_5d5a4.
Proof. vm_refl. Qed.
Lemma D_5d5a4 : decode_any W_5d5a4 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5a8 : bv 32 := 0x00054683.
Lemma F_5d5a8 : fetch_word Ubsan.M.loaded_segments (0x5f384 : word) = Some W_5d5a8.
Proof. vm_refl. Qed.
Lemma D_5d5a8 : decode_any W_5d5a8 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5ac : bv 32 := 0x04b68663.
Lemma F_5d5ac : fetch_word Ubsan.M.loaded_segments (0x5f388 : word) = Some W_5d5ac.
Proof. vm_refl. Qed.
Lemma D_5d5ac : decode_any W_5d5ac = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5b0 : bv 32 := 0x00800693.
Lemma F_5d5b0 : fetch_word Ubsan.M.loaded_segments (0x5f38c : word) = Some W_5d5b0.
Proof. vm_refl. Qed.
Lemma D_5d5b0 : decode_any W_5d5b0 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5b4 : bv 32 := 0x04d66263.
Lemma F_5d5b4 : fetch_word Ubsan.M.loaded_segments (0x5f390 : word) = Some W_5d5b4.
Proof. vm_refl. Qed.
Lemma D_5d5b4 : decode_any W_5d5b4 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5b8 : bv 32 := 0xfffb4697.
Lemma F_5d5b8 : fetch_word Ubsan.M.loaded_segments (0x5f394 : word) = Some W_5d5b8.
Proof. vm_refl. Qed.
Lemma D_5d5b8 : decode_any W_5d5b8 = Some (Auipc 13 1048500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5bc : bv 32 := 0x08c6b683.
Lemma F_5d5bc : fetch_word Ubsan.M.loaded_segments (0x5f398 : word) = Some W_5d5bc.
Proof. vm_refl. Qed.
Lemma D_5d5bc : decode_any W_5d5bc = Some (Load SZ8 true 13 13 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5c0 : bv 32 := 0xfffb4717.
Lemma F_5d5c0 : fetch_word Ubsan.M.loaded_segments (0x5f39c : word) = Some W_5d5c0.
Proof. vm_refl. Qed.
Lemma D_5d5c0 : decode_any W_5d5c0 = Some (Auipc 14 1048500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5c4 : bv 32 := 0x07473703.
Lemma F_5d5c4 : fetch_word Ubsan.M.loaded_segments (0x5f3a0 : word) = Some W_5d5c4.
Proof. vm_refl. Qed.
Lemma D_5d5c4 : decode_any W_5d5c4 = Some (Load SZ8 true 14 14 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5c8 : bv 32 := 0x00168793.
Lemma F_5d5c8 : fetch_word Ubsan.M.loaded_segments (0x5f3a4 : word) = Some W_5d5c8.
Proof. vm_refl. Qed.
Lemma D_5d5c8 : decode_any W_5d5c8 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5cc : bv 32 := 0x02f587b3.
Lemma F_5d5cc : fetch_word Ubsan.M.loaded_segments (0x5f3a8 : word) = Some W_5d5cc.
Proof. vm_refl. Qed.
Lemma D_5d5cc : decode_any W_5d5cc = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5d0 : bv 32 := 0x00700813.
Lemma F_5d5d0 : fetch_word Ubsan.M.loaded_segments (0x5f3ac : word) = Some W_5d5d0.
Proof. vm_refl. Qed.
Lemma D_5d5d0 : decode_any W_5d5d0 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5d4 : bv 32 := 0x00053883.
Lemma F_5d5d4 : fetch_word Ubsan.M.loaded_segments (0x5f3b0 : word) = Some W_5d5d4.
Proof. vm_refl. Qed.
Lemma D_5d5d4 : decode_any W_5d5d4 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5d8 : bv 32 := 0x00f8c8b3.
Lemma F_5d5d8 : fetch_word Ubsan.M.loaded_segments (0x5f3b4 : word) = Some W_5d5d8.
Proof. vm_refl. Qed.
Lemma D_5d5d8 : decode_any W_5d5d8 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5dc : bv 32 := 0x411682b3.
Lemma F_5d5dc : fetch_word Ubsan.M.loaded_segments (0x5f3b8 : word) = Some W_5d5dc.
Proof. vm_refl. Qed.
Lemma D_5d5dc : decode_any W_5d5dc = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5e0 : bv 32 := 0x0112e8b3.
Lemma F_5d5e0 : fetch_word Ubsan.M.loaded_segments (0x5f3bc : word) = Some W_5d5e0.
Proof. vm_refl. Qed.
Lemma D_5d5e0 : decode_any W_5d5e0 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5e4 : bv 32 := 0x00e8f8b3.
Lemma F_5d5e4 : fetch_word Ubsan.M.loaded_segments (0x5f3c0 : word) = Some W_5d5e4.
Proof. vm_refl. Qed.
Lemma D_5d5e4 : decode_any W_5d5e4 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5e8 : bv 32 := 0x02e89a63.
Lemma F_5d5e8 : fetch_word Ubsan.M.loaded_segments (0x5f3c4 : word) = Some W_5d5e8.
Proof. vm_refl. Qed.
Lemma D_5d5e8 : decode_any W_5d5e8 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5ec : bv 32 := 0xff860613.
Lemma F_5d5ec : fetch_word Ubsan.M.loaded_segments (0x5f3c8 : word) = Some W_5d5ec.
Proof. vm_refl. Qed.
Lemma D_5d5ec : decode_any W_5d5ec = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5f0 : bv 32 := 0x00850513.
Lemma F_5d5f0 : fetch_word Ubsan.M.loaded_segments (0x5f3cc : word) = Some W_5d5f0.
Proof. vm_refl. Qed.
Lemma D_5d5f0 : decode_any W_5d5f0 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5f4 : bv 32 := 0xfec860e3.
Lemma F_5d5f4 : fetch_word Ubsan.M.loaded_segments (0x5f3d0 : word) = Some W_5d5f4.
Proof. vm_refl. Qed.
Lemma D_5d5f4 : decode_any W_5d5f4 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5f8 : bv 32 := 0x00060693.
Lemma F_5d5f8 : fetch_word Ubsan.M.loaded_segments (0x5f3d4 : word) = Some W_5d5f8.
Proof. vm_refl. Qed.
Lemma D_5d5f8 : decode_any W_5d5f8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5fc : bv 32 := 0x00060c63.
Lemma F_5d5fc : fetch_word Ubsan.M.loaded_segments (0x5f3d8 : word) = Some W_5d5fc.
Proof. vm_refl. Qed.
Lemma D_5d5fc : decode_any W_5d5fc = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d600 : bv 32 := 0x00054603.
Lemma F_5d600 : fetch_word Ubsan.M.loaded_segments (0x5f3dc : word) = Some W_5d600.
Proof. vm_refl. Qed.
Lemma D_5d600 : decode_any W_5d600 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d604 : bv 32 := 0x00b60a63.
Lemma F_5d604 : fetch_word Ubsan.M.loaded_segments (0x5f3e0 : word) = Some W_5d604.
Proof. vm_refl. Qed.
Lemma D_5d604 : decode_any W_5d604 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d608 : bv 32 := 0xfff68693.
Lemma F_5d608 : fetch_word Ubsan.M.loaded_segments (0x5f3e4 : word) = Some W_5d608.
Proof. vm_refl. Qed.
Lemma D_5d608 : decode_any W_5d608 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d60c : bv 32 := 0x00150513.
Lemma F_5d60c : fetch_word Ubsan.M.loaded_segments (0x5f3e8 : word) = Some W_5d60c.
Proof. vm_refl. Qed.
Lemma D_5d60c : decode_any W_5d60c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d610 : bv 32 := 0xfe0698e3.
Lemma F_5d610 : fetch_word Ubsan.M.loaded_segments (0x5f3ec : word) = Some W_5d610.
Proof. vm_refl. Qed.
Lemma D_5d610 : decode_any W_5d610 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d618 : bv 32 := 0x00008067.
Lemma F_5d618 : fetch_word Ubsan.M.loaded_segments (0x5f3f4 : word) = Some W_5d618.
Proof. vm_refl. Qed.
Lemma D_5d618 : decode_any W_5d618 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d61c : bv 32 := 0x00060693.
Lemma F_5d61c : fetch_word Ubsan.M.loaded_segments (0x5f3f8 : word) = Some W_5d61c.
Proof. vm_refl. Qed.
Lemma D_5d61c : decode_any W_5d61c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d620 : bv 32 := 0x00054603.
Lemma F_5d620 : fetch_word Ubsan.M.loaded_segments (0x5f3fc : word) = Some W_5d620.
Proof. vm_refl. Qed.
Lemma D_5d620 : decode_any W_5d620 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d624 : bv 32 := 0xfeb612e3.
Lemma F_5d624 : fetch_word Ubsan.M.loaded_segments (0x5f400 : word) = Some W_5d624.
Proof. vm_refl. Qed.
Lemma D_5d624 : decode_any W_5d624 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d628 : bv 32 := 0xff1ff06f.
Lemma F_5d628 : fetch_word Ubsan.M.loaded_segments (0x5f404 : word) = Some W_5d628.
Proof. vm_refl. Qed.
Lemma D_5d628 : decode_any W_5d628 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.
