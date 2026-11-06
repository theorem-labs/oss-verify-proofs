(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_ac344 : bv 32 := 0x0ff5f593.
Lemma F_ac344 : fetch_word Plain.M.loaded_segments (0xac390 : word) = Some W_ac344.
Proof. vm_refl. Qed.
Lemma D_ac344 : decode_any W_ac344 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac348 : bv 32 := 0x00757693.
Lemma F_ac348 : fetch_word Plain.M.loaded_segments (0xac394 : word) = Some W_ac348.
Proof. vm_refl. Qed.
Lemma D_ac348 : decode_any W_ac348 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac34c : bv 32 := 0x00c03733.
Lemma F_ac34c : fetch_word Plain.M.loaded_segments (0xac398 : word) = Some W_ac34c.
Proof. vm_refl. Qed.
Lemma D_ac34c : decode_any W_ac34c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac350 : bv 32 := 0x02068c63.
Lemma F_ac350 : fetch_word Plain.M.loaded_segments (0xac39c : word) = Some W_ac350.
Proof. vm_refl. Qed.
Lemma D_ac350 : decode_any W_ac350 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac354 : bv 32 := 0x02060a63.
Lemma F_ac354 : fetch_word Plain.M.loaded_segments (0xac3a0 : word) = Some W_ac354.
Proof. vm_refl. Qed.
Lemma D_ac354 : decode_any W_ac354 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac358 : bv 32 := 0x00150793.
Lemma F_ac358 : fetch_word Plain.M.loaded_segments (0xac3a4 : word) = Some W_ac358.
Proof. vm_refl. Qed.
Lemma D_ac358 : decode_any W_ac358 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac35c : bv 32 := 0x00100813.
Lemma F_ac35c : fetch_word Plain.M.loaded_segments (0xac3a8 : word) = Some W_ac35c.
Proof. vm_refl. Qed.
Lemma D_ac35c : decode_any W_ac35c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac360 : bv 32 := 0x00054703.
Lemma F_ac360 : fetch_word Plain.M.loaded_segments (0xac3ac : word) = Some W_ac360.
Proof. vm_refl. Qed.
Lemma D_ac360 : decode_any W_ac360 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac364 : bv 32 := 0x00060693.
Lemma F_ac364 : fetch_word Plain.M.loaded_segments (0xac3b0 : word) = Some W_ac364.
Proof. vm_refl. Qed.
Lemma D_ac364 : decode_any W_ac364 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac368 : bv 32 := 0x06b70e63.
Lemma F_ac368 : fetch_word Plain.M.loaded_segments (0xac3b4 : word) = Some W_ac368.
Proof. vm_refl. Qed.
Lemma D_ac368 : decode_any W_ac368 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac36c : bv 32 := 0x00150513.
Lemma F_ac36c : fetch_word Plain.M.loaded_segments (0xac3b8 : word) = Some W_ac36c.
Proof. vm_refl. Qed.
Lemma D_ac36c : decode_any W_ac36c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac370 : bv 32 := 0xfff68613.
Lemma F_ac370 : fetch_word Plain.M.loaded_segments (0xac3bc : word) = Some W_ac370.
Proof. vm_refl. Qed.
Lemma D_ac370 : decode_any W_ac370 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac374 : bv 32 := 0x0077f893.
Lemma F_ac374 : fetch_word Plain.M.loaded_segments (0xac3c0 : word) = Some W_ac374.
Proof. vm_refl. Qed.
Lemma D_ac374 : decode_any W_ac374 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac378 : bv 32 := 0x00c03733.
Lemma F_ac378 : fetch_word Plain.M.loaded_segments (0xac3c4 : word) = Some W_ac378.
Proof. vm_refl. Qed.
Lemma D_ac378 : decode_any W_ac378 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac37c : bv 32 := 0x00088663.
Lemma F_ac37c : fetch_word Plain.M.loaded_segments (0xac3c8 : word) = Some W_ac37c.
Proof. vm_refl. Qed.
Lemma D_ac37c : decode_any W_ac37c = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac380 : bv 32 := 0x00178793.
Lemma F_ac380 : fetch_word Plain.M.loaded_segments (0xac3cc : word) = Some W_ac380.
Proof. vm_refl. Qed.
Lemma D_ac380 : decode_any W_ac380 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac384 : bv 32 := 0xfd069ee3.
Lemma F_ac384 : fetch_word Plain.M.loaded_segments (0xac3d0 : word) = Some W_ac384.
Proof. vm_refl. Qed.
Lemma D_ac384 : decode_any W_ac384 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac388 : bv 32 := 0x06070863.
Lemma F_ac388 : fetch_word Plain.M.loaded_segments (0xac3d4 : word) = Some W_ac388.
Proof. vm_refl. Qed.
Lemma D_ac388 : decode_any W_ac388 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac38c : bv 32 := 0x00054683.
Lemma F_ac38c : fetch_word Plain.M.loaded_segments (0xac3d8 : word) = Some W_ac38c.
Proof. vm_refl. Qed.
Lemma D_ac38c : decode_any W_ac38c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac390 : bv 32 := 0x04b68663.
Lemma F_ac390 : fetch_word Plain.M.loaded_segments (0xac3dc : word) = Some W_ac390.
Proof. vm_refl. Qed.
Lemma D_ac390 : decode_any W_ac390 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac394 : bv 32 := 0x00800693.
Lemma F_ac394 : fetch_word Plain.M.loaded_segments (0xac3e0 : word) = Some W_ac394.
Proof. vm_refl. Qed.
Lemma D_ac394 : decode_any W_ac394 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac398 : bv 32 := 0x04d66263.
Lemma F_ac398 : fetch_word Plain.M.loaded_segments (0xac3e4 : word) = Some W_ac398.
Proof. vm_refl. Qed.
Lemma D_ac398 : decode_any W_ac398 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac39c : bv 32 := 0xfff67697.
Lemma F_ac39c : fetch_word Plain.M.loaded_segments (0xac3e8 : word) = Some W_ac39c.
Proof. vm_refl. Qed.
Lemma D_ac39c : decode_any W_ac39c = Some (Auipc 13 1048423, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3a0 : bv 32 := 0x3686b683.
Lemma F_ac3a0 : fetch_word Plain.M.loaded_segments (0xac3ec : word) = Some W_ac3a0.
Proof. vm_refl. Qed.
Lemma D_ac3a0 : decode_any W_ac3a0 = Some (Load SZ8 true 13 13 872, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3a4 : bv 32 := 0xfff67717.
Lemma F_ac3a4 : fetch_word Plain.M.loaded_segments (0xac3f0 : word) = Some W_ac3a4.
Proof. vm_refl. Qed.
Lemma D_ac3a4 : decode_any W_ac3a4 = Some (Auipc 14 1048423, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3a8 : bv 32 := 0x35073703.
Lemma F_ac3a8 : fetch_word Plain.M.loaded_segments (0xac3f4 : word) = Some W_ac3a8.
Proof. vm_refl. Qed.
Lemma D_ac3a8 : decode_any W_ac3a8 = Some (Load SZ8 true 14 14 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3ac : bv 32 := 0x00168793.
Lemma F_ac3ac : fetch_word Plain.M.loaded_segments (0xac3f8 : word) = Some W_ac3ac.
Proof. vm_refl. Qed.
Lemma D_ac3ac : decode_any W_ac3ac = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3b0 : bv 32 := 0x02f587b3.
Lemma F_ac3b0 : fetch_word Plain.M.loaded_segments (0xac3fc : word) = Some W_ac3b0.
Proof. vm_refl. Qed.
Lemma D_ac3b0 : decode_any W_ac3b0 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3b4 : bv 32 := 0x00700813.
Lemma F_ac3b4 : fetch_word Plain.M.loaded_segments (0xac400 : word) = Some W_ac3b4.
Proof. vm_refl. Qed.
Lemma D_ac3b4 : decode_any W_ac3b4 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3b8 : bv 32 := 0x00053883.
Lemma F_ac3b8 : fetch_word Plain.M.loaded_segments (0xac404 : word) = Some W_ac3b8.
Proof. vm_refl. Qed.
Lemma D_ac3b8 : decode_any W_ac3b8 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3bc : bv 32 := 0x00f8c8b3.
Lemma F_ac3bc : fetch_word Plain.M.loaded_segments (0xac408 : word) = Some W_ac3bc.
Proof. vm_refl. Qed.
Lemma D_ac3bc : decode_any W_ac3bc = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3c0 : bv 32 := 0x411682b3.
Lemma F_ac3c0 : fetch_word Plain.M.loaded_segments (0xac40c : word) = Some W_ac3c0.
Proof. vm_refl. Qed.
Lemma D_ac3c0 : decode_any W_ac3c0 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3c4 : bv 32 := 0x0112e8b3.
Lemma F_ac3c4 : fetch_word Plain.M.loaded_segments (0xac410 : word) = Some W_ac3c4.
Proof. vm_refl. Qed.
Lemma D_ac3c4 : decode_any W_ac3c4 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3c8 : bv 32 := 0x00e8f8b3.
Lemma F_ac3c8 : fetch_word Plain.M.loaded_segments (0xac414 : word) = Some W_ac3c8.
Proof. vm_refl. Qed.
Lemma D_ac3c8 : decode_any W_ac3c8 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3cc : bv 32 := 0x02e89a63.
Lemma F_ac3cc : fetch_word Plain.M.loaded_segments (0xac418 : word) = Some W_ac3cc.
Proof. vm_refl. Qed.
Lemma D_ac3cc : decode_any W_ac3cc = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3d0 : bv 32 := 0xff860613.
Lemma F_ac3d0 : fetch_word Plain.M.loaded_segments (0xac41c : word) = Some W_ac3d0.
Proof. vm_refl. Qed.
Lemma D_ac3d0 : decode_any W_ac3d0 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3d4 : bv 32 := 0x00850513.
Lemma F_ac3d4 : fetch_word Plain.M.loaded_segments (0xac420 : word) = Some W_ac3d4.
Proof. vm_refl. Qed.
Lemma D_ac3d4 : decode_any W_ac3d4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3d8 : bv 32 := 0xfec860e3.
Lemma F_ac3d8 : fetch_word Plain.M.loaded_segments (0xac424 : word) = Some W_ac3d8.
Proof. vm_refl. Qed.
Lemma D_ac3d8 : decode_any W_ac3d8 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3dc : bv 32 := 0x00060693.
Lemma F_ac3dc : fetch_word Plain.M.loaded_segments (0xac428 : word) = Some W_ac3dc.
Proof. vm_refl. Qed.
Lemma D_ac3dc : decode_any W_ac3dc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3e0 : bv 32 := 0x00060c63.
Lemma F_ac3e0 : fetch_word Plain.M.loaded_segments (0xac42c : word) = Some W_ac3e0.
Proof. vm_refl. Qed.
Lemma D_ac3e0 : decode_any W_ac3e0 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3e4 : bv 32 := 0x00054603.
Lemma F_ac3e4 : fetch_word Plain.M.loaded_segments (0xac430 : word) = Some W_ac3e4.
Proof. vm_refl. Qed.
Lemma D_ac3e4 : decode_any W_ac3e4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3e8 : bv 32 := 0x00b60a63.
Lemma F_ac3e8 : fetch_word Plain.M.loaded_segments (0xac434 : word) = Some W_ac3e8.
Proof. vm_refl. Qed.
Lemma D_ac3e8 : decode_any W_ac3e8 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3ec : bv 32 := 0xfff68693.
Lemma F_ac3ec : fetch_word Plain.M.loaded_segments (0xac438 : word) = Some W_ac3ec.
Proof. vm_refl. Qed.
Lemma D_ac3ec : decode_any W_ac3ec = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3f0 : bv 32 := 0x00150513.
Lemma F_ac3f0 : fetch_word Plain.M.loaded_segments (0xac43c : word) = Some W_ac3f0.
Proof. vm_refl. Qed.
Lemma D_ac3f0 : decode_any W_ac3f0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3f4 : bv 32 := 0xfe0698e3.
Lemma F_ac3f4 : fetch_word Plain.M.loaded_segments (0xac440 : word) = Some W_ac3f4.
Proof. vm_refl. Qed.
Lemma D_ac3f4 : decode_any W_ac3f4 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac3fc : bv 32 := 0x00008067.
Lemma F_ac3fc : fetch_word Plain.M.loaded_segments (0xac448 : word) = Some W_ac3fc.
Proof. vm_refl. Qed.
Lemma D_ac3fc : decode_any W_ac3fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac400 : bv 32 := 0x00060693.
Lemma F_ac400 : fetch_word Plain.M.loaded_segments (0xac44c : word) = Some W_ac400.
Proof. vm_refl. Qed.
Lemma D_ac400 : decode_any W_ac400 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac404 : bv 32 := 0x00054603.
Lemma F_ac404 : fetch_word Plain.M.loaded_segments (0xac450 : word) = Some W_ac404.
Proof. vm_refl. Qed.
Lemma D_ac404 : decode_any W_ac404 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac408 : bv 32 := 0xfeb612e3.
Lemma F_ac408 : fetch_word Plain.M.loaded_segments (0xac454 : word) = Some W_ac408.
Proof. vm_refl. Qed.
Lemma D_ac408 : decode_any W_ac408 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac40c : bv 32 := 0xff1ff06f.
Lemma F_ac40c : fetch_word Plain.M.loaded_segments (0xac458 : word) = Some W_ac40c.
Proof. vm_refl. Qed.
Lemma D_ac40c : decode_any W_ac40c = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac440 : bv 32 := 0x0035f693.
Lemma F_ac440 : fetch_word Plain.M.loaded_segments (0xac48c : word) = Some W_ac440.
Proof. vm_refl. Qed.
Lemma D_ac440 : decode_any W_ac440 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac444 : bv 32 := 0x10068863.
Lemma F_ac444 : fetch_word Plain.M.loaded_segments (0xac490 : word) = Some W_ac444.
Proof. vm_refl. Qed.
Lemma D_ac444 : decode_any W_ac444 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac448 : bv 32 := 0x02060e63.
Lemma F_ac448 : fetch_word Plain.M.loaded_segments (0xac494 : word) = Some W_ac448.
Proof. vm_refl. Qed.
Lemma D_ac448 : decode_any W_ac448 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac44c : bv 32 := 0x00158713.
Lemma F_ac44c : fetch_word Plain.M.loaded_segments (0xac498 : word) = Some W_ac44c.
Proof. vm_refl. Qed.
Lemma D_ac44c : decode_any W_ac44c = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac450 : bv 32 := 0x00100793.
Lemma F_ac450 : fetch_word Plain.M.loaded_segments (0xac49c : word) = Some W_ac450.
Proof. vm_refl. Qed.
Lemma D_ac450 : decode_any W_ac450 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac454 : bv 32 := 0x00050693.
Lemma F_ac454 : fetch_word Plain.M.loaded_segments (0xac4a0 : word) = Some W_ac454.
Proof. vm_refl. Qed.
Lemma D_ac454 : decode_any W_ac454 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac458 : bv 32 := 0x0005c883.
Lemma F_ac458 : fetch_word Plain.M.loaded_segments (0xac4a4 : word) = Some W_ac458.
Proof. vm_refl. Qed.
Lemma D_ac458 : decode_any W_ac458 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac45c : bv 32 := 0x00060813.
Lemma F_ac45c : fetch_word Plain.M.loaded_segments (0xac4a8 : word) = Some W_ac45c.
Proof. vm_refl. Qed.
Lemma D_ac45c : decode_any W_ac45c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac460 : bv 32 := 0x00158593.
Lemma F_ac460 : fetch_word Plain.M.loaded_segments (0xac4ac : word) = Some W_ac460.
Proof. vm_refl. Qed.
Lemma D_ac460 : decode_any W_ac460 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac464 : bv 32 := 0x00377293.
Lemma F_ac464 : fetch_word Plain.M.loaded_segments (0xac4b0 : word) = Some W_ac464.
Proof. vm_refl. Qed.
Lemma D_ac464 : decode_any W_ac464 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac468 : bv 32 := 0x01168023.
Lemma F_ac468 : fetch_word Plain.M.loaded_segments (0xac4b4 : word) = Some W_ac468.
Proof. vm_refl. Qed.
Lemma D_ac468 : decode_any W_ac468 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac46c : bv 32 := 0x00168693.
Lemma F_ac46c : fetch_word Plain.M.loaded_segments (0xac4b8 : word) = Some W_ac46c.
Proof. vm_refl. Qed.
Lemma D_ac46c : decode_any W_ac46c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac470 : bv 32 := 0xfff60613.
Lemma F_ac470 : fetch_word Plain.M.loaded_segments (0xac4bc : word) = Some W_ac470.
Proof. vm_refl. Qed.
Lemma D_ac470 : decode_any W_ac470 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac474 : bv 32 := 0x00028a63.
Lemma F_ac474 : fetch_word Plain.M.loaded_segments (0xac4c0 : word) = Some W_ac474.
Proof. vm_refl. Qed.
Lemma D_ac474 : decode_any W_ac474 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac478 : bv 32 := 0x00170713.
Lemma F_ac478 : fetch_word Plain.M.loaded_segments (0xac4c4 : word) = Some W_ac478.
Proof. vm_refl. Qed.
Lemma D_ac478 : decode_any W_ac478 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac47c : bv 32 := 0xfcf81ee3.
Lemma F_ac47c : fetch_word Plain.M.loaded_segments (0xac4c8 : word) = Some W_ac47c.
Proof. vm_refl. Qed.
Lemma D_ac47c : decode_any W_ac47c = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac480 : bv 32 := 0x0080006f.
Lemma F_ac480 : fetch_word Plain.M.loaded_segments (0xac4cc : word) = Some W_ac480.
Proof. vm_refl. Qed.
Lemma D_ac480 : decode_any W_ac480 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac484 : bv 32 := 0x00050693.
Lemma F_ac484 : fetch_word Plain.M.loaded_segments (0xac4d0 : word) = Some W_ac484.
Proof. vm_refl. Qed.
Lemma D_ac484 : decode_any W_ac484 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac488 : bv 32 := 0x0036f793.
Lemma F_ac488 : fetch_word Plain.M.loaded_segments (0xac4d4 : word) = Some W_ac488.
Proof. vm_refl. Qed.
Lemma D_ac488 : decode_any W_ac488 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac48c : bv 32 := 0x0c078a63.
Lemma F_ac48c : fetch_word Plain.M.loaded_segments (0xac4d8 : word) = Some W_ac48c.
Proof. vm_refl. Qed.
Lemma D_ac48c : decode_any W_ac48c = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac490 : bv 32 := 0x02000713.
Lemma F_ac490 : fetch_word Plain.M.loaded_segments (0xac4dc : word) = Some W_ac490.
Proof. vm_refl. Qed.
Lemma D_ac490 : decode_any W_ac490 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac494 : bv 32 := 0x02e67063.
Lemma F_ac494 : fetch_word Plain.M.loaded_segments (0xac4e0 : word) = Some W_ac494.
Proof. vm_refl. Qed.
Lemma D_ac494 : decode_any W_ac494 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac498 : bv 32 := 0x01000713.
Lemma F_ac498 : fetch_word Plain.M.loaded_segments (0xac4e4 : word) = Some W_ac498.
Proof. vm_refl. Qed.
Lemma D_ac498 : decode_any W_ac498 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac49c : bv 32 := 0x24e67863.
Lemma F_ac49c : fetch_word Plain.M.loaded_segments (0xac4e8 : word) = Some W_ac49c.
Proof. vm_refl. Qed.
Lemma D_ac49c : decode_any W_ac49c = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4a0 : bv 32 := 0x00867713.
Lemma F_ac4a0 : fetch_word Plain.M.loaded_segments (0xac4ec : word) = Some W_ac4a0.
Proof. vm_refl. Qed.
Lemma D_ac4a0 : decode_any W_ac4a0 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4a4 : bv 32 := 0x2c071e63.
Lemma F_ac4a4 : fetch_word Plain.M.loaded_segments (0xac4f0 : word) = Some W_ac4a4.
Proof. vm_refl. Qed.
Lemma D_ac4a4 : decode_any W_ac4a4 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4a8 : bv 32 := 0x00467713.
Lemma F_ac4a8 : fetch_word Plain.M.loaded_segments (0xac4f4 : word) = Some W_ac4a8.
Proof. vm_refl. Qed.
Lemma D_ac4a8 : decode_any W_ac4a8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4ac : bv 32 := 0x32071463.
Lemma F_ac4ac : fetch_word Plain.M.loaded_segments (0xac4f8 : word) = Some W_ac4ac.
Proof. vm_refl. Qed.
Lemma D_ac4ac : decode_any W_ac4ac = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4b0 : bv 32 := 0x3500006f.
Lemma F_ac4b0 : fetch_word Plain.M.loaded_segments (0xac4fc : word) = Some W_ac4b0.
Proof. vm_refl. Qed.
Lemma D_ac4b0 : decode_any W_ac4b0 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4b4 : bv 32 := 0x0005a703.
Lemma F_ac4b4 : fetch_word Plain.M.loaded_segments (0xac500 : word) = Some W_ac4b4.
Proof. vm_refl. Qed.
Lemma D_ac4b4 : decode_any W_ac4b4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4b8 : bv 32 := 0x00300813.
Lemma F_ac4b8 : fetch_word Plain.M.loaded_segments (0xac504 : word) = Some W_ac4b8.
Proof. vm_refl. Qed.
Lemma D_ac4b8 : decode_any W_ac4b8 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4bc : bv 32 := 0x11078e63.
Lemma F_ac4bc : fetch_word Plain.M.loaded_segments (0xac508 : word) = Some W_ac4bc.
Proof. vm_refl. Qed.
Lemma D_ac4bc : decode_any W_ac4bc = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4c0 : bv 32 := 0x00200813.
Lemma F_ac4c0 : fetch_word Plain.M.loaded_segments (0xac50c : word) = Some W_ac4c0.
Proof. vm_refl. Qed.
Lemma D_ac4c0 : decode_any W_ac4c0 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4c4 : bv 32 := 0x19079c63.
Lemma F_ac4c4 : fetch_word Plain.M.loaded_segments (0xac510 : word) = Some W_ac4c4.
Proof. vm_refl. Qed.
Lemma D_ac4c4 : decode_any W_ac4c4 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4c8 : bv 32 := 0x00875793.
Lemma F_ac4c8 : fetch_word Plain.M.loaded_segments (0xac514 : word) = Some W_ac4c8.
Proof. vm_refl. Qed.
Lemma D_ac4c8 : decode_any W_ac4c8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4cc : bv 32 := 0xffe60613.
Lemma F_ac4cc : fetch_word Plain.M.loaded_segments (0xac518 : word) = Some W_ac4cc.
Proof. vm_refl. Qed.
Lemma D_ac4cc : decode_any W_ac4cc = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4d0 : bv 32 := 0x00e68023.
Lemma F_ac4d0 : fetch_word Plain.M.loaded_segments (0xac51c : word) = Some W_ac4d0.
Proof. vm_refl. Qed.
Lemma D_ac4d0 : decode_any W_ac4d0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4d4 : bv 32 := 0x00f680a3.
Lemma F_ac4d4 : fetch_word Plain.M.loaded_segments (0xac520 : word) = Some W_ac4d4.
Proof. vm_refl. Qed.
Lemma D_ac4d4 : decode_any W_ac4d4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4d8 : bv 32 := 0x00268693.
Lemma F_ac4d8 : fetch_word Plain.M.loaded_segments (0xac524 : word) = Some W_ac4d8.
Proof. vm_refl. Qed.
Lemma D_ac4d8 : decode_any W_ac4d8 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4dc : bv 32 := 0x01058593.
Lemma F_ac4dc : fetch_word Plain.M.loaded_segments (0xac528 : word) = Some W_ac4dc.
Proof. vm_refl. Qed.
Lemma D_ac4dc : decode_any W_ac4dc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4e0 : bv 32 := 0x01100793.
Lemma F_ac4e0 : fetch_word Plain.M.loaded_segments (0xac52c : word) = Some W_ac4e0.
Proof. vm_refl. Qed.
Lemma D_ac4e0 : decode_any W_ac4e0 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4e4 : bv 32 := 0x0107581b.
Lemma F_ac4e4 : fetch_word Plain.M.loaded_segments (0xac530 : word) = Some W_ac4e4.
Proof. vm_refl. Qed.
Lemma D_ac4e4 : decode_any W_ac4e4 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4e8 : bv 32 := 0xff45a883.
Lemma F_ac4e8 : fetch_word Plain.M.loaded_segments (0xac534 : word) = Some W_ac4e8.
Proof. vm_refl. Qed.
Lemma D_ac4e8 : decode_any W_ac4e8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4ec : bv 32 := 0xff85a283.
Lemma F_ac4ec : fetch_word Plain.M.loaded_segments (0xac538 : word) = Some W_ac4ec.
Proof. vm_refl. Qed.
Lemma D_ac4ec : decode_any W_ac4ec = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4f0 : bv 32 := 0xffc5a303.
Lemma F_ac4f0 : fetch_word Plain.M.loaded_segments (0xac53c : word) = Some W_ac4f0.
Proof. vm_refl. Qed.
Lemma D_ac4f0 : decode_any W_ac4f0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4f4 : bv 32 := 0x0005a703.
Lemma F_ac4f4 : fetch_word Plain.M.loaded_segments (0xac540 : word) = Some W_ac4f4.
Proof. vm_refl. Qed.
Lemma D_ac4f4 : decode_any W_ac4f4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4f8 : bv 32 := 0x01089393.
Lemma F_ac4f8 : fetch_word Plain.M.loaded_segments (0xac544 : word) = Some W_ac4f8.
Proof. vm_refl. Qed.
Lemma D_ac4f8 : decode_any W_ac4f8 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4fc : bv 32 := 0x0108d89b.
Lemma F_ac4fc : fetch_word Plain.M.loaded_segments (0xac548 : word) = Some W_ac4fc.
Proof. vm_refl. Qed.
Lemma D_ac4fc : decode_any W_ac4fc = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac500 : bv 32 := 0x0103e833.
Lemma F_ac500 : fetch_word Plain.M.loaded_segments (0xac54c : word) = Some W_ac500.
Proof. vm_refl. Qed.
Lemma D_ac500 : decode_any W_ac500 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac504 : bv 32 := 0x01029393.
Lemma F_ac504 : fetch_word Plain.M.loaded_segments (0xac550 : word) = Some W_ac504.
Proof. vm_refl. Qed.
Lemma D_ac504 : decode_any W_ac504 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac508 : bv 32 := 0x0102d29b.
Lemma F_ac508 : fetch_word Plain.M.loaded_segments (0xac554 : word) = Some W_ac508.
Proof. vm_refl. Qed.
Lemma D_ac508 : decode_any W_ac508 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac50c : bv 32 := 0x0113e8b3.
Lemma F_ac50c : fetch_word Plain.M.loaded_segments (0xac558 : word) = Some W_ac50c.
Proof. vm_refl. Qed.
Lemma D_ac50c : decode_any W_ac50c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac510 : bv 32 := 0x01031393.
Lemma F_ac510 : fetch_word Plain.M.loaded_segments (0xac55c : word) = Some W_ac510.
Proof. vm_refl. Qed.
Lemma D_ac510 : decode_any W_ac510 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac514 : bv 32 := 0x0103531b.
Lemma F_ac514 : fetch_word Plain.M.loaded_segments (0xac560 : word) = Some W_ac514.
Proof. vm_refl. Qed.
Lemma D_ac514 : decode_any W_ac514 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac518 : bv 32 := 0x0053e2b3.
Lemma F_ac518 : fetch_word Plain.M.loaded_segments (0xac564 : word) = Some W_ac518.
Proof. vm_refl. Qed.
Lemma D_ac518 : decode_any W_ac518 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac51c : bv 32 := 0x01071393.
Lemma F_ac51c : fetch_word Plain.M.loaded_segments (0xac568 : word) = Some W_ac51c.
Proof. vm_refl. Qed.
Lemma D_ac51c : decode_any W_ac51c = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac520 : bv 32 := 0x0063e333.
Lemma F_ac520 : fetch_word Plain.M.loaded_segments (0xac56c : word) = Some W_ac520.
Proof. vm_refl. Qed.
Lemma D_ac520 : decode_any W_ac520 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac524 : bv 32 := 0xff060613.
Lemma F_ac524 : fetch_word Plain.M.loaded_segments (0xac570 : word) = Some W_ac524.
Proof. vm_refl. Qed.
Lemma D_ac524 : decode_any W_ac524 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac528 : bv 32 := 0x0106a023.
Lemma F_ac528 : fetch_word Plain.M.loaded_segments (0xac574 : word) = Some W_ac528.
Proof. vm_refl. Qed.
Lemma D_ac528 : decode_any W_ac528 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac52c : bv 32 := 0x0116a223.
Lemma F_ac52c : fetch_word Plain.M.loaded_segments (0xac578 : word) = Some W_ac52c.
Proof. vm_refl. Qed.
Lemma D_ac52c : decode_any W_ac52c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac530 : bv 32 := 0x0056a423.
Lemma F_ac530 : fetch_word Plain.M.loaded_segments (0xac57c : word) = Some W_ac530.
Proof. vm_refl. Qed.
Lemma D_ac530 : decode_any W_ac530 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac534 : bv 32 := 0x0066a623.
Lemma F_ac534 : fetch_word Plain.M.loaded_segments (0xac580 : word) = Some W_ac534.
Proof. vm_refl. Qed.
Lemma D_ac534 : decode_any W_ac534 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac538 : bv 32 := 0x01068693.
Lemma F_ac538 : fetch_word Plain.M.loaded_segments (0xac584 : word) = Some W_ac538.
Proof. vm_refl. Qed.
Lemma D_ac538 : decode_any W_ac538 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac53c : bv 32 := 0x01058593.
Lemma F_ac53c : fetch_word Plain.M.loaded_segments (0xac588 : word) = Some W_ac53c.
Proof. vm_refl. Qed.
Lemma D_ac53c : decode_any W_ac53c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac540 : bv 32 := 0xfac7e2e3.
Lemma F_ac540 : fetch_word Plain.M.loaded_segments (0xac58c : word) = Some W_ac540.
Proof. vm_refl. Qed.
Lemma D_ac540 : decode_any W_ac540 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac544 : bv 32 := 0xff258593.
Lemma F_ac544 : fetch_word Plain.M.loaded_segments (0xac590 : word) = Some W_ac544.
Proof. vm_refl. Qed.
Lemma D_ac544 : decode_any W_ac544 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac548 : bv 32 := 0x01000713.
Lemma F_ac548 : fetch_word Plain.M.loaded_segments (0xac594 : word) = Some W_ac548.
Proof. vm_refl. Qed.
Lemma D_ac548 : decode_any W_ac548 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac54c : bv 32 := 0xf4e66ae3.
Lemma F_ac54c : fetch_word Plain.M.loaded_segments (0xac598 : word) = Some W_ac54c.
Proof. vm_refl. Qed.
Lemma D_ac54c : decode_any W_ac54c = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac550 : bv 32 := 0x19c0006f.
Lemma F_ac550 : fetch_word Plain.M.loaded_segments (0xac59c : word) = Some W_ac550.
Proof. vm_refl. Qed.
Lemma D_ac550 : decode_any W_ac550 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac554 : bv 32 := 0x00050693.
Lemma F_ac554 : fetch_word Plain.M.loaded_segments (0xac5a0 : word) = Some W_ac554.
Proof. vm_refl. Qed.
Lemma D_ac554 : decode_any W_ac554 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac558 : bv 32 := 0x00357793.
Lemma F_ac558 : fetch_word Plain.M.loaded_segments (0xac5a4 : word) = Some W_ac558.
Proof. vm_refl. Qed.
Lemma D_ac558 : decode_any W_ac558 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac55c : bv 32 := 0xf2079ae3.
Lemma F_ac55c : fetch_word Plain.M.loaded_segments (0xac5a8 : word) = Some W_ac55c.
Proof. vm_refl. Qed.
Lemma D_ac55c : decode_any W_ac55c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac560 : bv 32 := 0x01000713.
Lemma F_ac560 : fetch_word Plain.M.loaded_segments (0xac5ac : word) = Some W_ac560.
Proof. vm_refl. Qed.
Lemma D_ac560 : decode_any W_ac560 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac564 : bv 32 := 0x02e66c63.
Lemma F_ac564 : fetch_word Plain.M.loaded_segments (0xac5b0 : word) = Some W_ac564.
Proof. vm_refl. Qed.
Lemma D_ac564 : decode_any W_ac564 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac568 : bv 32 := 0x00f00713.
Lemma F_ac568 : fetch_word Plain.M.loaded_segments (0xac5b4 : word) = Some W_ac568.
Proof. vm_refl. Qed.
Lemma D_ac568 : decode_any W_ac568 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac56c : bv 32 := 0x0005a783.
Lemma F_ac56c : fetch_word Plain.M.loaded_segments (0xac5b8 : word) = Some W_ac56c.
Proof. vm_refl. Qed.
Lemma D_ac56c : decode_any W_ac56c = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac570 : bv 32 := 0x0045a803.
Lemma F_ac570 : fetch_word Plain.M.loaded_segments (0xac5bc : word) = Some W_ac570.
Proof. vm_refl. Qed.
Lemma D_ac570 : decode_any W_ac570 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac574 : bv 32 := 0x0085a883.
Lemma F_ac574 : fetch_word Plain.M.loaded_segments (0xac5c0 : word) = Some W_ac574.
Proof. vm_refl. Qed.
Lemma D_ac574 : decode_any W_ac574 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac578 : bv 32 := 0x00c5a283.
Lemma F_ac578 : fetch_word Plain.M.loaded_segments (0xac5c4 : word) = Some W_ac578.
Proof. vm_refl. Qed.
Lemma D_ac578 : decode_any W_ac578 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac57c : bv 32 := 0x01058593.
Lemma F_ac57c : fetch_word Plain.M.loaded_segments (0xac5c8 : word) = Some W_ac57c.
Proof. vm_refl. Qed.
Lemma D_ac57c : decode_any W_ac57c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac580 : bv 32 := 0xff060613.
Lemma F_ac580 : fetch_word Plain.M.loaded_segments (0xac5cc : word) = Some W_ac580.
Proof. vm_refl. Qed.
Lemma D_ac580 : decode_any W_ac580 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac584 : bv 32 := 0x00f6a023.
Lemma F_ac584 : fetch_word Plain.M.loaded_segments (0xac5d0 : word) = Some W_ac584.
Proof. vm_refl. Qed.
Lemma D_ac584 : decode_any W_ac584 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac588 : bv 32 := 0x0106a223.
Lemma F_ac588 : fetch_word Plain.M.loaded_segments (0xac5d4 : word) = Some W_ac588.
Proof. vm_refl. Qed.
Lemma D_ac588 : decode_any W_ac588 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac58c : bv 32 := 0x0116a423.
Lemma F_ac58c : fetch_word Plain.M.loaded_segments (0xac5d8 : word) = Some W_ac58c.
Proof. vm_refl. Qed.
Lemma D_ac58c : decode_any W_ac58c = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac590 : bv 32 := 0x0056a623.
Lemma F_ac590 : fetch_word Plain.M.loaded_segments (0xac5dc : word) = Some W_ac590.
Proof. vm_refl. Qed.
Lemma D_ac590 : decode_any W_ac590 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac594 : bv 32 := 0x01068693.
Lemma F_ac594 : fetch_word Plain.M.loaded_segments (0xac5e0 : word) = Some W_ac594.
Proof. vm_refl. Qed.
Lemma D_ac594 : decode_any W_ac594 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac598 : bv 32 := 0xfcc76ae3.
Lemma F_ac598 : fetch_word Plain.M.loaded_segments (0xac5e4 : word) = Some W_ac598.
Proof. vm_refl. Qed.
Lemma D_ac598 : decode_any W_ac598 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac59c : bv 32 := 0x00800713.
Lemma F_ac59c : fetch_word Plain.M.loaded_segments (0xac5e8 : word) = Some W_ac59c.
Proof. vm_refl. Qed.
Lemma D_ac59c : decode_any W_ac59c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5a0 : bv 32 := 0x00e66e63.
Lemma F_ac5a0 : fetch_word Plain.M.loaded_segments (0xac5ec : word) = Some W_ac5a0.
Proof. vm_refl. Qed.
Lemma D_ac5a0 : decode_any W_ac5a0 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5a4 : bv 32 := 0x0005a703.
Lemma F_ac5a4 : fetch_word Plain.M.loaded_segments (0xac5f0 : word) = Some W_ac5a4.
Proof. vm_refl. Qed.
Lemma D_ac5a4 : decode_any W_ac5a4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5a8 : bv 32 := 0x0045a783.
Lemma F_ac5a8 : fetch_word Plain.M.loaded_segments (0xac5f4 : word) = Some W_ac5a8.
Proof. vm_refl. Qed.
Lemma D_ac5a8 : decode_any W_ac5a8 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5ac : bv 32 := 0x00e6a023.
Lemma F_ac5ac : fetch_word Plain.M.loaded_segments (0xac5f8 : word) = Some W_ac5ac.
Proof. vm_refl. Qed.
Lemma D_ac5ac : decode_any W_ac5ac = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5b0 : bv 32 := 0x00f6a223.
Lemma F_ac5b0 : fetch_word Plain.M.loaded_segments (0xac5fc : word) = Some W_ac5b0.
Proof. vm_refl. Qed.
Lemma D_ac5b0 : decode_any W_ac5b0 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5b4 : bv 32 := 0x00868693.
Lemma F_ac5b4 : fetch_word Plain.M.loaded_segments (0xac600 : word) = Some W_ac5b4.
Proof. vm_refl. Qed.
Lemma D_ac5b4 : decode_any W_ac5b4 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5b8 : bv 32 := 0x00858593.
Lemma F_ac5b8 : fetch_word Plain.M.loaded_segments (0xac604 : word) = Some W_ac5b8.
Proof. vm_refl. Qed.
Lemma D_ac5b8 : decode_any W_ac5b8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5bc : bv 32 := 0x00467713.
Lemma F_ac5bc : fetch_word Plain.M.loaded_segments (0xac608 : word) = Some W_ac5bc.
Proof. vm_refl. Qed.
Lemma D_ac5bc : decode_any W_ac5bc = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5c0 : bv 32 := 0x24070063.
Lemma F_ac5c0 : fetch_word Plain.M.loaded_segments (0xac60c : word) = Some W_ac5c0.
Proof. vm_refl. Qed.
Lemma D_ac5c0 : decode_any W_ac5c0 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5c4 : bv 32 := 0x0005a703.
Lemma F_ac5c4 : fetch_word Plain.M.loaded_segments (0xac610 : word) = Some W_ac5c4.
Proof. vm_refl. Qed.
Lemma D_ac5c4 : decode_any W_ac5c4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5c8 : bv 32 := 0x00458593.
Lemma F_ac5c8 : fetch_word Plain.M.loaded_segments (0xac614 : word) = Some W_ac5c8.
Proof. vm_refl. Qed.
Lemma D_ac5c8 : decode_any W_ac5c8 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5cc : bv 32 := 0x00e6a023.
Lemma F_ac5cc : fetch_word Plain.M.loaded_segments (0xac618 : word) = Some W_ac5cc.
Proof. vm_refl. Qed.
Lemma D_ac5cc : decode_any W_ac5cc = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5d0 : bv 32 := 0x00468693.
Lemma F_ac5d0 : fetch_word Plain.M.loaded_segments (0xac61c : word) = Some W_ac5d0.
Proof. vm_refl. Qed.
Lemma D_ac5d0 : decode_any W_ac5d0 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5d4 : bv 32 := 0x22c0006f.
Lemma F_ac5d4 : fetch_word Plain.M.loaded_segments (0xac620 : word) = Some W_ac5d4.
Proof. vm_refl. Qed.
Lemma D_ac5d4 : decode_any W_ac5d4 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5d8 : bv 32 := 0x00e68023.
Lemma F_ac5d8 : fetch_word Plain.M.loaded_segments (0xac624 : word) = Some W_ac5d8.
Proof. vm_refl. Qed.
Lemma D_ac5d8 : decode_any W_ac5d8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5dc : bv 32 := 0x00168693.
Lemma F_ac5dc : fetch_word Plain.M.loaded_segments (0xac628 : word) = Some W_ac5dc.
Proof. vm_refl. Qed.
Lemma D_ac5dc : decode_any W_ac5dc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5e0 : bv 32 := 0xfff60613.
Lemma F_ac5e0 : fetch_word Plain.M.loaded_segments (0xac62c : word) = Some W_ac5e0.
Proof. vm_refl. Qed.
Lemma D_ac5e0 : decode_any W_ac5e0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5e4 : bv 32 := 0x01058593.
Lemma F_ac5e4 : fetch_word Plain.M.loaded_segments (0xac630 : word) = Some W_ac5e4.
Proof. vm_refl. Qed.
Lemma D_ac5e4 : decode_any W_ac5e4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5e8 : bv 32 := 0x01200793.
Lemma F_ac5e8 : fetch_word Plain.M.loaded_segments (0xac634 : word) = Some W_ac5e8.
Proof. vm_refl. Qed.
Lemma D_ac5e8 : decode_any W_ac5e8 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5ec : bv 32 := 0x0087581b.
Lemma F_ac5ec : fetch_word Plain.M.loaded_segments (0xac638 : word) = Some W_ac5ec.
Proof. vm_refl. Qed.
Lemma D_ac5ec : decode_any W_ac5ec = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5f0 : bv 32 := 0xff45a883.
Lemma F_ac5f0 : fetch_word Plain.M.loaded_segments (0xac63c : word) = Some W_ac5f0.
Proof. vm_refl. Qed.
Lemma D_ac5f0 : decode_any W_ac5f0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5f4 : bv 32 := 0xff85a283.
Lemma F_ac5f4 : fetch_word Plain.M.loaded_segments (0xac640 : word) = Some W_ac5f4.
Proof. vm_refl. Qed.
Lemma D_ac5f4 : decode_any W_ac5f4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5f8 : bv 32 := 0xffc5a303.
Lemma F_ac5f8 : fetch_word Plain.M.loaded_segments (0xac644 : word) = Some W_ac5f8.
Proof. vm_refl. Qed.
Lemma D_ac5f8 : decode_any W_ac5f8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac5fc : bv 32 := 0x0005a703.
Lemma F_ac5fc : fetch_word Plain.M.loaded_segments (0xac648 : word) = Some W_ac5fc.
Proof. vm_refl. Qed.
Lemma D_ac5fc : decode_any W_ac5fc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac600 : bv 32 := 0x01889393.
Lemma F_ac600 : fetch_word Plain.M.loaded_segments (0xac64c : word) = Some W_ac600.
Proof. vm_refl. Qed.
Lemma D_ac600 : decode_any W_ac600 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac604 : bv 32 := 0x0088d89b.
Lemma F_ac604 : fetch_word Plain.M.loaded_segments (0xac650 : word) = Some W_ac604.
Proof. vm_refl. Qed.
Lemma D_ac604 : decode_any W_ac604 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac608 : bv 32 := 0x0103e833.
Lemma F_ac608 : fetch_word Plain.M.loaded_segments (0xac654 : word) = Some W_ac608.
Proof. vm_refl. Qed.
Lemma D_ac608 : decode_any W_ac608 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac60c : bv 32 := 0x01829393.
Lemma F_ac60c : fetch_word Plain.M.loaded_segments (0xac658 : word) = Some W_ac60c.
Proof. vm_refl. Qed.
Lemma D_ac60c : decode_any W_ac60c = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac610 : bv 32 := 0x0082d29b.
Lemma F_ac610 : fetch_word Plain.M.loaded_segments (0xac65c : word) = Some W_ac610.
Proof. vm_refl. Qed.
Lemma D_ac610 : decode_any W_ac610 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac614 : bv 32 := 0x0113e8b3.
Lemma F_ac614 : fetch_word Plain.M.loaded_segments (0xac660 : word) = Some W_ac614.
Proof. vm_refl. Qed.
Lemma D_ac614 : decode_any W_ac614 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac618 : bv 32 := 0x01831393.
Lemma F_ac618 : fetch_word Plain.M.loaded_segments (0xac664 : word) = Some W_ac618.
Proof. vm_refl. Qed.
Lemma D_ac618 : decode_any W_ac618 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac61c : bv 32 := 0x0083531b.
Lemma F_ac61c : fetch_word Plain.M.loaded_segments (0xac668 : word) = Some W_ac61c.
Proof. vm_refl. Qed.
Lemma D_ac61c : decode_any W_ac61c = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac620 : bv 32 := 0x0053e2b3.
Lemma F_ac620 : fetch_word Plain.M.loaded_segments (0xac66c : word) = Some W_ac620.
Proof. vm_refl. Qed.
Lemma D_ac620 : decode_any W_ac620 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac624 : bv 32 := 0x01871393.
Lemma F_ac624 : fetch_word Plain.M.loaded_segments (0xac670 : word) = Some W_ac624.
Proof. vm_refl. Qed.
Lemma D_ac624 : decode_any W_ac624 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac628 : bv 32 := 0x0063e333.
Lemma F_ac628 : fetch_word Plain.M.loaded_segments (0xac674 : word) = Some W_ac628.
Proof. vm_refl. Qed.
Lemma D_ac628 : decode_any W_ac628 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac62c : bv 32 := 0xff060613.
Lemma F_ac62c : fetch_word Plain.M.loaded_segments (0xac678 : word) = Some W_ac62c.
Proof. vm_refl. Qed.
Lemma D_ac62c : decode_any W_ac62c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac630 : bv 32 := 0x0106a023.
Lemma F_ac630 : fetch_word Plain.M.loaded_segments (0xac67c : word) = Some W_ac630.
Proof. vm_refl. Qed.
Lemma D_ac630 : decode_any W_ac630 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac634 : bv 32 := 0x0116a223.
Lemma F_ac634 : fetch_word Plain.M.loaded_segments (0xac680 : word) = Some W_ac634.
Proof. vm_refl. Qed.
Lemma D_ac634 : decode_any W_ac634 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac638 : bv 32 := 0x0056a423.
Lemma F_ac638 : fetch_word Plain.M.loaded_segments (0xac684 : word) = Some W_ac638.
Proof. vm_refl. Qed.
Lemma D_ac638 : decode_any W_ac638 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac63c : bv 32 := 0x0066a623.
Lemma F_ac63c : fetch_word Plain.M.loaded_segments (0xac688 : word) = Some W_ac63c.
Proof. vm_refl. Qed.
Lemma D_ac63c : decode_any W_ac63c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac640 : bv 32 := 0x01068693.
Lemma F_ac640 : fetch_word Plain.M.loaded_segments (0xac68c : word) = Some W_ac640.
Proof. vm_refl. Qed.
Lemma D_ac640 : decode_any W_ac640 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac644 : bv 32 := 0x01058593.
Lemma F_ac644 : fetch_word Plain.M.loaded_segments (0xac690 : word) = Some W_ac644.
Proof. vm_refl. Qed.
Lemma D_ac644 : decode_any W_ac644 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac648 : bv 32 := 0xfac7e2e3.
Lemma F_ac648 : fetch_word Plain.M.loaded_segments (0xac694 : word) = Some W_ac648.
Proof. vm_refl. Qed.
Lemma D_ac648 : decode_any W_ac648 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac64c : bv 32 := 0xff158593.
Lemma F_ac64c : fetch_word Plain.M.loaded_segments (0xac698 : word) = Some W_ac64c.
Proof. vm_refl. Qed.
Lemma D_ac64c : decode_any W_ac64c = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac650 : bv 32 := 0x01000713.
Lemma F_ac650 : fetch_word Plain.M.loaded_segments (0xac69c : word) = Some W_ac650.
Proof. vm_refl. Qed.
Lemma D_ac650 : decode_any W_ac650 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac654 : bv 32 := 0xe4e666e3.
Lemma F_ac654 : fetch_word Plain.M.loaded_segments (0xac6a0 : word) = Some W_ac654.
Proof. vm_refl. Qed.
Lemma D_ac654 : decode_any W_ac654 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac658 : bv 32 := 0x0940006f.
Lemma F_ac658 : fetch_word Plain.M.loaded_segments (0xac6a4 : word) = Some W_ac658.
Proof. vm_refl. Qed.
Lemma D_ac658 : decode_any W_ac658 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac65c : bv 32 := 0x00875793.
Lemma F_ac65c : fetch_word Plain.M.loaded_segments (0xac6a8 : word) = Some W_ac65c.
Proof. vm_refl. Qed.
Lemma D_ac65c : decode_any W_ac65c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac660 : bv 32 := 0x01075813.
Lemma F_ac660 : fetch_word Plain.M.loaded_segments (0xac6ac : word) = Some W_ac660.
Proof. vm_refl. Qed.
Lemma D_ac660 : decode_any W_ac660 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac664 : bv 32 := 0xffd60613.
Lemma F_ac664 : fetch_word Plain.M.loaded_segments (0xac6b0 : word) = Some W_ac664.
Proof. vm_refl. Qed.
Lemma D_ac664 : decode_any W_ac664 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac668 : bv 32 := 0x00e68023.
Lemma F_ac668 : fetch_word Plain.M.loaded_segments (0xac6b4 : word) = Some W_ac668.
Proof. vm_refl. Qed.
Lemma D_ac668 : decode_any W_ac668 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac66c : bv 32 := 0x00f680a3.
Lemma F_ac66c : fetch_word Plain.M.loaded_segments (0xac6b8 : word) = Some W_ac66c.
Proof. vm_refl. Qed.
Lemma D_ac66c : decode_any W_ac66c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac670 : bv 32 := 0x01068123.
Lemma F_ac670 : fetch_word Plain.M.loaded_segments (0xac6bc : word) = Some W_ac670.
Proof. vm_refl. Qed.
Lemma D_ac670 : decode_any W_ac670 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac674 : bv 32 := 0x00368693.
Lemma F_ac674 : fetch_word Plain.M.loaded_segments (0xac6c0 : word) = Some W_ac674.
Proof. vm_refl. Qed.
Lemma D_ac674 : decode_any W_ac674 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac678 : bv 32 := 0x01058593.
Lemma F_ac678 : fetch_word Plain.M.loaded_segments (0xac6c4 : word) = Some W_ac678.
Proof. vm_refl. Qed.
Lemma D_ac678 : decode_any W_ac678 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac67c : bv 32 := 0x01000793.
Lemma F_ac67c : fetch_word Plain.M.loaded_segments (0xac6c8 : word) = Some W_ac67c.
Proof. vm_refl. Qed.
Lemma D_ac67c : decode_any W_ac67c = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac680 : bv 32 := 0x0187581b.
Lemma F_ac680 : fetch_word Plain.M.loaded_segments (0xac6cc : word) = Some W_ac680.
Proof. vm_refl. Qed.
Lemma D_ac680 : decode_any W_ac680 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac684 : bv 32 := 0xff45a883.
Lemma F_ac684 : fetch_word Plain.M.loaded_segments (0xac6d0 : word) = Some W_ac684.
Proof. vm_refl. Qed.
Lemma D_ac684 : decode_any W_ac684 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac688 : bv 32 := 0xff85a283.
Lemma F_ac688 : fetch_word Plain.M.loaded_segments (0xac6d4 : word) = Some W_ac688.
Proof. vm_refl. Qed.
Lemma D_ac688 : decode_any W_ac688 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac68c : bv 32 := 0xffc5a303.
Lemma F_ac68c : fetch_word Plain.M.loaded_segments (0xac6d8 : word) = Some W_ac68c.
Proof. vm_refl. Qed.
Lemma D_ac68c : decode_any W_ac68c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac690 : bv 32 := 0x0005a703.
Lemma F_ac690 : fetch_word Plain.M.loaded_segments (0xac6dc : word) = Some W_ac690.
Proof. vm_refl. Qed.
Lemma D_ac690 : decode_any W_ac690 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac694 : bv 32 := 0x00889393.
Lemma F_ac694 : fetch_word Plain.M.loaded_segments (0xac6e0 : word) = Some W_ac694.
Proof. vm_refl. Qed.
Lemma D_ac694 : decode_any W_ac694 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac698 : bv 32 := 0x0188d89b.
Lemma F_ac698 : fetch_word Plain.M.loaded_segments (0xac6e4 : word) = Some W_ac698.
Proof. vm_refl. Qed.
Lemma D_ac698 : decode_any W_ac698 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac69c : bv 32 := 0x0103e833.
Lemma F_ac69c : fetch_word Plain.M.loaded_segments (0xac6e8 : word) = Some W_ac69c.
Proof. vm_refl. Qed.
Lemma D_ac69c : decode_any W_ac69c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6a0 : bv 32 := 0x00829393.
Lemma F_ac6a0 : fetch_word Plain.M.loaded_segments (0xac6ec : word) = Some W_ac6a0.
Proof. vm_refl. Qed.
Lemma D_ac6a0 : decode_any W_ac6a0 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6a4 : bv 32 := 0x0182d29b.
Lemma F_ac6a4 : fetch_word Plain.M.loaded_segments (0xac6f0 : word) = Some W_ac6a4.
Proof. vm_refl. Qed.
Lemma D_ac6a4 : decode_any W_ac6a4 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6a8 : bv 32 := 0x0113e8b3.
Lemma F_ac6a8 : fetch_word Plain.M.loaded_segments (0xac6f4 : word) = Some W_ac6a8.
Proof. vm_refl. Qed.
Lemma D_ac6a8 : decode_any W_ac6a8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6ac : bv 32 := 0x00831393.
Lemma F_ac6ac : fetch_word Plain.M.loaded_segments (0xac6f8 : word) = Some W_ac6ac.
Proof. vm_refl. Qed.
Lemma D_ac6ac : decode_any W_ac6ac = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6b0 : bv 32 := 0x0183531b.
Lemma F_ac6b0 : fetch_word Plain.M.loaded_segments (0xac6fc : word) = Some W_ac6b0.
Proof. vm_refl. Qed.
Lemma D_ac6b0 : decode_any W_ac6b0 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6b4 : bv 32 := 0x0053e2b3.
Lemma F_ac6b4 : fetch_word Plain.M.loaded_segments (0xac700 : word) = Some W_ac6b4.
Proof. vm_refl. Qed.
Lemma D_ac6b4 : decode_any W_ac6b4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6b8 : bv 32 := 0x00871393.
Lemma F_ac6b8 : fetch_word Plain.M.loaded_segments (0xac704 : word) = Some W_ac6b8.
Proof. vm_refl. Qed.
Lemma D_ac6b8 : decode_any W_ac6b8 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6bc : bv 32 := 0x0063e333.
Lemma F_ac6bc : fetch_word Plain.M.loaded_segments (0xac708 : word) = Some W_ac6bc.
Proof. vm_refl. Qed.
Lemma D_ac6bc : decode_any W_ac6bc = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6c0 : bv 32 := 0xff060613.
Lemma F_ac6c0 : fetch_word Plain.M.loaded_segments (0xac70c : word) = Some W_ac6c0.
Proof. vm_refl. Qed.
Lemma D_ac6c0 : decode_any W_ac6c0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6c4 : bv 32 := 0x0106a023.
Lemma F_ac6c4 : fetch_word Plain.M.loaded_segments (0xac710 : word) = Some W_ac6c4.
Proof. vm_refl. Qed.
Lemma D_ac6c4 : decode_any W_ac6c4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6c8 : bv 32 := 0x0116a223.
Lemma F_ac6c8 : fetch_word Plain.M.loaded_segments (0xac714 : word) = Some W_ac6c8.
Proof. vm_refl. Qed.
Lemma D_ac6c8 : decode_any W_ac6c8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6cc : bv 32 := 0x0056a423.
Lemma F_ac6cc : fetch_word Plain.M.loaded_segments (0xac718 : word) = Some W_ac6cc.
Proof. vm_refl. Qed.
Lemma D_ac6cc : decode_any W_ac6cc = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6d0 : bv 32 := 0x0066a623.
Lemma F_ac6d0 : fetch_word Plain.M.loaded_segments (0xac71c : word) = Some W_ac6d0.
Proof. vm_refl. Qed.
Lemma D_ac6d0 : decode_any W_ac6d0 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6d4 : bv 32 := 0x01068693.
Lemma F_ac6d4 : fetch_word Plain.M.loaded_segments (0xac720 : word) = Some W_ac6d4.
Proof. vm_refl. Qed.
Lemma D_ac6d4 : decode_any W_ac6d4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6d8 : bv 32 := 0x01058593.
Lemma F_ac6d8 : fetch_word Plain.M.loaded_segments (0xac724 : word) = Some W_ac6d8.
Proof. vm_refl. Qed.
Lemma D_ac6d8 : decode_any W_ac6d8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6dc : bv 32 := 0xfac7e2e3.
Lemma F_ac6dc : fetch_word Plain.M.loaded_segments (0xac728 : word) = Some W_ac6dc.
Proof. vm_refl. Qed.
Lemma D_ac6dc : decode_any W_ac6dc = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6e0 : bv 32 := 0xff358593.
Lemma F_ac6e0 : fetch_word Plain.M.loaded_segments (0xac72c : word) = Some W_ac6e0.
Proof. vm_refl. Qed.
Lemma D_ac6e0 : decode_any W_ac6e0 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6e4 : bv 32 := 0x01000713.
Lemma F_ac6e4 : fetch_word Plain.M.loaded_segments (0xac730 : word) = Some W_ac6e4.
Proof. vm_refl. Qed.
Lemma D_ac6e4 : decode_any W_ac6e4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6e8 : bv 32 := 0xdae66ce3.
Lemma F_ac6e8 : fetch_word Plain.M.loaded_segments (0xac734 : word) = Some W_ac6e8.
Proof. vm_refl. Qed.
Lemma D_ac6e8 : decode_any W_ac6e8 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6ec : bv 32 := 0x0005c703.
Lemma F_ac6ec : fetch_word Plain.M.loaded_segments (0xac738 : word) = Some W_ac6ec.
Proof. vm_refl. Qed.
Lemma D_ac6ec : decode_any W_ac6ec = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6f0 : bv 32 := 0x0015c783.
Lemma F_ac6f0 : fetch_word Plain.M.loaded_segments (0xac73c : word) = Some W_ac6f0.
Proof. vm_refl. Qed.
Lemma D_ac6f0 : decode_any W_ac6f0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6f4 : bv 32 := 0x0025c803.
Lemma F_ac6f4 : fetch_word Plain.M.loaded_segments (0xac740 : word) = Some W_ac6f4.
Proof. vm_refl. Qed.
Lemma D_ac6f4 : decode_any W_ac6f4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6f8 : bv 32 := 0x0035c883.
Lemma F_ac6f8 : fetch_word Plain.M.loaded_segments (0xac744 : word) = Some W_ac6f8.
Proof. vm_refl. Qed.
Lemma D_ac6f8 : decode_any W_ac6f8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac6fc : bv 32 := 0x0045c283.
Lemma F_ac6fc : fetch_word Plain.M.loaded_segments (0xac748 : word) = Some W_ac6fc.
Proof. vm_refl. Qed.
Lemma D_ac6fc : decode_any W_ac6fc = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac700 : bv 32 := 0x0055c303.
Lemma F_ac700 : fetch_word Plain.M.loaded_segments (0xac74c : word) = Some W_ac700.
Proof. vm_refl. Qed.
Lemma D_ac700 : decode_any W_ac700 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac704 : bv 32 := 0x0065c383.
Lemma F_ac704 : fetch_word Plain.M.loaded_segments (0xac750 : word) = Some W_ac704.
Proof. vm_refl. Qed.
Lemma D_ac704 : decode_any W_ac704 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac708 : bv 32 := 0x0075ce03.
Lemma F_ac708 : fetch_word Plain.M.loaded_segments (0xac754 : word) = Some W_ac708.
Proof. vm_refl. Qed.
Lemma D_ac708 : decode_any W_ac708 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac70c : bv 32 := 0x00e68023.
Lemma F_ac70c : fetch_word Plain.M.loaded_segments (0xac758 : word) = Some W_ac70c.
Proof. vm_refl. Qed.
Lemma D_ac70c : decode_any W_ac70c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac710 : bv 32 := 0x00f680a3.
Lemma F_ac710 : fetch_word Plain.M.loaded_segments (0xac75c : word) = Some W_ac710.
Proof. vm_refl. Qed.
Lemma D_ac710 : decode_any W_ac710 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac714 : bv 32 := 0x01068123.
Lemma F_ac714 : fetch_word Plain.M.loaded_segments (0xac760 : word) = Some W_ac714.
Proof. vm_refl. Qed.
Lemma D_ac714 : decode_any W_ac714 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac718 : bv 32 := 0x011681a3.
Lemma F_ac718 : fetch_word Plain.M.loaded_segments (0xac764 : word) = Some W_ac718.
Proof. vm_refl. Qed.
Lemma D_ac718 : decode_any W_ac718 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac71c : bv 32 := 0x0085c703.
Lemma F_ac71c : fetch_word Plain.M.loaded_segments (0xac768 : word) = Some W_ac71c.
Proof. vm_refl. Qed.
Lemma D_ac71c : decode_any W_ac71c = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac720 : bv 32 := 0x0095c783.
Lemma F_ac720 : fetch_word Plain.M.loaded_segments (0xac76c : word) = Some W_ac720.
Proof. vm_refl. Qed.
Lemma D_ac720 : decode_any W_ac720 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac724 : bv 32 := 0x00a5c803.
Lemma F_ac724 : fetch_word Plain.M.loaded_segments (0xac770 : word) = Some W_ac724.
Proof. vm_refl. Qed.
Lemma D_ac724 : decode_any W_ac724 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac728 : bv 32 := 0x00b5c883.
Lemma F_ac728 : fetch_word Plain.M.loaded_segments (0xac774 : word) = Some W_ac728.
Proof. vm_refl. Qed.
Lemma D_ac728 : decode_any W_ac728 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac72c : bv 32 := 0x00568223.
Lemma F_ac72c : fetch_word Plain.M.loaded_segments (0xac778 : word) = Some W_ac72c.
Proof. vm_refl. Qed.
Lemma D_ac72c : decode_any W_ac72c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac730 : bv 32 := 0x006682a3.
Lemma F_ac730 : fetch_word Plain.M.loaded_segments (0xac77c : word) = Some W_ac730.
Proof. vm_refl. Qed.
Lemma D_ac730 : decode_any W_ac730 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac734 : bv 32 := 0x00768323.
Lemma F_ac734 : fetch_word Plain.M.loaded_segments (0xac780 : word) = Some W_ac734.
Proof. vm_refl. Qed.
Lemma D_ac734 : decode_any W_ac734 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac738 : bv 32 := 0x01c683a3.
Lemma F_ac738 : fetch_word Plain.M.loaded_segments (0xac784 : word) = Some W_ac738.
Proof. vm_refl. Qed.
Lemma D_ac738 : decode_any W_ac738 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac73c : bv 32 := 0x00c5c283.
Lemma F_ac73c : fetch_word Plain.M.loaded_segments (0xac788 : word) = Some W_ac73c.
Proof. vm_refl. Qed.
Lemma D_ac73c : decode_any W_ac73c = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac740 : bv 32 := 0x00d5c303.
Lemma F_ac740 : fetch_word Plain.M.loaded_segments (0xac78c : word) = Some W_ac740.
Proof. vm_refl. Qed.
Lemma D_ac740 : decode_any W_ac740 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac744 : bv 32 := 0x00e5c383.
Lemma F_ac744 : fetch_word Plain.M.loaded_segments (0xac790 : word) = Some W_ac744.
Proof. vm_refl. Qed.
Lemma D_ac744 : decode_any W_ac744 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac748 : bv 32 := 0x00f5ce03.
Lemma F_ac748 : fetch_word Plain.M.loaded_segments (0xac794 : word) = Some W_ac748.
Proof. vm_refl. Qed.
Lemma D_ac748 : decode_any W_ac748 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac74c : bv 32 := 0x01058593.
Lemma F_ac74c : fetch_word Plain.M.loaded_segments (0xac798 : word) = Some W_ac74c.
Proof. vm_refl. Qed.
Lemma D_ac74c : decode_any W_ac74c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac750 : bv 32 := 0x00e68423.
Lemma F_ac750 : fetch_word Plain.M.loaded_segments (0xac79c : word) = Some W_ac750.
Proof. vm_refl. Qed.
Lemma D_ac750 : decode_any W_ac750 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac754 : bv 32 := 0x00f684a3.
Lemma F_ac754 : fetch_word Plain.M.loaded_segments (0xac7a0 : word) = Some W_ac754.
Proof. vm_refl. Qed.
Lemma D_ac754 : decode_any W_ac754 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac758 : bv 32 := 0x01068523.
Lemma F_ac758 : fetch_word Plain.M.loaded_segments (0xac7a4 : word) = Some W_ac758.
Proof. vm_refl. Qed.
Lemma D_ac758 : decode_any W_ac758 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac75c : bv 32 := 0x011685a3.
Lemma F_ac75c : fetch_word Plain.M.loaded_segments (0xac7a8 : word) = Some W_ac75c.
Proof. vm_refl. Qed.
Lemma D_ac75c : decode_any W_ac75c = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac760 : bv 32 := 0x01068713.
Lemma F_ac760 : fetch_word Plain.M.loaded_segments (0xac7ac : word) = Some W_ac760.
Proof. vm_refl. Qed.
Lemma D_ac760 : decode_any W_ac760 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac764 : bv 32 := 0x00568623.
Lemma F_ac764 : fetch_word Plain.M.loaded_segments (0xac7b0 : word) = Some W_ac764.
Proof. vm_refl. Qed.
Lemma D_ac764 : decode_any W_ac764 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac768 : bv 32 := 0x006686a3.
Lemma F_ac768 : fetch_word Plain.M.loaded_segments (0xac7b4 : word) = Some W_ac768.
Proof. vm_refl. Qed.
Lemma D_ac768 : decode_any W_ac768 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac76c : bv 32 := 0x00768723.
Lemma F_ac76c : fetch_word Plain.M.loaded_segments (0xac7b8 : word) = Some W_ac76c.
Proof. vm_refl. Qed.
Lemma D_ac76c : decode_any W_ac76c = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac770 : bv 32 := 0x01c687a3.
Lemma F_ac770 : fetch_word Plain.M.loaded_segments (0xac7bc : word) = Some W_ac770.
Proof. vm_refl. Qed.
Lemma D_ac770 : decode_any W_ac770 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac774 : bv 32 := 0x00070693.
Lemma F_ac774 : fetch_word Plain.M.loaded_segments (0xac7c0 : word) = Some W_ac774.
Proof. vm_refl. Qed.
Lemma D_ac774 : decode_any W_ac774 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac778 : bv 32 := 0x00867713.
Lemma F_ac778 : fetch_word Plain.M.loaded_segments (0xac7c4 : word) = Some W_ac778.
Proof. vm_refl. Qed.
Lemma D_ac778 : decode_any W_ac778 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac77c : bv 32 := 0xd20706e3.
Lemma F_ac77c : fetch_word Plain.M.loaded_segments (0xac7c8 : word) = Some W_ac77c.
Proof. vm_refl. Qed.
Lemma D_ac77c : decode_any W_ac77c = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac780 : bv 32 := 0x0005c703.
Lemma F_ac780 : fetch_word Plain.M.loaded_segments (0xac7cc : word) = Some W_ac780.
Proof. vm_refl. Qed.
Lemma D_ac780 : decode_any W_ac780 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac784 : bv 32 := 0x0015c783.
Lemma F_ac784 : fetch_word Plain.M.loaded_segments (0xac7d0 : word) = Some W_ac784.
Proof. vm_refl. Qed.
Lemma D_ac784 : decode_any W_ac784 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac788 : bv 32 := 0x0025c803.
Lemma F_ac788 : fetch_word Plain.M.loaded_segments (0xac7d4 : word) = Some W_ac788.
Proof. vm_refl. Qed.
Lemma D_ac788 : decode_any W_ac788 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac78c : bv 32 := 0x0035c883.
Lemma F_ac78c : fetch_word Plain.M.loaded_segments (0xac7d8 : word) = Some W_ac78c.
Proof. vm_refl. Qed.
Lemma D_ac78c : decode_any W_ac78c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac790 : bv 32 := 0x0045c283.
Lemma F_ac790 : fetch_word Plain.M.loaded_segments (0xac7dc : word) = Some W_ac790.
Proof. vm_refl. Qed.
Lemma D_ac790 : decode_any W_ac790 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac794 : bv 32 := 0x0055c303.
Lemma F_ac794 : fetch_word Plain.M.loaded_segments (0xac7e0 : word) = Some W_ac794.
Proof. vm_refl. Qed.
Lemma D_ac794 : decode_any W_ac794 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac798 : bv 32 := 0x0065c383.
Lemma F_ac798 : fetch_word Plain.M.loaded_segments (0xac7e4 : word) = Some W_ac798.
Proof. vm_refl. Qed.
Lemma D_ac798 : decode_any W_ac798 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac79c : bv 32 := 0x0075ce03.
Lemma F_ac79c : fetch_word Plain.M.loaded_segments (0xac7e8 : word) = Some W_ac79c.
Proof. vm_refl. Qed.
Lemma D_ac79c : decode_any W_ac79c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7a0 : bv 32 := 0x00858593.
Lemma F_ac7a0 : fetch_word Plain.M.loaded_segments (0xac7ec : word) = Some W_ac7a0.
Proof. vm_refl. Qed.
Lemma D_ac7a0 : decode_any W_ac7a0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7a4 : bv 32 := 0x00e68023.
Lemma F_ac7a4 : fetch_word Plain.M.loaded_segments (0xac7f0 : word) = Some W_ac7a4.
Proof. vm_refl. Qed.
Lemma D_ac7a4 : decode_any W_ac7a4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7a8 : bv 32 := 0x00f680a3.
Lemma F_ac7a8 : fetch_word Plain.M.loaded_segments (0xac7f4 : word) = Some W_ac7a8.
Proof. vm_refl. Qed.
Lemma D_ac7a8 : decode_any W_ac7a8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7ac : bv 32 := 0x01068123.
Lemma F_ac7ac : fetch_word Plain.M.loaded_segments (0xac7f8 : word) = Some W_ac7ac.
Proof. vm_refl. Qed.
Lemma D_ac7ac : decode_any W_ac7ac = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7b0 : bv 32 := 0x011681a3.
Lemma F_ac7b0 : fetch_word Plain.M.loaded_segments (0xac7fc : word) = Some W_ac7b0.
Proof. vm_refl. Qed.
Lemma D_ac7b0 : decode_any W_ac7b0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7b4 : bv 32 := 0x00868713.
Lemma F_ac7b4 : fetch_word Plain.M.loaded_segments (0xac800 : word) = Some W_ac7b4.
Proof. vm_refl. Qed.
Lemma D_ac7b4 : decode_any W_ac7b4 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7b8 : bv 32 := 0x00568223.
Lemma F_ac7b8 : fetch_word Plain.M.loaded_segments (0xac804 : word) = Some W_ac7b8.
Proof. vm_refl. Qed.
Lemma D_ac7b8 : decode_any W_ac7b8 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7bc : bv 32 := 0x006682a3.
Lemma F_ac7bc : fetch_word Plain.M.loaded_segments (0xac808 : word) = Some W_ac7bc.
Proof. vm_refl. Qed.
Lemma D_ac7bc : decode_any W_ac7bc = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7c0 : bv 32 := 0x00768323.
Lemma F_ac7c0 : fetch_word Plain.M.loaded_segments (0xac80c : word) = Some W_ac7c0.
Proof. vm_refl. Qed.
Lemma D_ac7c0 : decode_any W_ac7c0 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7c4 : bv 32 := 0x01c683a3.
Lemma F_ac7c4 : fetch_word Plain.M.loaded_segments (0xac810 : word) = Some W_ac7c4.
Proof. vm_refl. Qed.
Lemma D_ac7c4 : decode_any W_ac7c4 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7c8 : bv 32 := 0x00070693.
Lemma F_ac7c8 : fetch_word Plain.M.loaded_segments (0xac814 : word) = Some W_ac7c8.
Proof. vm_refl. Qed.
Lemma D_ac7c8 : decode_any W_ac7c8 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7cc : bv 32 := 0x00467713.
Lemma F_ac7cc : fetch_word Plain.M.loaded_segments (0xac818 : word) = Some W_ac7cc.
Proof. vm_refl. Qed.
Lemma D_ac7cc : decode_any W_ac7cc = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7d0 : bv 32 := 0x02070863.
Lemma F_ac7d0 : fetch_word Plain.M.loaded_segments (0xac81c : word) = Some W_ac7d0.
Proof. vm_refl. Qed.
Lemma D_ac7d0 : decode_any W_ac7d0 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7d4 : bv 32 := 0x0005c703.
Lemma F_ac7d4 : fetch_word Plain.M.loaded_segments (0xac820 : word) = Some W_ac7d4.
Proof. vm_refl. Qed.
Lemma D_ac7d4 : decode_any W_ac7d4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7d8 : bv 32 := 0x0015c783.
Lemma F_ac7d8 : fetch_word Plain.M.loaded_segments (0xac824 : word) = Some W_ac7d8.
Proof. vm_refl. Qed.
Lemma D_ac7d8 : decode_any W_ac7d8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7dc : bv 32 := 0x0025c803.
Lemma F_ac7dc : fetch_word Plain.M.loaded_segments (0xac828 : word) = Some W_ac7dc.
Proof. vm_refl. Qed.
Lemma D_ac7dc : decode_any W_ac7dc = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7e0 : bv 32 := 0x0035c883.
Lemma F_ac7e0 : fetch_word Plain.M.loaded_segments (0xac82c : word) = Some W_ac7e0.
Proof. vm_refl. Qed.
Lemma D_ac7e0 : decode_any W_ac7e0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7e4 : bv 32 := 0x00458593.
Lemma F_ac7e4 : fetch_word Plain.M.loaded_segments (0xac830 : word) = Some W_ac7e4.
Proof. vm_refl. Qed.
Lemma D_ac7e4 : decode_any W_ac7e4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7e8 : bv 32 := 0x00468293.
Lemma F_ac7e8 : fetch_word Plain.M.loaded_segments (0xac834 : word) = Some W_ac7e8.
Proof. vm_refl. Qed.
Lemma D_ac7e8 : decode_any W_ac7e8 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7ec : bv 32 := 0x00e68023.
Lemma F_ac7ec : fetch_word Plain.M.loaded_segments (0xac838 : word) = Some W_ac7ec.
Proof. vm_refl. Qed.
Lemma D_ac7ec : decode_any W_ac7ec = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7f0 : bv 32 := 0x00f680a3.
Lemma F_ac7f0 : fetch_word Plain.M.loaded_segments (0xac83c : word) = Some W_ac7f0.
Proof. vm_refl. Qed.
Lemma D_ac7f0 : decode_any W_ac7f0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7f4 : bv 32 := 0x01068123.
Lemma F_ac7f4 : fetch_word Plain.M.loaded_segments (0xac840 : word) = Some W_ac7f4.
Proof. vm_refl. Qed.
Lemma D_ac7f4 : decode_any W_ac7f4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7f8 : bv 32 := 0x011681a3.
Lemma F_ac7f8 : fetch_word Plain.M.loaded_segments (0xac844 : word) = Some W_ac7f8.
Proof. vm_refl. Qed.
Lemma D_ac7f8 : decode_any W_ac7f8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7fc : bv 32 := 0x00028693.
Lemma F_ac7fc : fetch_word Plain.M.loaded_segments (0xac848 : word) = Some W_ac7fc.
Proof. vm_refl. Qed.
Lemma D_ac7fc : decode_any W_ac7fc = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac800 : bv 32 := 0x00267713.
Lemma F_ac800 : fetch_word Plain.M.loaded_segments (0xac84c : word) = Some W_ac800.
Proof. vm_refl. Qed.
Lemma D_ac800 : decode_any W_ac800 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac804 : bv 32 := 0x00071863.
Lemma F_ac804 : fetch_word Plain.M.loaded_segments (0xac850 : word) = Some W_ac804.
Proof. vm_refl. Qed.
Lemma D_ac804 : decode_any W_ac804 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac808 : bv 32 := 0x00167613.
Lemma F_ac808 : fetch_word Plain.M.loaded_segments (0xac854 : word) = Some W_ac808.
Proof. vm_refl. Qed.
Lemma D_ac808 : decode_any W_ac808 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac80c : bv 32 := 0x02061663.
Lemma F_ac80c : fetch_word Plain.M.loaded_segments (0xac858 : word) = Some W_ac80c.
Proof. vm_refl. Qed.
Lemma D_ac80c : decode_any W_ac80c = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac810 : bv 32 := 0x00008067.
Lemma F_ac810 : fetch_word Plain.M.loaded_segments (0xac85c : word) = Some W_ac810.
Proof. vm_refl. Qed.
Lemma D_ac810 : decode_any W_ac810 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac814 : bv 32 := 0x0005c703.
Lemma F_ac814 : fetch_word Plain.M.loaded_segments (0xac860 : word) = Some W_ac814.
Proof. vm_refl. Qed.
Lemma D_ac814 : decode_any W_ac814 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac818 : bv 32 := 0x0015c783.
Lemma F_ac818 : fetch_word Plain.M.loaded_segments (0xac864 : word) = Some W_ac818.
Proof. vm_refl. Qed.
Lemma D_ac818 : decode_any W_ac818 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac81c : bv 32 := 0x00258593.
Lemma F_ac81c : fetch_word Plain.M.loaded_segments (0xac868 : word) = Some W_ac81c.
Proof. vm_refl. Qed.
Lemma D_ac81c : decode_any W_ac81c = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac820 : bv 32 := 0x00268813.
Lemma F_ac820 : fetch_word Plain.M.loaded_segments (0xac86c : word) = Some W_ac820.
Proof. vm_refl. Qed.
Lemma D_ac820 : decode_any W_ac820 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac824 : bv 32 := 0x00e68023.
Lemma F_ac824 : fetch_word Plain.M.loaded_segments (0xac870 : word) = Some W_ac824.
Proof. vm_refl. Qed.
Lemma D_ac824 : decode_any W_ac824 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac828 : bv 32 := 0x00f680a3.
Lemma F_ac828 : fetch_word Plain.M.loaded_segments (0xac874 : word) = Some W_ac828.
Proof. vm_refl. Qed.
Lemma D_ac828 : decode_any W_ac828 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac82c : bv 32 := 0x00080693.
Lemma F_ac82c : fetch_word Plain.M.loaded_segments (0xac878 : word) = Some W_ac82c.
Proof. vm_refl. Qed.
Lemma D_ac82c : decode_any W_ac82c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac830 : bv 32 := 0x00167613.
Lemma F_ac830 : fetch_word Plain.M.loaded_segments (0xac87c : word) = Some W_ac830.
Proof. vm_refl. Qed.
Lemma D_ac830 : decode_any W_ac830 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac834 : bv 32 := 0xfc060ee3.
Lemma F_ac834 : fetch_word Plain.M.loaded_segments (0xac880 : word) = Some W_ac834.
Proof. vm_refl. Qed.
Lemma D_ac834 : decode_any W_ac834 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac838 : bv 32 := 0x0005c583.
Lemma F_ac838 : fetch_word Plain.M.loaded_segments (0xac884 : word) = Some W_ac838.
Proof. vm_refl. Qed.
Lemma D_ac838 : decode_any W_ac838 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac83c : bv 32 := 0x00b68023.
Lemma F_ac83c : fetch_word Plain.M.loaded_segments (0xac888 : word) = Some W_ac83c.
Proof. vm_refl. Qed.
Lemma D_ac83c : decode_any W_ac83c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac840 : bv 32 := 0x00008067.
Lemma F_ac840 : fetch_word Plain.M.loaded_segments (0xac88c : word) = Some W_ac840.
Proof. vm_refl. Qed.
Lemma D_ac840 : decode_any W_ac840 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9c0 : bv 32 := 0x0e060a63.
Lemma F_ac9c0 : fetch_word Plain.M.loaded_segments (0xaca0c : word) = Some W_ac9c0.
Proof. vm_refl. Qed.
Lemma D_ac9c0 : decode_any W_ac9c0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9c4 : bv 32 := 0x00b50023.
Lemma F_ac9c4 : fetch_word Plain.M.loaded_segments (0xaca10 : word) = Some W_ac9c4.
Proof. vm_refl. Qed.
Lemma D_ac9c4 : decode_any W_ac9c4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9c8 : bv 32 := 0x00c506b3.
Lemma F_ac9c8 : fetch_word Plain.M.loaded_segments (0xaca14 : word) = Some W_ac9c8.
Proof. vm_refl. Qed.
Lemma D_ac9c8 : decode_any W_ac9c8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9cc : bv 32 := 0x00300713.
Lemma F_ac9cc : fetch_word Plain.M.loaded_segments (0xaca18 : word) = Some W_ac9cc.
Proof. vm_refl. Qed.
Lemma D_ac9cc : decode_any W_ac9cc = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9d0 : bv 32 := 0xfeb68fa3.
Lemma F_ac9d0 : fetch_word Plain.M.loaded_segments (0xaca1c : word) = Some W_ac9d0.
Proof. vm_refl. Qed.
Lemma D_ac9d0 : decode_any W_ac9d0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9d4 : bv 32 := 0x0ee66063.
Lemma F_ac9d4 : fetch_word Plain.M.loaded_segments (0xaca20 : word) = Some W_ac9d4.
Proof. vm_refl. Qed.
Lemma D_ac9d4 : decode_any W_ac9d4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9d8 : bv 32 := 0x00b500a3.
Lemma F_ac9d8 : fetch_word Plain.M.loaded_segments (0xaca24 : word) = Some W_ac9d8.
Proof. vm_refl. Qed.
Lemma D_ac9d8 : decode_any W_ac9d8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9dc : bv 32 := 0x00b50123.
Lemma F_ac9dc : fetch_word Plain.M.loaded_segments (0xaca28 : word) = Some W_ac9dc.
Proof. vm_refl. Qed.
Lemma D_ac9dc : decode_any W_ac9dc = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9e0 : bv 32 := 0x00700713.
Lemma F_ac9e0 : fetch_word Plain.M.loaded_segments (0xaca2c : word) = Some W_ac9e0.
Proof. vm_refl. Qed.
Lemma D_ac9e0 : decode_any W_ac9e0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9e4 : bv 32 := 0xfeb68ea3.
Lemma F_ac9e4 : fetch_word Plain.M.loaded_segments (0xaca30 : word) = Some W_ac9e4.
Proof. vm_refl. Qed.
Lemma D_ac9e4 : decode_any W_ac9e4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9e8 : bv 32 := 0xfeb68f23.
Lemma F_ac9e8 : fetch_word Plain.M.loaded_segments (0xaca34 : word) = Some W_ac9e8.
Proof. vm_refl. Qed.
Lemma D_ac9e8 : decode_any W_ac9e8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9ec : bv 32 := 0x0ce66463.
Lemma F_ac9ec : fetch_word Plain.M.loaded_segments (0xaca38 : word) = Some W_ac9ec.
Proof. vm_refl. Qed.
Lemma D_ac9ec : decode_any W_ac9ec = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9f0 : bv 32 := 0x00b501a3.
Lemma F_ac9f0 : fetch_word Plain.M.loaded_segments (0xaca3c : word) = Some W_ac9f0.
Proof. vm_refl. Qed.
Lemma D_ac9f0 : decode_any W_ac9f0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9f4 : bv 32 := 0x00900793.
Lemma F_ac9f4 : fetch_word Plain.M.loaded_segments (0xaca40 : word) = Some W_ac9f4.
Proof. vm_refl. Qed.
Lemma D_ac9f4 : decode_any W_ac9f4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9f8 : bv 32 := 0xfeb68e23.
Lemma F_ac9f8 : fetch_word Plain.M.loaded_segments (0xaca44 : word) = Some W_ac9f8.
Proof. vm_refl. Qed.
Lemma D_ac9f8 : decode_any W_ac9f8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac9fc : bv 32 := 0x0af66c63.
Lemma F_ac9fc : fetch_word Plain.M.loaded_segments (0xaca48 : word) = Some W_ac9fc.
Proof. vm_refl. Qed.
Lemma D_ac9fc : decode_any W_ac9fc = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca00 : bv 32 := 0x40a006bb.
Lemma F_aca00 : fetch_word Plain.M.loaded_segments (0xaca4c : word) = Some W_aca00.
Proof. vm_refl. Qed.
Lemma D_aca00 : decode_any W_aca00 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca04 : bv 32 := 0x03859813.
Lemma F_aca04 : fetch_word Plain.M.loaded_segments (0xaca50 : word) = Some W_aca04.
Proof. vm_refl. Qed.
Lemma D_aca04 : decode_any W_aca04 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca08 : bv 32 := 0x101015b7.
Lemma F_aca08 : fetch_word Plain.M.loaded_segments (0xaca54 : word) = Some W_aca08.
Proof. vm_refl. Qed.
Lemma D_aca08 : decode_any W_aca08 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca0c : bv 32 := 0x0036f693.
Lemma F_aca0c : fetch_word Plain.M.loaded_segments (0xaca58 : word) = Some W_aca0c.
Proof. vm_refl. Qed.
Lemma D_aca0c : decode_any W_aca0c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca10 : bv 32 := 0x00459713.
Lemma F_aca10 : fetch_word Plain.M.loaded_segments (0xaca5c : word) = Some W_aca10.
Proof. vm_refl. Qed.
Lemma D_aca10 : decode_any W_aca10 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca14 : bv 32 := 0x40d60633.
Lemma F_aca14 : fetch_word Plain.M.loaded_segments (0xaca60 : word) = Some W_aca14.
Proof. vm_refl. Qed.
Lemma D_aca14 : decode_any W_aca14 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca18 : bv 32 := 0x00d505b3.
Lemma F_aca18 : fetch_word Plain.M.loaded_segments (0xaca64 : word) = Some W_aca18.
Proof. vm_refl. Qed.
Lemma D_aca18 : decode_any W_aca18 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca1c : bv 32 := 0x10070693.
Lemma F_aca1c : fetch_word Plain.M.loaded_segments (0xaca68 : word) = Some W_aca1c.
Proof. vm_refl. Qed.
Lemma D_aca1c : decode_any W_aca1c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca20 : bv 32 := 0xffc67713.
Lemma F_aca20 : fetch_word Plain.M.loaded_segments (0xaca6c : word) = Some W_aca20.
Proof. vm_refl. Qed.
Lemma D_aca20 : decode_any W_aca20 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca24 : bv 32 := 0x02d83633.
Lemma F_aca24 : fetch_word Plain.M.loaded_segments (0xaca70 : word) = Some W_aca24.
Proof. vm_refl. Qed.
Lemma D_aca24 : decode_any W_aca24 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca28 : bv 32 := 0x00c5a023.
Lemma F_aca28 : fetch_word Plain.M.loaded_segments (0xaca74 : word) = Some W_aca28.
Proof. vm_refl. Qed.
Lemma D_aca28 : decode_any W_aca28 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca2c : bv 32 := 0x00e586b3.
Lemma F_aca2c : fetch_word Plain.M.loaded_segments (0xaca78 : word) = Some W_aca2c.
Proof. vm_refl. Qed.
Lemma D_aca2c : decode_any W_aca2c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca30 : bv 32 := 0xfec6ae23.
Lemma F_aca30 : fetch_word Plain.M.loaded_segments (0xaca7c : word) = Some W_aca30.
Proof. vm_refl. Qed.
Lemma D_aca30 : decode_any W_aca30 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca34 : bv 32 := 0x08f76063.
Lemma F_aca34 : fetch_word Plain.M.loaded_segments (0xaca80 : word) = Some W_aca34.
Proof. vm_refl. Qed.
Lemma D_aca34 : decode_any W_aca34 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca38 : bv 32 := 0x00c5a223.
Lemma F_aca38 : fetch_word Plain.M.loaded_segments (0xaca84 : word) = Some W_aca38.
Proof. vm_refl. Qed.
Lemma D_aca38 : decode_any W_aca38 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca3c : bv 32 := 0x00c5a423.
Lemma F_aca3c : fetch_word Plain.M.loaded_segments (0xaca88 : word) = Some W_aca3c.
Proof. vm_refl. Qed.
Lemma D_aca3c : decode_any W_aca3c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca40 : bv 32 := 0x01900793.
Lemma F_aca40 : fetch_word Plain.M.loaded_segments (0xaca8c : word) = Some W_aca40.
Proof. vm_refl. Qed.
Lemma D_aca40 : decode_any W_aca40 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca44 : bv 32 := 0xfec6aa23.
Lemma F_aca44 : fetch_word Plain.M.loaded_segments (0xaca90 : word) = Some W_aca44.
Proof. vm_refl. Qed.
Lemma D_aca44 : decode_any W_aca44 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca48 : bv 32 := 0xfec6ac23.
Lemma F_aca48 : fetch_word Plain.M.loaded_segments (0xaca94 : word) = Some W_aca48.
Proof. vm_refl. Qed.
Lemma D_aca48 : decode_any W_aca48 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca4c : bv 32 := 0x06f76463.
Lemma F_aca4c : fetch_word Plain.M.loaded_segments (0xaca98 : word) = Some W_aca4c.
Proof. vm_refl. Qed.
Lemma D_aca4c : decode_any W_aca4c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca50 : bv 32 := 0x00c5a623.
Lemma F_aca50 : fetch_word Plain.M.loaded_segments (0xaca9c : word) = Some W_aca50.
Proof. vm_refl. Qed.
Lemma D_aca50 : decode_any W_aca50 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca54 : bv 32 := 0x00c5a823.
Lemma F_aca54 : fetch_word Plain.M.loaded_segments (0xacaa0 : word) = Some W_aca54.
Proof. vm_refl. Qed.
Lemma D_aca54 : decode_any W_aca54 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca58 : bv 32 := 0x00c5aa23.
Lemma F_aca58 : fetch_word Plain.M.loaded_segments (0xacaa4 : word) = Some W_aca58.
Proof. vm_refl. Qed.
Lemma D_aca58 : decode_any W_aca58 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca5c : bv 32 := 0x00c5ac23.
Lemma F_aca5c : fetch_word Plain.M.loaded_segments (0xacaa8 : word) = Some W_aca5c.
Proof. vm_refl. Qed.
Lemma D_aca5c : decode_any W_aca5c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca60 : bv 32 := 0x0045f793.
Lemma F_aca60 : fetch_word Plain.M.loaded_segments (0xacaac : word) = Some W_aca60.
Proof. vm_refl. Qed.
Lemma D_aca60 : decode_any W_aca60 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca64 : bv 32 := 0x02000813.
Lemma F_aca64 : fetch_word Plain.M.loaded_segments (0xacab0 : word) = Some W_aca64.
Proof. vm_refl. Qed.
Lemma D_aca64 : decode_any W_aca64 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca68 : bv 32 := 0x01878793.
Lemma F_aca68 : fetch_word Plain.M.loaded_segments (0xacab4 : word) = Some W_aca68.
Proof. vm_refl. Qed.
Lemma D_aca68 : decode_any W_aca68 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca6c : bv 32 := 0x40f70733.
Lemma F_aca6c : fetch_word Plain.M.loaded_segments (0xacab8 : word) = Some W_aca6c.
Proof. vm_refl. Qed.
Lemma D_aca6c : decode_any W_aca6c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca70 : bv 32 := 0xfec6a223.
Lemma F_aca70 : fetch_word Plain.M.loaded_segments (0xacabc : word) = Some W_aca70.
Proof. vm_refl. Qed.
Lemma D_aca70 : decode_any W_aca70 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca74 : bv 32 := 0xfec6a423.
Lemma F_aca74 : fetch_word Plain.M.loaded_segments (0xacac0 : word) = Some W_aca74.
Proof. vm_refl. Qed.
Lemma D_aca74 : decode_any W_aca74 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca78 : bv 32 := 0xfec6a623.
Lemma F_aca78 : fetch_word Plain.M.loaded_segments (0xacac4 : word) = Some W_aca78.
Proof. vm_refl. Qed.
Lemma D_aca78 : decode_any W_aca78 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca7c : bv 32 := 0xfec6a823.
Lemma F_aca7c : fetch_word Plain.M.loaded_segments (0xacac8 : word) = Some W_aca7c.
Proof. vm_refl. Qed.
Lemma D_aca7c : decode_any W_aca7c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca80 : bv 32 := 0x03076a63.
Lemma F_aca80 : fetch_word Plain.M.loaded_segments (0xacacc : word) = Some W_aca80.
Proof. vm_refl. Qed.
Lemma D_aca80 : decode_any W_aca80 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca84 : bv 32 := 0x02061613.
Lemma F_aca84 : fetch_word Plain.M.loaded_segments (0xacad0 : word) = Some W_aca84.
Proof. vm_refl. Qed.
Lemma D_aca84 : decode_any W_aca84 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca88 : bv 32 := 0x00f585b3.
Lemma F_aca88 : fetch_word Plain.M.loaded_segments (0xacad4 : word) = Some W_aca88.
Proof. vm_refl. Qed.
Lemma D_aca88 : decode_any W_aca88 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca8c : bv 32 := 0x02065693.
Lemma F_aca8c : fetch_word Plain.M.loaded_segments (0xacad8 : word) = Some W_aca8c.
Proof. vm_refl. Qed.
Lemma D_aca8c : decode_any W_aca8c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca90 : bv 32 := 0x00d66633.
Lemma F_aca90 : fetch_word Plain.M.loaded_segments (0xacadc : word) = Some W_aca90.
Proof. vm_refl. Qed.
Lemma D_aca90 : decode_any W_aca90 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca94 : bv 32 := 0x01f00693.
Lemma F_aca94 : fetch_word Plain.M.loaded_segments (0xacae0 : word) = Some W_aca94.
Proof. vm_refl. Qed.
Lemma D_aca94 : decode_any W_aca94 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca98 : bv 32 := 0x00c5b023.
Lemma F_aca98 : fetch_word Plain.M.loaded_segments (0xacae4 : word) = Some W_aca98.
Proof. vm_refl. Qed.
Lemma D_aca98 : decode_any W_aca98 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aca9c : bv 32 := 0x00c5b423.
Lemma F_aca9c : fetch_word Plain.M.loaded_segments (0xacae8 : word) = Some W_aca9c.
Proof. vm_refl. Qed.
Lemma D_aca9c : decode_any W_aca9c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_acaa0 : bv 32 := 0x00c5b823.
Lemma F_acaa0 : fetch_word Plain.M.loaded_segments (0xacaec : word) = Some W_acaa0.
Proof. vm_refl. Qed.
Lemma D_acaa0 : decode_any W_acaa0 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_acaa4 : bv 32 := 0x00c5bc23.
Lemma F_acaa4 : fetch_word Plain.M.loaded_segments (0xacaf0 : word) = Some W_acaa4.
Proof. vm_refl. Qed.
Lemma D_acaa4 : decode_any W_acaa4 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_acaa8 : bv 32 := 0xfe070713.
Lemma F_acaa8 : fetch_word Plain.M.loaded_segments (0xacaf4 : word) = Some W_acaa8.
Proof. vm_refl. Qed.
Lemma D_acaa8 : decode_any W_acaa8 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_acaac : bv 32 := 0x02058593.
Lemma F_acaac : fetch_word Plain.M.loaded_segments (0xacaf8 : word) = Some W_acaac.
Proof. vm_refl. Qed.
Lemma D_acaac : decode_any W_acaac = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_acab0 : bv 32 := 0xfee6e4e3.
Lemma F_acab0 : fetch_word Plain.M.loaded_segments (0xacafc : word) = Some W_acab0.
Proof. vm_refl. Qed.
Lemma D_acab0 : decode_any W_acab0 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_acab4 : bv 32 := 0x00008067.
Lemma F_acab4 : fetch_word Plain.M.loaded_segments (0xacb00 : word) = Some W_acab4.
Proof. vm_refl. Qed.
Lemma D_acab4 : decode_any W_acab4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_acea4 : bv 32 := 0x00757593.
Lemma F_acea4 : fetch_word Plain.M.loaded_segments (0xacef0 : word) = Some W_acea4.
Proof. vm_refl. Qed.
Lemma D_acea4 : decode_any W_acea4 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_acea8 : bv 32 := 0x00050613.
Lemma F_acea8 : fetch_word Plain.M.loaded_segments (0xacef4 : word) = Some W_acea8.
Proof. vm_refl. Qed.
Lemma D_acea8 : decode_any W_acea8 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aceac : bv 32 := 0x02058a63.
Lemma F_aceac : fetch_word Plain.M.loaded_segments (0xacef8 : word) = Some W_aceac.
Proof. vm_refl. Qed.
Lemma D_aceac : decode_any W_aceac = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_aceb0 : bv 32 := 0x00054583.
Lemma F_aceb0 : fetch_word Plain.M.loaded_segments (0xacefc : word) = Some W_aceb0.
Proof. vm_refl. Qed.
Lemma D_aceb0 : decode_any W_aceb0 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aceb4 : bv 32 := 0x06058c63.
Lemma F_aceb4 : fetch_word Plain.M.loaded_segments (0xacf00 : word) = Some W_aceb4.
Proof. vm_refl. Qed.
Lemma D_aceb4 : decode_any W_aceb4 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_aceb8 : bv 32 := 0x00150613.
Lemma F_aceb8 : fetch_word Plain.M.loaded_segments (0xacf04 : word) = Some W_aceb8.
Proof. vm_refl. Qed.
Lemma D_aceb8 : decode_any W_aceb8 = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_acebc : bv 32 := 0x00050593.
Lemma F_acebc : fetch_word Plain.M.loaded_segments (0xacf08 : word) = Some W_acebc.
Proof. vm_refl. Qed.
Lemma D_acebc : decode_any W_acebc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_acec0 : bv 32 := 0x00158693.
Lemma F_acec0 : fetch_word Plain.M.loaded_segments (0xacf0c : word) = Some W_acec0.
Proof. vm_refl. Qed.
Lemma D_acec0 : decode_any W_acec0 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_acec4 : bv 32 := 0x0076f693.
Lemma F_acec4 : fetch_word Plain.M.loaded_segments (0xacf10 : word) = Some W_acec4.
Proof. vm_refl. Qed.
Lemma D_acec4 : decode_any W_acec4 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_acec8 : bv 32 := 0x00068c63.
Lemma F_acec8 : fetch_word Plain.M.loaded_segments (0xacf14 : word) = Some W_acec8.
Proof. vm_refl. Qed.
Lemma D_acec8 : decode_any W_acec8 = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_acecc : bv 32 := 0x00064683.
Lemma F_acecc : fetch_word Plain.M.loaded_segments (0xacf18 : word) = Some W_acecc.
Proof. vm_refl. Qed.
Lemma D_acecc : decode_any W_acecc = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aced0 : bv 32 := 0x00160613.
Lemma F_aced0 : fetch_word Plain.M.loaded_segments (0xacf1c : word) = Some W_aced0.
Proof. vm_refl. Qed.
Lemma D_aced0 : decode_any W_aced0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_aced4 : bv 32 := 0x00158593.
Lemma F_aced4 : fetch_word Plain.M.loaded_segments (0xacf20 : word) = Some W_aced4.
Proof. vm_refl. Qed.
Lemma D_aced4 : decode_any W_aced4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_aced8 : bv 32 := 0xfe0694e3.
Lemma F_aced8 : fetch_word Plain.M.loaded_segments (0xacf24 : word) = Some W_aced8.
Proof. vm_refl. Qed.
Lemma D_aced8 : decode_any W_aced8 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_acedc : bv 32 := 0x0480006f.
Lemma F_acedc : fetch_word Plain.M.loaded_segments (0xacf28 : word) = Some W_acedc.
Proof. vm_refl. Qed.
Lemma D_acedc : decode_any W_acedc = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_acee0 : bv 32 := 0xfff67597.
Lemma F_acee0 : fetch_word Plain.M.loaded_segments (0xacf2c : word) = Some W_acee0.
Proof. vm_refl. Qed.
Lemma D_acee0 : decode_any W_acee0 = Some (Auipc 11 1048423, 4%Z).
Proof. vm_refl. Qed.

Definition W_acee4 : bv 32 := 0xfff67717.
Lemma F_acee4 : fetch_word Plain.M.loaded_segments (0xacf30 : word) = Some W_acee4.
Proof. vm_refl. Qed.
Lemma D_acee4 : decode_any W_acee4 = Some (Auipc 14 1048423, 4%Z).
Proof. vm_refl. Qed.

Definition W_acee8 : bv 32 := 0x8245b683.
Lemma F_acee8 : fetch_word Plain.M.loaded_segments (0xacf34 : word) = Some W_acee8.
Proof. vm_refl. Qed.
Lemma D_acee8 : decode_any W_acee8 = Some (Load SZ8 true 13 11 2084, 4%Z).
Proof. vm_refl. Qed.

Definition W_aceec : bv 32 := 0x81073703.
Lemma F_aceec : fetch_word Plain.M.loaded_segments (0xacf38 : word) = Some W_aceec.
Proof. vm_refl. Qed.
Lemma D_aceec : decode_any W_aceec = Some (Load SZ8 true 14 14 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_acef0 : bv 32 := 0xff760593.
Lemma F_acef0 : fetch_word Plain.M.loaded_segments (0xacf3c : word) = Some W_acef0.
Proof. vm_refl. Qed.
Lemma D_acef0 : decode_any W_acef0 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_acef4 : bv 32 := 0xff860613.
Lemma F_acef4 : fetch_word Plain.M.loaded_segments (0xacf40 : word) = Some W_acef4.
Proof. vm_refl. Qed.
Lemma D_acef4 : decode_any W_acef4 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_acef8 : bv 32 := 0x00863783.
Lemma F_acef8 : fetch_word Plain.M.loaded_segments (0xacf44 : word) = Some W_acef8.
Proof. vm_refl. Qed.
Lemma D_acef8 : decode_any W_acef8 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_acefc : bv 32 := 0x00860613.
Lemma F_acefc : fetch_word Plain.M.loaded_segments (0xacf48 : word) = Some W_acefc.
Proof. vm_refl. Qed.
Lemma D_acefc : decode_any W_acefc = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf00 : bv 32 := 0x40f68833.
Lemma F_acf00 : fetch_word Plain.M.loaded_segments (0xacf4c : word) = Some W_acf00.
Proof. vm_refl. Qed.
Lemma D_acf00 : decode_any W_acf00 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf04 : bv 32 := 0x00f867b3.
Lemma F_acf04 : fetch_word Plain.M.loaded_segments (0xacf50 : word) = Some W_acf04.
Proof. vm_refl. Qed.
Lemma D_acf04 : decode_any W_acf04 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf08 : bv 32 := 0x00e7f7b3.
Lemma F_acf08 : fetch_word Plain.M.loaded_segments (0xacf54 : word) = Some W_acf08.
Proof. vm_refl. Qed.
Lemma D_acf08 : decode_any W_acf08 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf0c : bv 32 := 0x00858593.
Lemma F_acf0c : fetch_word Plain.M.loaded_segments (0xacf58 : word) = Some W_acf0c.
Proof. vm_refl. Qed.
Lemma D_acf0c : decode_any W_acf0c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf10 : bv 32 := 0xfee784e3.
Lemma F_acf10 : fetch_word Plain.M.loaded_segments (0xacf5c : word) = Some W_acf10.
Proof. vm_refl. Qed.
Lemma D_acf10 : decode_any W_acf10 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf14 : bv 32 := 0x00064683.
Lemma F_acf14 : fetch_word Plain.M.loaded_segments (0xacf60 : word) = Some W_acf14.
Proof. vm_refl. Qed.
Lemma D_acf14 : decode_any W_acf14 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf18 : bv 32 := 0x00160613.
Lemma F_acf18 : fetch_word Plain.M.loaded_segments (0xacf64 : word) = Some W_acf18.
Proof. vm_refl. Qed.
Lemma D_acf18 : decode_any W_acf18 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf1c : bv 32 := 0x00158593.
Lemma F_acf1c : fetch_word Plain.M.loaded_segments (0xacf68 : word) = Some W_acf1c.
Proof. vm_refl. Qed.
Lemma D_acf1c : decode_any W_acf1c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf20 : bv 32 := 0xfe069ae3.
Lemma F_acf20 : fetch_word Plain.M.loaded_segments (0xacf6c : word) = Some W_acf20.
Proof. vm_refl. Qed.
Lemma D_acf20 : decode_any W_acf20 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf24 : bv 32 := 0x40a58533.
Lemma F_acf24 : fetch_word Plain.M.loaded_segments (0xacf70 : word) = Some W_acf24.
Proof. vm_refl. Qed.
Lemma D_acf24 : decode_any W_acf24 = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf28 : bv 32 := 0x00008067.
Lemma F_acf28 : fetch_word Plain.M.loaded_segments (0xacf74 : word) = Some W_acf28.
Proof. vm_refl. Qed.
Lemma D_acf28 : decode_any W_acf28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf2c : bv 32 := 0x40a50533.
Lemma F_acf2c : fetch_word Plain.M.loaded_segments (0xacf78 : word) = Some W_acf2c.
Proof. vm_refl. Qed.
Lemma D_acf2c : decode_any W_acf2c = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf30 : bv 32 := 0x00008067.
Lemma F_acf30 : fetch_word Plain.M.loaded_segments (0xacf7c : word) = Some W_acf30.
Proof. vm_refl. Qed.
Lemma D_acf30 : decode_any W_acf30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf34 : bv 32 := 0xfe010113.
Lemma F_acf34 : fetch_word Plain.M.loaded_segments (0xacf80 : word) = Some W_acf34.
Proof. vm_refl. Qed.
Lemma D_acf34 : decode_any W_acf34 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf38 : bv 32 := 0x00113c23.
Lemma F_acf38 : fetch_word Plain.M.loaded_segments (0xacf84 : word) = Some W_acf38.
Proof. vm_refl. Qed.
Lemma D_acf38 : decode_any W_acf38 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf3c : bv 32 := 0x00813823.
Lemma F_acf3c : fetch_word Plain.M.loaded_segments (0xacf88 : word) = Some W_acf3c.
Proof. vm_refl. Qed.
Lemma D_acf3c : decode_any W_acf3c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf40 : bv 32 := 0x00913423.
Lemma F_acf40 : fetch_word Plain.M.loaded_segments (0xacf8c : word) = Some W_acf40.
Proof. vm_refl. Qed.
Lemma D_acf40 : decode_any W_acf40 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf44 : bv 32 := 0x00058413.
Lemma F_acf44 : fetch_word Plain.M.loaded_segments (0xacf90 : word) = Some W_acf44.
Proof. vm_refl. Qed.
Lemma D_acf44 : decode_any W_acf44 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf48 : bv 32 := 0x00050493.
Lemma F_acf48 : fetch_word Plain.M.loaded_segments (0xacf94 : word) = Some W_acf48.
Proof. vm_refl. Qed.
Lemma D_acf48 : decode_any W_acf48 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf4c : bv 32 := 0x00000593.
Lemma F_acf4c : fetch_word Plain.M.loaded_segments (0xacf98 : word) = Some W_acf4c.
Proof. vm_refl. Qed.
Lemma D_acf4c : decode_any W_acf4c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf50 : bv 32 := 0x00040613.
Lemma F_acf50 : fetch_word Plain.M.loaded_segments (0xacf9c : word) = Some W_acf50.
Proof. vm_refl. Qed.
Lemma D_acf50 : decode_any W_acf50 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf54 : bv 32 := 0xbf0ff0ef.
Lemma F_acf54 : fetch_word Plain.M.loaded_segments (0xacfa0 : word) = Some W_acf54.
Proof. vm_refl. Qed.
Lemma D_acf54 : decode_any W_acf54 = Some (Jal 1 2094064, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf58 : bv 32 := 0x00050463.
Lemma F_acf58 : fetch_word Plain.M.loaded_segments (0xacfa4 : word) = Some W_acf58.
Proof. vm_refl. Qed.
Lemma D_acf58 : decode_any W_acf58 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf5c : bv 32 := 0x40950433.
Lemma F_acf5c : fetch_word Plain.M.loaded_segments (0xacfa8 : word) = Some W_acf5c.
Proof. vm_refl. Qed.
Lemma D_acf5c : decode_any W_acf5c = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf60 : bv 32 := 0x00040513.
Lemma F_acf60 : fetch_word Plain.M.loaded_segments (0xacfac : word) = Some W_acf60.
Proof. vm_refl. Qed.
Lemma D_acf60 : decode_any W_acf60 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf64 : bv 32 := 0x01813083.
Lemma F_acf64 : fetch_word Plain.M.loaded_segments (0xacfb0 : word) = Some W_acf64.
Proof. vm_refl. Qed.
Lemma D_acf64 : decode_any W_acf64 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf68 : bv 32 := 0x01013403.
Lemma F_acf68 : fetch_word Plain.M.loaded_segments (0xacfb4 : word) = Some W_acf68.
Proof. vm_refl. Qed.
Lemma D_acf68 : decode_any W_acf68 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf6c : bv 32 := 0x00813483.
Lemma F_acf6c : fetch_word Plain.M.loaded_segments (0xacfb8 : word) = Some W_acf6c.
Proof. vm_refl. Qed.
Lemma D_acf6c : decode_any W_acf6c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf70 : bv 32 := 0x02010113.
Lemma F_acf70 : fetch_word Plain.M.loaded_segments (0xacfbc : word) = Some W_acf70.
Proof. vm_refl. Qed.
Lemma D_acf70 : decode_any W_acf70 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_acf74 : bv 32 := 0x00008067.
Lemma F_acf74 : fetch_word Plain.M.loaded_segments (0xacfc0 : word) = Some W_acf74.
Proof. vm_refl. Qed.
Lemma D_acf74 : decode_any W_acf74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad0d0 : bv 32 := 0x0003e597.
Lemma F_ad0d0 : fetch_word Plain.M.loaded_segments (0xad11c : word) = Some W_ad0d0.
Proof. vm_refl. Qed.
Lemma D_ad0d0 : decode_any W_ad0d0 = Some (Auipc 11 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad0d4 : bv 32 := 0x1b758683.
Lemma F_ad0d4 : fetch_word Plain.M.loaded_segments (0xad120 : word) = Some W_ad0d4.
Proof. vm_refl. Qed.
Lemma D_ad0d4 : decode_any W_ad0d4 = Some (Load SZ1 true 13 11 439, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad0d8 : bv 32 := 0x1e068863.
Lemma F_ad0d8 : fetch_word Plain.M.loaded_segments (0xad124 : word) = Some W_ad0d8.
Proof. vm_refl. Qed.
Lemma D_ad0d8 : decode_any W_ad0d8 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad2c8 : bv 32 := 0x00008067.
Lemma F_ad2c8 : fetch_word Plain.M.loaded_segments (0xad314 : word) = Some W_ad2c8.
Proof. vm_refl. Qed.
Lemma D_ad2c8 : decode_any W_ad2c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad3cc : bv 32 := 0x00050893.
Lemma F_ad3cc : fetch_word Plain.M.loaded_segments (0xad418 : word) = Some W_ad3cc.
Proof. vm_refl. Qed.
Lemma D_ad3cc : decode_any W_ad3cc = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad3d0 : bv 32 := 0x00058513.
Lemma F_ad3d0 : fetch_word Plain.M.loaded_segments (0xad41c : word) = Some W_ad3d0.
Proof. vm_refl. Qed.
Lemma D_ad3d0 : decode_any W_ad3d0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad3d4 : bv 32 := 0x00060593.
Lemma F_ad3d4 : fetch_word Plain.M.loaded_segments (0xad420 : word) = Some W_ad3d4.
Proof. vm_refl. Qed.
Lemma D_ad3d4 : decode_any W_ad3d4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad3d8 : bv 32 := 0x00068613.
Lemma F_ad3d8 : fetch_word Plain.M.loaded_segments (0xad424 : word) = Some W_ad3d8.
Proof. vm_refl. Qed.
Lemma D_ad3d8 : decode_any W_ad3d8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad3dc : bv 32 := 0x00070693.
Lemma F_ad3dc : fetch_word Plain.M.loaded_segments (0xad428 : word) = Some W_ad3dc.
Proof. vm_refl. Qed.
Lemma D_ad3dc : decode_any W_ad3dc = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad3e0 : bv 32 := 0x00078713.
Lemma F_ad3e0 : fetch_word Plain.M.loaded_segments (0xad42c : word) = Some W_ad3e0.
Proof. vm_refl. Qed.
Lemma D_ad3e0 : decode_any W_ad3e0 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad3e4 : bv 32 := 0x00080793.
Lemma F_ad3e4 : fetch_word Plain.M.loaded_segments (0xad430 : word) = Some W_ad3e4.
Proof. vm_refl. Qed.
Lemma D_ad3e4 : decode_any W_ad3e4 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.
