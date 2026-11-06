(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_59324 : bv 32 := 0x0ff5f593.
Lemma F_59324 : fetch_word Ubsan.M.loaded_segments (0x59324 : word) = Some W_59324.
Proof. vm_refl. Qed.
Lemma D_59324 : decode_any W_59324 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_59328 : bv 32 := 0x00757693.
Lemma F_59328 : fetch_word Ubsan.M.loaded_segments (0x59328 : word) = Some W_59328.
Proof. vm_refl. Qed.
Lemma D_59328 : decode_any W_59328 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5932c : bv 32 := 0x00c03733.
Lemma F_5932c : fetch_word Ubsan.M.loaded_segments (0x5932c : word) = Some W_5932c.
Proof. vm_refl. Qed.
Lemma D_5932c : decode_any W_5932c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59330 : bv 32 := 0x02068c63.
Lemma F_59330 : fetch_word Ubsan.M.loaded_segments (0x59330 : word) = Some W_59330.
Proof. vm_refl. Qed.
Lemma D_59330 : decode_any W_59330 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_59334 : bv 32 := 0x02060a63.
Lemma F_59334 : fetch_word Ubsan.M.loaded_segments (0x59334 : word) = Some W_59334.
Proof. vm_refl. Qed.
Lemma D_59334 : decode_any W_59334 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_59338 : bv 32 := 0x00150793.
Lemma F_59338 : fetch_word Ubsan.M.loaded_segments (0x59338 : word) = Some W_59338.
Proof. vm_refl. Qed.
Lemma D_59338 : decode_any W_59338 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5933c : bv 32 := 0x00100813.
Lemma F_5933c : fetch_word Ubsan.M.loaded_segments (0x5933c : word) = Some W_5933c.
Proof. vm_refl. Qed.
Lemma D_5933c : decode_any W_5933c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59340 : bv 32 := 0x00054703.
Lemma F_59340 : fetch_word Ubsan.M.loaded_segments (0x59340 : word) = Some W_59340.
Proof. vm_refl. Qed.
Lemma D_59340 : decode_any W_59340 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59344 : bv 32 := 0x00060693.
Lemma F_59344 : fetch_word Ubsan.M.loaded_segments (0x59344 : word) = Some W_59344.
Proof. vm_refl. Qed.
Lemma D_59344 : decode_any W_59344 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59348 : bv 32 := 0x06b70e63.
Lemma F_59348 : fetch_word Ubsan.M.loaded_segments (0x59348 : word) = Some W_59348.
Proof. vm_refl. Qed.
Lemma D_59348 : decode_any W_59348 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5934c : bv 32 := 0x00150513.
Lemma F_5934c : fetch_word Ubsan.M.loaded_segments (0x5934c : word) = Some W_5934c.
Proof. vm_refl. Qed.
Lemma D_5934c : decode_any W_5934c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59350 : bv 32 := 0xfff68613.
Lemma F_59350 : fetch_word Ubsan.M.loaded_segments (0x59350 : word) = Some W_59350.
Proof. vm_refl. Qed.
Lemma D_59350 : decode_any W_59350 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_59354 : bv 32 := 0x0077f893.
Lemma F_59354 : fetch_word Ubsan.M.loaded_segments (0x59354 : word) = Some W_59354.
Proof. vm_refl. Qed.
Lemma D_59354 : decode_any W_59354 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_59358 : bv 32 := 0x00c03733.
Lemma F_59358 : fetch_word Ubsan.M.loaded_segments (0x59358 : word) = Some W_59358.
Proof. vm_refl. Qed.
Lemma D_59358 : decode_any W_59358 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5935c : bv 32 := 0x00088663.
Lemma F_5935c : fetch_word Ubsan.M.loaded_segments (0x5935c : word) = Some W_5935c.
Proof. vm_refl. Qed.
Lemma D_5935c : decode_any W_5935c = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59360 : bv 32 := 0x00178793.
Lemma F_59360 : fetch_word Ubsan.M.loaded_segments (0x59360 : word) = Some W_59360.
Proof. vm_refl. Qed.
Lemma D_59360 : decode_any W_59360 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59364 : bv 32 := 0xfd069ee3.
Lemma F_59364 : fetch_word Ubsan.M.loaded_segments (0x59364 : word) = Some W_59364.
Proof. vm_refl. Qed.
Lemma D_59364 : decode_any W_59364 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_59368 : bv 32 := 0x06070863.
Lemma F_59368 : fetch_word Ubsan.M.loaded_segments (0x59368 : word) = Some W_59368.
Proof. vm_refl. Qed.
Lemma D_59368 : decode_any W_59368 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5936c : bv 32 := 0x00054683.
Lemma F_5936c : fetch_word Ubsan.M.loaded_segments (0x5936c : word) = Some W_5936c.
Proof. vm_refl. Qed.
Lemma D_5936c : decode_any W_5936c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59370 : bv 32 := 0x04b68663.
Lemma F_59370 : fetch_word Ubsan.M.loaded_segments (0x59370 : word) = Some W_59370.
Proof. vm_refl. Qed.
Lemma D_59370 : decode_any W_59370 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_59374 : bv 32 := 0x00800693.
Lemma F_59374 : fetch_word Ubsan.M.loaded_segments (0x59374 : word) = Some W_59374.
Proof. vm_refl. Qed.
Lemma D_59374 : decode_any W_59374 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59378 : bv 32 := 0x04d66263.
Lemma F_59378 : fetch_word Ubsan.M.loaded_segments (0x59378 : word) = Some W_59378.
Proof. vm_refl. Qed.
Lemma D_59378 : decode_any W_59378 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5937c : bv 32 := 0xfffba697.
Lemma F_5937c : fetch_word Ubsan.M.loaded_segments (0x5937c : word) = Some W_5937c.
Proof. vm_refl. Qed.
Lemma D_5937c : decode_any W_5937c = Some (Auipc 13 1048506, 4%Z).
Proof. vm_refl. Qed.

Definition W_59380 : bv 32 := 0xed46b683.
Lemma F_59380 : fetch_word Ubsan.M.loaded_segments (0x59380 : word) = Some W_59380.
Proof. vm_refl. Qed.
Lemma D_59380 : decode_any W_59380 = Some (Load SZ8 true 13 13 3796, 4%Z).
Proof. vm_refl. Qed.

Definition W_59384 : bv 32 := 0xfffba717.
Lemma F_59384 : fetch_word Ubsan.M.loaded_segments (0x59384 : word) = Some W_59384.
Proof. vm_refl. Qed.
Lemma D_59384 : decode_any W_59384 = Some (Auipc 14 1048506, 4%Z).
Proof. vm_refl. Qed.

Definition W_59388 : bv 32 := 0xebc73703.
Lemma F_59388 : fetch_word Ubsan.M.loaded_segments (0x59388 : word) = Some W_59388.
Proof. vm_refl. Qed.
Lemma D_59388 : decode_any W_59388 = Some (Load SZ8 true 14 14 3772, 4%Z).
Proof. vm_refl. Qed.

Definition W_5938c : bv 32 := 0x00168793.
Lemma F_5938c : fetch_word Ubsan.M.loaded_segments (0x5938c : word) = Some W_5938c.
Proof. vm_refl. Qed.
Lemma D_5938c : decode_any W_5938c = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59390 : bv 32 := 0x02f587b3.
Lemma F_59390 : fetch_word Ubsan.M.loaded_segments (0x59390 : word) = Some W_59390.
Proof. vm_refl. Qed.
Lemma D_59390 : decode_any W_59390 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_59394 : bv 32 := 0x00700813.
Lemma F_59394 : fetch_word Ubsan.M.loaded_segments (0x59394 : word) = Some W_59394.
Proof. vm_refl. Qed.
Lemma D_59394 : decode_any W_59394 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_59398 : bv 32 := 0x00053883.
Lemma F_59398 : fetch_word Ubsan.M.loaded_segments (0x59398 : word) = Some W_59398.
Proof. vm_refl. Qed.
Lemma D_59398 : decode_any W_59398 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5939c : bv 32 := 0x00f8c8b3.
Lemma F_5939c : fetch_word Ubsan.M.loaded_segments (0x5939c : word) = Some W_5939c.
Proof. vm_refl. Qed.
Lemma D_5939c : decode_any W_5939c = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_593a0 : bv 32 := 0x411682b3.
Lemma F_593a0 : fetch_word Ubsan.M.loaded_segments (0x593a0 : word) = Some W_593a0.
Proof. vm_refl. Qed.
Lemma D_593a0 : decode_any W_593a0 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_593a4 : bv 32 := 0x0112e8b3.
Lemma F_593a4 : fetch_word Ubsan.M.loaded_segments (0x593a4 : word) = Some W_593a4.
Proof. vm_refl. Qed.
Lemma D_593a4 : decode_any W_593a4 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_593a8 : bv 32 := 0x00e8f8b3.
Lemma F_593a8 : fetch_word Ubsan.M.loaded_segments (0x593a8 : word) = Some W_593a8.
Proof. vm_refl. Qed.
Lemma D_593a8 : decode_any W_593a8 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_593ac : bv 32 := 0x02e89a63.
Lemma F_593ac : fetch_word Ubsan.M.loaded_segments (0x593ac : word) = Some W_593ac.
Proof. vm_refl. Qed.
Lemma D_593ac : decode_any W_593ac = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_593b0 : bv 32 := 0xff860613.
Lemma F_593b0 : fetch_word Ubsan.M.loaded_segments (0x593b0 : word) = Some W_593b0.
Proof. vm_refl. Qed.
Lemma D_593b0 : decode_any W_593b0 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_593b4 : bv 32 := 0x00850513.
Lemma F_593b4 : fetch_word Ubsan.M.loaded_segments (0x593b4 : word) = Some W_593b4.
Proof. vm_refl. Qed.
Lemma D_593b4 : decode_any W_593b4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_593b8 : bv 32 := 0xfec860e3.
Lemma F_593b8 : fetch_word Ubsan.M.loaded_segments (0x593b8 : word) = Some W_593b8.
Proof. vm_refl. Qed.
Lemma D_593b8 : decode_any W_593b8 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_593bc : bv 32 := 0x00060693.
Lemma F_593bc : fetch_word Ubsan.M.loaded_segments (0x593bc : word) = Some W_593bc.
Proof. vm_refl. Qed.
Lemma D_593bc : decode_any W_593bc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593c0 : bv 32 := 0x00060c63.
Lemma F_593c0 : fetch_word Ubsan.M.loaded_segments (0x593c0 : word) = Some W_593c0.
Proof. vm_refl. Qed.
Lemma D_593c0 : decode_any W_593c0 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_593c4 : bv 32 := 0x00054603.
Lemma F_593c4 : fetch_word Ubsan.M.loaded_segments (0x593c4 : word) = Some W_593c4.
Proof. vm_refl. Qed.
Lemma D_593c4 : decode_any W_593c4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593c8 : bv 32 := 0x00b60a63.
Lemma F_593c8 : fetch_word Ubsan.M.loaded_segments (0x593c8 : word) = Some W_593c8.
Proof. vm_refl. Qed.
Lemma D_593c8 : decode_any W_593c8 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_593cc : bv 32 := 0xfff68693.
Lemma F_593cc : fetch_word Ubsan.M.loaded_segments (0x593cc : word) = Some W_593cc.
Proof. vm_refl. Qed.
Lemma D_593cc : decode_any W_593cc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_593d0 : bv 32 := 0x00150513.
Lemma F_593d0 : fetch_word Ubsan.M.loaded_segments (0x593d0 : word) = Some W_593d0.
Proof. vm_refl. Qed.
Lemma D_593d0 : decode_any W_593d0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_593d4 : bv 32 := 0xfe0698e3.
Lemma F_593d4 : fetch_word Ubsan.M.loaded_segments (0x593d4 : word) = Some W_593d4.
Proof. vm_refl. Qed.
Lemma D_593d4 : decode_any W_593d4 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_593dc : bv 32 := 0x00008067.
Lemma F_593dc : fetch_word Ubsan.M.loaded_segments (0x593dc : word) = Some W_593dc.
Proof. vm_refl. Qed.
Lemma D_593dc : decode_any W_593dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593e0 : bv 32 := 0x00060693.
Lemma F_593e0 : fetch_word Ubsan.M.loaded_segments (0x593e0 : word) = Some W_593e0.
Proof. vm_refl. Qed.
Lemma D_593e0 : decode_any W_593e0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593e4 : bv 32 := 0x00054603.
Lemma F_593e4 : fetch_word Ubsan.M.loaded_segments (0x593e4 : word) = Some W_593e4.
Proof. vm_refl. Qed.
Lemma D_593e4 : decode_any W_593e4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593e8 : bv 32 := 0xfeb612e3.
Lemma F_593e8 : fetch_word Ubsan.M.loaded_segments (0x593e8 : word) = Some W_593e8.
Proof. vm_refl. Qed.
Lemma D_593e8 : decode_any W_593e8 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_593ec : bv 32 := 0xff1ff06f.
Lemma F_593ec : fetch_word Ubsan.M.loaded_segments (0x593ec : word) = Some W_593ec.
Proof. vm_refl. Qed.
Lemma D_593ec : decode_any W_593ec = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_59420 : bv 32 := 0x0035f693.
Lemma F_59420 : fetch_word Ubsan.M.loaded_segments (0x59420 : word) = Some W_59420.
Proof. vm_refl. Qed.
Lemma D_59420 : decode_any W_59420 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_59424 : bv 32 := 0x10068863.
Lemma F_59424 : fetch_word Ubsan.M.loaded_segments (0x59424 : word) = Some W_59424.
Proof. vm_refl. Qed.
Lemma D_59424 : decode_any W_59424 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_59428 : bv 32 := 0x02060e63.
Lemma F_59428 : fetch_word Ubsan.M.loaded_segments (0x59428 : word) = Some W_59428.
Proof. vm_refl. Qed.
Lemma D_59428 : decode_any W_59428 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5942c : bv 32 := 0x00158713.
Lemma F_5942c : fetch_word Ubsan.M.loaded_segments (0x5942c : word) = Some W_5942c.
Proof. vm_refl. Qed.
Lemma D_5942c : decode_any W_5942c = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59430 : bv 32 := 0x00100793.
Lemma F_59430 : fetch_word Ubsan.M.loaded_segments (0x59430 : word) = Some W_59430.
Proof. vm_refl. Qed.
Lemma D_59430 : decode_any W_59430 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59434 : bv 32 := 0x00050693.
Lemma F_59434 : fetch_word Ubsan.M.loaded_segments (0x59434 : word) = Some W_59434.
Proof. vm_refl. Qed.
Lemma D_59434 : decode_any W_59434 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59438 : bv 32 := 0x0005c883.
Lemma F_59438 : fetch_word Ubsan.M.loaded_segments (0x59438 : word) = Some W_59438.
Proof. vm_refl. Qed.
Lemma D_59438 : decode_any W_59438 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5943c : bv 32 := 0x00060813.
Lemma F_5943c : fetch_word Ubsan.M.loaded_segments (0x5943c : word) = Some W_5943c.
Proof. vm_refl. Qed.
Lemma D_5943c : decode_any W_5943c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59440 : bv 32 := 0x00158593.
Lemma F_59440 : fetch_word Ubsan.M.loaded_segments (0x59440 : word) = Some W_59440.
Proof. vm_refl. Qed.
Lemma D_59440 : decode_any W_59440 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59444 : bv 32 := 0x00377293.
Lemma F_59444 : fetch_word Ubsan.M.loaded_segments (0x59444 : word) = Some W_59444.
Proof. vm_refl. Qed.
Lemma D_59444 : decode_any W_59444 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_59448 : bv 32 := 0x01168023.
Lemma F_59448 : fetch_word Ubsan.M.loaded_segments (0x59448 : word) = Some W_59448.
Proof. vm_refl. Qed.
Lemma D_59448 : decode_any W_59448 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5944c : bv 32 := 0x00168693.
Lemma F_5944c : fetch_word Ubsan.M.loaded_segments (0x5944c : word) = Some W_5944c.
Proof. vm_refl. Qed.
Lemma D_5944c : decode_any W_5944c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59450 : bv 32 := 0xfff60613.
Lemma F_59450 : fetch_word Ubsan.M.loaded_segments (0x59450 : word) = Some W_59450.
Proof. vm_refl. Qed.
Lemma D_59450 : decode_any W_59450 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_59454 : bv 32 := 0x00028a63.
Lemma F_59454 : fetch_word Ubsan.M.loaded_segments (0x59454 : word) = Some W_59454.
Proof. vm_refl. Qed.
Lemma D_59454 : decode_any W_59454 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_59458 : bv 32 := 0x00170713.
Lemma F_59458 : fetch_word Ubsan.M.loaded_segments (0x59458 : word) = Some W_59458.
Proof. vm_refl. Qed.
Lemma D_59458 : decode_any W_59458 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5945c : bv 32 := 0xfcf81ee3.
Lemma F_5945c : fetch_word Ubsan.M.loaded_segments (0x5945c : word) = Some W_5945c.
Proof. vm_refl. Qed.
Lemma D_5945c : decode_any W_5945c = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_59460 : bv 32 := 0x0080006f.
Lemma F_59460 : fetch_word Ubsan.M.loaded_segments (0x59460 : word) = Some W_59460.
Proof. vm_refl. Qed.
Lemma D_59460 : decode_any W_59460 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59464 : bv 32 := 0x00050693.
Lemma F_59464 : fetch_word Ubsan.M.loaded_segments (0x59464 : word) = Some W_59464.
Proof. vm_refl. Qed.
Lemma D_59464 : decode_any W_59464 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59468 : bv 32 := 0x0036f793.
Lemma F_59468 : fetch_word Ubsan.M.loaded_segments (0x59468 : word) = Some W_59468.
Proof. vm_refl. Qed.
Lemma D_59468 : decode_any W_59468 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5946c : bv 32 := 0x0c078a63.
Lemma F_5946c : fetch_word Ubsan.M.loaded_segments (0x5946c : word) = Some W_5946c.
Proof. vm_refl. Qed.
Lemma D_5946c : decode_any W_5946c = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_59470 : bv 32 := 0x02000713.
Lemma F_59470 : fetch_word Ubsan.M.loaded_segments (0x59470 : word) = Some W_59470.
Proof. vm_refl. Qed.
Lemma D_59470 : decode_any W_59470 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59474 : bv 32 := 0x02e67063.
Lemma F_59474 : fetch_word Ubsan.M.loaded_segments (0x59474 : word) = Some W_59474.
Proof. vm_refl. Qed.
Lemma D_59474 : decode_any W_59474 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59478 : bv 32 := 0x01000713.
Lemma F_59478 : fetch_word Ubsan.M.loaded_segments (0x59478 : word) = Some W_59478.
Proof. vm_refl. Qed.
Lemma D_59478 : decode_any W_59478 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5947c : bv 32 := 0x24e67863.
Lemma F_5947c : fetch_word Ubsan.M.loaded_segments (0x5947c : word) = Some W_5947c.
Proof. vm_refl. Qed.
Lemma D_5947c : decode_any W_5947c = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_59480 : bv 32 := 0x00867713.
Lemma F_59480 : fetch_word Ubsan.M.loaded_segments (0x59480 : word) = Some W_59480.
Proof. vm_refl. Qed.
Lemma D_59480 : decode_any W_59480 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59484 : bv 32 := 0x2c071e63.
Lemma F_59484 : fetch_word Ubsan.M.loaded_segments (0x59484 : word) = Some W_59484.
Proof. vm_refl. Qed.
Lemma D_59484 : decode_any W_59484 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_59488 : bv 32 := 0x00467713.
Lemma F_59488 : fetch_word Ubsan.M.loaded_segments (0x59488 : word) = Some W_59488.
Proof. vm_refl. Qed.
Lemma D_59488 : decode_any W_59488 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5948c : bv 32 := 0x32071463.
Lemma F_5948c : fetch_word Ubsan.M.loaded_segments (0x5948c : word) = Some W_5948c.
Proof. vm_refl. Qed.
Lemma D_5948c : decode_any W_5948c = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_59490 : bv 32 := 0x3500006f.
Lemma F_59490 : fetch_word Ubsan.M.loaded_segments (0x59490 : word) = Some W_59490.
Proof. vm_refl. Qed.
Lemma D_59490 : decode_any W_59490 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_59494 : bv 32 := 0x0005a703.
Lemma F_59494 : fetch_word Ubsan.M.loaded_segments (0x59494 : word) = Some W_59494.
Proof. vm_refl. Qed.
Lemma D_59494 : decode_any W_59494 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59498 : bv 32 := 0x00300813.
Lemma F_59498 : fetch_word Ubsan.M.loaded_segments (0x59498 : word) = Some W_59498.
Proof. vm_refl. Qed.
Lemma D_59498 : decode_any W_59498 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5949c : bv 32 := 0x11078e63.
Lemma F_5949c : fetch_word Ubsan.M.loaded_segments (0x5949c : word) = Some W_5949c.
Proof. vm_refl. Qed.
Lemma D_5949c : decode_any W_5949c = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_594a0 : bv 32 := 0x00200813.
Lemma F_594a0 : fetch_word Ubsan.M.loaded_segments (0x594a0 : word) = Some W_594a0.
Proof. vm_refl. Qed.
Lemma D_594a0 : decode_any W_594a0 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_594a4 : bv 32 := 0x19079c63.
Lemma F_594a4 : fetch_word Ubsan.M.loaded_segments (0x594a4 : word) = Some W_594a4.
Proof. vm_refl. Qed.
Lemma D_594a4 : decode_any W_594a4 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_594a8 : bv 32 := 0x00875793.
Lemma F_594a8 : fetch_word Ubsan.M.loaded_segments (0x594a8 : word) = Some W_594a8.
Proof. vm_refl. Qed.
Lemma D_594a8 : decode_any W_594a8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_594ac : bv 32 := 0xffe60613.
Lemma F_594ac : fetch_word Ubsan.M.loaded_segments (0x594ac : word) = Some W_594ac.
Proof. vm_refl. Qed.
Lemma D_594ac : decode_any W_594ac = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_594b0 : bv 32 := 0x00e68023.
Lemma F_594b0 : fetch_word Ubsan.M.loaded_segments (0x594b0 : word) = Some W_594b0.
Proof. vm_refl. Qed.
Lemma D_594b0 : decode_any W_594b0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_594b4 : bv 32 := 0x00f680a3.
Lemma F_594b4 : fetch_word Ubsan.M.loaded_segments (0x594b4 : word) = Some W_594b4.
Proof. vm_refl. Qed.
Lemma D_594b4 : decode_any W_594b4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_594b8 : bv 32 := 0x00268693.
Lemma F_594b8 : fetch_word Ubsan.M.loaded_segments (0x594b8 : word) = Some W_594b8.
Proof. vm_refl. Qed.
Lemma D_594b8 : decode_any W_594b8 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_594bc : bv 32 := 0x01058593.
Lemma F_594bc : fetch_word Ubsan.M.loaded_segments (0x594bc : word) = Some W_594bc.
Proof. vm_refl. Qed.
Lemma D_594bc : decode_any W_594bc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_594c0 : bv 32 := 0x01100793.
Lemma F_594c0 : fetch_word Ubsan.M.loaded_segments (0x594c0 : word) = Some W_594c0.
Proof. vm_refl. Qed.
Lemma D_594c0 : decode_any W_594c0 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_594c4 : bv 32 := 0x0107581b.
Lemma F_594c4 : fetch_word Ubsan.M.loaded_segments (0x594c4 : word) = Some W_594c4.
Proof. vm_refl. Qed.
Lemma D_594c4 : decode_any W_594c4 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_594c8 : bv 32 := 0xff45a883.
Lemma F_594c8 : fetch_word Ubsan.M.loaded_segments (0x594c8 : word) = Some W_594c8.
Proof. vm_refl. Qed.
Lemma D_594c8 : decode_any W_594c8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_594cc : bv 32 := 0xff85a283.
Lemma F_594cc : fetch_word Ubsan.M.loaded_segments (0x594cc : word) = Some W_594cc.
Proof. vm_refl. Qed.
Lemma D_594cc : decode_any W_594cc = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_594d0 : bv 32 := 0xffc5a303.
Lemma F_594d0 : fetch_word Ubsan.M.loaded_segments (0x594d0 : word) = Some W_594d0.
Proof. vm_refl. Qed.
Lemma D_594d0 : decode_any W_594d0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_594d4 : bv 32 := 0x0005a703.
Lemma F_594d4 : fetch_word Ubsan.M.loaded_segments (0x594d4 : word) = Some W_594d4.
Proof. vm_refl. Qed.
Lemma D_594d4 : decode_any W_594d4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_594d8 : bv 32 := 0x01089393.
Lemma F_594d8 : fetch_word Ubsan.M.loaded_segments (0x594d8 : word) = Some W_594d8.
Proof. vm_refl. Qed.
Lemma D_594d8 : decode_any W_594d8 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_594dc : bv 32 := 0x0108d89b.
Lemma F_594dc : fetch_word Ubsan.M.loaded_segments (0x594dc : word) = Some W_594dc.
Proof. vm_refl. Qed.
Lemma D_594dc : decode_any W_594dc = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_594e0 : bv 32 := 0x0103e833.
Lemma F_594e0 : fetch_word Ubsan.M.loaded_segments (0x594e0 : word) = Some W_594e0.
Proof. vm_refl. Qed.
Lemma D_594e0 : decode_any W_594e0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_594e4 : bv 32 := 0x01029393.
Lemma F_594e4 : fetch_word Ubsan.M.loaded_segments (0x594e4 : word) = Some W_594e4.
Proof. vm_refl. Qed.
Lemma D_594e4 : decode_any W_594e4 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_594e8 : bv 32 := 0x0102d29b.
Lemma F_594e8 : fetch_word Ubsan.M.loaded_segments (0x594e8 : word) = Some W_594e8.
Proof. vm_refl. Qed.
Lemma D_594e8 : decode_any W_594e8 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_594ec : bv 32 := 0x0113e8b3.
Lemma F_594ec : fetch_word Ubsan.M.loaded_segments (0x594ec : word) = Some W_594ec.
Proof. vm_refl. Qed.
Lemma D_594ec : decode_any W_594ec = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_594f0 : bv 32 := 0x01031393.
Lemma F_594f0 : fetch_word Ubsan.M.loaded_segments (0x594f0 : word) = Some W_594f0.
Proof. vm_refl. Qed.
Lemma D_594f0 : decode_any W_594f0 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_594f4 : bv 32 := 0x0103531b.
Lemma F_594f4 : fetch_word Ubsan.M.loaded_segments (0x594f4 : word) = Some W_594f4.
Proof. vm_refl. Qed.
Lemma D_594f4 : decode_any W_594f4 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_594f8 : bv 32 := 0x0053e2b3.
Lemma F_594f8 : fetch_word Ubsan.M.loaded_segments (0x594f8 : word) = Some W_594f8.
Proof. vm_refl. Qed.
Lemma D_594f8 : decode_any W_594f8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_594fc : bv 32 := 0x01071393.
Lemma F_594fc : fetch_word Ubsan.M.loaded_segments (0x594fc : word) = Some W_594fc.
Proof. vm_refl. Qed.
Lemma D_594fc : decode_any W_594fc = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59500 : bv 32 := 0x0063e333.
Lemma F_59500 : fetch_word Ubsan.M.loaded_segments (0x59500 : word) = Some W_59500.
Proof. vm_refl. Qed.
Lemma D_59500 : decode_any W_59500 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_59504 : bv 32 := 0xff060613.
Lemma F_59504 : fetch_word Ubsan.M.loaded_segments (0x59504 : word) = Some W_59504.
Proof. vm_refl. Qed.
Lemma D_59504 : decode_any W_59504 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_59508 : bv 32 := 0x0106a023.
Lemma F_59508 : fetch_word Ubsan.M.loaded_segments (0x59508 : word) = Some W_59508.
Proof. vm_refl. Qed.
Lemma D_59508 : decode_any W_59508 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5950c : bv 32 := 0x0116a223.
Lemma F_5950c : fetch_word Ubsan.M.loaded_segments (0x5950c : word) = Some W_5950c.
Proof. vm_refl. Qed.
Lemma D_5950c : decode_any W_5950c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_59510 : bv 32 := 0x0056a423.
Lemma F_59510 : fetch_word Ubsan.M.loaded_segments (0x59510 : word) = Some W_59510.
Proof. vm_refl. Qed.
Lemma D_59510 : decode_any W_59510 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59514 : bv 32 := 0x0066a623.
Lemma F_59514 : fetch_word Ubsan.M.loaded_segments (0x59514 : word) = Some W_59514.
Proof. vm_refl. Qed.
Lemma D_59514 : decode_any W_59514 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59518 : bv 32 := 0x01068693.
Lemma F_59518 : fetch_word Ubsan.M.loaded_segments (0x59518 : word) = Some W_59518.
Proof. vm_refl. Qed.
Lemma D_59518 : decode_any W_59518 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5951c : bv 32 := 0x01058593.
Lemma F_5951c : fetch_word Ubsan.M.loaded_segments (0x5951c : word) = Some W_5951c.
Proof. vm_refl. Qed.
Lemma D_5951c : decode_any W_5951c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59520 : bv 32 := 0xfac7e2e3.
Lemma F_59520 : fetch_word Ubsan.M.loaded_segments (0x59520 : word) = Some W_59520.
Proof. vm_refl. Qed.
Lemma D_59520 : decode_any W_59520 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_59524 : bv 32 := 0xff258593.
Lemma F_59524 : fetch_word Ubsan.M.loaded_segments (0x59524 : word) = Some W_59524.
Proof. vm_refl. Qed.
Lemma D_59524 : decode_any W_59524 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_59528 : bv 32 := 0x01000713.
Lemma F_59528 : fetch_word Ubsan.M.loaded_segments (0x59528 : word) = Some W_59528.
Proof. vm_refl. Qed.
Lemma D_59528 : decode_any W_59528 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5952c : bv 32 := 0xf4e66ae3.
Lemma F_5952c : fetch_word Ubsan.M.loaded_segments (0x5952c : word) = Some W_5952c.
Proof. vm_refl. Qed.
Lemma D_5952c : decode_any W_5952c = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_59530 : bv 32 := 0x19c0006f.
Lemma F_59530 : fetch_word Ubsan.M.loaded_segments (0x59530 : word) = Some W_59530.
Proof. vm_refl. Qed.
Lemma D_59530 : decode_any W_59530 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_59534 : bv 32 := 0x00050693.
Lemma F_59534 : fetch_word Ubsan.M.loaded_segments (0x59534 : word) = Some W_59534.
Proof. vm_refl. Qed.
Lemma D_59534 : decode_any W_59534 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59538 : bv 32 := 0x00357793.
Lemma F_59538 : fetch_word Ubsan.M.loaded_segments (0x59538 : word) = Some W_59538.
Proof. vm_refl. Qed.
Lemma D_59538 : decode_any W_59538 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5953c : bv 32 := 0xf2079ae3.
Lemma F_5953c : fetch_word Ubsan.M.loaded_segments (0x5953c : word) = Some W_5953c.
Proof. vm_refl. Qed.
Lemma D_5953c : decode_any W_5953c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.
