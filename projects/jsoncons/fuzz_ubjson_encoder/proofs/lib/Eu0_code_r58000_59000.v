(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_adec0 : bv 32 := 0x0ff5f593.
Lemma F_adec0 : fetch_word Ubsan.M.loaded_segments (0xadf0c : word) = Some W_adec0.
Proof. vm_refl. Qed.
Lemma D_adec0 : decode_any W_adec0 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_adec4 : bv 32 := 0x00757693.
Lemma F_adec4 : fetch_word Ubsan.M.loaded_segments (0xadf10 : word) = Some W_adec4.
Proof. vm_refl. Qed.
Lemma D_adec4 : decode_any W_adec4 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_adec8 : bv 32 := 0x00c03733.
Lemma F_adec8 : fetch_word Ubsan.M.loaded_segments (0xadf14 : word) = Some W_adec8.
Proof. vm_refl. Qed.
Lemma D_adec8 : decode_any W_adec8 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_adecc : bv 32 := 0x02068c63.
Lemma F_adecc : fetch_word Ubsan.M.loaded_segments (0xadf18 : word) = Some W_adecc.
Proof. vm_refl. Qed.
Lemma D_adecc : decode_any W_adecc = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_aded0 : bv 32 := 0x02060a63.
Lemma F_aded0 : fetch_word Ubsan.M.loaded_segments (0xadf1c : word) = Some W_aded0.
Proof. vm_refl. Qed.
Lemma D_aded0 : decode_any W_aded0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_aded4 : bv 32 := 0x00150793.
Lemma F_aded4 : fetch_word Ubsan.M.loaded_segments (0xadf20 : word) = Some W_aded4.
Proof. vm_refl. Qed.
Lemma D_aded4 : decode_any W_aded4 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_aded8 : bv 32 := 0x00100813.
Lemma F_aded8 : fetch_word Ubsan.M.loaded_segments (0xadf24 : word) = Some W_aded8.
Proof. vm_refl. Qed.
Lemma D_aded8 : decode_any W_aded8 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_adedc : bv 32 := 0x00054703.
Lemma F_adedc : fetch_word Ubsan.M.loaded_segments (0xadf28 : word) = Some W_adedc.
Proof. vm_refl. Qed.
Lemma D_adedc : decode_any W_adedc = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adee0 : bv 32 := 0x00060693.
Lemma F_adee0 : fetch_word Ubsan.M.loaded_segments (0xadf2c : word) = Some W_adee0.
Proof. vm_refl. Qed.
Lemma D_adee0 : decode_any W_adee0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adee4 : bv 32 := 0x06b70e63.
Lemma F_adee4 : fetch_word Ubsan.M.loaded_segments (0xadf30 : word) = Some W_adee4.
Proof. vm_refl. Qed.
Lemma D_adee4 : decode_any W_adee4 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_adee8 : bv 32 := 0x00150513.
Lemma F_adee8 : fetch_word Ubsan.M.loaded_segments (0xadf34 : word) = Some W_adee8.
Proof. vm_refl. Qed.
Lemma D_adee8 : decode_any W_adee8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_adeec : bv 32 := 0xfff68613.
Lemma F_adeec : fetch_word Ubsan.M.loaded_segments (0xadf38 : word) = Some W_adeec.
Proof. vm_refl. Qed.
Lemma D_adeec : decode_any W_adeec = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_adef0 : bv 32 := 0x0077f893.
Lemma F_adef0 : fetch_word Ubsan.M.loaded_segments (0xadf3c : word) = Some W_adef0.
Proof. vm_refl. Qed.
Lemma D_adef0 : decode_any W_adef0 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_adef4 : bv 32 := 0x00c03733.
Lemma F_adef4 : fetch_word Ubsan.M.loaded_segments (0xadf40 : word) = Some W_adef4.
Proof. vm_refl. Qed.
Lemma D_adef4 : decode_any W_adef4 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_adef8 : bv 32 := 0x00088663.
Lemma F_adef8 : fetch_word Ubsan.M.loaded_segments (0xadf44 : word) = Some W_adef8.
Proof. vm_refl. Qed.
Lemma D_adef8 : decode_any W_adef8 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_adefc : bv 32 := 0x00178793.
Lemma F_adefc : fetch_word Ubsan.M.loaded_segments (0xadf48 : word) = Some W_adefc.
Proof. vm_refl. Qed.
Lemma D_adefc : decode_any W_adefc = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf00 : bv 32 := 0xfd069ee3.
Lemma F_adf00 : fetch_word Ubsan.M.loaded_segments (0xadf4c : word) = Some W_adf00.
Proof. vm_refl. Qed.
Lemma D_adf00 : decode_any W_adf00 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf04 : bv 32 := 0x06070863.
Lemma F_adf04 : fetch_word Ubsan.M.loaded_segments (0xadf50 : word) = Some W_adf04.
Proof. vm_refl. Qed.
Lemma D_adf04 : decode_any W_adf04 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf08 : bv 32 := 0x00054683.
Lemma F_adf08 : fetch_word Ubsan.M.loaded_segments (0xadf54 : word) = Some W_adf08.
Proof. vm_refl. Qed.
Lemma D_adf08 : decode_any W_adf08 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf0c : bv 32 := 0x04b68663.
Lemma F_adf0c : fetch_word Ubsan.M.loaded_segments (0xadf58 : word) = Some W_adf0c.
Proof. vm_refl. Qed.
Lemma D_adf0c : decode_any W_adf0c = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf10 : bv 32 := 0x00800693.
Lemma F_adf10 : fetch_word Ubsan.M.loaded_segments (0xadf5c : word) = Some W_adf10.
Proof. vm_refl. Qed.
Lemma D_adf10 : decode_any W_adf10 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf14 : bv 32 := 0x04d66263.
Lemma F_adf14 : fetch_word Ubsan.M.loaded_segments (0xadf60 : word) = Some W_adf14.
Proof. vm_refl. Qed.
Lemma D_adf14 : decode_any W_adf14 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf18 : bv 32 := 0xfff65697.
Lemma F_adf18 : fetch_word Ubsan.M.loaded_segments (0xadf64 : word) = Some W_adf18.
Proof. vm_refl. Qed.
Lemma D_adf18 : decode_any W_adf18 = Some (Auipc 13 1048421, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf1c : bv 32 := 0x7f46b683.
Lemma F_adf1c : fetch_word Ubsan.M.loaded_segments (0xadf68 : word) = Some W_adf1c.
Proof. vm_refl. Qed.
Lemma D_adf1c : decode_any W_adf1c = Some (Load SZ8 true 13 13 2036, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf20 : bv 32 := 0xfff65717.
Lemma F_adf20 : fetch_word Ubsan.M.loaded_segments (0xadf6c : word) = Some W_adf20.
Proof. vm_refl. Qed.
Lemma D_adf20 : decode_any W_adf20 = Some (Auipc 14 1048421, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf24 : bv 32 := 0x7dc73703.
Lemma F_adf24 : fetch_word Ubsan.M.loaded_segments (0xadf70 : word) = Some W_adf24.
Proof. vm_refl. Qed.
Lemma D_adf24 : decode_any W_adf24 = Some (Load SZ8 true 14 14 2012, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf28 : bv 32 := 0x00168793.
Lemma F_adf28 : fetch_word Ubsan.M.loaded_segments (0xadf74 : word) = Some W_adf28.
Proof. vm_refl. Qed.
Lemma D_adf28 : decode_any W_adf28 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf2c : bv 32 := 0x02f587b3.
Lemma F_adf2c : fetch_word Ubsan.M.loaded_segments (0xadf78 : word) = Some W_adf2c.
Proof. vm_refl. Qed.
Lemma D_adf2c : decode_any W_adf2c = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf30 : bv 32 := 0x00700813.
Lemma F_adf30 : fetch_word Ubsan.M.loaded_segments (0xadf7c : word) = Some W_adf30.
Proof. vm_refl. Qed.
Lemma D_adf30 : decode_any W_adf30 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf34 : bv 32 := 0x00053883.
Lemma F_adf34 : fetch_word Ubsan.M.loaded_segments (0xadf80 : word) = Some W_adf34.
Proof. vm_refl. Qed.
Lemma D_adf34 : decode_any W_adf34 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf38 : bv 32 := 0x00f8c8b3.
Lemma F_adf38 : fetch_word Ubsan.M.loaded_segments (0xadf84 : word) = Some W_adf38.
Proof. vm_refl. Qed.
Lemma D_adf38 : decode_any W_adf38 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf3c : bv 32 := 0x411682b3.
Lemma F_adf3c : fetch_word Ubsan.M.loaded_segments (0xadf88 : word) = Some W_adf3c.
Proof. vm_refl. Qed.
Lemma D_adf3c : decode_any W_adf3c = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf40 : bv 32 := 0x0112e8b3.
Lemma F_adf40 : fetch_word Ubsan.M.loaded_segments (0xadf8c : word) = Some W_adf40.
Proof. vm_refl. Qed.
Lemma D_adf40 : decode_any W_adf40 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf44 : bv 32 := 0x00e8f8b3.
Lemma F_adf44 : fetch_word Ubsan.M.loaded_segments (0xadf90 : word) = Some W_adf44.
Proof. vm_refl. Qed.
Lemma D_adf44 : decode_any W_adf44 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf48 : bv 32 := 0x02e89a63.
Lemma F_adf48 : fetch_word Ubsan.M.loaded_segments (0xadf94 : word) = Some W_adf48.
Proof. vm_refl. Qed.
Lemma D_adf48 : decode_any W_adf48 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf4c : bv 32 := 0xff860613.
Lemma F_adf4c : fetch_word Ubsan.M.loaded_segments (0xadf98 : word) = Some W_adf4c.
Proof. vm_refl. Qed.
Lemma D_adf4c : decode_any W_adf4c = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf50 : bv 32 := 0x00850513.
Lemma F_adf50 : fetch_word Ubsan.M.loaded_segments (0xadf9c : word) = Some W_adf50.
Proof. vm_refl. Qed.
Lemma D_adf50 : decode_any W_adf50 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf54 : bv 32 := 0xfec860e3.
Lemma F_adf54 : fetch_word Ubsan.M.loaded_segments (0xadfa0 : word) = Some W_adf54.
Proof. vm_refl. Qed.
Lemma D_adf54 : decode_any W_adf54 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf58 : bv 32 := 0x00060693.
Lemma F_adf58 : fetch_word Ubsan.M.loaded_segments (0xadfa4 : word) = Some W_adf58.
Proof. vm_refl. Qed.
Lemma D_adf58 : decode_any W_adf58 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf5c : bv 32 := 0x00060c63.
Lemma F_adf5c : fetch_word Ubsan.M.loaded_segments (0xadfa8 : word) = Some W_adf5c.
Proof. vm_refl. Qed.
Lemma D_adf5c : decode_any W_adf5c = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf60 : bv 32 := 0x00054603.
Lemma F_adf60 : fetch_word Ubsan.M.loaded_segments (0xadfac : word) = Some W_adf60.
Proof. vm_refl. Qed.
Lemma D_adf60 : decode_any W_adf60 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf64 : bv 32 := 0x00b60a63.
Lemma F_adf64 : fetch_word Ubsan.M.loaded_segments (0xadfb0 : word) = Some W_adf64.
Proof. vm_refl. Qed.
Lemma D_adf64 : decode_any W_adf64 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf68 : bv 32 := 0xfff68693.
Lemma F_adf68 : fetch_word Ubsan.M.loaded_segments (0xadfb4 : word) = Some W_adf68.
Proof. vm_refl. Qed.
Lemma D_adf68 : decode_any W_adf68 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf6c : bv 32 := 0x00150513.
Lemma F_adf6c : fetch_word Ubsan.M.loaded_segments (0xadfb8 : word) = Some W_adf6c.
Proof. vm_refl. Qed.
Lemma D_adf6c : decode_any W_adf6c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf70 : bv 32 := 0xfe0698e3.
Lemma F_adf70 : fetch_word Ubsan.M.loaded_segments (0xadfbc : word) = Some W_adf70.
Proof. vm_refl. Qed.
Lemma D_adf70 : decode_any W_adf70 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf78 : bv 32 := 0x00008067.
Lemma F_adf78 : fetch_word Ubsan.M.loaded_segments (0xadfc4 : word) = Some W_adf78.
Proof. vm_refl. Qed.
Lemma D_adf78 : decode_any W_adf78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf7c : bv 32 := 0x00060693.
Lemma F_adf7c : fetch_word Ubsan.M.loaded_segments (0xadfc8 : word) = Some W_adf7c.
Proof. vm_refl. Qed.
Lemma D_adf7c : decode_any W_adf7c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf80 : bv 32 := 0x00054603.
Lemma F_adf80 : fetch_word Ubsan.M.loaded_segments (0xadfcc : word) = Some W_adf80.
Proof. vm_refl. Qed.
Lemma D_adf80 : decode_any W_adf80 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf84 : bv 32 := 0xfeb612e3.
Lemma F_adf84 : fetch_word Ubsan.M.loaded_segments (0xadfd0 : word) = Some W_adf84.
Proof. vm_refl. Qed.
Lemma D_adf84 : decode_any W_adf84 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_adf88 : bv 32 := 0xff1ff06f.
Lemma F_adf88 : fetch_word Ubsan.M.loaded_segments (0xadfd4 : word) = Some W_adf88.
Proof. vm_refl. Qed.
Lemma D_adf88 : decode_any W_adf88 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfbc : bv 32 := 0x0035f693.
Lemma F_adfbc : fetch_word Ubsan.M.loaded_segments (0xae008 : word) = Some W_adfbc.
Proof. vm_refl. Qed.
Lemma D_adfbc : decode_any W_adfbc = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfc0 : bv 32 := 0x10068863.
Lemma F_adfc0 : fetch_word Ubsan.M.loaded_segments (0xae00c : word) = Some W_adfc0.
Proof. vm_refl. Qed.
Lemma D_adfc0 : decode_any W_adfc0 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfc4 : bv 32 := 0x02060e63.
Lemma F_adfc4 : fetch_word Ubsan.M.loaded_segments (0xae010 : word) = Some W_adfc4.
Proof. vm_refl. Qed.
Lemma D_adfc4 : decode_any W_adfc4 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfc8 : bv 32 := 0x00158713.
Lemma F_adfc8 : fetch_word Ubsan.M.loaded_segments (0xae014 : word) = Some W_adfc8.
Proof. vm_refl. Qed.
Lemma D_adfc8 : decode_any W_adfc8 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfcc : bv 32 := 0x00100793.
Lemma F_adfcc : fetch_word Ubsan.M.loaded_segments (0xae018 : word) = Some W_adfcc.
Proof. vm_refl. Qed.
Lemma D_adfcc : decode_any W_adfcc = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfd0 : bv 32 := 0x00050693.
Lemma F_adfd0 : fetch_word Ubsan.M.loaded_segments (0xae01c : word) = Some W_adfd0.
Proof. vm_refl. Qed.
Lemma D_adfd0 : decode_any W_adfd0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfd4 : bv 32 := 0x0005c883.
Lemma F_adfd4 : fetch_word Ubsan.M.loaded_segments (0xae020 : word) = Some W_adfd4.
Proof. vm_refl. Qed.
Lemma D_adfd4 : decode_any W_adfd4 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfd8 : bv 32 := 0x00060813.
Lemma F_adfd8 : fetch_word Ubsan.M.loaded_segments (0xae024 : word) = Some W_adfd8.
Proof. vm_refl. Qed.
Lemma D_adfd8 : decode_any W_adfd8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfdc : bv 32 := 0x00158593.
Lemma F_adfdc : fetch_word Ubsan.M.loaded_segments (0xae028 : word) = Some W_adfdc.
Proof. vm_refl. Qed.
Lemma D_adfdc : decode_any W_adfdc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfe0 : bv 32 := 0x00377293.
Lemma F_adfe0 : fetch_word Ubsan.M.loaded_segments (0xae02c : word) = Some W_adfe0.
Proof. vm_refl. Qed.
Lemma D_adfe0 : decode_any W_adfe0 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfe4 : bv 32 := 0x01168023.
Lemma F_adfe4 : fetch_word Ubsan.M.loaded_segments (0xae030 : word) = Some W_adfe4.
Proof. vm_refl. Qed.
Lemma D_adfe4 : decode_any W_adfe4 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfe8 : bv 32 := 0x00168693.
Lemma F_adfe8 : fetch_word Ubsan.M.loaded_segments (0xae034 : word) = Some W_adfe8.
Proof. vm_refl. Qed.
Lemma D_adfe8 : decode_any W_adfe8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_adfec : bv 32 := 0xfff60613.
Lemma F_adfec : fetch_word Ubsan.M.loaded_segments (0xae038 : word) = Some W_adfec.
Proof. vm_refl. Qed.
Lemma D_adfec : decode_any W_adfec = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_adff0 : bv 32 := 0x00028a63.
Lemma F_adff0 : fetch_word Ubsan.M.loaded_segments (0xae03c : word) = Some W_adff0.
Proof. vm_refl. Qed.
Lemma D_adff0 : decode_any W_adff0 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_adff4 : bv 32 := 0x00170713.
Lemma F_adff4 : fetch_word Ubsan.M.loaded_segments (0xae040 : word) = Some W_adff4.
Proof. vm_refl. Qed.
Lemma D_adff4 : decode_any W_adff4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_adff8 : bv 32 := 0xfcf81ee3.
Lemma F_adff8 : fetch_word Ubsan.M.loaded_segments (0xae044 : word) = Some W_adff8.
Proof. vm_refl. Qed.
Lemma D_adff8 : decode_any W_adff8 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_adffc : bv 32 := 0x0080006f.
Lemma F_adffc : fetch_word Ubsan.M.loaded_segments (0xae048 : word) = Some W_adffc.
Proof. vm_refl. Qed.
Lemma D_adffc : decode_any W_adffc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae000 : bv 32 := 0x00050693.
Lemma F_ae000 : fetch_word Ubsan.M.loaded_segments (0xae04c : word) = Some W_ae000.
Proof. vm_refl. Qed.
Lemma D_ae000 : decode_any W_ae000 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae004 : bv 32 := 0x0036f793.
Lemma F_ae004 : fetch_word Ubsan.M.loaded_segments (0xae050 : word) = Some W_ae004.
Proof. vm_refl. Qed.
Lemma D_ae004 : decode_any W_ae004 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae008 : bv 32 := 0x0c078a63.
Lemma F_ae008 : fetch_word Ubsan.M.loaded_segments (0xae054 : word) = Some W_ae008.
Proof. vm_refl. Qed.
Lemma D_ae008 : decode_any W_ae008 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae00c : bv 32 := 0x02000713.
Lemma F_ae00c : fetch_word Ubsan.M.loaded_segments (0xae058 : word) = Some W_ae00c.
Proof. vm_refl. Qed.
Lemma D_ae00c : decode_any W_ae00c = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae010 : bv 32 := 0x02e67063.
Lemma F_ae010 : fetch_word Ubsan.M.loaded_segments (0xae05c : word) = Some W_ae010.
Proof. vm_refl. Qed.
Lemma D_ae010 : decode_any W_ae010 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae014 : bv 32 := 0x01000713.
Lemma F_ae014 : fetch_word Ubsan.M.loaded_segments (0xae060 : word) = Some W_ae014.
Proof. vm_refl. Qed.
Lemma D_ae014 : decode_any W_ae014 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae018 : bv 32 := 0x24e67863.
Lemma F_ae018 : fetch_word Ubsan.M.loaded_segments (0xae064 : word) = Some W_ae018.
Proof. vm_refl. Qed.
Lemma D_ae018 : decode_any W_ae018 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae01c : bv 32 := 0x00867713.
Lemma F_ae01c : fetch_word Ubsan.M.loaded_segments (0xae068 : word) = Some W_ae01c.
Proof. vm_refl. Qed.
Lemma D_ae01c : decode_any W_ae01c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae020 : bv 32 := 0x2c071e63.
Lemma F_ae020 : fetch_word Ubsan.M.loaded_segments (0xae06c : word) = Some W_ae020.
Proof. vm_refl. Qed.
Lemma D_ae020 : decode_any W_ae020 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae024 : bv 32 := 0x00467713.
Lemma F_ae024 : fetch_word Ubsan.M.loaded_segments (0xae070 : word) = Some W_ae024.
Proof. vm_refl. Qed.
Lemma D_ae024 : decode_any W_ae024 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae028 : bv 32 := 0x32071463.
Lemma F_ae028 : fetch_word Ubsan.M.loaded_segments (0xae074 : word) = Some W_ae028.
Proof. vm_refl. Qed.
Lemma D_ae028 : decode_any W_ae028 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae02c : bv 32 := 0x3500006f.
Lemma F_ae02c : fetch_word Ubsan.M.loaded_segments (0xae078 : word) = Some W_ae02c.
Proof. vm_refl. Qed.
Lemma D_ae02c : decode_any W_ae02c = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae030 : bv 32 := 0x0005a703.
Lemma F_ae030 : fetch_word Ubsan.M.loaded_segments (0xae07c : word) = Some W_ae030.
Proof. vm_refl. Qed.
Lemma D_ae030 : decode_any W_ae030 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae034 : bv 32 := 0x00300813.
Lemma F_ae034 : fetch_word Ubsan.M.loaded_segments (0xae080 : word) = Some W_ae034.
Proof. vm_refl. Qed.
Lemma D_ae034 : decode_any W_ae034 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae038 : bv 32 := 0x11078e63.
Lemma F_ae038 : fetch_word Ubsan.M.loaded_segments (0xae084 : word) = Some W_ae038.
Proof. vm_refl. Qed.
Lemma D_ae038 : decode_any W_ae038 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae03c : bv 32 := 0x00200813.
Lemma F_ae03c : fetch_word Ubsan.M.loaded_segments (0xae088 : word) = Some W_ae03c.
Proof. vm_refl. Qed.
Lemma D_ae03c : decode_any W_ae03c = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae040 : bv 32 := 0x19079c63.
Lemma F_ae040 : fetch_word Ubsan.M.loaded_segments (0xae08c : word) = Some W_ae040.
Proof. vm_refl. Qed.
Lemma D_ae040 : decode_any W_ae040 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae044 : bv 32 := 0x00875793.
Lemma F_ae044 : fetch_word Ubsan.M.loaded_segments (0xae090 : word) = Some W_ae044.
Proof. vm_refl. Qed.
Lemma D_ae044 : decode_any W_ae044 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae048 : bv 32 := 0xffe60613.
Lemma F_ae048 : fetch_word Ubsan.M.loaded_segments (0xae094 : word) = Some W_ae048.
Proof. vm_refl. Qed.
Lemma D_ae048 : decode_any W_ae048 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae04c : bv 32 := 0x00e68023.
Lemma F_ae04c : fetch_word Ubsan.M.loaded_segments (0xae098 : word) = Some W_ae04c.
Proof. vm_refl. Qed.
Lemma D_ae04c : decode_any W_ae04c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae050 : bv 32 := 0x00f680a3.
Lemma F_ae050 : fetch_word Ubsan.M.loaded_segments (0xae09c : word) = Some W_ae050.
Proof. vm_refl. Qed.
Lemma D_ae050 : decode_any W_ae050 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae054 : bv 32 := 0x00268693.
Lemma F_ae054 : fetch_word Ubsan.M.loaded_segments (0xae0a0 : word) = Some W_ae054.
Proof. vm_refl. Qed.
Lemma D_ae054 : decode_any W_ae054 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae058 : bv 32 := 0x01058593.
Lemma F_ae058 : fetch_word Ubsan.M.loaded_segments (0xae0a4 : word) = Some W_ae058.
Proof. vm_refl. Qed.
Lemma D_ae058 : decode_any W_ae058 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae05c : bv 32 := 0x01100793.
Lemma F_ae05c : fetch_word Ubsan.M.loaded_segments (0xae0a8 : word) = Some W_ae05c.
Proof. vm_refl. Qed.
Lemma D_ae05c : decode_any W_ae05c = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae060 : bv 32 := 0x0107581b.
Lemma F_ae060 : fetch_word Ubsan.M.loaded_segments (0xae0ac : word) = Some W_ae060.
Proof. vm_refl. Qed.
Lemma D_ae060 : decode_any W_ae060 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae064 : bv 32 := 0xff45a883.
Lemma F_ae064 : fetch_word Ubsan.M.loaded_segments (0xae0b0 : word) = Some W_ae064.
Proof. vm_refl. Qed.
Lemma D_ae064 : decode_any W_ae064 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae068 : bv 32 := 0xff85a283.
Lemma F_ae068 : fetch_word Ubsan.M.loaded_segments (0xae0b4 : word) = Some W_ae068.
Proof. vm_refl. Qed.
Lemma D_ae068 : decode_any W_ae068 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae06c : bv 32 := 0xffc5a303.
Lemma F_ae06c : fetch_word Ubsan.M.loaded_segments (0xae0b8 : word) = Some W_ae06c.
Proof. vm_refl. Qed.
Lemma D_ae06c : decode_any W_ae06c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae070 : bv 32 := 0x0005a703.
Lemma F_ae070 : fetch_word Ubsan.M.loaded_segments (0xae0bc : word) = Some W_ae070.
Proof. vm_refl. Qed.
Lemma D_ae070 : decode_any W_ae070 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae074 : bv 32 := 0x01089393.
Lemma F_ae074 : fetch_word Ubsan.M.loaded_segments (0xae0c0 : word) = Some W_ae074.
Proof. vm_refl. Qed.
Lemma D_ae074 : decode_any W_ae074 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae078 : bv 32 := 0x0108d89b.
Lemma F_ae078 : fetch_word Ubsan.M.loaded_segments (0xae0c4 : word) = Some W_ae078.
Proof. vm_refl. Qed.
Lemma D_ae078 : decode_any W_ae078 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae07c : bv 32 := 0x0103e833.
Lemma F_ae07c : fetch_word Ubsan.M.loaded_segments (0xae0c8 : word) = Some W_ae07c.
Proof. vm_refl. Qed.
Lemma D_ae07c : decode_any W_ae07c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae080 : bv 32 := 0x01029393.
Lemma F_ae080 : fetch_word Ubsan.M.loaded_segments (0xae0cc : word) = Some W_ae080.
Proof. vm_refl. Qed.
Lemma D_ae080 : decode_any W_ae080 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae084 : bv 32 := 0x0102d29b.
Lemma F_ae084 : fetch_word Ubsan.M.loaded_segments (0xae0d0 : word) = Some W_ae084.
Proof. vm_refl. Qed.
Lemma D_ae084 : decode_any W_ae084 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae088 : bv 32 := 0x0113e8b3.
Lemma F_ae088 : fetch_word Ubsan.M.loaded_segments (0xae0d4 : word) = Some W_ae088.
Proof. vm_refl. Qed.
Lemma D_ae088 : decode_any W_ae088 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae08c : bv 32 := 0x01031393.
Lemma F_ae08c : fetch_word Ubsan.M.loaded_segments (0xae0d8 : word) = Some W_ae08c.
Proof. vm_refl. Qed.
Lemma D_ae08c : decode_any W_ae08c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae090 : bv 32 := 0x0103531b.
Lemma F_ae090 : fetch_word Ubsan.M.loaded_segments (0xae0dc : word) = Some W_ae090.
Proof. vm_refl. Qed.
Lemma D_ae090 : decode_any W_ae090 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae094 : bv 32 := 0x0053e2b3.
Lemma F_ae094 : fetch_word Ubsan.M.loaded_segments (0xae0e0 : word) = Some W_ae094.
Proof. vm_refl. Qed.
Lemma D_ae094 : decode_any W_ae094 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae098 : bv 32 := 0x01071393.
Lemma F_ae098 : fetch_word Ubsan.M.loaded_segments (0xae0e4 : word) = Some W_ae098.
Proof. vm_refl. Qed.
Lemma D_ae098 : decode_any W_ae098 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae09c : bv 32 := 0x0063e333.
Lemma F_ae09c : fetch_word Ubsan.M.loaded_segments (0xae0e8 : word) = Some W_ae09c.
Proof. vm_refl. Qed.
Lemma D_ae09c : decode_any W_ae09c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0a0 : bv 32 := 0xff060613.
Lemma F_ae0a0 : fetch_word Ubsan.M.loaded_segments (0xae0ec : word) = Some W_ae0a0.
Proof. vm_refl. Qed.
Lemma D_ae0a0 : decode_any W_ae0a0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0a4 : bv 32 := 0x0106a023.
Lemma F_ae0a4 : fetch_word Ubsan.M.loaded_segments (0xae0f0 : word) = Some W_ae0a4.
Proof. vm_refl. Qed.
Lemma D_ae0a4 : decode_any W_ae0a4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0a8 : bv 32 := 0x0116a223.
Lemma F_ae0a8 : fetch_word Ubsan.M.loaded_segments (0xae0f4 : word) = Some W_ae0a8.
Proof. vm_refl. Qed.
Lemma D_ae0a8 : decode_any W_ae0a8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0ac : bv 32 := 0x0056a423.
Lemma F_ae0ac : fetch_word Ubsan.M.loaded_segments (0xae0f8 : word) = Some W_ae0ac.
Proof. vm_refl. Qed.
Lemma D_ae0ac : decode_any W_ae0ac = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0b0 : bv 32 := 0x0066a623.
Lemma F_ae0b0 : fetch_word Ubsan.M.loaded_segments (0xae0fc : word) = Some W_ae0b0.
Proof. vm_refl. Qed.
Lemma D_ae0b0 : decode_any W_ae0b0 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0b4 : bv 32 := 0x01068693.
Lemma F_ae0b4 : fetch_word Ubsan.M.loaded_segments (0xae100 : word) = Some W_ae0b4.
Proof. vm_refl. Qed.
Lemma D_ae0b4 : decode_any W_ae0b4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0b8 : bv 32 := 0x01058593.
Lemma F_ae0b8 : fetch_word Ubsan.M.loaded_segments (0xae104 : word) = Some W_ae0b8.
Proof. vm_refl. Qed.
Lemma D_ae0b8 : decode_any W_ae0b8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0bc : bv 32 := 0xfac7e2e3.
Lemma F_ae0bc : fetch_word Ubsan.M.loaded_segments (0xae108 : word) = Some W_ae0bc.
Proof. vm_refl. Qed.
Lemma D_ae0bc : decode_any W_ae0bc = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0c0 : bv 32 := 0xff258593.
Lemma F_ae0c0 : fetch_word Ubsan.M.loaded_segments (0xae10c : word) = Some W_ae0c0.
Proof. vm_refl. Qed.
Lemma D_ae0c0 : decode_any W_ae0c0 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0c4 : bv 32 := 0x01000713.
Lemma F_ae0c4 : fetch_word Ubsan.M.loaded_segments (0xae110 : word) = Some W_ae0c4.
Proof. vm_refl. Qed.
Lemma D_ae0c4 : decode_any W_ae0c4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0c8 : bv 32 := 0xf4e66ae3.
Lemma F_ae0c8 : fetch_word Ubsan.M.loaded_segments (0xae114 : word) = Some W_ae0c8.
Proof. vm_refl. Qed.
Lemma D_ae0c8 : decode_any W_ae0c8 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0cc : bv 32 := 0x19c0006f.
Lemma F_ae0cc : fetch_word Ubsan.M.loaded_segments (0xae118 : word) = Some W_ae0cc.
Proof. vm_refl. Qed.
Lemma D_ae0cc : decode_any W_ae0cc = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0d0 : bv 32 := 0x00050693.
Lemma F_ae0d0 : fetch_word Ubsan.M.loaded_segments (0xae11c : word) = Some W_ae0d0.
Proof. vm_refl. Qed.
Lemma D_ae0d0 : decode_any W_ae0d0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0d4 : bv 32 := 0x00357793.
Lemma F_ae0d4 : fetch_word Ubsan.M.loaded_segments (0xae120 : word) = Some W_ae0d4.
Proof. vm_refl. Qed.
Lemma D_ae0d4 : decode_any W_ae0d4 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae0d8 : bv 32 := 0xf2079ae3.
Lemma F_ae0d8 : fetch_word Ubsan.M.loaded_segments (0xae124 : word) = Some W_ae0d8.
Proof. vm_refl. Qed.
Lemma D_ae0d8 : decode_any W_ae0d8 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.
