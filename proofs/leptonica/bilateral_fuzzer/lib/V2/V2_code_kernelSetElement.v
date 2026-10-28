(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_38940 : bv 32 := 0x0a050863.
Lemma F_38940 : fetch_word Ubsan.M.loaded_segments (0x38940 : word) = Some W_38940.
Proof. vm_refl. Qed.
Lemma D_38940 : decode_any W_38940 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_38944 : bv 32 := 0x0805c063.
Lemma F_38944 : fetch_word Ubsan.M.loaded_segments (0x38944 : word) = Some W_38944.
Proof. vm_refl. Qed.
Lemma D_38944 : decode_any W_38944 = Some (Branch BC_LT 11 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_38948 : bv 32 := 0x00757693.
Lemma F_38948 : fetch_word Ubsan.M.loaded_segments (0x38948 : word) = Some W_38948.
Proof. vm_refl. Qed.
Lemma D_38948 : decode_any W_38948 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3894c : bv 32 := 0x10069263.
Lemma F_3894c : fetch_word Ubsan.M.loaded_segments (0x3894c : word) = Some W_3894c.
Proof. vm_refl. Qed.
Lemma D_3894c : decode_any W_3894c = Some (Branch BC_NE 13 0 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_38950 : bv 32 := 0x00052683.
Lemma F_38950 : fetch_word Ubsan.M.loaded_segments (0x38950 : word) = Some W_38950.
Proof. vm_refl. Qed.
Lemma D_38950 : decode_any W_38950 = Some (Load SZ4 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38954 : bv 32 := 0x06d5d863.
Lemma F_38954 : fetch_word Ubsan.M.loaded_segments (0x38954 : word) = Some W_38954.
Proof. vm_refl. Qed.
Lemma D_38954 : decode_any W_38954 = Some (Branch BC_GE 11 13 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_38958 : bv 32 := 0x0c064263.
Lemma F_38958 : fetch_word Ubsan.M.loaded_segments (0x38958 : word) = Some W_38958.
Proof. vm_refl. Qed.
Lemma D_38958 : decode_any W_38958 = Some (Branch BC_LT 12 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_3895c : bv 32 := 0x00452683.
Lemma F_3895c : fetch_word Ubsan.M.loaded_segments (0x3895c : word) = Some W_3895c.
Proof. vm_refl. Qed.
Lemma D_3895c : decode_any W_3895c = Some (Load SZ4 true 13 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38960 : bv 32 := 0x0ad65e63.
Lemma F_38960 : fetch_word Ubsan.M.loaded_segments (0x38960 : word) = Some W_38960.
Proof. vm_refl. Qed.
Lemma D_38960 : decode_any W_38960 = Some (Branch BC_GE 12 13 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_38964 : bv 32 := 0x01053683.
Lemma F_38964 : fetch_word Ubsan.M.loaded_segments (0x38964 : word) = Some W_38964.
Proof. vm_refl. Qed.
Lemma D_38964 : decode_any W_38964 = Some (Load SZ8 true 13 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38968 : bv 32 := 0x00359513.
Lemma F_38968 : fetch_word Ubsan.M.loaded_segments (0x38968 : word) = Some W_38968.
Proof. vm_refl. Qed.
Lemma D_38968 : decode_any W_38968 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3896c : bv 32 := 0x00a68533.
Lemma F_3896c : fetch_word Ubsan.M.loaded_segments (0x3896c : word) = Some W_3896c.
Proof. vm_refl. Qed.
Lemma D_3896c : decode_any W_3896c = Some (Op ALU_ADD 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_38970 : bv 32 := 0x0ed56063.
Lemma F_38970 : fetch_word Ubsan.M.loaded_segments (0x38970 : word) = Some W_38970.
Proof. vm_refl. Qed.
Lemma D_38970 : decode_any W_38970 = Some (Branch BC_LTU 10 13 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_38974 : bv 32 := 0x00d035b3.
Lemma F_38974 : fetch_word Ubsan.M.loaded_segments (0x38974 : word) = Some W_38974.
Proof. vm_refl. Qed.
Lemma D_38974 : decode_any W_38974 = Some (Op ALU_SLTU 11 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_38978 : bv 32 := 0x00153713.
Lemma F_38978 : fetch_word Ubsan.M.loaded_segments (0x38978 : word) = Some W_38978.
Proof. vm_refl. Qed.
Lemma D_38978 : decode_any W_38978 = Some (OpImm ALU_SLTU 14 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3897c : bv 32 := 0x00e5c5b3.
Lemma F_3897c : fetch_word Ubsan.M.loaded_segments (0x3897c : word) = Some W_3897c.
Proof. vm_refl. Qed.
Lemma D_3897c : decode_any W_3897c = Some (Op ALU_XOR 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_38980 : bv 32 := 0x0c058863.
Lemma F_38980 : fetch_word Ubsan.M.loaded_segments (0x38980 : word) = Some W_38980.
Proof. vm_refl. Qed.
Lemma D_38980 : decode_any W_38980 = Some (Branch BC_EQ 11 0 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_38984 : bv 32 := 0x0c068663.
Lemma F_38984 : fetch_word Ubsan.M.loaded_segments (0x38984 : word) = Some W_38984.
Proof. vm_refl. Qed.
Lemma D_38984 : decode_any W_38984 = Some (Branch BC_EQ 13 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_38988 : bv 32 := 0x00757593.
Lemma F_38988 : fetch_word Ubsan.M.loaded_segments (0x38988 : word) = Some W_38988.
Proof. vm_refl. Qed.
Lemma D_38988 : decode_any W_38988 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3898c : bv 32 := 0x0c059263.
Lemma F_3898c : fetch_word Ubsan.M.loaded_segments (0x3898c : word) = Some W_3898c.
Proof. vm_refl. Qed.
Lemma D_3898c : decode_any W_3898c = Some (Branch BC_NE 11 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_38990 : bv 32 := 0x00053503.
Lemma F_38990 : fetch_word Ubsan.M.loaded_segments (0x38990 : word) = Some W_38990.
Proof. vm_refl. Qed.
Lemma D_38990 : decode_any W_38990 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38994 : bv 32 := 0x00261593.
Lemma F_38994 : fetch_word Ubsan.M.loaded_segments (0x38994 : word) = Some W_38994.
Proof. vm_refl. Qed.
Lemma D_38994 : decode_any W_38994 = Some (ShiftImm ALU_SLL 11 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_38998 : bv 32 := 0x00b505b3.
Lemma F_38998 : fetch_word Ubsan.M.loaded_segments (0x38998 : word) = Some W_38998.
Proof. vm_refl. Qed.
Lemma D_38998 : decode_any W_38998 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3899c : bv 32 := 0x0aa5ea63.
Lemma F_3899c : fetch_word Ubsan.M.loaded_segments (0x3899c : word) = Some W_3899c.
Proof. vm_refl. Qed.
Lemma D_3899c : decode_any W_3899c = Some (Branch BC_LTU 11 10 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_389a0 : bv 32 := 0x00a03633.
Lemma F_389a0 : fetch_word Ubsan.M.loaded_segments (0x389a0 : word) = Some W_389a0.
Proof. vm_refl. Qed.
Lemma D_389a0 : decode_any W_389a0 = Some (Op ALU_SLTU 12 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_389a4 : bv 32 := 0x0015b693.
Lemma F_389a4 : fetch_word Ubsan.M.loaded_segments (0x389a4 : word) = Some W_389a4.
Proof. vm_refl. Qed.
Lemma D_389a4 : decode_any W_389a4 = Some (OpImm ALU_SLTU 13 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_389a8 : bv 32 := 0x00d64633.
Lemma F_389a8 : fetch_word Ubsan.M.loaded_segments (0x389a8 : word) = Some W_389a8.
Proof. vm_refl. Qed.
Lemma D_389a8 : decode_any W_389a8 = Some (Op ALU_XOR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_389ac : bv 32 := 0x0a060263.
Lemma F_389ac : fetch_word Ubsan.M.loaded_segments (0x389ac : word) = Some W_389ac.
Proof. vm_refl. Qed.
Lemma D_389ac : decode_any W_389ac = Some (Branch BC_EQ 12 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_389b0 : bv 32 := 0x0a050063.
Lemma F_389b0 : fetch_word Ubsan.M.loaded_segments (0x389b0 : word) = Some W_389b0.
Proof. vm_refl. Qed.
Lemma D_389b0 : decode_any W_389b0 = Some (Branch BC_EQ 10 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_389b4 : bv 32 := 0x0035f513.
Lemma F_389b4 : fetch_word Ubsan.M.loaded_segments (0x389b4 : word) = Some W_389b4.
Proof. vm_refl. Qed.
Lemma D_389b4 : decode_any W_389b4 = Some (OpImm ALU_AND 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_389b8 : bv 32 := 0x08051c63.
Lemma F_389b8 : fetch_word Ubsan.M.loaded_segments (0x389b8 : word) = Some W_389b8.
Proof. vm_refl. Qed.
Lemma D_389b8 : decode_any W_389b8 = Some (Branch BC_NE 10 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_389bc : bv 32 := 0x00a5a027.
Lemma F_389bc : fetch_word Ubsan.M.loaded_segments (0x389bc : word) = Some W_389bc.
Proof. vm_refl. Qed.
Lemma D_389bc : decode_any W_389bc = Some (FStore FMT_S 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_389c0 : bv 32 := 0x00008067.
Lemma F_389c0 : fetch_word Ubsan.M.loaded_segments (0x389c0 : word) = Some W_389c0.
Proof. vm_refl. Qed.
Lemma D_389c0 : decode_any W_389c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_389c4 : bv 32 := 0x0000c517.
Lemma F_389c4 : fetch_word Ubsan.M.loaded_segments (0x389c4 : word) = Some W_389c4.
Proof. vm_refl. Qed.
Lemma D_389c4 : decode_any W_389c4 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_389c8 : bv 32 := 0x4d453503.
Lemma F_389c8 : fetch_word Ubsan.M.loaded_segments (0x389c8 : word) = Some W_389c8.
Proof. vm_refl. Qed.
Lemma D_389c8 : decode_any W_389c8 = Some (Load SZ8 true 10 10 1236, 4%Z).
Proof. vm_refl. Qed.

Definition W_389cc : bv 32 := 0x00052503.
Lemma F_389cc : fetch_word Ubsan.M.loaded_segments (0x389cc : word) = Some W_389cc.
Proof. vm_refl. Qed.
Lemma D_389cc : decode_any W_389cc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_389d0 : bv 32 := 0x00500593.
Lemma F_389d0 : fetch_word Ubsan.M.loaded_segments (0x389d0 : word) = Some W_389d0.
Proof. vm_refl. Qed.
Lemma D_389d0 : decode_any W_389d0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_389d4 : bv 32 := 0x06a5ca63.
Lemma F_389d4 : fetch_word Ubsan.M.loaded_segments (0x389d4 : word) = Some W_389d4.
Proof. vm_refl. Qed.
Lemma D_389d4 : decode_any W_389d4 = Some (Branch BC_LT 11 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_389d8 : bv 32 := 0xfffd8517.
Lemma F_389d8 : fetch_word Ubsan.M.loaded_segments (0x389d8 : word) = Some W_389d8.
Proof. vm_refl. Qed.
Lemma D_389d8 : decode_any W_389d8 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_389dc : bv 32 := 0xfffd8597.
Lemma F_389dc : fetch_word Ubsan.M.loaded_segments (0x389dc : word) = Some W_389dc.
Proof. vm_refl. Qed.
Lemma D_389dc : decode_any W_389dc = Some (Auipc 11 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_389e0 : bv 32 := 0x3da50513.
Lemma F_389e0 : fetch_word Ubsan.M.loaded_segments (0x389e0 : word) = Some W_389e0.
Proof. vm_refl. Qed.
Lemma D_389e0 : decode_any W_389e0 = Some (OpImm ALU_ADD 10 10 986, 4%Z).
Proof. vm_refl. Qed.

Definition W_389e4 : bv 32 := 0x2c158593.
Lemma F_389e4 : fetch_word Ubsan.M.loaded_segments (0x389e4 : word) = Some W_389e4.
Proof. vm_refl. Qed.
Lemma D_389e4 : decode_any W_389e4 = Some (OpImm ALU_ADD 11 11 705, 4%Z).
Proof. vm_refl. Qed.

Definition W_389e8 : bv 32 := 0x00100613.
Lemma F_389e8 : fetch_word Ubsan.M.loaded_segments (0x389e8 : word) = Some W_389e8.
Proof. vm_refl. Qed.
Lemma D_389e8 : decode_any W_389e8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_389ec : bv 32 := 0xc08df06f.
Lemma F_389ec : fetch_word Ubsan.M.loaded_segments (0x389ec : word) = Some W_389ec.
Proof. vm_refl. Qed.
Lemma D_389ec : decode_any W_389ec = Some (Jal 0 1963016, 4%Z).
Proof. vm_refl. Qed.

Definition W_389f0 : bv 32 := 0x0000c517.
Lemma F_389f0 : fetch_word Ubsan.M.loaded_segments (0x389f0 : word) = Some W_389f0.
Proof. vm_refl. Qed.
Lemma D_389f0 : decode_any W_389f0 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_389f4 : bv 32 := 0x4a853503.
Lemma F_389f4 : fetch_word Ubsan.M.loaded_segments (0x389f4 : word) = Some W_389f4.
Proof. vm_refl. Qed.
Lemma D_389f4 : decode_any W_389f4 = Some (Load SZ8 true 10 10 1192, 4%Z).
Proof. vm_refl. Qed.

Definition W_389f8 : bv 32 := 0x00052503.
Lemma F_389f8 : fetch_word Ubsan.M.loaded_segments (0x389f8 : word) = Some W_389f8.
Proof. vm_refl. Qed.
Lemma D_389f8 : decode_any W_389f8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_389fc : bv 32 := 0x00500593.
Lemma F_389fc : fetch_word Ubsan.M.loaded_segments (0x389fc : word) = Some W_389fc.
Proof. vm_refl. Qed.
Lemma D_389fc : decode_any W_389fc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a00 : bv 32 := 0x04a5c463.
Lemma F_38a00 : fetch_word Ubsan.M.loaded_segments (0x38a00 : word) = Some W_38a00.
Proof. vm_refl. Qed.
Lemma D_38a00 : decode_any W_38a00 = Some (Branch BC_LT 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a04 : bv 32 := 0xfffd8517.
Lemma F_38a04 : fetch_word Ubsan.M.loaded_segments (0x38a04 : word) = Some W_38a04.
Proof. vm_refl. Qed.
Lemma D_38a04 : decode_any W_38a04 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a08 : bv 32 := 0xfffd8597.
Lemma F_38a08 : fetch_word Ubsan.M.loaded_segments (0x38a08 : word) = Some W_38a08.
Proof. vm_refl. Qed.
Lemma D_38a08 : decode_any W_38a08 = Some (Auipc 11 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a0c : bv 32 := 0xc9550513.
Lemma F_38a0c : fetch_word Ubsan.M.loaded_segments (0x38a0c : word) = Some W_38a0c.
Proof. vm_refl. Qed.
Lemma D_38a0c : decode_any W_38a0c = Some (OpImm ALU_ADD 10 10 3221, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a10 : bv 32 := 0x29558593.
Lemma F_38a10 : fetch_word Ubsan.M.loaded_segments (0x38a10 : word) = Some W_38a10.
Proof. vm_refl. Qed.
Lemma D_38a10 : decode_any W_38a10 = Some (OpImm ALU_ADD 11 11 661, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a14 : bv 32 := 0x00100613.
Lemma F_38a14 : fetch_word Ubsan.M.loaded_segments (0x38a14 : word) = Some W_38a14.
Proof. vm_refl. Qed.
Lemma D_38a14 : decode_any W_38a14 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a18 : bv 32 := 0xbdcdf06f.
Lemma F_38a18 : fetch_word Ubsan.M.loaded_segments (0x38a18 : word) = Some W_38a18.
Proof. vm_refl. Qed.
Lemma D_38a18 : decode_any W_38a18 = Some (Jal 0 1962972, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a1c : bv 32 := 0x0000c517.
Lemma F_38a1c : fetch_word Ubsan.M.loaded_segments (0x38a1c : word) = Some W_38a1c.
Proof. vm_refl. Qed.
Lemma D_38a1c : decode_any W_38a1c = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a20 : bv 32 := 0x47c53503.
Lemma F_38a20 : fetch_word Ubsan.M.loaded_segments (0x38a20 : word) = Some W_38a20.
Proof. vm_refl. Qed.
Lemma D_38a20 : decode_any W_38a20 = Some (Load SZ8 true 10 10 1148, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a24 : bv 32 := 0x00052503.
Lemma F_38a24 : fetch_word Ubsan.M.loaded_segments (0x38a24 : word) = Some W_38a24.
Proof. vm_refl. Qed.
Lemma D_38a24 : decode_any W_38a24 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a28 : bv 32 := 0x00500593.
Lemma F_38a28 : fetch_word Ubsan.M.loaded_segments (0x38a28 : word) = Some W_38a28.
Proof. vm_refl. Qed.
Lemma D_38a28 : decode_any W_38a28 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a2c : bv 32 := 0x00a5ce63.
Lemma F_38a2c : fetch_word Ubsan.M.loaded_segments (0x38a2c : word) = Some W_38a2c.
Proof. vm_refl. Qed.
Lemma D_38a2c : decode_any W_38a2c = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a30 : bv 32 := 0xfffd9517.
Lemma F_38a30 : fetch_word Ubsan.M.loaded_segments (0x38a30 : word) = Some W_38a30.
Proof. vm_refl. Qed.
Lemma D_38a30 : decode_any W_38a30 = Some (Auipc 10 1048537, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a34 : bv 32 := 0xfffd8597.
Lemma F_38a34 : fetch_word Ubsan.M.loaded_segments (0x38a34 : word) = Some W_38a34.
Proof. vm_refl. Qed.
Lemma D_38a34 : decode_any W_38a34 = Some (Auipc 11 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a38 : bv 32 := 0xc5750513.
Lemma F_38a38 : fetch_word Ubsan.M.loaded_segments (0x38a38 : word) = Some W_38a38.
Proof. vm_refl. Qed.
Lemma D_38a38 : decode_any W_38a38 = Some (OpImm ALU_ADD 10 10 3159, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a3c : bv 32 := 0x26958593.
Lemma F_38a3c : fetch_word Ubsan.M.loaded_segments (0x38a3c : word) = Some W_38a3c.
Proof. vm_refl. Qed.
Lemma D_38a3c : decode_any W_38a3c = Some (OpImm ALU_ADD 11 11 617, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a40 : bv 32 := 0x00100613.
Lemma F_38a40 : fetch_word Ubsan.M.loaded_segments (0x38a40 : word) = Some W_38a40.
Proof. vm_refl. Qed.
Lemma D_38a40 : decode_any W_38a40 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a44 : bv 32 := 0xbb0df06f.
Lemma F_38a44 : fetch_word Ubsan.M.loaded_segments (0x38a44 : word) = Some W_38a44.
Proof. vm_refl. Qed.
Lemma D_38a44 : decode_any W_38a44 = Some (Jal 0 1962928, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a48 : bv 32 := 0x00100513.
Lemma F_38a48 : fetch_word Ubsan.M.loaded_segments (0x38a48 : word) = Some W_38a48.
Proof. vm_refl. Qed.
Lemma D_38a48 : decode_any W_38a48 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a4c : bv 32 := 0x00008067.
Lemma F_38a4c : fetch_word Ubsan.M.loaded_segments (0x38a4c : word) = Some W_38a4c.
Proof. vm_refl. Qed.
Lemma D_38a4c : decode_any W_38a4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a50 : bv 32 := 0xc0001073.
Lemma F_38a50 : fetch_word Ubsan.M.loaded_segments (0x38a50 : word) = Some W_38a50.
Proof. vm_refl. Qed.
Lemma D_38a50 : decode_any W_38a50 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
