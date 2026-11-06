(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_79454 : bv 32 := 0x0ff5f593.
Lemma F_79454 : fetch_word Ubsan.M.loaded_segments (0x79454 : word) = Some W_79454.
Proof. vm_refl. Qed.
Lemma D_79454 : decode_any W_79454 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79458 : bv 32 := 0x00757693.
Lemma F_79458 : fetch_word Ubsan.M.loaded_segments (0x79458 : word) = Some W_79458.
Proof. vm_refl. Qed.
Lemma D_79458 : decode_any W_79458 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7945c : bv 32 := 0x00c03733.
Lemma F_7945c : fetch_word Ubsan.M.loaded_segments (0x7945c : word) = Some W_7945c.
Proof. vm_refl. Qed.
Lemma D_7945c : decode_any W_7945c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79460 : bv 32 := 0x02068c63.
Lemma F_79460 : fetch_word Ubsan.M.loaded_segments (0x79460 : word) = Some W_79460.
Proof. vm_refl. Qed.
Lemma D_79460 : decode_any W_79460 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79464 : bv 32 := 0x02060a63.
Lemma F_79464 : fetch_word Ubsan.M.loaded_segments (0x79464 : word) = Some W_79464.
Proof. vm_refl. Qed.
Lemma D_79464 : decode_any W_79464 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79468 : bv 32 := 0x00150793.
Lemma F_79468 : fetch_word Ubsan.M.loaded_segments (0x79468 : word) = Some W_79468.
Proof. vm_refl. Qed.
Lemma D_79468 : decode_any W_79468 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7946c : bv 32 := 0x00100813.
Lemma F_7946c : fetch_word Ubsan.M.loaded_segments (0x7946c : word) = Some W_7946c.
Proof. vm_refl. Qed.
Lemma D_7946c : decode_any W_7946c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79470 : bv 32 := 0x00054703.
Lemma F_79470 : fetch_word Ubsan.M.loaded_segments (0x79470 : word) = Some W_79470.
Proof. vm_refl. Qed.
Lemma D_79470 : decode_any W_79470 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79474 : bv 32 := 0x00060693.
Lemma F_79474 : fetch_word Ubsan.M.loaded_segments (0x79474 : word) = Some W_79474.
Proof. vm_refl. Qed.
Lemma D_79474 : decode_any W_79474 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79478 : bv 32 := 0x06b70e63.
Lemma F_79478 : fetch_word Ubsan.M.loaded_segments (0x79478 : word) = Some W_79478.
Proof. vm_refl. Qed.
Lemma D_79478 : decode_any W_79478 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7947c : bv 32 := 0x00150513.
Lemma F_7947c : fetch_word Ubsan.M.loaded_segments (0x7947c : word) = Some W_7947c.
Proof. vm_refl. Qed.
Lemma D_7947c : decode_any W_7947c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79480 : bv 32 := 0xfff68613.
Lemma F_79480 : fetch_word Ubsan.M.loaded_segments (0x79480 : word) = Some W_79480.
Proof. vm_refl. Qed.
Lemma D_79480 : decode_any W_79480 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79484 : bv 32 := 0x0077f893.
Lemma F_79484 : fetch_word Ubsan.M.loaded_segments (0x79484 : word) = Some W_79484.
Proof. vm_refl. Qed.
Lemma D_79484 : decode_any W_79484 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79488 : bv 32 := 0x00c03733.
Lemma F_79488 : fetch_word Ubsan.M.loaded_segments (0x79488 : word) = Some W_79488.
Proof. vm_refl. Qed.
Lemma D_79488 : decode_any W_79488 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7948c : bv 32 := 0x00088663.
Lemma F_7948c : fetch_word Ubsan.M.loaded_segments (0x7948c : word) = Some W_7948c.
Proof. vm_refl. Qed.
Lemma D_7948c : decode_any W_7948c = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79490 : bv 32 := 0x00178793.
Lemma F_79490 : fetch_word Ubsan.M.loaded_segments (0x79490 : word) = Some W_79490.
Proof. vm_refl. Qed.
Lemma D_79490 : decode_any W_79490 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79494 : bv 32 := 0xfd069ee3.
Lemma F_79494 : fetch_word Ubsan.M.loaded_segments (0x79494 : word) = Some W_79494.
Proof. vm_refl. Qed.
Lemma D_79494 : decode_any W_79494 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79498 : bv 32 := 0x06070863.
Lemma F_79498 : fetch_word Ubsan.M.loaded_segments (0x79498 : word) = Some W_79498.
Proof. vm_refl. Qed.
Lemma D_79498 : decode_any W_79498 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7949c : bv 32 := 0x00054683.
Lemma F_7949c : fetch_word Ubsan.M.loaded_segments (0x7949c : word) = Some W_7949c.
Proof. vm_refl. Qed.
Lemma D_7949c : decode_any W_7949c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794a0 : bv 32 := 0x04b68663.
Lemma F_794a0 : fetch_word Ubsan.M.loaded_segments (0x794a0 : word) = Some W_794a0.
Proof. vm_refl. Qed.
Lemma D_794a0 : decode_any W_794a0 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794a4 : bv 32 := 0x00800693.
Lemma F_794a4 : fetch_word Ubsan.M.loaded_segments (0x794a4 : word) = Some W_794a4.
Proof. vm_refl. Qed.
Lemma D_794a4 : decode_any W_794a4 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794a8 : bv 32 := 0x04d66263.
Lemma F_794a8 : fetch_word Ubsan.M.loaded_segments (0x794a8 : word) = Some W_794a8.
Proof. vm_refl. Qed.
Lemma D_794a8 : decode_any W_794a8 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794ac : bv 32 := 0xfff9c697.
Lemma F_794ac : fetch_word Ubsan.M.loaded_segments (0x794ac : word) = Some W_794ac.
Proof. vm_refl. Qed.
Lemma D_794ac : decode_any W_794ac = Some (Auipc 13 1048476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794b0 : bv 32 := 0x9e46b683.
Lemma F_794b0 : fetch_word Ubsan.M.loaded_segments (0x794b0 : word) = Some W_794b0.
Proof. vm_refl. Qed.
Lemma D_794b0 : decode_any W_794b0 = Some (Load SZ8 true 13 13 2532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794b4 : bv 32 := 0xfff9c717.
Lemma F_794b4 : fetch_word Ubsan.M.loaded_segments (0x794b4 : word) = Some W_794b4.
Proof. vm_refl. Qed.
Lemma D_794b4 : decode_any W_794b4 = Some (Auipc 14 1048476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794b8 : bv 32 := 0x9c473703.
Lemma F_794b8 : fetch_word Ubsan.M.loaded_segments (0x794b8 : word) = Some W_794b8.
Proof. vm_refl. Qed.
Lemma D_794b8 : decode_any W_794b8 = Some (Load SZ8 true 14 14 2500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794bc : bv 32 := 0x00168793.
Lemma F_794bc : fetch_word Ubsan.M.loaded_segments (0x794bc : word) = Some W_794bc.
Proof. vm_refl. Qed.
Lemma D_794bc : decode_any W_794bc = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794c0 : bv 32 := 0x02f587b3.
Lemma F_794c0 : fetch_word Ubsan.M.loaded_segments (0x794c0 : word) = Some W_794c0.
Proof. vm_refl. Qed.
Lemma D_794c0 : decode_any W_794c0 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794c4 : bv 32 := 0x00700813.
Lemma F_794c4 : fetch_word Ubsan.M.loaded_segments (0x794c4 : word) = Some W_794c4.
Proof. vm_refl. Qed.
Lemma D_794c4 : decode_any W_794c4 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794c8 : bv 32 := 0x00053883.
Lemma F_794c8 : fetch_word Ubsan.M.loaded_segments (0x794c8 : word) = Some W_794c8.
Proof. vm_refl. Qed.
Lemma D_794c8 : decode_any W_794c8 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794cc : bv 32 := 0x00f8c8b3.
Lemma F_794cc : fetch_word Ubsan.M.loaded_segments (0x794cc : word) = Some W_794cc.
Proof. vm_refl. Qed.
Lemma D_794cc : decode_any W_794cc = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794d0 : bv 32 := 0x411682b3.
Lemma F_794d0 : fetch_word Ubsan.M.loaded_segments (0x794d0 : word) = Some W_794d0.
Proof. vm_refl. Qed.
Lemma D_794d0 : decode_any W_794d0 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794d4 : bv 32 := 0x0112e8b3.
Lemma F_794d4 : fetch_word Ubsan.M.loaded_segments (0x794d4 : word) = Some W_794d4.
Proof. vm_refl. Qed.
Lemma D_794d4 : decode_any W_794d4 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794d8 : bv 32 := 0x00e8f8b3.
Lemma F_794d8 : fetch_word Ubsan.M.loaded_segments (0x794d8 : word) = Some W_794d8.
Proof. vm_refl. Qed.
Lemma D_794d8 : decode_any W_794d8 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794dc : bv 32 := 0x02e89a63.
Lemma F_794dc : fetch_word Ubsan.M.loaded_segments (0x794dc : word) = Some W_794dc.
Proof. vm_refl. Qed.
Lemma D_794dc : decode_any W_794dc = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794e0 : bv 32 := 0xff860613.
Lemma F_794e0 : fetch_word Ubsan.M.loaded_segments (0x794e0 : word) = Some W_794e0.
Proof. vm_refl. Qed.
Lemma D_794e0 : decode_any W_794e0 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794e4 : bv 32 := 0x00850513.
Lemma F_794e4 : fetch_word Ubsan.M.loaded_segments (0x794e4 : word) = Some W_794e4.
Proof. vm_refl. Qed.
Lemma D_794e4 : decode_any W_794e4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794e8 : bv 32 := 0xfec860e3.
Lemma F_794e8 : fetch_word Ubsan.M.loaded_segments (0x794e8 : word) = Some W_794e8.
Proof. vm_refl. Qed.
Lemma D_794e8 : decode_any W_794e8 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794ec : bv 32 := 0x00060693.
Lemma F_794ec : fetch_word Ubsan.M.loaded_segments (0x794ec : word) = Some W_794ec.
Proof. vm_refl. Qed.
Lemma D_794ec : decode_any W_794ec = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794f0 : bv 32 := 0x00060c63.
Lemma F_794f0 : fetch_word Ubsan.M.loaded_segments (0x794f0 : word) = Some W_794f0.
Proof. vm_refl. Qed.
Lemma D_794f0 : decode_any W_794f0 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794f4 : bv 32 := 0x00054603.
Lemma F_794f4 : fetch_word Ubsan.M.loaded_segments (0x794f4 : word) = Some W_794f4.
Proof. vm_refl. Qed.
Lemma D_794f4 : decode_any W_794f4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794f8 : bv 32 := 0x00b60a63.
Lemma F_794f8 : fetch_word Ubsan.M.loaded_segments (0x794f8 : word) = Some W_794f8.
Proof. vm_refl. Qed.
Lemma D_794f8 : decode_any W_794f8 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794fc : bv 32 := 0xfff68693.
Lemma F_794fc : fetch_word Ubsan.M.loaded_segments (0x794fc : word) = Some W_794fc.
Proof. vm_refl. Qed.
Lemma D_794fc : decode_any W_794fc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79500 : bv 32 := 0x00150513.
Lemma F_79500 : fetch_word Ubsan.M.loaded_segments (0x79500 : word) = Some W_79500.
Proof. vm_refl. Qed.
Lemma D_79500 : decode_any W_79500 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79504 : bv 32 := 0xfe0698e3.
Lemma F_79504 : fetch_word Ubsan.M.loaded_segments (0x79504 : word) = Some W_79504.
Proof. vm_refl. Qed.
Lemma D_79504 : decode_any W_79504 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79508 : bv 32 := 0x00000513.
Lemma F_79508 : fetch_word Ubsan.M.loaded_segments (0x79508 : word) = Some W_79508.
Proof. vm_refl. Qed.
Lemma D_79508 : decode_any W_79508 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7950c : bv 32 := 0x00008067.
Lemma F_7950c : fetch_word Ubsan.M.loaded_segments (0x7950c : word) = Some W_7950c.
Proof. vm_refl. Qed.
Lemma D_7950c : decode_any W_7950c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79510 : bv 32 := 0x00060693.
Lemma F_79510 : fetch_word Ubsan.M.loaded_segments (0x79510 : word) = Some W_79510.
Proof. vm_refl. Qed.
Lemma D_79510 : decode_any W_79510 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79514 : bv 32 := 0x00054603.
Lemma F_79514 : fetch_word Ubsan.M.loaded_segments (0x79514 : word) = Some W_79514.
Proof. vm_refl. Qed.
Lemma D_79514 : decode_any W_79514 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79518 : bv 32 := 0xfeb612e3.
Lemma F_79518 : fetch_word Ubsan.M.loaded_segments (0x79518 : word) = Some W_79518.
Proof. vm_refl. Qed.
Lemma D_79518 : decode_any W_79518 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7951c : bv 32 := 0xff1ff06f.
Lemma F_7951c : fetch_word Ubsan.M.loaded_segments (0x7951c : word) = Some W_7951c.
Proof. vm_refl. Qed.
Lemma D_7951c : decode_any W_7951c = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79520 : bv 32 := 0x02060063.
Lemma F_79520 : fetch_word Ubsan.M.loaded_segments (0x79520 : word) = Some W_79520.
Proof. vm_refl. Qed.
Lemma D_79520 : decode_any W_79520 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79524 : bv 32 := 0x00054683.
Lemma F_79524 : fetch_word Ubsan.M.loaded_segments (0x79524 : word) = Some W_79524.
Proof. vm_refl. Qed.
Lemma D_79524 : decode_any W_79524 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79528 : bv 32 := 0x0005c703.
Lemma F_79528 : fetch_word Ubsan.M.loaded_segments (0x79528 : word) = Some W_79528.
Proof. vm_refl. Qed.
Lemma D_79528 : decode_any W_79528 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7952c : bv 32 := 0x00e69e63.
Lemma F_7952c : fetch_word Ubsan.M.loaded_segments (0x7952c : word) = Some W_7952c.
Proof. vm_refl. Qed.
Lemma D_7952c : decode_any W_7952c = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79530 : bv 32 := 0xfff60613.
Lemma F_79530 : fetch_word Ubsan.M.loaded_segments (0x79530 : word) = Some W_79530.
Proof. vm_refl. Qed.
Lemma D_79530 : decode_any W_79530 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79534 : bv 32 := 0x00150513.
Lemma F_79534 : fetch_word Ubsan.M.loaded_segments (0x79534 : word) = Some W_79534.
Proof. vm_refl. Qed.
Lemma D_79534 : decode_any W_79534 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79538 : bv 32 := 0x00158593.
Lemma F_79538 : fetch_word Ubsan.M.loaded_segments (0x79538 : word) = Some W_79538.
Proof. vm_refl. Qed.
Lemma D_79538 : decode_any W_79538 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7953c : bv 32 := 0xfe0614e3.
Lemma F_7953c : fetch_word Ubsan.M.loaded_segments (0x7953c : word) = Some W_7953c.
Proof. vm_refl. Qed.
Lemma D_7953c : decode_any W_7953c = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79540 : bv 32 := 0x00000513.
Lemma F_79540 : fetch_word Ubsan.M.loaded_segments (0x79540 : word) = Some W_79540.
Proof. vm_refl. Qed.
Lemma D_79540 : decode_any W_79540 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79544 : bv 32 := 0x00008067.
Lemma F_79544 : fetch_word Ubsan.M.loaded_segments (0x79544 : word) = Some W_79544.
Proof. vm_refl. Qed.
Lemma D_79544 : decode_any W_79544 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79548 : bv 32 := 0x40e68533.
Lemma F_79548 : fetch_word Ubsan.M.loaded_segments (0x79548 : word) = Some W_79548.
Proof. vm_refl. Qed.
Lemma D_79548 : decode_any W_79548 = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7954c : bv 32 := 0x00008067.
Lemma F_7954c : fetch_word Ubsan.M.loaded_segments (0x7954c : word) = Some W_7954c.
Proof. vm_refl. Qed.
Lemma D_7954c : decode_any W_7954c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79550 : bv 32 := 0x0035f693.
Lemma F_79550 : fetch_word Ubsan.M.loaded_segments (0x79550 : word) = Some W_79550.
Proof. vm_refl. Qed.
Lemma D_79550 : decode_any W_79550 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79554 : bv 32 := 0x10068863.
Lemma F_79554 : fetch_word Ubsan.M.loaded_segments (0x79554 : word) = Some W_79554.
Proof. vm_refl. Qed.
Lemma D_79554 : decode_any W_79554 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79558 : bv 32 := 0x02060e63.
Lemma F_79558 : fetch_word Ubsan.M.loaded_segments (0x79558 : word) = Some W_79558.
Proof. vm_refl. Qed.
Lemma D_79558 : decode_any W_79558 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7955c : bv 32 := 0x00158713.
Lemma F_7955c : fetch_word Ubsan.M.loaded_segments (0x7955c : word) = Some W_7955c.
Proof. vm_refl. Qed.
Lemma D_7955c : decode_any W_7955c = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79560 : bv 32 := 0x00100793.
Lemma F_79560 : fetch_word Ubsan.M.loaded_segments (0x79560 : word) = Some W_79560.
Proof. vm_refl. Qed.
Lemma D_79560 : decode_any W_79560 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79564 : bv 32 := 0x00050693.
Lemma F_79564 : fetch_word Ubsan.M.loaded_segments (0x79564 : word) = Some W_79564.
Proof. vm_refl. Qed.
Lemma D_79564 : decode_any W_79564 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79568 : bv 32 := 0x0005c883.
Lemma F_79568 : fetch_word Ubsan.M.loaded_segments (0x79568 : word) = Some W_79568.
Proof. vm_refl. Qed.
Lemma D_79568 : decode_any W_79568 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7956c : bv 32 := 0x00060813.
Lemma F_7956c : fetch_word Ubsan.M.loaded_segments (0x7956c : word) = Some W_7956c.
Proof. vm_refl. Qed.
Lemma D_7956c : decode_any W_7956c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79570 : bv 32 := 0x00158593.
Lemma F_79570 : fetch_word Ubsan.M.loaded_segments (0x79570 : word) = Some W_79570.
Proof. vm_refl. Qed.
Lemma D_79570 : decode_any W_79570 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79574 : bv 32 := 0x00377293.
Lemma F_79574 : fetch_word Ubsan.M.loaded_segments (0x79574 : word) = Some W_79574.
Proof. vm_refl. Qed.
Lemma D_79574 : decode_any W_79574 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79578 : bv 32 := 0x01168023.
Lemma F_79578 : fetch_word Ubsan.M.loaded_segments (0x79578 : word) = Some W_79578.
Proof. vm_refl. Qed.
Lemma D_79578 : decode_any W_79578 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7957c : bv 32 := 0x00168693.
Lemma F_7957c : fetch_word Ubsan.M.loaded_segments (0x7957c : word) = Some W_7957c.
Proof. vm_refl. Qed.
Lemma D_7957c : decode_any W_7957c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79580 : bv 32 := 0xfff60613.
Lemma F_79580 : fetch_word Ubsan.M.loaded_segments (0x79580 : word) = Some W_79580.
Proof. vm_refl. Qed.
Lemma D_79580 : decode_any W_79580 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79584 : bv 32 := 0x00028a63.
Lemma F_79584 : fetch_word Ubsan.M.loaded_segments (0x79584 : word) = Some W_79584.
Proof. vm_refl. Qed.
Lemma D_79584 : decode_any W_79584 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79588 : bv 32 := 0x00170713.
Lemma F_79588 : fetch_word Ubsan.M.loaded_segments (0x79588 : word) = Some W_79588.
Proof. vm_refl. Qed.
Lemma D_79588 : decode_any W_79588 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7958c : bv 32 := 0xfcf81ee3.
Lemma F_7958c : fetch_word Ubsan.M.loaded_segments (0x7958c : word) = Some W_7958c.
Proof. vm_refl. Qed.
Lemma D_7958c : decode_any W_7958c = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79590 : bv 32 := 0x0080006f.
Lemma F_79590 : fetch_word Ubsan.M.loaded_segments (0x79590 : word) = Some W_79590.
Proof. vm_refl. Qed.
Lemma D_79590 : decode_any W_79590 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79594 : bv 32 := 0x00050693.
Lemma F_79594 : fetch_word Ubsan.M.loaded_segments (0x79594 : word) = Some W_79594.
Proof. vm_refl. Qed.
Lemma D_79594 : decode_any W_79594 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79598 : bv 32 := 0x0036f793.
Lemma F_79598 : fetch_word Ubsan.M.loaded_segments (0x79598 : word) = Some W_79598.
Proof. vm_refl. Qed.
Lemma D_79598 : decode_any W_79598 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7959c : bv 32 := 0x0c078a63.
Lemma F_7959c : fetch_word Ubsan.M.loaded_segments (0x7959c : word) = Some W_7959c.
Proof. vm_refl. Qed.
Lemma D_7959c : decode_any W_7959c = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795a0 : bv 32 := 0x02000713.
Lemma F_795a0 : fetch_word Ubsan.M.loaded_segments (0x795a0 : word) = Some W_795a0.
Proof. vm_refl. Qed.
Lemma D_795a0 : decode_any W_795a0 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795a4 : bv 32 := 0x02e67063.
Lemma F_795a4 : fetch_word Ubsan.M.loaded_segments (0x795a4 : word) = Some W_795a4.
Proof. vm_refl. Qed.
Lemma D_795a4 : decode_any W_795a4 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795a8 : bv 32 := 0x01000713.
Lemma F_795a8 : fetch_word Ubsan.M.loaded_segments (0x795a8 : word) = Some W_795a8.
Proof. vm_refl. Qed.
Lemma D_795a8 : decode_any W_795a8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795ac : bv 32 := 0x24e67863.
Lemma F_795ac : fetch_word Ubsan.M.loaded_segments (0x795ac : word) = Some W_795ac.
Proof. vm_refl. Qed.
Lemma D_795ac : decode_any W_795ac = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795b0 : bv 32 := 0x00867713.
Lemma F_795b0 : fetch_word Ubsan.M.loaded_segments (0x795b0 : word) = Some W_795b0.
Proof. vm_refl. Qed.
Lemma D_795b0 : decode_any W_795b0 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795b4 : bv 32 := 0x2c071e63.
Lemma F_795b4 : fetch_word Ubsan.M.loaded_segments (0x795b4 : word) = Some W_795b4.
Proof. vm_refl. Qed.
Lemma D_795b4 : decode_any W_795b4 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795b8 : bv 32 := 0x00467713.
Lemma F_795b8 : fetch_word Ubsan.M.loaded_segments (0x795b8 : word) = Some W_795b8.
Proof. vm_refl. Qed.
Lemma D_795b8 : decode_any W_795b8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795bc : bv 32 := 0x32071463.
Lemma F_795bc : fetch_word Ubsan.M.loaded_segments (0x795bc : word) = Some W_795bc.
Proof. vm_refl. Qed.
Lemma D_795bc : decode_any W_795bc = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795c0 : bv 32 := 0x3500006f.
Lemma F_795c0 : fetch_word Ubsan.M.loaded_segments (0x795c0 : word) = Some W_795c0.
Proof. vm_refl. Qed.
Lemma D_795c0 : decode_any W_795c0 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795c4 : bv 32 := 0x0005a703.
Lemma F_795c4 : fetch_word Ubsan.M.loaded_segments (0x795c4 : word) = Some W_795c4.
Proof. vm_refl. Qed.
Lemma D_795c4 : decode_any W_795c4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795c8 : bv 32 := 0x00300813.
Lemma F_795c8 : fetch_word Ubsan.M.loaded_segments (0x795c8 : word) = Some W_795c8.
Proof. vm_refl. Qed.
Lemma D_795c8 : decode_any W_795c8 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795cc : bv 32 := 0x11078e63.
Lemma F_795cc : fetch_word Ubsan.M.loaded_segments (0x795cc : word) = Some W_795cc.
Proof. vm_refl. Qed.
Lemma D_795cc : decode_any W_795cc = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795d0 : bv 32 := 0x00200813.
Lemma F_795d0 : fetch_word Ubsan.M.loaded_segments (0x795d0 : word) = Some W_795d0.
Proof. vm_refl. Qed.
Lemma D_795d0 : decode_any W_795d0 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795d4 : bv 32 := 0x19079c63.
Lemma F_795d4 : fetch_word Ubsan.M.loaded_segments (0x795d4 : word) = Some W_795d4.
Proof. vm_refl. Qed.
Lemma D_795d4 : decode_any W_795d4 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795d8 : bv 32 := 0x00875793.
Lemma F_795d8 : fetch_word Ubsan.M.loaded_segments (0x795d8 : word) = Some W_795d8.
Proof. vm_refl. Qed.
Lemma D_795d8 : decode_any W_795d8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795dc : bv 32 := 0xffe60613.
Lemma F_795dc : fetch_word Ubsan.M.loaded_segments (0x795dc : word) = Some W_795dc.
Proof. vm_refl. Qed.
Lemma D_795dc : decode_any W_795dc = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795e0 : bv 32 := 0x00e68023.
Lemma F_795e0 : fetch_word Ubsan.M.loaded_segments (0x795e0 : word) = Some W_795e0.
Proof. vm_refl. Qed.
Lemma D_795e0 : decode_any W_795e0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795e4 : bv 32 := 0x00f680a3.
Lemma F_795e4 : fetch_word Ubsan.M.loaded_segments (0x795e4 : word) = Some W_795e4.
Proof. vm_refl. Qed.
Lemma D_795e4 : decode_any W_795e4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795e8 : bv 32 := 0x00268693.
Lemma F_795e8 : fetch_word Ubsan.M.loaded_segments (0x795e8 : word) = Some W_795e8.
Proof. vm_refl. Qed.
Lemma D_795e8 : decode_any W_795e8 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795ec : bv 32 := 0x01058593.
Lemma F_795ec : fetch_word Ubsan.M.loaded_segments (0x795ec : word) = Some W_795ec.
Proof. vm_refl. Qed.
Lemma D_795ec : decode_any W_795ec = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795f0 : bv 32 := 0x01100793.
Lemma F_795f0 : fetch_word Ubsan.M.loaded_segments (0x795f0 : word) = Some W_795f0.
Proof. vm_refl. Qed.
Lemma D_795f0 : decode_any W_795f0 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795f4 : bv 32 := 0x0107581b.
Lemma F_795f4 : fetch_word Ubsan.M.loaded_segments (0x795f4 : word) = Some W_795f4.
Proof. vm_refl. Qed.
Lemma D_795f4 : decode_any W_795f4 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795f8 : bv 32 := 0xff45a883.
Lemma F_795f8 : fetch_word Ubsan.M.loaded_segments (0x795f8 : word) = Some W_795f8.
Proof. vm_refl. Qed.
Lemma D_795f8 : decode_any W_795f8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795fc : bv 32 := 0xff85a283.
Lemma F_795fc : fetch_word Ubsan.M.loaded_segments (0x795fc : word) = Some W_795fc.
Proof. vm_refl. Qed.
Lemma D_795fc : decode_any W_795fc = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79600 : bv 32 := 0xffc5a303.
Lemma F_79600 : fetch_word Ubsan.M.loaded_segments (0x79600 : word) = Some W_79600.
Proof. vm_refl. Qed.
Lemma D_79600 : decode_any W_79600 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79604 : bv 32 := 0x0005a703.
Lemma F_79604 : fetch_word Ubsan.M.loaded_segments (0x79604 : word) = Some W_79604.
Proof. vm_refl. Qed.
Lemma D_79604 : decode_any W_79604 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79608 : bv 32 := 0x01089393.
Lemma F_79608 : fetch_word Ubsan.M.loaded_segments (0x79608 : word) = Some W_79608.
Proof. vm_refl. Qed.
Lemma D_79608 : decode_any W_79608 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7960c : bv 32 := 0x0108d89b.
Lemma F_7960c : fetch_word Ubsan.M.loaded_segments (0x7960c : word) = Some W_7960c.
Proof. vm_refl. Qed.
Lemma D_7960c : decode_any W_7960c = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79610 : bv 32 := 0x0103e833.
Lemma F_79610 : fetch_word Ubsan.M.loaded_segments (0x79610 : word) = Some W_79610.
Proof. vm_refl. Qed.
Lemma D_79610 : decode_any W_79610 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79614 : bv 32 := 0x01029393.
Lemma F_79614 : fetch_word Ubsan.M.loaded_segments (0x79614 : word) = Some W_79614.
Proof. vm_refl. Qed.
Lemma D_79614 : decode_any W_79614 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79618 : bv 32 := 0x0102d29b.
Lemma F_79618 : fetch_word Ubsan.M.loaded_segments (0x79618 : word) = Some W_79618.
Proof. vm_refl. Qed.
Lemma D_79618 : decode_any W_79618 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7961c : bv 32 := 0x0113e8b3.
Lemma F_7961c : fetch_word Ubsan.M.loaded_segments (0x7961c : word) = Some W_7961c.
Proof. vm_refl. Qed.
Lemma D_7961c : decode_any W_7961c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79620 : bv 32 := 0x01031393.
Lemma F_79620 : fetch_word Ubsan.M.loaded_segments (0x79620 : word) = Some W_79620.
Proof. vm_refl. Qed.
Lemma D_79620 : decode_any W_79620 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79624 : bv 32 := 0x0103531b.
Lemma F_79624 : fetch_word Ubsan.M.loaded_segments (0x79624 : word) = Some W_79624.
Proof. vm_refl. Qed.
Lemma D_79624 : decode_any W_79624 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79628 : bv 32 := 0x0053e2b3.
Lemma F_79628 : fetch_word Ubsan.M.loaded_segments (0x79628 : word) = Some W_79628.
Proof. vm_refl. Qed.
Lemma D_79628 : decode_any W_79628 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7962c : bv 32 := 0x01071393.
Lemma F_7962c : fetch_word Ubsan.M.loaded_segments (0x7962c : word) = Some W_7962c.
Proof. vm_refl. Qed.
Lemma D_7962c : decode_any W_7962c = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79630 : bv 32 := 0x0063e333.
Lemma F_79630 : fetch_word Ubsan.M.loaded_segments (0x79630 : word) = Some W_79630.
Proof. vm_refl. Qed.
Lemma D_79630 : decode_any W_79630 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79634 : bv 32 := 0xff060613.
Lemma F_79634 : fetch_word Ubsan.M.loaded_segments (0x79634 : word) = Some W_79634.
Proof. vm_refl. Qed.
Lemma D_79634 : decode_any W_79634 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79638 : bv 32 := 0x0106a023.
Lemma F_79638 : fetch_word Ubsan.M.loaded_segments (0x79638 : word) = Some W_79638.
Proof. vm_refl. Qed.
Lemma D_79638 : decode_any W_79638 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7963c : bv 32 := 0x0116a223.
Lemma F_7963c : fetch_word Ubsan.M.loaded_segments (0x7963c : word) = Some W_7963c.
Proof. vm_refl. Qed.
Lemma D_7963c : decode_any W_7963c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79640 : bv 32 := 0x0056a423.
Lemma F_79640 : fetch_word Ubsan.M.loaded_segments (0x79640 : word) = Some W_79640.
Proof. vm_refl. Qed.
Lemma D_79640 : decode_any W_79640 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79644 : bv 32 := 0x0066a623.
Lemma F_79644 : fetch_word Ubsan.M.loaded_segments (0x79644 : word) = Some W_79644.
Proof. vm_refl. Qed.
Lemma D_79644 : decode_any W_79644 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79648 : bv 32 := 0x01068693.
Lemma F_79648 : fetch_word Ubsan.M.loaded_segments (0x79648 : word) = Some W_79648.
Proof. vm_refl. Qed.
Lemma D_79648 : decode_any W_79648 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7964c : bv 32 := 0x01058593.
Lemma F_7964c : fetch_word Ubsan.M.loaded_segments (0x7964c : word) = Some W_7964c.
Proof. vm_refl. Qed.
Lemma D_7964c : decode_any W_7964c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79650 : bv 32 := 0xfac7e2e3.
Lemma F_79650 : fetch_word Ubsan.M.loaded_segments (0x79650 : word) = Some W_79650.
Proof. vm_refl. Qed.
Lemma D_79650 : decode_any W_79650 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79654 : bv 32 := 0xff258593.
Lemma F_79654 : fetch_word Ubsan.M.loaded_segments (0x79654 : word) = Some W_79654.
Proof. vm_refl. Qed.
Lemma D_79654 : decode_any W_79654 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79658 : bv 32 := 0x01000713.
Lemma F_79658 : fetch_word Ubsan.M.loaded_segments (0x79658 : word) = Some W_79658.
Proof. vm_refl. Qed.
Lemma D_79658 : decode_any W_79658 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7965c : bv 32 := 0xf4e66ae3.
Lemma F_7965c : fetch_word Ubsan.M.loaded_segments (0x7965c : word) = Some W_7965c.
Proof. vm_refl. Qed.
Lemma D_7965c : decode_any W_7965c = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79660 : bv 32 := 0x19c0006f.
Lemma F_79660 : fetch_word Ubsan.M.loaded_segments (0x79660 : word) = Some W_79660.
Proof. vm_refl. Qed.
Lemma D_79660 : decode_any W_79660 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79664 : bv 32 := 0x00050693.
Lemma F_79664 : fetch_word Ubsan.M.loaded_segments (0x79664 : word) = Some W_79664.
Proof. vm_refl. Qed.
Lemma D_79664 : decode_any W_79664 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79668 : bv 32 := 0x00357793.
Lemma F_79668 : fetch_word Ubsan.M.loaded_segments (0x79668 : word) = Some W_79668.
Proof. vm_refl. Qed.
Lemma D_79668 : decode_any W_79668 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7966c : bv 32 := 0xf2079ae3.
Lemma F_7966c : fetch_word Ubsan.M.loaded_segments (0x7966c : word) = Some W_7966c.
Proof. vm_refl. Qed.
Lemma D_7966c : decode_any W_7966c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79670 : bv 32 := 0x01000713.
Lemma F_79670 : fetch_word Ubsan.M.loaded_segments (0x79670 : word) = Some W_79670.
Proof. vm_refl. Qed.
Lemma D_79670 : decode_any W_79670 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79674 : bv 32 := 0x02e66c63.
Lemma F_79674 : fetch_word Ubsan.M.loaded_segments (0x79674 : word) = Some W_79674.
Proof. vm_refl. Qed.
Lemma D_79674 : decode_any W_79674 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79678 : bv 32 := 0x00f00713.
Lemma F_79678 : fetch_word Ubsan.M.loaded_segments (0x79678 : word) = Some W_79678.
Proof. vm_refl. Qed.
Lemma D_79678 : decode_any W_79678 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7967c : bv 32 := 0x0005a783.
Lemma F_7967c : fetch_word Ubsan.M.loaded_segments (0x7967c : word) = Some W_7967c.
Proof. vm_refl. Qed.
Lemma D_7967c : decode_any W_7967c = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79680 : bv 32 := 0x0045a803.
Lemma F_79680 : fetch_word Ubsan.M.loaded_segments (0x79680 : word) = Some W_79680.
Proof. vm_refl. Qed.
Lemma D_79680 : decode_any W_79680 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79684 : bv 32 := 0x0085a883.
Lemma F_79684 : fetch_word Ubsan.M.loaded_segments (0x79684 : word) = Some W_79684.
Proof. vm_refl. Qed.
Lemma D_79684 : decode_any W_79684 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79688 : bv 32 := 0x00c5a283.
Lemma F_79688 : fetch_word Ubsan.M.loaded_segments (0x79688 : word) = Some W_79688.
Proof. vm_refl. Qed.
Lemma D_79688 : decode_any W_79688 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7968c : bv 32 := 0x01058593.
Lemma F_7968c : fetch_word Ubsan.M.loaded_segments (0x7968c : word) = Some W_7968c.
Proof. vm_refl. Qed.
Lemma D_7968c : decode_any W_7968c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79690 : bv 32 := 0xff060613.
Lemma F_79690 : fetch_word Ubsan.M.loaded_segments (0x79690 : word) = Some W_79690.
Proof. vm_refl. Qed.
Lemma D_79690 : decode_any W_79690 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79694 : bv 32 := 0x00f6a023.
Lemma F_79694 : fetch_word Ubsan.M.loaded_segments (0x79694 : word) = Some W_79694.
Proof. vm_refl. Qed.
Lemma D_79694 : decode_any W_79694 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79698 : bv 32 := 0x0106a223.
Lemma F_79698 : fetch_word Ubsan.M.loaded_segments (0x79698 : word) = Some W_79698.
Proof. vm_refl. Qed.
Lemma D_79698 : decode_any W_79698 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7969c : bv 32 := 0x0116a423.
Lemma F_7969c : fetch_word Ubsan.M.loaded_segments (0x7969c : word) = Some W_7969c.
Proof. vm_refl. Qed.
Lemma D_7969c : decode_any W_7969c = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796a0 : bv 32 := 0x0056a623.
Lemma F_796a0 : fetch_word Ubsan.M.loaded_segments (0x796a0 : word) = Some W_796a0.
Proof. vm_refl. Qed.
Lemma D_796a0 : decode_any W_796a0 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796a4 : bv 32 := 0x01068693.
Lemma F_796a4 : fetch_word Ubsan.M.loaded_segments (0x796a4 : word) = Some W_796a4.
Proof. vm_refl. Qed.
Lemma D_796a4 : decode_any W_796a4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796a8 : bv 32 := 0xfcc76ae3.
Lemma F_796a8 : fetch_word Ubsan.M.loaded_segments (0x796a8 : word) = Some W_796a8.
Proof. vm_refl. Qed.
Lemma D_796a8 : decode_any W_796a8 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796ac : bv 32 := 0x00800713.
Lemma F_796ac : fetch_word Ubsan.M.loaded_segments (0x796ac : word) = Some W_796ac.
Proof. vm_refl. Qed.
Lemma D_796ac : decode_any W_796ac = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796b0 : bv 32 := 0x00e66e63.
Lemma F_796b0 : fetch_word Ubsan.M.loaded_segments (0x796b0 : word) = Some W_796b0.
Proof. vm_refl. Qed.
Lemma D_796b0 : decode_any W_796b0 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796b4 : bv 32 := 0x0005a703.
Lemma F_796b4 : fetch_word Ubsan.M.loaded_segments (0x796b4 : word) = Some W_796b4.
Proof. vm_refl. Qed.
Lemma D_796b4 : decode_any W_796b4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796b8 : bv 32 := 0x0045a783.
Lemma F_796b8 : fetch_word Ubsan.M.loaded_segments (0x796b8 : word) = Some W_796b8.
Proof. vm_refl. Qed.
Lemma D_796b8 : decode_any W_796b8 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796bc : bv 32 := 0x00e6a023.
Lemma F_796bc : fetch_word Ubsan.M.loaded_segments (0x796bc : word) = Some W_796bc.
Proof. vm_refl. Qed.
Lemma D_796bc : decode_any W_796bc = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796c0 : bv 32 := 0x00f6a223.
Lemma F_796c0 : fetch_word Ubsan.M.loaded_segments (0x796c0 : word) = Some W_796c0.
Proof. vm_refl. Qed.
Lemma D_796c0 : decode_any W_796c0 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796c4 : bv 32 := 0x00868693.
Lemma F_796c4 : fetch_word Ubsan.M.loaded_segments (0x796c4 : word) = Some W_796c4.
Proof. vm_refl. Qed.
Lemma D_796c4 : decode_any W_796c4 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796c8 : bv 32 := 0x00858593.
Lemma F_796c8 : fetch_word Ubsan.M.loaded_segments (0x796c8 : word) = Some W_796c8.
Proof. vm_refl. Qed.
Lemma D_796c8 : decode_any W_796c8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796cc : bv 32 := 0x00467713.
Lemma F_796cc : fetch_word Ubsan.M.loaded_segments (0x796cc : word) = Some W_796cc.
Proof. vm_refl. Qed.
Lemma D_796cc : decode_any W_796cc = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796d0 : bv 32 := 0x24070063.
Lemma F_796d0 : fetch_word Ubsan.M.loaded_segments (0x796d0 : word) = Some W_796d0.
Proof. vm_refl. Qed.
Lemma D_796d0 : decode_any W_796d0 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796d4 : bv 32 := 0x0005a703.
Lemma F_796d4 : fetch_word Ubsan.M.loaded_segments (0x796d4 : word) = Some W_796d4.
Proof. vm_refl. Qed.
Lemma D_796d4 : decode_any W_796d4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796d8 : bv 32 := 0x00458593.
Lemma F_796d8 : fetch_word Ubsan.M.loaded_segments (0x796d8 : word) = Some W_796d8.
Proof. vm_refl. Qed.
Lemma D_796d8 : decode_any W_796d8 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796dc : bv 32 := 0x00e6a023.
Lemma F_796dc : fetch_word Ubsan.M.loaded_segments (0x796dc : word) = Some W_796dc.
Proof. vm_refl. Qed.
Lemma D_796dc : decode_any W_796dc = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796e0 : bv 32 := 0x00468693.
Lemma F_796e0 : fetch_word Ubsan.M.loaded_segments (0x796e0 : word) = Some W_796e0.
Proof. vm_refl. Qed.
Lemma D_796e0 : decode_any W_796e0 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796e4 : bv 32 := 0x22c0006f.
Lemma F_796e4 : fetch_word Ubsan.M.loaded_segments (0x796e4 : word) = Some W_796e4.
Proof. vm_refl. Qed.
Lemma D_796e4 : decode_any W_796e4 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796e8 : bv 32 := 0x00e68023.
Lemma F_796e8 : fetch_word Ubsan.M.loaded_segments (0x796e8 : word) = Some W_796e8.
Proof. vm_refl. Qed.
Lemma D_796e8 : decode_any W_796e8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796ec : bv 32 := 0x00168693.
Lemma F_796ec : fetch_word Ubsan.M.loaded_segments (0x796ec : word) = Some W_796ec.
Proof. vm_refl. Qed.
Lemma D_796ec : decode_any W_796ec = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796f0 : bv 32 := 0xfff60613.
Lemma F_796f0 : fetch_word Ubsan.M.loaded_segments (0x796f0 : word) = Some W_796f0.
Proof. vm_refl. Qed.
Lemma D_796f0 : decode_any W_796f0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796f4 : bv 32 := 0x01058593.
Lemma F_796f4 : fetch_word Ubsan.M.loaded_segments (0x796f4 : word) = Some W_796f4.
Proof. vm_refl. Qed.
Lemma D_796f4 : decode_any W_796f4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796f8 : bv 32 := 0x01200793.
Lemma F_796f8 : fetch_word Ubsan.M.loaded_segments (0x796f8 : word) = Some W_796f8.
Proof. vm_refl. Qed.
Lemma D_796f8 : decode_any W_796f8 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796fc : bv 32 := 0x0087581b.
Lemma F_796fc : fetch_word Ubsan.M.loaded_segments (0x796fc : word) = Some W_796fc.
Proof. vm_refl. Qed.
Lemma D_796fc : decode_any W_796fc = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79700 : bv 32 := 0xff45a883.
Lemma F_79700 : fetch_word Ubsan.M.loaded_segments (0x79700 : word) = Some W_79700.
Proof. vm_refl. Qed.
Lemma D_79700 : decode_any W_79700 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79704 : bv 32 := 0xff85a283.
Lemma F_79704 : fetch_word Ubsan.M.loaded_segments (0x79704 : word) = Some W_79704.
Proof. vm_refl. Qed.
Lemma D_79704 : decode_any W_79704 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79708 : bv 32 := 0xffc5a303.
Lemma F_79708 : fetch_word Ubsan.M.loaded_segments (0x79708 : word) = Some W_79708.
Proof. vm_refl. Qed.
Lemma D_79708 : decode_any W_79708 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7970c : bv 32 := 0x0005a703.
Lemma F_7970c : fetch_word Ubsan.M.loaded_segments (0x7970c : word) = Some W_7970c.
Proof. vm_refl. Qed.
Lemma D_7970c : decode_any W_7970c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79710 : bv 32 := 0x01889393.
Lemma F_79710 : fetch_word Ubsan.M.loaded_segments (0x79710 : word) = Some W_79710.
Proof. vm_refl. Qed.
Lemma D_79710 : decode_any W_79710 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79714 : bv 32 := 0x0088d89b.
Lemma F_79714 : fetch_word Ubsan.M.loaded_segments (0x79714 : word) = Some W_79714.
Proof. vm_refl. Qed.
Lemma D_79714 : decode_any W_79714 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79718 : bv 32 := 0x0103e833.
Lemma F_79718 : fetch_word Ubsan.M.loaded_segments (0x79718 : word) = Some W_79718.
Proof. vm_refl. Qed.
Lemma D_79718 : decode_any W_79718 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7971c : bv 32 := 0x01829393.
Lemma F_7971c : fetch_word Ubsan.M.loaded_segments (0x7971c : word) = Some W_7971c.
Proof. vm_refl. Qed.
Lemma D_7971c : decode_any W_7971c = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79720 : bv 32 := 0x0082d29b.
Lemma F_79720 : fetch_word Ubsan.M.loaded_segments (0x79720 : word) = Some W_79720.
Proof. vm_refl. Qed.
Lemma D_79720 : decode_any W_79720 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79724 : bv 32 := 0x0113e8b3.
Lemma F_79724 : fetch_word Ubsan.M.loaded_segments (0x79724 : word) = Some W_79724.
Proof. vm_refl. Qed.
Lemma D_79724 : decode_any W_79724 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79728 : bv 32 := 0x01831393.
Lemma F_79728 : fetch_word Ubsan.M.loaded_segments (0x79728 : word) = Some W_79728.
Proof. vm_refl. Qed.
Lemma D_79728 : decode_any W_79728 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7972c : bv 32 := 0x0083531b.
Lemma F_7972c : fetch_word Ubsan.M.loaded_segments (0x7972c : word) = Some W_7972c.
Proof. vm_refl. Qed.
Lemma D_7972c : decode_any W_7972c = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79730 : bv 32 := 0x0053e2b3.
Lemma F_79730 : fetch_word Ubsan.M.loaded_segments (0x79730 : word) = Some W_79730.
Proof. vm_refl. Qed.
Lemma D_79730 : decode_any W_79730 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79734 : bv 32 := 0x01871393.
Lemma F_79734 : fetch_word Ubsan.M.loaded_segments (0x79734 : word) = Some W_79734.
Proof. vm_refl. Qed.
Lemma D_79734 : decode_any W_79734 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79738 : bv 32 := 0x0063e333.
Lemma F_79738 : fetch_word Ubsan.M.loaded_segments (0x79738 : word) = Some W_79738.
Proof. vm_refl. Qed.
Lemma D_79738 : decode_any W_79738 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7973c : bv 32 := 0xff060613.
Lemma F_7973c : fetch_word Ubsan.M.loaded_segments (0x7973c : word) = Some W_7973c.
Proof. vm_refl. Qed.
Lemma D_7973c : decode_any W_7973c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79740 : bv 32 := 0x0106a023.
Lemma F_79740 : fetch_word Ubsan.M.loaded_segments (0x79740 : word) = Some W_79740.
Proof. vm_refl. Qed.
Lemma D_79740 : decode_any W_79740 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79744 : bv 32 := 0x0116a223.
Lemma F_79744 : fetch_word Ubsan.M.loaded_segments (0x79744 : word) = Some W_79744.
Proof. vm_refl. Qed.
Lemma D_79744 : decode_any W_79744 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79748 : bv 32 := 0x0056a423.
Lemma F_79748 : fetch_word Ubsan.M.loaded_segments (0x79748 : word) = Some W_79748.
Proof. vm_refl. Qed.
Lemma D_79748 : decode_any W_79748 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7974c : bv 32 := 0x0066a623.
Lemma F_7974c : fetch_word Ubsan.M.loaded_segments (0x7974c : word) = Some W_7974c.
Proof. vm_refl. Qed.
Lemma D_7974c : decode_any W_7974c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79750 : bv 32 := 0x01068693.
Lemma F_79750 : fetch_word Ubsan.M.loaded_segments (0x79750 : word) = Some W_79750.
Proof. vm_refl. Qed.
Lemma D_79750 : decode_any W_79750 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79754 : bv 32 := 0x01058593.
Lemma F_79754 : fetch_word Ubsan.M.loaded_segments (0x79754 : word) = Some W_79754.
Proof. vm_refl. Qed.
Lemma D_79754 : decode_any W_79754 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79758 : bv 32 := 0xfac7e2e3.
Lemma F_79758 : fetch_word Ubsan.M.loaded_segments (0x79758 : word) = Some W_79758.
Proof. vm_refl. Qed.
Lemma D_79758 : decode_any W_79758 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7975c : bv 32 := 0xff158593.
Lemma F_7975c : fetch_word Ubsan.M.loaded_segments (0x7975c : word) = Some W_7975c.
Proof. vm_refl. Qed.
Lemma D_7975c : decode_any W_7975c = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79760 : bv 32 := 0x01000713.
Lemma F_79760 : fetch_word Ubsan.M.loaded_segments (0x79760 : word) = Some W_79760.
Proof. vm_refl. Qed.
Lemma D_79760 : decode_any W_79760 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79764 : bv 32 := 0xe4e666e3.
Lemma F_79764 : fetch_word Ubsan.M.loaded_segments (0x79764 : word) = Some W_79764.
Proof. vm_refl. Qed.
Lemma D_79764 : decode_any W_79764 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79768 : bv 32 := 0x0940006f.
Lemma F_79768 : fetch_word Ubsan.M.loaded_segments (0x79768 : word) = Some W_79768.
Proof. vm_refl. Qed.
Lemma D_79768 : decode_any W_79768 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7976c : bv 32 := 0x00875793.
Lemma F_7976c : fetch_word Ubsan.M.loaded_segments (0x7976c : word) = Some W_7976c.
Proof. vm_refl. Qed.
Lemma D_7976c : decode_any W_7976c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79770 : bv 32 := 0x01075813.
Lemma F_79770 : fetch_word Ubsan.M.loaded_segments (0x79770 : word) = Some W_79770.
Proof. vm_refl. Qed.
Lemma D_79770 : decode_any W_79770 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79774 : bv 32 := 0xffd60613.
Lemma F_79774 : fetch_word Ubsan.M.loaded_segments (0x79774 : word) = Some W_79774.
Proof. vm_refl. Qed.
Lemma D_79774 : decode_any W_79774 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79778 : bv 32 := 0x00e68023.
Lemma F_79778 : fetch_word Ubsan.M.loaded_segments (0x79778 : word) = Some W_79778.
Proof. vm_refl. Qed.
Lemma D_79778 : decode_any W_79778 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7977c : bv 32 := 0x00f680a3.
Lemma F_7977c : fetch_word Ubsan.M.loaded_segments (0x7977c : word) = Some W_7977c.
Proof. vm_refl. Qed.
Lemma D_7977c : decode_any W_7977c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79780 : bv 32 := 0x01068123.
Lemma F_79780 : fetch_word Ubsan.M.loaded_segments (0x79780 : word) = Some W_79780.
Proof. vm_refl. Qed.
Lemma D_79780 : decode_any W_79780 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79784 : bv 32 := 0x00368693.
Lemma F_79784 : fetch_word Ubsan.M.loaded_segments (0x79784 : word) = Some W_79784.
Proof. vm_refl. Qed.
Lemma D_79784 : decode_any W_79784 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79788 : bv 32 := 0x01058593.
Lemma F_79788 : fetch_word Ubsan.M.loaded_segments (0x79788 : word) = Some W_79788.
Proof. vm_refl. Qed.
Lemma D_79788 : decode_any W_79788 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7978c : bv 32 := 0x01000793.
Lemma F_7978c : fetch_word Ubsan.M.loaded_segments (0x7978c : word) = Some W_7978c.
Proof. vm_refl. Qed.
Lemma D_7978c : decode_any W_7978c = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79790 : bv 32 := 0x0187581b.
Lemma F_79790 : fetch_word Ubsan.M.loaded_segments (0x79790 : word) = Some W_79790.
Proof. vm_refl. Qed.
Lemma D_79790 : decode_any W_79790 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79794 : bv 32 := 0xff45a883.
Lemma F_79794 : fetch_word Ubsan.M.loaded_segments (0x79794 : word) = Some W_79794.
Proof. vm_refl. Qed.
Lemma D_79794 : decode_any W_79794 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79798 : bv 32 := 0xff85a283.
Lemma F_79798 : fetch_word Ubsan.M.loaded_segments (0x79798 : word) = Some W_79798.
Proof. vm_refl. Qed.
Lemma D_79798 : decode_any W_79798 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7979c : bv 32 := 0xffc5a303.
Lemma F_7979c : fetch_word Ubsan.M.loaded_segments (0x7979c : word) = Some W_7979c.
Proof. vm_refl. Qed.
Lemma D_7979c : decode_any W_7979c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797a0 : bv 32 := 0x0005a703.
Lemma F_797a0 : fetch_word Ubsan.M.loaded_segments (0x797a0 : word) = Some W_797a0.
Proof. vm_refl. Qed.
Lemma D_797a0 : decode_any W_797a0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797a4 : bv 32 := 0x00889393.
Lemma F_797a4 : fetch_word Ubsan.M.loaded_segments (0x797a4 : word) = Some W_797a4.
Proof. vm_refl. Qed.
Lemma D_797a4 : decode_any W_797a4 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797a8 : bv 32 := 0x0188d89b.
Lemma F_797a8 : fetch_word Ubsan.M.loaded_segments (0x797a8 : word) = Some W_797a8.
Proof. vm_refl. Qed.
Lemma D_797a8 : decode_any W_797a8 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797ac : bv 32 := 0x0103e833.
Lemma F_797ac : fetch_word Ubsan.M.loaded_segments (0x797ac : word) = Some W_797ac.
Proof. vm_refl. Qed.
Lemma D_797ac : decode_any W_797ac = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797b0 : bv 32 := 0x00829393.
Lemma F_797b0 : fetch_word Ubsan.M.loaded_segments (0x797b0 : word) = Some W_797b0.
Proof. vm_refl. Qed.
Lemma D_797b0 : decode_any W_797b0 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797b4 : bv 32 := 0x0182d29b.
Lemma F_797b4 : fetch_word Ubsan.M.loaded_segments (0x797b4 : word) = Some W_797b4.
Proof. vm_refl. Qed.
Lemma D_797b4 : decode_any W_797b4 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797b8 : bv 32 := 0x0113e8b3.
Lemma F_797b8 : fetch_word Ubsan.M.loaded_segments (0x797b8 : word) = Some W_797b8.
Proof. vm_refl. Qed.
Lemma D_797b8 : decode_any W_797b8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797bc : bv 32 := 0x00831393.
Lemma F_797bc : fetch_word Ubsan.M.loaded_segments (0x797bc : word) = Some W_797bc.
Proof. vm_refl. Qed.
Lemma D_797bc : decode_any W_797bc = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797c0 : bv 32 := 0x0183531b.
Lemma F_797c0 : fetch_word Ubsan.M.loaded_segments (0x797c0 : word) = Some W_797c0.
Proof. vm_refl. Qed.
Lemma D_797c0 : decode_any W_797c0 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797c4 : bv 32 := 0x0053e2b3.
Lemma F_797c4 : fetch_word Ubsan.M.loaded_segments (0x797c4 : word) = Some W_797c4.
Proof. vm_refl. Qed.
Lemma D_797c4 : decode_any W_797c4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797c8 : bv 32 := 0x00871393.
Lemma F_797c8 : fetch_word Ubsan.M.loaded_segments (0x797c8 : word) = Some W_797c8.
Proof. vm_refl. Qed.
Lemma D_797c8 : decode_any W_797c8 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797cc : bv 32 := 0x0063e333.
Lemma F_797cc : fetch_word Ubsan.M.loaded_segments (0x797cc : word) = Some W_797cc.
Proof. vm_refl. Qed.
Lemma D_797cc : decode_any W_797cc = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797d0 : bv 32 := 0xff060613.
Lemma F_797d0 : fetch_word Ubsan.M.loaded_segments (0x797d0 : word) = Some W_797d0.
Proof. vm_refl. Qed.
Lemma D_797d0 : decode_any W_797d0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797d4 : bv 32 := 0x0106a023.
Lemma F_797d4 : fetch_word Ubsan.M.loaded_segments (0x797d4 : word) = Some W_797d4.
Proof. vm_refl. Qed.
Lemma D_797d4 : decode_any W_797d4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797d8 : bv 32 := 0x0116a223.
Lemma F_797d8 : fetch_word Ubsan.M.loaded_segments (0x797d8 : word) = Some W_797d8.
Proof. vm_refl. Qed.
Lemma D_797d8 : decode_any W_797d8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797dc : bv 32 := 0x0056a423.
Lemma F_797dc : fetch_word Ubsan.M.loaded_segments (0x797dc : word) = Some W_797dc.
Proof. vm_refl. Qed.
Lemma D_797dc : decode_any W_797dc = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797e0 : bv 32 := 0x0066a623.
Lemma F_797e0 : fetch_word Ubsan.M.loaded_segments (0x797e0 : word) = Some W_797e0.
Proof. vm_refl. Qed.
Lemma D_797e0 : decode_any W_797e0 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797e4 : bv 32 := 0x01068693.
Lemma F_797e4 : fetch_word Ubsan.M.loaded_segments (0x797e4 : word) = Some W_797e4.
Proof. vm_refl. Qed.
Lemma D_797e4 : decode_any W_797e4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797e8 : bv 32 := 0x01058593.
Lemma F_797e8 : fetch_word Ubsan.M.loaded_segments (0x797e8 : word) = Some W_797e8.
Proof. vm_refl. Qed.
Lemma D_797e8 : decode_any W_797e8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797ec : bv 32 := 0xfac7e2e3.
Lemma F_797ec : fetch_word Ubsan.M.loaded_segments (0x797ec : word) = Some W_797ec.
Proof. vm_refl. Qed.
Lemma D_797ec : decode_any W_797ec = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797f0 : bv 32 := 0xff358593.
Lemma F_797f0 : fetch_word Ubsan.M.loaded_segments (0x797f0 : word) = Some W_797f0.
Proof. vm_refl. Qed.
Lemma D_797f0 : decode_any W_797f0 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797f4 : bv 32 := 0x01000713.
Lemma F_797f4 : fetch_word Ubsan.M.loaded_segments (0x797f4 : word) = Some W_797f4.
Proof. vm_refl. Qed.
Lemma D_797f4 : decode_any W_797f4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797f8 : bv 32 := 0xdae66ce3.
Lemma F_797f8 : fetch_word Ubsan.M.loaded_segments (0x797f8 : word) = Some W_797f8.
Proof. vm_refl. Qed.
Lemma D_797f8 : decode_any W_797f8 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_797fc : bv 32 := 0x0005c703.
Lemma F_797fc : fetch_word Ubsan.M.loaded_segments (0x797fc : word) = Some W_797fc.
Proof. vm_refl. Qed.
Lemma D_797fc : decode_any W_797fc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79800 : bv 32 := 0x0015c783.
Lemma F_79800 : fetch_word Ubsan.M.loaded_segments (0x79800 : word) = Some W_79800.
Proof. vm_refl. Qed.
Lemma D_79800 : decode_any W_79800 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79804 : bv 32 := 0x0025c803.
Lemma F_79804 : fetch_word Ubsan.M.loaded_segments (0x79804 : word) = Some W_79804.
Proof. vm_refl. Qed.
Lemma D_79804 : decode_any W_79804 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79808 : bv 32 := 0x0035c883.
Lemma F_79808 : fetch_word Ubsan.M.loaded_segments (0x79808 : word) = Some W_79808.
Proof. vm_refl. Qed.
Lemma D_79808 : decode_any W_79808 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7980c : bv 32 := 0x0045c283.
Lemma F_7980c : fetch_word Ubsan.M.loaded_segments (0x7980c : word) = Some W_7980c.
Proof. vm_refl. Qed.
Lemma D_7980c : decode_any W_7980c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79810 : bv 32 := 0x0055c303.
Lemma F_79810 : fetch_word Ubsan.M.loaded_segments (0x79810 : word) = Some W_79810.
Proof. vm_refl. Qed.
Lemma D_79810 : decode_any W_79810 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79814 : bv 32 := 0x0065c383.
Lemma F_79814 : fetch_word Ubsan.M.loaded_segments (0x79814 : word) = Some W_79814.
Proof. vm_refl. Qed.
Lemma D_79814 : decode_any W_79814 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79818 : bv 32 := 0x0075ce03.
Lemma F_79818 : fetch_word Ubsan.M.loaded_segments (0x79818 : word) = Some W_79818.
Proof. vm_refl. Qed.
Lemma D_79818 : decode_any W_79818 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7981c : bv 32 := 0x00e68023.
Lemma F_7981c : fetch_word Ubsan.M.loaded_segments (0x7981c : word) = Some W_7981c.
Proof. vm_refl. Qed.
Lemma D_7981c : decode_any W_7981c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79820 : bv 32 := 0x00f680a3.
Lemma F_79820 : fetch_word Ubsan.M.loaded_segments (0x79820 : word) = Some W_79820.
Proof. vm_refl. Qed.
Lemma D_79820 : decode_any W_79820 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79824 : bv 32 := 0x01068123.
Lemma F_79824 : fetch_word Ubsan.M.loaded_segments (0x79824 : word) = Some W_79824.
Proof. vm_refl. Qed.
Lemma D_79824 : decode_any W_79824 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79828 : bv 32 := 0x011681a3.
Lemma F_79828 : fetch_word Ubsan.M.loaded_segments (0x79828 : word) = Some W_79828.
Proof. vm_refl. Qed.
Lemma D_79828 : decode_any W_79828 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7982c : bv 32 := 0x0085c703.
Lemma F_7982c : fetch_word Ubsan.M.loaded_segments (0x7982c : word) = Some W_7982c.
Proof. vm_refl. Qed.
Lemma D_7982c : decode_any W_7982c = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79830 : bv 32 := 0x0095c783.
Lemma F_79830 : fetch_word Ubsan.M.loaded_segments (0x79830 : word) = Some W_79830.
Proof. vm_refl. Qed.
Lemma D_79830 : decode_any W_79830 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79834 : bv 32 := 0x00a5c803.
Lemma F_79834 : fetch_word Ubsan.M.loaded_segments (0x79834 : word) = Some W_79834.
Proof. vm_refl. Qed.
Lemma D_79834 : decode_any W_79834 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79838 : bv 32 := 0x00b5c883.
Lemma F_79838 : fetch_word Ubsan.M.loaded_segments (0x79838 : word) = Some W_79838.
Proof. vm_refl. Qed.
Lemma D_79838 : decode_any W_79838 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7983c : bv 32 := 0x00568223.
Lemma F_7983c : fetch_word Ubsan.M.loaded_segments (0x7983c : word) = Some W_7983c.
Proof. vm_refl. Qed.
Lemma D_7983c : decode_any W_7983c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79840 : bv 32 := 0x006682a3.
Lemma F_79840 : fetch_word Ubsan.M.loaded_segments (0x79840 : word) = Some W_79840.
Proof. vm_refl. Qed.
Lemma D_79840 : decode_any W_79840 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79844 : bv 32 := 0x00768323.
Lemma F_79844 : fetch_word Ubsan.M.loaded_segments (0x79844 : word) = Some W_79844.
Proof. vm_refl. Qed.
Lemma D_79844 : decode_any W_79844 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79848 : bv 32 := 0x01c683a3.
Lemma F_79848 : fetch_word Ubsan.M.loaded_segments (0x79848 : word) = Some W_79848.
Proof. vm_refl. Qed.
Lemma D_79848 : decode_any W_79848 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7984c : bv 32 := 0x00c5c283.
Lemma F_7984c : fetch_word Ubsan.M.loaded_segments (0x7984c : word) = Some W_7984c.
Proof. vm_refl. Qed.
Lemma D_7984c : decode_any W_7984c = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79850 : bv 32 := 0x00d5c303.
Lemma F_79850 : fetch_word Ubsan.M.loaded_segments (0x79850 : word) = Some W_79850.
Proof. vm_refl. Qed.
Lemma D_79850 : decode_any W_79850 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79854 : bv 32 := 0x00e5c383.
Lemma F_79854 : fetch_word Ubsan.M.loaded_segments (0x79854 : word) = Some W_79854.
Proof. vm_refl. Qed.
Lemma D_79854 : decode_any W_79854 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79858 : bv 32 := 0x00f5ce03.
Lemma F_79858 : fetch_word Ubsan.M.loaded_segments (0x79858 : word) = Some W_79858.
Proof. vm_refl. Qed.
Lemma D_79858 : decode_any W_79858 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7985c : bv 32 := 0x01058593.
Lemma F_7985c : fetch_word Ubsan.M.loaded_segments (0x7985c : word) = Some W_7985c.
Proof. vm_refl. Qed.
Lemma D_7985c : decode_any W_7985c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79860 : bv 32 := 0x00e68423.
Lemma F_79860 : fetch_word Ubsan.M.loaded_segments (0x79860 : word) = Some W_79860.
Proof. vm_refl. Qed.
Lemma D_79860 : decode_any W_79860 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79864 : bv 32 := 0x00f684a3.
Lemma F_79864 : fetch_word Ubsan.M.loaded_segments (0x79864 : word) = Some W_79864.
Proof. vm_refl. Qed.
Lemma D_79864 : decode_any W_79864 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79868 : bv 32 := 0x01068523.
Lemma F_79868 : fetch_word Ubsan.M.loaded_segments (0x79868 : word) = Some W_79868.
Proof. vm_refl. Qed.
Lemma D_79868 : decode_any W_79868 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7986c : bv 32 := 0x011685a3.
Lemma F_7986c : fetch_word Ubsan.M.loaded_segments (0x7986c : word) = Some W_7986c.
Proof. vm_refl. Qed.
Lemma D_7986c : decode_any W_7986c = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79870 : bv 32 := 0x01068713.
Lemma F_79870 : fetch_word Ubsan.M.loaded_segments (0x79870 : word) = Some W_79870.
Proof. vm_refl. Qed.
Lemma D_79870 : decode_any W_79870 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79874 : bv 32 := 0x00568623.
Lemma F_79874 : fetch_word Ubsan.M.loaded_segments (0x79874 : word) = Some W_79874.
Proof. vm_refl. Qed.
Lemma D_79874 : decode_any W_79874 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79878 : bv 32 := 0x006686a3.
Lemma F_79878 : fetch_word Ubsan.M.loaded_segments (0x79878 : word) = Some W_79878.
Proof. vm_refl. Qed.
Lemma D_79878 : decode_any W_79878 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7987c : bv 32 := 0x00768723.
Lemma F_7987c : fetch_word Ubsan.M.loaded_segments (0x7987c : word) = Some W_7987c.
Proof. vm_refl. Qed.
Lemma D_7987c : decode_any W_7987c = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79880 : bv 32 := 0x01c687a3.
Lemma F_79880 : fetch_word Ubsan.M.loaded_segments (0x79880 : word) = Some W_79880.
Proof. vm_refl. Qed.
Lemma D_79880 : decode_any W_79880 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79884 : bv 32 := 0x00070693.
Lemma F_79884 : fetch_word Ubsan.M.loaded_segments (0x79884 : word) = Some W_79884.
Proof. vm_refl. Qed.
Lemma D_79884 : decode_any W_79884 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79888 : bv 32 := 0x00867713.
Lemma F_79888 : fetch_word Ubsan.M.loaded_segments (0x79888 : word) = Some W_79888.
Proof. vm_refl. Qed.
Lemma D_79888 : decode_any W_79888 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7988c : bv 32 := 0xd20706e3.
Lemma F_7988c : fetch_word Ubsan.M.loaded_segments (0x7988c : word) = Some W_7988c.
Proof. vm_refl. Qed.
Lemma D_7988c : decode_any W_7988c = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79890 : bv 32 := 0x0005c703.
Lemma F_79890 : fetch_word Ubsan.M.loaded_segments (0x79890 : word) = Some W_79890.
Proof. vm_refl. Qed.
Lemma D_79890 : decode_any W_79890 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79894 : bv 32 := 0x0015c783.
Lemma F_79894 : fetch_word Ubsan.M.loaded_segments (0x79894 : word) = Some W_79894.
Proof. vm_refl. Qed.
Lemma D_79894 : decode_any W_79894 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79898 : bv 32 := 0x0025c803.
Lemma F_79898 : fetch_word Ubsan.M.loaded_segments (0x79898 : word) = Some W_79898.
Proof. vm_refl. Qed.
Lemma D_79898 : decode_any W_79898 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7989c : bv 32 := 0x0035c883.
Lemma F_7989c : fetch_word Ubsan.M.loaded_segments (0x7989c : word) = Some W_7989c.
Proof. vm_refl. Qed.
Lemma D_7989c : decode_any W_7989c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798a0 : bv 32 := 0x0045c283.
Lemma F_798a0 : fetch_word Ubsan.M.loaded_segments (0x798a0 : word) = Some W_798a0.
Proof. vm_refl. Qed.
Lemma D_798a0 : decode_any W_798a0 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798a4 : bv 32 := 0x0055c303.
Lemma F_798a4 : fetch_word Ubsan.M.loaded_segments (0x798a4 : word) = Some W_798a4.
Proof. vm_refl. Qed.
Lemma D_798a4 : decode_any W_798a4 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798a8 : bv 32 := 0x0065c383.
Lemma F_798a8 : fetch_word Ubsan.M.loaded_segments (0x798a8 : word) = Some W_798a8.
Proof. vm_refl. Qed.
Lemma D_798a8 : decode_any W_798a8 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798ac : bv 32 := 0x0075ce03.
Lemma F_798ac : fetch_word Ubsan.M.loaded_segments (0x798ac : word) = Some W_798ac.
Proof. vm_refl. Qed.
Lemma D_798ac : decode_any W_798ac = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798b0 : bv 32 := 0x00858593.
Lemma F_798b0 : fetch_word Ubsan.M.loaded_segments (0x798b0 : word) = Some W_798b0.
Proof. vm_refl. Qed.
Lemma D_798b0 : decode_any W_798b0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798b4 : bv 32 := 0x00e68023.
Lemma F_798b4 : fetch_word Ubsan.M.loaded_segments (0x798b4 : word) = Some W_798b4.
Proof. vm_refl. Qed.
Lemma D_798b4 : decode_any W_798b4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798b8 : bv 32 := 0x00f680a3.
Lemma F_798b8 : fetch_word Ubsan.M.loaded_segments (0x798b8 : word) = Some W_798b8.
Proof. vm_refl. Qed.
Lemma D_798b8 : decode_any W_798b8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798bc : bv 32 := 0x01068123.
Lemma F_798bc : fetch_word Ubsan.M.loaded_segments (0x798bc : word) = Some W_798bc.
Proof. vm_refl. Qed.
Lemma D_798bc : decode_any W_798bc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798c0 : bv 32 := 0x011681a3.
Lemma F_798c0 : fetch_word Ubsan.M.loaded_segments (0x798c0 : word) = Some W_798c0.
Proof. vm_refl. Qed.
Lemma D_798c0 : decode_any W_798c0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798c4 : bv 32 := 0x00868713.
Lemma F_798c4 : fetch_word Ubsan.M.loaded_segments (0x798c4 : word) = Some W_798c4.
Proof. vm_refl. Qed.
Lemma D_798c4 : decode_any W_798c4 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798c8 : bv 32 := 0x00568223.
Lemma F_798c8 : fetch_word Ubsan.M.loaded_segments (0x798c8 : word) = Some W_798c8.
Proof. vm_refl. Qed.
Lemma D_798c8 : decode_any W_798c8 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798cc : bv 32 := 0x006682a3.
Lemma F_798cc : fetch_word Ubsan.M.loaded_segments (0x798cc : word) = Some W_798cc.
Proof. vm_refl. Qed.
Lemma D_798cc : decode_any W_798cc = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798d0 : bv 32 := 0x00768323.
Lemma F_798d0 : fetch_word Ubsan.M.loaded_segments (0x798d0 : word) = Some W_798d0.
Proof. vm_refl. Qed.
Lemma D_798d0 : decode_any W_798d0 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798d4 : bv 32 := 0x01c683a3.
Lemma F_798d4 : fetch_word Ubsan.M.loaded_segments (0x798d4 : word) = Some W_798d4.
Proof. vm_refl. Qed.
Lemma D_798d4 : decode_any W_798d4 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798d8 : bv 32 := 0x00070693.
Lemma F_798d8 : fetch_word Ubsan.M.loaded_segments (0x798d8 : word) = Some W_798d8.
Proof. vm_refl. Qed.
Lemma D_798d8 : decode_any W_798d8 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798dc : bv 32 := 0x00467713.
Lemma F_798dc : fetch_word Ubsan.M.loaded_segments (0x798dc : word) = Some W_798dc.
Proof. vm_refl. Qed.
Lemma D_798dc : decode_any W_798dc = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798e0 : bv 32 := 0x02070863.
Lemma F_798e0 : fetch_word Ubsan.M.loaded_segments (0x798e0 : word) = Some W_798e0.
Proof. vm_refl. Qed.
Lemma D_798e0 : decode_any W_798e0 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798e4 : bv 32 := 0x0005c703.
Lemma F_798e4 : fetch_word Ubsan.M.loaded_segments (0x798e4 : word) = Some W_798e4.
Proof. vm_refl. Qed.
Lemma D_798e4 : decode_any W_798e4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798e8 : bv 32 := 0x0015c783.
Lemma F_798e8 : fetch_word Ubsan.M.loaded_segments (0x798e8 : word) = Some W_798e8.
Proof. vm_refl. Qed.
Lemma D_798e8 : decode_any W_798e8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798ec : bv 32 := 0x0025c803.
Lemma F_798ec : fetch_word Ubsan.M.loaded_segments (0x798ec : word) = Some W_798ec.
Proof. vm_refl. Qed.
Lemma D_798ec : decode_any W_798ec = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798f0 : bv 32 := 0x0035c883.
Lemma F_798f0 : fetch_word Ubsan.M.loaded_segments (0x798f0 : word) = Some W_798f0.
Proof. vm_refl. Qed.
Lemma D_798f0 : decode_any W_798f0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798f4 : bv 32 := 0x00458593.
Lemma F_798f4 : fetch_word Ubsan.M.loaded_segments (0x798f4 : word) = Some W_798f4.
Proof. vm_refl. Qed.
Lemma D_798f4 : decode_any W_798f4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798f8 : bv 32 := 0x00468293.
Lemma F_798f8 : fetch_word Ubsan.M.loaded_segments (0x798f8 : word) = Some W_798f8.
Proof. vm_refl. Qed.
Lemma D_798f8 : decode_any W_798f8 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_798fc : bv 32 := 0x00e68023.
Lemma F_798fc : fetch_word Ubsan.M.loaded_segments (0x798fc : word) = Some W_798fc.
Proof. vm_refl. Qed.
Lemma D_798fc : decode_any W_798fc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79900 : bv 32 := 0x00f680a3.
Lemma F_79900 : fetch_word Ubsan.M.loaded_segments (0x79900 : word) = Some W_79900.
Proof. vm_refl. Qed.
Lemma D_79900 : decode_any W_79900 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79904 : bv 32 := 0x01068123.
Lemma F_79904 : fetch_word Ubsan.M.loaded_segments (0x79904 : word) = Some W_79904.
Proof. vm_refl. Qed.
Lemma D_79904 : decode_any W_79904 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79908 : bv 32 := 0x011681a3.
Lemma F_79908 : fetch_word Ubsan.M.loaded_segments (0x79908 : word) = Some W_79908.
Proof. vm_refl. Qed.
Lemma D_79908 : decode_any W_79908 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7990c : bv 32 := 0x00028693.
Lemma F_7990c : fetch_word Ubsan.M.loaded_segments (0x7990c : word) = Some W_7990c.
Proof. vm_refl. Qed.
Lemma D_7990c : decode_any W_7990c = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79910 : bv 32 := 0x00267713.
Lemma F_79910 : fetch_word Ubsan.M.loaded_segments (0x79910 : word) = Some W_79910.
Proof. vm_refl. Qed.
Lemma D_79910 : decode_any W_79910 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79914 : bv 32 := 0x00071863.
Lemma F_79914 : fetch_word Ubsan.M.loaded_segments (0x79914 : word) = Some W_79914.
Proof. vm_refl. Qed.
Lemma D_79914 : decode_any W_79914 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79918 : bv 32 := 0x00167613.
Lemma F_79918 : fetch_word Ubsan.M.loaded_segments (0x79918 : word) = Some W_79918.
Proof. vm_refl. Qed.
Lemma D_79918 : decode_any W_79918 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7991c : bv 32 := 0x02061663.
Lemma F_7991c : fetch_word Ubsan.M.loaded_segments (0x7991c : word) = Some W_7991c.
Proof. vm_refl. Qed.
Lemma D_7991c : decode_any W_7991c = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79920 : bv 32 := 0x00008067.
Lemma F_79920 : fetch_word Ubsan.M.loaded_segments (0x79920 : word) = Some W_79920.
Proof. vm_refl. Qed.
Lemma D_79920 : decode_any W_79920 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79924 : bv 32 := 0x0005c703.
Lemma F_79924 : fetch_word Ubsan.M.loaded_segments (0x79924 : word) = Some W_79924.
Proof. vm_refl. Qed.
Lemma D_79924 : decode_any W_79924 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79928 : bv 32 := 0x0015c783.
Lemma F_79928 : fetch_word Ubsan.M.loaded_segments (0x79928 : word) = Some W_79928.
Proof. vm_refl. Qed.
Lemma D_79928 : decode_any W_79928 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7992c : bv 32 := 0x00258593.
Lemma F_7992c : fetch_word Ubsan.M.loaded_segments (0x7992c : word) = Some W_7992c.
Proof. vm_refl. Qed.
Lemma D_7992c : decode_any W_7992c = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79930 : bv 32 := 0x00268813.
Lemma F_79930 : fetch_word Ubsan.M.loaded_segments (0x79930 : word) = Some W_79930.
Proof. vm_refl. Qed.
Lemma D_79930 : decode_any W_79930 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79934 : bv 32 := 0x00e68023.
Lemma F_79934 : fetch_word Ubsan.M.loaded_segments (0x79934 : word) = Some W_79934.
Proof. vm_refl. Qed.
Lemma D_79934 : decode_any W_79934 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79938 : bv 32 := 0x00f680a3.
Lemma F_79938 : fetch_word Ubsan.M.loaded_segments (0x79938 : word) = Some W_79938.
Proof. vm_refl. Qed.
Lemma D_79938 : decode_any W_79938 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7993c : bv 32 := 0x00080693.
Lemma F_7993c : fetch_word Ubsan.M.loaded_segments (0x7993c : word) = Some W_7993c.
Proof. vm_refl. Qed.
Lemma D_7993c : decode_any W_7993c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79940 : bv 32 := 0x00167613.
Lemma F_79940 : fetch_word Ubsan.M.loaded_segments (0x79940 : word) = Some W_79940.
Proof. vm_refl. Qed.
Lemma D_79940 : decode_any W_79940 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79944 : bv 32 := 0xfc060ee3.
Lemma F_79944 : fetch_word Ubsan.M.loaded_segments (0x79944 : word) = Some W_79944.
Proof. vm_refl. Qed.
Lemma D_79944 : decode_any W_79944 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79948 : bv 32 := 0x0005c583.
Lemma F_79948 : fetch_word Ubsan.M.loaded_segments (0x79948 : word) = Some W_79948.
Proof. vm_refl. Qed.
Lemma D_79948 : decode_any W_79948 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7994c : bv 32 := 0x00b68023.
Lemma F_7994c : fetch_word Ubsan.M.loaded_segments (0x7994c : word) = Some W_7994c.
Proof. vm_refl. Qed.
Lemma D_7994c : decode_any W_7994c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79950 : bv 32 := 0x00008067.
Lemma F_79950 : fetch_word Ubsan.M.loaded_segments (0x79950 : word) = Some W_79950.
Proof. vm_refl. Qed.
Lemma D_79950 : decode_any W_79950 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79954 : bv 32 := 0x08b50663.
Lemma F_79954 : fetch_word Ubsan.M.loaded_segments (0x79954 : word) = Some W_79954.
Proof. vm_refl. Qed.
Lemma D_79954 : decode_any W_79954 = Some (Branch BC_EQ 10 11 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79958 : bv 32 := 0x00a606b3.
Lemma F_79958 : fetch_word Ubsan.M.loaded_segments (0x79958 : word) = Some W_79958.
Proof. vm_refl. Qed.
Lemma D_79958 : decode_any W_79958 = Some (Op ALU_ADD 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7995c : bv 32 := 0x00161713.
Lemma F_7995c : fetch_word Ubsan.M.loaded_segments (0x7995c : word) = Some W_7995c.
Proof. vm_refl. Qed.
Lemma D_7995c : decode_any W_7995c = Some (ShiftImm ALU_SLL 14 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79960 : bv 32 := 0x40d586b3.
Lemma F_79960 : fetch_word Ubsan.M.loaded_segments (0x79960 : word) = Some W_79960.
Proof. vm_refl. Qed.
Lemma D_79960 : decode_any W_79960 = Some (Op ALU_SUB 13 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79964 : bv 32 := 0x40e00733.
Lemma F_79964 : fetch_word Ubsan.M.loaded_segments (0x79964 : word) = Some W_79964.
Proof. vm_refl. Qed.
Lemma D_79964 : decode_any W_79964 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79968 : bv 32 := 0x04d77063.
Lemma F_79968 : fetch_word Ubsan.M.loaded_segments (0x79968 : word) = Some W_79968.
Proof. vm_refl. Qed.
Lemma D_79968 : decode_any W_79968 = Some (Branch BC_GEU 14 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7996c : bv 32 := 0x00a5c6b3.
Lemma F_7996c : fetch_word Ubsan.M.loaded_segments (0x7996c : word) = Some W_7996c.
Proof. vm_refl. Qed.
Lemma D_7996c : decode_any W_7996c = Some (Op ALU_XOR 13 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79970 : bv 32 := 0x0076f693.
Lemma F_79970 : fetch_word Ubsan.M.loaded_segments (0x79970 : word) = Some W_79970.
Proof. vm_refl. Qed.
Lemma D_79970 : decode_any W_79970 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79974 : bv 32 := 0x02b57c63.
Lemma F_79974 : fetch_word Ubsan.M.loaded_segments (0x79974 : word) = Some W_79974.
Proof. vm_refl. Qed.
Lemma D_79974 : decode_any W_79974 = Some (Branch BC_GEU 10 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79978 : bv 32 := 0x06068663.
Lemma F_79978 : fetch_word Ubsan.M.loaded_segments (0x79978 : word) = Some W_79978.
Proof. vm_refl. Qed.
Lemma D_79978 : decode_any W_79978 = Some (Branch BC_EQ 13 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7997c : bv 32 := 0x00050693.
Lemma F_7997c : fetch_word Ubsan.M.loaded_segments (0x7997c : word) = Some W_7997c.
Proof. vm_refl. Qed.
Lemma D_7997c : decode_any W_7997c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79980 : bv 32 := 0x00058713.
Lemma F_79980 : fetch_word Ubsan.M.loaded_segments (0x79980 : word) = Some W_79980.
Proof. vm_refl. Qed.
Lemma D_79980 : decode_any W_79980 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79984 : bv 32 := 0x04060e63.
Lemma F_79984 : fetch_word Ubsan.M.loaded_segments (0x79984 : word) = Some W_79984.
Proof. vm_refl. Qed.
Lemma D_79984 : decode_any W_79984 = Some (Branch BC_EQ 12 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79988 : bv 32 := 0x00c68633.
Lemma F_79988 : fetch_word Ubsan.M.loaded_segments (0x79988 : word) = Some W_79988.
Proof. vm_refl. Qed.
Lemma D_79988 : decode_any W_79988 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7998c : bv 32 := 0x00074583.
Lemma F_7998c : fetch_word Ubsan.M.loaded_segments (0x7998c : word) = Some W_7998c.
Proof. vm_refl. Qed.
Lemma D_7998c : decode_any W_7998c = Some (Load SZ1 false 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79990 : bv 32 := 0x00170713.
Lemma F_79990 : fetch_word Ubsan.M.loaded_segments (0x79990 : word) = Some W_79990.
Proof. vm_refl. Qed.
Lemma D_79990 : decode_any W_79990 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79994 : bv 32 := 0x00168793.
Lemma F_79994 : fetch_word Ubsan.M.loaded_segments (0x79994 : word) = Some W_79994.
Proof. vm_refl. Qed.
Lemma D_79994 : decode_any W_79994 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79998 : bv 32 := 0x00b68023.
Lemma F_79998 : fetch_word Ubsan.M.loaded_segments (0x79998 : word) = Some W_79998.
Proof. vm_refl. Qed.
Lemma D_79998 : decode_any W_79998 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7999c : bv 32 := 0x00078693.
Lemma F_7999c : fetch_word Ubsan.M.loaded_segments (0x7999c : word) = Some W_7999c.
Proof. vm_refl. Qed.
Lemma D_7999c : decode_any W_7999c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799a0 : bv 32 := 0xfec796e3.
Lemma F_799a0 : fetch_word Ubsan.M.loaded_segments (0x799a0 : word) = Some W_799a0.
Proof. vm_refl. Qed.
Lemma D_799a0 : decode_any W_799a0 = Some (Branch BC_NE 15 12 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799a4 : bv 32 := 0x03c0006f.
Lemma F_799a4 : fetch_word Ubsan.M.loaded_segments (0x799a4 : word) = Some W_799a4.
Proof. vm_refl. Qed.
Lemma D_799a4 : decode_any W_799a4 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799a8 : bv 32 := 0xba9ff06f.
Lemma F_799a8 : fetch_word Ubsan.M.loaded_segments (0x799a8 : word) = Some W_799a8.
Proof. vm_refl. Qed.
Lemma D_799a8 : decode_any W_799a8 = Some (Jal 0 2096040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799ac : bv 32 := 0x06068c63.
Lemma F_799ac : fetch_word Ubsan.M.loaded_segments (0x799ac : word) = Some W_799ac.
Proof. vm_refl. Qed.
Lemma D_799ac : decode_any W_799ac = Some (Branch BC_EQ 13 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799b0 : bv 32 := 0x00060693.
Lemma F_799b0 : fetch_word Ubsan.M.loaded_segments (0x799b0 : word) = Some W_799b0.
Proof. vm_refl. Qed.
Lemma D_799b0 : decode_any W_799b0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799b4 : bv 32 := 0x02068663.
Lemma F_799b4 : fetch_word Ubsan.M.loaded_segments (0x799b4 : word) = Some W_799b4.
Proof. vm_refl. Qed.
Lemma D_799b4 : decode_any W_799b4 = Some (Branch BC_EQ 13 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799b8 : bv 32 := 0x40d00633.
Lemma F_799b8 : fetch_word Ubsan.M.loaded_segments (0x799b8 : word) = Some W_799b8.
Proof. vm_refl. Qed.
Lemma D_799b8 : decode_any W_799b8 = Some (Op ALU_SUB 12 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799bc : bv 32 := 0xfff68713.
Lemma F_799bc : fetch_word Ubsan.M.loaded_segments (0x799bc : word) = Some W_799bc.
Proof. vm_refl. Qed.
Lemma D_799bc : decode_any W_799bc = Some (OpImm ALU_ADD 14 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799c0 : bv 32 := 0x00e506b3.
Lemma F_799c0 : fetch_word Ubsan.M.loaded_segments (0x799c0 : word) = Some W_799c0.
Proof. vm_refl. Qed.
Lemma D_799c0 : decode_any W_799c0 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799c4 : bv 32 := 0x00e585b3.
Lemma F_799c4 : fetch_word Ubsan.M.loaded_segments (0x799c4 : word) = Some W_799c4.
Proof. vm_refl. Qed.
Lemma D_799c4 : decode_any W_799c4 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799c8 : bv 32 := 0x0005c703.
Lemma F_799c8 : fetch_word Ubsan.M.loaded_segments (0x799c8 : word) = Some W_799c8.
Proof. vm_refl. Qed.
Lemma D_799c8 : decode_any W_799c8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799cc : bv 32 := 0x00160613.
Lemma F_799cc : fetch_word Ubsan.M.loaded_segments (0x799cc : word) = Some W_799cc.
Proof. vm_refl. Qed.
Lemma D_799cc : decode_any W_799cc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799d0 : bv 32 := 0x00e68023.
Lemma F_799d0 : fetch_word Ubsan.M.loaded_segments (0x799d0 : word) = Some W_799d0.
Proof. vm_refl. Qed.
Lemma D_799d0 : decode_any W_799d0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799d4 : bv 32 := 0xfff68693.
Lemma F_799d4 : fetch_word Ubsan.M.loaded_segments (0x799d4 : word) = Some W_799d4.
Proof. vm_refl. Qed.
Lemma D_799d4 : decode_any W_799d4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799d8 : bv 32 := 0xfff58593.
Lemma F_799d8 : fetch_word Ubsan.M.loaded_segments (0x799d8 : word) = Some W_799d8.
Proof. vm_refl. Qed.
Lemma D_799d8 : decode_any W_799d8 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799dc : bv 32 := 0xfe0616e3.
Lemma F_799dc : fetch_word Ubsan.M.loaded_segments (0x799dc : word) = Some W_799dc.
Proof. vm_refl. Qed.
Lemma D_799dc : decode_any W_799dc = Some (Branch BC_NE 12 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799e0 : bv 32 := 0x00008067.
Lemma F_799e0 : fetch_word Ubsan.M.loaded_segments (0x799e0 : word) = Some W_799e0.
Proof. vm_refl. Qed.
Lemma D_799e0 : decode_any W_799e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799e4 : bv 32 := 0x00757693.
Lemma F_799e4 : fetch_word Ubsan.M.loaded_segments (0x799e4 : word) = Some W_799e4.
Proof. vm_refl. Qed.
Lemma D_799e4 : decode_any W_799e4 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799e8 : bv 32 := 0x0a068c63.
Lemma F_799e8 : fetch_word Ubsan.M.loaded_segments (0x799e8 : word) = Some W_799e8.
Proof. vm_refl. Qed.
Lemma D_799e8 : decode_any W_799e8 = Some (Branch BC_EQ 13 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799ec : bv 32 := 0x00150793.
Lemma F_799ec : fetch_word Ubsan.M.loaded_segments (0x799ec : word) = Some W_799ec.
Proof. vm_refl. Qed.
Lemma D_799ec : decode_any W_799ec = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799f0 : bv 32 := 0x00050813.
Lemma F_799f0 : fetch_word Ubsan.M.loaded_segments (0x799f0 : word) = Some W_799f0.
Proof. vm_refl. Qed.
Lemma D_799f0 : decode_any W_799f0 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799f4 : bv 32 := 0xfe0606e3.
Lemma F_799f4 : fetch_word Ubsan.M.loaded_segments (0x799f4 : word) = Some W_799f4.
Proof. vm_refl. Qed.
Lemma D_799f4 : decode_any W_799f4 = Some (Branch BC_EQ 12 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799f8 : bv 32 := 0xfff60613.
Lemma F_799f8 : fetch_word Ubsan.M.loaded_segments (0x799f8 : word) = Some W_799f8.
Proof. vm_refl. Qed.
Lemma D_799f8 : decode_any W_799f8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799fc : bv 32 := 0x0005c883.
Lemma F_799fc : fetch_word Ubsan.M.loaded_segments (0x799fc : word) = Some W_799fc.
Proof. vm_refl. Qed.
Lemma D_799fc : decode_any W_799fc = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a00 : bv 32 := 0x00158713.
Lemma F_79a00 : fetch_word Ubsan.M.loaded_segments (0x79a00 : word) = Some W_79a00.
Proof. vm_refl. Qed.
Lemma D_79a00 : decode_any W_79a00 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a04 : bv 32 := 0x00180693.
Lemma F_79a04 : fetch_word Ubsan.M.loaded_segments (0x79a04 : word) = Some W_79a04.
Proof. vm_refl. Qed.
Lemma D_79a04 : decode_any W_79a04 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a08 : bv 32 := 0x0077f293.
Lemma F_79a08 : fetch_word Ubsan.M.loaded_segments (0x79a08 : word) = Some W_79a08.
Proof. vm_refl. Qed.
Lemma D_79a08 : decode_any W_79a08 = Some (OpImm ALU_AND 5 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a0c : bv 32 := 0x01180023.
Lemma F_79a0c : fetch_word Ubsan.M.loaded_segments (0x79a0c : word) = Some W_79a0c.
Proof. vm_refl. Qed.
Lemma D_79a0c : decode_any W_79a0c = Some (Store SZ1 16 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a10 : bv 32 := 0x00178793.
Lemma F_79a10 : fetch_word Ubsan.M.loaded_segments (0x79a10 : word) = Some W_79a10.
Proof. vm_refl. Qed.
Lemma D_79a10 : decode_any W_79a10 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a14 : bv 32 := 0x00070593.
Lemma F_79a14 : fetch_word Ubsan.M.loaded_segments (0x79a14 : word) = Some W_79a14.
Proof. vm_refl. Qed.
Lemma D_79a14 : decode_any W_79a14 = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a18 : bv 32 := 0x00068813.
Lemma F_79a18 : fetch_word Ubsan.M.loaded_segments (0x79a18 : word) = Some W_79a18.
Proof. vm_refl. Qed.
Lemma D_79a18 : decode_any W_79a18 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a1c : bv 32 := 0xfc029ce3.
Lemma F_79a1c : fetch_word Ubsan.M.loaded_segments (0x79a1c : word) = Some W_79a1c.
Proof. vm_refl. Qed.
Lemma D_79a1c : decode_any W_79a1c = Some (Branch BC_NE 5 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a20 : bv 32 := 0x0880006f.
Lemma F_79a20 : fetch_word Ubsan.M.loaded_segments (0x79a20 : word) = Some W_79a20.
Proof. vm_refl. Qed.
Lemma D_79a20 : decode_any W_79a20 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a24 : bv 32 := 0x00c506b3.
Lemma F_79a24 : fetch_word Ubsan.M.loaded_segments (0x79a24 : word) = Some W_79a24.
Proof. vm_refl. Qed.
Lemma D_79a24 : decode_any W_79a24 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a28 : bv 32 := 0x0076f693.
Lemma F_79a28 : fetch_word Ubsan.M.loaded_segments (0x79a28 : word) = Some W_79a28.
Proof. vm_refl. Qed.
Lemma D_79a28 : decode_any W_79a28 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a2c : bv 32 := 0x04068063.
Lemma F_79a2c : fetch_word Ubsan.M.loaded_segments (0x79a2c : word) = Some W_79a2c.
Proof. vm_refl. Qed.
Lemma D_79a2c : decode_any W_79a2c = Some (Branch BC_EQ 13 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a30 : bv 32 := 0x40c006b3.
Lemma F_79a30 : fetch_word Ubsan.M.loaded_segments (0x79a30 : word) = Some W_79a30.
Proof. vm_refl. Qed.
Lemma D_79a30 : decode_any W_79a30 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a34 : bv 32 := 0xfff60713.
Lemma F_79a34 : fetch_word Ubsan.M.loaded_segments (0x79a34 : word) = Some W_79a34.
Proof. vm_refl. Qed.
Lemma D_79a34 : decode_any W_79a34 = Some (OpImm ALU_ADD 14 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a38 : bv 32 := 0x00e50633.
Lemma F_79a38 : fetch_word Ubsan.M.loaded_segments (0x79a38 : word) = Some W_79a38.
Proof. vm_refl. Qed.
Lemma D_79a38 : decode_any W_79a38 = Some (Op ALU_ADD 12 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a3c : bv 32 := 0x00e58733.
Lemma F_79a3c : fetch_word Ubsan.M.loaded_segments (0x79a3c : word) = Some W_79a3c.
Proof. vm_refl. Qed.
Lemma D_79a3c : decode_any W_79a3c = Some (Op ALU_ADD 14 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a40 : bv 32 := 0x00060793.
Lemma F_79a40 : fetch_word Ubsan.M.loaded_segments (0x79a40 : word) = Some W_79a40.
Proof. vm_refl. Qed.
Lemma D_79a40 : decode_any W_79a40 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a44 : bv 32 := 0xf8068ee3.
Lemma F_79a44 : fetch_word Ubsan.M.loaded_segments (0x79a44 : word) = Some W_79a44.
Proof. vm_refl. Qed.
Lemma D_79a44 : decode_any W_79a44 = Some (Branch BC_EQ 13 0 8092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a48 : bv 32 := 0x00074803.
Lemma F_79a48 : fetch_word Ubsan.M.loaded_segments (0x79a48 : word) = Some W_79a48.
Proof. vm_refl. Qed.
Lemma D_79a48 : decode_any W_79a48 = Some (Load SZ1 false 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a4c : bv 32 := 0x01060023.
Lemma F_79a4c : fetch_word Ubsan.M.loaded_segments (0x79a4c : word) = Some W_79a4c.
Proof. vm_refl. Qed.
Lemma D_79a4c : decode_any W_79a4c = Some (Store SZ1 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a50 : bv 32 := 0x0077f813.
Lemma F_79a50 : fetch_word Ubsan.M.loaded_segments (0x79a50 : word) = Some W_79a50.
Proof. vm_refl. Qed.
Lemma D_79a50 : decode_any W_79a50 = Some (OpImm ALU_AND 16 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a54 : bv 32 := 0x00168693.
Lemma F_79a54 : fetch_word Ubsan.M.loaded_segments (0x79a54 : word) = Some W_79a54.
Proof. vm_refl. Qed.
Lemma D_79a54 : decode_any W_79a54 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a58 : bv 32 := 0xfff78793.
Lemma F_79a58 : fetch_word Ubsan.M.loaded_segments (0x79a58 : word) = Some W_79a58.
Proof. vm_refl. Qed.
Lemma D_79a58 : decode_any W_79a58 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a5c : bv 32 := 0xfff60613.
Lemma F_79a5c : fetch_word Ubsan.M.loaded_segments (0x79a5c : word) = Some W_79a5c.
Proof. vm_refl. Qed.
Lemma D_79a5c : decode_any W_79a5c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a60 : bv 32 := 0xfff70713.
Lemma F_79a60 : fetch_word Ubsan.M.loaded_segments (0x79a60 : word) = Some W_79a60.
Proof. vm_refl. Qed.
Lemma D_79a60 : decode_any W_79a60 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a64 : bv 32 := 0xfe0810e3.
Lemma F_79a64 : fetch_word Ubsan.M.loaded_segments (0x79a64 : word) = Some W_79a64.
Proof. vm_refl. Qed.
Lemma D_79a64 : decode_any W_79a64 = Some (Branch BC_NE 16 0 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a68 : bv 32 := 0x40d00633.
Lemma F_79a68 : fetch_word Ubsan.M.loaded_segments (0x79a68 : word) = Some W_79a68.
Proof. vm_refl. Qed.
Lemma D_79a68 : decode_any W_79a68 = Some (Op ALU_SUB 12 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a6c : bv 32 := 0x00800693.
Lemma F_79a6c : fetch_word Ubsan.M.loaded_segments (0x79a6c : word) = Some W_79a6c.
Proof. vm_refl. Qed.
Lemma D_79a6c : decode_any W_79a6c = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a70 : bv 32 := 0xf4d660e3.
Lemma F_79a70 : fetch_word Ubsan.M.loaded_segments (0x79a70 : word) = Some W_79a70.
Proof. vm_refl. Qed.
Lemma D_79a70 : decode_any W_79a70 = Some (Branch BC_LTU 12 13 8000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a74 : bv 32 := 0xff858713.
Lemma F_79a74 : fetch_word Ubsan.M.loaded_segments (0x79a74 : word) = Some W_79a74.
Proof. vm_refl. Qed.
Lemma D_79a74 : decode_any W_79a74 = Some (OpImm ALU_ADD 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a78 : bv 32 := 0xff850793.
Lemma F_79a78 : fetch_word Ubsan.M.loaded_segments (0x79a78 : word) = Some W_79a78.
Proof. vm_refl. Qed.
Lemma D_79a78 : decode_any W_79a78 = Some (OpImm ALU_ADD 15 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a7c : bv 32 := 0x00700813.
Lemma F_79a7c : fetch_word Ubsan.M.loaded_segments (0x79a7c : word) = Some W_79a7c.
Proof. vm_refl. Qed.
Lemma D_79a7c : decode_any W_79a7c = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a80 : bv 32 := 0x00c706b3.
Lemma F_79a80 : fetch_word Ubsan.M.loaded_segments (0x79a80 : word) = Some W_79a80.
Proof. vm_refl. Qed.
Lemma D_79a80 : decode_any W_79a80 = Some (Op ALU_ADD 13 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a84 : bv 32 := 0x0006b883.
Lemma F_79a84 : fetch_word Ubsan.M.loaded_segments (0x79a84 : word) = Some W_79a84.
Proof. vm_refl. Qed.
Lemma D_79a84 : decode_any W_79a84 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a88 : bv 32 := 0xff860693.
Lemma F_79a88 : fetch_word Ubsan.M.loaded_segments (0x79a88 : word) = Some W_79a88.
Proof. vm_refl. Qed.
Lemma D_79a88 : decode_any W_79a88 = Some (OpImm ALU_ADD 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a8c : bv 32 := 0x00c78633.
Lemma F_79a8c : fetch_word Ubsan.M.loaded_segments (0x79a8c : word) = Some W_79a8c.
Proof. vm_refl. Qed.
Lemma D_79a8c : decode_any W_79a8c = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a90 : bv 32 := 0x01163023.
Lemma F_79a90 : fetch_word Ubsan.M.loaded_segments (0x79a90 : word) = Some W_79a90.
Proof. vm_refl. Qed.
Lemma D_79a90 : decode_any W_79a90 = Some (Store SZ8 12 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a94 : bv 32 := 0x00068613.
Lemma F_79a94 : fetch_word Ubsan.M.loaded_segments (0x79a94 : word) = Some W_79a94.
Proof. vm_refl. Qed.
Lemma D_79a94 : decode_any W_79a94 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a98 : bv 32 := 0xfed864e3.
Lemma F_79a98 : fetch_word Ubsan.M.loaded_segments (0x79a98 : word) = Some W_79a98.
Proof. vm_refl. Qed.
Lemma D_79a98 : decode_any W_79a98 = Some (Branch BC_LTU 16 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a9c : bv 32 := 0xf19ff06f.
Lemma F_79a9c : fetch_word Ubsan.M.loaded_segments (0x79a9c : word) = Some W_79a9c.
Proof. vm_refl. Qed.
Lemma D_79a9c : decode_any W_79a9c = Some (Jal 0 2096920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aa0 : bv 32 := 0x00050693.
Lemma F_79aa0 : fetch_word Ubsan.M.loaded_segments (0x79aa0 : word) = Some W_79aa0.
Proof. vm_refl. Qed.
Lemma D_79aa0 : decode_any W_79aa0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aa4 : bv 32 := 0x00058713.
Lemma F_79aa4 : fetch_word Ubsan.M.loaded_segments (0x79aa4 : word) = Some W_79aa4.
Proof. vm_refl. Qed.
Lemma D_79aa4 : decode_any W_79aa4 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aa8 : bv 32 := 0x00800593.
Lemma F_79aa8 : fetch_word Ubsan.M.loaded_segments (0x79aa8 : word) = Some W_79aa8.
Proof. vm_refl. Qed.
Lemma D_79aa8 : decode_any W_79aa8 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aac : bv 32 := 0xecb66ce3.
Lemma F_79aac : fetch_word Ubsan.M.loaded_segments (0x79aac : word) = Some W_79aac.
Proof. vm_refl. Qed.
Lemma D_79aac : decode_any W_79aac = Some (Branch BC_LTU 12 11 7896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ab0 : bv 32 := 0x00700593.
Lemma F_79ab0 : fetch_word Ubsan.M.loaded_segments (0x79ab0 : word) = Some W_79ab0.
Proof. vm_refl. Qed.
Lemma D_79ab0 : decode_any W_79ab0 = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ab4 : bv 32 := 0x00073783.
Lemma F_79ab4 : fetch_word Ubsan.M.loaded_segments (0x79ab4 : word) = Some W_79ab4.
Proof. vm_refl. Qed.
Lemma D_79ab4 : decode_any W_79ab4 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ab8 : bv 32 := 0xff860613.
Lemma F_79ab8 : fetch_word Ubsan.M.loaded_segments (0x79ab8 : word) = Some W_79ab8.
Proof. vm_refl. Qed.
Lemma D_79ab8 : decode_any W_79ab8 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79abc : bv 32 := 0x00f6b023.
Lemma F_79abc : fetch_word Ubsan.M.loaded_segments (0x79abc : word) = Some W_79abc.
Proof. vm_refl. Qed.
Lemma D_79abc : decode_any W_79abc = Some (Store SZ8 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ac0 : bv 32 := 0x00868693.
Lemma F_79ac0 : fetch_word Ubsan.M.loaded_segments (0x79ac0 : word) = Some W_79ac0.
Proof. vm_refl. Qed.
Lemma D_79ac0 : decode_any W_79ac0 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ac4 : bv 32 := 0x00870713.
Lemma F_79ac4 : fetch_word Ubsan.M.loaded_segments (0x79ac4 : word) = Some W_79ac4.
Proof. vm_refl. Qed.
Lemma D_79ac4 : decode_any W_79ac4 = Some (OpImm ALU_ADD 14 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ac8 : bv 32 := 0xfec5e6e3.
Lemma F_79ac8 : fetch_word Ubsan.M.loaded_segments (0x79ac8 : word) = Some W_79ac8.
Proof. vm_refl. Qed.
Lemma D_79ac8 : decode_any W_79ac8 = Some (Branch BC_LTU 11 12 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79acc : bv 32 := 0xeb9ff06f.
Lemma F_79acc : fetch_word Ubsan.M.loaded_segments (0x79acc : word) = Some W_79acc.
Proof. vm_refl. Qed.
Lemma D_79acc : decode_any W_79acc = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ad0 : bv 32 := 0x0e060a63.
Lemma F_79ad0 : fetch_word Ubsan.M.loaded_segments (0x79ad0 : word) = Some W_79ad0.
Proof. vm_refl. Qed.
Lemma D_79ad0 : decode_any W_79ad0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ad4 : bv 32 := 0x00b50023.
Lemma F_79ad4 : fetch_word Ubsan.M.loaded_segments (0x79ad4 : word) = Some W_79ad4.
Proof. vm_refl. Qed.
Lemma D_79ad4 : decode_any W_79ad4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ad8 : bv 32 := 0x00c506b3.
Lemma F_79ad8 : fetch_word Ubsan.M.loaded_segments (0x79ad8 : word) = Some W_79ad8.
Proof. vm_refl. Qed.
Lemma D_79ad8 : decode_any W_79ad8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79adc : bv 32 := 0x00300713.
Lemma F_79adc : fetch_word Ubsan.M.loaded_segments (0x79adc : word) = Some W_79adc.
Proof. vm_refl. Qed.
Lemma D_79adc : decode_any W_79adc = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ae0 : bv 32 := 0xfeb68fa3.
Lemma F_79ae0 : fetch_word Ubsan.M.loaded_segments (0x79ae0 : word) = Some W_79ae0.
Proof. vm_refl. Qed.
Lemma D_79ae0 : decode_any W_79ae0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ae4 : bv 32 := 0x0ee66063.
Lemma F_79ae4 : fetch_word Ubsan.M.loaded_segments (0x79ae4 : word) = Some W_79ae4.
Proof. vm_refl. Qed.
Lemma D_79ae4 : decode_any W_79ae4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ae8 : bv 32 := 0x00b500a3.
Lemma F_79ae8 : fetch_word Ubsan.M.loaded_segments (0x79ae8 : word) = Some W_79ae8.
Proof. vm_refl. Qed.
Lemma D_79ae8 : decode_any W_79ae8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aec : bv 32 := 0x00b50123.
Lemma F_79aec : fetch_word Ubsan.M.loaded_segments (0x79aec : word) = Some W_79aec.
Proof. vm_refl. Qed.
Lemma D_79aec : decode_any W_79aec = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79af0 : bv 32 := 0x00700713.
Lemma F_79af0 : fetch_word Ubsan.M.loaded_segments (0x79af0 : word) = Some W_79af0.
Proof. vm_refl. Qed.
Lemma D_79af0 : decode_any W_79af0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79af4 : bv 32 := 0xfeb68ea3.
Lemma F_79af4 : fetch_word Ubsan.M.loaded_segments (0x79af4 : word) = Some W_79af4.
Proof. vm_refl. Qed.
Lemma D_79af4 : decode_any W_79af4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79af8 : bv 32 := 0xfeb68f23.
Lemma F_79af8 : fetch_word Ubsan.M.loaded_segments (0x79af8 : word) = Some W_79af8.
Proof. vm_refl. Qed.
Lemma D_79af8 : decode_any W_79af8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79afc : bv 32 := 0x0ce66463.
Lemma F_79afc : fetch_word Ubsan.M.loaded_segments (0x79afc : word) = Some W_79afc.
Proof. vm_refl. Qed.
Lemma D_79afc : decode_any W_79afc = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b00 : bv 32 := 0x00b501a3.
Lemma F_79b00 : fetch_word Ubsan.M.loaded_segments (0x79b00 : word) = Some W_79b00.
Proof. vm_refl. Qed.
Lemma D_79b00 : decode_any W_79b00 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b04 : bv 32 := 0x00900793.
Lemma F_79b04 : fetch_word Ubsan.M.loaded_segments (0x79b04 : word) = Some W_79b04.
Proof. vm_refl. Qed.
Lemma D_79b04 : decode_any W_79b04 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b08 : bv 32 := 0xfeb68e23.
Lemma F_79b08 : fetch_word Ubsan.M.loaded_segments (0x79b08 : word) = Some W_79b08.
Proof. vm_refl. Qed.
Lemma D_79b08 : decode_any W_79b08 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b0c : bv 32 := 0x0af66c63.
Lemma F_79b0c : fetch_word Ubsan.M.loaded_segments (0x79b0c : word) = Some W_79b0c.
Proof. vm_refl. Qed.
Lemma D_79b0c : decode_any W_79b0c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b10 : bv 32 := 0x40a006bb.
Lemma F_79b10 : fetch_word Ubsan.M.loaded_segments (0x79b10 : word) = Some W_79b10.
Proof. vm_refl. Qed.
Lemma D_79b10 : decode_any W_79b10 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b14 : bv 32 := 0x03859813.
Lemma F_79b14 : fetch_word Ubsan.M.loaded_segments (0x79b14 : word) = Some W_79b14.
Proof. vm_refl. Qed.
Lemma D_79b14 : decode_any W_79b14 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b18 : bv 32 := 0x101015b7.
Lemma F_79b18 : fetch_word Ubsan.M.loaded_segments (0x79b18 : word) = Some W_79b18.
Proof. vm_refl. Qed.
Lemma D_79b18 : decode_any W_79b18 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b1c : bv 32 := 0x0036f693.
Lemma F_79b1c : fetch_word Ubsan.M.loaded_segments (0x79b1c : word) = Some W_79b1c.
Proof. vm_refl. Qed.
Lemma D_79b1c : decode_any W_79b1c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b20 : bv 32 := 0x00459713.
Lemma F_79b20 : fetch_word Ubsan.M.loaded_segments (0x79b20 : word) = Some W_79b20.
Proof. vm_refl. Qed.
Lemma D_79b20 : decode_any W_79b20 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b24 : bv 32 := 0x40d60633.
Lemma F_79b24 : fetch_word Ubsan.M.loaded_segments (0x79b24 : word) = Some W_79b24.
Proof. vm_refl. Qed.
Lemma D_79b24 : decode_any W_79b24 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b28 : bv 32 := 0x00d505b3.
Lemma F_79b28 : fetch_word Ubsan.M.loaded_segments (0x79b28 : word) = Some W_79b28.
Proof. vm_refl. Qed.
Lemma D_79b28 : decode_any W_79b28 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b2c : bv 32 := 0x10070693.
Lemma F_79b2c : fetch_word Ubsan.M.loaded_segments (0x79b2c : word) = Some W_79b2c.
Proof. vm_refl. Qed.
Lemma D_79b2c : decode_any W_79b2c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b30 : bv 32 := 0xffc67713.
Lemma F_79b30 : fetch_word Ubsan.M.loaded_segments (0x79b30 : word) = Some W_79b30.
Proof. vm_refl. Qed.
Lemma D_79b30 : decode_any W_79b30 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b34 : bv 32 := 0x02d83633.
Lemma F_79b34 : fetch_word Ubsan.M.loaded_segments (0x79b34 : word) = Some W_79b34.
Proof. vm_refl. Qed.
Lemma D_79b34 : decode_any W_79b34 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b38 : bv 32 := 0x00c5a023.
Lemma F_79b38 : fetch_word Ubsan.M.loaded_segments (0x79b38 : word) = Some W_79b38.
Proof. vm_refl. Qed.
Lemma D_79b38 : decode_any W_79b38 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b3c : bv 32 := 0x00e586b3.
Lemma F_79b3c : fetch_word Ubsan.M.loaded_segments (0x79b3c : word) = Some W_79b3c.
Proof. vm_refl. Qed.
Lemma D_79b3c : decode_any W_79b3c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b40 : bv 32 := 0xfec6ae23.
Lemma F_79b40 : fetch_word Ubsan.M.loaded_segments (0x79b40 : word) = Some W_79b40.
Proof. vm_refl. Qed.
Lemma D_79b40 : decode_any W_79b40 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b44 : bv 32 := 0x08f76063.
Lemma F_79b44 : fetch_word Ubsan.M.loaded_segments (0x79b44 : word) = Some W_79b44.
Proof. vm_refl. Qed.
Lemma D_79b44 : decode_any W_79b44 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b48 : bv 32 := 0x00c5a223.
Lemma F_79b48 : fetch_word Ubsan.M.loaded_segments (0x79b48 : word) = Some W_79b48.
Proof. vm_refl. Qed.
Lemma D_79b48 : decode_any W_79b48 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b4c : bv 32 := 0x00c5a423.
Lemma F_79b4c : fetch_word Ubsan.M.loaded_segments (0x79b4c : word) = Some W_79b4c.
Proof. vm_refl. Qed.
Lemma D_79b4c : decode_any W_79b4c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b50 : bv 32 := 0x01900793.
Lemma F_79b50 : fetch_word Ubsan.M.loaded_segments (0x79b50 : word) = Some W_79b50.
Proof. vm_refl. Qed.
Lemma D_79b50 : decode_any W_79b50 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b54 : bv 32 := 0xfec6aa23.
Lemma F_79b54 : fetch_word Ubsan.M.loaded_segments (0x79b54 : word) = Some W_79b54.
Proof. vm_refl. Qed.
Lemma D_79b54 : decode_any W_79b54 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b58 : bv 32 := 0xfec6ac23.
Lemma F_79b58 : fetch_word Ubsan.M.loaded_segments (0x79b58 : word) = Some W_79b58.
Proof. vm_refl. Qed.
Lemma D_79b58 : decode_any W_79b58 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b5c : bv 32 := 0x06f76463.
Lemma F_79b5c : fetch_word Ubsan.M.loaded_segments (0x79b5c : word) = Some W_79b5c.
Proof. vm_refl. Qed.
Lemma D_79b5c : decode_any W_79b5c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b60 : bv 32 := 0x00c5a623.
Lemma F_79b60 : fetch_word Ubsan.M.loaded_segments (0x79b60 : word) = Some W_79b60.
Proof. vm_refl. Qed.
Lemma D_79b60 : decode_any W_79b60 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b64 : bv 32 := 0x00c5a823.
Lemma F_79b64 : fetch_word Ubsan.M.loaded_segments (0x79b64 : word) = Some W_79b64.
Proof. vm_refl. Qed.
Lemma D_79b64 : decode_any W_79b64 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b68 : bv 32 := 0x00c5aa23.
Lemma F_79b68 : fetch_word Ubsan.M.loaded_segments (0x79b68 : word) = Some W_79b68.
Proof. vm_refl. Qed.
Lemma D_79b68 : decode_any W_79b68 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b6c : bv 32 := 0x00c5ac23.
Lemma F_79b6c : fetch_word Ubsan.M.loaded_segments (0x79b6c : word) = Some W_79b6c.
Proof. vm_refl. Qed.
Lemma D_79b6c : decode_any W_79b6c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b70 : bv 32 := 0x0045f793.
Lemma F_79b70 : fetch_word Ubsan.M.loaded_segments (0x79b70 : word) = Some W_79b70.
Proof. vm_refl. Qed.
Lemma D_79b70 : decode_any W_79b70 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b74 : bv 32 := 0x02000813.
Lemma F_79b74 : fetch_word Ubsan.M.loaded_segments (0x79b74 : word) = Some W_79b74.
Proof. vm_refl. Qed.
Lemma D_79b74 : decode_any W_79b74 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b78 : bv 32 := 0x01878793.
Lemma F_79b78 : fetch_word Ubsan.M.loaded_segments (0x79b78 : word) = Some W_79b78.
Proof. vm_refl. Qed.
Lemma D_79b78 : decode_any W_79b78 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b7c : bv 32 := 0x40f70733.
Lemma F_79b7c : fetch_word Ubsan.M.loaded_segments (0x79b7c : word) = Some W_79b7c.
Proof. vm_refl. Qed.
Lemma D_79b7c : decode_any W_79b7c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b80 : bv 32 := 0xfec6a223.
Lemma F_79b80 : fetch_word Ubsan.M.loaded_segments (0x79b80 : word) = Some W_79b80.
Proof. vm_refl. Qed.
Lemma D_79b80 : decode_any W_79b80 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b84 : bv 32 := 0xfec6a423.
Lemma F_79b84 : fetch_word Ubsan.M.loaded_segments (0x79b84 : word) = Some W_79b84.
Proof. vm_refl. Qed.
Lemma D_79b84 : decode_any W_79b84 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b88 : bv 32 := 0xfec6a623.
Lemma F_79b88 : fetch_word Ubsan.M.loaded_segments (0x79b88 : word) = Some W_79b88.
Proof. vm_refl. Qed.
Lemma D_79b88 : decode_any W_79b88 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b8c : bv 32 := 0xfec6a823.
Lemma F_79b8c : fetch_word Ubsan.M.loaded_segments (0x79b8c : word) = Some W_79b8c.
Proof. vm_refl. Qed.
Lemma D_79b8c : decode_any W_79b8c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b90 : bv 32 := 0x03076a63.
Lemma F_79b90 : fetch_word Ubsan.M.loaded_segments (0x79b90 : word) = Some W_79b90.
Proof. vm_refl. Qed.
Lemma D_79b90 : decode_any W_79b90 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b94 : bv 32 := 0x02061613.
Lemma F_79b94 : fetch_word Ubsan.M.loaded_segments (0x79b94 : word) = Some W_79b94.
Proof. vm_refl. Qed.
Lemma D_79b94 : decode_any W_79b94 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b98 : bv 32 := 0x00f585b3.
Lemma F_79b98 : fetch_word Ubsan.M.loaded_segments (0x79b98 : word) = Some W_79b98.
Proof. vm_refl. Qed.
Lemma D_79b98 : decode_any W_79b98 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b9c : bv 32 := 0x02065693.
Lemma F_79b9c : fetch_word Ubsan.M.loaded_segments (0x79b9c : word) = Some W_79b9c.
Proof. vm_refl. Qed.
Lemma D_79b9c : decode_any W_79b9c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ba0 : bv 32 := 0x00d66633.
Lemma F_79ba0 : fetch_word Ubsan.M.loaded_segments (0x79ba0 : word) = Some W_79ba0.
Proof. vm_refl. Qed.
Lemma D_79ba0 : decode_any W_79ba0 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ba4 : bv 32 := 0x01f00693.
Lemma F_79ba4 : fetch_word Ubsan.M.loaded_segments (0x79ba4 : word) = Some W_79ba4.
Proof. vm_refl. Qed.
Lemma D_79ba4 : decode_any W_79ba4 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ba8 : bv 32 := 0x00c5b023.
Lemma F_79ba8 : fetch_word Ubsan.M.loaded_segments (0x79ba8 : word) = Some W_79ba8.
Proof. vm_refl. Qed.
Lemma D_79ba8 : decode_any W_79ba8 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bac : bv 32 := 0x00c5b423.
Lemma F_79bac : fetch_word Ubsan.M.loaded_segments (0x79bac : word) = Some W_79bac.
Proof. vm_refl. Qed.
Lemma D_79bac : decode_any W_79bac = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bb0 : bv 32 := 0x00c5b823.
Lemma F_79bb0 : fetch_word Ubsan.M.loaded_segments (0x79bb0 : word) = Some W_79bb0.
Proof. vm_refl. Qed.
Lemma D_79bb0 : decode_any W_79bb0 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bb4 : bv 32 := 0x00c5bc23.
Lemma F_79bb4 : fetch_word Ubsan.M.loaded_segments (0x79bb4 : word) = Some W_79bb4.
Proof. vm_refl. Qed.
Lemma D_79bb4 : decode_any W_79bb4 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bb8 : bv 32 := 0xfe070713.
Lemma F_79bb8 : fetch_word Ubsan.M.loaded_segments (0x79bb8 : word) = Some W_79bb8.
Proof. vm_refl. Qed.
Lemma D_79bb8 : decode_any W_79bb8 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bbc : bv 32 := 0x02058593.
Lemma F_79bbc : fetch_word Ubsan.M.loaded_segments (0x79bbc : word) = Some W_79bbc.
Proof. vm_refl. Qed.
Lemma D_79bbc : decode_any W_79bbc = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bc0 : bv 32 := 0xfee6e4e3.
Lemma F_79bc0 : fetch_word Ubsan.M.loaded_segments (0x79bc0 : word) = Some W_79bc0.
Proof. vm_refl. Qed.
Lemma D_79bc0 : decode_any W_79bc0 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bc4 : bv 32 := 0x00008067.
Lemma F_79bc4 : fetch_word Ubsan.M.loaded_segments (0x79bc4 : word) = Some W_79bc4.
Proof. vm_refl. Qed.
Lemma D_79bc4 : decode_any W_79bc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bc8 : bv 32 := 0x00054603.
Lemma F_79bc8 : fetch_word Ubsan.M.loaded_segments (0x79bc8 : word) = Some W_79bc8.
Proof. vm_refl. Qed.
Lemma D_79bc8 : decode_any W_79bc8 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bcc : bv 32 := 0x0005c683.
Lemma F_79bcc : fetch_word Ubsan.M.loaded_segments (0x79bcc : word) = Some W_79bcc.
Proof. vm_refl. Qed.
Lemma D_79bcc : decode_any W_79bcc = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bd0 : bv 32 := 0x02060463.
Lemma F_79bd0 : fetch_word Ubsan.M.loaded_segments (0x79bd0 : word) = Some W_79bd0.
Proof. vm_refl. Qed.
Lemma D_79bd0 : decode_any W_79bd0 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bd4 : bv 32 := 0x02d61263.
Lemma F_79bd4 : fetch_word Ubsan.M.loaded_segments (0x79bd4 : word) = Some W_79bd4.
Proof. vm_refl. Qed.
Lemma D_79bd4 : decode_any W_79bd4 = Some (Branch BC_NE 12 13 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bd8 : bv 32 := 0x00158593.
Lemma F_79bd8 : fetch_word Ubsan.M.loaded_segments (0x79bd8 : word) = Some W_79bd8.
Proof. vm_refl. Qed.
Lemma D_79bd8 : decode_any W_79bd8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bdc : bv 32 := 0x00150513.
Lemma F_79bdc : fetch_word Ubsan.M.loaded_segments (0x79bdc : word) = Some W_79bdc.
Proof. vm_refl. Qed.
Lemma D_79bdc : decode_any W_79bdc = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79be0 : bv 32 := 0x00054603.
Lemma F_79be0 : fetch_word Ubsan.M.loaded_segments (0x79be0 : word) = Some W_79be0.
Proof. vm_refl. Qed.
Lemma D_79be0 : decode_any W_79be0 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79be4 : bv 32 := 0x0005c683.
Lemma F_79be4 : fetch_word Ubsan.M.loaded_segments (0x79be4 : word) = Some W_79be4.
Proof. vm_refl. Qed.
Lemma D_79be4 : decode_any W_79be4 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79be8 : bv 32 := 0x00060863.
Lemma F_79be8 : fetch_word Ubsan.M.loaded_segments (0x79be8 : word) = Some W_79be8.
Proof. vm_refl. Qed.
Lemma D_79be8 : decode_any W_79be8 = Some (Branch BC_EQ 12 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bec : bv 32 := 0x00158593.
Lemma F_79bec : fetch_word Ubsan.M.loaded_segments (0x79bec : word) = Some W_79bec.
Proof. vm_refl. Qed.
Lemma D_79bec : decode_any W_79bec = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bf0 : bv 32 := 0x00150513.
Lemma F_79bf0 : fetch_word Ubsan.M.loaded_segments (0x79bf0 : word) = Some W_79bf0.
Proof. vm_refl. Qed.
Lemma D_79bf0 : decode_any W_79bf0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bf4 : bv 32 := 0xfed606e3.
Lemma F_79bf4 : fetch_word Ubsan.M.loaded_segments (0x79bf4 : word) = Some W_79bf4.
Proof. vm_refl. Qed.
Lemma D_79bf4 : decode_any W_79bf4 = Some (Branch BC_EQ 12 13 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bf8 : bv 32 := 0x40d60533.
Lemma F_79bf8 : fetch_word Ubsan.M.loaded_segments (0x79bf8 : word) = Some W_79bf8.
Proof. vm_refl. Qed.
Lemma D_79bf8 : decode_any W_79bf8 = Some (Op ALU_SUB 10 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bfc : bv 32 := 0x00008067.
Lemma F_79bfc : fetch_word Ubsan.M.loaded_segments (0x79bfc : word) = Some W_79bfc.
Proof. vm_refl. Qed.
Lemma D_79bfc : decode_any W_79bfc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
