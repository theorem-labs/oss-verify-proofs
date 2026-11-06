(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2aef8 : bv 32 := 0x0ff5f593.
Lemma F_2aef8 : fetch_word Ubsan.M.loaded_segments (0x2aef8 : word) = Some W_2aef8.
Proof. vm_refl. Qed.
Lemma D_2aef8 : decode_any W_2aef8 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aefc : bv 32 := 0x00757693.
Lemma F_2aefc : fetch_word Ubsan.M.loaded_segments (0x2aefc : word) = Some W_2aefc.
Proof. vm_refl. Qed.
Lemma D_2aefc : decode_any W_2aefc = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af00 : bv 32 := 0x00c03733.
Lemma F_2af00 : fetch_word Ubsan.M.loaded_segments (0x2af00 : word) = Some W_2af00.
Proof. vm_refl. Qed.
Lemma D_2af00 : decode_any W_2af00 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af04 : bv 32 := 0x02068c63.
Lemma F_2af04 : fetch_word Ubsan.M.loaded_segments (0x2af04 : word) = Some W_2af04.
Proof. vm_refl. Qed.
Lemma D_2af04 : decode_any W_2af04 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af08 : bv 32 := 0x02060a63.
Lemma F_2af08 : fetch_word Ubsan.M.loaded_segments (0x2af08 : word) = Some W_2af08.
Proof. vm_refl. Qed.
Lemma D_2af08 : decode_any W_2af08 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af0c : bv 32 := 0x00150793.
Lemma F_2af0c : fetch_word Ubsan.M.loaded_segments (0x2af0c : word) = Some W_2af0c.
Proof. vm_refl. Qed.
Lemma D_2af0c : decode_any W_2af0c = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af10 : bv 32 := 0x00100813.
Lemma F_2af10 : fetch_word Ubsan.M.loaded_segments (0x2af10 : word) = Some W_2af10.
Proof. vm_refl. Qed.
Lemma D_2af10 : decode_any W_2af10 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af14 : bv 32 := 0x00054703.
Lemma F_2af14 : fetch_word Ubsan.M.loaded_segments (0x2af14 : word) = Some W_2af14.
Proof. vm_refl. Qed.
Lemma D_2af14 : decode_any W_2af14 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af18 : bv 32 := 0x00060693.
Lemma F_2af18 : fetch_word Ubsan.M.loaded_segments (0x2af18 : word) = Some W_2af18.
Proof. vm_refl. Qed.
Lemma D_2af18 : decode_any W_2af18 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af1c : bv 32 := 0x06b70e63.
Lemma F_2af1c : fetch_word Ubsan.M.loaded_segments (0x2af1c : word) = Some W_2af1c.
Proof. vm_refl. Qed.
Lemma D_2af1c : decode_any W_2af1c = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af20 : bv 32 := 0x00150513.
Lemma F_2af20 : fetch_word Ubsan.M.loaded_segments (0x2af20 : word) = Some W_2af20.
Proof. vm_refl. Qed.
Lemma D_2af20 : decode_any W_2af20 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af24 : bv 32 := 0xfff68613.
Lemma F_2af24 : fetch_word Ubsan.M.loaded_segments (0x2af24 : word) = Some W_2af24.
Proof. vm_refl. Qed.
Lemma D_2af24 : decode_any W_2af24 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af28 : bv 32 := 0x0077f893.
Lemma F_2af28 : fetch_word Ubsan.M.loaded_segments (0x2af28 : word) = Some W_2af28.
Proof. vm_refl. Qed.
Lemma D_2af28 : decode_any W_2af28 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af2c : bv 32 := 0x00c03733.
Lemma F_2af2c : fetch_word Ubsan.M.loaded_segments (0x2af2c : word) = Some W_2af2c.
Proof. vm_refl. Qed.
Lemma D_2af2c : decode_any W_2af2c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af30 : bv 32 := 0x00088663.
Lemma F_2af30 : fetch_word Ubsan.M.loaded_segments (0x2af30 : word) = Some W_2af30.
Proof. vm_refl. Qed.
Lemma D_2af30 : decode_any W_2af30 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af34 : bv 32 := 0x00178793.
Lemma F_2af34 : fetch_word Ubsan.M.loaded_segments (0x2af34 : word) = Some W_2af34.
Proof. vm_refl. Qed.
Lemma D_2af34 : decode_any W_2af34 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af38 : bv 32 := 0xfd069ee3.
Lemma F_2af38 : fetch_word Ubsan.M.loaded_segments (0x2af38 : word) = Some W_2af38.
Proof. vm_refl. Qed.
Lemma D_2af38 : decode_any W_2af38 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af3c : bv 32 := 0x06070863.
Lemma F_2af3c : fetch_word Ubsan.M.loaded_segments (0x2af3c : word) = Some W_2af3c.
Proof. vm_refl. Qed.
Lemma D_2af3c : decode_any W_2af3c = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af40 : bv 32 := 0x00054683.
Lemma F_2af40 : fetch_word Ubsan.M.loaded_segments (0x2af40 : word) = Some W_2af40.
Proof. vm_refl. Qed.
Lemma D_2af40 : decode_any W_2af40 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af44 : bv 32 := 0x04b68663.
Lemma F_2af44 : fetch_word Ubsan.M.loaded_segments (0x2af44 : word) = Some W_2af44.
Proof. vm_refl. Qed.
Lemma D_2af44 : decode_any W_2af44 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af48 : bv 32 := 0x00800693.
Lemma F_2af48 : fetch_word Ubsan.M.loaded_segments (0x2af48 : word) = Some W_2af48.
Proof. vm_refl. Qed.
Lemma D_2af48 : decode_any W_2af48 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af4c : bv 32 := 0x04d66263.
Lemma F_2af4c : fetch_word Ubsan.M.loaded_segments (0x2af4c : word) = Some W_2af4c.
Proof. vm_refl. Qed.
Lemma D_2af4c : decode_any W_2af4c = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af50 : bv 32 := 0xfffe8697.
Lemma F_2af50 : fetch_word Ubsan.M.loaded_segments (0x2af50 : word) = Some W_2af50.
Proof. vm_refl. Qed.
Lemma D_2af50 : decode_any W_2af50 = Some (Auipc 13 1048552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af54 : bv 32 := 0xa106b683.
Lemma F_2af54 : fetch_word Ubsan.M.loaded_segments (0x2af54 : word) = Some W_2af54.
Proof. vm_refl. Qed.
Lemma D_2af54 : decode_any W_2af54 = Some (Load SZ8 true 13 13 2576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af58 : bv 32 := 0xfffe8717.
Lemma F_2af58 : fetch_word Ubsan.M.loaded_segments (0x2af58 : word) = Some W_2af58.
Proof. vm_refl. Qed.
Lemma D_2af58 : decode_any W_2af58 = Some (Auipc 14 1048552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af5c : bv 32 := 0x9f873703.
Lemma F_2af5c : fetch_word Ubsan.M.loaded_segments (0x2af5c : word) = Some W_2af5c.
Proof. vm_refl. Qed.
Lemma D_2af5c : decode_any W_2af5c = Some (Load SZ8 true 14 14 2552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af60 : bv 32 := 0x00168793.
Lemma F_2af60 : fetch_word Ubsan.M.loaded_segments (0x2af60 : word) = Some W_2af60.
Proof. vm_refl. Qed.
Lemma D_2af60 : decode_any W_2af60 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af64 : bv 32 := 0x02f587b3.
Lemma F_2af64 : fetch_word Ubsan.M.loaded_segments (0x2af64 : word) = Some W_2af64.
Proof. vm_refl. Qed.
Lemma D_2af64 : decode_any W_2af64 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af68 : bv 32 := 0x00700813.
Lemma F_2af68 : fetch_word Ubsan.M.loaded_segments (0x2af68 : word) = Some W_2af68.
Proof. vm_refl. Qed.
Lemma D_2af68 : decode_any W_2af68 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af6c : bv 32 := 0x00053883.
Lemma F_2af6c : fetch_word Ubsan.M.loaded_segments (0x2af6c : word) = Some W_2af6c.
Proof. vm_refl. Qed.
Lemma D_2af6c : decode_any W_2af6c = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af70 : bv 32 := 0x00f8c8b3.
Lemma F_2af70 : fetch_word Ubsan.M.loaded_segments (0x2af70 : word) = Some W_2af70.
Proof. vm_refl. Qed.
Lemma D_2af70 : decode_any W_2af70 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af74 : bv 32 := 0x411682b3.
Lemma F_2af74 : fetch_word Ubsan.M.loaded_segments (0x2af74 : word) = Some W_2af74.
Proof. vm_refl. Qed.
Lemma D_2af74 : decode_any W_2af74 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af78 : bv 32 := 0x0112e8b3.
Lemma F_2af78 : fetch_word Ubsan.M.loaded_segments (0x2af78 : word) = Some W_2af78.
Proof. vm_refl. Qed.
Lemma D_2af78 : decode_any W_2af78 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af7c : bv 32 := 0x00e8f8b3.
Lemma F_2af7c : fetch_word Ubsan.M.loaded_segments (0x2af7c : word) = Some W_2af7c.
Proof. vm_refl. Qed.
Lemma D_2af7c : decode_any W_2af7c = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af80 : bv 32 := 0x02e89a63.
Lemma F_2af80 : fetch_word Ubsan.M.loaded_segments (0x2af80 : word) = Some W_2af80.
Proof. vm_refl. Qed.
Lemma D_2af80 : decode_any W_2af80 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af84 : bv 32 := 0xff860613.
Lemma F_2af84 : fetch_word Ubsan.M.loaded_segments (0x2af84 : word) = Some W_2af84.
Proof. vm_refl. Qed.
Lemma D_2af84 : decode_any W_2af84 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af88 : bv 32 := 0x00850513.
Lemma F_2af88 : fetch_word Ubsan.M.loaded_segments (0x2af88 : word) = Some W_2af88.
Proof. vm_refl. Qed.
Lemma D_2af88 : decode_any W_2af88 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af8c : bv 32 := 0xfec860e3.
Lemma F_2af8c : fetch_word Ubsan.M.loaded_segments (0x2af8c : word) = Some W_2af8c.
Proof. vm_refl. Qed.
Lemma D_2af8c : decode_any W_2af8c = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af90 : bv 32 := 0x00060693.
Lemma F_2af90 : fetch_word Ubsan.M.loaded_segments (0x2af90 : word) = Some W_2af90.
Proof. vm_refl. Qed.
Lemma D_2af90 : decode_any W_2af90 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af94 : bv 32 := 0x00060c63.
Lemma F_2af94 : fetch_word Ubsan.M.loaded_segments (0x2af94 : word) = Some W_2af94.
Proof. vm_refl. Qed.
Lemma D_2af94 : decode_any W_2af94 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af98 : bv 32 := 0x00054603.
Lemma F_2af98 : fetch_word Ubsan.M.loaded_segments (0x2af98 : word) = Some W_2af98.
Proof. vm_refl. Qed.
Lemma D_2af98 : decode_any W_2af98 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af9c : bv 32 := 0x00b60a63.
Lemma F_2af9c : fetch_word Ubsan.M.loaded_segments (0x2af9c : word) = Some W_2af9c.
Proof. vm_refl. Qed.
Lemma D_2af9c : decode_any W_2af9c = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2afa0 : bv 32 := 0xfff68693.
Lemma F_2afa0 : fetch_word Ubsan.M.loaded_segments (0x2afa0 : word) = Some W_2afa0.
Proof. vm_refl. Qed.
Lemma D_2afa0 : decode_any W_2afa0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2afa4 : bv 32 := 0x00150513.
Lemma F_2afa4 : fetch_word Ubsan.M.loaded_segments (0x2afa4 : word) = Some W_2afa4.
Proof. vm_refl. Qed.
Lemma D_2afa4 : decode_any W_2afa4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2afa8 : bv 32 := 0xfe0698e3.
Lemma F_2afa8 : fetch_word Ubsan.M.loaded_segments (0x2afa8 : word) = Some W_2afa8.
Proof. vm_refl. Qed.
Lemma D_2afa8 : decode_any W_2afa8 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2afb0 : bv 32 := 0x00008067.
Lemma F_2afb0 : fetch_word Ubsan.M.loaded_segments (0x2afb0 : word) = Some W_2afb0.
Proof. vm_refl. Qed.
Lemma D_2afb0 : decode_any W_2afb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2afb4 : bv 32 := 0x00060693.
Lemma F_2afb4 : fetch_word Ubsan.M.loaded_segments (0x2afb4 : word) = Some W_2afb4.
Proof. vm_refl. Qed.
Lemma D_2afb4 : decode_any W_2afb4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2afb8 : bv 32 := 0x00054603.
Lemma F_2afb8 : fetch_word Ubsan.M.loaded_segments (0x2afb8 : word) = Some W_2afb8.
Proof. vm_refl. Qed.
Lemma D_2afb8 : decode_any W_2afb8 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2afbc : bv 32 := 0xfeb612e3.
Lemma F_2afbc : fetch_word Ubsan.M.loaded_segments (0x2afbc : word) = Some W_2afbc.
Proof. vm_refl. Qed.
Lemma D_2afbc : decode_any W_2afbc = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2afc0 : bv 32 := 0xff1ff06f.
Lemma F_2afc0 : fetch_word Ubsan.M.loaded_segments (0x2afc0 : word) = Some W_2afc0.
Proof. vm_refl. Qed.
Lemma D_2afc0 : decode_any W_2afc0 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aff4 : bv 32 := 0x0035f693.
Lemma F_2aff4 : fetch_word Ubsan.M.loaded_segments (0x2aff4 : word) = Some W_2aff4.
Proof. vm_refl. Qed.
Lemma D_2aff4 : decode_any W_2aff4 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aff8 : bv 32 := 0x10068863.
Lemma F_2aff8 : fetch_word Ubsan.M.loaded_segments (0x2aff8 : word) = Some W_2aff8.
Proof. vm_refl. Qed.
Lemma D_2aff8 : decode_any W_2aff8 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2affc : bv 32 := 0x02060e63.
Lemma F_2affc : fetch_word Ubsan.M.loaded_segments (0x2affc : word) = Some W_2affc.
Proof. vm_refl. Qed.
Lemma D_2affc : decode_any W_2affc = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b000 : bv 32 := 0x00158713.
Lemma F_2b000 : fetch_word Ubsan.M.loaded_segments (0x2b000 : word) = Some W_2b000.
Proof. vm_refl. Qed.
Lemma D_2b000 : decode_any W_2b000 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b004 : bv 32 := 0x00100793.
Lemma F_2b004 : fetch_word Ubsan.M.loaded_segments (0x2b004 : word) = Some W_2b004.
Proof. vm_refl. Qed.
Lemma D_2b004 : decode_any W_2b004 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b008 : bv 32 := 0x00050693.
Lemma F_2b008 : fetch_word Ubsan.M.loaded_segments (0x2b008 : word) = Some W_2b008.
Proof. vm_refl. Qed.
Lemma D_2b008 : decode_any W_2b008 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b00c : bv 32 := 0x0005c883.
Lemma F_2b00c : fetch_word Ubsan.M.loaded_segments (0x2b00c : word) = Some W_2b00c.
Proof. vm_refl. Qed.
Lemma D_2b00c : decode_any W_2b00c = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b010 : bv 32 := 0x00060813.
Lemma F_2b010 : fetch_word Ubsan.M.loaded_segments (0x2b010 : word) = Some W_2b010.
Proof. vm_refl. Qed.
Lemma D_2b010 : decode_any W_2b010 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b014 : bv 32 := 0x00158593.
Lemma F_2b014 : fetch_word Ubsan.M.loaded_segments (0x2b014 : word) = Some W_2b014.
Proof. vm_refl. Qed.
Lemma D_2b014 : decode_any W_2b014 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b018 : bv 32 := 0x00377293.
Lemma F_2b018 : fetch_word Ubsan.M.loaded_segments (0x2b018 : word) = Some W_2b018.
Proof. vm_refl. Qed.
Lemma D_2b018 : decode_any W_2b018 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b01c : bv 32 := 0x01168023.
Lemma F_2b01c : fetch_word Ubsan.M.loaded_segments (0x2b01c : word) = Some W_2b01c.
Proof. vm_refl. Qed.
Lemma D_2b01c : decode_any W_2b01c = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b020 : bv 32 := 0x00168693.
Lemma F_2b020 : fetch_word Ubsan.M.loaded_segments (0x2b020 : word) = Some W_2b020.
Proof. vm_refl. Qed.
Lemma D_2b020 : decode_any W_2b020 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b024 : bv 32 := 0xfff60613.
Lemma F_2b024 : fetch_word Ubsan.M.loaded_segments (0x2b024 : word) = Some W_2b024.
Proof. vm_refl. Qed.
Lemma D_2b024 : decode_any W_2b024 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b028 : bv 32 := 0x00028a63.
Lemma F_2b028 : fetch_word Ubsan.M.loaded_segments (0x2b028 : word) = Some W_2b028.
Proof. vm_refl. Qed.
Lemma D_2b028 : decode_any W_2b028 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b02c : bv 32 := 0x00170713.
Lemma F_2b02c : fetch_word Ubsan.M.loaded_segments (0x2b02c : word) = Some W_2b02c.
Proof. vm_refl. Qed.
Lemma D_2b02c : decode_any W_2b02c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b030 : bv 32 := 0xfcf81ee3.
Lemma F_2b030 : fetch_word Ubsan.M.loaded_segments (0x2b030 : word) = Some W_2b030.
Proof. vm_refl. Qed.
Lemma D_2b030 : decode_any W_2b030 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b034 : bv 32 := 0x0080006f.
Lemma F_2b034 : fetch_word Ubsan.M.loaded_segments (0x2b034 : word) = Some W_2b034.
Proof. vm_refl. Qed.
Lemma D_2b034 : decode_any W_2b034 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b038 : bv 32 := 0x00050693.
Lemma F_2b038 : fetch_word Ubsan.M.loaded_segments (0x2b038 : word) = Some W_2b038.
Proof. vm_refl. Qed.
Lemma D_2b038 : decode_any W_2b038 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
