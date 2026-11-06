(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ce020 : bv 32 := 0x0ff5f593.
Lemma F_ce020 : fetch_word Ubsan.M.loaded_segments (0xce1d8 : word) = Some W_ce020.
Proof. vm_refl. Qed.
Lemma D_ce020 : decode_any W_ce020 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce024 : bv 32 := 0x00757693.
Lemma F_ce024 : fetch_word Ubsan.M.loaded_segments (0xce1dc : word) = Some W_ce024.
Proof. vm_refl. Qed.
Lemma D_ce024 : decode_any W_ce024 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce028 : bv 32 := 0x00c03733.
Lemma F_ce028 : fetch_word Ubsan.M.loaded_segments (0xce1e0 : word) = Some W_ce028.
Proof. vm_refl. Qed.
Lemma D_ce028 : decode_any W_ce028 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce02c : bv 32 := 0x02068c63.
Lemma F_ce02c : fetch_word Ubsan.M.loaded_segments (0xce1e4 : word) = Some W_ce02c.
Proof. vm_refl. Qed.
Lemma D_ce02c : decode_any W_ce02c = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce030 : bv 32 := 0x02060a63.
Lemma F_ce030 : fetch_word Ubsan.M.loaded_segments (0xce1e8 : word) = Some W_ce030.
Proof. vm_refl. Qed.
Lemma D_ce030 : decode_any W_ce030 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce034 : bv 32 := 0x00150793.
Lemma F_ce034 : fetch_word Ubsan.M.loaded_segments (0xce1ec : word) = Some W_ce034.
Proof. vm_refl. Qed.
Lemma D_ce034 : decode_any W_ce034 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce038 : bv 32 := 0x00100813.
Lemma F_ce038 : fetch_word Ubsan.M.loaded_segments (0xce1f0 : word) = Some W_ce038.
Proof. vm_refl. Qed.
Lemma D_ce038 : decode_any W_ce038 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce03c : bv 32 := 0x00054703.
Lemma F_ce03c : fetch_word Ubsan.M.loaded_segments (0xce1f4 : word) = Some W_ce03c.
Proof. vm_refl. Qed.
Lemma D_ce03c : decode_any W_ce03c = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce040 : bv 32 := 0x00060693.
Lemma F_ce040 : fetch_word Ubsan.M.loaded_segments (0xce1f8 : word) = Some W_ce040.
Proof. vm_refl. Qed.
Lemma D_ce040 : decode_any W_ce040 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce044 : bv 32 := 0x06b70e63.
Lemma F_ce044 : fetch_word Ubsan.M.loaded_segments (0xce1fc : word) = Some W_ce044.
Proof. vm_refl. Qed.
Lemma D_ce044 : decode_any W_ce044 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce048 : bv 32 := 0x00150513.
Lemma F_ce048 : fetch_word Ubsan.M.loaded_segments (0xce200 : word) = Some W_ce048.
Proof. vm_refl. Qed.
Lemma D_ce048 : decode_any W_ce048 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce04c : bv 32 := 0xfff68613.
Lemma F_ce04c : fetch_word Ubsan.M.loaded_segments (0xce204 : word) = Some W_ce04c.
Proof. vm_refl. Qed.
Lemma D_ce04c : decode_any W_ce04c = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce050 : bv 32 := 0x0077f893.
Lemma F_ce050 : fetch_word Ubsan.M.loaded_segments (0xce208 : word) = Some W_ce050.
Proof. vm_refl. Qed.
Lemma D_ce050 : decode_any W_ce050 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce054 : bv 32 := 0x00c03733.
Lemma F_ce054 : fetch_word Ubsan.M.loaded_segments (0xce20c : word) = Some W_ce054.
Proof. vm_refl. Qed.
Lemma D_ce054 : decode_any W_ce054 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce058 : bv 32 := 0x00088663.
Lemma F_ce058 : fetch_word Ubsan.M.loaded_segments (0xce210 : word) = Some W_ce058.
Proof. vm_refl. Qed.
Lemma D_ce058 : decode_any W_ce058 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce05c : bv 32 := 0x00178793.
Lemma F_ce05c : fetch_word Ubsan.M.loaded_segments (0xce214 : word) = Some W_ce05c.
Proof. vm_refl. Qed.
Lemma D_ce05c : decode_any W_ce05c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce060 : bv 32 := 0xfd069ee3.
Lemma F_ce060 : fetch_word Ubsan.M.loaded_segments (0xce218 : word) = Some W_ce060.
Proof. vm_refl. Qed.
Lemma D_ce060 : decode_any W_ce060 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce064 : bv 32 := 0x06070863.
Lemma F_ce064 : fetch_word Ubsan.M.loaded_segments (0xce21c : word) = Some W_ce064.
Proof. vm_refl. Qed.
Lemma D_ce064 : decode_any W_ce064 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce068 : bv 32 := 0x00054683.
Lemma F_ce068 : fetch_word Ubsan.M.loaded_segments (0xce220 : word) = Some W_ce068.
Proof. vm_refl. Qed.
Lemma D_ce068 : decode_any W_ce068 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce06c : bv 32 := 0x04b68663.
Lemma F_ce06c : fetch_word Ubsan.M.loaded_segments (0xce224 : word) = Some W_ce06c.
Proof. vm_refl. Qed.
Lemma D_ce06c : decode_any W_ce06c = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce070 : bv 32 := 0x00800693.
Lemma F_ce070 : fetch_word Ubsan.M.loaded_segments (0xce228 : word) = Some W_ce070.
Proof. vm_refl. Qed.
Lemma D_ce070 : decode_any W_ce070 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce074 : bv 32 := 0x04d66263.
Lemma F_ce074 : fetch_word Ubsan.M.loaded_segments (0xce22c : word) = Some W_ce074.
Proof. vm_refl. Qed.
Lemma D_ce074 : decode_any W_ce074 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce078 : bv 32 := 0xfff45697.
Lemma F_ce078 : fetch_word Ubsan.M.loaded_segments (0xce230 : word) = Some W_ce078.
Proof. vm_refl. Qed.
Lemma D_ce078 : decode_any W_ce078 = Some (Auipc 13 1048389, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce07c : bv 32 := 0x2c06b683.
Lemma F_ce07c : fetch_word Ubsan.M.loaded_segments (0xce234 : word) = Some W_ce07c.
Proof. vm_refl. Qed.
Lemma D_ce07c : decode_any W_ce07c = Some (Load SZ8 true 13 13 704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce080 : bv 32 := 0xfff45717.
Lemma F_ce080 : fetch_word Ubsan.M.loaded_segments (0xce238 : word) = Some W_ce080.
Proof. vm_refl. Qed.
Lemma D_ce080 : decode_any W_ce080 = Some (Auipc 14 1048389, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce084 : bv 32 := 0x2a073703.
Lemma F_ce084 : fetch_word Ubsan.M.loaded_segments (0xce23c : word) = Some W_ce084.
Proof. vm_refl. Qed.
Lemma D_ce084 : decode_any W_ce084 = Some (Load SZ8 true 14 14 672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce088 : bv 32 := 0x00168793.
Lemma F_ce088 : fetch_word Ubsan.M.loaded_segments (0xce240 : word) = Some W_ce088.
Proof. vm_refl. Qed.
Lemma D_ce088 : decode_any W_ce088 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce08c : bv 32 := 0x02f587b3.
Lemma F_ce08c : fetch_word Ubsan.M.loaded_segments (0xce244 : word) = Some W_ce08c.
Proof. vm_refl. Qed.
Lemma D_ce08c : decode_any W_ce08c = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce090 : bv 32 := 0x00700813.
Lemma F_ce090 : fetch_word Ubsan.M.loaded_segments (0xce248 : word) = Some W_ce090.
Proof. vm_refl. Qed.
Lemma D_ce090 : decode_any W_ce090 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce094 : bv 32 := 0x00053883.
Lemma F_ce094 : fetch_word Ubsan.M.loaded_segments (0xce24c : word) = Some W_ce094.
Proof. vm_refl. Qed.
Lemma D_ce094 : decode_any W_ce094 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce098 : bv 32 := 0x00f8c8b3.
Lemma F_ce098 : fetch_word Ubsan.M.loaded_segments (0xce250 : word) = Some W_ce098.
Proof. vm_refl. Qed.
Lemma D_ce098 : decode_any W_ce098 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce09c : bv 32 := 0x411682b3.
Lemma F_ce09c : fetch_word Ubsan.M.loaded_segments (0xce254 : word) = Some W_ce09c.
Proof. vm_refl. Qed.
Lemma D_ce09c : decode_any W_ce09c = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0a0 : bv 32 := 0x0112e8b3.
Lemma F_ce0a0 : fetch_word Ubsan.M.loaded_segments (0xce258 : word) = Some W_ce0a0.
Proof. vm_refl. Qed.
Lemma D_ce0a0 : decode_any W_ce0a0 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0a4 : bv 32 := 0x00e8f8b3.
Lemma F_ce0a4 : fetch_word Ubsan.M.loaded_segments (0xce25c : word) = Some W_ce0a4.
Proof. vm_refl. Qed.
Lemma D_ce0a4 : decode_any W_ce0a4 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0a8 : bv 32 := 0x02e89a63.
Lemma F_ce0a8 : fetch_word Ubsan.M.loaded_segments (0xce260 : word) = Some W_ce0a8.
Proof. vm_refl. Qed.
Lemma D_ce0a8 : decode_any W_ce0a8 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0ac : bv 32 := 0xff860613.
Lemma F_ce0ac : fetch_word Ubsan.M.loaded_segments (0xce264 : word) = Some W_ce0ac.
Proof. vm_refl. Qed.
Lemma D_ce0ac : decode_any W_ce0ac = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0b0 : bv 32 := 0x00850513.
Lemma F_ce0b0 : fetch_word Ubsan.M.loaded_segments (0xce268 : word) = Some W_ce0b0.
Proof. vm_refl. Qed.
Lemma D_ce0b0 : decode_any W_ce0b0 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0b4 : bv 32 := 0xfec860e3.
Lemma F_ce0b4 : fetch_word Ubsan.M.loaded_segments (0xce26c : word) = Some W_ce0b4.
Proof. vm_refl. Qed.
Lemma D_ce0b4 : decode_any W_ce0b4 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0b8 : bv 32 := 0x00060693.
Lemma F_ce0b8 : fetch_word Ubsan.M.loaded_segments (0xce270 : word) = Some W_ce0b8.
Proof. vm_refl. Qed.
Lemma D_ce0b8 : decode_any W_ce0b8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0bc : bv 32 := 0x00060c63.
Lemma F_ce0bc : fetch_word Ubsan.M.loaded_segments (0xce274 : word) = Some W_ce0bc.
Proof. vm_refl. Qed.
Lemma D_ce0bc : decode_any W_ce0bc = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0c0 : bv 32 := 0x00054603.
Lemma F_ce0c0 : fetch_word Ubsan.M.loaded_segments (0xce278 : word) = Some W_ce0c0.
Proof. vm_refl. Qed.
Lemma D_ce0c0 : decode_any W_ce0c0 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0c4 : bv 32 := 0x00b60a63.
Lemma F_ce0c4 : fetch_word Ubsan.M.loaded_segments (0xce27c : word) = Some W_ce0c4.
Proof. vm_refl. Qed.
Lemma D_ce0c4 : decode_any W_ce0c4 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0c8 : bv 32 := 0xfff68693.
Lemma F_ce0c8 : fetch_word Ubsan.M.loaded_segments (0xce280 : word) = Some W_ce0c8.
Proof. vm_refl. Qed.
Lemma D_ce0c8 : decode_any W_ce0c8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0cc : bv 32 := 0x00150513.
Lemma F_ce0cc : fetch_word Ubsan.M.loaded_segments (0xce284 : word) = Some W_ce0cc.
Proof. vm_refl. Qed.
Lemma D_ce0cc : decode_any W_ce0cc = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0d0 : bv 32 := 0xfe0698e3.
Lemma F_ce0d0 : fetch_word Ubsan.M.loaded_segments (0xce288 : word) = Some W_ce0d0.
Proof. vm_refl. Qed.
Lemma D_ce0d0 : decode_any W_ce0d0 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0d4 : bv 32 := 0x00000513.
Lemma F_ce0d4 : fetch_word Ubsan.M.loaded_segments (0xce28c : word) = Some W_ce0d4.
Proof. vm_refl. Qed.
Lemma D_ce0d4 : decode_any W_ce0d4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0d8 : bv 32 := 0x00008067.
Lemma F_ce0d8 : fetch_word Ubsan.M.loaded_segments (0xce290 : word) = Some W_ce0d8.
Proof. vm_refl. Qed.
Lemma D_ce0d8 : decode_any W_ce0d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0dc : bv 32 := 0x00060693.
Lemma F_ce0dc : fetch_word Ubsan.M.loaded_segments (0xce294 : word) = Some W_ce0dc.
Proof. vm_refl. Qed.
Lemma D_ce0dc : decode_any W_ce0dc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0e0 : bv 32 := 0x00054603.
Lemma F_ce0e0 : fetch_word Ubsan.M.loaded_segments (0xce298 : word) = Some W_ce0e0.
Proof. vm_refl. Qed.
Lemma D_ce0e0 : decode_any W_ce0e0 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0e4 : bv 32 := 0xfeb612e3.
Lemma F_ce0e4 : fetch_word Ubsan.M.loaded_segments (0xce29c : word) = Some W_ce0e4.
Proof. vm_refl. Qed.
Lemma D_ce0e4 : decode_any W_ce0e4 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce0e8 : bv 32 := 0xff1ff06f.
Lemma F_ce0e8 : fetch_word Ubsan.M.loaded_segments (0xce2a0 : word) = Some W_ce0e8.
Proof. vm_refl. Qed.
Lemma D_ce0e8 : decode_any W_ce0e8 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.
