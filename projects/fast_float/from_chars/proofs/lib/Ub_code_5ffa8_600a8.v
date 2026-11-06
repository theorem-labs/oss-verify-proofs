(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5ffa8 : bv 32 := 0x0d00006f.
Lemma F_5ffa8 : fetch_word Ubsan.M.loaded_segments (0x5ffa8 : word) = Some W_5ffa8.
Proof. vm_refl. Qed.
Lemma D_5ffa8 : decode_any W_5ffa8 = Some (Jal 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffac : bv 32 := 0x0ff5f593.
Lemma F_5ffac : fetch_word Ubsan.M.loaded_segments (0x5ffac : word) = Some W_5ffac.
Proof. vm_refl. Qed.
Lemma D_5ffac : decode_any W_5ffac = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffb0 : bv 32 := 0x00757693.
Lemma F_5ffb0 : fetch_word Ubsan.M.loaded_segments (0x5ffb0 : word) = Some W_5ffb0.
Proof. vm_refl. Qed.
Lemma D_5ffb0 : decode_any W_5ffb0 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffb4 : bv 32 := 0x00c03733.
Lemma F_5ffb4 : fetch_word Ubsan.M.loaded_segments (0x5ffb4 : word) = Some W_5ffb4.
Proof. vm_refl. Qed.
Lemma D_5ffb4 : decode_any W_5ffb4 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffb8 : bv 32 := 0x02068c63.
Lemma F_5ffb8 : fetch_word Ubsan.M.loaded_segments (0x5ffb8 : word) = Some W_5ffb8.
Proof. vm_refl. Qed.
Lemma D_5ffb8 : decode_any W_5ffb8 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffbc : bv 32 := 0x02060a63.
Lemma F_5ffbc : fetch_word Ubsan.M.loaded_segments (0x5ffbc : word) = Some W_5ffbc.
Proof. vm_refl. Qed.
Lemma D_5ffbc : decode_any W_5ffbc = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffc0 : bv 32 := 0x00150793.
Lemma F_5ffc0 : fetch_word Ubsan.M.loaded_segments (0x5ffc0 : word) = Some W_5ffc0.
Proof. vm_refl. Qed.
Lemma D_5ffc0 : decode_any W_5ffc0 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffc4 : bv 32 := 0x00100813.
Lemma F_5ffc4 : fetch_word Ubsan.M.loaded_segments (0x5ffc4 : word) = Some W_5ffc4.
Proof. vm_refl. Qed.
Lemma D_5ffc4 : decode_any W_5ffc4 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffc8 : bv 32 := 0x00054703.
Lemma F_5ffc8 : fetch_word Ubsan.M.loaded_segments (0x5ffc8 : word) = Some W_5ffc8.
Proof. vm_refl. Qed.
Lemma D_5ffc8 : decode_any W_5ffc8 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffcc : bv 32 := 0x00060693.
Lemma F_5ffcc : fetch_word Ubsan.M.loaded_segments (0x5ffcc : word) = Some W_5ffcc.
Proof. vm_refl. Qed.
Lemma D_5ffcc : decode_any W_5ffcc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffd0 : bv 32 := 0x06b70e63.
Lemma F_5ffd0 : fetch_word Ubsan.M.loaded_segments (0x5ffd0 : word) = Some W_5ffd0.
Proof. vm_refl. Qed.
Lemma D_5ffd0 : decode_any W_5ffd0 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffd4 : bv 32 := 0x00150513.
Lemma F_5ffd4 : fetch_word Ubsan.M.loaded_segments (0x5ffd4 : word) = Some W_5ffd4.
Proof. vm_refl. Qed.
Lemma D_5ffd4 : decode_any W_5ffd4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffd8 : bv 32 := 0xfff68613.
Lemma F_5ffd8 : fetch_word Ubsan.M.loaded_segments (0x5ffd8 : word) = Some W_5ffd8.
Proof. vm_refl. Qed.
Lemma D_5ffd8 : decode_any W_5ffd8 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffdc : bv 32 := 0x0077f893.
Lemma F_5ffdc : fetch_word Ubsan.M.loaded_segments (0x5ffdc : word) = Some W_5ffdc.
Proof. vm_refl. Qed.
Lemma D_5ffdc : decode_any W_5ffdc = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffe0 : bv 32 := 0x00c03733.
Lemma F_5ffe0 : fetch_word Ubsan.M.loaded_segments (0x5ffe0 : word) = Some W_5ffe0.
Proof. vm_refl. Qed.
Lemma D_5ffe0 : decode_any W_5ffe0 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffe4 : bv 32 := 0x00088663.
Lemma F_5ffe4 : fetch_word Ubsan.M.loaded_segments (0x5ffe4 : word) = Some W_5ffe4.
Proof. vm_refl. Qed.
Lemma D_5ffe4 : decode_any W_5ffe4 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffe8 : bv 32 := 0x00178793.
Lemma F_5ffe8 : fetch_word Ubsan.M.loaded_segments (0x5ffe8 : word) = Some W_5ffe8.
Proof. vm_refl. Qed.
Lemma D_5ffe8 : decode_any W_5ffe8 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ffec : bv 32 := 0xfd069ee3.
Lemma F_5ffec : fetch_word Ubsan.M.loaded_segments (0x5ffec : word) = Some W_5ffec.
Proof. vm_refl. Qed.
Lemma D_5ffec : decode_any W_5ffec = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fff0 : bv 32 := 0x06070863.
Lemma F_5fff0 : fetch_word Ubsan.M.loaded_segments (0x5fff0 : word) = Some W_5fff0.
Proof. vm_refl. Qed.
Lemma D_5fff0 : decode_any W_5fff0 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fff4 : bv 32 := 0x00054683.
Lemma F_5fff4 : fetch_word Ubsan.M.loaded_segments (0x5fff4 : word) = Some W_5fff4.
Proof. vm_refl. Qed.
Lemma D_5fff4 : decode_any W_5fff4 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fff8 : bv 32 := 0x04b68663.
Lemma F_5fff8 : fetch_word Ubsan.M.loaded_segments (0x5fff8 : word) = Some W_5fff8.
Proof. vm_refl. Qed.
Lemma D_5fff8 : decode_any W_5fff8 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fffc : bv 32 := 0x00800693.
Lemma F_5fffc : fetch_word Ubsan.M.loaded_segments (0x5fffc : word) = Some W_5fffc.
Proof. vm_refl. Qed.
Lemma D_5fffc : decode_any W_5fffc = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60000 : bv 32 := 0x04d66263.
Lemma F_60000 : fetch_word Ubsan.M.loaded_segments (0x60000 : word) = Some W_60000.
Proof. vm_refl. Qed.
Lemma D_60000 : decode_any W_60000 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60004 : bv 32 := 0xfffb3697.
Lemma F_60004 : fetch_word Ubsan.M.loaded_segments (0x60004 : word) = Some W_60004.
Proof. vm_refl. Qed.
Lemma D_60004 : decode_any W_60004 = Some (Auipc 13 1048499, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60008 : bv 32 := 0xfbc6b683.
Lemma F_60008 : fetch_word Ubsan.M.loaded_segments (0x60008 : word) = Some W_60008.
Proof. vm_refl. Qed.
Lemma D_60008 : decode_any W_60008 = Some (Load SZ8 true 13 13 4028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6000c : bv 32 := 0xfffb3717.
Lemma F_6000c : fetch_word Ubsan.M.loaded_segments (0x6000c : word) = Some W_6000c.
Proof. vm_refl. Qed.
Lemma D_6000c : decode_any W_6000c = Some (Auipc 14 1048499, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60010 : bv 32 := 0xf9c73703.
Lemma F_60010 : fetch_word Ubsan.M.loaded_segments (0x60010 : word) = Some W_60010.
Proof. vm_refl. Qed.
Lemma D_60010 : decode_any W_60010 = Some (Load SZ8 true 14 14 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60014 : bv 32 := 0x00168793.
Lemma F_60014 : fetch_word Ubsan.M.loaded_segments (0x60014 : word) = Some W_60014.
Proof. vm_refl. Qed.
Lemma D_60014 : decode_any W_60014 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60018 : bv 32 := 0x02f587b3.
Lemma F_60018 : fetch_word Ubsan.M.loaded_segments (0x60018 : word) = Some W_60018.
Proof. vm_refl. Qed.
Lemma D_60018 : decode_any W_60018 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6001c : bv 32 := 0x00700813.
Lemma F_6001c : fetch_word Ubsan.M.loaded_segments (0x6001c : word) = Some W_6001c.
Proof. vm_refl. Qed.
Lemma D_6001c : decode_any W_6001c = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60020 : bv 32 := 0x00053883.
Lemma F_60020 : fetch_word Ubsan.M.loaded_segments (0x60020 : word) = Some W_60020.
Proof. vm_refl. Qed.
Lemma D_60020 : decode_any W_60020 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60024 : bv 32 := 0x00f8c8b3.
Lemma F_60024 : fetch_word Ubsan.M.loaded_segments (0x60024 : word) = Some W_60024.
Proof. vm_refl. Qed.
Lemma D_60024 : decode_any W_60024 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60028 : bv 32 := 0x411682b3.
Lemma F_60028 : fetch_word Ubsan.M.loaded_segments (0x60028 : word) = Some W_60028.
Proof. vm_refl. Qed.
Lemma D_60028 : decode_any W_60028 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6002c : bv 32 := 0x0112e8b3.
Lemma F_6002c : fetch_word Ubsan.M.loaded_segments (0x6002c : word) = Some W_6002c.
Proof. vm_refl. Qed.
Lemma D_6002c : decode_any W_6002c = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60030 : bv 32 := 0x00e8f8b3.
Lemma F_60030 : fetch_word Ubsan.M.loaded_segments (0x60030 : word) = Some W_60030.
Proof. vm_refl. Qed.
Lemma D_60030 : decode_any W_60030 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60034 : bv 32 := 0x02e89a63.
Lemma F_60034 : fetch_word Ubsan.M.loaded_segments (0x60034 : word) = Some W_60034.
Proof. vm_refl. Qed.
Lemma D_60034 : decode_any W_60034 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60038 : bv 32 := 0xff860613.
Lemma F_60038 : fetch_word Ubsan.M.loaded_segments (0x60038 : word) = Some W_60038.
Proof. vm_refl. Qed.
Lemma D_60038 : decode_any W_60038 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6003c : bv 32 := 0x00850513.
Lemma F_6003c : fetch_word Ubsan.M.loaded_segments (0x6003c : word) = Some W_6003c.
Proof. vm_refl. Qed.
Lemma D_6003c : decode_any W_6003c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60040 : bv 32 := 0xfec860e3.
Lemma F_60040 : fetch_word Ubsan.M.loaded_segments (0x60040 : word) = Some W_60040.
Proof. vm_refl. Qed.
Lemma D_60040 : decode_any W_60040 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60044 : bv 32 := 0x00060693.
Lemma F_60044 : fetch_word Ubsan.M.loaded_segments (0x60044 : word) = Some W_60044.
Proof. vm_refl. Qed.
Lemma D_60044 : decode_any W_60044 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60048 : bv 32 := 0x00060c63.
Lemma F_60048 : fetch_word Ubsan.M.loaded_segments (0x60048 : word) = Some W_60048.
Proof. vm_refl. Qed.
Lemma D_60048 : decode_any W_60048 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6004c : bv 32 := 0x00054603.
Lemma F_6004c : fetch_word Ubsan.M.loaded_segments (0x6004c : word) = Some W_6004c.
Proof. vm_refl. Qed.
Lemma D_6004c : decode_any W_6004c = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60050 : bv 32 := 0x00b60a63.
Lemma F_60050 : fetch_word Ubsan.M.loaded_segments (0x60050 : word) = Some W_60050.
Proof. vm_refl. Qed.
Lemma D_60050 : decode_any W_60050 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60054 : bv 32 := 0xfff68693.
Lemma F_60054 : fetch_word Ubsan.M.loaded_segments (0x60054 : word) = Some W_60054.
Proof. vm_refl. Qed.
Lemma D_60054 : decode_any W_60054 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60058 : bv 32 := 0x00150513.
Lemma F_60058 : fetch_word Ubsan.M.loaded_segments (0x60058 : word) = Some W_60058.
Proof. vm_refl. Qed.
Lemma D_60058 : decode_any W_60058 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6005c : bv 32 := 0xfe0698e3.
Lemma F_6005c : fetch_word Ubsan.M.loaded_segments (0x6005c : word) = Some W_6005c.
Proof. vm_refl. Qed.
Lemma D_6005c : decode_any W_6005c = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60060 : bv 32 := 0x00000513.
Lemma F_60060 : fetch_word Ubsan.M.loaded_segments (0x60060 : word) = Some W_60060.
Proof. vm_refl. Qed.
Lemma D_60060 : decode_any W_60060 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60064 : bv 32 := 0x00008067.
Lemma F_60064 : fetch_word Ubsan.M.loaded_segments (0x60064 : word) = Some W_60064.
Proof. vm_refl. Qed.
Lemma D_60064 : decode_any W_60064 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60068 : bv 32 := 0x00060693.
Lemma F_60068 : fetch_word Ubsan.M.loaded_segments (0x60068 : word) = Some W_60068.
Proof. vm_refl. Qed.
Lemma D_60068 : decode_any W_60068 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6006c : bv 32 := 0x00054603.
Lemma F_6006c : fetch_word Ubsan.M.loaded_segments (0x6006c : word) = Some W_6006c.
Proof. vm_refl. Qed.
Lemma D_6006c : decode_any W_6006c = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60070 : bv 32 := 0xfeb612e3.
Lemma F_60070 : fetch_word Ubsan.M.loaded_segments (0x60070 : word) = Some W_60070.
Proof. vm_refl. Qed.
Lemma D_60070 : decode_any W_60070 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60074 : bv 32 := 0xff1ff06f.
Lemma F_60074 : fetch_word Ubsan.M.loaded_segments (0x60074 : word) = Some W_60074.
Proof. vm_refl. Qed.
Lemma D_60074 : decode_any W_60074 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60078 : bv 32 := 0x02060063.
Lemma F_60078 : fetch_word Ubsan.M.loaded_segments (0x60078 : word) = Some W_60078.
Proof. vm_refl. Qed.
Lemma D_60078 : decode_any W_60078 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6007c : bv 32 := 0x00054683.
Lemma F_6007c : fetch_word Ubsan.M.loaded_segments (0x6007c : word) = Some W_6007c.
Proof. vm_refl. Qed.
Lemma D_6007c : decode_any W_6007c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60080 : bv 32 := 0x0005c703.
Lemma F_60080 : fetch_word Ubsan.M.loaded_segments (0x60080 : word) = Some W_60080.
Proof. vm_refl. Qed.
Lemma D_60080 : decode_any W_60080 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60084 : bv 32 := 0x00e69e63.
Lemma F_60084 : fetch_word Ubsan.M.loaded_segments (0x60084 : word) = Some W_60084.
Proof. vm_refl. Qed.
Lemma D_60084 : decode_any W_60084 = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60088 : bv 32 := 0xfff60613.
Lemma F_60088 : fetch_word Ubsan.M.loaded_segments (0x60088 : word) = Some W_60088.
Proof. vm_refl. Qed.
Lemma D_60088 : decode_any W_60088 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6008c : bv 32 := 0x00150513.
Lemma F_6008c : fetch_word Ubsan.M.loaded_segments (0x6008c : word) = Some W_6008c.
Proof. vm_refl. Qed.
Lemma D_6008c : decode_any W_6008c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60090 : bv 32 := 0x00158593.
Lemma F_60090 : fetch_word Ubsan.M.loaded_segments (0x60090 : word) = Some W_60090.
Proof. vm_refl. Qed.
Lemma D_60090 : decode_any W_60090 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60094 : bv 32 := 0xfe0614e3.
Lemma F_60094 : fetch_word Ubsan.M.loaded_segments (0x60094 : word) = Some W_60094.
Proof. vm_refl. Qed.
Lemma D_60094 : decode_any W_60094 = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60098 : bv 32 := 0x00000513.
Lemma F_60098 : fetch_word Ubsan.M.loaded_segments (0x60098 : word) = Some W_60098.
Proof. vm_refl. Qed.
Lemma D_60098 : decode_any W_60098 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6009c : bv 32 := 0x00008067.
Lemma F_6009c : fetch_word Ubsan.M.loaded_segments (0x6009c : word) = Some W_6009c.
Proof. vm_refl. Qed.
Lemma D_6009c : decode_any W_6009c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600a0 : bv 32 := 0x40e68533.
Lemma F_600a0 : fetch_word Ubsan.M.loaded_segments (0x600a0 : word) = Some W_600a0.
Proof. vm_refl. Qed.
Lemma D_600a0 : decode_any W_600a0 = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600a4 : bv 32 := 0x00008067.
Lemma F_600a4 : fetch_word Ubsan.M.loaded_segments (0x600a4 : word) = Some W_600a4.
Proof. vm_refl. Qed.
Lemma D_600a4 : decode_any W_600a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
