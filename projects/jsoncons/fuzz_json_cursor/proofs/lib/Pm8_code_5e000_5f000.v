(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5e000 : bv 32 := 0x0f0f17b7.
Lemma F_5e000 : fetch_word Asan.M.loaded_segments (0x5e050 : word) = Some W_5e000.
Proof. vm_refl. Qed.
Lemma D_5e000 : decode_any W_5e000 = Some (Lui 15 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e004 : bv 32 := 0x00b965b3.
Lemma F_5e004 : fetch_word Asan.M.loaded_segments (0x5e054 : word) = Some W_5e004.
Proof. vm_refl. Qed.
Lemma D_5e004 : decode_any W_5e004 = Some (Op ALU_OR 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e008 : bv 32 := 0x5556061b.
Lemma F_5e008 : fetch_word Asan.M.loaded_segments (0x5e058 : word) = Some W_5e008.
Proof. vm_refl. Qed.
Lemma D_5e008 : decode_any W_5e008 = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e00c : bv 32 := 0x3337071b.
Lemma F_5e00c : fetch_word Asan.M.loaded_segments (0x5e05c : word) = Some W_5e00c.
Proof. vm_refl. Qed.
Lemma D_5e00c : decode_any W_5e00c = Some (OpImm32 14 14 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e010 : bv 32 := 0xf0f7879b.
Lemma F_5e010 : fetch_word Asan.M.loaded_segments (0x5e060 : word) = Some W_5e010.
Proof. vm_refl. Qed.
Lemma D_5e010 : decode_any W_5e010 = Some (OpImm32 15 15 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e014 : bv 32 := 0x0025d813.
Lemma F_5e014 : fetch_word Asan.M.loaded_segments (0x5e064 : word) = Some W_5e014.
Proof. vm_refl. Qed.
Lemma D_5e014 : decode_any W_5e014 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e018 : bv 32 := 0x0105e5b3.
Lemma F_5e018 : fetch_word Asan.M.loaded_segments (0x5e068 : word) = Some W_5e018.
Proof. vm_refl. Qed.
Lemma D_5e018 : decode_any W_5e018 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e01c : bv 32 := 0x02061813.
Lemma F_5e01c : fetch_word Asan.M.loaded_segments (0x5e06c : word) = Some W_5e01c.
Proof. vm_refl. Qed.
Lemma D_5e01c : decode_any W_5e01c = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e020 : bv 32 := 0x01060633.
Lemma F_5e020 : fetch_word Asan.M.loaded_segments (0x5e070 : word) = Some W_5e020.
Proof. vm_refl. Qed.
Lemma D_5e020 : decode_any W_5e020 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e024 : bv 32 := 0x02071813.
Lemma F_5e024 : fetch_word Asan.M.loaded_segments (0x5e074 : word) = Some W_5e024.
Proof. vm_refl. Qed.
Lemma D_5e024 : decode_any W_5e024 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e028 : bv 32 := 0x01070733.
Lemma F_5e028 : fetch_word Asan.M.loaded_segments (0x5e078 : word) = Some W_5e028.
Proof. vm_refl. Qed.
Lemma D_5e028 : decode_any W_5e028 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e02c : bv 32 := 0x02079813.
Lemma F_5e02c : fetch_word Asan.M.loaded_segments (0x5e07c : word) = Some W_5e02c.
Proof. vm_refl. Qed.
Lemma D_5e02c : decode_any W_5e02c = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e030 : bv 32 := 0x010787b3.
Lemma F_5e030 : fetch_word Asan.M.loaded_segments (0x5e080 : word) = Some W_5e030.
Proof. vm_refl. Qed.
Lemma D_5e030 : decode_any W_5e030 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e034 : bv 32 := 0x0045d813.
Lemma F_5e034 : fetch_word Asan.M.loaded_segments (0x5e084 : word) = Some W_5e034.
Proof. vm_refl. Qed.
Lemma D_5e034 : decode_any W_5e034 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e038 : bv 32 := 0x0105e5b3.
Lemma F_5e038 : fetch_word Asan.M.loaded_segments (0x5e088 : word) = Some W_5e038.
Proof. vm_refl. Qed.
Lemma D_5e038 : decode_any W_5e038 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e03c : bv 32 := 0x0085d813.
Lemma F_5e03c : fetch_word Asan.M.loaded_segments (0x5e08c : word) = Some W_5e03c.
Proof. vm_refl. Qed.
Lemma D_5e03c : decode_any W_5e03c = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e040 : bv 32 := 0x0105e5b3.
Lemma F_5e040 : fetch_word Asan.M.loaded_segments (0x5e090 : word) = Some W_5e040.
Proof. vm_refl. Qed.
Lemma D_5e040 : decode_any W_5e040 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e044 : bv 32 := 0x0105d813.
Lemma F_5e044 : fetch_word Asan.M.loaded_segments (0x5e094 : word) = Some W_5e044.
Proof. vm_refl. Qed.
Lemma D_5e044 : decode_any W_5e044 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e048 : bv 32 := 0x0105e5b3.
Lemma F_5e048 : fetch_word Asan.M.loaded_segments (0x5e098 : word) = Some W_5e048.
Proof. vm_refl. Qed.
Lemma D_5e048 : decode_any W_5e048 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e04c : bv 32 := 0x0205d813.
Lemma F_5e04c : fetch_word Asan.M.loaded_segments (0x5e09c : word) = Some W_5e04c.
Proof. vm_refl. Qed.
Lemma D_5e04c : decode_any W_5e04c = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e050 : bv 32 := 0x0105e5b3.
Lemma F_5e050 : fetch_word Asan.M.loaded_segments (0x5e0a0 : word) = Some W_5e050.
Proof. vm_refl. Qed.
Lemma D_5e050 : decode_any W_5e050 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e054 : bv 32 := 0xfff5c593.
Lemma F_5e054 : fetch_word Asan.M.loaded_segments (0x5e0a4 : word) = Some W_5e054.
Proof. vm_refl. Qed.
Lemma D_5e054 : decode_any W_5e054 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e058 : bv 32 := 0x0015d813.
Lemma F_5e058 : fetch_word Asan.M.loaded_segments (0x5e0a8 : word) = Some W_5e058.
Proof. vm_refl. Qed.
Lemma D_5e058 : decode_any W_5e058 = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e05c : bv 32 := 0x00c87633.
Lemma F_5e05c : fetch_word Asan.M.loaded_segments (0x5e0ac : word) = Some W_5e05c.
Proof. vm_refl. Qed.
Lemma D_5e05c : decode_any W_5e05c = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e060 : bv 32 := 0x01010837.
Lemma F_5e060 : fetch_word Asan.M.loaded_segments (0x5e0b0 : word) = Some W_5e060.
Proof. vm_refl. Qed.
Lemma D_5e060 : decode_any W_5e060 = Some (Lui 16 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e064 : bv 32 := 0x40c585b3.
Lemma F_5e064 : fetch_word Asan.M.loaded_segments (0x5e0b4 : word) = Some W_5e064.
Proof. vm_refl. Qed.
Lemma D_5e064 : decode_any W_5e064 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e068 : bv 32 := 0x0025d613.
Lemma F_5e068 : fetch_word Asan.M.loaded_segments (0x5e0b8 : word) = Some W_5e068.
Proof. vm_refl. Qed.
Lemma D_5e068 : decode_any W_5e068 = Some (ShiftImm ALU_SRL 12 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e06c : bv 32 := 0x00e5f5b3.
Lemma F_5e06c : fetch_word Asan.M.loaded_segments (0x5e0bc : word) = Some W_5e06c.
Proof. vm_refl. Qed.
Lemma D_5e06c : decode_any W_5e06c = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e070 : bv 32 := 0x00e67633.
Lemma F_5e070 : fetch_word Asan.M.loaded_segments (0x5e0c0 : word) = Some W_5e070.
Proof. vm_refl. Qed.
Lemma D_5e070 : decode_any W_5e070 = Some (Op ALU_AND 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e074 : bv 32 := 0x0304b703.
Lemma F_5e074 : fetch_word Asan.M.loaded_segments (0x5e0c4 : word) = Some W_5e074.
Proof. vm_refl. Qed.
Lemma D_5e074 : decode_any W_5e074 = Some (Load SZ8 true 14 9 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e078 : bv 32 := 0x1018081b.
Lemma F_5e078 : fetch_word Asan.M.loaded_segments (0x5e0c8 : word) = Some W_5e078.
Proof. vm_refl. Qed.
Lemma D_5e078 : decode_any W_5e078 = Some (OpImm32 16 16 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e07c : bv 32 := 0x00c585b3.
Lemma F_5e07c : fetch_word Asan.M.loaded_segments (0x5e0cc : word) = Some W_5e07c.
Proof. vm_refl. Qed.
Lemma D_5e07c : decode_any W_5e07c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e080 : bv 32 := 0x0045d613.
Lemma F_5e080 : fetch_word Asan.M.loaded_segments (0x5e0d0 : word) = Some W_5e080.
Proof. vm_refl. Qed.
Lemma D_5e080 : decode_any W_5e080 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e084 : bv 32 := 0x00c585b3.
Lemma F_5e084 : fetch_word Asan.M.loaded_segments (0x5e0d4 : word) = Some W_5e084.
Proof. vm_refl. Qed.
Lemma D_5e084 : decode_any W_5e084 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e088 : bv 32 := 0x02081613.
Lemma F_5e088 : fetch_word Asan.M.loaded_segments (0x5e0d8 : word) = Some W_5e088.
Proof. vm_refl. Qed.
Lemma D_5e088 : decode_any W_5e088 = Some (ShiftImm ALU_SLL 12 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e08c : bv 32 := 0x00f5f5b3.
Lemma F_5e08c : fetch_word Asan.M.loaded_segments (0x5e0dc : word) = Some W_5e08c.
Proof. vm_refl. Qed.
Lemma D_5e08c : decode_any W_5e08c = Some (Op ALU_AND 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e090 : bv 32 := 0x00c80633.
Lemma F_5e090 : fetch_word Asan.M.loaded_segments (0x5e0e0 : word) = Some W_5e090.
Proof. vm_refl. Qed.
Lemma D_5e090 : decode_any W_5e090 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e094 : bv 32 := 0x02c585b3.
Lemma F_5e094 : fetch_word Asan.M.loaded_segments (0x5e0e4 : word) = Some W_5e094.
Proof. vm_refl. Qed.
Lemma D_5e094 : decode_any W_5e094 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e098 : bv 32 := 0x0385d993.
Lemma F_5e098 : fetch_word Asan.M.loaded_segments (0x5e0e8 : word) = Some W_5e098.
Proof. vm_refl. Qed.
Lemma D_5e098 : decode_any W_5e098 = Some (ShiftImm ALU_SRL 19 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e09c : bv 32 := 0x1ce68c63.
Lemma F_5e09c : fetch_word Asan.M.loaded_segments (0x5e0ec : word) = Some W_5e09c.
Proof. vm_refl. Qed.
Lemma D_5e09c : decode_any W_5e09c = Some (Branch BC_EQ 13 14 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a0 : bv 32 := 0x0084b603.
Lemma F_5e0a0 : fetch_word Asan.M.loaded_segments (0x5e0f0 : word) = Some W_5e0a0.
Proof. vm_refl. Qed.
Lemma D_5e0a0 : decode_any W_5e0a0 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a4 : bv 32 := 0x03f9c593.
Lemma F_5e0a4 : fetch_word Asan.M.loaded_segments (0x5e0f4 : word) = Some W_5e0a4.
Proof. vm_refl. Qed.
Lemma D_5e0a4 : decode_any W_5e0a4 = Some (OpImm ALU_XOR 11 19 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a8 : bv 32 := 0x00dabc23.
Lemma F_5e0a8 : fetch_word Asan.M.loaded_segments (0x5e0f8 : word) = Some W_5e0a8.
Proof. vm_refl. Qed.
Lemma D_5e0a8 : decode_any W_5e0a8 = Some (Store SZ8 21 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0ac : bv 32 := 0x00369713.
Lemma F_5e0ac : fetch_word Asan.M.loaded_segments (0x5e0fc : word) = Some W_5e0ac.
Proof. vm_refl. Qed.
Lemma D_5e0ac : decode_any W_5e0ac = Some (ShiftImm ALU_SLL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b0 : bv 32 := 0x00e60633.
Lemma F_5e0b0 : fetch_word Asan.M.loaded_segments (0x5e100 : word) = Some W_5e0b0.
Proof. vm_refl. Qed.
Lemma D_5e0b0 : decode_any W_5e0b0 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b4 : bv 32 := 0x01563023.
Lemma F_5e0b4 : fetch_word Asan.M.loaded_segments (0x5e104 : word) = Some W_5e0b4.
Proof. vm_refl. Qed.
Lemma D_5e0b4 : decode_any W_5e0b4 = Some (Store SZ8 12 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b8 : bv 32 := 0x0484b703.
Lemma F_5e0b8 : fetch_word Asan.M.loaded_segments (0x5e108 : word) = Some W_5e0b8.
Proof. vm_refl. Qed.
Lemma D_5e0b8 : decode_any W_5e0b8 = Some (Load SZ8 true 14 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0bc : bv 32 := 0x0584b783.
Lemma F_5e0bc : fetch_word Asan.M.loaded_segments (0x5e10c : word) = Some W_5e0bc.
Proof. vm_refl. Qed.
Lemma D_5e0bc : decode_any W_5e0bc = Some (Load SZ8 true 15 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c0 : bv 32 := 0x00168813.
Lemma F_5e0c0 : fetch_word Asan.M.loaded_segments (0x5e110 : word) = Some W_5e0c0.
Proof. vm_refl. Qed.
Lemma D_5e0c0 : decode_any W_5e0c0 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c4 : bv 32 := 0x0604b603.
Lemma F_5e0c4 : fetch_word Asan.M.loaded_segments (0x5e114 : word) = Some W_5e0c4.
Proof. vm_refl. Qed.
Lemma D_5e0c4 : decode_any W_5e0c4 = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c8 : bv 32 := 0x00170713.
Lemma F_5e0c8 : fetch_word Asan.M.loaded_segments (0x5e118 : word) = Some W_5e0c8.
Proof. vm_refl. Qed.
Lemma D_5e0c8 : decode_any W_5e0c8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0cc : bv 32 := 0x012786b3.
Lemma F_5e0cc : fetch_word Asan.M.loaded_segments (0x5e11c : word) = Some W_5e0cc.
Proof. vm_refl. Qed.
Lemma D_5e0cc : decode_any W_5e0cc = Some (Op ALU_ADD 13 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d0 : bv 32 := 0x0304bc23.
Lemma F_5e0d0 : fetch_word Asan.M.loaded_segments (0x5e120 : word) = Some W_5e0d0.
Proof. vm_refl. Qed.
Lemma D_5e0d0 : decode_any W_5e0d0 = Some (Store SZ8 9 16 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d4 : bv 32 := 0x04048023.
Lemma F_5e0d4 : fetch_word Asan.M.loaded_segments (0x5e124 : word) = Some W_5e0d4.
Proof. vm_refl. Qed.
Lemma D_5e0d4 : decode_any W_5e0d4 = Some (Store SZ1 9 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d8 : bv 32 := 0x04e4b423.
Lemma F_5e0d8 : fetch_word Asan.M.loaded_segments (0x5e128 : word) = Some W_5e0d8.
Proof. vm_refl. Qed.
Lemma D_5e0d8 : decode_any W_5e0d8 = Some (Store SZ8 9 14 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0dc : bv 32 := 0x04d4bc23.
Lemma F_5e0dc : fetch_word Asan.M.loaded_segments (0x5e12c : word) = Some W_5e0dc.
Proof. vm_refl. Qed.
Lemma D_5e0dc : decode_any W_5e0dc = Some (Store SZ8 9 13 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e0 : bv 32 := 0x00c6e463.
Lemma F_5e0e0 : fetch_word Asan.M.loaded_segments (0x5e130 : word) = Some W_5e0e0.
Proof. vm_refl. Qed.
Lemma D_5e0e0 : decode_any W_5e0e0 = Some (Branch BC_LTU 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e4 : bv 32 := 0x00068613.
Lemma F_5e0e4 : fetch_word Asan.M.loaded_segments (0x5e134 : word) = Some W_5e0e4.
Proof. vm_refl. Qed.
Lemma D_5e0e4 : decode_any W_5e0e4 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e8 : bv 32 := 0x00359593.
Lemma F_5e0e8 : fetch_word Asan.M.loaded_segments (0x5e138 : word) = Some W_5e0e8.
Proof. vm_refl. Qed.
Lemma D_5e0e8 : decode_any W_5e0e8 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0ec : bv 32 := 0x00b485b3.
Lemma F_5e0ec : fetch_word Asan.M.loaded_segments (0x5e13c : word) = Some W_5e0ec.
Proof. vm_refl. Qed.
Lemma D_5e0ec : decode_any W_5e0ec = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f0 : bv 32 := 0x0685b683.
Lemma F_5e0f0 : fetch_word Asan.M.loaded_segments (0x5e140 : word) = Some W_5e0f0.
Proof. vm_refl. Qed.
Lemma D_5e0f0 : decode_any W_5e0f0 = Some (Load SZ8 true 13 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f4 : bv 32 := 0x00168693.
Lemma F_5e0f4 : fetch_word Asan.M.loaded_segments (0x5e144 : word) = Some W_5e0f4.
Proof. vm_refl. Qed.
Lemma D_5e0f4 : decode_any W_5e0f4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f8 : bv 32 := 0x06c4b023.
Lemma F_5e0f8 : fetch_word Asan.M.loaded_segments (0x5e148 : word) = Some W_5e0f8.
Proof. vm_refl. Qed.
Lemma D_5e0f8 : decode_any W_5e0f8 = Some (Store SZ8 9 12 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0fc : bv 32 := 0x06d5b423.
Lemma F_5e0fc : fetch_word Asan.M.loaded_segments (0x5e14c : word) = Some W_5e0fc.
Proof. vm_refl. Qed.
Lemma D_5e0fc : decode_any W_5e0fc = Some (Store SZ8 11 13 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e100 : bv 32 := 0x01040593.
Lemma F_5e100 : fetch_word Asan.M.loaded_segments (0x5e150 : word) = Some W_5e100.
Proof. vm_refl. Qed.
Lemma D_5e100 : decode_any W_5e100 = Some (OpImm ALU_ADD 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e104 : bv 32 := 0x0125b02f.
Lemma F_5e104 : fetch_word Asan.M.loaded_segments (0x5e154 : word) = Some W_5e104.
Proof. vm_refl. Qed.
Lemma D_5e104 : decode_any W_5e104 = Some (Amo AMO_ADD AD false false 0 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e108 : bv 32 := 0x01840413.
Lemma F_5e108 : fetch_word Asan.M.loaded_segments (0x5e158 : word) = Some W_5e108.
Proof. vm_refl. Qed.
Lemma D_5e108 : decode_any W_5e108 = Some (OpImm ALU_ADD 8 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e10c : bv 32 := 0x0124302f.
Lemma F_5e10c : fetch_word Asan.M.loaded_segments (0x5e15c : word) = Some W_5e10c.
Proof. vm_refl. Qed.
Lemma D_5e10c : decode_any W_5e10c = Some (Amo AMO_ADD AD false false 0 8 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e110 : bv 32 := 0x0310000f.
Lemma F_5e110 : fetch_word Asan.M.loaded_segments (0x5e160 : word) = Some W_5e110.
Proof. vm_refl. Qed.
Lemma D_5e110 : decode_any W_5e110 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e114 : bv 32 := 0x26048423.
Lemma F_5e114 : fetch_word Asan.M.loaded_segments (0x5e164 : word) = Some W_5e114.
Proof. vm_refl. Qed.
Lemma D_5e114 : decode_any W_5e114 = Some (Store SZ1 9 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e118 : bv 32 := 0x05813083.
Lemma F_5e118 : fetch_word Asan.M.loaded_segments (0x5e168 : word) = Some W_5e118.
Proof. vm_refl. Qed.
Lemma D_5e118 : decode_any W_5e118 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e11c : bv 32 := 0x05013403.
Lemma F_5e11c : fetch_word Asan.M.loaded_segments (0x5e16c : word) = Some W_5e11c.
Proof. vm_refl. Qed.
Lemma D_5e11c : decode_any W_5e11c = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e120 : bv 32 := 0x04813483.
Lemma F_5e120 : fetch_word Asan.M.loaded_segments (0x5e170 : word) = Some W_5e120.
Proof. vm_refl. Qed.
Lemma D_5e120 : decode_any W_5e120 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e124 : bv 32 := 0x04013903.
Lemma F_5e124 : fetch_word Asan.M.loaded_segments (0x5e174 : word) = Some W_5e124.
Proof. vm_refl. Qed.
Lemma D_5e124 : decode_any W_5e124 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e128 : bv 32 := 0x03813983.
Lemma F_5e128 : fetch_word Asan.M.loaded_segments (0x5e178 : word) = Some W_5e128.
Proof. vm_refl. Qed.
Lemma D_5e128 : decode_any W_5e128 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e12c : bv 32 := 0x03013a03.
Lemma F_5e12c : fetch_word Asan.M.loaded_segments (0x5e17c : word) = Some W_5e12c.
Proof. vm_refl. Qed.
Lemma D_5e12c : decode_any W_5e12c = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e130 : bv 32 := 0x02813a83.
Lemma F_5e130 : fetch_word Asan.M.loaded_segments (0x5e180 : word) = Some W_5e130.
Proof. vm_refl. Qed.
Lemma D_5e130 : decode_any W_5e130 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e134 : bv 32 := 0x02013b03.
Lemma F_5e134 : fetch_word Asan.M.loaded_segments (0x5e184 : word) = Some W_5e134.
Proof. vm_refl. Qed.
Lemma D_5e134 : decode_any W_5e134 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e138 : bv 32 := 0x01813b83.
Lemma F_5e138 : fetch_word Asan.M.loaded_segments (0x5e188 : word) = Some W_5e138.
Proof. vm_refl. Qed.
Lemma D_5e138 : decode_any W_5e138 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e13c : bv 32 := 0x01013c03.
Lemma F_5e13c : fetch_word Asan.M.loaded_segments (0x5e18c : word) = Some W_5e13c.
Proof. vm_refl. Qed.
Lemma D_5e13c : decode_any W_5e13c = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e140 : bv 32 := 0x00813c83.
Lemma F_5e140 : fetch_word Asan.M.loaded_segments (0x5e190 : word) = Some W_5e140.
Proof. vm_refl. Qed.
Lemma D_5e140 : decode_any W_5e140 = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e144 : bv 32 := 0x06010113.
Lemma F_5e144 : fetch_word Asan.M.loaded_segments (0x5e194 : word) = Some W_5e144.
Proof. vm_refl. Qed.
Lemma D_5e144 : decode_any W_5e144 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e148 : bv 32 := 0x00008067.
Lemma F_5e148 : fetch_word Asan.M.loaded_segments (0x5e198 : word) = Some W_5e148.
Proof. vm_refl. Qed.
Lemma D_5e148 : decode_any W_5e148 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e274 : bv 32 := 0x0104b583.
Lemma F_5e274 : fetch_word Asan.M.loaded_segments (0x5e2c4 : word) = Some W_5e274.
Proof. vm_refl. Qed.
Lemma D_5e274 : decode_any W_5e274 = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e278 : bv 32 := 0x01048713.
Lemma F_5e278 : fetch_word Asan.M.loaded_segments (0x5e2c8 : word) = Some W_5e278.
Proof. vm_refl. Qed.
Lemma D_5e278 : decode_any W_5e278 = Some (OpImm ALU_ADD 14 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e27c : bv 32 := 0x00369693.
Lemma F_5e27c : fetch_word Asan.M.loaded_segments (0x5e2cc : word) = Some W_5e27c.
Proof. vm_refl. Qed.
Lemma D_5e27c : decode_any W_5e27c = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e280 : bv 32 := 0x00b685b3.
Lemma F_5e280 : fetch_word Asan.M.loaded_segments (0x5e2d0 : word) = Some W_5e280.
Proof. vm_refl. Qed.
Lemma D_5e280 : decode_any W_5e280 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e284 : bv 32 := 0x00020637.
Lemma F_5e284 : fetch_word Asan.M.loaded_segments (0x5e2d4 : word) = Some W_5e284.
Proof. vm_refl. Qed.
Lemma D_5e284 : decode_any W_5e284 = Some (Lui 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e288 : bv 32 := 0x00050a13.
Lemma F_5e288 : fetch_word Asan.M.loaded_segments (0x5e2d8 : word) = Some W_5e288.
Proof. vm_refl. Qed.
Lemma D_5e288 : decode_any W_5e288 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e28c : bv 32 := 0x00070513.
Lemma F_5e28c : fetch_word Asan.M.loaded_segments (0x5e2dc : word) = Some W_5e28c.
Proof. vm_refl. Qed.
Lemma D_5e28c : decode_any W_5e28c = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e290 : bv 32 := 0x00000693.
Lemma F_5e290 : fetch_word Asan.M.loaded_segments (0x5e2e0 : word) = Some W_5e290.
Proof. vm_refl. Qed.
Lemma D_5e290 : decode_any W_5e290 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e294 : bv 32 := 0x4153e0ef.
Lemma F_5e294 : fetch_word Asan.M.loaded_segments (0x5e2e4 : word) = Some W_5e294.
Proof. vm_refl. Qed.
Lemma D_5e294 : decode_any W_5e294 = Some (Jal 1 257044, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e298 : bv 32 := 0x000a0513.
Lemma F_5e298 : fetch_word Asan.M.loaded_segments (0x5e2e8 : word) = Some W_5e298.
Proof. vm_refl. Qed.
Lemma D_5e298 : decode_any W_5e298 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e29c : bv 32 := 0x0304b583.
Lemma F_5e29c : fetch_word Asan.M.loaded_segments (0x5e2ec : word) = Some W_5e29c.
Proof. vm_refl. Qed.
Lemma D_5e29c : decode_any W_5e29c = Some (Load SZ8 true 11 9 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2a0 : bv 32 := 0x0384b683.
Lemma F_5e2a0 : fetch_word Asan.M.loaded_segments (0x5e2f0 : word) = Some W_5e2a0.
Proof. vm_refl. Qed.
Lemma D_5e2a0 : decode_any W_5e2a0 = Some (Load SZ8 true 13 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2a4 : bv 32 := 0x00004637.
Lemma F_5e2a4 : fetch_word Asan.M.loaded_segments (0x5e2f4 : word) = Some W_5e2a4.
Proof. vm_refl. Qed.
Lemma D_5e2a4 : decode_any W_5e2a4 = Some (Lui 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2a8 : bv 32 := 0x00c585b3.
Lemma F_5e2a8 : fetch_word Asan.M.loaded_segments (0x5e2f8 : word) = Some W_5e2a8.
Proof. vm_refl. Qed.
Lemma D_5e2a8 : decode_any W_5e2a8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2ac : bv 32 := 0x02b4b823.
Lemma F_5e2ac : fetch_word Asan.M.loaded_segments (0x5e2fc : word) = Some W_5e2ac.
Proof. vm_refl. Qed.
Lemma D_5e2ac : decode_any W_5e2ac = Some (Store SZ8 9 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2b0 : bv 32 := 0xdf1ff06f.
Lemma F_5e2b0 : fetch_word Asan.M.loaded_segments (0x5e300 : word) = Some W_5e2b0.
Proof. vm_refl. Qed.
Lemma D_5e2b0 : decode_any W_5e2b0 = Some (Jal 0 2096624, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2b4 : bv 32 := 0xfe010113.
Lemma F_5e2b4 : fetch_word Asan.M.loaded_segments (0x5e304 : word) = Some W_5e2b4.
Proof. vm_refl. Qed.
Lemma D_5e2b4 : decode_any W_5e2b4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2b8 : bv 32 := 0x00113c23.
Lemma F_5e2b8 : fetch_word Asan.M.loaded_segments (0x5e308 : word) = Some W_5e2b8.
Proof. vm_refl. Qed.
Lemma D_5e2b8 : decode_any W_5e2b8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2bc : bv 32 := 0x00813823.
Lemma F_5e2bc : fetch_word Asan.M.loaded_segments (0x5e30c : word) = Some W_5e2bc.
Proof. vm_refl. Qed.
Lemma D_5e2bc : decode_any W_5e2bc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2c0 : bv 32 := 0x00913423.
Lemma F_5e2c0 : fetch_word Asan.M.loaded_segments (0x5e310 : word) = Some W_5e2c0.
Proof. vm_refl. Qed.
Lemma D_5e2c0 : decode_any W_5e2c0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2c4 : bv 32 := 0x00068713.
Lemma F_5e2c4 : fetch_word Asan.M.loaded_segments (0x5e314 : word) = Some W_5e2c4.
Proof. vm_refl. Qed.
Lemma D_5e2c4 : decode_any W_5e2c4 = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2c8 : bv 32 := 0x00058413.
Lemma F_5e2c8 : fetch_word Asan.M.loaded_segments (0x5e318 : word) = Some W_5e2c8.
Proof. vm_refl. Qed.
Lemma D_5e2c8 : decode_any W_5e2c8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2cc : bv 32 := 0x0045a583.
Lemma F_5e2cc : fetch_word Asan.M.loaded_segments (0x5e31c : word) = Some W_5e2cc.
Proof. vm_refl. Qed.
Lemma D_5e2cc : decode_any W_5e2cc = Some (Load SZ4 true 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2d0 : bv 32 := 0x04058063.
Lemma F_5e2d0 : fetch_word Asan.M.loaded_segments (0x5e320 : word) = Some W_5e2d0.
Proof. vm_refl. Qed.
Lemma D_5e2d0 : decode_any W_5e2d0 = Some (Branch BC_EQ 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2d4 : bv 32 := 0x0015d49b.
Lemma F_5e2d4 : fetch_word Asan.M.loaded_segments (0x5e324 : word) = Some W_5e2d4.
Proof. vm_refl. Qed.
Lemma D_5e2d4 : decode_any W_5e2d4 = Some (ShiftImm32 ALU_SRL 9 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2d8 : bv 32 := 0x7ff50513.
Lemma F_5e2d8 : fetch_word Asan.M.loaded_segments (0x5e328 : word) = Some W_5e2d8.
Proof. vm_refl. Qed.
Lemma D_5e2d8 : decode_any W_5e2d8 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2dc : bv 32 := 0x20150593.
Lemma F_5e2dc : fetch_word Asan.M.loaded_segments (0x5e32c : word) = Some W_5e2dc.
Proof. vm_refl. Qed.
Lemma D_5e2dc : decode_any W_5e2dc = Some (OpImm ALU_ADD 11 10 513, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2e0 : bv 32 := 0x01040693.
Lemma F_5e2e0 : fetch_word Asan.M.loaded_segments (0x5e330 : word) = Some W_5e2e0.
Proof. vm_refl. Qed.
Lemma D_5e2e0 : decode_any W_5e2e0 = Some (OpImm ALU_ADD 13 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2e4 : bv 32 := 0x00060513.
Lemma F_5e2e4 : fetch_word Asan.M.loaded_segments (0x5e334 : word) = Some W_5e2e4.
Proof. vm_refl. Qed.
Lemma D_5e2e4 : decode_any W_5e2e4 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2e8 : bv 32 := 0x00070613.
Lemma F_5e2e8 : fetch_word Asan.M.loaded_segments (0x5e338 : word) = Some W_5e2e8.
Proof. vm_refl. Qed.
Lemma D_5e2e8 : decode_any W_5e2e8 = Some (OpImm ALU_ADD 12 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2ec : bv 32 := 0x00048713.
Lemma F_5e2ec : fetch_word Asan.M.loaded_segments (0x5e33c : word) = Some W_5e2ec.
Proof. vm_refl. Qed.
Lemma D_5e2ec : decode_any W_5e2ec = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2f0 : bv 32 := 0x0c4000ef.
Lemma F_5e2f0 : fetch_word Asan.M.loaded_segments (0x5e340 : word) = Some W_5e2f0.
Proof. vm_refl. Qed.
Lemma D_5e2f0 : decode_any W_5e2f0 = Some (Jal 1 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2f4 : bv 32 := 0x00050463.
Lemma F_5e2f4 : fetch_word Asan.M.loaded_segments (0x5e344 : word) = Some W_5e2f4.
Proof. vm_refl. Qed.
Lemma D_5e2f4 : decode_any W_5e2f4 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2f8 : bv 32 := 0x00942023.
Lemma F_5e2f8 : fetch_word Asan.M.loaded_segments (0x5e348 : word) = Some W_5e2f8.
Proof. vm_refl. Qed.
Lemma D_5e2f8 : decode_any W_5e2f8 = Some (Store SZ4 8 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2fc : bv 32 := 0x01813083.
Lemma F_5e2fc : fetch_word Asan.M.loaded_segments (0x5e34c : word) = Some W_5e2fc.
Proof. vm_refl. Qed.
Lemma D_5e2fc : decode_any W_5e2fc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e300 : bv 32 := 0x01013403.
Lemma F_5e300 : fetch_word Asan.M.loaded_segments (0x5e350 : word) = Some W_5e300.
Proof. vm_refl. Qed.
Lemma D_5e300 : decode_any W_5e300 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e304 : bv 32 := 0x00813483.
Lemma F_5e304 : fetch_word Asan.M.loaded_segments (0x5e354 : word) = Some W_5e304.
Proof. vm_refl. Qed.
Lemma D_5e304 : decode_any W_5e304 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e308 : bv 32 := 0x02010113.
Lemma F_5e308 : fetch_word Asan.M.loaded_segments (0x5e358 : word) = Some W_5e308.
Proof. vm_refl. Qed.
Lemma D_5e308 : decode_any W_5e308 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e30c : bv 32 := 0x00008067.
Lemma F_5e30c : fetch_word Asan.M.loaded_segments (0x5e35c : word) = Some W_5e30c.
Proof. vm_refl. Qed.
Lemma D_5e30c : decode_any W_5e30c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e310 : bv 32 := 0x05850593.
Lemma F_5e310 : fetch_word Asan.M.loaded_segments (0x5e360 : word) = Some W_5e310.
Proof. vm_refl. Qed.
Lemma D_5e310 : decode_any W_5e310 = Some (OpImm ALU_ADD 11 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e314 : bv 32 := 0x02000693.
Lemma F_5e314 : fetch_word Asan.M.loaded_segments (0x5e364 : word) = Some W_5e314.
Proof. vm_refl. Qed.
Lemma D_5e314 : decode_any W_5e314 = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e318 : bv 32 := 0xff100793.
Lemma F_5e318 : fetch_word Asan.M.loaded_segments (0x5e368 : word) = Some W_5e318.
Proof. vm_refl. Qed.
Lemma D_5e318 : decode_any W_5e318 = Some (OpImm ALU_ADD 15 0 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e31c : bv 32 := 0x00f00813.
Lemma F_5e31c : fetch_word Asan.M.loaded_segments (0x5e36c : word) = Some W_5e31c.
Proof. vm_refl. Qed.
Lemma D_5e31c : decode_any W_5e31c = Some (OpImm ALU_ADD 16 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e320 : bv 32 := 0x40000893.
Lemma F_5e320 : fetch_word Asan.M.loaded_segments (0x5e370 : word) = Some W_5e320.
Proof. vm_refl. Qed.
Lemma D_5e320 : decode_any W_5e320 = Some (OpImm ALU_ADD 17 0 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e324 : bv 32 := 0x01000293.
Lemma F_5e324 : fetch_word Asan.M.loaded_segments (0x5e374 : word) = Some W_5e324.
Proof. vm_refl. Qed.
Lemma D_5e324 : decode_any W_5e324 = Some (OpImm ALU_ADD 5 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e328 : bv 32 := 0x01100313.
Lemma F_5e328 : fetch_word Asan.M.loaded_segments (0x5e378 : word) = Some W_5e328.
Proof. vm_refl. Qed.
Lemma D_5e328 : decode_any W_5e328 = Some (OpImm ALU_ADD 6 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e32c : bv 32 := 0x20000393.
Lemma F_5e32c : fetch_word Asan.M.loaded_segments (0x5e37c : word) = Some W_5e32c.
Proof. vm_refl. Qed.
Lemma D_5e32c : decode_any W_5e32c = Some (OpImm ALU_ADD 7 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e330 : bv 32 := 0x0280006f.
Lemma F_5e330 : fetch_word Asan.M.loaded_segments (0x5e380 : word) = Some W_5e330.
Proof. vm_refl. Qed.
Lemma D_5e330 : decode_any W_5e330 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e334 : bv 32 := 0x001ebf13.
Lemma F_5e334 : fetch_word Asan.M.loaded_segments (0x5e384 : word) = Some W_5e334.
Proof. vm_refl. Qed.
Lemma D_5e334 : decode_any W_5e334 = Some (OpImm ALU_SLTU 30 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e338 : bv 32 := 0x02068693.
Lemma F_5e338 : fetch_word Asan.M.loaded_segments (0x5e388 : word) = Some W_5e338.
Proof. vm_refl. Qed.
Lemma D_5e338 : decode_any W_5e338 = Some (OpImm ALU_ADD 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e33c : bv 32 := 0x00178793.
Lemma F_5e33c : fetch_word Asan.M.loaded_segments (0x5e38c : word) = Some W_5e33c.
Proof. vm_refl. Qed.
Lemma D_5e33c : decode_any W_5e33c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e340 : bv 32 := 0x01ee8eb3.
Lemma F_5e340 : fetch_word Asan.M.loaded_segments (0x5e390 : word) = Some W_5e340.
Proof. vm_refl. Qed.
Lemma D_5e340 : decode_any W_5e340 = Some (Op ALU_ADD 29 29 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e344 : bv 32 := 0x001e9e93.
Lemma F_5e344 : fetch_word Asan.M.loaded_segments (0x5e394 : word) = Some W_5e344.
Proof. vm_refl. Qed.
Lemma D_5e344 : decode_any W_5e344 = Some (ShiftImm ALU_SLL 29 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e348 : bv 32 := 0xffd5ae23.
Lemma F_5e348 : fetch_word Asan.M.loaded_segments (0x5e398 : word) = Some W_5e348.
Proof. vm_refl. Qed.
Lemma D_5e348 : decode_any W_5e348 = Some (Store SZ4 11 29 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e34c : bv 32 := 0x01c5b023.
Lemma F_5e34c : fetch_word Asan.M.loaded_segments (0x5e39c : word) = Some W_5e34c.
Proof. vm_refl. Qed.
Lemma D_5e34c : decode_any W_5e34c = Some (Store SZ8 11 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e350 : bv 32 := 0x05058593.
Lemma F_5e350 : fetch_word Asan.M.loaded_segments (0x5e3a0 : word) = Some W_5e350.
Proof. vm_refl. Qed.
Lemma D_5e350 : decode_any W_5e350 = Some (OpImm ALU_ADD 11 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e354 : bv 32 := 0x04578c63.
Lemma F_5e354 : fetch_word Asan.M.loaded_segments (0x5e3a4 : word) = Some W_5e354.
Proof. vm_refl. Qed.
Lemma D_5e354 : decode_any W_5e354 = Some (Branch BC_EQ 15 5 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e358 : bv 32 := 0x05078063.
Lemma F_5e358 : fetch_word Asan.M.loaded_segments (0x5e3a8 : word) = Some W_5e358.
Proof. vm_refl. Qed.
Lemma D_5e358 : decode_any W_5e358 = Some (Branch BC_EQ 15 16 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e35c : bv 32 := 0x01078e93.
Lemma F_5e35c : fetch_word Asan.M.loaded_segments (0x5e3ac : word) = Some W_5e35c.
Proof. vm_refl. Qed.
Lemma D_5e35c : decode_any W_5e35c = Some (OpImm ALU_ADD 29 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e360 : bv 32 := 0x00068e13.
Lemma F_5e360 : fetch_word Asan.M.loaded_segments (0x5e3b0 : word) = Some W_5e360.
Proof. vm_refl. Qed.
Lemma D_5e360 : decode_any W_5e360 = Some (OpImm ALU_ADD 28 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e364 : bv 32 := 0x026ee063.
Lemma F_5e364 : fetch_word Asan.M.loaded_segments (0x5e3b4 : word) = Some W_5e364.
Proof. vm_refl. Qed.
Lemma D_5e364 : decode_any W_5e364 = Some (Branch BC_LTU 29 6 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e368 : bv 32 := 0x0017de13.
Lemma F_5e368 : fetch_word Asan.M.loaded_segments (0x5e3b8 : word) = Some W_5e368.
Proof. vm_refl. Qed.
Lemma D_5e368 : decode_any W_5e368 = Some (ShiftImm ALU_SRL 28 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e36c : bv 32 := 0x03fe9e93.
Lemma F_5e36c : fetch_word Asan.M.loaded_segments (0x5e3bc : word) = Some W_5e36c.
Proof. vm_refl. Qed.
Lemma D_5e36c : decode_any W_5e36c = Some (ShiftImm ALU_SLL 29 29 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e370 : bv 32 := 0x01c39e33.
Lemma F_5e370 : fetch_word Asan.M.loaded_segments (0x5e3c0 : word) = Some W_5e370.
Proof. vm_refl. Qed.
Lemma D_5e370 : decode_any W_5e370 = Some (Op ALU_SLL 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e374 : bv 32 := 0x001e5f13.
Lemma F_5e374 : fetch_word Asan.M.loaded_segments (0x5e3c4 : word) = Some W_5e374.
Proof. vm_refl. Qed.
Lemma D_5e374 : decode_any W_5e374 = Some (ShiftImm ALU_SRL 30 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e378 : bv 32 := 0x43fede93.
Lemma F_5e378 : fetch_word Asan.M.loaded_segments (0x5e3c8 : word) = Some W_5e378.
Proof. vm_refl. Qed.
Lemma D_5e378 : decode_any W_5e378 = Some (ShiftImm ALU_SRA 29 29 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e37c : bv 32 := 0x01eefeb3.
Lemma F_5e37c : fetch_word Asan.M.loaded_segments (0x5e3cc : word) = Some W_5e37c.
Proof. vm_refl. Qed.
Lemma D_5e37c : decode_any W_5e37c = Some (Op ALU_AND 29 29 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e380 : bv 32 := 0x01ce8e33.
Lemma F_5e380 : fetch_word Asan.M.loaded_segments (0x5e3d0 : word) = Some W_5e380.
Proof. vm_refl. Qed.
Lemma D_5e380 : decode_any W_5e380 = Some (Op ALU_ADD 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e384 : bv 32 := 0x03c8debb.
Lemma F_5e384 : fetch_word Asan.M.loaded_segments (0x5e3d4 : word) = Some W_5e384.
Proof. vm_refl. Qed.
Lemma D_5e384 : decode_any W_5e384 = Some (Mul32 M_DIVU 29 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e388 : bv 32 := 0x00800f13.
Lemma F_5e388 : fetch_word Asan.M.loaded_segments (0x5e3d8 : word) = Some W_5e388.
Proof. vm_refl. Qed.
Lemma D_5e388 : decode_any W_5e388 = Some (OpImm ALU_ADD 30 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e38c : bv 32 := 0xfbeee4e3.
Lemma F_5e38c : fetch_word Asan.M.loaded_segments (0x5e3dc : word) = Some W_5e38c.
Proof. vm_refl. Qed.
Lemma D_5e38c : decode_any W_5e38c = Some (Branch BC_LTU 29 30 8104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e390 : bv 32 := 0x00800e93.
Lemma F_5e390 : fetch_word Asan.M.loaded_segments (0x5e3e0 : word) = Some W_5e390.
Proof. vm_refl. Qed.
Lemma D_5e390 : decode_any W_5e390 = Some (OpImm ALU_ADD 29 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e394 : bv 32 := 0xfa1ff06f.
Lemma F_5e394 : fetch_word Asan.M.loaded_segments (0x5e3e4 : word) = Some W_5e394.
Proof. vm_refl. Qed.
Lemma D_5e394 : decode_any W_5e394 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e398 : bv 32 := 0x04000e13.
Lemma F_5e398 : fetch_word Asan.M.loaded_segments (0x5e3e8 : word) = Some W_5e398.
Proof. vm_refl. Qed.
Lemma D_5e398 : decode_any W_5e398 = Some (OpImm ALU_ADD 28 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e39c : bv 32 := 0x03c8debb.
Lemma F_5e39c : fetch_word Asan.M.loaded_segments (0x5e3ec : word) = Some W_5e39c.
Proof. vm_refl. Qed.
Lemma D_5e39c : decode_any W_5e39c = Some (Mul32 M_DIVU 29 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a0 : bv 32 := 0x00800f13.
Lemma F_5e3a0 : fetch_word Asan.M.loaded_segments (0x5e3f0 : word) = Some W_5e3a0.
Proof. vm_refl. Qed.
Lemma D_5e3a0 : decode_any W_5e3a0 = Some (OpImm ALU_ADD 30 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a4 : bv 32 := 0xf9eee8e3.
Lemma F_5e3a4 : fetch_word Asan.M.loaded_segments (0x5e3f4 : word) = Some W_5e3a4.
Proof. vm_refl. Qed.
Lemma D_5e3a4 : decode_any W_5e3a4 = Some (Branch BC_LTU 29 30 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a8 : bv 32 := 0xfe9ff06f.
Lemma F_5e3a8 : fetch_word Asan.M.loaded_segments (0x5e3f8 : word) = Some W_5e3a8.
Proof. vm_refl. Qed.
Lemma D_5e3a8 : decode_any W_5e3a8 = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3ac : bv 32 := 0x00442583.
Lemma F_5e3ac : fetch_word Asan.M.loaded_segments (0x5e3fc : word) = Some W_5e3ac.
Proof. vm_refl. Qed.
Lemma D_5e3ac : decode_any W_5e3ac = Some (Load SZ4 true 11 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b0 : bv 32 := 0xf25ff06f.
Lemma F_5e3b0 : fetch_word Asan.M.loaded_segments (0x5e400 : word) = Some W_5e3b0.
Proof. vm_refl. Qed.
Lemma D_5e3b0 : decode_any W_5e3b0 = Some (Jal 0 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b4 : bv 32 := 0xf8010113.
Lemma F_5e3b4 : fetch_word Asan.M.loaded_segments (0x5e404 : word) = Some W_5e3b4.
Proof. vm_refl. Qed.
Lemma D_5e3b4 : decode_any W_5e3b4 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b8 : bv 32 := 0x06113c23.
Lemma F_5e3b8 : fetch_word Asan.M.loaded_segments (0x5e408 : word) = Some W_5e3b8.
Proof. vm_refl. Qed.
Lemma D_5e3b8 : decode_any W_5e3b8 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3bc : bv 32 := 0x06813823.
Lemma F_5e3bc : fetch_word Asan.M.loaded_segments (0x5e40c : word) = Some W_5e3bc.
Proof. vm_refl. Qed.
Lemma D_5e3bc : decode_any W_5e3bc = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c0 : bv 32 := 0x06913423.
Lemma F_5e3c0 : fetch_word Asan.M.loaded_segments (0x5e410 : word) = Some W_5e3c0.
Proof. vm_refl. Qed.
Lemma D_5e3c0 : decode_any W_5e3c0 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c4 : bv 32 := 0x07213023.
Lemma F_5e3c4 : fetch_word Asan.M.loaded_segments (0x5e414 : word) = Some W_5e3c4.
Proof. vm_refl. Qed.
Lemma D_5e3c4 : decode_any W_5e3c4 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c8 : bv 32 := 0x05313c23.
Lemma F_5e3c8 : fetch_word Asan.M.loaded_segments (0x5e418 : word) = Some W_5e3c8.
Proof. vm_refl. Qed.
Lemma D_5e3c8 : decode_any W_5e3c8 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3cc : bv 32 := 0x05413823.
Lemma F_5e3cc : fetch_word Asan.M.loaded_segments (0x5e41c : word) = Some W_5e3cc.
Proof. vm_refl. Qed.
Lemma D_5e3cc : decode_any W_5e3cc = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d0 : bv 32 := 0x05513423.
Lemma F_5e3d0 : fetch_word Asan.M.loaded_segments (0x5e420 : word) = Some W_5e3d0.
Proof. vm_refl. Qed.
Lemma D_5e3d0 : decode_any W_5e3d0 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d4 : bv 32 := 0x05613023.
Lemma F_5e3d4 : fetch_word Asan.M.loaded_segments (0x5e424 : word) = Some W_5e3d4.
Proof. vm_refl. Qed.
Lemma D_5e3d4 : decode_any W_5e3d4 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d8 : bv 32 := 0x03713c23.
Lemma F_5e3d8 : fetch_word Asan.M.loaded_segments (0x5e428 : word) = Some W_5e3d8.
Proof. vm_refl. Qed.
Lemma D_5e3d8 : decode_any W_5e3d8 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3dc : bv 32 := 0x03813823.
Lemma F_5e3dc : fetch_word Asan.M.loaded_segments (0x5e42c : word) = Some W_5e3dc.
Proof. vm_refl. Qed.
Lemma D_5e3dc : decode_any W_5e3dc = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e0 : bv 32 := 0x03913423.
Lemma F_5e3e0 : fetch_word Asan.M.loaded_segments (0x5e430 : word) = Some W_5e3e0.
Proof. vm_refl. Qed.
Lemma D_5e3e0 : decode_any W_5e3e0 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e4 : bv 32 := 0x03a13023.
Lemma F_5e3e4 : fetch_word Asan.M.loaded_segments (0x5e434 : word) = Some W_5e3e4.
Proof. vm_refl. Qed.
Lemma D_5e3e4 : decode_any W_5e3e4 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e8 : bv 32 := 0x01b13c23.
Lemma F_5e3e8 : fetch_word Asan.M.loaded_segments (0x5e438 : word) = Some W_5e3e8.
Proof. vm_refl. Qed.
Lemma D_5e3e8 : decode_any W_5e3e8 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3ec : bv 32 := 0x00050493.
Lemma F_5e3ec : fetch_word Asan.M.loaded_segments (0x5e43c : word) = Some W_5e3ec.
Proof. vm_refl. Qed.
Lemma D_5e3ec : decode_any W_5e3ec = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f0 : bv 32 := 0x00000793.
Lemma F_5e3f0 : fetch_word Asan.M.loaded_segments (0x5e440 : word) = Some W_5e3f0.
Proof. vm_refl. Qed.
Lemma D_5e3f0 : decode_any W_5e3f0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f4 : bv 32 := 0x00100b93.
Lemma F_5e3f4 : fetch_word Asan.M.loaded_segments (0x5e444 : word) = Some W_5e3f4.
Proof. vm_refl. Qed.
Lemma D_5e3f4 : decode_any W_5e3f4 = Some (OpImm ALU_ADD 23 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f8 : bv 32 := 0x02053a03.
Lemma F_5e3f8 : fetch_word Asan.M.loaded_segments (0x5e448 : word) = Some W_5e3f8.
Proof. vm_refl. Qed.
Lemma D_5e3f8 : decode_any W_5e3f8 = Some (Load SZ8 true 20 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3fc : bv 32 := 0x03053403.
Lemma F_5e3fc : fetch_word Asan.M.loaded_segments (0x5e44c : word) = Some W_5e3fc.
Proof. vm_refl. Qed.
Lemma D_5e3fc : decode_any W_5e3fc = Some (Load SZ8 true 8 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e400 : bv 32 := 0x00761513.
Lemma F_5e400 : fetch_word Asan.M.loaded_segments (0x5e450 : word) = Some W_5e400.
Proof. vm_refl. Qed.
Lemma D_5e400 : decode_any W_5e400 = Some (ShiftImm ALU_SLL 10 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e404 : bv 32 := 0x02061893.
Lemma F_5e404 : fetch_word Asan.M.loaded_segments (0x5e454 : word) = Some W_5e404.
Proof. vm_refl. Qed.
Lemma D_5e404 : decode_any W_5e404 = Some (ShiftImm ALU_SLL 17 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e408 : bv 32 := 0x00700293.
Lemma F_5e408 : fetch_word Asan.M.loaded_segments (0x5e458 : word) = Some W_5e408.
Proof. vm_refl. Qed.
Lemma D_5e408 : decode_any W_5e408 = Some (OpImm ALU_ADD 5 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e40c : bv 32 := 0xfff00813.
Lemma F_5e40c : fetch_word Asan.M.loaded_segments (0x5e45c : word) = Some W_5e40c.
Proof. vm_refl. Qed.
Lemma D_5e40c : decode_any W_5e40c = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e410 : bv 32 := 0x03db9993.
Lemma F_5e410 : fetch_word Asan.M.loaded_segments (0x5e460 : word) = Some W_5e410.
Proof. vm_refl. Qed.
Lemma D_5e410 : decode_any W_5e410 = Some (ShiftImm ALU_SLL 19 23 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e414 : bv 32 := 0x01d29293.
Lemma F_5e414 : fetch_word Asan.M.loaded_segments (0x5e464 : word) = Some W_5e414.
Proof. vm_refl. Qed.
Lemma D_5e414 : decode_any W_5e414 = Some (ShiftImm ALU_SLL 5 5 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e418 : bv 32 := 0x028b9a93.
Lemma F_5e418 : fetch_word Asan.M.loaded_segments (0x5e468 : word) = Some W_5e418.
Proof. vm_refl. Qed.
Lemma D_5e418 : decode_any W_5e418 = Some (ShiftImm ALU_SLL 21 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e41c : bv 32 := 0x005888b3.
Lemma F_5e41c : fetch_word Asan.M.loaded_segments (0x5e46c : word) = Some W_5e41c.
Proof. vm_refl. Qed.
Lemma D_5e41c : decode_any W_5e41c = Some (Op ALU_ADD 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e420 : bv 32 := 0x001a8293.
Lemma F_5e420 : fetch_word Asan.M.loaded_segments (0x5e470 : word) = Some W_5e420.
Proof. vm_refl. Qed.
Lemma D_5e420 : decode_any W_5e420 = Some (OpImm ALU_ADD 5 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e424 : bv 32 := 0x01429293.
Lemma F_5e424 : fetch_word Asan.M.loaded_segments (0x5e474 : word) = Some W_5e424.
Proof. vm_refl. Qed.
Lemma D_5e424 : decode_any W_5e424 = Some (ShiftImm ALU_SLL 5 5 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e428 : bv 32 := 0x00a40433.
Lemma F_5e428 : fetch_word Asan.M.loaded_segments (0x5e478 : word) = Some W_5e428.
Proof. vm_refl. Qed.
Lemma D_5e428 : decode_any W_5e428 = Some (Op ALU_ADD 8 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e42c : bv 32 := 0x011a0a33.
Lemma F_5e42c : fetch_word Asan.M.loaded_segments (0x5e47c : word) = Some W_5e42c.
Proof. vm_refl. Qed.
Lemma D_5e42c : decode_any W_5e42c = Some (Op ALU_ADD 20 20 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e430 : bv 32 := 0xfff28b13.
Lemma F_5e430 : fetch_word Asan.M.loaded_segments (0x5e480 : word) = Some W_5e430.
Proof. vm_refl. Qed.
Lemma D_5e430 : decode_any W_5e430 = Some (OpImm ALU_ADD 22 5 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e434 : bv 32 := 0x00043883.
Lemma F_5e434 : fetch_word Asan.M.loaded_segments (0x5e484 : word) = Some W_5e434.
Proof. vm_refl. Qed.
Lemma D_5e434 : decode_any W_5e434 = Some (Load SZ8 true 17 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e438 : bv 32 := 0x00840513.
Lemma F_5e438 : fetch_word Asan.M.loaded_segments (0x5e488 : word) = Some W_5e438.
Proof. vm_refl. Qed.
Lemma D_5e438 : decode_any W_5e438 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e43c : bv 32 := 0x03cb9b93.
Lemma F_5e43c : fetch_word Asan.M.loaded_segments (0x5e48c : word) = Some W_5e43c.
Proof. vm_refl. Qed.
Lemma D_5e43c : decode_any W_5e43c = Some (ShiftImm ALU_SLL 23 23 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e440 : bv 32 := 0x5dc00c13.
Lemma F_5e440 : fetch_word Asan.M.loaded_segments (0x5e490 : word) = Some W_5e440.
Proof. vm_refl. Qed.
Lemma D_5e440 : decode_any W_5e440 = Some (OpImm ALU_ADD 24 0 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e444 : bv 32 := 0x03d81c93.
Lemma F_5e444 : fetch_word Asan.M.loaded_segments (0x5e494 : word) = Some W_5e444.
Proof. vm_refl. Qed.
Lemma D_5e444 : decode_any W_5e444 = Some (ShiftImm ALU_SLL 25 16 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e448 : bv 32 := 0xfffc8c93.
Lemma F_5e448 : fetch_word Asan.M.loaded_segments (0x5e498 : word) = Some W_5e448.
Proof. vm_refl. Qed.
Lemma D_5e448 : decode_any W_5e448 = Some (OpImm ALU_ADD 25 25 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e44c : bv 32 := 0x0168f2b3.
Lemma F_5e44c : fetch_word Asan.M.loaded_segments (0x5e49c : word) = Some W_5e44c.
Proof. vm_refl. Qed.
Lemma D_5e44c : decode_any W_5e44c = Some (Op ALU_AND 5 17 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e450 : bv 32 := 0x02029663.
Lemma F_5e450 : fetch_word Asan.M.loaded_segments (0x5e4a0 : word) = Some W_5e450.
Proof. vm_refl. Qed.
Lemma D_5e450 : decode_any W_5e450 = Some (Branch BC_NE 5 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e454 : bv 32 := 0x0178e2b3.
Lemma F_5e454 : fetch_word Asan.M.loaded_segments (0x5e4a4 : word) = Some W_5e454.
Proof. vm_refl. Qed.
Lemma D_5e454 : decode_any W_5e454 = Some (Op ALU_OR 5 17 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e458 : bv 32 := 0x00587333.
Lemma F_5e458 : fetch_word Asan.M.loaded_segments (0x5e4a8 : word) = Some W_5e458.
Proof. vm_refl. Qed.
Lemma D_5e458 : decode_any W_5e458 = Some (Op ALU_AND 6 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e45c : bv 32 := 0x160432af.
Lemma F_5e45c : fetch_word Asan.M.loaded_segments (0x5e4ac : word) = Some W_5e45c.
Proof. vm_refl. Qed.
Lemma D_5e45c : decode_any W_5e45c = Some (Lr AD true true 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e460 : bv 32 := 0x01129663.
Lemma F_5e460 : fetch_word Asan.M.loaded_segments (0x5e4b0 : word) = Some W_5e460.
Proof. vm_refl. Qed.
Lemma D_5e460 : decode_any W_5e460 = Some (Branch BC_NE 5 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e464 : bv 32 := 0x1a6433af.
Lemma F_5e464 : fetch_word Asan.M.loaded_segments (0x5e4b4 : word) = Some W_5e464.
Proof. vm_refl. Qed.
Lemma D_5e464 : decode_any W_5e464 = Some (Sc AD false true 7 8 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e468 : bv 32 := 0xfe039ae3.
Lemma F_5e468 : fetch_word Asan.M.loaded_segments (0x5e4b8 : word) = Some W_5e468.
Proof. vm_refl. Qed.
Lemma D_5e468 : decode_any W_5e468 = Some (Branch BC_NE 7 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e46c : bv 32 := 0x09128c63.
Lemma F_5e46c : fetch_word Asan.M.loaded_segments (0x5e4bc : word) = Some W_5e46c.
Proof. vm_refl. Qed.
Lemma D_5e46c : decode_any W_5e46c = Some (Branch BC_EQ 5 17 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e504 : bv 32 := 0x01043783.
Lemma F_5e504 : fetch_word Asan.M.loaded_segments (0x5e554 : word) = Some W_5e504.
Proof. vm_refl. Qed.
Lemma D_5e504 : decode_any W_5e504 = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e508 : bv 32 := 0x14e7e663.
Lemma F_5e508 : fetch_word Asan.M.loaded_segments (0x5e558 : word) = Some W_5e508.
Proof. vm_refl. Qed.
Lemma D_5e508 : decode_any W_5e508 = Some (Branch BC_LTU 15 14 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e50c : bv 32 := 0x40e787b3.
Lemma F_5e50c : fetch_word Asan.M.loaded_segments (0x5e55c : word) = Some W_5e50c.
Proof. vm_refl. Qed.
Lemma D_5e50c : decode_any W_5e50c = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e510 : bv 32 := 0x00f43823.
Lemma F_5e510 : fetch_word Asan.M.loaded_segments (0x5e560 : word) = Some W_5e510.
Proof. vm_refl. Qed.
Lemma D_5e510 : decode_any W_5e510 = Some (Store SZ8 8 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e514 : bv 32 := 0x02070463.
Lemma F_5e514 : fetch_word Asan.M.loaded_segments (0x5e564 : word) = Some W_5e514.
Proof. vm_refl. Qed.
Lemma D_5e514 : decode_any W_5e514 = Some (Branch BC_EQ 14 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e518 : bv 32 := 0x00279793.
Lemma F_5e518 : fetch_word Asan.M.loaded_segments (0x5e568 : word) = Some W_5e518.
Proof. vm_refl. Qed.
Lemma D_5e518 : decode_any W_5e518 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e51c : bv 32 := 0x00fa0a33.
Lemma F_5e51c : fetch_word Asan.M.loaded_segments (0x5e56c : word) = Some W_5e51c.
Proof. vm_refl. Qed.
Lemma D_5e51c : decode_any W_5e51c = Some (Op ALU_ADD 20 20 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e520 : bv 32 := 0x00271593.
Lemma F_5e520 : fetch_word Asan.M.loaded_segments (0x5e570 : word) = Some W_5e520.
Proof. vm_refl. Qed.
Lemma D_5e520 : decode_any W_5e520 = Some (ShiftImm ALU_SLL 11 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e524 : bv 32 := 0x00b685b3.
Lemma F_5e524 : fetch_word Asan.M.loaded_segments (0x5e574 : word) = Some W_5e524.
Proof. vm_refl. Qed.
Lemma D_5e524 : decode_any W_5e524 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e528 : bv 32 := 0x000a2603.
Lemma F_5e528 : fetch_word Asan.M.loaded_segments (0x5e578 : word) = Some W_5e528.
Proof. vm_refl. Qed.
Lemma D_5e528 : decode_any W_5e528 = Some (Load SZ4 true 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e52c : bv 32 := 0x00c6a023.
Lemma F_5e52c : fetch_word Asan.M.loaded_segments (0x5e57c : word) = Some W_5e52c.
Proof. vm_refl. Qed.
Lemma D_5e52c : decode_any W_5e52c = Some (Store SZ4 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e530 : bv 32 := 0x00468693.
Lemma F_5e530 : fetch_word Asan.M.loaded_segments (0x5e580 : word) = Some W_5e530.
Proof. vm_refl. Qed.
Lemma D_5e530 : decode_any W_5e530 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e534 : bv 32 := 0x004a0a13.
Lemma F_5e534 : fetch_word Asan.M.loaded_segments (0x5e584 : word) = Some W_5e534.
Proof. vm_refl. Qed.
Lemma D_5e534 : decode_any W_5e534 = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e538 : bv 32 := 0xfeb698e3.
Lemma F_5e538 : fetch_word Asan.M.loaded_segments (0x5e588 : word) = Some W_5e538.
Proof. vm_refl. Qed.
Lemma D_5e538 : decode_any W_5e538 = Some (Branch BC_NE 13 11 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e53c : bv 32 := 0x04843583.
Lemma F_5e53c : fetch_word Asan.M.loaded_segments (0x5e58c : word) = Some W_5e53c.
Proof. vm_refl. Qed.
Lemma D_5e53c : decode_any W_5e53c = Some (Load SZ8 true 11 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e540 : bv 32 := 0x00e585b3.
Lemma F_5e540 : fetch_word Asan.M.loaded_segments (0x5e590 : word) = Some W_5e540.
Proof. vm_refl. Qed.
Lemma D_5e540 : decode_any W_5e540 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e544 : bv 32 := 0x04b43423.
Lemma F_5e544 : fetch_word Asan.M.loaded_segments (0x5e594 : word) = Some W_5e544.
Proof. vm_refl. Qed.
Lemma D_5e544 : decode_any W_5e544 = Some (Store SZ8 8 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e548 : bv 32 := 0x00100493.
Lemma F_5e548 : fetch_word Asan.M.loaded_segments (0x5e598 : word) = Some W_5e548.
Proof. vm_refl. Qed.
Lemma D_5e548 : decode_any W_5e548 = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e54c : bv 32 := 0x00043603.
Lemma F_5e54c : fetch_word Asan.M.loaded_segments (0x5e59c : word) = Some W_5e54c.
Proof. vm_refl. Qed.
Lemma D_5e54c : decode_any W_5e54c = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e550 : bv 32 := 0xfff00893.
Lemma F_5e550 : fetch_word Asan.M.loaded_segments (0x5e5a0 : word) = Some W_5e550.
Proof. vm_refl. Qed.
Lemma D_5e550 : decode_any W_5e550 = Some (OpImm ALU_ADD 17 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e554 : bv 32 := 0x00300693.
Lemma F_5e554 : fetch_word Asan.M.loaded_segments (0x5e5a4 : word) = Some W_5e554.
Proof. vm_refl. Qed.
Lemma D_5e554 : decode_any W_5e554 = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e558 : bv 32 := 0x001005b7.
Lemma F_5e558 : fetch_word Asan.M.loaded_segments (0x5e5a8 : word) = Some W_5e558.
Proof. vm_refl. Qed.
Lemma D_5e558 : decode_any W_5e558 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e55c : bv 32 := 0xfffb2717.
Lemma F_5e55c : fetch_word Asan.M.loaded_segments (0x5e5ac : word) = Some W_5e55c.
Proof. vm_refl. Qed.
Lemma D_5e55c : decode_any W_5e55c = Some (Auipc 14 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e560 : bv 32 := 0x03c89793.
Lemma F_5e560 : fetch_word Asan.M.loaded_segments (0x5e5b0 : word) = Some W_5e560.
Proof. vm_refl. Qed.
Lemma D_5e560 : decode_any W_5e560 = Some (ShiftImm ALU_SLL 15 17 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e564 : bv 32 := 0x03d69693.
Lemma F_5e564 : fetch_word Asan.M.loaded_segments (0x5e5b4 : word) = Some W_5e564.
Proof. vm_refl. Qed.
Lemma D_5e564 : decode_any W_5e564 = Some (ShiftImm ALU_SLL 13 13 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e568 : bv 32 := 0xfff58593.
Lemma F_5e568 : fetch_word Asan.M.loaded_segments (0x5e5b8 : word) = Some W_5e568.
Proof. vm_refl. Qed.
Lemma D_5e568 : decode_any W_5e568 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e56c : bv 32 := 0xe9473703.
Lemma F_5e56c : fetch_word Asan.M.loaded_segments (0x5e5bc : word) = Some W_5e56c.
Proof. vm_refl. Qed.
Lemma D_5e56c : decode_any W_5e56c = Some (Load SZ8 true 14 14 3732, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e570 : bv 32 := 0xfff78793.
Lemma F_5e570 : fetch_word Asan.M.loaded_segments (0x5e5c0 : word) = Some W_5e570.
Proof. vm_refl. Qed.
Lemma D_5e570 : decode_any W_5e570 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e574 : bv 32 := 0x02859813.
Lemma F_5e574 : fetch_word Asan.M.loaded_segments (0x5e5c4 : word) = Some W_5e574.
Proof. vm_refl. Qed.
Lemma D_5e574 : decode_any W_5e574 = Some (ShiftImm ALU_SLL 16 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e578 : bv 32 := 0x02889893.
Lemma F_5e578 : fetch_word Asan.M.loaded_segments (0x5e5c8 : word) = Some W_5e578.
Proof. vm_refl. Qed.
Lemma D_5e578 : decode_any W_5e578 = Some (ShiftImm ALU_SLL 17 17 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e57c : bv 32 := 0x00100293.
Lemma F_5e57c : fetch_word Asan.M.loaded_segments (0x5e5cc : word) = Some W_5e57c.
Proof. vm_refl. Qed.
Lemma D_5e57c : decode_any W_5e57c = Some (OpImm ALU_ADD 5 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e580 : bv 32 := 0x03e29293.
Lemma F_5e580 : fetch_word Asan.M.loaded_segments (0x5e5d0 : word) = Some W_5e580.
Proof. vm_refl. Qed.
Lemma D_5e580 : decode_any W_5e580 = Some (ShiftImm ALU_SLL 5 5 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e584 : bv 32 := 0x01c0006f.
Lemma F_5e584 : fetch_word Asan.M.loaded_segments (0x5e5d4 : word) = Some W_5e584.
Proof. vm_refl. Qed.
Lemma D_5e584 : decode_any W_5e584 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e588 : bv 32 := 0x160433af.
Lemma F_5e588 : fetch_word Asan.M.loaded_segments (0x5e5d8 : word) = Some W_5e588.
Proof. vm_refl. Qed.
Lemma D_5e588 : decode_any W_5e588 = Some (Lr AD true true 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e58c : bv 32 := 0x00c39663.
Lemma F_5e58c : fetch_word Asan.M.loaded_segments (0x5e5dc : word) = Some W_5e58c.
Proof. vm_refl. Qed.
Lemma D_5e58c : decode_any W_5e58c = Some (Branch BC_NE 7 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e590 : bv 32 := 0x1a643e2f.
Lemma F_5e590 : fetch_word Asan.M.loaded_segments (0x5e5e0 : word) = Some W_5e590.
Proof. vm_refl. Qed.
Lemma D_5e590 : decode_any W_5e590 = Some (Sc AD false true 28 8 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e594 : bv 32 := 0xfe0e1ae3.
Lemma F_5e594 : fetch_word Asan.M.loaded_segments (0x5e5e4 : word) = Some W_5e594.
Proof. vm_refl. Qed.
Lemma D_5e594 : decode_any W_5e594 = Some (Branch BC_NE 28 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e598 : bv 32 := 0x06c38463.
Lemma F_5e598 : fetch_word Asan.M.loaded_segments (0x5e5e8 : word) = Some W_5e598.
Proof. vm_refl. Qed.
Lemma D_5e598 : decode_any W_5e598 = Some (Branch BC_EQ 7 12 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a0 : bv 32 := 0x00d675b3.
Lemma F_5e5a0 : fetch_word Asan.M.loaded_segments (0x5e5f0 : word) = Some W_5e5a0.
Proof. vm_refl. Qed.
Lemma D_5e5a0 : decode_any W_5e5a0 = Some (Op ALU_AND 11 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a4 : bv 32 := 0x00f67333.
Lemma F_5e5a4 : fetch_word Asan.M.loaded_segments (0x5e5f4 : word) = Some W_5e5a4.
Proof. vm_refl. Qed.
Lemma D_5e5a4 : decode_any W_5e5a4 = Some (Op ALU_AND 6 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a8 : bv 32 := 0x02059663.
Lemma F_5e5a8 : fetch_word Asan.M.loaded_segments (0x5e5f8 : word) = Some W_5e5a8.
Proof. vm_refl. Qed.
Lemma D_5e5a8 : decode_any W_5e5a8 = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5ac : bv 32 := 0x010675b3.
Lemma F_5e5ac : fetch_word Asan.M.loaded_segments (0x5e5fc : word) = Some W_5e5ac.
Proof. vm_refl. Qed.
Lemma D_5e5ac : decode_any W_5e5ac = Some (Op ALU_AND 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5b0 : bv 32 := 0x02058263.
Lemma F_5e5b0 : fetch_word Asan.M.loaded_segments (0x5e600 : word) = Some W_5e5b0.
Proof. vm_refl. Qed.
Lemma D_5e5b0 : decode_any W_5e5b0 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d4 : bv 32 := 0x013675b3.
Lemma F_5e5d4 : fetch_word Asan.M.loaded_segments (0x5e624 : word) = Some W_5e5d4.
Proof. vm_refl. Qed.
Lemma D_5e5d4 : decode_any W_5e5d4 = Some (Op ALU_AND 11 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d8 : bv 32 := 0x00b035b3.
Lemma F_5e5d8 : fetch_word Asan.M.loaded_segments (0x5e628 : word) = Some W_5e5d8.
Proof. vm_refl. Qed.
Lemma D_5e5d8 : decode_any W_5e5d8 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5dc : bv 32 := 0x01465393.
Lemma F_5e5dc : fetch_word Asan.M.loaded_segments (0x5e62c : word) = Some W_5e5dc.
Proof. vm_refl. Qed.
Lemma D_5e5dc : decode_any W_5e5dc = Some (ShiftImm ALU_SRL 7 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e0 : bv 32 := 0xfff58593.
Lemma F_5e5e0 : fetch_word Asan.M.loaded_segments (0x5e630 : word) = Some W_5e5e0.
Proof. vm_refl. Qed.
Lemma D_5e5e0 : decode_any W_5e5e0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e4 : bv 32 := 0x00b3f5b3.
Lemma F_5e5e4 : fetch_word Asan.M.loaded_segments (0x5e634 : word) = Some W_5e5e4.
Proof. vm_refl. Qed.
Lemma D_5e5e4 : decode_any W_5e5e4 = Some (Op ALU_AND 11 7 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e8 : bv 32 := 0x02c59593.
Lemma F_5e5e8 : fetch_word Asan.M.loaded_segments (0x5e638 : word) = Some W_5e5e8.
Proof. vm_refl. Qed.
Lemma D_5e5e8 : decode_any W_5e5e8 = Some (ShiftImm ALU_SLL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5ec : bv 32 := 0x02c5d593.
Lemma F_5e5ec : fetch_word Asan.M.loaded_segments (0x5e63c : word) = Some W_5e5ec.
Proof. vm_refl. Qed.
Lemma D_5e5ec : decode_any W_5e5ec = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5f0 : bv 32 := 0xf8058ce3.
Lemma F_5e5f0 : fetch_word Asan.M.loaded_segments (0x5e640 : word) = Some W_5e5f0.
Proof. vm_refl. Qed.
Lemma D_5e5f0 : decode_any W_5e5f0 = Some (Branch BC_EQ 11 0 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e600 : bv 32 := 0x00058a63.
Lemma F_5e600 : fetch_word Asan.M.loaded_segments (0x5e650 : word) = Some W_5e600.
Proof. vm_refl. Qed.
Lemma D_5e600 : decode_any W_5e600 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e614 : bv 32 := 0x00048513.
Lemma F_5e614 : fetch_word Asan.M.loaded_segments (0x5e664 : word) = Some W_5e614.
Proof. vm_refl. Qed.
Lemma D_5e614 : decode_any W_5e614 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e618 : bv 32 := 0x07813083.
Lemma F_5e618 : fetch_word Asan.M.loaded_segments (0x5e668 : word) = Some W_5e618.
Proof. vm_refl. Qed.
Lemma D_5e618 : decode_any W_5e618 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e61c : bv 32 := 0x07013403.
Lemma F_5e61c : fetch_word Asan.M.loaded_segments (0x5e66c : word) = Some W_5e61c.
Proof. vm_refl. Qed.
Lemma D_5e61c : decode_any W_5e61c = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e620 : bv 32 := 0x06813483.
Lemma F_5e620 : fetch_word Asan.M.loaded_segments (0x5e670 : word) = Some W_5e620.
Proof. vm_refl. Qed.
Lemma D_5e620 : decode_any W_5e620 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e624 : bv 32 := 0x06013903.
Lemma F_5e624 : fetch_word Asan.M.loaded_segments (0x5e674 : word) = Some W_5e624.
Proof. vm_refl. Qed.
Lemma D_5e624 : decode_any W_5e624 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e628 : bv 32 := 0x05813983.
Lemma F_5e628 : fetch_word Asan.M.loaded_segments (0x5e678 : word) = Some W_5e628.
Proof. vm_refl. Qed.
Lemma D_5e628 : decode_any W_5e628 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e62c : bv 32 := 0x05013a03.
Lemma F_5e62c : fetch_word Asan.M.loaded_segments (0x5e67c : word) = Some W_5e62c.
Proof. vm_refl. Qed.
Lemma D_5e62c : decode_any W_5e62c = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e630 : bv 32 := 0x04813a83.
Lemma F_5e630 : fetch_word Asan.M.loaded_segments (0x5e680 : word) = Some W_5e630.
Proof. vm_refl. Qed.
Lemma D_5e630 : decode_any W_5e630 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e634 : bv 32 := 0x04013b03.
Lemma F_5e634 : fetch_word Asan.M.loaded_segments (0x5e684 : word) = Some W_5e634.
Proof. vm_refl. Qed.
Lemma D_5e634 : decode_any W_5e634 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e638 : bv 32 := 0x03813b83.
Lemma F_5e638 : fetch_word Asan.M.loaded_segments (0x5e688 : word) = Some W_5e638.
Proof. vm_refl. Qed.
Lemma D_5e638 : decode_any W_5e638 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e63c : bv 32 := 0x03013c03.
Lemma F_5e63c : fetch_word Asan.M.loaded_segments (0x5e68c : word) = Some W_5e63c.
Proof. vm_refl. Qed.
Lemma D_5e63c : decode_any W_5e63c = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e640 : bv 32 := 0x02813c83.
Lemma F_5e640 : fetch_word Asan.M.loaded_segments (0x5e690 : word) = Some W_5e640.
Proof. vm_refl. Qed.
Lemma D_5e640 : decode_any W_5e640 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e644 : bv 32 := 0x02013d03.
Lemma F_5e644 : fetch_word Asan.M.loaded_segments (0x5e694 : word) = Some W_5e644.
Proof. vm_refl. Qed.
Lemma D_5e644 : decode_any W_5e644 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e648 : bv 32 := 0x01813d83.
Lemma F_5e648 : fetch_word Asan.M.loaded_segments (0x5e698 : word) = Some W_5e648.
Proof. vm_refl. Qed.
Lemma D_5e648 : decode_any W_5e648 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e64c : bv 32 := 0x08010113.
Lemma F_5e64c : fetch_word Asan.M.loaded_segments (0x5e69c : word) = Some W_5e64c.
Proof. vm_refl. Qed.
Lemma D_5e64c : decode_any W_5e64c = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e650 : bv 32 := 0x00008067.
Lemma F_5e650 : fetch_word Asan.M.loaded_segments (0x5e6a0 : word) = Some W_5e650.
Proof. vm_refl. Qed.
Lemma D_5e650 : decode_any W_5e650 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e654 : bv 32 := 0x00068a93.
Lemma F_5e654 : fetch_word Asan.M.loaded_segments (0x5e6a4 : word) = Some W_5e654.
Proof. vm_refl. Qed.
Lemma D_5e654 : decode_any W_5e654 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e658 : bv 32 := 0x00050913.
Lemma F_5e658 : fetch_word Asan.M.loaded_segments (0x5e6a8 : word) = Some W_5e658.
Proof. vm_refl. Qed.
Lemma D_5e658 : decode_any W_5e658 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e65c : bv 32 := 0x00070b13.
Lemma F_5e65c : fetch_word Asan.M.loaded_segments (0x5e6ac : word) = Some W_5e65c.
Proof. vm_refl. Qed.
Lemma D_5e65c : decode_any W_5e65c = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e660 : bv 32 := 0x40f70733.
Lemma F_5e660 : fetch_word Asan.M.loaded_segments (0x5e6b0 : word) = Some W_5e660.
Proof. vm_refl. Qed.
Lemma D_5e660 : decode_any W_5e660 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e664 : bv 32 := 0x00048513.
Lemma F_5e664 : fetch_word Asan.M.loaded_segments (0x5e6b4 : word) = Some W_5e664.
Proof. vm_refl. Qed.
Lemma D_5e664 : decode_any W_5e664 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e668 : bv 32 := 0x00040693.
Lemma F_5e668 : fetch_word Asan.M.loaded_segments (0x5e6b8 : word) = Some W_5e668.
Proof. vm_refl. Qed.
Lemma D_5e668 : decode_any W_5e668 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e66c : bv 32 := 0x050000ef.
Lemma F_5e66c : fetch_word Asan.M.loaded_segments (0x5e6bc : word) = Some W_5e66c.
Proof. vm_refl. Qed.
Lemma D_5e66c : decode_any W_5e66c = Some (Jal 1 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e670 : bv 32 := 0x02050263.
Lemma F_5e670 : fetch_word Asan.M.loaded_segments (0x5e6c0 : word) = Some W_5e670.
Proof. vm_refl. Qed.
Lemma D_5e670 : decode_any W_5e670 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e674 : bv 32 := 0x01043783.
Lemma F_5e674 : fetch_word Asan.M.loaded_segments (0x5e6c4 : word) = Some W_5e674.
Proof. vm_refl. Qed.
Lemma D_5e674 : decode_any W_5e674 = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e678 : bv 32 := 0x000b0713.
Lemma F_5e678 : fetch_word Asan.M.loaded_segments (0x5e6c8 : word) = Some W_5e678.
Proof. vm_refl. Qed.
Lemma D_5e678 : decode_any W_5e678 = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e67c : bv 32 := 0x0367e263.
Lemma F_5e67c : fetch_word Asan.M.loaded_segments (0x5e6cc : word) = Some W_5e67c.
Proof. vm_refl. Qed.
Lemma D_5e67c : decode_any W_5e67c = Some (Branch BC_LTU 15 22 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e680 : bv 32 := 0x000a8693.
Lemma F_5e680 : fetch_word Asan.M.loaded_segments (0x5e6d0 : word) = Some W_5e680.
Proof. vm_refl. Qed.
Lemma D_5e680 : decode_any W_5e680 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e684 : bv 32 := 0x40e787b3.
Lemma F_5e684 : fetch_word Asan.M.loaded_segments (0x5e6d4 : word) = Some W_5e684.
Proof. vm_refl. Qed.
Lemma D_5e684 : decode_any W_5e684 = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e688 : bv 32 := 0x00f43823.
Lemma F_5e688 : fetch_word Asan.M.loaded_segments (0x5e6d8 : word) = Some W_5e688.
Proof. vm_refl. Qed.
Lemma D_5e688 : decode_any W_5e688 = Some (Store SZ8 8 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e68c : bv 32 := 0x00090513.
Lemma F_5e68c : fetch_word Asan.M.loaded_segments (0x5e6dc : word) = Some W_5e68c.
Proof. vm_refl. Qed.
Lemma D_5e68c : decode_any W_5e68c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e690 : bv 32 := 0xe89ff06f.
Lemma F_5e690 : fetch_word Asan.M.loaded_segments (0x5e6e0 : word) = Some W_5e690.
Proof. vm_refl. Qed.
Lemma D_5e690 : decode_any W_5e690 = Some (Jal 0 2096776, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6bc : bv 32 := 0xfc010113.
Lemma F_5e6bc : fetch_word Asan.M.loaded_segments (0x5e70c : word) = Some W_5e6bc.
Proof. vm_refl. Qed.
Lemma D_5e6bc : decode_any W_5e6bc = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6c0 : bv 32 := 0x02113c23.
Lemma F_5e6c0 : fetch_word Asan.M.loaded_segments (0x5e710 : word) = Some W_5e6c0.
Proof. vm_refl. Qed.
Lemma D_5e6c0 : decode_any W_5e6c0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6c4 : bv 32 := 0x02813823.
Lemma F_5e6c4 : fetch_word Asan.M.loaded_segments (0x5e714 : word) = Some W_5e6c4.
Proof. vm_refl. Qed.
Lemma D_5e6c4 : decode_any W_5e6c4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6c8 : bv 32 := 0x02913423.
Lemma F_5e6c8 : fetch_word Asan.M.loaded_segments (0x5e718 : word) = Some W_5e6c8.
Proof. vm_refl. Qed.
Lemma D_5e6c8 : decode_any W_5e6c8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6cc : bv 32 := 0x03213023.
Lemma F_5e6cc : fetch_word Asan.M.loaded_segments (0x5e71c : word) = Some W_5e6cc.
Proof. vm_refl. Qed.
Lemma D_5e6cc : decode_any W_5e6cc = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d0 : bv 32 := 0x01313c23.
Lemma F_5e6d0 : fetch_word Asan.M.loaded_segments (0x5e720 : word) = Some W_5e6d0.
Proof. vm_refl. Qed.
Lemma D_5e6d0 : decode_any W_5e6d0 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d4 : bv 32 := 0x01413823.
Lemma F_5e6d4 : fetch_word Asan.M.loaded_segments (0x5e724 : word) = Some W_5e6d4.
Proof. vm_refl. Qed.
Lemma D_5e6d4 : decode_any W_5e6d4 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d8 : bv 32 := 0x01513423.
Lemma F_5e6d8 : fetch_word Asan.M.loaded_segments (0x5e728 : word) = Some W_5e6d8.
Proof. vm_refl. Qed.
Lemma D_5e6d8 : decode_any W_5e6d8 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6dc : bv 32 := 0x01613023.
Lemma F_5e6dc : fetch_word Asan.M.loaded_segments (0x5e72c : word) = Some W_5e6dc.
Proof. vm_refl. Qed.
Lemma D_5e6dc : decode_any W_5e6dc = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e0 : bv 32 := 0x00068413.
Lemma F_5e6e0 : fetch_word Asan.M.loaded_segments (0x5e730 : word) = Some W_5e6e0.
Proof. vm_refl. Qed.
Lemma D_5e6e0 : decode_any W_5e6e0 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e4 : bv 32 := 0x00058493.
Lemma F_5e6e4 : fetch_word Asan.M.loaded_segments (0x5e734 : word) = Some W_5e6e4.
Proof. vm_refl. Qed.
Lemma D_5e6e4 : decode_any W_5e6e4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e8 : bv 32 := 0x02053903.
Lemma F_5e6e8 : fetch_word Asan.M.loaded_segments (0x5e738 : word) = Some W_5e6e8.
Proof. vm_refl. Qed.
Lemma D_5e6e8 : decode_any W_5e6e8 = Some (Load SZ8 true 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6ec : bv 32 := 0x01f00693.
Lemma F_5e6ec : fetch_word Asan.M.loaded_segments (0x5e73c : word) = Some W_5e6ec.
Proof. vm_refl. Qed.
Lemma D_5e6ec : decode_any W_5e6ec = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f0 : bv 32 := 0x02061593.
Lemma F_5e6f0 : fetch_word Asan.M.loaded_segments (0x5e740 : word) = Some W_5e6f0.
Proof. vm_refl. Qed.
Lemma D_5e6f0 : decode_any W_5e6f0 = Some (ShiftImm ALU_SLL 11 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f4 : bv 32 := 0x20d60263.
Lemma F_5e6f4 : fetch_word Asan.M.loaded_segments (0x5e744 : word) = Some W_5e6f4.
Proof. vm_refl. Qed.
Lemma D_5e6f4 : decode_any W_5e6f4 = Some (Branch BC_EQ 12 13 516, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f8 : bv 32 := 0x01000693.
Lemma F_5e6f8 : fetch_word Asan.M.loaded_segments (0x5e748 : word) = Some W_5e6f8.
Proof. vm_refl. Qed.
Lemma D_5e6f8 : decode_any W_5e6f8 = Some (OpImm ALU_ADD 13 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6fc : bv 32 := 0x02c6e263.
Lemma F_5e6fc : fetch_word Asan.M.loaded_segments (0x5e74c : word) = Some W_5e6fc.
Proof. vm_refl. Qed.
Lemma D_5e6fc : decode_any W_5e6fc = Some (Branch BC_LTU 13 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e700 : bv 32 := 0x00561a93.
Lemma F_5e700 : fetch_word Asan.M.loaded_segments (0x5e750 : word) = Some W_5e700.
Proof. vm_refl. Qed.
Lemma D_5e700 : decode_any W_5e700 = Some (ShiftImm ALU_SLL 21 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e704 : bv 32 := 0x02043683.
Lemma F_5e704 : fetch_word Asan.M.loaded_segments (0x5e754 : word) = Some W_5e704.
Proof. vm_refl. Qed.
Lemma D_5e704 : decode_any W_5e704 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e708 : bv 32 := 0x03043a03.
Lemma F_5e708 : fetch_word Asan.M.loaded_segments (0x5e758 : word) = Some W_5e708.
Proof. vm_refl. Qed.
Lemma D_5e708 : decode_any W_5e708 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e70c : bv 32 := 0x02ea89b3.
Lemma F_5e70c : fetch_word Asan.M.loaded_segments (0x5e75c : word) = Some W_5e70c.
Proof. vm_refl. Qed.
Lemma D_5e70c : decode_any W_5e70c = Some (Mul M_MUL 19 21 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e710 : bv 32 := 0x013689b3.
Lemma F_5e710 : fetch_word Asan.M.loaded_segments (0x5e760 : word) = Some W_5e710.
Proof. vm_refl. Qed.
Lemma D_5e710 : decode_any W_5e710 = Some (Op ALU_ADD 19 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e714 : bv 32 := 0x00b90933.
Lemma F_5e714 : fetch_word Asan.M.loaded_segments (0x5e764 : word) = Some W_5e714.
Proof. vm_refl. Qed.
Lemma D_5e714 : decode_any W_5e714 = Some (Op ALU_ADD 18 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e718 : bv 32 := 0x053a6263.
Lemma F_5e718 : fetch_word Asan.M.loaded_segments (0x5e768 : word) = Some W_5e718.
Proof. vm_refl. Qed.
Lemma D_5e718 : decode_any W_5e718 = Some (Branch BC_LTU 20 19 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e720 : bv 32 := 0xff060693.
Lemma F_5e720 : fetch_word Asan.M.loaded_segments (0x5e770 : word) = Some W_5e720.
Proof. vm_refl. Qed.
Lemma D_5e720 : decode_any W_5e720 = Some (OpImm ALU_ADD 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e724 : bv 32 := 0x20000793.
Lemma F_5e724 : fetch_word Asan.M.loaded_segments (0x5e774 : word) = Some W_5e724.
Proof. vm_refl. Qed.
Lemma D_5e724 : decode_any W_5e724 = Some (OpImm ALU_ADD 15 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e728 : bv 32 := 0x03f61813.
Lemma F_5e728 : fetch_word Asan.M.loaded_segments (0x5e778 : word) = Some W_5e728.
Proof. vm_refl. Qed.
Lemma D_5e728 : decode_any W_5e728 = Some (ShiftImm ALU_SLL 16 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e72c : bv 32 := 0x0016d693.
Lemma F_5e72c : fetch_word Asan.M.loaded_segments (0x5e77c : word) = Some W_5e72c.
Proof. vm_refl. Qed.
Lemma D_5e72c : decode_any W_5e72c = Some (ShiftImm ALU_SRL 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e730 : bv 32 := 0x00d79ab3.
Lemma F_5e730 : fetch_word Asan.M.loaded_segments (0x5e780 : word) = Some W_5e730.
Proof. vm_refl. Qed.
Lemma D_5e730 : decode_any W_5e730 = Some (Op ALU_SLL 21 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e734 : bv 32 := 0x001ad693.
Lemma F_5e734 : fetch_word Asan.M.loaded_segments (0x5e784 : word) = Some W_5e734.
Proof. vm_refl. Qed.
Lemma D_5e734 : decode_any W_5e734 = Some (ShiftImm ALU_SRL 13 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e738 : bv 32 := 0x43f85793.
Lemma F_5e738 : fetch_word Asan.M.loaded_segments (0x5e788 : word) = Some W_5e738.
Proof. vm_refl. Qed.
Lemma D_5e738 : decode_any W_5e738 = Some (ShiftImm ALU_SRA 15 16 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e73c : bv 32 := 0x00d7f6b3.
Lemma F_5e73c : fetch_word Asan.M.loaded_segments (0x5e78c : word) = Some W_5e73c.
Proof. vm_refl. Qed.
Lemma D_5e73c : decode_any W_5e73c = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e740 : bv 32 := 0x01568ab3.
Lemma F_5e740 : fetch_word Asan.M.loaded_segments (0x5e790 : word) = Some W_5e740.
Proof. vm_refl. Qed.
Lemma D_5e740 : decode_any W_5e740 = Some (Op ALU_ADD 21 13 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e744 : bv 32 := 0x02043683.
Lemma F_5e744 : fetch_word Asan.M.loaded_segments (0x5e794 : word) = Some W_5e744.
Proof. vm_refl. Qed.
Lemma D_5e744 : decode_any W_5e744 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e748 : bv 32 := 0x03043a03.
Lemma F_5e748 : fetch_word Asan.M.loaded_segments (0x5e798 : word) = Some W_5e748.
Proof. vm_refl. Qed.
Lemma D_5e748 : decode_any W_5e748 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e74c : bv 32 := 0x02ea89b3.
Lemma F_5e74c : fetch_word Asan.M.loaded_segments (0x5e79c : word) = Some W_5e74c.
Proof. vm_refl. Qed.
Lemma D_5e74c : decode_any W_5e74c = Some (Mul M_MUL 19 21 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e750 : bv 32 := 0x013689b3.
Lemma F_5e750 : fetch_word Asan.M.loaded_segments (0x5e7a0 : word) = Some W_5e750.
Proof. vm_refl. Qed.
Lemma D_5e750 : decode_any W_5e750 = Some (Op ALU_ADD 19 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e754 : bv 32 := 0x00b90933.
Lemma F_5e754 : fetch_word Asan.M.loaded_segments (0x5e7a4 : word) = Some W_5e754.
Proof. vm_refl. Qed.
Lemma D_5e754 : decode_any W_5e754 = Some (Op ALU_ADD 18 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e758 : bv 32 := 0x0d3a7c63.
Lemma F_5e758 : fetch_word Asan.M.loaded_segments (0x5e7a8 : word) = Some W_5e758.
Proof. vm_refl. Qed.
Lemma D_5e758 : decode_any W_5e758 = Some (Branch BC_GEU 20 19 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e75c : bv 32 := 0x1a0a0e63.
Lemma F_5e75c : fetch_word Asan.M.loaded_segments (0x5e7ac : word) = Some W_5e75c.
Proof. vm_refl. Qed.
Lemma D_5e75c : decode_any W_5e75c = Some (Branch BC_EQ 20 0 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e760 : bv 32 := 0xfffa4593.
Lemma F_5e760 : fetch_word Asan.M.loaded_segments (0x5e7b0 : word) = Some W_5e760.
Proof. vm_refl. Qed.
Lemma D_5e760 : decode_any W_5e760 = Some (OpImm ALU_XOR 11 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e764 : bv 32 := 0xfffc06b7.
Lemma F_5e764 : fetch_word Asan.M.loaded_segments (0x5e7b4 : word) = Some W_5e764.
Proof. vm_refl. Qed.
Lemma D_5e764 : decode_any W_5e764 = Some (Lui 13 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e768 : bv 32 := 0x00b985b3.
Lemma F_5e768 : fetch_word Asan.M.loaded_segments (0x5e7b8 : word) = Some W_5e768.
Proof. vm_refl. Qed.
Lemma D_5e768 : decode_any W_5e768 = Some (Op ALU_ADD 11 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e76c : bv 32 := 0x000409b7.
Lemma F_5e76c : fetch_word Asan.M.loaded_segments (0x5e7bc : word) = Some W_5e76c.
Proof. vm_refl. Qed.
Lemma D_5e76c : decode_any W_5e76c = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e770 : bv 32 := 0x00d5f5b3.
Lemma F_5e770 : fetch_word Asan.M.loaded_segments (0x5e7c0 : word) = Some W_5e770.
Proof. vm_refl. Qed.
Lemma D_5e770 : decode_any W_5e770 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e774 : bv 32 := 0x03843683.
Lemma F_5e774 : fetch_word Asan.M.loaded_segments (0x5e7c4 : word) = Some W_5e774.
Proof. vm_refl. Qed.
Lemma D_5e774 : decode_any W_5e774 = Some (Load SZ8 true 13 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e778 : bv 32 := 0x013589b3.
Lemma F_5e778 : fetch_word Asan.M.loaded_segments (0x5e7c8 : word) = Some W_5e778.
Proof. vm_refl. Qed.
Lemma D_5e778 : decode_any W_5e778 = Some (Op ALU_ADD 19 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e77c : bv 32 := 0x00700593.
Lemma F_5e77c : fetch_word Asan.M.loaded_segments (0x5e7cc : word) = Some W_5e77c.
Proof. vm_refl. Qed.
Lemma D_5e77c : decode_any W_5e77c = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e780 : bv 32 := 0x01d59593.
Lemma F_5e780 : fetch_word Asan.M.loaded_segments (0x5e7d0 : word) = Some W_5e780.
Proof. vm_refl. Qed.
Lemma D_5e780 : decode_any W_5e780 = Some (ShiftImm ALU_SLL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e784 : bv 32 := 0x014686b3.
Lemma F_5e784 : fetch_word Asan.M.loaded_segments (0x5e7d4 : word) = Some W_5e784.
Proof. vm_refl. Qed.
Lemma D_5e784 : decode_any W_5e784 = Some (Op ALU_ADD 13 13 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e788 : bv 32 := 0x013686b3.
Lemma F_5e788 : fetch_word Asan.M.loaded_segments (0x5e7d8 : word) = Some W_5e788.
Proof. vm_refl. Qed.
Lemma D_5e788 : decode_any W_5e788 = Some (Op ALU_ADD 13 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e78c : bv 32 := 0x00158593.
Lemma F_5e78c : fetch_word Asan.M.loaded_segments (0x5e7dc : word) = Some W_5e78c.
Proof. vm_refl. Qed.
Lemma D_5e78c : decode_any W_5e78c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e790 : bv 32 := 0x1ab6fa63.
Lemma F_5e790 : fetch_word Asan.M.loaded_segments (0x5e7e0 : word) = Some W_5e790.
Proof. vm_refl. Qed.
Lemma D_5e790 : decode_any W_5e790 = Some (Branch BC_GEU 13 11 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e794 : bv 32 := 0x03854583.
Lemma F_5e794 : fetch_word Asan.M.loaded_segments (0x5e7e4 : word) = Some W_5e794.
Proof. vm_refl. Qed.
Lemma D_5e794 : decode_any W_5e794 = Some (Load SZ1 false 11 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e798 : bv 32 := 0x012a0a33.
Lemma F_5e798 : fetch_word Asan.M.loaded_segments (0x5e7e8 : word) = Some W_5e798.
Proof. vm_refl. Qed.
Lemma D_5e798 : decode_any W_5e798 = Some (Op ALU_ADD 20 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e79c : bv 32 := 0x02058463.
Lemma F_5e79c : fetch_word Asan.M.loaded_segments (0x5e7ec : word) = Some W_5e79c.
Proof. vm_refl. Qed.
Lemma D_5e79c : decode_any W_5e79c = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c4 : bv 32 := 0xfffb9597.
Lemma F_5e7c4 : fetch_word Asan.M.loaded_segments (0x5e814 : word) = Some W_5e7c4.
Proof. vm_refl. Qed.
Lemma D_5e7c4 : decode_any W_5e7c4 = Some (Auipc 11 1048505, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c8 : bv 32 := 0x78358693.
Lemma F_5e7c8 : fetch_word Asan.M.loaded_segments (0x5e818 : word) = Some W_5e7c8.
Proof. vm_refl. Qed.
Lemma D_5e7c8 : decode_any W_5e7c8 = Some (OpImm ALU_ADD 13 11 1923, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7cc : bv 32 := 0x00050b13.
Lemma F_5e7cc : fetch_word Asan.M.loaded_segments (0x5e81c : word) = Some W_5e7cc.
Proof. vm_refl. Qed.
Lemma D_5e7cc : decode_any W_5e7cc = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d0 : bv 32 := 0x000a0593.
Lemma F_5e7d0 : fetch_word Asan.M.loaded_segments (0x5e820 : word) = Some W_5e7d0.
Proof. vm_refl. Qed.
Lemma D_5e7d0 : decode_any W_5e7d0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d4 : bv 32 := 0x00098613.
Lemma F_5e7d4 : fetch_word Asan.M.loaded_segments (0x5e824 : word) = Some W_5e7d4.
Proof. vm_refl. Qed.
Lemma D_5e7d4 : decode_any W_5e7d4 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d8 : bv 32 := 0x5843e0ef.
Lemma F_5e7d8 : fetch_word Asan.M.loaded_segments (0x5e828 : word) = Some W_5e7d8.
Proof. vm_refl. Qed.
Lemma D_5e7d8 : decode_any W_5e7d8 = Some (Jal 1 255364, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7dc : bv 32 := 0x16050863.
Lemma F_5e7dc : fetch_word Asan.M.loaded_segments (0x5e82c : word) = Some W_5e7dc.
Proof. vm_refl. Qed.
Lemma D_5e7dc : decode_any W_5e7dc = Some (Branch BC_EQ 10 0 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e0 : bv 32 := 0x00050713.
Lemma F_5e7e0 : fetch_word Asan.M.loaded_segments (0x5e830 : word) = Some W_5e7e0.
Proof. vm_refl. Qed.
Lemma D_5e7e0 : decode_any W_5e7e0 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e4 : bv 32 := 0x1eaa1063.
Lemma F_5e7e4 : fetch_word Asan.M.loaded_segments (0x5e834 : word) = Some W_5e7e4.
Proof. vm_refl. Qed.
Lemma D_5e7e4 : decode_any W_5e7e4 = Some (Branch BC_NE 20 10 480, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e8 : bv 32 := 0x0fa00613.
Lemma F_5e7e8 : fetch_word Asan.M.loaded_segments (0x5e838 : word) = Some W_5e7e8.
Proof. vm_refl. Qed.
Lemma D_5e7e8 : decode_any W_5e7e8 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ec : bv 32 := 0x000a0513.
Lemma F_5e7ec : fetch_word Asan.M.loaded_segments (0x5e83c : word) = Some W_5e7ec.
Proof. vm_refl. Qed.
Lemma D_5e7ec : decode_any W_5e7ec = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f0 : bv 32 := 0x00098593.
Lemma F_5e7f0 : fetch_word Asan.M.loaded_segments (0x5e840 : word) = Some W_5e7f0.
Proof. vm_refl. Qed.
Lemma D_5e7f0 : decode_any W_5e7f0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f4 : bv 32 := 0x4d4230ef.
Lemma F_5e7f4 : fetch_word Asan.M.loaded_segments (0x5e844 : word) = Some W_5e7f4.
Proof. vm_refl. Qed.
Lemma D_5e7f4 : decode_any W_5e7f4 = Some (Jal 1 144596, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f8 : bv 32 := 0x4482b0ef.
Lemma F_5e7f8 : fetch_word Asan.M.loaded_segments (0x5e848 : word) = Some W_5e7f8.
Proof. vm_refl. Qed.
Lemma D_5e7f8 : decode_any W_5e7f8 = Some (Jal 1 177224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7fc : bv 32 := 0x04853583.
Lemma F_5e7fc : fetch_word Asan.M.loaded_segments (0x5e84c : word) = Some W_5e7fc.
Proof. vm_refl. Qed.
Lemma D_5e7fc : decode_any W_5e7fc = Some (Load SZ8 true 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e800 : bv 32 := 0x05053603.
Lemma F_5e800 : fetch_word Asan.M.loaded_segments (0x5e850 : word) = Some W_5e800.
Proof. vm_refl. Qed.
Lemma D_5e800 : decode_any W_5e800 = Some (Load SZ8 true 12 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e804 : bv 32 := 0x00158593.
Lemma F_5e804 : fetch_word Asan.M.loaded_segments (0x5e854 : word) = Some W_5e804.
Proof. vm_refl. Qed.
Lemma D_5e804 : decode_any W_5e804 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e808 : bv 32 := 0x01360633.
Lemma F_5e808 : fetch_word Asan.M.loaded_segments (0x5e858 : word) = Some W_5e808.
Proof. vm_refl. Qed.
Lemma D_5e808 : decode_any W_5e808 = Some (Op ALU_ADD 12 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e80c : bv 32 := 0x04b53423.
Lemma F_5e80c : fetch_word Asan.M.loaded_segments (0x5e85c : word) = Some W_5e80c.
Proof. vm_refl. Qed.
Lemma D_5e80c : decode_any W_5e80c = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e810 : bv 32 := 0x04c53823.
Lemma F_5e810 : fetch_word Asan.M.loaded_segments (0x5e860 : word) = Some W_5e810.
Proof. vm_refl. Qed.
Lemma D_5e810 : decode_any W_5e810 = Some (Store SZ8 10 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e814 : bv 32 := 0x000b0513.
Lemma F_5e814 : fetch_word Asan.M.loaded_segments (0x5e864 : word) = Some W_5e814.
Proof. vm_refl. Qed.
Lemma D_5e814 : decode_any W_5e814 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e818 : bv 32 := 0x01848493.
Lemma F_5e818 : fetch_word Asan.M.loaded_segments (0x5e868 : word) = Some W_5e818.
Proof. vm_refl. Qed.
Lemma D_5e818 : decode_any W_5e818 = Some (OpImm ALU_ADD 9 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e81c : bv 32 := 0x0134b02f.
Lemma F_5e81c : fetch_word Asan.M.loaded_segments (0x5e86c : word) = Some W_5e81c.
Proof. vm_refl. Qed.
Lemma D_5e81c : decode_any W_5e81c = Some (Amo AMO_ADD AD false false 0 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e820 : bv 32 := 0x03043a03.
Lemma F_5e820 : fetch_word Asan.M.loaded_segments (0x5e870 : word) = Some W_5e820.
Proof. vm_refl. Qed.
Lemma D_5e820 : decode_any W_5e820 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e824 : bv 32 := 0x02043683.
Lemma F_5e824 : fetch_word Asan.M.loaded_segments (0x5e874 : word) = Some W_5e824.
Proof. vm_refl. Qed.
Lemma D_5e824 : decode_any W_5e824 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e828 : bv 32 := 0x013a0a33.
Lemma F_5e828 : fetch_word Asan.M.loaded_segments (0x5e878 : word) = Some W_5e828.
Proof. vm_refl. Qed.
Lemma D_5e828 : decode_any W_5e828 = Some (Op ALU_ADD 20 20 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e82c : bv 32 := 0x03443823.
Lemma F_5e82c : fetch_word Asan.M.loaded_segments (0x5e87c : word) = Some W_5e82c.
Proof. vm_refl. Qed.
Lemma D_5e82c : decode_any W_5e82c = Some (Store SZ8 8 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e830 : bv 32 := 0x01043483.
Lemma F_5e830 : fetch_word Asan.M.loaded_segments (0x5e880 : word) = Some W_5e830.
Proof. vm_refl. Qed.
Lemma D_5e830 : decode_any W_5e830 = Some (Load SZ8 true 9 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e834 : bv 32 := 0x40da0a33.
Lemma F_5e834 : fetch_word Asan.M.loaded_segments (0x5e884 : word) = Some W_5e834.
Proof. vm_refl. Qed.
Lemma D_5e834 : decode_any W_5e834 = Some (Op ALU_SUB 20 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e838 : bv 32 := 0x035a59b3.
Lemma F_5e838 : fetch_word Asan.M.loaded_segments (0x5e888 : word) = Some W_5e838.
Proof. vm_refl. Qed.
Lemma D_5e838 : decode_any W_5e838 = Some (Mul M_DIVU 19 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e83c : bv 32 := 0x013484b3.
Lemma F_5e83c : fetch_word Asan.M.loaded_segments (0x5e88c : word) = Some W_5e83c.
Proof. vm_refl. Qed.
Lemma D_5e83c : decode_any W_5e83c = Some (Op ALU_ADD 9 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e840 : bv 32 := 0x00040593.
Lemma F_5e840 : fetch_word Asan.M.loaded_segments (0x5e890 : word) = Some W_5e840.
Proof. vm_refl. Qed.
Lemma D_5e840 : decode_any W_5e840 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e844 : bv 32 := 0x00090613.
Lemma F_5e844 : fetch_word Asan.M.loaded_segments (0x5e894 : word) = Some W_5e844.
Proof. vm_refl. Qed.
Lemma D_5e844 : decode_any W_5e844 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e848 : bv 32 := 0x00048693.
Lemma F_5e848 : fetch_word Asan.M.loaded_segments (0x5e898 : word) = Some W_5e848.
Proof. vm_refl. Qed.
Lemma D_5e848 : decode_any W_5e848 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e84c : bv 32 := 0xb35fd0ef.
Lemma F_5e84c : fetch_word Asan.M.loaded_segments (0x5e89c : word) = Some W_5e84c.
Proof. vm_refl. Qed.
Lemma D_5e84c : decode_any W_5e84c = Some (Jal 1 2087732, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e850 : bv 32 := 0x0e050e63.
Lemma F_5e850 : fetch_word Asan.M.loaded_segments (0x5e8a0 : word) = Some W_5e850.
Proof. vm_refl. Qed.
Lemma D_5e850 : decode_any W_5e850 = Some (Branch BC_EQ 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e854 : bv 32 := 0x02043683.
Lemma F_5e854 : fetch_word Asan.M.loaded_segments (0x5e8a4 : word) = Some W_5e854.
Proof. vm_refl. Qed.
Lemma D_5e854 : decode_any W_5e854 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e858 : bv 32 := 0x055a6063.
Lemma F_5e858 : fetch_word Asan.M.loaded_segments (0x5e8a8 : word) = Some W_5e858.
Proof. vm_refl. Qed.
Lemma D_5e858 : decode_any W_5e858 = Some (Branch BC_LTU 20 21 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e85c : bv 32 := 0x00000513.
Lemma F_5e85c : fetch_word Asan.M.loaded_segments (0x5e8ac : word) = Some W_5e85c.
Proof. vm_refl. Qed.
Lemma D_5e85c : decode_any W_5e85c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e860 : bv 32 := 0x00700593.
Lemma F_5e860 : fetch_word Asan.M.loaded_segments (0x5e8b0 : word) = Some W_5e860.
Proof. vm_refl. Qed.
Lemma D_5e860 : decode_any W_5e860 = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e864 : bv 32 := 0x01d59593.
Lemma F_5e864 : fetch_word Asan.M.loaded_segments (0x5e8b4 : word) = Some W_5e864.
Proof. vm_refl. Qed.
Lemma D_5e864 : decode_any W_5e864 = Some (ShiftImm ALU_SLL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e868 : bv 32 := 0x00b905b3.
Lemma F_5e868 : fetch_word Asan.M.loaded_segments (0x5e8b8 : word) = Some W_5e868.
Proof. vm_refl. Qed.
Lemma D_5e868 : decode_any W_5e868 = Some (Op ALU_ADD 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e86c : bv 32 := 0x00249493.
Lemma F_5e86c : fetch_word Asan.M.loaded_segments (0x5e8bc : word) = Some W_5e86c.
Proof. vm_refl. Qed.
Lemma D_5e86c : decode_any W_5e86c = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e870 : bv 32 := 0x009585b3.
Lemma F_5e870 : fetch_word Asan.M.loaded_segments (0x5e8c0 : word) = Some W_5e870.
Proof. vm_refl. Qed.
Lemma D_5e870 : decode_any W_5e870 = Some (Op ALU_ADD 11 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e874 : bv 32 := 0x00068613.
Lemma F_5e874 : fetch_word Asan.M.loaded_segments (0x5e8c4 : word) = Some W_5e874.
Proof. vm_refl. Qed.
Lemma D_5e874 : decode_any W_5e874 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e878 : bv 32 := 0x00465713.
Lemma F_5e878 : fetch_word Asan.M.loaded_segments (0x5e8c8 : word) = Some W_5e878.
Proof. vm_refl. Qed.
Lemma D_5e878 : decode_any W_5e878 = Some (ShiftImm ALU_SRL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e87c : bv 32 := 0xfff54793.
Lemma F_5e87c : fetch_word Asan.M.loaded_segments (0x5e8cc : word) = Some W_5e87c.
Proof. vm_refl. Qed.
Lemma D_5e87c : decode_any W_5e87c = Some (OpImm ALU_XOR 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e880 : bv 32 := 0x00150513.
Lemma F_5e880 : fetch_word Asan.M.loaded_segments (0x5e8d0 : word) = Some W_5e880.
Proof. vm_refl. Qed.
Lemma D_5e880 : decode_any W_5e880 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e884 : bv 32 := 0x00279793.
Lemma F_5e884 : fetch_word Asan.M.loaded_segments (0x5e8d4 : word) = Some W_5e884.
Proof. vm_refl. Qed.
Lemma D_5e884 : decode_any W_5e884 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e888 : bv 32 := 0x00f587b3.
Lemma F_5e888 : fetch_word Asan.M.loaded_segments (0x5e8d8 : word) = Some W_5e888.
Proof. vm_refl. Qed.
Lemma D_5e888 : decode_any W_5e888 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e88c : bv 32 := 0x00e7a023.
Lemma F_5e88c : fetch_word Asan.M.loaded_segments (0x5e8dc : word) = Some W_5e88c.
Proof. vm_refl. Qed.
Lemma D_5e88c : decode_any W_5e88c = Some (Store SZ4 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e890 : bv 32 := 0x01560633.
Lemma F_5e890 : fetch_word Asan.M.loaded_segments (0x5e8e0 : word) = Some W_5e890.
Proof. vm_refl. Qed.
Lemma D_5e890 : decode_any W_5e890 = Some (Op ALU_ADD 12 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e894 : bv 32 := 0xff3562e3.
Lemma F_5e894 : fetch_word Asan.M.loaded_segments (0x5e8e4 : word) = Some W_5e894.
Proof. vm_refl. Qed.
Lemma D_5e894 : decode_any W_5e894 = Some (Branch BC_LTU 10 19 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e898 : bv 32 := 0x01043503.
Lemma F_5e898 : fetch_word Asan.M.loaded_segments (0x5e8e8 : word) = Some W_5e898.
Proof. vm_refl. Qed.
Lemma D_5e898 : decode_any W_5e898 = Some (Load SZ8 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e89c : bv 32 := 0x035985b3.
Lemma F_5e89c : fetch_word Asan.M.loaded_segments (0x5e8ec : word) = Some W_5e89c.
Proof. vm_refl. Qed.
Lemma D_5e89c : decode_any W_5e89c = Some (Mul M_MUL 11 19 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a0 : bv 32 := 0x03043703.
Lemma F_5e8a0 : fetch_word Asan.M.loaded_segments (0x5e8f0 : word) = Some W_5e8a0.
Proof. vm_refl. Qed.
Lemma D_5e8a0 : decode_any W_5e8a0 = Some (Load SZ8 true 14 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a4 : bv 32 := 0x00b686b3.
Lemma F_5e8a4 : fetch_word Asan.M.loaded_segments (0x5e8f4 : word) = Some W_5e8a4.
Proof. vm_refl. Qed.
Lemma D_5e8a4 : decode_any W_5e8a4 = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a8 : bv 32 := 0x01350533.
Lemma F_5e8a8 : fetch_word Asan.M.loaded_segments (0x5e8f8 : word) = Some W_5e8a8.
Proof. vm_refl. Qed.
Lemma D_5e8a8 : decode_any W_5e8a8 = Some (Op ALU_ADD 10 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8ac : bv 32 := 0x00a43823.
Lemma F_5e8ac : fetch_word Asan.M.loaded_segments (0x5e8fc : word) = Some W_5e8ac.
Proof. vm_refl. Qed.
Lemma D_5e8ac : decode_any W_5e8ac = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8b0 : bv 32 := 0x02d43023.
Lemma F_5e8b0 : fetch_word Asan.M.loaded_segments (0x5e900 : word) = Some W_5e8b0.
Proof. vm_refl. Qed.
Lemma D_5e8b0 : decode_any W_5e8b0 = Some (Store SZ8 8 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8b4 : bv 32 := 0x0ad76063.
Lemma F_5e8b4 : fetch_word Asan.M.loaded_segments (0x5e904 : word) = Some W_5e8b4.
Proof. vm_refl. Qed.
Lemma D_5e8b4 : decode_any W_5e8b4 = Some (Branch BC_LTU 14 13 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8b8 : bv 32 := 0x02843683.
Lemma F_5e8b8 : fetch_word Asan.M.loaded_segments (0x5e908 : word) = Some W_5e8b8.
Proof. vm_refl. Qed.
Lemma D_5e8b8 : decode_any W_5e8b8 = Some (Load SZ8 true 13 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8bc : bv 32 := 0x03843703.
Lemma F_5e8bc : fetch_word Asan.M.loaded_segments (0x5e90c : word) = Some W_5e8bc.
Proof. vm_refl. Qed.
Lemma D_5e8bc : decode_any W_5e8bc = Some (Load SZ8 true 14 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8c0 : bv 32 := 0x0ad76663.
Lemma F_5e8c0 : fetch_word Asan.M.loaded_segments (0x5e910 : word) = Some W_5e8c0.
Proof. vm_refl. Qed.
Lemma D_5e8c0 : decode_any W_5e8c0 = Some (Branch BC_LTU 14 13 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8c4 : bv 32 := 0x04040223.
Lemma F_5e8c4 : fetch_word Asan.M.loaded_segments (0x5e914 : word) = Some W_5e8c4.
Proof. vm_refl. Qed.
Lemma D_5e8c4 : decode_any W_5e8c4 = Some (Store SZ1 8 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8c8 : bv 32 := 0x00100593.
Lemma F_5e8c8 : fetch_word Asan.M.loaded_segments (0x5e918 : word) = Some W_5e8c8.
Proof. vm_refl. Qed.
Lemma D_5e8c8 : decode_any W_5e8c8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8cc : bv 32 := 0x00058513.
Lemma F_5e8cc : fetch_word Asan.M.loaded_segments (0x5e91c : word) = Some W_5e8cc.
Proof. vm_refl. Qed.
Lemma D_5e8cc : decode_any W_5e8cc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d0 : bv 32 := 0x03813083.
Lemma F_5e8d0 : fetch_word Asan.M.loaded_segments (0x5e920 : word) = Some W_5e8d0.
Proof. vm_refl. Qed.
Lemma D_5e8d0 : decode_any W_5e8d0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d4 : bv 32 := 0x03013403.
Lemma F_5e8d4 : fetch_word Asan.M.loaded_segments (0x5e924 : word) = Some W_5e8d4.
Proof. vm_refl. Qed.
Lemma D_5e8d4 : decode_any W_5e8d4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d8 : bv 32 := 0x02813483.
Lemma F_5e8d8 : fetch_word Asan.M.loaded_segments (0x5e928 : word) = Some W_5e8d8.
Proof. vm_refl. Qed.
Lemma D_5e8d8 : decode_any W_5e8d8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8dc : bv 32 := 0x02013903.
Lemma F_5e8dc : fetch_word Asan.M.loaded_segments (0x5e92c : word) = Some W_5e8dc.
Proof. vm_refl. Qed.
Lemma D_5e8dc : decode_any W_5e8dc = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e0 : bv 32 := 0x01813983.
Lemma F_5e8e0 : fetch_word Asan.M.loaded_segments (0x5e930 : word) = Some W_5e8e0.
Proof. vm_refl. Qed.
Lemma D_5e8e0 : decode_any W_5e8e0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e4 : bv 32 := 0x01013a03.
Lemma F_5e8e4 : fetch_word Asan.M.loaded_segments (0x5e934 : word) = Some W_5e8e4.
Proof. vm_refl. Qed.
Lemma D_5e8e4 : decode_any W_5e8e4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e8 : bv 32 := 0x00813a83.
Lemma F_5e8e8 : fetch_word Asan.M.loaded_segments (0x5e938 : word) = Some W_5e8e8.
Proof. vm_refl. Qed.
Lemma D_5e8e8 : decode_any W_5e8e8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8ec : bv 32 := 0x00013b03.
Lemma F_5e8ec : fetch_word Asan.M.loaded_segments (0x5e93c : word) = Some W_5e8ec.
Proof. vm_refl. Qed.
Lemma D_5e8ec : decode_any W_5e8ec = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f0 : bv 32 := 0x04010113.
Lemma F_5e8f0 : fetch_word Asan.M.loaded_segments (0x5e940 : word) = Some W_5e8f0.
Proof. vm_refl. Qed.
Lemma D_5e8f0 : decode_any W_5e8f0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f4 : bv 32 := 0x00008067.
Lemma F_5e8f4 : fetch_word Asan.M.loaded_segments (0x5e944 : word) = Some W_5e8f4.
Proof. vm_refl. Qed.
Lemma D_5e8f4 : decode_any W_5e8f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e918 : bv 32 := 0x02852583.
Lemma F_5e918 : fetch_word Asan.M.loaded_segments (0x5e968 : word) = Some W_5e918.
Proof. vm_refl. Qed.
Lemma D_5e918 : decode_any W_5e918 = Some (Load SZ4 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e91c : bv 32 := 0x0c05c263.
Lemma F_5e91c : fetch_word Asan.M.loaded_segments (0x5e96c : word) = Some W_5e91c.
Proof. vm_refl. Qed.
Lemma D_5e91c : decode_any W_5e91c = Some (Branch BC_LT 11 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e0 : bv 32 := 0x00000a13.
Lemma F_5e9e0 : fetch_word Asan.M.loaded_segments (0x5ea30 : word) = Some W_5e9e0.
Proof. vm_refl. Qed.
Lemma D_5e9e0 : decode_any W_5e9e0 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e4 : bv 32 := 0xd7dff06f.
Lemma F_5e9e4 : fetch_word Asan.M.loaded_segments (0x5ea34 : word) = Some W_5e9e4.
Proof. vm_refl. Qed.
Lemma D_5e9e4 : decode_any W_5e9e4 = Some (Jal 0 2096508, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea2c : bv 32 := 0xff010113.
Lemma F_5ea2c : fetch_word Asan.M.loaded_segments (0x5ea7c : word) = Some W_5ea2c.
Proof. vm_refl. Qed.
Lemma D_5ea2c : decode_any W_5ea2c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea30 : bv 32 := 0x00113423.
Lemma F_5ea30 : fetch_word Asan.M.loaded_segments (0x5ea80 : word) = Some W_5ea30.
Proof. vm_refl. Qed.
Lemma D_5ea30 : decode_any W_5ea30 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea34 : bv 32 := 0x02051693.
Lemma F_5ea34 : fetch_word Asan.M.loaded_segments (0x5ea84 : word) = Some W_5ea34.
Proof. vm_refl. Qed.
Lemma D_5ea34 : decode_any W_5ea34 = Some (ShiftImm ALU_SLL 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea38 : bv 32 := 0x00f00593.
Lemma F_5ea38 : fetch_word Asan.M.loaded_segments (0x5ea88 : word) = Some W_5ea38.
Proof. vm_refl. Qed.
Lemma D_5ea38 : decode_any W_5ea38 = Some (OpImm ALU_ADD 11 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea3c : bv 32 := 0x0206d693.
Lemma F_5ea3c : fetch_word Asan.M.loaded_segments (0x5ea8c : word) = Some W_5ea3c.
Proof. vm_refl. Qed.
Lemma D_5ea3c : decode_any W_5ea3c = Some (ShiftImm ALU_SRL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea40 : bv 32 := 0x06a5f663.
Lemma F_5ea40 : fetch_word Asan.M.loaded_segments (0x5ea90 : word) = Some W_5ea40.
Proof. vm_refl. Qed.
Lemma D_5ea40 : decode_any W_5ea40 = Some (Branch BC_GEU 11 10 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea44 : bv 32 := 0x000015b7.
Lemma F_5ea44 : fetch_word Asan.M.loaded_segments (0x5ea94 : word) = Some W_5ea44.
Proof. vm_refl. Qed.
Lemma D_5ea44 : decode_any W_5ea44 = Some (Lui 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea48 : bv 32 := 0x8015859b.
Lemma F_5ea48 : fetch_word Asan.M.loaded_segments (0x5ea98 : word) = Some W_5ea48.
Proof. vm_refl. Qed.
Lemma D_5ea48 : decode_any W_5ea48 = Some (OpImm32 11 11 2049, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea4c : bv 32 := 0x06b57e63.
Lemma F_5ea4c : fetch_word Asan.M.loaded_segments (0x5ea9c : word) = Some W_5ea4c.
Proof. vm_refl. Qed.
Lemma D_5ea4c : decode_any W_5ea4c = Some (Branch BC_GEU 10 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea50 : bv 32 := 0xfff68593.
Lemma F_5ea50 : fetch_word Asan.M.loaded_segments (0x5eaa0 : word) = Some W_5ea50.
Proof. vm_refl. Qed.
Lemma D_5ea50 : decode_any W_5ea50 = Some (OpImm ALU_ADD 11 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea54 : bv 32 := 0x00b6f5b3.
Lemma F_5ea54 : fetch_word Asan.M.loaded_segments (0x5eaa4 : word) = Some W_5ea54.
Proof. vm_refl. Qed.
Lemma D_5ea54 : decode_any W_5ea54 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea58 : bv 32 := 0x08059863.
Lemma F_5ea58 : fetch_word Asan.M.loaded_segments (0x5eaa8 : word) = Some W_5ea58.
Proof. vm_refl. Qed.
Lemma D_5ea58 : decode_any W_5ea58 = Some (Branch BC_NE 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea5c : bv 32 := 0x40d005b3.
Lemma F_5ea5c : fetch_word Asan.M.loaded_segments (0x5eaac : word) = Some W_5ea5c.
Proof. vm_refl. Qed.
Lemma D_5ea5c : decode_any W_5ea5c = Some (Op ALU_SUB 11 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea60 : bv 32 := 0xfffb2617.
Lemma F_5ea60 : fetch_word Asan.M.loaded_segments (0x5eab0 : word) = Some W_5ea60.
Proof. vm_refl. Qed.
Lemma D_5ea60 : decode_any W_5ea60 = Some (Auipc 12 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea64 : bv 32 := 0x9b063603.
Lemma F_5ea64 : fetch_word Asan.M.loaded_segments (0x5eab4 : word) = Some W_5ea64.
Proof. vm_refl. Qed.
Lemma D_5ea64 : decode_any W_5ea64 = Some (Load SZ8 true 12 12 2480, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea68 : bv 32 := 0xfffb2717.
Lemma F_5ea68 : fetch_word Asan.M.loaded_segments (0x5eab8 : word) = Some W_5ea68.
Proof. vm_refl. Qed.
Lemma D_5ea68 : decode_any W_5ea68 = Some (Auipc 14 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea6c : bv 32 := 0x00b6f5b3.
Lemma F_5ea6c : fetch_word Asan.M.loaded_segments (0x5eabc : word) = Some W_5ea6c.
Proof. vm_refl. Qed.
Lemma D_5ea6c : decode_any W_5ea6c = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea70 : bv 32 := 0xb2070713.
Lemma F_5ea70 : fetch_word Asan.M.loaded_segments (0x5eac0 : word) = Some W_5ea70.
Proof. vm_refl. Qed.
Lemma D_5ea70 : decode_any W_5ea70 = Some (OpImm ALU_ADD 14 14 2848, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea74 : bv 32 := 0x02c585b3.
Lemma F_5ea74 : fetch_word Asan.M.loaded_segments (0x5eac4 : word) = Some W_5ea74.
Proof. vm_refl. Qed.
Lemma D_5ea74 : decode_any W_5ea74 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea78 : bv 32 := 0x03a5d593.
Lemma F_5ea78 : fetch_word Asan.M.loaded_segments (0x5eac8 : word) = Some W_5ea78.
Proof. vm_refl. Qed.
Lemma D_5ea78 : decode_any W_5ea78 = Some (ShiftImm ALU_SRL 11 11 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea7c : bv 32 := 0x00b705b3.
Lemma F_5ea7c : fetch_word Asan.M.loaded_segments (0x5eacc : word) = Some W_5ea7c.
Proof. vm_refl. Qed.
Lemma D_5ea7c : decode_any W_5ea7c = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea80 : bv 32 := 0x0005c603.
Lemma F_5ea80 : fetch_word Asan.M.loaded_segments (0x5ead0 : word) = Some W_5ea80.
Proof. vm_refl. Qed.
Lemma D_5ea80 : decode_any W_5ea80 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea84 : bv 32 := 0xffc60593.
Lemma F_5ea84 : fetch_word Asan.M.loaded_segments (0x5ead4 : word) = Some W_5ea84.
Proof. vm_refl. Qed.
Lemma D_5ea84 : decode_any W_5ea84 = Some (OpImm ALU_ADD 11 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea88 : bv 32 := 0x00800713.
Lemma F_5ea88 : fetch_word Asan.M.loaded_segments (0x5ead8 : word) = Some W_5ea88.
Proof. vm_refl. Qed.
Lemma D_5ea88 : decode_any W_5ea88 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea8c : bv 32 := 0x06e5fe63.
Lemma F_5ea8c : fetch_word Asan.M.loaded_segments (0x5eadc : word) = Some W_5ea8c.
Proof. vm_refl. Qed.
Lemma D_5ea8c : decode_any W_5ea8c = Some (Branch BC_GEU 11 14 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea90 : bv 32 := 0x00100713.
Lemma F_5ea90 : fetch_word Asan.M.loaded_segments (0x5eae0 : word) = Some W_5ea90.
Proof. vm_refl. Qed.
Lemma D_5ea90 : decode_any W_5ea90 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea94 : bv 32 := 0x00c7173b.
Lemma F_5ea94 : fetch_word Asan.M.loaded_segments (0x5eae4 : word) = Some W_5ea94.
Proof. vm_refl. Qed.
Lemma D_5ea94 : decode_any W_5ea94 = Some (Op32 ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea98 : bv 32 := 0x08e51a63.
Lemma F_5ea98 : fetch_word Asan.M.loaded_segments (0x5eae8 : word) = Some W_5ea98.
Proof. vm_refl. Qed.
Lemma D_5ea98 : decode_any W_5ea98 = Some (Branch BC_NE 10 14 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea9c : bv 32 := 0x00058513.
Lemma F_5ea9c : fetch_word Asan.M.loaded_segments (0x5eaec : word) = Some W_5ea9c.
Proof. vm_refl. Qed.
Lemma D_5ea9c : decode_any W_5ea9c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa0 : bv 32 := 0x00813083.
Lemma F_5eaa0 : fetch_word Asan.M.loaded_segments (0x5eaf0 : word) = Some W_5eaa0.
Proof. vm_refl. Qed.
Lemma D_5eaa0 : decode_any W_5eaa0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa4 : bv 32 := 0x01010113.
Lemma F_5eaa4 : fetch_word Asan.M.loaded_segments (0x5eaf4 : word) = Some W_5eaa4.
Proof. vm_refl. Qed.
Lemma D_5eaa4 : decode_any W_5eaa4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa8 : bv 32 := 0x00008067.
Lemma F_5eaa8 : fetch_word Asan.M.loaded_segments (0x5eaf8 : word) = Some W_5eaa8.
Proof. vm_refl. Qed.
Lemma D_5eaa8 : decode_any W_5eaa8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

