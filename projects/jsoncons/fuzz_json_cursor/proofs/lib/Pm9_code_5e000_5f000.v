(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5e000 : bv 32 := 0x3338081b.
Lemma F_5e000 : fetch_word AsanUbsan.M.loaded_segments (0x5e048 : word) = Some W_5e000.
Proof. vm_refl. Qed.
Lemma D_5e000 : decode_any W_5e000 = Some (OpImm32 16 16 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e004 : bv 32 := 0xf0f8889b.
Lemma F_5e004 : fetch_word AsanUbsan.M.loaded_segments (0x5e04c : word) = Some W_5e004.
Proof. vm_refl. Qed.
Lemma D_5e004 : decode_any W_5e004 = Some (OpImm32 17 17 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e008 : bv 32 := 0x1012829b.
Lemma F_5e008 : fetch_word AsanUbsan.M.loaded_segments (0x5e050 : word) = Some W_5e008.
Proof. vm_refl. Qed.
Lemma D_5e008 : decode_any W_5e008 = Some (OpImm32 5 5 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e00c : bv 32 := 0x00265313.
Lemma F_5e00c : fetch_word AsanUbsan.M.loaded_segments (0x5e054 : word) = Some W_5e00c.
Proof. vm_refl. Qed.
Lemma D_5e00c : decode_any W_5e00c = Some (ShiftImm ALU_SRL 6 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e010 : bv 32 := 0x00666633.
Lemma F_5e010 : fetch_word AsanUbsan.M.loaded_segments (0x5e058 : word) = Some W_5e010.
Proof. vm_refl. Qed.
Lemma D_5e010 : decode_any W_5e010 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e014 : bv 32 := 0x02079313.
Lemma F_5e014 : fetch_word AsanUbsan.M.loaded_segments (0x5e05c : word) = Some W_5e014.
Proof. vm_refl. Qed.
Lemma D_5e014 : decode_any W_5e014 = Some (ShiftImm ALU_SLL 6 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e018 : bv 32 := 0x006787b3.
Lemma F_5e018 : fetch_word AsanUbsan.M.loaded_segments (0x5e060 : word) = Some W_5e018.
Proof. vm_refl. Qed.
Lemma D_5e018 : decode_any W_5e018 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e01c : bv 32 := 0x02081313.
Lemma F_5e01c : fetch_word AsanUbsan.M.loaded_segments (0x5e064 : word) = Some W_5e01c.
Proof. vm_refl. Qed.
Lemma D_5e01c : decode_any W_5e01c = Some (ShiftImm ALU_SLL 6 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e020 : bv 32 := 0x00680833.
Lemma F_5e020 : fetch_word AsanUbsan.M.loaded_segments (0x5e068 : word) = Some W_5e020.
Proof. vm_refl. Qed.
Lemma D_5e020 : decode_any W_5e020 = Some (Op ALU_ADD 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e024 : bv 32 := 0x02089313.
Lemma F_5e024 : fetch_word AsanUbsan.M.loaded_segments (0x5e06c : word) = Some W_5e024.
Proof. vm_refl. Qed.
Lemma D_5e024 : decode_any W_5e024 = Some (ShiftImm ALU_SLL 6 17 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e028 : bv 32 := 0x006888b3.
Lemma F_5e028 : fetch_word AsanUbsan.M.loaded_segments (0x5e070 : word) = Some W_5e028.
Proof. vm_refl. Qed.
Lemma D_5e028 : decode_any W_5e028 = Some (Op ALU_ADD 17 17 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e02c : bv 32 := 0x02029313.
Lemma F_5e02c : fetch_word AsanUbsan.M.loaded_segments (0x5e074 : word) = Some W_5e02c.
Proof. vm_refl. Qed.
Lemma D_5e02c : decode_any W_5e02c = Some (ShiftImm ALU_SLL 6 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e030 : bv 32 := 0x006282b3.
Lemma F_5e030 : fetch_word AsanUbsan.M.loaded_segments (0x5e078 : word) = Some W_5e030.
Proof. vm_refl. Qed.
Lemma D_5e030 : decode_any W_5e030 = Some (Op ALU_ADD 5 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e034 : bv 32 := 0x00465313.
Lemma F_5e034 : fetch_word AsanUbsan.M.loaded_segments (0x5e07c : word) = Some W_5e034.
Proof. vm_refl. Qed.
Lemma D_5e034 : decode_any W_5e034 = Some (ShiftImm ALU_SRL 6 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e038 : bv 32 := 0x00666633.
Lemma F_5e038 : fetch_word AsanUbsan.M.loaded_segments (0x5e080 : word) = Some W_5e038.
Proof. vm_refl. Qed.
Lemma D_5e038 : decode_any W_5e038 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e03c : bv 32 := 0x00865313.
Lemma F_5e03c : fetch_word AsanUbsan.M.loaded_segments (0x5e084 : word) = Some W_5e03c.
Proof. vm_refl. Qed.
Lemma D_5e03c : decode_any W_5e03c = Some (ShiftImm ALU_SRL 6 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e040 : bv 32 := 0x00666633.
Lemma F_5e040 : fetch_word AsanUbsan.M.loaded_segments (0x5e088 : word) = Some W_5e040.
Proof. vm_refl. Qed.
Lemma D_5e040 : decode_any W_5e040 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e044 : bv 32 := 0x01065313.
Lemma F_5e044 : fetch_word AsanUbsan.M.loaded_segments (0x5e08c : word) = Some W_5e044.
Proof. vm_refl. Qed.
Lemma D_5e044 : decode_any W_5e044 = Some (ShiftImm ALU_SRL 6 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e048 : bv 32 := 0x00666633.
Lemma F_5e048 : fetch_word AsanUbsan.M.loaded_segments (0x5e090 : word) = Some W_5e048.
Proof. vm_refl. Qed.
Lemma D_5e048 : decode_any W_5e048 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e04c : bv 32 := 0x02065313.
Lemma F_5e04c : fetch_word AsanUbsan.M.loaded_segments (0x5e094 : word) = Some W_5e04c.
Proof. vm_refl. Qed.
Lemma D_5e04c : decode_any W_5e04c = Some (ShiftImm ALU_SRL 6 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e050 : bv 32 := 0x00666633.
Lemma F_5e050 : fetch_word AsanUbsan.M.loaded_segments (0x5e098 : word) = Some W_5e050.
Proof. vm_refl. Qed.
Lemma D_5e050 : decode_any W_5e050 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e054 : bv 32 := 0xfff64613.
Lemma F_5e054 : fetch_word AsanUbsan.M.loaded_segments (0x5e09c : word) = Some W_5e054.
Proof. vm_refl. Qed.
Lemma D_5e054 : decode_any W_5e054 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e058 : bv 32 := 0x00165313.
Lemma F_5e058 : fetch_word AsanUbsan.M.loaded_segments (0x5e0a0 : word) = Some W_5e058.
Proof. vm_refl. Qed.
Lemma D_5e058 : decode_any W_5e058 = Some (ShiftImm ALU_SRL 6 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e05c : bv 32 := 0x00f377b3.
Lemma F_5e05c : fetch_word AsanUbsan.M.loaded_segments (0x5e0a4 : word) = Some W_5e05c.
Proof. vm_refl. Qed.
Lemma D_5e05c : decode_any W_5e05c = Some (Op ALU_AND 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e060 : bv 32 := 0x40f60633.
Lemma F_5e060 : fetch_word AsanUbsan.M.loaded_segments (0x5e0a8 : word) = Some W_5e060.
Proof. vm_refl. Qed.
Lemma D_5e060 : decode_any W_5e060 = Some (Op ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e064 : bv 32 := 0x010677b3.
Lemma F_5e064 : fetch_word AsanUbsan.M.loaded_segments (0x5e0ac : word) = Some W_5e064.
Proof. vm_refl. Qed.
Lemma D_5e064 : decode_any W_5e064 = Some (Op ALU_AND 15 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e068 : bv 32 := 0x00265613.
Lemma F_5e068 : fetch_word AsanUbsan.M.loaded_segments (0x5e0b0 : word) = Some W_5e068.
Proof. vm_refl. Qed.
Lemma D_5e068 : decode_any W_5e068 = Some (ShiftImm ALU_SRL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e06c : bv 32 := 0x01067633.
Lemma F_5e06c : fetch_word AsanUbsan.M.loaded_segments (0x5e0b4 : word) = Some W_5e06c.
Proof. vm_refl. Qed.
Lemma D_5e06c : decode_any W_5e06c = Some (Op ALU_AND 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e070 : bv 32 := 0x00c78633.
Lemma F_5e070 : fetch_word AsanUbsan.M.loaded_segments (0x5e0b8 : word) = Some W_5e070.
Proof. vm_refl. Qed.
Lemma D_5e070 : decode_any W_5e070 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e074 : bv 32 := 0x00465793.
Lemma F_5e074 : fetch_word AsanUbsan.M.loaded_segments (0x5e0bc : word) = Some W_5e074.
Proof. vm_refl. Qed.
Lemma D_5e074 : decode_any W_5e074 = Some (ShiftImm ALU_SRL 15 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e078 : bv 32 := 0x00f60633.
Lemma F_5e078 : fetch_word AsanUbsan.M.loaded_segments (0x5e0c0 : word) = Some W_5e078.
Proof. vm_refl. Qed.
Lemma D_5e078 : decode_any W_5e078 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e07c : bv 32 := 0x03e00793.
Lemma F_5e07c : fetch_word AsanUbsan.M.loaded_segments (0x5e0c4 : word) = Some W_5e07c.
Proof. vm_refl. Qed.
Lemma D_5e07c : decode_any W_5e07c = Some (OpImm ALU_ADD 15 0 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e080 : bv 32 := 0x01167633.
Lemma F_5e080 : fetch_word AsanUbsan.M.loaded_segments (0x5e0c8 : word) = Some W_5e080.
Proof. vm_refl. Qed.
Lemma D_5e080 : decode_any W_5e080 = Some (Op ALU_AND 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e084 : bv 32 := 0xfff00813.
Lemma F_5e084 : fetch_word AsanUbsan.M.loaded_segments (0x5e0cc : word) = Some W_5e084.
Proof. vm_refl. Qed.
Lemma D_5e084 : decode_any W_5e084 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e088 : bv 32 := 0x02560633.
Lemma F_5e088 : fetch_word AsanUbsan.M.loaded_segments (0x5e0d0 : word) = Some W_5e088.
Proof. vm_refl. Qed.
Lemma D_5e088 : decode_any W_5e088 = Some (Mul M_MUL 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e08c : bv 32 := 0x03865613.
Lemma F_5e08c : fetch_word AsanUbsan.M.loaded_segments (0x5e0d4 : word) = Some W_5e08c.
Proof. vm_refl. Qed.
Lemma D_5e08c : decode_any W_5e08c = Some (ShiftImm ALU_SRL 12 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e090 : bv 32 := 0x40c787bb.
Lemma F_5e090 : fetch_word AsanUbsan.M.loaded_segments (0x5e0d8 : word) = Some W_5e090.
Proof. vm_refl. Qed.
Lemma D_5e090 : decode_any W_5e090 = Some (Op32 ALU_SUB 15 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e094 : bv 32 := 0x00161613.
Lemma F_5e094 : fetch_word AsanUbsan.M.loaded_segments (0x5e0dc : word) = Some W_5e094.
Proof. vm_refl. Qed.
Lemma D_5e094 : decode_any W_5e094 = Some (ShiftImm ALU_SLL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e098 : bv 32 := 0x00f758b3.
Lemma F_5e098 : fetch_word AsanUbsan.M.loaded_segments (0x5e0e0 : word) = Some W_5e098.
Proof. vm_refl. Qed.
Lemma D_5e098 : decode_any W_5e098 = Some (Op ALU_SRL 17 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e09c : bv 32 := 0x00f817bb.
Lemma F_5e09c : fetch_word AsanUbsan.M.loaded_segments (0x5e0e4 : word) = Some W_5e09c.
Proof. vm_refl. Qed.
Lemma D_5e09c : decode_any W_5e09c = Some (Op32 ALU_SLL 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a0 : bv 32 := 0x07e64613.
Lemma F_5e0a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e0e8 : word) = Some W_5e0a0.
Proof. vm_refl. Qed.
Lemma D_5e0a0 : decode_any W_5e0a0 = Some (OpImm ALU_XOR 12 12 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a4 : bv 32 := 0x0018f813.
Lemma F_5e0a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e0ec : word) = Some W_5e0a4.
Proof. vm_refl. Qed.
Lemma D_5e0a4 : decode_any W_5e0a4 = Some (OpImm ALU_AND 16 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a8 : bv 32 := 0xfff7c793.
Lemma F_5e0a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e0f0 : word) = Some W_5e0a8.
Proof. vm_refl. Qed.
Lemma D_5e0a8 : decode_any W_5e0a8 = Some (OpImm ALU_XOR 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0ac : bv 32 := 0x00f77733.
Lemma F_5e0ac : fetch_word AsanUbsan.M.loaded_segments (0x5e0f4 : word) = Some W_5e0ac.
Proof. vm_refl. Qed.
Lemma D_5e0ac : decode_any W_5e0ac = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b0 : bv 32 := 0x01066633.
Lemma F_5e0b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e0f8 : word) = Some W_5e0b0.
Proof. vm_refl. Qed.
Lemma D_5e0b0 : decode_any W_5e0b0 = Some (Op ALU_OR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b4 : bv 32 := 0x00e03733.
Lemma F_5e0b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e0fc : word) = Some W_5e0b4.
Proof. vm_refl. Qed.
Lemma D_5e0b4 : decode_any W_5e0b4 = Some (Op ALU_SLTU 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b8 : bv 32 := 0x00e60633.
Lemma F_5e0b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e100 : word) = Some W_5e0b8.
Proof. vm_refl. Qed.
Lemma D_5e0b8 : decode_any W_5e0b8 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0bc : bv 32 := 0xffe60413.
Lemma F_5e0bc : fetch_word AsanUbsan.M.loaded_segments (0x5e104 : word) = Some W_5e0bc.
Proof. vm_refl. Qed.
Lemma D_5e0bc : decode_any W_5e0bc = Some (OpImm ALU_ADD 8 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c0 : bv 32 := 0x0a040063.
Lemma F_5e0c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e108 : word) = Some W_5e0c0.
Proof. vm_refl. Qed.
Lemma D_5e0c0 : decode_any W_5e0c0 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c4 : bv 32 := 0x02000613.
Lemma F_5e0c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e10c : word) = Some W_5e0c4.
Proof. vm_refl. Qed.
Lemma D_5e0c4 : decode_any W_5e0c4 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c8 : bv 32 := 0x0cc47a63.
Lemma F_5e0c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e110 : word) = Some W_5e0c8.
Proof. vm_refl. Qed.
Lemma D_5e0c8 : decode_any W_5e0c8 = Some (Branch BC_GEU 8 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0cc : bv 32 := 0x05000613.
Lemma F_5e0cc : fetch_word AsanUbsan.M.loaded_segments (0x5e114 : word) = Some W_5e0cc.
Proof. vm_refl. Qed.
Lemma D_5e0cc : decode_any W_5e0cc = Some (OpImm ALU_ADD 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d0 : bv 32 := 0x02c404b3.
Lemma F_5e0d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e118 : word) = Some W_5e0d0.
Proof. vm_refl. Qed.
Lemma D_5e0d0 : decode_any W_5e0d0 = Some (Mul M_MUL 9 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d4 : bv 32 := 0x009584b3.
Lemma F_5e0d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e11c : word) = Some W_5e0d4.
Proof. vm_refl. Qed.
Lemma D_5e0d4 : decode_any W_5e0d4 = Some (Op ALU_ADD 9 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d8 : bv 32 := 0x0004a603.
Lemma F_5e0d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e120 : word) = Some W_5e0d8.
Proof. vm_refl. Qed.
Lemma D_5e0d8 : decode_any W_5e0d8 = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0dc : bv 32 := 0x0e060063.
Lemma F_5e0dc : fetch_word AsanUbsan.M.loaded_segments (0x5e124 : word) = Some W_5e0dc.
Proof. vm_refl. Qed.
Lemma D_5e0dc : decode_any W_5e0dc = Some (Branch BC_EQ 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e0 : bv 32 := 0xfff60613.
Lemma F_5e0e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e128 : word) = Some W_5e0e0.
Proof. vm_refl. Qed.
Lemma D_5e0e0 : decode_any W_5e0e0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e4 : bv 32 := 0x7ff58593.
Lemma F_5e0e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e12c : word) = Some W_5e0e4.
Proof. vm_refl. Qed.
Lemma D_5e0e4 : decode_any W_5e0e4 = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e8 : bv 32 := 0x02061713.
Lemma F_5e0e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e130 : word) = Some W_5e0e8.
Proof. vm_refl. Qed.
Lemma D_5e0e8 : decode_any W_5e0e8 = Some (ShiftImm ALU_SLL 14 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0ec : bv 32 := 0x00c4a023.
Lemma F_5e0ec : fetch_word AsanUbsan.M.loaded_segments (0x5e134 : word) = Some W_5e0ec.
Proof. vm_refl. Qed.
Lemma D_5e0ec : decode_any W_5e0ec = Some (Store SZ4 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f0 : bv 32 := 0x21158593.
Lemma F_5e0f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e138 : word) = Some W_5e0f0.
Proof. vm_refl. Qed.
Lemma D_5e0f0 : decode_any W_5e0f0 = Some (OpImm ALU_ADD 11 11 529, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f4 : bv 32 := 0x0084b603.
Lemma F_5e0f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e13c : word) = Some W_5e0f4.
Proof. vm_refl. Qed.
Lemma D_5e0f4 : decode_any W_5e0f4 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f8 : bv 32 := 0x01e75713.
Lemma F_5e0f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e140 : word) = Some W_5e0f8.
Proof. vm_refl. Qed.
Lemma D_5e0f8 : decode_any W_5e0f8 = Some (ShiftImm ALU_SRL 14 14 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0fc : bv 32 := 0x00e48733.
Lemma F_5e0fc : fetch_word AsanUbsan.M.loaded_segments (0x5e144 : word) = Some W_5e0fc.
Proof. vm_refl. Qed.
Lemma D_5e0fc : decode_any W_5e0fc = Some (Op ALU_ADD 14 9 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e100 : bv 32 := 0x01076703.
Lemma F_5e100 : fetch_word AsanUbsan.M.loaded_segments (0x5e148 : word) = Some W_5e100.
Proof. vm_refl. Qed.
Lemma D_5e100 : decode_any W_5e100 = Some (Load SZ4 false 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e104 : bv 32 := 0x00c5b02f.
Lemma F_5e104 : fetch_word AsanUbsan.M.loaded_segments (0x5e14c : word) = Some W_5e104.
Proof. vm_refl. Qed.
Lemma D_5e104 : decode_any W_5e104 = Some (Amo AMO_ADD AD false false 0 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e108 : bv 32 := 0x02053503.
Lemma F_5e108 : fetch_word AsanUbsan.M.loaded_segments (0x5e150 : word) = Some W_5e108.
Proof. vm_refl. Qed.
Lemma D_5e108 : decode_any W_5e108 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e10c : bv 32 := 0x02041413.
Lemma F_5e10c : fetch_word AsanUbsan.M.loaded_segments (0x5e154 : word) = Some W_5e10c.
Proof. vm_refl. Qed.
Lemma D_5e10c : decode_any W_5e10c = Some (ShiftImm ALU_SLL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e110 : bv 32 := 0x00471713.
Lemma F_5e110 : fetch_word AsanUbsan.M.loaded_segments (0x5e158 : word) = Some W_5e110.
Proof. vm_refl. Qed.
Lemma D_5e110 : decode_any W_5e110 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e114 : bv 32 := 0x00a40533.
Lemma F_5e114 : fetch_word AsanUbsan.M.loaded_segments (0x5e15c : word) = Some W_5e114.
Proof. vm_refl. Qed.
Lemma D_5e114 : decode_any W_5e114 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e118 : bv 32 := 0x00a70533.
Lemma F_5e118 : fetch_word AsanUbsan.M.loaded_segments (0x5e160 : word) = Some W_5e118.
Proof. vm_refl. Qed.
Lemma D_5e118 : decode_any W_5e118 = Some (Op ALU_ADD 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e11c : bv 32 := 0x00900593.
Lemma F_5e11c : fetch_word AsanUbsan.M.loaded_segments (0x5e164 : word) = Some W_5e11c.
Proof. vm_refl. Qed.
Lemma D_5e11c : decode_any W_5e11c = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e120 : bv 32 := 0x00b6e863.
Lemma F_5e120 : fetch_word AsanUbsan.M.loaded_segments (0x5e168 : word) = Some W_5e120.
Proof. vm_refl. Qed.
Lemma D_5e120 : decode_any W_5e120 = Some (Branch BC_LTU 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e124 : bv 32 := 0xfff68693.
Lemma F_5e124 : fetch_word AsanUbsan.M.loaded_segments (0x5e16c : word) = Some W_5e124.
Proof. vm_refl. Qed.
Lemma D_5e124 : decode_any W_5e124 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e128 : bv 32 := 0x00a6f6b3.
Lemma F_5e128 : fetch_word AsanUbsan.M.loaded_segments (0x5e170 : word) = Some W_5e128.
Proof. vm_refl. Qed.
Lemma D_5e128 : decode_any W_5e128 = Some (Op ALU_AND 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e12c : bv 32 := 0x04069a63.
Lemma F_5e12c : fetch_word AsanUbsan.M.loaded_segments (0x5e174 : word) = Some W_5e12c.
Proof. vm_refl. Qed.
Lemma D_5e12c : decode_any W_5e12c = Some (Branch BC_NE 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e130 : bv 32 := 0x02813083.
Lemma F_5e130 : fetch_word AsanUbsan.M.loaded_segments (0x5e178 : word) = Some W_5e130.
Proof. vm_refl. Qed.
Lemma D_5e130 : decode_any W_5e130 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e134 : bv 32 := 0x02013403.
Lemma F_5e134 : fetch_word AsanUbsan.M.loaded_segments (0x5e17c : word) = Some W_5e134.
Proof. vm_refl. Qed.
Lemma D_5e134 : decode_any W_5e134 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e138 : bv 32 := 0x01813483.
Lemma F_5e138 : fetch_word AsanUbsan.M.loaded_segments (0x5e180 : word) = Some W_5e138.
Proof. vm_refl. Qed.
Lemma D_5e138 : decode_any W_5e138 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e13c : bv 32 := 0x01013903.
Lemma F_5e13c : fetch_word AsanUbsan.M.loaded_segments (0x5e184 : word) = Some W_5e13c.
Proof. vm_refl. Qed.
Lemma D_5e13c : decode_any W_5e13c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e140 : bv 32 := 0x00813983.
Lemma F_5e140 : fetch_word AsanUbsan.M.loaded_segments (0x5e188 : word) = Some W_5e140.
Proof. vm_refl. Qed.
Lemma D_5e140 : decode_any W_5e140 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e144 : bv 32 := 0x00013a03.
Lemma F_5e144 : fetch_word AsanUbsan.M.loaded_segments (0x5e18c : word) = Some W_5e144.
Proof. vm_refl. Qed.
Lemma D_5e144 : decode_any W_5e144 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e148 : bv 32 := 0x03010113.
Lemma F_5e148 : fetch_word AsanUbsan.M.loaded_segments (0x5e190 : word) = Some W_5e148.
Proof. vm_refl. Qed.
Lemma D_5e148 : decode_any W_5e148 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e14c : bv 32 := 0x00008067.
Lemma F_5e14c : fetch_word AsanUbsan.M.loaded_segments (0x5e194 : word) = Some W_5e14c.
Proof. vm_refl. Qed.
Lemma D_5e14c : decode_any W_5e14c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1bc : bv 32 := 0x00068913.
Lemma F_5e1bc : fetch_word AsanUbsan.M.loaded_segments (0x5e204 : word) = Some W_5e1bc.
Proof. vm_refl. Qed.
Lemma D_5e1bc : decode_any W_5e1bc = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1c0 : bv 32 := 0x00050613.
Lemma F_5e1c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e208 : word) = Some W_5e1c0.
Proof. vm_refl. Qed.
Lemma D_5e1c0 : decode_any W_5e1c0 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1c4 : bv 32 := 0x00058993.
Lemma F_5e1c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e20c : word) = Some W_5e1c4.
Proof. vm_refl. Qed.
Lemma D_5e1c4 : decode_any W_5e1c4 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1c8 : bv 32 := 0x00058513.
Lemma F_5e1c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e210 : word) = Some W_5e1c8.
Proof. vm_refl. Qed.
Lemma D_5e1c8 : decode_any W_5e1c8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1cc : bv 32 := 0x00048593.
Lemma F_5e1cc : fetch_word AsanUbsan.M.loaded_segments (0x5e214 : word) = Some W_5e1cc.
Proof. vm_refl. Qed.
Lemma D_5e1cc : decode_any W_5e1cc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1d0 : bv 32 := 0x00060a13.
Lemma F_5e1d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e218 : word) = Some W_5e1d0.
Proof. vm_refl. Qed.
Lemma D_5e1d0 : decode_any W_5e1d0 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1d4 : bv 32 := 0x00040693.
Lemma F_5e1d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e21c : word) = Some W_5e1d4.
Proof. vm_refl. Qed.
Lemma D_5e1d4 : decode_any W_5e1d4 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1d8 : bv 32 := 0x4a4000ef.
Lemma F_5e1d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e220 : word) = Some W_5e1d8.
Proof. vm_refl. Qed.
Lemma D_5e1d8 : decode_any W_5e1d8 = Some (Jal 1 1188, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1dc : bv 32 := 0x00050c63.
Lemma F_5e1dc : fetch_word AsanUbsan.M.loaded_segments (0x5e224 : word) = Some W_5e1dc.
Proof. vm_refl. Qed.
Lemma D_5e1dc : decode_any W_5e1dc = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1e0 : bv 32 := 0x0004a603.
Lemma F_5e1e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e228 : word) = Some W_5e1e0.
Proof. vm_refl. Qed.
Lemma D_5e1e0 : decode_any W_5e1e0 = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1e4 : bv 32 := 0x00090693.
Lemma F_5e1e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e22c : word) = Some W_5e1e4.
Proof. vm_refl. Qed.
Lemma D_5e1e4 : decode_any W_5e1e4 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1e8 : bv 32 := 0x000a0513.
Lemma F_5e1e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e230 : word) = Some W_5e1e8.
Proof. vm_refl. Qed.
Lemma D_5e1e8 : decode_any W_5e1e8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1ec : bv 32 := 0x00098593.
Lemma F_5e1ec : fetch_word AsanUbsan.M.loaded_segments (0x5e234 : word) = Some W_5e1ec.
Proof. vm_refl. Qed.
Lemma D_5e1ec : decode_any W_5e1ec = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1f0 : bv 32 := 0xef1ff06f.
Lemma F_5e1f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e238 : word) = Some W_5e1f0.
Proof. vm_refl. Qed.
Lemma D_5e1f0 : decode_any W_5e1f0 = Some (Jal 0 2096880, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e204 : bv 32 := 0xfa010113.
Lemma F_5e204 : fetch_word AsanUbsan.M.loaded_segments (0x5e24c : word) = Some W_5e204.
Proof. vm_refl. Qed.
Lemma D_5e204 : decode_any W_5e204 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e208 : bv 32 := 0x04113c23.
Lemma F_5e208 : fetch_word AsanUbsan.M.loaded_segments (0x5e250 : word) = Some W_5e208.
Proof. vm_refl. Qed.
Lemma D_5e208 : decode_any W_5e208 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e20c : bv 32 := 0x04813823.
Lemma F_5e20c : fetch_word AsanUbsan.M.loaded_segments (0x5e254 : word) = Some W_5e20c.
Proof. vm_refl. Qed.
Lemma D_5e20c : decode_any W_5e20c = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e210 : bv 32 := 0x04913423.
Lemma F_5e210 : fetch_word AsanUbsan.M.loaded_segments (0x5e258 : word) = Some W_5e210.
Proof. vm_refl. Qed.
Lemma D_5e210 : decode_any W_5e210 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e214 : bv 32 := 0x05213023.
Lemma F_5e214 : fetch_word AsanUbsan.M.loaded_segments (0x5e25c : word) = Some W_5e214.
Proof. vm_refl. Qed.
Lemma D_5e214 : decode_any W_5e214 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e218 : bv 32 := 0x03313c23.
Lemma F_5e218 : fetch_word AsanUbsan.M.loaded_segments (0x5e260 : word) = Some W_5e218.
Proof. vm_refl. Qed.
Lemma D_5e218 : decode_any W_5e218 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e21c : bv 32 := 0x03413823.
Lemma F_5e21c : fetch_word AsanUbsan.M.loaded_segments (0x5e264 : word) = Some W_5e21c.
Proof. vm_refl. Qed.
Lemma D_5e21c : decode_any W_5e21c = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e220 : bv 32 := 0x03513423.
Lemma F_5e220 : fetch_word AsanUbsan.M.loaded_segments (0x5e268 : word) = Some W_5e220.
Proof. vm_refl. Qed.
Lemma D_5e220 : decode_any W_5e220 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e224 : bv 32 := 0x03613023.
Lemma F_5e224 : fetch_word AsanUbsan.M.loaded_segments (0x5e26c : word) = Some W_5e224.
Proof. vm_refl. Qed.
Lemma D_5e224 : decode_any W_5e224 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e228 : bv 32 := 0x01713c23.
Lemma F_5e228 : fetch_word AsanUbsan.M.loaded_segments (0x5e270 : word) = Some W_5e228.
Proof. vm_refl. Qed.
Lemma D_5e228 : decode_any W_5e228 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e22c : bv 32 := 0x01813823.
Lemma F_5e22c : fetch_word AsanUbsan.M.loaded_segments (0x5e274 : word) = Some W_5e22c.
Proof. vm_refl. Qed.
Lemma D_5e22c : decode_any W_5e22c = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e230 : bv 32 := 0x01913423.
Lemma F_5e230 : fetch_word AsanUbsan.M.loaded_segments (0x5e278 : word) = Some W_5e230.
Proof. vm_refl. Qed.
Lemma D_5e230 : decode_any W_5e230 = Some (Store SZ8 2 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e234 : bv 32 := 0x00058413.
Lemma F_5e234 : fetch_word AsanUbsan.M.loaded_segments (0x5e27c : word) = Some W_5e234.
Proof. vm_refl. Qed.
Lemma D_5e234 : decode_any W_5e234 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e238 : bv 32 := 0xfff68c13.
Lemma F_5e238 : fetch_word AsanUbsan.M.loaded_segments (0x5e280 : word) = Some W_5e238.
Proof. vm_refl. Qed.
Lemma D_5e238 : decode_any W_5e238 = Some (OpImm ALU_ADD 24 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e23c : bv 32 := 0x0186f5b3.
Lemma F_5e23c : fetch_word AsanUbsan.M.loaded_segments (0x5e284 : word) = Some W_5e23c.
Proof. vm_refl. Qed.
Lemma D_5e23c : decode_any W_5e23c = Some (Op ALU_AND 11 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e240 : bv 32 := 0x2c059a63.
Lemma F_5e240 : fetch_word AsanUbsan.M.loaded_segments (0x5e288 : word) = Some W_5e240.
Proof. vm_refl. Qed.
Lemma D_5e240 : decode_any W_5e240 = Some (Branch BC_NE 11 0 724, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e244 : bv 32 := 0x00050493.
Lemma F_5e244 : fetch_word AsanUbsan.M.loaded_segments (0x5e28c : word) = Some W_5e244.
Proof. vm_refl. Qed.
Lemma D_5e244 : decode_any W_5e244 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e248 : bv 32 := 0x00053503.
Lemma F_5e248 : fetch_word AsanUbsan.M.loaded_segments (0x5e290 : word) = Some W_5e248.
Proof. vm_refl. Qed.
Lemma D_5e248 : decode_any W_5e248 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e24c : bv 32 := 0xfff50593.
Lemma F_5e24c : fetch_word AsanUbsan.M.loaded_segments (0x5e294 : word) = Some W_5e24c.
Proof. vm_refl. Qed.
Lemma D_5e24c : decode_any W_5e24c = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e250 : bv 32 := 0x00b575b3.
Lemma F_5e250 : fetch_word AsanUbsan.M.loaded_segments (0x5e298 : word) = Some W_5e250.
Proof. vm_refl. Qed.
Lemma D_5e250 : decode_any W_5e250 = Some (Op ALU_AND 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e254 : bv 32 := 0x2e059063.
Lemma F_5e254 : fetch_word AsanUbsan.M.loaded_segments (0x5e29c : word) = Some W_5e254.
Proof. vm_refl. Qed.
Lemma D_5e254 : decode_any W_5e254 = Some (Branch BC_NE 11 0 736, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e258 : bv 32 := 0x00060993.
Lemma F_5e258 : fetch_word AsanUbsan.M.loaded_segments (0x5e2a0 : word) = Some W_5e258.
Proof. vm_refl. Qed.
Lemma D_5e258 : decode_any W_5e258 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e25c : bv 32 := 0x00a605b3.
Lemma F_5e25c : fetch_word AsanUbsan.M.loaded_segments (0x5e2a4 : word) = Some W_5e25c.
Proof. vm_refl. Qed.
Lemma D_5e25c : decode_any W_5e25c = Some (Op ALU_ADD 11 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e260 : bv 32 := 0x40a00633.
Lemma F_5e260 : fetch_word AsanUbsan.M.loaded_segments (0x5e2a8 : word) = Some W_5e260.
Proof. vm_refl. Qed.
Lemma D_5e260 : decode_any W_5e260 = Some (Op ALU_SUB 12 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e264 : bv 32 := 0xfff58593.
Lemma F_5e264 : fetch_word AsanUbsan.M.loaded_segments (0x5e2ac : word) = Some W_5e264.
Proof. vm_refl. Qed.
Lemma D_5e264 : decode_any W_5e264 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e268 : bv 32 := 0x00c5f5b3.
Lemma F_5e268 : fetch_word AsanUbsan.M.loaded_segments (0x5e2b0 : word) = Some W_5e268.
Proof. vm_refl. Qed.
Lemma D_5e268 : decode_any W_5e268 = Some (Op ALU_AND 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e26c : bv 32 := 0x00d53633.
Lemma F_5e26c : fetch_word AsanUbsan.M.loaded_segments (0x5e2b4 : word) = Some W_5e26c.
Proof. vm_refl. Qed.
Lemma D_5e26c : decode_any W_5e26c = Some (Op ALU_SLTU 12 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e270 : bv 32 := 0x40c00633.
Lemma F_5e270 : fetch_word AsanUbsan.M.loaded_segments (0x5e2b8 : word) = Some W_5e270.
Proof. vm_refl. Qed.
Lemma D_5e270 : decode_any W_5e270 = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e274 : bv 32 := 0x00a58533.
Lemma F_5e274 : fetch_word AsanUbsan.M.loaded_segments (0x5e2bc : word) = Some W_5e274.
Proof. vm_refl. Qed.
Lemma D_5e274 : decode_any W_5e274 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e278 : bv 32 := 0x00d67633.
Lemma F_5e278 : fetch_word AsanUbsan.M.loaded_segments (0x5e2c0 : word) = Some W_5e278.
Proof. vm_refl. Qed.
Lemma D_5e278 : decode_any W_5e278 = Some (Op ALU_AND 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e27c : bv 32 := 0x00c50933.
Lemma F_5e27c : fetch_word AsanUbsan.M.loaded_segments (0x5e2c4 : word) = Some W_5e27c.
Proof. vm_refl. Qed.
Lemma D_5e27c : decode_any W_5e27c = Some (Op ALU_ADD 18 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e280 : bv 32 := 0x03397463.
Lemma F_5e280 : fetch_word AsanUbsan.M.loaded_segments (0x5e2c8 : word) = Some W_5e280.
Proof. vm_refl. Qed.
Lemma D_5e280 : decode_any W_5e280 = Some (Branch BC_GEU 18 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2a8 : bv 32 := 0x00068a93.
Lemma F_5e2a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e2f0 : word) = Some W_5e2a8.
Proof. vm_refl. Qed.
Lemma D_5e2a8 : decode_any W_5e2a8 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2ac : bv 32 := 0x000f6517.
Lemma F_5e2ac : fetch_word AsanUbsan.M.loaded_segments (0x5e2f4 : word) = Some W_5e2ac.
Proof. vm_refl. Qed.
Lemma D_5e2ac : decode_any W_5e2ac = Some (Auipc 10 246, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2b0 : bv 32 := 0x1f453503.
Lemma F_5e2b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e2f8 : word) = Some W_5e2b0.
Proof. vm_refl. Qed.
Lemma D_5e2b0 : decode_any W_5e2b0 = Some (Load SZ8 true 10 10 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2b4 : bv 32 := 0x00053583.
Lemma F_5e2b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e2fc : word) = Some W_5e2b4.
Proof. vm_refl. Qed.
Lemma D_5e2b4 : decode_any W_5e2b4 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2b8 : bv 32 := 0x00090513.
Lemma F_5e2b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e300 : word) = Some W_5e2b8.
Proof. vm_refl. Qed.
Lemma D_5e2b8 : decode_any W_5e2b8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2bc : bv 32 := 0x7e4360ef.
Lemma F_5e2bc : fetch_word AsanUbsan.M.loaded_segments (0x5e304 : word) = Some W_5e2bc.
Proof. vm_refl. Qed.
Lemma D_5e2bc : decode_any W_5e2bc = Some (Jal 1 223204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2c0 : bv 32 := 0x22050063.
Lemma F_5e2c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e308 : word) = Some W_5e2c0.
Proof. vm_refl. Qed.
Lemma D_5e2c0 : decode_any W_5e2c0 = Some (Branch BC_EQ 10 0 544, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2c4 : bv 32 := 0x00050a13.
Lemma F_5e2c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e30c : word) = Some W_5e2c4.
Proof. vm_refl. Qed.
Lemma D_5e2c4 : decode_any W_5e2c4 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2c8 : bv 32 := 0x0004b503.
Lemma F_5e2c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e310 : word) = Some W_5e2c8.
Proof. vm_refl. Qed.
Lemma D_5e2c8 : decode_any W_5e2c8 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2cc : bv 32 := 0xfff50593.
Lemma F_5e2cc : fetch_word AsanUbsan.M.loaded_segments (0x5e314 : word) = Some W_5e2cc.
Proof. vm_refl. Qed.
Lemma D_5e2cc : decode_any W_5e2cc = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2d0 : bv 32 := 0x0145f5b3.
Lemma F_5e2d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e318 : word) = Some W_5e2d0.
Proof. vm_refl. Qed.
Lemma D_5e2d0 : decode_any W_5e2d0 = Some (Op ALU_AND 11 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2d4 : bv 32 := 0x26059863.
Lemma F_5e2d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e31c : word) = Some W_5e2d4.
Proof. vm_refl. Qed.
Lemma D_5e2d4 : decode_any W_5e2d4 = Some (Branch BC_NE 11 0 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2d8 : bv 32 := 0x01490b33.
Lemma F_5e2d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e320 : word) = Some W_5e2d8.
Proof. vm_refl. Qed.
Lemma D_5e2d8 : decode_any W_5e2d8 = Some (Op ALU_ADD 22 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2dc : bv 32 := 0x01450533.
Lemma F_5e2dc : fetch_word AsanUbsan.M.loaded_segments (0x5e324 : word) = Some W_5e2dc.
Proof. vm_refl. Qed.
Lemma D_5e2dc : decode_any W_5e2dc = Some (Op ALU_ADD 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2e0 : bv 32 := 0x018575b3.
Lemma F_5e2e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e328 : word) = Some W_5e2e0.
Proof. vm_refl. Qed.
Lemma D_5e2e0 : decode_any W_5e2e0 = Some (Op ALU_AND 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2e4 : bv 32 := 0x0015b613.
Lemma F_5e2e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e32c : word) = Some W_5e2e4.
Proof. vm_refl. Qed.
Lemma D_5e2e4 : decode_any W_5e2e4 = Some (OpImm ALU_SLTU 12 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2e8 : bv 32 := 0x40ba85b3.
Lemma F_5e2e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e330 : word) = Some W_5e2e8.
Proof. vm_refl. Qed.
Lemma D_5e2e8 : decode_any W_5e2e8 = Some (Op ALU_SUB 11 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2ec : bv 32 := 0xfff60613.
Lemma F_5e2ec : fetch_word AsanUbsan.M.loaded_segments (0x5e334 : word) = Some W_5e2ec.
Proof. vm_refl. Qed.
Lemma D_5e2ec : decode_any W_5e2ec = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2f0 : bv 32 := 0x00b675b3.
Lemma F_5e2f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e338 : word) = Some W_5e2f0.
Proof. vm_refl. Qed.
Lemma D_5e2f0 : decode_any W_5e2f0 = Some (Op ALU_AND 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2f4 : bv 32 := 0x00a58cb3.
Lemma F_5e2f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e33c : word) = Some W_5e2f4.
Proof. vm_refl. Qed.
Lemma D_5e2f4 : decode_any W_5e2f4 = Some (Op ALU_ADD 25 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2f8 : bv 32 := 0x013c8ab3.
Lemma F_5e2f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e340 : word) = Some W_5e2f8.
Proof. vm_refl. Qed.
Lemma D_5e2f8 : decode_any W_5e2f8 = Some (Op ALU_ADD 21 25 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2fc : bv 32 := 0x007c8513.
Lemma F_5e2fc : fetch_word AsanUbsan.M.loaded_segments (0x5e344 : word) = Some W_5e2fc.
Proof. vm_refl. Qed.
Lemma D_5e2fc : decode_any W_5e2fc = Some (OpImm ALU_ADD 10 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e300 : bv 32 := 0xff8afb93.
Lemma F_5e300 : fetch_word AsanUbsan.M.loaded_segments (0x5e348 : word) = Some W_5e300.
Proof. vm_refl. Qed.
Lemma D_5e300 : decode_any W_5e300 = Some (OpImm ALU_AND 23 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e304 : bv 32 := 0xff857513.
Lemma F_5e304 : fetch_word AsanUbsan.M.loaded_segments (0x5e34c : word) = Some W_5e304.
Proof. vm_refl. Qed.
Lemma D_5e304 : decode_any W_5e304 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e308 : bv 32 := 0x414505b3.
Lemma F_5e308 : fetch_word AsanUbsan.M.loaded_segments (0x5e350 : word) = Some W_5e308.
Proof. vm_refl. Qed.
Lemma D_5e308 : decode_any W_5e308 = Some (Op ALU_SUB 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e30c : bv 32 := 0x0fa00613.
Lemma F_5e30c : fetch_word AsanUbsan.M.loaded_segments (0x5e354 : word) = Some W_5e30c.
Proof. vm_refl. Qed.
Lemma D_5e30c : decode_any W_5e30c = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e310 : bv 32 := 0x000a0513.
Lemma F_5e310 : fetch_word AsanUbsan.M.loaded_segments (0x5e358 : word) = Some W_5e310.
Proof. vm_refl. Qed.
Lemma D_5e310 : decode_any W_5e310 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e314 : bv 32 := 0x57d230ef.
Lemma F_5e314 : fetch_word AsanUbsan.M.loaded_segments (0x5e35c : word) = Some W_5e314.
Proof. vm_refl. Qed.
Lemma D_5e314 : decode_any W_5e314 = Some (Jal 1 146812, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e318 : bv 32 := 0x417b05b3.
Lemma F_5e318 : fetch_word AsanUbsan.M.loaded_segments (0x5e360 : word) = Some W_5e318.
Proof. vm_refl. Qed.
Lemma D_5e318 : decode_any W_5e318 = Some (Op ALU_SUB 11 22 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e31c : bv 32 := 0x0fa00613.
Lemma F_5e31c : fetch_word AsanUbsan.M.loaded_segments (0x5e364 : word) = Some W_5e31c.
Proof. vm_refl. Qed.
Lemma D_5e31c : decode_any W_5e31c = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e320 : bv 32 := 0x000b8513.
Lemma F_5e320 : fetch_word AsanUbsan.M.loaded_segments (0x5e368 : word) = Some W_5e320.
Proof. vm_refl. Qed.
Lemma D_5e320 : decode_any W_5e320 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e324 : bv 32 := 0x56d230ef.
Lemma F_5e324 : fetch_word AsanUbsan.M.loaded_segments (0x5e36c : word) = Some W_5e324.
Proof. vm_refl. Qed.
Lemma D_5e324 : decode_any W_5e324 = Some (Jal 1 146796, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e328 : bv 32 := 0x4e12b0ef.
Lemma F_5e328 : fetch_word AsanUbsan.M.loaded_segments (0x5e370 : word) = Some W_5e328.
Proof. vm_refl. Qed.
Lemma D_5e328 : decode_any W_5e328 = Some (Jal 1 179424, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e32c : bv 32 := 0x04853603.
Lemma F_5e32c : fetch_word AsanUbsan.M.loaded_segments (0x5e374 : word) = Some W_5e32c.
Proof. vm_refl. Qed.
Lemma D_5e32c : decode_any W_5e32c = Some (Load SZ8 true 12 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e330 : bv 32 := 0x05053683.
Lemma F_5e330 : fetch_word AsanUbsan.M.loaded_segments (0x5e378 : word) = Some W_5e330.
Proof. vm_refl. Qed.
Lemma D_5e330 : decode_any W_5e330 = Some (Load SZ8 true 13 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e334 : bv 32 := 0x018cf733.
Lemma F_5e334 : fetch_word AsanUbsan.M.loaded_segments (0x5e37c : word) = Some W_5e334.
Proof. vm_refl. Qed.
Lemma D_5e334 : decode_any W_5e334 = Some (Op ALU_AND 14 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e338 : bv 32 := 0x00160613.
Lemma F_5e338 : fetch_word AsanUbsan.M.loaded_segments (0x5e380 : word) = Some W_5e338.
Proof. vm_refl. Qed.
Lemma D_5e338 : decode_any W_5e338 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e33c : bv 32 := 0x012686b3.
Lemma F_5e33c : fetch_word AsanUbsan.M.loaded_segments (0x5e384 : word) = Some W_5e33c.
Proof. vm_refl. Qed.
Lemma D_5e33c : decode_any W_5e33c = Some (Op ALU_ADD 13 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e340 : bv 32 := 0x04c53423.
Lemma F_5e340 : fetch_word AsanUbsan.M.loaded_segments (0x5e388 : word) = Some W_5e340.
Proof. vm_refl. Qed.
Lemma D_5e340 : decode_any W_5e340 = Some (Store SZ8 10 12 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e344 : bv 32 := 0x04d53823.
Lemma F_5e344 : fetch_word AsanUbsan.M.loaded_segments (0x5e38c : word) = Some W_5e344.
Proof. vm_refl. Qed.
Lemma D_5e344 : decode_any W_5e344 = Some (Store SZ8 10 13 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e348 : bv 32 := 0x20071e63.
Lemma F_5e348 : fetch_word AsanUbsan.M.loaded_segments (0x5e390 : word) = Some W_5e348.
Proof. vm_refl. Qed.
Lemma D_5e348 : decode_any W_5e348 = Some (Branch BC_NE 14 0 540, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e34c : bv 32 := 0x000c8513.
Lemma F_5e34c : fetch_word AsanUbsan.M.loaded_segments (0x5e394 : word) = Some W_5e34c.
Proof. vm_refl. Qed.
Lemma D_5e34c : decode_any W_5e34c = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e350 : bv 32 := 0x0004b583.
Lemma F_5e350 : fetch_word AsanUbsan.M.loaded_segments (0x5e398 : word) = Some W_5e350.
Proof. vm_refl. Qed.
Lemma D_5e350 : decode_any W_5e350 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e354 : bv 32 := 0xfff58613.
Lemma F_5e354 : fetch_word AsanUbsan.M.loaded_segments (0x5e39c : word) = Some W_5e354.
Proof. vm_refl. Qed.
Lemma D_5e354 : decode_any W_5e354 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e358 : bv 32 := 0x01967633.
Lemma F_5e358 : fetch_word AsanUbsan.M.loaded_segments (0x5e3a0 : word) = Some W_5e358.
Proof. vm_refl. Qed.
Lemma D_5e358 : decode_any W_5e358 = Some (Op ALU_AND 12 12 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e35c : bv 32 := 0x22061463.
Lemma F_5e35c : fetch_word AsanUbsan.M.loaded_segments (0x5e3a4 : word) = Some W_5e35c.
Proof. vm_refl. Qed.
Lemma D_5e35c : decode_any W_5e35c = Some (Branch BC_NE 12 0 552, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e360 : bv 32 := 0x254ae263.
Lemma F_5e360 : fetch_word AsanUbsan.M.loaded_segments (0x5e3a8 : word) = Some W_5e360.
Proof. vm_refl. Qed.
Lemma D_5e360 : decode_any W_5e360 = Some (Branch BC_LTU 21 20 580, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e364 : bv 32 := 0x275b6063.
Lemma F_5e364 : fetch_word AsanUbsan.M.loaded_segments (0x5e3ac : word) = Some W_5e364.
Proof. vm_refl. Qed.
Lemma D_5e364 : decode_any W_5e364 = Some (Branch BC_LTU 22 21 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e368 : bv 32 := 0x40b50ab3.
Lemma F_5e368 : fetch_word AsanUbsan.M.loaded_segments (0x5e3b0 : word) = Some W_5e368.
Proof. vm_refl. Qed.
Lemma D_5e368 : decode_any W_5e368 = Some (Op ALU_SUB 21 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e36c : bv 32 := 0x014ab023.
Lemma F_5e36c : fetch_word AsanUbsan.M.loaded_segments (0x5e3b4 : word) = Some W_5e36c.
Proof. vm_refl. Qed.
Lemma D_5e36c : decode_any W_5e36c = Some (Store SZ8 21 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e370 : bv 32 := 0x012ab423.
Lemma F_5e370 : fetch_word AsanUbsan.M.loaded_segments (0x5e3b8 : word) = Some W_5e370.
Proof. vm_refl. Qed.
Lemma D_5e370 : decode_any W_5e370 = Some (Store SZ8 21 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e374 : bv 32 := 0x013ab823.
Lemma F_5e374 : fetch_word AsanUbsan.M.loaded_segments (0x5e3bc : word) = Some W_5e374.
Proof. vm_refl. Qed.
Lemma D_5e374 : decode_any W_5e374 = Some (Store SZ8 21 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e378 : bv 32 := 0x26090663.
Lemma F_5e378 : fetch_word AsanUbsan.M.loaded_segments (0x5e3c0 : word) = Some W_5e378.
Proof. vm_refl. Qed.
Lemma D_5e378 : decode_any W_5e378 = Some (Branch BC_EQ 18 0 620, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e37c : bv 32 := 0x26848593.
Lemma F_5e37c : fetch_word AsanUbsan.M.loaded_segments (0x5e3c4 : word) = Some W_5e37c.
Proof. vm_refl. Qed.
Lemma D_5e37c : decode_any W_5e37c = Some (OpImm ALU_ADD 11 9 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e380 : bv 32 := 0x0ff00613.
Lemma F_5e380 : fetch_word AsanUbsan.M.loaded_segments (0x5e3c8 : word) = Some W_5e380.
Proof. vm_refl. Qed.
Lemma D_5e380 : decode_any W_5e380 = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e384 : bv 32 := 0xffc5f693.
Lemma F_5e384 : fetch_word AsanUbsan.M.loaded_segments (0x5e3cc : word) = Some W_5e384.
Proof. vm_refl. Qed.
Lemma D_5e384 : decode_any W_5e384 = Some (OpImm ALU_AND 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e388 : bv 32 := 0x00100713.
Lemma F_5e388 : fetch_word AsanUbsan.M.loaded_segments (0x5e3d0 : word) = Some W_5e388.
Proof. vm_refl. Qed.
Lemma D_5e388 : decode_any W_5e388 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e38c : bv 32 := 0x1406a7af.
Lemma F_5e38c : fetch_word AsanUbsan.M.loaded_segments (0x5e3d4 : word) = Some W_5e38c.
Proof. vm_refl. Qed.
Lemma D_5e38c : decode_any W_5e38c = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e390 : bv 32 := 0x00070813.
Lemma F_5e390 : fetch_word AsanUbsan.M.loaded_segments (0x5e3d8 : word) = Some W_5e390.
Proof. vm_refl. Qed.
Lemma D_5e390 : decode_any W_5e390 = Some (OpImm ALU_ADD 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e394 : bv 32 := 0x0107c833.
Lemma F_5e394 : fetch_word AsanUbsan.M.loaded_segments (0x5e3dc : word) = Some W_5e394.
Proof. vm_refl. Qed.
Lemma D_5e394 : decode_any W_5e394 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e398 : bv 32 := 0x00c87833.
Lemma F_5e398 : fetch_word AsanUbsan.M.loaded_segments (0x5e3e0 : word) = Some W_5e398.
Proof. vm_refl. Qed.
Lemma D_5e398 : decode_any W_5e398 = Some (Op ALU_AND 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e39c : bv 32 := 0x0107c833.
Lemma F_5e39c : fetch_word AsanUbsan.M.loaded_segments (0x5e3e4 : word) = Some W_5e39c.
Proof. vm_refl. Qed.
Lemma D_5e39c : decode_any W_5e39c = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a0 : bv 32 := 0x1906a82f.
Lemma F_5e3a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3e8 : word) = Some W_5e3a0.
Proof. vm_refl. Qed.
Lemma D_5e3a0 : decode_any W_5e3a0 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a4 : bv 32 := 0xfe0814e3.
Lemma F_5e3a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3ec : word) = Some W_5e3a4.
Proof. vm_refl. Qed.
Lemma D_5e3a4 : decode_any W_5e3a4 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a8 : bv 32 := 0x0ff7f613.
Lemma F_5e3a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e3f0 : word) = Some W_5e3a8.
Proof. vm_refl. Qed.
Lemma D_5e3a8 : decode_any W_5e3a8 = Some (OpImm ALU_AND 12 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3ac : bv 32 := 0x24061c63.
Lemma F_5e3ac : fetch_word AsanUbsan.M.loaded_segments (0x5e3f4 : word) = Some W_5e3ac.
Proof. vm_refl. Qed.
Lemma D_5e3ac : decode_any W_5e3ac = Some (Branch BC_NE 12 0 600, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b0 : bv 32 := 0x0384b683.
Lemma F_5e3b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e3f8 : word) = Some W_5e3b0.
Proof. vm_refl. Qed.
Lemma D_5e3b0 : decode_any W_5e3b0 = Some (Load SZ8 true 13 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b4 : bv 32 := 0x0146d593.
Lemma F_5e3b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e3fc : word) = Some W_5e3b4.
Proof. vm_refl. Qed.
Lemma D_5e3b4 : decode_any W_5e3b4 = Some (ShiftImm ALU_SRL 11 13 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b8 : bv 32 := 0x26059463.
Lemma F_5e3b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e400 : word) = Some W_5e3b8.
Proof. vm_refl. Qed.
Lemma D_5e3b8 : decode_any W_5e3b8 = Some (Branch BC_NE 11 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3bc : bv 32 := 0x00195593.
Lemma F_5e3bc : fetch_word AsanUbsan.M.loaded_segments (0x5e404 : word) = Some W_5e3bc.
Proof. vm_refl. Qed.
Lemma D_5e3bc : decode_any W_5e3bc = Some (ShiftImm ALU_SRL 11 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c0 : bv 32 := 0x55555637.
Lemma F_5e3c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e408 : word) = Some W_5e3c0.
Proof. vm_refl. Qed.
Lemma D_5e3c0 : decode_any W_5e3c0 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c4 : bv 32 := 0x33333737.
Lemma F_5e3c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e40c : word) = Some W_5e3c4.
Proof. vm_refl. Qed.
Lemma D_5e3c4 : decode_any W_5e3c4 = Some (Lui 14 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c8 : bv 32 := 0x0f0f17b7.
Lemma F_5e3c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e410 : word) = Some W_5e3c8.
Proof. vm_refl. Qed.
Lemma D_5e3c8 : decode_any W_5e3c8 = Some (Lui 15 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3cc : bv 32 := 0x00b965b3.
Lemma F_5e3cc : fetch_word AsanUbsan.M.loaded_segments (0x5e414 : word) = Some W_5e3cc.
Proof. vm_refl. Qed.
Lemma D_5e3cc : decode_any W_5e3cc = Some (Op ALU_OR 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d0 : bv 32 := 0x5556061b.
Lemma F_5e3d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e418 : word) = Some W_5e3d0.
Proof. vm_refl. Qed.
Lemma D_5e3d0 : decode_any W_5e3d0 = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d4 : bv 32 := 0x3337071b.
Lemma F_5e3d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e41c : word) = Some W_5e3d4.
Proof. vm_refl. Qed.
Lemma D_5e3d4 : decode_any W_5e3d4 = Some (OpImm32 14 14 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d8 : bv 32 := 0xf0f7879b.
Lemma F_5e3d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e420 : word) = Some W_5e3d8.
Proof. vm_refl. Qed.
Lemma D_5e3d8 : decode_any W_5e3d8 = Some (OpImm32 15 15 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3dc : bv 32 := 0x0025d813.
Lemma F_5e3dc : fetch_word AsanUbsan.M.loaded_segments (0x5e424 : word) = Some W_5e3dc.
Proof. vm_refl. Qed.
Lemma D_5e3dc : decode_any W_5e3dc = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e0 : bv 32 := 0x0105e5b3.
Lemma F_5e3e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e428 : word) = Some W_5e3e0.
Proof. vm_refl. Qed.
Lemma D_5e3e0 : decode_any W_5e3e0 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e4 : bv 32 := 0x02061813.
Lemma F_5e3e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e42c : word) = Some W_5e3e4.
Proof. vm_refl. Qed.
Lemma D_5e3e4 : decode_any W_5e3e4 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e8 : bv 32 := 0x01060633.
Lemma F_5e3e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e430 : word) = Some W_5e3e8.
Proof. vm_refl. Qed.
Lemma D_5e3e8 : decode_any W_5e3e8 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3ec : bv 32 := 0x02071813.
Lemma F_5e3ec : fetch_word AsanUbsan.M.loaded_segments (0x5e434 : word) = Some W_5e3ec.
Proof. vm_refl. Qed.
Lemma D_5e3ec : decode_any W_5e3ec = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f0 : bv 32 := 0x01070733.
Lemma F_5e3f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e438 : word) = Some W_5e3f0.
Proof. vm_refl. Qed.
Lemma D_5e3f0 : decode_any W_5e3f0 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f4 : bv 32 := 0x02079813.
Lemma F_5e3f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e43c : word) = Some W_5e3f4.
Proof. vm_refl. Qed.
Lemma D_5e3f4 : decode_any W_5e3f4 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f8 : bv 32 := 0x010787b3.
Lemma F_5e3f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e440 : word) = Some W_5e3f8.
Proof. vm_refl. Qed.
Lemma D_5e3f8 : decode_any W_5e3f8 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3fc : bv 32 := 0x0045d813.
Lemma F_5e3fc : fetch_word AsanUbsan.M.loaded_segments (0x5e444 : word) = Some W_5e3fc.
Proof. vm_refl. Qed.
Lemma D_5e3fc : decode_any W_5e3fc = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e400 : bv 32 := 0x0105e5b3.
Lemma F_5e400 : fetch_word AsanUbsan.M.loaded_segments (0x5e448 : word) = Some W_5e400.
Proof. vm_refl. Qed.
Lemma D_5e400 : decode_any W_5e400 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e404 : bv 32 := 0x0085d813.
Lemma F_5e404 : fetch_word AsanUbsan.M.loaded_segments (0x5e44c : word) = Some W_5e404.
Proof. vm_refl. Qed.
Lemma D_5e404 : decode_any W_5e404 = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e408 : bv 32 := 0x0105e5b3.
Lemma F_5e408 : fetch_word AsanUbsan.M.loaded_segments (0x5e450 : word) = Some W_5e408.
Proof. vm_refl. Qed.
Lemma D_5e408 : decode_any W_5e408 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e40c : bv 32 := 0x0105d813.
Lemma F_5e40c : fetch_word AsanUbsan.M.loaded_segments (0x5e454 : word) = Some W_5e40c.
Proof. vm_refl. Qed.
Lemma D_5e40c : decode_any W_5e40c = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e410 : bv 32 := 0x0105e5b3.
Lemma F_5e410 : fetch_word AsanUbsan.M.loaded_segments (0x5e458 : word) = Some W_5e410.
Proof. vm_refl. Qed.
Lemma D_5e410 : decode_any W_5e410 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e414 : bv 32 := 0x0205d813.
Lemma F_5e414 : fetch_word AsanUbsan.M.loaded_segments (0x5e45c : word) = Some W_5e414.
Proof. vm_refl. Qed.
Lemma D_5e414 : decode_any W_5e414 = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e418 : bv 32 := 0x0105e5b3.
Lemma F_5e418 : fetch_word AsanUbsan.M.loaded_segments (0x5e460 : word) = Some W_5e418.
Proof. vm_refl. Qed.
Lemma D_5e418 : decode_any W_5e418 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e41c : bv 32 := 0xfff5c593.
Lemma F_5e41c : fetch_word AsanUbsan.M.loaded_segments (0x5e464 : word) = Some W_5e41c.
Proof. vm_refl. Qed.
Lemma D_5e41c : decode_any W_5e41c = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e420 : bv 32 := 0x0015d813.
Lemma F_5e420 : fetch_word AsanUbsan.M.loaded_segments (0x5e468 : word) = Some W_5e420.
Proof. vm_refl. Qed.
Lemma D_5e420 : decode_any W_5e420 = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e424 : bv 32 := 0x00c87633.
Lemma F_5e424 : fetch_word AsanUbsan.M.loaded_segments (0x5e46c : word) = Some W_5e424.
Proof. vm_refl. Qed.
Lemma D_5e424 : decode_any W_5e424 = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e428 : bv 32 := 0x01010837.
Lemma F_5e428 : fetch_word AsanUbsan.M.loaded_segments (0x5e470 : word) = Some W_5e428.
Proof. vm_refl. Qed.
Lemma D_5e428 : decode_any W_5e428 = Some (Lui 16 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e42c : bv 32 := 0x40c585b3.
Lemma F_5e42c : fetch_word AsanUbsan.M.loaded_segments (0x5e474 : word) = Some W_5e42c.
Proof. vm_refl. Qed.
Lemma D_5e42c : decode_any W_5e42c = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e430 : bv 32 := 0x0025d613.
Lemma F_5e430 : fetch_word AsanUbsan.M.loaded_segments (0x5e478 : word) = Some W_5e430.
Proof. vm_refl. Qed.
Lemma D_5e430 : decode_any W_5e430 = Some (ShiftImm ALU_SRL 12 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e434 : bv 32 := 0x00e5f5b3.
Lemma F_5e434 : fetch_word AsanUbsan.M.loaded_segments (0x5e47c : word) = Some W_5e434.
Proof. vm_refl. Qed.
Lemma D_5e434 : decode_any W_5e434 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e438 : bv 32 := 0x00e67633.
Lemma F_5e438 : fetch_word AsanUbsan.M.loaded_segments (0x5e480 : word) = Some W_5e438.
Proof. vm_refl. Qed.
Lemma D_5e438 : decode_any W_5e438 = Some (Op ALU_AND 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e43c : bv 32 := 0x0304b703.
Lemma F_5e43c : fetch_word AsanUbsan.M.loaded_segments (0x5e484 : word) = Some W_5e43c.
Proof. vm_refl. Qed.
Lemma D_5e43c : decode_any W_5e43c = Some (Load SZ8 true 14 9 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e440 : bv 32 := 0x1018081b.
Lemma F_5e440 : fetch_word AsanUbsan.M.loaded_segments (0x5e488 : word) = Some W_5e440.
Proof. vm_refl. Qed.
Lemma D_5e440 : decode_any W_5e440 = Some (OpImm32 16 16 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e444 : bv 32 := 0x00c585b3.
Lemma F_5e444 : fetch_word AsanUbsan.M.loaded_segments (0x5e48c : word) = Some W_5e444.
Proof. vm_refl. Qed.
Lemma D_5e444 : decode_any W_5e444 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e448 : bv 32 := 0x0045d613.
Lemma F_5e448 : fetch_word AsanUbsan.M.loaded_segments (0x5e490 : word) = Some W_5e448.
Proof. vm_refl. Qed.
Lemma D_5e448 : decode_any W_5e448 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e44c : bv 32 := 0x00c585b3.
Lemma F_5e44c : fetch_word AsanUbsan.M.loaded_segments (0x5e494 : word) = Some W_5e44c.
Proof. vm_refl. Qed.
Lemma D_5e44c : decode_any W_5e44c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e450 : bv 32 := 0x02081613.
Lemma F_5e450 : fetch_word AsanUbsan.M.loaded_segments (0x5e498 : word) = Some W_5e450.
Proof. vm_refl. Qed.
Lemma D_5e450 : decode_any W_5e450 = Some (ShiftImm ALU_SLL 12 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e454 : bv 32 := 0x00f5f5b3.
Lemma F_5e454 : fetch_word AsanUbsan.M.loaded_segments (0x5e49c : word) = Some W_5e454.
Proof. vm_refl. Qed.
Lemma D_5e454 : decode_any W_5e454 = Some (Op ALU_AND 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e458 : bv 32 := 0x00c80633.
Lemma F_5e458 : fetch_word AsanUbsan.M.loaded_segments (0x5e4a0 : word) = Some W_5e458.
Proof. vm_refl. Qed.
Lemma D_5e458 : decode_any W_5e458 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e45c : bv 32 := 0x02c585b3.
Lemma F_5e45c : fetch_word AsanUbsan.M.loaded_segments (0x5e4a4 : word) = Some W_5e45c.
Proof. vm_refl. Qed.
Lemma D_5e45c : decode_any W_5e45c = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e460 : bv 32 := 0x0385d993.
Lemma F_5e460 : fetch_word AsanUbsan.M.loaded_segments (0x5e4a8 : word) = Some W_5e460.
Proof. vm_refl. Qed.
Lemma D_5e460 : decode_any W_5e460 = Some (ShiftImm ALU_SRL 19 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e464 : bv 32 := 0x1ce68c63.
Lemma F_5e464 : fetch_word AsanUbsan.M.loaded_segments (0x5e4ac : word) = Some W_5e464.
Proof. vm_refl. Qed.
Lemma D_5e464 : decode_any W_5e464 = Some (Branch BC_EQ 13 14 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e468 : bv 32 := 0x0084b603.
Lemma F_5e468 : fetch_word AsanUbsan.M.loaded_segments (0x5e4b0 : word) = Some W_5e468.
Proof. vm_refl. Qed.
Lemma D_5e468 : decode_any W_5e468 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e46c : bv 32 := 0x03f9c593.
Lemma F_5e46c : fetch_word AsanUbsan.M.loaded_segments (0x5e4b4 : word) = Some W_5e46c.
Proof. vm_refl. Qed.
Lemma D_5e46c : decode_any W_5e46c = Some (OpImm ALU_XOR 11 19 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e470 : bv 32 := 0x00dabc23.
Lemma F_5e470 : fetch_word AsanUbsan.M.loaded_segments (0x5e4b8 : word) = Some W_5e470.
Proof. vm_refl. Qed.
Lemma D_5e470 : decode_any W_5e470 = Some (Store SZ8 21 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e474 : bv 32 := 0x00369713.
Lemma F_5e474 : fetch_word AsanUbsan.M.loaded_segments (0x5e4bc : word) = Some W_5e474.
Proof. vm_refl. Qed.
Lemma D_5e474 : decode_any W_5e474 = Some (ShiftImm ALU_SLL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e478 : bv 32 := 0x00e60633.
Lemma F_5e478 : fetch_word AsanUbsan.M.loaded_segments (0x5e4c0 : word) = Some W_5e478.
Proof. vm_refl. Qed.
Lemma D_5e478 : decode_any W_5e478 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e47c : bv 32 := 0x01563023.
Lemma F_5e47c : fetch_word AsanUbsan.M.loaded_segments (0x5e4c4 : word) = Some W_5e47c.
Proof. vm_refl. Qed.
Lemma D_5e47c : decode_any W_5e47c = Some (Store SZ8 12 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e480 : bv 32 := 0x0484b703.
Lemma F_5e480 : fetch_word AsanUbsan.M.loaded_segments (0x5e4c8 : word) = Some W_5e480.
Proof. vm_refl. Qed.
Lemma D_5e480 : decode_any W_5e480 = Some (Load SZ8 true 14 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e484 : bv 32 := 0x0584b783.
Lemma F_5e484 : fetch_word AsanUbsan.M.loaded_segments (0x5e4cc : word) = Some W_5e484.
Proof. vm_refl. Qed.
Lemma D_5e484 : decode_any W_5e484 = Some (Load SZ8 true 15 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e488 : bv 32 := 0x00168813.
Lemma F_5e488 : fetch_word AsanUbsan.M.loaded_segments (0x5e4d0 : word) = Some W_5e488.
Proof. vm_refl. Qed.
Lemma D_5e488 : decode_any W_5e488 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e48c : bv 32 := 0x0604b603.
Lemma F_5e48c : fetch_word AsanUbsan.M.loaded_segments (0x5e4d4 : word) = Some W_5e48c.
Proof. vm_refl. Qed.
Lemma D_5e48c : decode_any W_5e48c = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e490 : bv 32 := 0x00170713.
Lemma F_5e490 : fetch_word AsanUbsan.M.loaded_segments (0x5e4d8 : word) = Some W_5e490.
Proof. vm_refl. Qed.
Lemma D_5e490 : decode_any W_5e490 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e494 : bv 32 := 0x012786b3.
Lemma F_5e494 : fetch_word AsanUbsan.M.loaded_segments (0x5e4dc : word) = Some W_5e494.
Proof. vm_refl. Qed.
Lemma D_5e494 : decode_any W_5e494 = Some (Op ALU_ADD 13 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e498 : bv 32 := 0x0304bc23.
Lemma F_5e498 : fetch_word AsanUbsan.M.loaded_segments (0x5e4e0 : word) = Some W_5e498.
Proof. vm_refl. Qed.
Lemma D_5e498 : decode_any W_5e498 = Some (Store SZ8 9 16 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e49c : bv 32 := 0x04048023.
Lemma F_5e49c : fetch_word AsanUbsan.M.loaded_segments (0x5e4e4 : word) = Some W_5e49c.
Proof. vm_refl. Qed.
Lemma D_5e49c : decode_any W_5e49c = Some (Store SZ1 9 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a0 : bv 32 := 0x04e4b423.
Lemma F_5e4a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e4e8 : word) = Some W_5e4a0.
Proof. vm_refl. Qed.
Lemma D_5e4a0 : decode_any W_5e4a0 = Some (Store SZ8 9 14 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a4 : bv 32 := 0x04d4bc23.
Lemma F_5e4a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e4ec : word) = Some W_5e4a4.
Proof. vm_refl. Qed.
Lemma D_5e4a4 : decode_any W_5e4a4 = Some (Store SZ8 9 13 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a8 : bv 32 := 0x00c6e463.
Lemma F_5e4a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e4f0 : word) = Some W_5e4a8.
Proof. vm_refl. Qed.
Lemma D_5e4a8 : decode_any W_5e4a8 = Some (Branch BC_LTU 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4ac : bv 32 := 0x00068613.
Lemma F_5e4ac : fetch_word AsanUbsan.M.loaded_segments (0x5e4f4 : word) = Some W_5e4ac.
Proof. vm_refl. Qed.
Lemma D_5e4ac : decode_any W_5e4ac = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b0 : bv 32 := 0x00359593.
Lemma F_5e4b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e4f8 : word) = Some W_5e4b0.
Proof. vm_refl. Qed.
Lemma D_5e4b0 : decode_any W_5e4b0 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b4 : bv 32 := 0x00b485b3.
Lemma F_5e4b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e4fc : word) = Some W_5e4b4.
Proof. vm_refl. Qed.
Lemma D_5e4b4 : decode_any W_5e4b4 = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b8 : bv 32 := 0x0685b683.
Lemma F_5e4b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e500 : word) = Some W_5e4b8.
Proof. vm_refl. Qed.
Lemma D_5e4b8 : decode_any W_5e4b8 = Some (Load SZ8 true 13 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4bc : bv 32 := 0x00168693.
Lemma F_5e4bc : fetch_word AsanUbsan.M.loaded_segments (0x5e504 : word) = Some W_5e4bc.
Proof. vm_refl. Qed.
Lemma D_5e4bc : decode_any W_5e4bc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c0 : bv 32 := 0x06c4b023.
Lemma F_5e4c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e508 : word) = Some W_5e4c0.
Proof. vm_refl. Qed.
Lemma D_5e4c0 : decode_any W_5e4c0 = Some (Store SZ8 9 12 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c4 : bv 32 := 0x06d5b423.
Lemma F_5e4c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e50c : word) = Some W_5e4c4.
Proof. vm_refl. Qed.
Lemma D_5e4c4 : decode_any W_5e4c4 = Some (Store SZ8 11 13 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c8 : bv 32 := 0x01040593.
Lemma F_5e4c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e510 : word) = Some W_5e4c8.
Proof. vm_refl. Qed.
Lemma D_5e4c8 : decode_any W_5e4c8 = Some (OpImm ALU_ADD 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4cc : bv 32 := 0x0125b02f.
Lemma F_5e4cc : fetch_word AsanUbsan.M.loaded_segments (0x5e514 : word) = Some W_5e4cc.
Proof. vm_refl. Qed.
Lemma D_5e4cc : decode_any W_5e4cc = Some (Amo AMO_ADD AD false false 0 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d0 : bv 32 := 0x01840413.
Lemma F_5e4d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e518 : word) = Some W_5e4d0.
Proof. vm_refl. Qed.
Lemma D_5e4d0 : decode_any W_5e4d0 = Some (OpImm ALU_ADD 8 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d4 : bv 32 := 0x0124302f.
Lemma F_5e4d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e51c : word) = Some W_5e4d4.
Proof. vm_refl. Qed.
Lemma D_5e4d4 : decode_any W_5e4d4 = Some (Amo AMO_ADD AD false false 0 8 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d8 : bv 32 := 0x0310000f.
Lemma F_5e4d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e520 : word) = Some W_5e4d8.
Proof. vm_refl. Qed.
Lemma D_5e4d8 : decode_any W_5e4d8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4dc : bv 32 := 0x26048423.
Lemma F_5e4dc : fetch_word AsanUbsan.M.loaded_segments (0x5e524 : word) = Some W_5e4dc.
Proof. vm_refl. Qed.
Lemma D_5e4dc : decode_any W_5e4dc = Some (Store SZ1 9 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e0 : bv 32 := 0x05813083.
Lemma F_5e4e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e528 : word) = Some W_5e4e0.
Proof. vm_refl. Qed.
Lemma D_5e4e0 : decode_any W_5e4e0 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e4 : bv 32 := 0x05013403.
Lemma F_5e4e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e52c : word) = Some W_5e4e4.
Proof. vm_refl. Qed.
Lemma D_5e4e4 : decode_any W_5e4e4 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e8 : bv 32 := 0x04813483.
Lemma F_5e4e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e530 : word) = Some W_5e4e8.
Proof. vm_refl. Qed.
Lemma D_5e4e8 : decode_any W_5e4e8 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4ec : bv 32 := 0x04013903.
Lemma F_5e4ec : fetch_word AsanUbsan.M.loaded_segments (0x5e534 : word) = Some W_5e4ec.
Proof. vm_refl. Qed.
Lemma D_5e4ec : decode_any W_5e4ec = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4f0 : bv 32 := 0x03813983.
Lemma F_5e4f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e538 : word) = Some W_5e4f0.
Proof. vm_refl. Qed.
Lemma D_5e4f0 : decode_any W_5e4f0 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4f4 : bv 32 := 0x03013a03.
Lemma F_5e4f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e53c : word) = Some W_5e4f4.
Proof. vm_refl. Qed.
Lemma D_5e4f4 : decode_any W_5e4f4 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4f8 : bv 32 := 0x02813a83.
Lemma F_5e4f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e540 : word) = Some W_5e4f8.
Proof. vm_refl. Qed.
Lemma D_5e4f8 : decode_any W_5e4f8 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4fc : bv 32 := 0x02013b03.
Lemma F_5e4fc : fetch_word AsanUbsan.M.loaded_segments (0x5e544 : word) = Some W_5e4fc.
Proof. vm_refl. Qed.
Lemma D_5e4fc : decode_any W_5e4fc = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e500 : bv 32 := 0x01813b83.
Lemma F_5e500 : fetch_word AsanUbsan.M.loaded_segments (0x5e548 : word) = Some W_5e500.
Proof. vm_refl. Qed.
Lemma D_5e500 : decode_any W_5e500 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e504 : bv 32 := 0x01013c03.
Lemma F_5e504 : fetch_word AsanUbsan.M.loaded_segments (0x5e54c : word) = Some W_5e504.
Proof. vm_refl. Qed.
Lemma D_5e504 : decode_any W_5e504 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e508 : bv 32 := 0x00813c83.
Lemma F_5e508 : fetch_word AsanUbsan.M.loaded_segments (0x5e550 : word) = Some W_5e508.
Proof. vm_refl. Qed.
Lemma D_5e508 : decode_any W_5e508 = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e50c : bv 32 := 0x06010113.
Lemma F_5e50c : fetch_word AsanUbsan.M.loaded_segments (0x5e554 : word) = Some W_5e50c.
Proof. vm_refl. Qed.
Lemma D_5e50c : decode_any W_5e50c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e510 : bv 32 := 0x00008067.
Lemma F_5e510 : fetch_word AsanUbsan.M.loaded_segments (0x5e558 : word) = Some W_5e510.
Proof. vm_refl. Qed.
Lemma D_5e510 : decode_any W_5e510 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e63c : bv 32 := 0x0104b583.
Lemma F_5e63c : fetch_word AsanUbsan.M.loaded_segments (0x5e684 : word) = Some W_5e63c.
Proof. vm_refl. Qed.
Lemma D_5e63c : decode_any W_5e63c = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e640 : bv 32 := 0x01048713.
Lemma F_5e640 : fetch_word AsanUbsan.M.loaded_segments (0x5e688 : word) = Some W_5e640.
Proof. vm_refl. Qed.
Lemma D_5e640 : decode_any W_5e640 = Some (OpImm ALU_ADD 14 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e644 : bv 32 := 0x00369693.
Lemma F_5e644 : fetch_word AsanUbsan.M.loaded_segments (0x5e68c : word) = Some W_5e644.
Proof. vm_refl. Qed.
Lemma D_5e644 : decode_any W_5e644 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e648 : bv 32 := 0x00b685b3.
Lemma F_5e648 : fetch_word AsanUbsan.M.loaded_segments (0x5e690 : word) = Some W_5e648.
Proof. vm_refl. Qed.
Lemma D_5e648 : decode_any W_5e648 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e64c : bv 32 := 0x00020637.
Lemma F_5e64c : fetch_word AsanUbsan.M.loaded_segments (0x5e694 : word) = Some W_5e64c.
Proof. vm_refl. Qed.
Lemma D_5e64c : decode_any W_5e64c = Some (Lui 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e650 : bv 32 := 0x00050a13.
Lemma F_5e650 : fetch_word AsanUbsan.M.loaded_segments (0x5e698 : word) = Some W_5e650.
Proof. vm_refl. Qed.
Lemma D_5e650 : decode_any W_5e650 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e654 : bv 32 := 0x00070513.
Lemma F_5e654 : fetch_word AsanUbsan.M.loaded_segments (0x5e69c : word) = Some W_5e654.
Proof. vm_refl. Qed.
Lemma D_5e654 : decode_any W_5e654 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e658 : bv 32 := 0x00000693.
Lemma F_5e658 : fetch_word AsanUbsan.M.loaded_segments (0x5e6a0 : word) = Some W_5e658.
Proof. vm_refl. Qed.
Lemma D_5e658 : decode_any W_5e658 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e65c : bv 32 := 0x4153e0ef.
Lemma F_5e65c : fetch_word AsanUbsan.M.loaded_segments (0x5e6a4 : word) = Some W_5e65c.
Proof. vm_refl. Qed.
Lemma D_5e65c : decode_any W_5e65c = Some (Jal 1 257044, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e660 : bv 32 := 0x000a0513.
Lemma F_5e660 : fetch_word AsanUbsan.M.loaded_segments (0x5e6a8 : word) = Some W_5e660.
Proof. vm_refl. Qed.
Lemma D_5e660 : decode_any W_5e660 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e664 : bv 32 := 0x0304b583.
Lemma F_5e664 : fetch_word AsanUbsan.M.loaded_segments (0x5e6ac : word) = Some W_5e664.
Proof. vm_refl. Qed.
Lemma D_5e664 : decode_any W_5e664 = Some (Load SZ8 true 11 9 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e668 : bv 32 := 0x0384b683.
Lemma F_5e668 : fetch_word AsanUbsan.M.loaded_segments (0x5e6b0 : word) = Some W_5e668.
Proof. vm_refl. Qed.
Lemma D_5e668 : decode_any W_5e668 = Some (Load SZ8 true 13 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e66c : bv 32 := 0x00004637.
Lemma F_5e66c : fetch_word AsanUbsan.M.loaded_segments (0x5e6b4 : word) = Some W_5e66c.
Proof. vm_refl. Qed.
Lemma D_5e66c : decode_any W_5e66c = Some (Lui 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e670 : bv 32 := 0x00c585b3.
Lemma F_5e670 : fetch_word AsanUbsan.M.loaded_segments (0x5e6b8 : word) = Some W_5e670.
Proof. vm_refl. Qed.
Lemma D_5e670 : decode_any W_5e670 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e674 : bv 32 := 0x02b4b823.
Lemma F_5e674 : fetch_word AsanUbsan.M.loaded_segments (0x5e6bc : word) = Some W_5e674.
Proof. vm_refl. Qed.
Lemma D_5e674 : decode_any W_5e674 = Some (Store SZ8 9 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e678 : bv 32 := 0xdf1ff06f.
Lemma F_5e678 : fetch_word AsanUbsan.M.loaded_segments (0x5e6c0 : word) = Some W_5e678.
Proof. vm_refl. Qed.
Lemma D_5e678 : decode_any W_5e678 = Some (Jal 0 2096624, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e67c : bv 32 := 0xfe010113.
Lemma F_5e67c : fetch_word AsanUbsan.M.loaded_segments (0x5e6c4 : word) = Some W_5e67c.
Proof. vm_refl. Qed.
Lemma D_5e67c : decode_any W_5e67c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e680 : bv 32 := 0x00113c23.
Lemma F_5e680 : fetch_word AsanUbsan.M.loaded_segments (0x5e6c8 : word) = Some W_5e680.
Proof. vm_refl. Qed.
Lemma D_5e680 : decode_any W_5e680 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e684 : bv 32 := 0x00813823.
Lemma F_5e684 : fetch_word AsanUbsan.M.loaded_segments (0x5e6cc : word) = Some W_5e684.
Proof. vm_refl. Qed.
Lemma D_5e684 : decode_any W_5e684 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e688 : bv 32 := 0x00913423.
Lemma F_5e688 : fetch_word AsanUbsan.M.loaded_segments (0x5e6d0 : word) = Some W_5e688.
Proof. vm_refl. Qed.
Lemma D_5e688 : decode_any W_5e688 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e68c : bv 32 := 0x00068713.
Lemma F_5e68c : fetch_word AsanUbsan.M.loaded_segments (0x5e6d4 : word) = Some W_5e68c.
Proof. vm_refl. Qed.
Lemma D_5e68c : decode_any W_5e68c = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e690 : bv 32 := 0x00058413.
Lemma F_5e690 : fetch_word AsanUbsan.M.loaded_segments (0x5e6d8 : word) = Some W_5e690.
Proof. vm_refl. Qed.
Lemma D_5e690 : decode_any W_5e690 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e694 : bv 32 := 0x0045a583.
Lemma F_5e694 : fetch_word AsanUbsan.M.loaded_segments (0x5e6dc : word) = Some W_5e694.
Proof. vm_refl. Qed.
Lemma D_5e694 : decode_any W_5e694 = Some (Load SZ4 true 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e698 : bv 32 := 0x04058063.
Lemma F_5e698 : fetch_word AsanUbsan.M.loaded_segments (0x5e6e0 : word) = Some W_5e698.
Proof. vm_refl. Qed.
Lemma D_5e698 : decode_any W_5e698 = Some (Branch BC_EQ 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e69c : bv 32 := 0x0015d49b.
Lemma F_5e69c : fetch_word AsanUbsan.M.loaded_segments (0x5e6e4 : word) = Some W_5e69c.
Proof. vm_refl. Qed.
Lemma D_5e69c : decode_any W_5e69c = Some (ShiftImm32 ALU_SRL 9 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6a0 : bv 32 := 0x7ff50513.
Lemma F_5e6a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e6e8 : word) = Some W_5e6a0.
Proof. vm_refl. Qed.
Lemma D_5e6a0 : decode_any W_5e6a0 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6a4 : bv 32 := 0x20150593.
Lemma F_5e6a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e6ec : word) = Some W_5e6a4.
Proof. vm_refl. Qed.
Lemma D_5e6a4 : decode_any W_5e6a4 = Some (OpImm ALU_ADD 11 10 513, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6a8 : bv 32 := 0x01040693.
Lemma F_5e6a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e6f0 : word) = Some W_5e6a8.
Proof. vm_refl. Qed.
Lemma D_5e6a8 : decode_any W_5e6a8 = Some (OpImm ALU_ADD 13 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6ac : bv 32 := 0x00060513.
Lemma F_5e6ac : fetch_word AsanUbsan.M.loaded_segments (0x5e6f4 : word) = Some W_5e6ac.
Proof. vm_refl. Qed.
Lemma D_5e6ac : decode_any W_5e6ac = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6b0 : bv 32 := 0x00070613.
Lemma F_5e6b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e6f8 : word) = Some W_5e6b0.
Proof. vm_refl. Qed.
Lemma D_5e6b0 : decode_any W_5e6b0 = Some (OpImm ALU_ADD 12 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6b4 : bv 32 := 0x00048713.
Lemma F_5e6b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e6fc : word) = Some W_5e6b4.
Proof. vm_refl. Qed.
Lemma D_5e6b4 : decode_any W_5e6b4 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6b8 : bv 32 := 0x0c4000ef.
Lemma F_5e6b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e700 : word) = Some W_5e6b8.
Proof. vm_refl. Qed.
Lemma D_5e6b8 : decode_any W_5e6b8 = Some (Jal 1 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6bc : bv 32 := 0x00050463.
Lemma F_5e6bc : fetch_word AsanUbsan.M.loaded_segments (0x5e704 : word) = Some W_5e6bc.
Proof. vm_refl. Qed.
Lemma D_5e6bc : decode_any W_5e6bc = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6c0 : bv 32 := 0x00942023.
Lemma F_5e6c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e708 : word) = Some W_5e6c0.
Proof. vm_refl. Qed.
Lemma D_5e6c0 : decode_any W_5e6c0 = Some (Store SZ4 8 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6c4 : bv 32 := 0x01813083.
Lemma F_5e6c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e70c : word) = Some W_5e6c4.
Proof. vm_refl. Qed.
Lemma D_5e6c4 : decode_any W_5e6c4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6c8 : bv 32 := 0x01013403.
Lemma F_5e6c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e710 : word) = Some W_5e6c8.
Proof. vm_refl. Qed.
Lemma D_5e6c8 : decode_any W_5e6c8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6cc : bv 32 := 0x00813483.
Lemma F_5e6cc : fetch_word AsanUbsan.M.loaded_segments (0x5e714 : word) = Some W_5e6cc.
Proof. vm_refl. Qed.
Lemma D_5e6cc : decode_any W_5e6cc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d0 : bv 32 := 0x02010113.
Lemma F_5e6d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e718 : word) = Some W_5e6d0.
Proof. vm_refl. Qed.
Lemma D_5e6d0 : decode_any W_5e6d0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d4 : bv 32 := 0x00008067.
Lemma F_5e6d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e71c : word) = Some W_5e6d4.
Proof. vm_refl. Qed.
Lemma D_5e6d4 : decode_any W_5e6d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d8 : bv 32 := 0x05850593.
Lemma F_5e6d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e720 : word) = Some W_5e6d8.
Proof. vm_refl. Qed.
Lemma D_5e6d8 : decode_any W_5e6d8 = Some (OpImm ALU_ADD 11 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6dc : bv 32 := 0x02000693.
Lemma F_5e6dc : fetch_word AsanUbsan.M.loaded_segments (0x5e724 : word) = Some W_5e6dc.
Proof. vm_refl. Qed.
Lemma D_5e6dc : decode_any W_5e6dc = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e0 : bv 32 := 0xff100793.
Lemma F_5e6e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e728 : word) = Some W_5e6e0.
Proof. vm_refl. Qed.
Lemma D_5e6e0 : decode_any W_5e6e0 = Some (OpImm ALU_ADD 15 0 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e4 : bv 32 := 0x00f00813.
Lemma F_5e6e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e72c : word) = Some W_5e6e4.
Proof. vm_refl. Qed.
Lemma D_5e6e4 : decode_any W_5e6e4 = Some (OpImm ALU_ADD 16 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e8 : bv 32 := 0x40000893.
Lemma F_5e6e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e730 : word) = Some W_5e6e8.
Proof. vm_refl. Qed.
Lemma D_5e6e8 : decode_any W_5e6e8 = Some (OpImm ALU_ADD 17 0 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6ec : bv 32 := 0x01000293.
Lemma F_5e6ec : fetch_word AsanUbsan.M.loaded_segments (0x5e734 : word) = Some W_5e6ec.
Proof. vm_refl. Qed.
Lemma D_5e6ec : decode_any W_5e6ec = Some (OpImm ALU_ADD 5 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f0 : bv 32 := 0x01100313.
Lemma F_5e6f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e738 : word) = Some W_5e6f0.
Proof. vm_refl. Qed.
Lemma D_5e6f0 : decode_any W_5e6f0 = Some (OpImm ALU_ADD 6 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f4 : bv 32 := 0x20000393.
Lemma F_5e6f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e73c : word) = Some W_5e6f4.
Proof. vm_refl. Qed.
Lemma D_5e6f4 : decode_any W_5e6f4 = Some (OpImm ALU_ADD 7 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f8 : bv 32 := 0x0280006f.
Lemma F_5e6f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e740 : word) = Some W_5e6f8.
Proof. vm_refl. Qed.
Lemma D_5e6f8 : decode_any W_5e6f8 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6fc : bv 32 := 0x001ebf13.
Lemma F_5e6fc : fetch_word AsanUbsan.M.loaded_segments (0x5e744 : word) = Some W_5e6fc.
Proof. vm_refl. Qed.
Lemma D_5e6fc : decode_any W_5e6fc = Some (OpImm ALU_SLTU 30 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e700 : bv 32 := 0x02068693.
Lemma F_5e700 : fetch_word AsanUbsan.M.loaded_segments (0x5e748 : word) = Some W_5e700.
Proof. vm_refl. Qed.
Lemma D_5e700 : decode_any W_5e700 = Some (OpImm ALU_ADD 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e704 : bv 32 := 0x00178793.
Lemma F_5e704 : fetch_word AsanUbsan.M.loaded_segments (0x5e74c : word) = Some W_5e704.
Proof. vm_refl. Qed.
Lemma D_5e704 : decode_any W_5e704 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e708 : bv 32 := 0x01ee8eb3.
Lemma F_5e708 : fetch_word AsanUbsan.M.loaded_segments (0x5e750 : word) = Some W_5e708.
Proof. vm_refl. Qed.
Lemma D_5e708 : decode_any W_5e708 = Some (Op ALU_ADD 29 29 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e70c : bv 32 := 0x001e9e93.
Lemma F_5e70c : fetch_word AsanUbsan.M.loaded_segments (0x5e754 : word) = Some W_5e70c.
Proof. vm_refl. Qed.
Lemma D_5e70c : decode_any W_5e70c = Some (ShiftImm ALU_SLL 29 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e710 : bv 32 := 0xffd5ae23.
Lemma F_5e710 : fetch_word AsanUbsan.M.loaded_segments (0x5e758 : word) = Some W_5e710.
Proof. vm_refl. Qed.
Lemma D_5e710 : decode_any W_5e710 = Some (Store SZ4 11 29 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e714 : bv 32 := 0x01c5b023.
Lemma F_5e714 : fetch_word AsanUbsan.M.loaded_segments (0x5e75c : word) = Some W_5e714.
Proof. vm_refl. Qed.
Lemma D_5e714 : decode_any W_5e714 = Some (Store SZ8 11 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e718 : bv 32 := 0x05058593.
Lemma F_5e718 : fetch_word AsanUbsan.M.loaded_segments (0x5e760 : word) = Some W_5e718.
Proof. vm_refl. Qed.
Lemma D_5e718 : decode_any W_5e718 = Some (OpImm ALU_ADD 11 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e71c : bv 32 := 0x04578c63.
Lemma F_5e71c : fetch_word AsanUbsan.M.loaded_segments (0x5e764 : word) = Some W_5e71c.
Proof. vm_refl. Qed.
Lemma D_5e71c : decode_any W_5e71c = Some (Branch BC_EQ 15 5 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e720 : bv 32 := 0x05078063.
Lemma F_5e720 : fetch_word AsanUbsan.M.loaded_segments (0x5e768 : word) = Some W_5e720.
Proof. vm_refl. Qed.
Lemma D_5e720 : decode_any W_5e720 = Some (Branch BC_EQ 15 16 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e724 : bv 32 := 0x01078e93.
Lemma F_5e724 : fetch_word AsanUbsan.M.loaded_segments (0x5e76c : word) = Some W_5e724.
Proof. vm_refl. Qed.
Lemma D_5e724 : decode_any W_5e724 = Some (OpImm ALU_ADD 29 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e728 : bv 32 := 0x00068e13.
Lemma F_5e728 : fetch_word AsanUbsan.M.loaded_segments (0x5e770 : word) = Some W_5e728.
Proof. vm_refl. Qed.
Lemma D_5e728 : decode_any W_5e728 = Some (OpImm ALU_ADD 28 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e72c : bv 32 := 0x026ee063.
Lemma F_5e72c : fetch_word AsanUbsan.M.loaded_segments (0x5e774 : word) = Some W_5e72c.
Proof. vm_refl. Qed.
Lemma D_5e72c : decode_any W_5e72c = Some (Branch BC_LTU 29 6 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e730 : bv 32 := 0x0017de13.
Lemma F_5e730 : fetch_word AsanUbsan.M.loaded_segments (0x5e778 : word) = Some W_5e730.
Proof. vm_refl. Qed.
Lemma D_5e730 : decode_any W_5e730 = Some (ShiftImm ALU_SRL 28 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e734 : bv 32 := 0x03fe9e93.
Lemma F_5e734 : fetch_word AsanUbsan.M.loaded_segments (0x5e77c : word) = Some W_5e734.
Proof. vm_refl. Qed.
Lemma D_5e734 : decode_any W_5e734 = Some (ShiftImm ALU_SLL 29 29 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e738 : bv 32 := 0x01c39e33.
Lemma F_5e738 : fetch_word AsanUbsan.M.loaded_segments (0x5e780 : word) = Some W_5e738.
Proof. vm_refl. Qed.
Lemma D_5e738 : decode_any W_5e738 = Some (Op ALU_SLL 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e73c : bv 32 := 0x001e5f13.
Lemma F_5e73c : fetch_word AsanUbsan.M.loaded_segments (0x5e784 : word) = Some W_5e73c.
Proof. vm_refl. Qed.
Lemma D_5e73c : decode_any W_5e73c = Some (ShiftImm ALU_SRL 30 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e740 : bv 32 := 0x43fede93.
Lemma F_5e740 : fetch_word AsanUbsan.M.loaded_segments (0x5e788 : word) = Some W_5e740.
Proof. vm_refl. Qed.
Lemma D_5e740 : decode_any W_5e740 = Some (ShiftImm ALU_SRA 29 29 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e744 : bv 32 := 0x01eefeb3.
Lemma F_5e744 : fetch_word AsanUbsan.M.loaded_segments (0x5e78c : word) = Some W_5e744.
Proof. vm_refl. Qed.
Lemma D_5e744 : decode_any W_5e744 = Some (Op ALU_AND 29 29 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e748 : bv 32 := 0x01ce8e33.
Lemma F_5e748 : fetch_word AsanUbsan.M.loaded_segments (0x5e790 : word) = Some W_5e748.
Proof. vm_refl. Qed.
Lemma D_5e748 : decode_any W_5e748 = Some (Op ALU_ADD 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e74c : bv 32 := 0x03c8debb.
Lemma F_5e74c : fetch_word AsanUbsan.M.loaded_segments (0x5e794 : word) = Some W_5e74c.
Proof. vm_refl. Qed.
Lemma D_5e74c : decode_any W_5e74c = Some (Mul32 M_DIVU 29 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e750 : bv 32 := 0x00800f13.
Lemma F_5e750 : fetch_word AsanUbsan.M.loaded_segments (0x5e798 : word) = Some W_5e750.
Proof. vm_refl. Qed.
Lemma D_5e750 : decode_any W_5e750 = Some (OpImm ALU_ADD 30 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e754 : bv 32 := 0xfbeee4e3.
Lemma F_5e754 : fetch_word AsanUbsan.M.loaded_segments (0x5e79c : word) = Some W_5e754.
Proof. vm_refl. Qed.
Lemma D_5e754 : decode_any W_5e754 = Some (Branch BC_LTU 29 30 8104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e758 : bv 32 := 0x00800e93.
Lemma F_5e758 : fetch_word AsanUbsan.M.loaded_segments (0x5e7a0 : word) = Some W_5e758.
Proof. vm_refl. Qed.
Lemma D_5e758 : decode_any W_5e758 = Some (OpImm ALU_ADD 29 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e75c : bv 32 := 0xfa1ff06f.
Lemma F_5e75c : fetch_word AsanUbsan.M.loaded_segments (0x5e7a4 : word) = Some W_5e75c.
Proof. vm_refl. Qed.
Lemma D_5e75c : decode_any W_5e75c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e760 : bv 32 := 0x04000e13.
Lemma F_5e760 : fetch_word AsanUbsan.M.loaded_segments (0x5e7a8 : word) = Some W_5e760.
Proof. vm_refl. Qed.
Lemma D_5e760 : decode_any W_5e760 = Some (OpImm ALU_ADD 28 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e764 : bv 32 := 0x03c8debb.
Lemma F_5e764 : fetch_word AsanUbsan.M.loaded_segments (0x5e7ac : word) = Some W_5e764.
Proof. vm_refl. Qed.
Lemma D_5e764 : decode_any W_5e764 = Some (Mul32 M_DIVU 29 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e768 : bv 32 := 0x00800f13.
Lemma F_5e768 : fetch_word AsanUbsan.M.loaded_segments (0x5e7b0 : word) = Some W_5e768.
Proof. vm_refl. Qed.
Lemma D_5e768 : decode_any W_5e768 = Some (OpImm ALU_ADD 30 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e76c : bv 32 := 0xf9eee8e3.
Lemma F_5e76c : fetch_word AsanUbsan.M.loaded_segments (0x5e7b4 : word) = Some W_5e76c.
Proof. vm_refl. Qed.
Lemma D_5e76c : decode_any W_5e76c = Some (Branch BC_LTU 29 30 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e770 : bv 32 := 0xfe9ff06f.
Lemma F_5e770 : fetch_word AsanUbsan.M.loaded_segments (0x5e7b8 : word) = Some W_5e770.
Proof. vm_refl. Qed.
Lemma D_5e770 : decode_any W_5e770 = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e774 : bv 32 := 0x00442583.
Lemma F_5e774 : fetch_word AsanUbsan.M.loaded_segments (0x5e7bc : word) = Some W_5e774.
Proof. vm_refl. Qed.
Lemma D_5e774 : decode_any W_5e774 = Some (Load SZ4 true 11 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e778 : bv 32 := 0xf25ff06f.
Lemma F_5e778 : fetch_word AsanUbsan.M.loaded_segments (0x5e7c0 : word) = Some W_5e778.
Proof. vm_refl. Qed.
Lemma D_5e778 : decode_any W_5e778 = Some (Jal 0 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e77c : bv 32 := 0xf8010113.
Lemma F_5e77c : fetch_word AsanUbsan.M.loaded_segments (0x5e7c4 : word) = Some W_5e77c.
Proof. vm_refl. Qed.
Lemma D_5e77c : decode_any W_5e77c = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e780 : bv 32 := 0x06113c23.
Lemma F_5e780 : fetch_word AsanUbsan.M.loaded_segments (0x5e7c8 : word) = Some W_5e780.
Proof. vm_refl. Qed.
Lemma D_5e780 : decode_any W_5e780 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e784 : bv 32 := 0x06813823.
Lemma F_5e784 : fetch_word AsanUbsan.M.loaded_segments (0x5e7cc : word) = Some W_5e784.
Proof. vm_refl. Qed.
Lemma D_5e784 : decode_any W_5e784 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e788 : bv 32 := 0x06913423.
Lemma F_5e788 : fetch_word AsanUbsan.M.loaded_segments (0x5e7d0 : word) = Some W_5e788.
Proof. vm_refl. Qed.
Lemma D_5e788 : decode_any W_5e788 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e78c : bv 32 := 0x07213023.
Lemma F_5e78c : fetch_word AsanUbsan.M.loaded_segments (0x5e7d4 : word) = Some W_5e78c.
Proof. vm_refl. Qed.
Lemma D_5e78c : decode_any W_5e78c = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e790 : bv 32 := 0x05313c23.
Lemma F_5e790 : fetch_word AsanUbsan.M.loaded_segments (0x5e7d8 : word) = Some W_5e790.
Proof. vm_refl. Qed.
Lemma D_5e790 : decode_any W_5e790 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e794 : bv 32 := 0x05413823.
Lemma F_5e794 : fetch_word AsanUbsan.M.loaded_segments (0x5e7dc : word) = Some W_5e794.
Proof. vm_refl. Qed.
Lemma D_5e794 : decode_any W_5e794 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e798 : bv 32 := 0x05513423.
Lemma F_5e798 : fetch_word AsanUbsan.M.loaded_segments (0x5e7e0 : word) = Some W_5e798.
Proof. vm_refl. Qed.
Lemma D_5e798 : decode_any W_5e798 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e79c : bv 32 := 0x05613023.
Lemma F_5e79c : fetch_word AsanUbsan.M.loaded_segments (0x5e7e4 : word) = Some W_5e79c.
Proof. vm_refl. Qed.
Lemma D_5e79c : decode_any W_5e79c = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a0 : bv 32 := 0x03713c23.
Lemma F_5e7a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e7e8 : word) = Some W_5e7a0.
Proof. vm_refl. Qed.
Lemma D_5e7a0 : decode_any W_5e7a0 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a4 : bv 32 := 0x03813823.
Lemma F_5e7a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e7ec : word) = Some W_5e7a4.
Proof. vm_refl. Qed.
Lemma D_5e7a4 : decode_any W_5e7a4 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a8 : bv 32 := 0x03913423.
Lemma F_5e7a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e7f0 : word) = Some W_5e7a8.
Proof. vm_refl. Qed.
Lemma D_5e7a8 : decode_any W_5e7a8 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ac : bv 32 := 0x03a13023.
Lemma F_5e7ac : fetch_word AsanUbsan.M.loaded_segments (0x5e7f4 : word) = Some W_5e7ac.
Proof. vm_refl. Qed.
Lemma D_5e7ac : decode_any W_5e7ac = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b0 : bv 32 := 0x01b13c23.
Lemma F_5e7b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e7f8 : word) = Some W_5e7b0.
Proof. vm_refl. Qed.
Lemma D_5e7b0 : decode_any W_5e7b0 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b4 : bv 32 := 0x00050493.
Lemma F_5e7b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e7fc : word) = Some W_5e7b4.
Proof. vm_refl. Qed.
Lemma D_5e7b4 : decode_any W_5e7b4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b8 : bv 32 := 0x00000793.
Lemma F_5e7b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e800 : word) = Some W_5e7b8.
Proof. vm_refl. Qed.
Lemma D_5e7b8 : decode_any W_5e7b8 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7bc : bv 32 := 0x00100b93.
Lemma F_5e7bc : fetch_word AsanUbsan.M.loaded_segments (0x5e804 : word) = Some W_5e7bc.
Proof. vm_refl. Qed.
Lemma D_5e7bc : decode_any W_5e7bc = Some (OpImm ALU_ADD 23 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c0 : bv 32 := 0x02053a03.
Lemma F_5e7c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e808 : word) = Some W_5e7c0.
Proof. vm_refl. Qed.
Lemma D_5e7c0 : decode_any W_5e7c0 = Some (Load SZ8 true 20 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c4 : bv 32 := 0x03053403.
Lemma F_5e7c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e80c : word) = Some W_5e7c4.
Proof. vm_refl. Qed.
Lemma D_5e7c4 : decode_any W_5e7c4 = Some (Load SZ8 true 8 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c8 : bv 32 := 0x00761513.
Lemma F_5e7c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e810 : word) = Some W_5e7c8.
Proof. vm_refl. Qed.
Lemma D_5e7c8 : decode_any W_5e7c8 = Some (ShiftImm ALU_SLL 10 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7cc : bv 32 := 0x02061893.
Lemma F_5e7cc : fetch_word AsanUbsan.M.loaded_segments (0x5e814 : word) = Some W_5e7cc.
Proof. vm_refl. Qed.
Lemma D_5e7cc : decode_any W_5e7cc = Some (ShiftImm ALU_SLL 17 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d0 : bv 32 := 0x00700293.
Lemma F_5e7d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e818 : word) = Some W_5e7d0.
Proof. vm_refl. Qed.
Lemma D_5e7d0 : decode_any W_5e7d0 = Some (OpImm ALU_ADD 5 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d4 : bv 32 := 0xfff00813.
Lemma F_5e7d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e81c : word) = Some W_5e7d4.
Proof. vm_refl. Qed.
Lemma D_5e7d4 : decode_any W_5e7d4 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d8 : bv 32 := 0x03db9993.
Lemma F_5e7d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e820 : word) = Some W_5e7d8.
Proof. vm_refl. Qed.
Lemma D_5e7d8 : decode_any W_5e7d8 = Some (ShiftImm ALU_SLL 19 23 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7dc : bv 32 := 0x01d29293.
Lemma F_5e7dc : fetch_word AsanUbsan.M.loaded_segments (0x5e824 : word) = Some W_5e7dc.
Proof. vm_refl. Qed.
Lemma D_5e7dc : decode_any W_5e7dc = Some (ShiftImm ALU_SLL 5 5 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e0 : bv 32 := 0x028b9a93.
Lemma F_5e7e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e828 : word) = Some W_5e7e0.
Proof. vm_refl. Qed.
Lemma D_5e7e0 : decode_any W_5e7e0 = Some (ShiftImm ALU_SLL 21 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e4 : bv 32 := 0x005888b3.
Lemma F_5e7e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e82c : word) = Some W_5e7e4.
Proof. vm_refl. Qed.
Lemma D_5e7e4 : decode_any W_5e7e4 = Some (Op ALU_ADD 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e8 : bv 32 := 0x001a8293.
Lemma F_5e7e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e830 : word) = Some W_5e7e8.
Proof. vm_refl. Qed.
Lemma D_5e7e8 : decode_any W_5e7e8 = Some (OpImm ALU_ADD 5 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ec : bv 32 := 0x01429293.
Lemma F_5e7ec : fetch_word AsanUbsan.M.loaded_segments (0x5e834 : word) = Some W_5e7ec.
Proof. vm_refl. Qed.
Lemma D_5e7ec : decode_any W_5e7ec = Some (ShiftImm ALU_SLL 5 5 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f0 : bv 32 := 0x00a40433.
Lemma F_5e7f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e838 : word) = Some W_5e7f0.
Proof. vm_refl. Qed.
Lemma D_5e7f0 : decode_any W_5e7f0 = Some (Op ALU_ADD 8 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f4 : bv 32 := 0x011a0a33.
Lemma F_5e7f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e83c : word) = Some W_5e7f4.
Proof. vm_refl. Qed.
Lemma D_5e7f4 : decode_any W_5e7f4 = Some (Op ALU_ADD 20 20 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f8 : bv 32 := 0xfff28b13.
Lemma F_5e7f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e840 : word) = Some W_5e7f8.
Proof. vm_refl. Qed.
Lemma D_5e7f8 : decode_any W_5e7f8 = Some (OpImm ALU_ADD 22 5 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7fc : bv 32 := 0x00043883.
Lemma F_5e7fc : fetch_word AsanUbsan.M.loaded_segments (0x5e844 : word) = Some W_5e7fc.
Proof. vm_refl. Qed.
Lemma D_5e7fc : decode_any W_5e7fc = Some (Load SZ8 true 17 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e800 : bv 32 := 0x00840513.
Lemma F_5e800 : fetch_word AsanUbsan.M.loaded_segments (0x5e848 : word) = Some W_5e800.
Proof. vm_refl. Qed.
Lemma D_5e800 : decode_any W_5e800 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e804 : bv 32 := 0x03cb9b93.
Lemma F_5e804 : fetch_word AsanUbsan.M.loaded_segments (0x5e84c : word) = Some W_5e804.
Proof. vm_refl. Qed.
Lemma D_5e804 : decode_any W_5e804 = Some (ShiftImm ALU_SLL 23 23 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e808 : bv 32 := 0x5dc00c13.
Lemma F_5e808 : fetch_word AsanUbsan.M.loaded_segments (0x5e850 : word) = Some W_5e808.
Proof. vm_refl. Qed.
Lemma D_5e808 : decode_any W_5e808 = Some (OpImm ALU_ADD 24 0 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e80c : bv 32 := 0x03d81c93.
Lemma F_5e80c : fetch_word AsanUbsan.M.loaded_segments (0x5e854 : word) = Some W_5e80c.
Proof. vm_refl. Qed.
Lemma D_5e80c : decode_any W_5e80c = Some (ShiftImm ALU_SLL 25 16 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e810 : bv 32 := 0xfffc8c93.
Lemma F_5e810 : fetch_word AsanUbsan.M.loaded_segments (0x5e858 : word) = Some W_5e810.
Proof. vm_refl. Qed.
Lemma D_5e810 : decode_any W_5e810 = Some (OpImm ALU_ADD 25 25 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e814 : bv 32 := 0x0168f2b3.
Lemma F_5e814 : fetch_word AsanUbsan.M.loaded_segments (0x5e85c : word) = Some W_5e814.
Proof. vm_refl. Qed.
Lemma D_5e814 : decode_any W_5e814 = Some (Op ALU_AND 5 17 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e818 : bv 32 := 0x02029663.
Lemma F_5e818 : fetch_word AsanUbsan.M.loaded_segments (0x5e860 : word) = Some W_5e818.
Proof. vm_refl. Qed.
Lemma D_5e818 : decode_any W_5e818 = Some (Branch BC_NE 5 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e81c : bv 32 := 0x0178e2b3.
Lemma F_5e81c : fetch_word AsanUbsan.M.loaded_segments (0x5e864 : word) = Some W_5e81c.
Proof. vm_refl. Qed.
Lemma D_5e81c : decode_any W_5e81c = Some (Op ALU_OR 5 17 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e820 : bv 32 := 0x00587333.
Lemma F_5e820 : fetch_word AsanUbsan.M.loaded_segments (0x5e868 : word) = Some W_5e820.
Proof. vm_refl. Qed.
Lemma D_5e820 : decode_any W_5e820 = Some (Op ALU_AND 6 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e824 : bv 32 := 0x160432af.
Lemma F_5e824 : fetch_word AsanUbsan.M.loaded_segments (0x5e86c : word) = Some W_5e824.
Proof. vm_refl. Qed.
Lemma D_5e824 : decode_any W_5e824 = Some (Lr AD true true 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e828 : bv 32 := 0x01129663.
Lemma F_5e828 : fetch_word AsanUbsan.M.loaded_segments (0x5e870 : word) = Some W_5e828.
Proof. vm_refl. Qed.
Lemma D_5e828 : decode_any W_5e828 = Some (Branch BC_NE 5 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e82c : bv 32 := 0x1a6433af.
Lemma F_5e82c : fetch_word AsanUbsan.M.loaded_segments (0x5e874 : word) = Some W_5e82c.
Proof. vm_refl. Qed.
Lemma D_5e82c : decode_any W_5e82c = Some (Sc AD false true 7 8 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e830 : bv 32 := 0xfe039ae3.
Lemma F_5e830 : fetch_word AsanUbsan.M.loaded_segments (0x5e878 : word) = Some W_5e830.
Proof. vm_refl. Qed.
Lemma D_5e830 : decode_any W_5e830 = Some (Branch BC_NE 7 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e834 : bv 32 := 0x09128c63.
Lemma F_5e834 : fetch_word AsanUbsan.M.loaded_segments (0x5e87c : word) = Some W_5e834.
Proof. vm_refl. Qed.
Lemma D_5e834 : decode_any W_5e834 = Some (Branch BC_EQ 5 17 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8cc : bv 32 := 0x01043783.
Lemma F_5e8cc : fetch_word AsanUbsan.M.loaded_segments (0x5e914 : word) = Some W_5e8cc.
Proof. vm_refl. Qed.
Lemma D_5e8cc : decode_any W_5e8cc = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d0 : bv 32 := 0x14e7e663.
Lemma F_5e8d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e918 : word) = Some W_5e8d0.
Proof. vm_refl. Qed.
Lemma D_5e8d0 : decode_any W_5e8d0 = Some (Branch BC_LTU 15 14 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d4 : bv 32 := 0x40e787b3.
Lemma F_5e8d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e91c : word) = Some W_5e8d4.
Proof. vm_refl. Qed.
Lemma D_5e8d4 : decode_any W_5e8d4 = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d8 : bv 32 := 0x00f43823.
Lemma F_5e8d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e920 : word) = Some W_5e8d8.
Proof. vm_refl. Qed.
Lemma D_5e8d8 : decode_any W_5e8d8 = Some (Store SZ8 8 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8dc : bv 32 := 0x02070463.
Lemma F_5e8dc : fetch_word AsanUbsan.M.loaded_segments (0x5e924 : word) = Some W_5e8dc.
Proof. vm_refl. Qed.
Lemma D_5e8dc : decode_any W_5e8dc = Some (Branch BC_EQ 14 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e0 : bv 32 := 0x00279793.
Lemma F_5e8e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e928 : word) = Some W_5e8e0.
Proof. vm_refl. Qed.
Lemma D_5e8e0 : decode_any W_5e8e0 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e4 : bv 32 := 0x00fa0a33.
Lemma F_5e8e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e92c : word) = Some W_5e8e4.
Proof. vm_refl. Qed.
Lemma D_5e8e4 : decode_any W_5e8e4 = Some (Op ALU_ADD 20 20 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e8 : bv 32 := 0x00271593.
Lemma F_5e8e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e930 : word) = Some W_5e8e8.
Proof. vm_refl. Qed.
Lemma D_5e8e8 : decode_any W_5e8e8 = Some (ShiftImm ALU_SLL 11 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8ec : bv 32 := 0x00b685b3.
Lemma F_5e8ec : fetch_word AsanUbsan.M.loaded_segments (0x5e934 : word) = Some W_5e8ec.
Proof. vm_refl. Qed.
Lemma D_5e8ec : decode_any W_5e8ec = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f0 : bv 32 := 0x000a2603.
Lemma F_5e8f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e938 : word) = Some W_5e8f0.
Proof. vm_refl. Qed.
Lemma D_5e8f0 : decode_any W_5e8f0 = Some (Load SZ4 true 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f4 : bv 32 := 0x00c6a023.
Lemma F_5e8f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e93c : word) = Some W_5e8f4.
Proof. vm_refl. Qed.
Lemma D_5e8f4 : decode_any W_5e8f4 = Some (Store SZ4 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f8 : bv 32 := 0x00468693.
Lemma F_5e8f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e940 : word) = Some W_5e8f8.
Proof. vm_refl. Qed.
Lemma D_5e8f8 : decode_any W_5e8f8 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8fc : bv 32 := 0x004a0a13.
Lemma F_5e8fc : fetch_word AsanUbsan.M.loaded_segments (0x5e944 : word) = Some W_5e8fc.
Proof. vm_refl. Qed.
Lemma D_5e8fc : decode_any W_5e8fc = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e900 : bv 32 := 0xfeb698e3.
Lemma F_5e900 : fetch_word AsanUbsan.M.loaded_segments (0x5e948 : word) = Some W_5e900.
Proof. vm_refl. Qed.
Lemma D_5e900 : decode_any W_5e900 = Some (Branch BC_NE 13 11 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e904 : bv 32 := 0x04843583.
Lemma F_5e904 : fetch_word AsanUbsan.M.loaded_segments (0x5e94c : word) = Some W_5e904.
Proof. vm_refl. Qed.
Lemma D_5e904 : decode_any W_5e904 = Some (Load SZ8 true 11 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e908 : bv 32 := 0x00e585b3.
Lemma F_5e908 : fetch_word AsanUbsan.M.loaded_segments (0x5e950 : word) = Some W_5e908.
Proof. vm_refl. Qed.
Lemma D_5e908 : decode_any W_5e908 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e90c : bv 32 := 0x04b43423.
Lemma F_5e90c : fetch_word AsanUbsan.M.loaded_segments (0x5e954 : word) = Some W_5e90c.
Proof. vm_refl. Qed.
Lemma D_5e90c : decode_any W_5e90c = Some (Store SZ8 8 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e910 : bv 32 := 0x00100493.
Lemma F_5e910 : fetch_word AsanUbsan.M.loaded_segments (0x5e958 : word) = Some W_5e910.
Proof. vm_refl. Qed.
Lemma D_5e910 : decode_any W_5e910 = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e914 : bv 32 := 0x00043603.
Lemma F_5e914 : fetch_word AsanUbsan.M.loaded_segments (0x5e95c : word) = Some W_5e914.
Proof. vm_refl. Qed.
Lemma D_5e914 : decode_any W_5e914 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e918 : bv 32 := 0xfff00893.
Lemma F_5e918 : fetch_word AsanUbsan.M.loaded_segments (0x5e960 : word) = Some W_5e918.
Proof. vm_refl. Qed.
Lemma D_5e918 : decode_any W_5e918 = Some (OpImm ALU_ADD 17 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e91c : bv 32 := 0x00300693.
Lemma F_5e91c : fetch_word AsanUbsan.M.loaded_segments (0x5e964 : word) = Some W_5e91c.
Proof. vm_refl. Qed.
Lemma D_5e91c : decode_any W_5e91c = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e920 : bv 32 := 0x001005b7.
Lemma F_5e920 : fetch_word AsanUbsan.M.loaded_segments (0x5e968 : word) = Some W_5e920.
Proof. vm_refl. Qed.
Lemma D_5e920 : decode_any W_5e920 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e924 : bv 32 := 0xfffb2717.
Lemma F_5e924 : fetch_word AsanUbsan.M.loaded_segments (0x5e96c : word) = Some W_5e924.
Proof. vm_refl. Qed.
Lemma D_5e924 : decode_any W_5e924 = Some (Auipc 14 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e928 : bv 32 := 0x03c89793.
Lemma F_5e928 : fetch_word AsanUbsan.M.loaded_segments (0x5e970 : word) = Some W_5e928.
Proof. vm_refl. Qed.
Lemma D_5e928 : decode_any W_5e928 = Some (ShiftImm ALU_SLL 15 17 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e92c : bv 32 := 0x03d69693.
Lemma F_5e92c : fetch_word AsanUbsan.M.loaded_segments (0x5e974 : word) = Some W_5e92c.
Proof. vm_refl. Qed.
Lemma D_5e92c : decode_any W_5e92c = Some (ShiftImm ALU_SLL 13 13 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e930 : bv 32 := 0xfff58593.
Lemma F_5e930 : fetch_word AsanUbsan.M.loaded_segments (0x5e978 : word) = Some W_5e930.
Proof. vm_refl. Qed.
Lemma D_5e930 : decode_any W_5e930 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e934 : bv 32 := 0xaec73703.
Lemma F_5e934 : fetch_word AsanUbsan.M.loaded_segments (0x5e97c : word) = Some W_5e934.
Proof. vm_refl. Qed.
Lemma D_5e934 : decode_any W_5e934 = Some (Load SZ8 true 14 14 2796, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e938 : bv 32 := 0xfff78793.
Lemma F_5e938 : fetch_word AsanUbsan.M.loaded_segments (0x5e980 : word) = Some W_5e938.
Proof. vm_refl. Qed.
Lemma D_5e938 : decode_any W_5e938 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e93c : bv 32 := 0x02859813.
Lemma F_5e93c : fetch_word AsanUbsan.M.loaded_segments (0x5e984 : word) = Some W_5e93c.
Proof. vm_refl. Qed.
Lemma D_5e93c : decode_any W_5e93c = Some (ShiftImm ALU_SLL 16 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e940 : bv 32 := 0x02889893.
Lemma F_5e940 : fetch_word AsanUbsan.M.loaded_segments (0x5e988 : word) = Some W_5e940.
Proof. vm_refl. Qed.
Lemma D_5e940 : decode_any W_5e940 = Some (ShiftImm ALU_SLL 17 17 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e944 : bv 32 := 0x00100293.
Lemma F_5e944 : fetch_word AsanUbsan.M.loaded_segments (0x5e98c : word) = Some W_5e944.
Proof. vm_refl. Qed.
Lemma D_5e944 : decode_any W_5e944 = Some (OpImm ALU_ADD 5 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e948 : bv 32 := 0x03e29293.
Lemma F_5e948 : fetch_word AsanUbsan.M.loaded_segments (0x5e990 : word) = Some W_5e948.
Proof. vm_refl. Qed.
Lemma D_5e948 : decode_any W_5e948 = Some (ShiftImm ALU_SLL 5 5 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e94c : bv 32 := 0x01c0006f.
Lemma F_5e94c : fetch_word AsanUbsan.M.loaded_segments (0x5e994 : word) = Some W_5e94c.
Proof. vm_refl. Qed.
Lemma D_5e94c : decode_any W_5e94c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e950 : bv 32 := 0x160433af.
Lemma F_5e950 : fetch_word AsanUbsan.M.loaded_segments (0x5e998 : word) = Some W_5e950.
Proof. vm_refl. Qed.
Lemma D_5e950 : decode_any W_5e950 = Some (Lr AD true true 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e954 : bv 32 := 0x00c39663.
Lemma F_5e954 : fetch_word AsanUbsan.M.loaded_segments (0x5e99c : word) = Some W_5e954.
Proof. vm_refl. Qed.
Lemma D_5e954 : decode_any W_5e954 = Some (Branch BC_NE 7 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e958 : bv 32 := 0x1a643e2f.
Lemma F_5e958 : fetch_word AsanUbsan.M.loaded_segments (0x5e9a0 : word) = Some W_5e958.
Proof. vm_refl. Qed.
Lemma D_5e958 : decode_any W_5e958 = Some (Sc AD false true 28 8 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e95c : bv 32 := 0xfe0e1ae3.
Lemma F_5e95c : fetch_word AsanUbsan.M.loaded_segments (0x5e9a4 : word) = Some W_5e95c.
Proof. vm_refl. Qed.
Lemma D_5e95c : decode_any W_5e95c = Some (Branch BC_NE 28 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e960 : bv 32 := 0x06c38463.
Lemma F_5e960 : fetch_word AsanUbsan.M.loaded_segments (0x5e9a8 : word) = Some W_5e960.
Proof. vm_refl. Qed.
Lemma D_5e960 : decode_any W_5e960 = Some (Branch BC_EQ 7 12 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e968 : bv 32 := 0x00d675b3.
Lemma F_5e968 : fetch_word AsanUbsan.M.loaded_segments (0x5e9b0 : word) = Some W_5e968.
Proof. vm_refl. Qed.
Lemma D_5e968 : decode_any W_5e968 = Some (Op ALU_AND 11 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e96c : bv 32 := 0x00f67333.
Lemma F_5e96c : fetch_word AsanUbsan.M.loaded_segments (0x5e9b4 : word) = Some W_5e96c.
Proof. vm_refl. Qed.
Lemma D_5e96c : decode_any W_5e96c = Some (Op ALU_AND 6 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e970 : bv 32 := 0x02059663.
Lemma F_5e970 : fetch_word AsanUbsan.M.loaded_segments (0x5e9b8 : word) = Some W_5e970.
Proof. vm_refl. Qed.
Lemma D_5e970 : decode_any W_5e970 = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e974 : bv 32 := 0x010675b3.
Lemma F_5e974 : fetch_word AsanUbsan.M.loaded_segments (0x5e9bc : word) = Some W_5e974.
Proof. vm_refl. Qed.
Lemma D_5e974 : decode_any W_5e974 = Some (Op ALU_AND 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e978 : bv 32 := 0x02058263.
Lemma F_5e978 : fetch_word AsanUbsan.M.loaded_segments (0x5e9c0 : word) = Some W_5e978.
Proof. vm_refl. Qed.
Lemma D_5e978 : decode_any W_5e978 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e99c : bv 32 := 0x013675b3.
Lemma F_5e99c : fetch_word AsanUbsan.M.loaded_segments (0x5e9e4 : word) = Some W_5e99c.
Proof. vm_refl. Qed.
Lemma D_5e99c : decode_any W_5e99c = Some (Op ALU_AND 11 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9a0 : bv 32 := 0x00b035b3.
Lemma F_5e9a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e9e8 : word) = Some W_5e9a0.
Proof. vm_refl. Qed.
Lemma D_5e9a0 : decode_any W_5e9a0 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9a4 : bv 32 := 0x01465393.
Lemma F_5e9a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e9ec : word) = Some W_5e9a4.
Proof. vm_refl. Qed.
Lemma D_5e9a4 : decode_any W_5e9a4 = Some (ShiftImm ALU_SRL 7 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9a8 : bv 32 := 0xfff58593.
Lemma F_5e9a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e9f0 : word) = Some W_5e9a8.
Proof. vm_refl. Qed.
Lemma D_5e9a8 : decode_any W_5e9a8 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9ac : bv 32 := 0x00b3f5b3.
Lemma F_5e9ac : fetch_word AsanUbsan.M.loaded_segments (0x5e9f4 : word) = Some W_5e9ac.
Proof. vm_refl. Qed.
Lemma D_5e9ac : decode_any W_5e9ac = Some (Op ALU_AND 11 7 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9b0 : bv 32 := 0x02c59593.
Lemma F_5e9b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e9f8 : word) = Some W_5e9b0.
Proof. vm_refl. Qed.
Lemma D_5e9b0 : decode_any W_5e9b0 = Some (ShiftImm ALU_SLL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9b4 : bv 32 := 0x02c5d593.
Lemma F_5e9b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e9fc : word) = Some W_5e9b4.
Proof. vm_refl. Qed.
Lemma D_5e9b4 : decode_any W_5e9b4 = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9b8 : bv 32 := 0xf8058ce3.
Lemma F_5e9b8 : fetch_word AsanUbsan.M.loaded_segments (0x5ea00 : word) = Some W_5e9b8.
Proof. vm_refl. Qed.
Lemma D_5e9b8 : decode_any W_5e9b8 = Some (Branch BC_EQ 11 0 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9c8 : bv 32 := 0x00058a63.
Lemma F_5e9c8 : fetch_word AsanUbsan.M.loaded_segments (0x5ea10 : word) = Some W_5e9c8.
Proof. vm_refl. Qed.
Lemma D_5e9c8 : decode_any W_5e9c8 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9dc : bv 32 := 0x00048513.
Lemma F_5e9dc : fetch_word AsanUbsan.M.loaded_segments (0x5ea24 : word) = Some W_5e9dc.
Proof. vm_refl. Qed.
Lemma D_5e9dc : decode_any W_5e9dc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e0 : bv 32 := 0x07813083.
Lemma F_5e9e0 : fetch_word AsanUbsan.M.loaded_segments (0x5ea28 : word) = Some W_5e9e0.
Proof. vm_refl. Qed.
Lemma D_5e9e0 : decode_any W_5e9e0 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e4 : bv 32 := 0x07013403.
Lemma F_5e9e4 : fetch_word AsanUbsan.M.loaded_segments (0x5ea2c : word) = Some W_5e9e4.
Proof. vm_refl. Qed.
Lemma D_5e9e4 : decode_any W_5e9e4 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e8 : bv 32 := 0x06813483.
Lemma F_5e9e8 : fetch_word AsanUbsan.M.loaded_segments (0x5ea30 : word) = Some W_5e9e8.
Proof. vm_refl. Qed.
Lemma D_5e9e8 : decode_any W_5e9e8 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9ec : bv 32 := 0x06013903.
Lemma F_5e9ec : fetch_word AsanUbsan.M.loaded_segments (0x5ea34 : word) = Some W_5e9ec.
Proof. vm_refl. Qed.
Lemma D_5e9ec : decode_any W_5e9ec = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9f0 : bv 32 := 0x05813983.
Lemma F_5e9f0 : fetch_word AsanUbsan.M.loaded_segments (0x5ea38 : word) = Some W_5e9f0.
Proof. vm_refl. Qed.
Lemma D_5e9f0 : decode_any W_5e9f0 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9f4 : bv 32 := 0x05013a03.
Lemma F_5e9f4 : fetch_word AsanUbsan.M.loaded_segments (0x5ea3c : word) = Some W_5e9f4.
Proof. vm_refl. Qed.
Lemma D_5e9f4 : decode_any W_5e9f4 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9f8 : bv 32 := 0x04813a83.
Lemma F_5e9f8 : fetch_word AsanUbsan.M.loaded_segments (0x5ea40 : word) = Some W_5e9f8.
Proof. vm_refl. Qed.
Lemma D_5e9f8 : decode_any W_5e9f8 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9fc : bv 32 := 0x04013b03.
Lemma F_5e9fc : fetch_word AsanUbsan.M.loaded_segments (0x5ea44 : word) = Some W_5e9fc.
Proof. vm_refl. Qed.
Lemma D_5e9fc : decode_any W_5e9fc = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea00 : bv 32 := 0x03813b83.
Lemma F_5ea00 : fetch_word AsanUbsan.M.loaded_segments (0x5ea48 : word) = Some W_5ea00.
Proof. vm_refl. Qed.
Lemma D_5ea00 : decode_any W_5ea00 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea04 : bv 32 := 0x03013c03.
Lemma F_5ea04 : fetch_word AsanUbsan.M.loaded_segments (0x5ea4c : word) = Some W_5ea04.
Proof. vm_refl. Qed.
Lemma D_5ea04 : decode_any W_5ea04 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea08 : bv 32 := 0x02813c83.
Lemma F_5ea08 : fetch_word AsanUbsan.M.loaded_segments (0x5ea50 : word) = Some W_5ea08.
Proof. vm_refl. Qed.
Lemma D_5ea08 : decode_any W_5ea08 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea0c : bv 32 := 0x02013d03.
Lemma F_5ea0c : fetch_word AsanUbsan.M.loaded_segments (0x5ea54 : word) = Some W_5ea0c.
Proof. vm_refl. Qed.
Lemma D_5ea0c : decode_any W_5ea0c = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea10 : bv 32 := 0x01813d83.
Lemma F_5ea10 : fetch_word AsanUbsan.M.loaded_segments (0x5ea58 : word) = Some W_5ea10.
Proof. vm_refl. Qed.
Lemma D_5ea10 : decode_any W_5ea10 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea14 : bv 32 := 0x08010113.
Lemma F_5ea14 : fetch_word AsanUbsan.M.loaded_segments (0x5ea5c : word) = Some W_5ea14.
Proof. vm_refl. Qed.
Lemma D_5ea14 : decode_any W_5ea14 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea18 : bv 32 := 0x00008067.
Lemma F_5ea18 : fetch_word AsanUbsan.M.loaded_segments (0x5ea60 : word) = Some W_5ea18.
Proof. vm_refl. Qed.
Lemma D_5ea18 : decode_any W_5ea18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea1c : bv 32 := 0x00068a93.
Lemma F_5ea1c : fetch_word AsanUbsan.M.loaded_segments (0x5ea64 : word) = Some W_5ea1c.
Proof. vm_refl. Qed.
Lemma D_5ea1c : decode_any W_5ea1c = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea20 : bv 32 := 0x00050913.
Lemma F_5ea20 : fetch_word AsanUbsan.M.loaded_segments (0x5ea68 : word) = Some W_5ea20.
Proof. vm_refl. Qed.
Lemma D_5ea20 : decode_any W_5ea20 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea24 : bv 32 := 0x00070b13.
Lemma F_5ea24 : fetch_word AsanUbsan.M.loaded_segments (0x5ea6c : word) = Some W_5ea24.
Proof. vm_refl. Qed.
Lemma D_5ea24 : decode_any W_5ea24 = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea28 : bv 32 := 0x40f70733.
Lemma F_5ea28 : fetch_word AsanUbsan.M.loaded_segments (0x5ea70 : word) = Some W_5ea28.
Proof. vm_refl. Qed.
Lemma D_5ea28 : decode_any W_5ea28 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea2c : bv 32 := 0x00048513.
Lemma F_5ea2c : fetch_word AsanUbsan.M.loaded_segments (0x5ea74 : word) = Some W_5ea2c.
Proof. vm_refl. Qed.
Lemma D_5ea2c : decode_any W_5ea2c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea30 : bv 32 := 0x00040693.
Lemma F_5ea30 : fetch_word AsanUbsan.M.loaded_segments (0x5ea78 : word) = Some W_5ea30.
Proof. vm_refl. Qed.
Lemma D_5ea30 : decode_any W_5ea30 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea34 : bv 32 := 0x050000ef.
Lemma F_5ea34 : fetch_word AsanUbsan.M.loaded_segments (0x5ea7c : word) = Some W_5ea34.
Proof. vm_refl. Qed.
Lemma D_5ea34 : decode_any W_5ea34 = Some (Jal 1 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea38 : bv 32 := 0x02050263.
Lemma F_5ea38 : fetch_word AsanUbsan.M.loaded_segments (0x5ea80 : word) = Some W_5ea38.
Proof. vm_refl. Qed.
Lemma D_5ea38 : decode_any W_5ea38 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea3c : bv 32 := 0x01043783.
Lemma F_5ea3c : fetch_word AsanUbsan.M.loaded_segments (0x5ea84 : word) = Some W_5ea3c.
Proof. vm_refl. Qed.
Lemma D_5ea3c : decode_any W_5ea3c = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea40 : bv 32 := 0x000b0713.
Lemma F_5ea40 : fetch_word AsanUbsan.M.loaded_segments (0x5ea88 : word) = Some W_5ea40.
Proof. vm_refl. Qed.
Lemma D_5ea40 : decode_any W_5ea40 = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea44 : bv 32 := 0x0367e263.
Lemma F_5ea44 : fetch_word AsanUbsan.M.loaded_segments (0x5ea8c : word) = Some W_5ea44.
Proof. vm_refl. Qed.
Lemma D_5ea44 : decode_any W_5ea44 = Some (Branch BC_LTU 15 22 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea48 : bv 32 := 0x000a8693.
Lemma F_5ea48 : fetch_word AsanUbsan.M.loaded_segments (0x5ea90 : word) = Some W_5ea48.
Proof. vm_refl. Qed.
Lemma D_5ea48 : decode_any W_5ea48 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea4c : bv 32 := 0x40e787b3.
Lemma F_5ea4c : fetch_word AsanUbsan.M.loaded_segments (0x5ea94 : word) = Some W_5ea4c.
Proof. vm_refl. Qed.
Lemma D_5ea4c : decode_any W_5ea4c = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea50 : bv 32 := 0x00f43823.
Lemma F_5ea50 : fetch_word AsanUbsan.M.loaded_segments (0x5ea98 : word) = Some W_5ea50.
Proof. vm_refl. Qed.
Lemma D_5ea50 : decode_any W_5ea50 = Some (Store SZ8 8 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea54 : bv 32 := 0x00090513.
Lemma F_5ea54 : fetch_word AsanUbsan.M.loaded_segments (0x5ea9c : word) = Some W_5ea54.
Proof. vm_refl. Qed.
Lemma D_5ea54 : decode_any W_5ea54 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea58 : bv 32 := 0xe89ff06f.
Lemma F_5ea58 : fetch_word AsanUbsan.M.loaded_segments (0x5eaa0 : word) = Some W_5ea58.
Proof. vm_refl. Qed.
Lemma D_5ea58 : decode_any W_5ea58 = Some (Jal 0 2096776, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea84 : bv 32 := 0xfc010113.
Lemma F_5ea84 : fetch_word AsanUbsan.M.loaded_segments (0x5eacc : word) = Some W_5ea84.
Proof. vm_refl. Qed.
Lemma D_5ea84 : decode_any W_5ea84 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea88 : bv 32 := 0x02113c23.
Lemma F_5ea88 : fetch_word AsanUbsan.M.loaded_segments (0x5ead0 : word) = Some W_5ea88.
Proof. vm_refl. Qed.
Lemma D_5ea88 : decode_any W_5ea88 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea8c : bv 32 := 0x02813823.
Lemma F_5ea8c : fetch_word AsanUbsan.M.loaded_segments (0x5ead4 : word) = Some W_5ea8c.
Proof. vm_refl. Qed.
Lemma D_5ea8c : decode_any W_5ea8c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea90 : bv 32 := 0x02913423.
Lemma F_5ea90 : fetch_word AsanUbsan.M.loaded_segments (0x5ead8 : word) = Some W_5ea90.
Proof. vm_refl. Qed.
Lemma D_5ea90 : decode_any W_5ea90 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea94 : bv 32 := 0x03213023.
Lemma F_5ea94 : fetch_word AsanUbsan.M.loaded_segments (0x5eadc : word) = Some W_5ea94.
Proof. vm_refl. Qed.
Lemma D_5ea94 : decode_any W_5ea94 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea98 : bv 32 := 0x01313c23.
Lemma F_5ea98 : fetch_word AsanUbsan.M.loaded_segments (0x5eae0 : word) = Some W_5ea98.
Proof. vm_refl. Qed.
Lemma D_5ea98 : decode_any W_5ea98 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea9c : bv 32 := 0x01413823.
Lemma F_5ea9c : fetch_word AsanUbsan.M.loaded_segments (0x5eae4 : word) = Some W_5ea9c.
Proof. vm_refl. Qed.
Lemma D_5ea9c : decode_any W_5ea9c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa0 : bv 32 := 0x01513423.
Lemma F_5eaa0 : fetch_word AsanUbsan.M.loaded_segments (0x5eae8 : word) = Some W_5eaa0.
Proof. vm_refl. Qed.
Lemma D_5eaa0 : decode_any W_5eaa0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa4 : bv 32 := 0x01613023.
Lemma F_5eaa4 : fetch_word AsanUbsan.M.loaded_segments (0x5eaec : word) = Some W_5eaa4.
Proof. vm_refl. Qed.
Lemma D_5eaa4 : decode_any W_5eaa4 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa8 : bv 32 := 0x00068413.
Lemma F_5eaa8 : fetch_word AsanUbsan.M.loaded_segments (0x5eaf0 : word) = Some W_5eaa8.
Proof. vm_refl. Qed.
Lemma D_5eaa8 : decode_any W_5eaa8 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaac : bv 32 := 0x00058493.
Lemma F_5eaac : fetch_word AsanUbsan.M.loaded_segments (0x5eaf4 : word) = Some W_5eaac.
Proof. vm_refl. Qed.
Lemma D_5eaac : decode_any W_5eaac = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eab0 : bv 32 := 0x02053903.
Lemma F_5eab0 : fetch_word AsanUbsan.M.loaded_segments (0x5eaf8 : word) = Some W_5eab0.
Proof. vm_refl. Qed.
Lemma D_5eab0 : decode_any W_5eab0 = Some (Load SZ8 true 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eab4 : bv 32 := 0x01f00693.
Lemma F_5eab4 : fetch_word AsanUbsan.M.loaded_segments (0x5eafc : word) = Some W_5eab4.
Proof. vm_refl. Qed.
Lemma D_5eab4 : decode_any W_5eab4 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eab8 : bv 32 := 0x02061593.
Lemma F_5eab8 : fetch_word AsanUbsan.M.loaded_segments (0x5eb00 : word) = Some W_5eab8.
Proof. vm_refl. Qed.
Lemma D_5eab8 : decode_any W_5eab8 = Some (ShiftImm ALU_SLL 11 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eabc : bv 32 := 0x20d60263.
Lemma F_5eabc : fetch_word AsanUbsan.M.loaded_segments (0x5eb04 : word) = Some W_5eabc.
Proof. vm_refl. Qed.
Lemma D_5eabc : decode_any W_5eabc = Some (Branch BC_EQ 12 13 516, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eac0 : bv 32 := 0x01000693.
Lemma F_5eac0 : fetch_word AsanUbsan.M.loaded_segments (0x5eb08 : word) = Some W_5eac0.
Proof. vm_refl. Qed.
Lemma D_5eac0 : decode_any W_5eac0 = Some (OpImm ALU_ADD 13 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eac4 : bv 32 := 0x02c6e263.
Lemma F_5eac4 : fetch_word AsanUbsan.M.loaded_segments (0x5eb0c : word) = Some W_5eac4.
Proof. vm_refl. Qed.
Lemma D_5eac4 : decode_any W_5eac4 = Some (Branch BC_LTU 13 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eac8 : bv 32 := 0x00561a93.
Lemma F_5eac8 : fetch_word AsanUbsan.M.loaded_segments (0x5eb10 : word) = Some W_5eac8.
Proof. vm_refl. Qed.
Lemma D_5eac8 : decode_any W_5eac8 = Some (ShiftImm ALU_SLL 21 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eacc : bv 32 := 0x02043683.
Lemma F_5eacc : fetch_word AsanUbsan.M.loaded_segments (0x5eb14 : word) = Some W_5eacc.
Proof. vm_refl. Qed.
Lemma D_5eacc : decode_any W_5eacc = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ead0 : bv 32 := 0x03043a03.
Lemma F_5ead0 : fetch_word AsanUbsan.M.loaded_segments (0x5eb18 : word) = Some W_5ead0.
Proof. vm_refl. Qed.
Lemma D_5ead0 : decode_any W_5ead0 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ead4 : bv 32 := 0x02ea89b3.
Lemma F_5ead4 : fetch_word AsanUbsan.M.loaded_segments (0x5eb1c : word) = Some W_5ead4.
Proof. vm_refl. Qed.
Lemma D_5ead4 : decode_any W_5ead4 = Some (Mul M_MUL 19 21 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ead8 : bv 32 := 0x013689b3.
Lemma F_5ead8 : fetch_word AsanUbsan.M.loaded_segments (0x5eb20 : word) = Some W_5ead8.
Proof. vm_refl. Qed.
Lemma D_5ead8 : decode_any W_5ead8 = Some (Op ALU_ADD 19 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eadc : bv 32 := 0x00b90933.
Lemma F_5eadc : fetch_word AsanUbsan.M.loaded_segments (0x5eb24 : word) = Some W_5eadc.
Proof. vm_refl. Qed.
Lemma D_5eadc : decode_any W_5eadc = Some (Op ALU_ADD 18 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eae0 : bv 32 := 0x053a6263.
Lemma F_5eae0 : fetch_word AsanUbsan.M.loaded_segments (0x5eb28 : word) = Some W_5eae0.
Proof. vm_refl. Qed.
Lemma D_5eae0 : decode_any W_5eae0 = Some (Branch BC_LTU 20 19 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eae8 : bv 32 := 0xff060693.
Lemma F_5eae8 : fetch_word AsanUbsan.M.loaded_segments (0x5eb30 : word) = Some W_5eae8.
Proof. vm_refl. Qed.
Lemma D_5eae8 : decode_any W_5eae8 = Some (OpImm ALU_ADD 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaec : bv 32 := 0x20000793.
Lemma F_5eaec : fetch_word AsanUbsan.M.loaded_segments (0x5eb34 : word) = Some W_5eaec.
Proof. vm_refl. Qed.
Lemma D_5eaec : decode_any W_5eaec = Some (OpImm ALU_ADD 15 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaf0 : bv 32 := 0x03f61813.
Lemma F_5eaf0 : fetch_word AsanUbsan.M.loaded_segments (0x5eb38 : word) = Some W_5eaf0.
Proof. vm_refl. Qed.
Lemma D_5eaf0 : decode_any W_5eaf0 = Some (ShiftImm ALU_SLL 16 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaf4 : bv 32 := 0x0016d693.
Lemma F_5eaf4 : fetch_word AsanUbsan.M.loaded_segments (0x5eb3c : word) = Some W_5eaf4.
Proof. vm_refl. Qed.
Lemma D_5eaf4 : decode_any W_5eaf4 = Some (ShiftImm ALU_SRL 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaf8 : bv 32 := 0x00d79ab3.
Lemma F_5eaf8 : fetch_word AsanUbsan.M.loaded_segments (0x5eb40 : word) = Some W_5eaf8.
Proof. vm_refl. Qed.
Lemma D_5eaf8 : decode_any W_5eaf8 = Some (Op ALU_SLL 21 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eafc : bv 32 := 0x001ad693.
Lemma F_5eafc : fetch_word AsanUbsan.M.loaded_segments (0x5eb44 : word) = Some W_5eafc.
Proof. vm_refl. Qed.
Lemma D_5eafc : decode_any W_5eafc = Some (ShiftImm ALU_SRL 13 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb00 : bv 32 := 0x43f85793.
Lemma F_5eb00 : fetch_word AsanUbsan.M.loaded_segments (0x5eb48 : word) = Some W_5eb00.
Proof. vm_refl. Qed.
Lemma D_5eb00 : decode_any W_5eb00 = Some (ShiftImm ALU_SRA 15 16 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb04 : bv 32 := 0x00d7f6b3.
Lemma F_5eb04 : fetch_word AsanUbsan.M.loaded_segments (0x5eb4c : word) = Some W_5eb04.
Proof. vm_refl. Qed.
Lemma D_5eb04 : decode_any W_5eb04 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb08 : bv 32 := 0x01568ab3.
Lemma F_5eb08 : fetch_word AsanUbsan.M.loaded_segments (0x5eb50 : word) = Some W_5eb08.
Proof. vm_refl. Qed.
Lemma D_5eb08 : decode_any W_5eb08 = Some (Op ALU_ADD 21 13 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb0c : bv 32 := 0x02043683.
Lemma F_5eb0c : fetch_word AsanUbsan.M.loaded_segments (0x5eb54 : word) = Some W_5eb0c.
Proof. vm_refl. Qed.
Lemma D_5eb0c : decode_any W_5eb0c = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb10 : bv 32 := 0x03043a03.
Lemma F_5eb10 : fetch_word AsanUbsan.M.loaded_segments (0x5eb58 : word) = Some W_5eb10.
Proof. vm_refl. Qed.
Lemma D_5eb10 : decode_any W_5eb10 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb14 : bv 32 := 0x02ea89b3.
Lemma F_5eb14 : fetch_word AsanUbsan.M.loaded_segments (0x5eb5c : word) = Some W_5eb14.
Proof. vm_refl. Qed.
Lemma D_5eb14 : decode_any W_5eb14 = Some (Mul M_MUL 19 21 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb18 : bv 32 := 0x013689b3.
Lemma F_5eb18 : fetch_word AsanUbsan.M.loaded_segments (0x5eb60 : word) = Some W_5eb18.
Proof. vm_refl. Qed.
Lemma D_5eb18 : decode_any W_5eb18 = Some (Op ALU_ADD 19 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb1c : bv 32 := 0x00b90933.
Lemma F_5eb1c : fetch_word AsanUbsan.M.loaded_segments (0x5eb64 : word) = Some W_5eb1c.
Proof. vm_refl. Qed.
Lemma D_5eb1c : decode_any W_5eb1c = Some (Op ALU_ADD 18 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb20 : bv 32 := 0x0d3a7c63.
Lemma F_5eb20 : fetch_word AsanUbsan.M.loaded_segments (0x5eb68 : word) = Some W_5eb20.
Proof. vm_refl. Qed.
Lemma D_5eb20 : decode_any W_5eb20 = Some (Branch BC_GEU 20 19 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb24 : bv 32 := 0x1a0a0e63.
Lemma F_5eb24 : fetch_word AsanUbsan.M.loaded_segments (0x5eb6c : word) = Some W_5eb24.
Proof. vm_refl. Qed.
Lemma D_5eb24 : decode_any W_5eb24 = Some (Branch BC_EQ 20 0 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb28 : bv 32 := 0xfffa4593.
Lemma F_5eb28 : fetch_word AsanUbsan.M.loaded_segments (0x5eb70 : word) = Some W_5eb28.
Proof. vm_refl. Qed.
Lemma D_5eb28 : decode_any W_5eb28 = Some (OpImm ALU_XOR 11 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb2c : bv 32 := 0xfffc06b7.
Lemma F_5eb2c : fetch_word AsanUbsan.M.loaded_segments (0x5eb74 : word) = Some W_5eb2c.
Proof. vm_refl. Qed.
Lemma D_5eb2c : decode_any W_5eb2c = Some (Lui 13 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb30 : bv 32 := 0x00b985b3.
Lemma F_5eb30 : fetch_word AsanUbsan.M.loaded_segments (0x5eb78 : word) = Some W_5eb30.
Proof. vm_refl. Qed.
Lemma D_5eb30 : decode_any W_5eb30 = Some (Op ALU_ADD 11 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb34 : bv 32 := 0x000409b7.
Lemma F_5eb34 : fetch_word AsanUbsan.M.loaded_segments (0x5eb7c : word) = Some W_5eb34.
Proof. vm_refl. Qed.
Lemma D_5eb34 : decode_any W_5eb34 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb38 : bv 32 := 0x00d5f5b3.
Lemma F_5eb38 : fetch_word AsanUbsan.M.loaded_segments (0x5eb80 : word) = Some W_5eb38.
Proof. vm_refl. Qed.
Lemma D_5eb38 : decode_any W_5eb38 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb3c : bv 32 := 0x03843683.
Lemma F_5eb3c : fetch_word AsanUbsan.M.loaded_segments (0x5eb84 : word) = Some W_5eb3c.
Proof. vm_refl. Qed.
Lemma D_5eb3c : decode_any W_5eb3c = Some (Load SZ8 true 13 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb40 : bv 32 := 0x013589b3.
Lemma F_5eb40 : fetch_word AsanUbsan.M.loaded_segments (0x5eb88 : word) = Some W_5eb40.
Proof. vm_refl. Qed.
Lemma D_5eb40 : decode_any W_5eb40 = Some (Op ALU_ADD 19 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb44 : bv 32 := 0x00700593.
Lemma F_5eb44 : fetch_word AsanUbsan.M.loaded_segments (0x5eb8c : word) = Some W_5eb44.
Proof. vm_refl. Qed.
Lemma D_5eb44 : decode_any W_5eb44 = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb48 : bv 32 := 0x01d59593.
Lemma F_5eb48 : fetch_word AsanUbsan.M.loaded_segments (0x5eb90 : word) = Some W_5eb48.
Proof. vm_refl. Qed.
Lemma D_5eb48 : decode_any W_5eb48 = Some (ShiftImm ALU_SLL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb4c : bv 32 := 0x014686b3.
Lemma F_5eb4c : fetch_word AsanUbsan.M.loaded_segments (0x5eb94 : word) = Some W_5eb4c.
Proof. vm_refl. Qed.
Lemma D_5eb4c : decode_any W_5eb4c = Some (Op ALU_ADD 13 13 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb50 : bv 32 := 0x013686b3.
Lemma F_5eb50 : fetch_word AsanUbsan.M.loaded_segments (0x5eb98 : word) = Some W_5eb50.
Proof. vm_refl. Qed.
Lemma D_5eb50 : decode_any W_5eb50 = Some (Op ALU_ADD 13 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb54 : bv 32 := 0x00158593.
Lemma F_5eb54 : fetch_word AsanUbsan.M.loaded_segments (0x5eb9c : word) = Some W_5eb54.
Proof. vm_refl. Qed.
Lemma D_5eb54 : decode_any W_5eb54 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb58 : bv 32 := 0x1ab6fa63.
Lemma F_5eb58 : fetch_word AsanUbsan.M.loaded_segments (0x5eba0 : word) = Some W_5eb58.
Proof. vm_refl. Qed.
Lemma D_5eb58 : decode_any W_5eb58 = Some (Branch BC_GEU 13 11 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb5c : bv 32 := 0x03854583.
Lemma F_5eb5c : fetch_word AsanUbsan.M.loaded_segments (0x5eba4 : word) = Some W_5eb5c.
Proof. vm_refl. Qed.
Lemma D_5eb5c : decode_any W_5eb5c = Some (Load SZ1 false 11 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb60 : bv 32 := 0x012a0a33.
Lemma F_5eb60 : fetch_word AsanUbsan.M.loaded_segments (0x5eba8 : word) = Some W_5eb60.
Proof. vm_refl. Qed.
Lemma D_5eb60 : decode_any W_5eb60 = Some (Op ALU_ADD 20 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb64 : bv 32 := 0x02058463.
Lemma F_5eb64 : fetch_word AsanUbsan.M.loaded_segments (0x5ebac : word) = Some W_5eb64.
Proof. vm_refl. Qed.
Lemma D_5eb64 : decode_any W_5eb64 = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb8c : bv 32 := 0xfffb9597.
Lemma F_5eb8c : fetch_word AsanUbsan.M.loaded_segments (0x5ebd4 : word) = Some W_5eb8c.
Proof. vm_refl. Qed.
Lemma D_5eb8c : decode_any W_5eb8c = Some (Auipc 11 1048505, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb90 : bv 32 := 0x36158693.
Lemma F_5eb90 : fetch_word AsanUbsan.M.loaded_segments (0x5ebd8 : word) = Some W_5eb90.
Proof. vm_refl. Qed.
Lemma D_5eb90 : decode_any W_5eb90 = Some (OpImm ALU_ADD 13 11 865, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb94 : bv 32 := 0x00050b13.
Lemma F_5eb94 : fetch_word AsanUbsan.M.loaded_segments (0x5ebdc : word) = Some W_5eb94.
Proof. vm_refl. Qed.
Lemma D_5eb94 : decode_any W_5eb94 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb98 : bv 32 := 0x000a0593.
Lemma F_5eb98 : fetch_word AsanUbsan.M.loaded_segments (0x5ebe0 : word) = Some W_5eb98.
Proof. vm_refl. Qed.
Lemma D_5eb98 : decode_any W_5eb98 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb9c : bv 32 := 0x00098613.
Lemma F_5eb9c : fetch_word AsanUbsan.M.loaded_segments (0x5ebe4 : word) = Some W_5eb9c.
Proof. vm_refl. Qed.
Lemma D_5eb9c : decode_any W_5eb9c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eba0 : bv 32 := 0x5843e0ef.
Lemma F_5eba0 : fetch_word AsanUbsan.M.loaded_segments (0x5ebe8 : word) = Some W_5eba0.
Proof. vm_refl. Qed.
Lemma D_5eba0 : decode_any W_5eba0 = Some (Jal 1 255364, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eba4 : bv 32 := 0x16050863.
Lemma F_5eba4 : fetch_word AsanUbsan.M.loaded_segments (0x5ebec : word) = Some W_5eba4.
Proof. vm_refl. Qed.
Lemma D_5eba4 : decode_any W_5eba4 = Some (Branch BC_EQ 10 0 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eba8 : bv 32 := 0x00050713.
Lemma F_5eba8 : fetch_word AsanUbsan.M.loaded_segments (0x5ebf0 : word) = Some W_5eba8.
Proof. vm_refl. Qed.
Lemma D_5eba8 : decode_any W_5eba8 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebac : bv 32 := 0x1eaa1063.
Lemma F_5ebac : fetch_word AsanUbsan.M.loaded_segments (0x5ebf4 : word) = Some W_5ebac.
Proof. vm_refl. Qed.
Lemma D_5ebac : decode_any W_5ebac = Some (Branch BC_NE 20 10 480, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebb0 : bv 32 := 0x0fa00613.
Lemma F_5ebb0 : fetch_word AsanUbsan.M.loaded_segments (0x5ebf8 : word) = Some W_5ebb0.
Proof. vm_refl. Qed.
Lemma D_5ebb0 : decode_any W_5ebb0 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebb4 : bv 32 := 0x000a0513.
Lemma F_5ebb4 : fetch_word AsanUbsan.M.loaded_segments (0x5ebfc : word) = Some W_5ebb4.
Proof. vm_refl. Qed.
Lemma D_5ebb4 : decode_any W_5ebb4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebb8 : bv 32 := 0x00098593.
Lemma F_5ebb8 : fetch_word AsanUbsan.M.loaded_segments (0x5ec00 : word) = Some W_5ebb8.
Proof. vm_refl. Qed.
Lemma D_5ebb8 : decode_any W_5ebb8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebbc : bv 32 := 0x4d4230ef.
Lemma F_5ebbc : fetch_word AsanUbsan.M.loaded_segments (0x5ec04 : word) = Some W_5ebbc.
Proof. vm_refl. Qed.
Lemma D_5ebbc : decode_any W_5ebbc = Some (Jal 1 144596, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebc0 : bv 32 := 0x4482b0ef.
Lemma F_5ebc0 : fetch_word AsanUbsan.M.loaded_segments (0x5ec08 : word) = Some W_5ebc0.
Proof. vm_refl. Qed.
Lemma D_5ebc0 : decode_any W_5ebc0 = Some (Jal 1 177224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebc4 : bv 32 := 0x04853583.
Lemma F_5ebc4 : fetch_word AsanUbsan.M.loaded_segments (0x5ec0c : word) = Some W_5ebc4.
Proof. vm_refl. Qed.
Lemma D_5ebc4 : decode_any W_5ebc4 = Some (Load SZ8 true 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebc8 : bv 32 := 0x05053603.
Lemma F_5ebc8 : fetch_word AsanUbsan.M.loaded_segments (0x5ec10 : word) = Some W_5ebc8.
Proof. vm_refl. Qed.
Lemma D_5ebc8 : decode_any W_5ebc8 = Some (Load SZ8 true 12 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebcc : bv 32 := 0x00158593.
Lemma F_5ebcc : fetch_word AsanUbsan.M.loaded_segments (0x5ec14 : word) = Some W_5ebcc.
Proof. vm_refl. Qed.
Lemma D_5ebcc : decode_any W_5ebcc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebd0 : bv 32 := 0x01360633.
Lemma F_5ebd0 : fetch_word AsanUbsan.M.loaded_segments (0x5ec18 : word) = Some W_5ebd0.
Proof. vm_refl. Qed.
Lemma D_5ebd0 : decode_any W_5ebd0 = Some (Op ALU_ADD 12 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebd4 : bv 32 := 0x04b53423.
Lemma F_5ebd4 : fetch_word AsanUbsan.M.loaded_segments (0x5ec1c : word) = Some W_5ebd4.
Proof. vm_refl. Qed.
Lemma D_5ebd4 : decode_any W_5ebd4 = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebd8 : bv 32 := 0x04c53823.
Lemma F_5ebd8 : fetch_word AsanUbsan.M.loaded_segments (0x5ec20 : word) = Some W_5ebd8.
Proof. vm_refl. Qed.
Lemma D_5ebd8 : decode_any W_5ebd8 = Some (Store SZ8 10 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebdc : bv 32 := 0x000b0513.
Lemma F_5ebdc : fetch_word AsanUbsan.M.loaded_segments (0x5ec24 : word) = Some W_5ebdc.
Proof. vm_refl. Qed.
Lemma D_5ebdc : decode_any W_5ebdc = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebe0 : bv 32 := 0x01848493.
Lemma F_5ebe0 : fetch_word AsanUbsan.M.loaded_segments (0x5ec28 : word) = Some W_5ebe0.
Proof. vm_refl. Qed.
Lemma D_5ebe0 : decode_any W_5ebe0 = Some (OpImm ALU_ADD 9 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebe4 : bv 32 := 0x0134b02f.
Lemma F_5ebe4 : fetch_word AsanUbsan.M.loaded_segments (0x5ec2c : word) = Some W_5ebe4.
Proof. vm_refl. Qed.
Lemma D_5ebe4 : decode_any W_5ebe4 = Some (Amo AMO_ADD AD false false 0 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebe8 : bv 32 := 0x03043a03.
Lemma F_5ebe8 : fetch_word AsanUbsan.M.loaded_segments (0x5ec30 : word) = Some W_5ebe8.
Proof. vm_refl. Qed.
Lemma D_5ebe8 : decode_any W_5ebe8 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebec : bv 32 := 0x02043683.
Lemma F_5ebec : fetch_word AsanUbsan.M.loaded_segments (0x5ec34 : word) = Some W_5ebec.
Proof. vm_refl. Qed.
Lemma D_5ebec : decode_any W_5ebec = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf0 : bv 32 := 0x013a0a33.
Lemma F_5ebf0 : fetch_word AsanUbsan.M.loaded_segments (0x5ec38 : word) = Some W_5ebf0.
Proof. vm_refl. Qed.
Lemma D_5ebf0 : decode_any W_5ebf0 = Some (Op ALU_ADD 20 20 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf4 : bv 32 := 0x03443823.
Lemma F_5ebf4 : fetch_word AsanUbsan.M.loaded_segments (0x5ec3c : word) = Some W_5ebf4.
Proof. vm_refl. Qed.
Lemma D_5ebf4 : decode_any W_5ebf4 = Some (Store SZ8 8 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf8 : bv 32 := 0x01043483.
Lemma F_5ebf8 : fetch_word AsanUbsan.M.loaded_segments (0x5ec40 : word) = Some W_5ebf8.
Proof. vm_refl. Qed.
Lemma D_5ebf8 : decode_any W_5ebf8 = Some (Load SZ8 true 9 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebfc : bv 32 := 0x40da0a33.
Lemma F_5ebfc : fetch_word AsanUbsan.M.loaded_segments (0x5ec44 : word) = Some W_5ebfc.
Proof. vm_refl. Qed.
Lemma D_5ebfc : decode_any W_5ebfc = Some (Op ALU_SUB 20 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec00 : bv 32 := 0x035a59b3.
Lemma F_5ec00 : fetch_word AsanUbsan.M.loaded_segments (0x5ec48 : word) = Some W_5ec00.
Proof. vm_refl. Qed.
Lemma D_5ec00 : decode_any W_5ec00 = Some (Mul M_DIVU 19 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec04 : bv 32 := 0x013484b3.
Lemma F_5ec04 : fetch_word AsanUbsan.M.loaded_segments (0x5ec4c : word) = Some W_5ec04.
Proof. vm_refl. Qed.
Lemma D_5ec04 : decode_any W_5ec04 = Some (Op ALU_ADD 9 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec08 : bv 32 := 0x00040593.
Lemma F_5ec08 : fetch_word AsanUbsan.M.loaded_segments (0x5ec50 : word) = Some W_5ec08.
Proof. vm_refl. Qed.
Lemma D_5ec08 : decode_any W_5ec08 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec0c : bv 32 := 0x00090613.
Lemma F_5ec0c : fetch_word AsanUbsan.M.loaded_segments (0x5ec54 : word) = Some W_5ec0c.
Proof. vm_refl. Qed.
Lemma D_5ec0c : decode_any W_5ec0c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec10 : bv 32 := 0x00048693.
Lemma F_5ec10 : fetch_word AsanUbsan.M.loaded_segments (0x5ec58 : word) = Some W_5ec10.
Proof. vm_refl. Qed.
Lemma D_5ec10 : decode_any W_5ec10 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec14 : bv 32 := 0xb35fd0ef.
Lemma F_5ec14 : fetch_word AsanUbsan.M.loaded_segments (0x5ec5c : word) = Some W_5ec14.
Proof. vm_refl. Qed.
Lemma D_5ec14 : decode_any W_5ec14 = Some (Jal 1 2087732, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec18 : bv 32 := 0x0e050e63.
Lemma F_5ec18 : fetch_word AsanUbsan.M.loaded_segments (0x5ec60 : word) = Some W_5ec18.
Proof. vm_refl. Qed.
Lemma D_5ec18 : decode_any W_5ec18 = Some (Branch BC_EQ 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec1c : bv 32 := 0x02043683.
Lemma F_5ec1c : fetch_word AsanUbsan.M.loaded_segments (0x5ec64 : word) = Some W_5ec1c.
Proof. vm_refl. Qed.
Lemma D_5ec1c : decode_any W_5ec1c = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec20 : bv 32 := 0x055a6063.
Lemma F_5ec20 : fetch_word AsanUbsan.M.loaded_segments (0x5ec68 : word) = Some W_5ec20.
Proof. vm_refl. Qed.
Lemma D_5ec20 : decode_any W_5ec20 = Some (Branch BC_LTU 20 21 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec24 : bv 32 := 0x00000513.
Lemma F_5ec24 : fetch_word AsanUbsan.M.loaded_segments (0x5ec6c : word) = Some W_5ec24.
Proof. vm_refl. Qed.
Lemma D_5ec24 : decode_any W_5ec24 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec28 : bv 32 := 0x00700593.
Lemma F_5ec28 : fetch_word AsanUbsan.M.loaded_segments (0x5ec70 : word) = Some W_5ec28.
Proof. vm_refl. Qed.
Lemma D_5ec28 : decode_any W_5ec28 = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec2c : bv 32 := 0x01d59593.
Lemma F_5ec2c : fetch_word AsanUbsan.M.loaded_segments (0x5ec74 : word) = Some W_5ec2c.
Proof. vm_refl. Qed.
Lemma D_5ec2c : decode_any W_5ec2c = Some (ShiftImm ALU_SLL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec30 : bv 32 := 0x00b905b3.
Lemma F_5ec30 : fetch_word AsanUbsan.M.loaded_segments (0x5ec78 : word) = Some W_5ec30.
Proof. vm_refl. Qed.
Lemma D_5ec30 : decode_any W_5ec30 = Some (Op ALU_ADD 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec34 : bv 32 := 0x00249493.
Lemma F_5ec34 : fetch_word AsanUbsan.M.loaded_segments (0x5ec7c : word) = Some W_5ec34.
Proof. vm_refl. Qed.
Lemma D_5ec34 : decode_any W_5ec34 = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec38 : bv 32 := 0x009585b3.
Lemma F_5ec38 : fetch_word AsanUbsan.M.loaded_segments (0x5ec80 : word) = Some W_5ec38.
Proof. vm_refl. Qed.
Lemma D_5ec38 : decode_any W_5ec38 = Some (Op ALU_ADD 11 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec3c : bv 32 := 0x00068613.
Lemma F_5ec3c : fetch_word AsanUbsan.M.loaded_segments (0x5ec84 : word) = Some W_5ec3c.
Proof. vm_refl. Qed.
Lemma D_5ec3c : decode_any W_5ec3c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec40 : bv 32 := 0x00465713.
Lemma F_5ec40 : fetch_word AsanUbsan.M.loaded_segments (0x5ec88 : word) = Some W_5ec40.
Proof. vm_refl. Qed.
Lemma D_5ec40 : decode_any W_5ec40 = Some (ShiftImm ALU_SRL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec44 : bv 32 := 0xfff54793.
Lemma F_5ec44 : fetch_word AsanUbsan.M.loaded_segments (0x5ec8c : word) = Some W_5ec44.
Proof. vm_refl. Qed.
Lemma D_5ec44 : decode_any W_5ec44 = Some (OpImm ALU_XOR 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec48 : bv 32 := 0x00150513.
Lemma F_5ec48 : fetch_word AsanUbsan.M.loaded_segments (0x5ec90 : word) = Some W_5ec48.
Proof. vm_refl. Qed.
Lemma D_5ec48 : decode_any W_5ec48 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec4c : bv 32 := 0x00279793.
Lemma F_5ec4c : fetch_word AsanUbsan.M.loaded_segments (0x5ec94 : word) = Some W_5ec4c.
Proof. vm_refl. Qed.
Lemma D_5ec4c : decode_any W_5ec4c = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec50 : bv 32 := 0x00f587b3.
Lemma F_5ec50 : fetch_word AsanUbsan.M.loaded_segments (0x5ec98 : word) = Some W_5ec50.
Proof. vm_refl. Qed.
Lemma D_5ec50 : decode_any W_5ec50 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec54 : bv 32 := 0x00e7a023.
Lemma F_5ec54 : fetch_word AsanUbsan.M.loaded_segments (0x5ec9c : word) = Some W_5ec54.
Proof. vm_refl. Qed.
Lemma D_5ec54 : decode_any W_5ec54 = Some (Store SZ4 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec58 : bv 32 := 0x01560633.
Lemma F_5ec58 : fetch_word AsanUbsan.M.loaded_segments (0x5eca0 : word) = Some W_5ec58.
Proof. vm_refl. Qed.
Lemma D_5ec58 : decode_any W_5ec58 = Some (Op ALU_ADD 12 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec5c : bv 32 := 0xff3562e3.
Lemma F_5ec5c : fetch_word AsanUbsan.M.loaded_segments (0x5eca4 : word) = Some W_5ec5c.
Proof. vm_refl. Qed.
Lemma D_5ec5c : decode_any W_5ec5c = Some (Branch BC_LTU 10 19 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec60 : bv 32 := 0x01043503.
Lemma F_5ec60 : fetch_word AsanUbsan.M.loaded_segments (0x5eca8 : word) = Some W_5ec60.
Proof. vm_refl. Qed.
Lemma D_5ec60 : decode_any W_5ec60 = Some (Load SZ8 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec64 : bv 32 := 0x035985b3.
Lemma F_5ec64 : fetch_word AsanUbsan.M.loaded_segments (0x5ecac : word) = Some W_5ec64.
Proof. vm_refl. Qed.
Lemma D_5ec64 : decode_any W_5ec64 = Some (Mul M_MUL 11 19 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec68 : bv 32 := 0x03043703.
Lemma F_5ec68 : fetch_word AsanUbsan.M.loaded_segments (0x5ecb0 : word) = Some W_5ec68.
Proof. vm_refl. Qed.
Lemma D_5ec68 : decode_any W_5ec68 = Some (Load SZ8 true 14 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec6c : bv 32 := 0x00b686b3.
Lemma F_5ec6c : fetch_word AsanUbsan.M.loaded_segments (0x5ecb4 : word) = Some W_5ec6c.
Proof. vm_refl. Qed.
Lemma D_5ec6c : decode_any W_5ec6c = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec70 : bv 32 := 0x01350533.
Lemma F_5ec70 : fetch_word AsanUbsan.M.loaded_segments (0x5ecb8 : word) = Some W_5ec70.
Proof. vm_refl. Qed.
Lemma D_5ec70 : decode_any W_5ec70 = Some (Op ALU_ADD 10 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec74 : bv 32 := 0x00a43823.
Lemma F_5ec74 : fetch_word AsanUbsan.M.loaded_segments (0x5ecbc : word) = Some W_5ec74.
Proof. vm_refl. Qed.
Lemma D_5ec74 : decode_any W_5ec74 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec78 : bv 32 := 0x02d43023.
Lemma F_5ec78 : fetch_word AsanUbsan.M.loaded_segments (0x5ecc0 : word) = Some W_5ec78.
Proof. vm_refl. Qed.
Lemma D_5ec78 : decode_any W_5ec78 = Some (Store SZ8 8 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec7c : bv 32 := 0x0ad76063.
Lemma F_5ec7c : fetch_word AsanUbsan.M.loaded_segments (0x5ecc4 : word) = Some W_5ec7c.
Proof. vm_refl. Qed.
Lemma D_5ec7c : decode_any W_5ec7c = Some (Branch BC_LTU 14 13 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec80 : bv 32 := 0x02843683.
Lemma F_5ec80 : fetch_word AsanUbsan.M.loaded_segments (0x5ecc8 : word) = Some W_5ec80.
Proof. vm_refl. Qed.
Lemma D_5ec80 : decode_any W_5ec80 = Some (Load SZ8 true 13 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec84 : bv 32 := 0x03843703.
Lemma F_5ec84 : fetch_word AsanUbsan.M.loaded_segments (0x5eccc : word) = Some W_5ec84.
Proof. vm_refl. Qed.
Lemma D_5ec84 : decode_any W_5ec84 = Some (Load SZ8 true 14 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec88 : bv 32 := 0x0ad76663.
Lemma F_5ec88 : fetch_word AsanUbsan.M.loaded_segments (0x5ecd0 : word) = Some W_5ec88.
Proof. vm_refl. Qed.
Lemma D_5ec88 : decode_any W_5ec88 = Some (Branch BC_LTU 14 13 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec8c : bv 32 := 0x04040223.
Lemma F_5ec8c : fetch_word AsanUbsan.M.loaded_segments (0x5ecd4 : word) = Some W_5ec8c.
Proof. vm_refl. Qed.
Lemma D_5ec8c : decode_any W_5ec8c = Some (Store SZ1 8 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec90 : bv 32 := 0x00100593.
Lemma F_5ec90 : fetch_word AsanUbsan.M.loaded_segments (0x5ecd8 : word) = Some W_5ec90.
Proof. vm_refl. Qed.
Lemma D_5ec90 : decode_any W_5ec90 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec94 : bv 32 := 0x00058513.
Lemma F_5ec94 : fetch_word AsanUbsan.M.loaded_segments (0x5ecdc : word) = Some W_5ec94.
Proof. vm_refl. Qed.
Lemma D_5ec94 : decode_any W_5ec94 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec98 : bv 32 := 0x03813083.
Lemma F_5ec98 : fetch_word AsanUbsan.M.loaded_segments (0x5ece0 : word) = Some W_5ec98.
Proof. vm_refl. Qed.
Lemma D_5ec98 : decode_any W_5ec98 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec9c : bv 32 := 0x03013403.
Lemma F_5ec9c : fetch_word AsanUbsan.M.loaded_segments (0x5ece4 : word) = Some W_5ec9c.
Proof. vm_refl. Qed.
Lemma D_5ec9c : decode_any W_5ec9c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca0 : bv 32 := 0x02813483.
Lemma F_5eca0 : fetch_word AsanUbsan.M.loaded_segments (0x5ece8 : word) = Some W_5eca0.
Proof. vm_refl. Qed.
Lemma D_5eca0 : decode_any W_5eca0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca4 : bv 32 := 0x02013903.
Lemma F_5eca4 : fetch_word AsanUbsan.M.loaded_segments (0x5ecec : word) = Some W_5eca4.
Proof. vm_refl. Qed.
Lemma D_5eca4 : decode_any W_5eca4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca8 : bv 32 := 0x01813983.
Lemma F_5eca8 : fetch_word AsanUbsan.M.loaded_segments (0x5ecf0 : word) = Some W_5eca8.
Proof. vm_refl. Qed.
Lemma D_5eca8 : decode_any W_5eca8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecac : bv 32 := 0x01013a03.
Lemma F_5ecac : fetch_word AsanUbsan.M.loaded_segments (0x5ecf4 : word) = Some W_5ecac.
Proof. vm_refl. Qed.
Lemma D_5ecac : decode_any W_5ecac = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb0 : bv 32 := 0x00813a83.
Lemma F_5ecb0 : fetch_word AsanUbsan.M.loaded_segments (0x5ecf8 : word) = Some W_5ecb0.
Proof. vm_refl. Qed.
Lemma D_5ecb0 : decode_any W_5ecb0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb4 : bv 32 := 0x00013b03.
Lemma F_5ecb4 : fetch_word AsanUbsan.M.loaded_segments (0x5ecfc : word) = Some W_5ecb4.
Proof. vm_refl. Qed.
Lemma D_5ecb4 : decode_any W_5ecb4 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb8 : bv 32 := 0x04010113.
Lemma F_5ecb8 : fetch_word AsanUbsan.M.loaded_segments (0x5ed00 : word) = Some W_5ecb8.
Proof. vm_refl. Qed.
Lemma D_5ecb8 : decode_any W_5ecb8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecbc : bv 32 := 0x00008067.
Lemma F_5ecbc : fetch_word AsanUbsan.M.loaded_segments (0x5ed04 : word) = Some W_5ecbc.
Proof. vm_refl. Qed.
Lemma D_5ecbc : decode_any W_5ecbc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece0 : bv 32 := 0x02852583.
Lemma F_5ece0 : fetch_word AsanUbsan.M.loaded_segments (0x5ed28 : word) = Some W_5ece0.
Proof. vm_refl. Qed.
Lemma D_5ece0 : decode_any W_5ece0 = Some (Load SZ4 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece4 : bv 32 := 0x0c05c263.
Lemma F_5ece4 : fetch_word AsanUbsan.M.loaded_segments (0x5ed2c : word) = Some W_5ece4.
Proof. vm_refl. Qed.
Lemma D_5ece4 : decode_any W_5ece4 = Some (Branch BC_LT 11 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eda8 : bv 32 := 0x00000a13.
Lemma F_5eda8 : fetch_word AsanUbsan.M.loaded_segments (0x5edf0 : word) = Some W_5eda8.
Proof. vm_refl. Qed.
Lemma D_5eda8 : decode_any W_5eda8 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edac : bv 32 := 0xd7dff06f.
Lemma F_5edac : fetch_word AsanUbsan.M.loaded_segments (0x5edf4 : word) = Some W_5edac.
Proof. vm_refl. Qed.
Lemma D_5edac : decode_any W_5edac = Some (Jal 0 2096508, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edf4 : bv 32 := 0xff010113.
Lemma F_5edf4 : fetch_word AsanUbsan.M.loaded_segments (0x5ee3c : word) = Some W_5edf4.
Proof. vm_refl. Qed.
Lemma D_5edf4 : decode_any W_5edf4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edf8 : bv 32 := 0x00113423.
Lemma F_5edf8 : fetch_word AsanUbsan.M.loaded_segments (0x5ee40 : word) = Some W_5edf8.
Proof. vm_refl. Qed.
Lemma D_5edf8 : decode_any W_5edf8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edfc : bv 32 := 0x02051693.
Lemma F_5edfc : fetch_word AsanUbsan.M.loaded_segments (0x5ee44 : word) = Some W_5edfc.
Proof. vm_refl. Qed.
Lemma D_5edfc : decode_any W_5edfc = Some (ShiftImm ALU_SLL 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee00 : bv 32 := 0x00f00593.
Lemma F_5ee00 : fetch_word AsanUbsan.M.loaded_segments (0x5ee48 : word) = Some W_5ee00.
Proof. vm_refl. Qed.
Lemma D_5ee00 : decode_any W_5ee00 = Some (OpImm ALU_ADD 11 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee04 : bv 32 := 0x0206d693.
Lemma F_5ee04 : fetch_word AsanUbsan.M.loaded_segments (0x5ee4c : word) = Some W_5ee04.
Proof. vm_refl. Qed.
Lemma D_5ee04 : decode_any W_5ee04 = Some (ShiftImm ALU_SRL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee08 : bv 32 := 0x06a5f663.
Lemma F_5ee08 : fetch_word AsanUbsan.M.loaded_segments (0x5ee50 : word) = Some W_5ee08.
Proof. vm_refl. Qed.
Lemma D_5ee08 : decode_any W_5ee08 = Some (Branch BC_GEU 11 10 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee0c : bv 32 := 0x000015b7.
Lemma F_5ee0c : fetch_word AsanUbsan.M.loaded_segments (0x5ee54 : word) = Some W_5ee0c.
Proof. vm_refl. Qed.
Lemma D_5ee0c : decode_any W_5ee0c = Some (Lui 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee10 : bv 32 := 0x8015859b.
Lemma F_5ee10 : fetch_word AsanUbsan.M.loaded_segments (0x5ee58 : word) = Some W_5ee10.
Proof. vm_refl. Qed.
Lemma D_5ee10 : decode_any W_5ee10 = Some (OpImm32 11 11 2049, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee14 : bv 32 := 0x06b57e63.
Lemma F_5ee14 : fetch_word AsanUbsan.M.loaded_segments (0x5ee5c : word) = Some W_5ee14.
Proof. vm_refl. Qed.
Lemma D_5ee14 : decode_any W_5ee14 = Some (Branch BC_GEU 10 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee18 : bv 32 := 0xfff68593.
Lemma F_5ee18 : fetch_word AsanUbsan.M.loaded_segments (0x5ee60 : word) = Some W_5ee18.
Proof. vm_refl. Qed.
Lemma D_5ee18 : decode_any W_5ee18 = Some (OpImm ALU_ADD 11 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee1c : bv 32 := 0x00b6f5b3.
Lemma F_5ee1c : fetch_word AsanUbsan.M.loaded_segments (0x5ee64 : word) = Some W_5ee1c.
Proof. vm_refl. Qed.
Lemma D_5ee1c : decode_any W_5ee1c = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee20 : bv 32 := 0x08059863.
Lemma F_5ee20 : fetch_word AsanUbsan.M.loaded_segments (0x5ee68 : word) = Some W_5ee20.
Proof. vm_refl. Qed.
Lemma D_5ee20 : decode_any W_5ee20 = Some (Branch BC_NE 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee24 : bv 32 := 0x40d005b3.
Lemma F_5ee24 : fetch_word AsanUbsan.M.loaded_segments (0x5ee6c : word) = Some W_5ee24.
Proof. vm_refl. Qed.
Lemma D_5ee24 : decode_any W_5ee24 = Some (Op ALU_SUB 11 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee28 : bv 32 := 0xfffb1617.
Lemma F_5ee28 : fetch_word AsanUbsan.M.loaded_segments (0x5ee70 : word) = Some W_5ee28.
Proof. vm_refl. Qed.
Lemma D_5ee28 : decode_any W_5ee28 = Some (Auipc 12 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee2c : bv 32 := 0x60863603.
Lemma F_5ee2c : fetch_word AsanUbsan.M.loaded_segments (0x5ee74 : word) = Some W_5ee2c.
Proof. vm_refl. Qed.
Lemma D_5ee2c : decode_any W_5ee2c = Some (Load SZ8 true 12 12 1544, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee30 : bv 32 := 0xfffb1717.
Lemma F_5ee30 : fetch_word AsanUbsan.M.loaded_segments (0x5ee78 : word) = Some W_5ee30.
Proof. vm_refl. Qed.
Lemma D_5ee30 : decode_any W_5ee30 = Some (Auipc 14 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee34 : bv 32 := 0x00b6f5b3.
Lemma F_5ee34 : fetch_word AsanUbsan.M.loaded_segments (0x5ee7c : word) = Some W_5ee34.
Proof. vm_refl. Qed.
Lemma D_5ee34 : decode_any W_5ee34 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee38 : bv 32 := 0x77870713.
Lemma F_5ee38 : fetch_word AsanUbsan.M.loaded_segments (0x5ee80 : word) = Some W_5ee38.
Proof. vm_refl. Qed.
Lemma D_5ee38 : decode_any W_5ee38 = Some (OpImm ALU_ADD 14 14 1912, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee3c : bv 32 := 0x02c585b3.
Lemma F_5ee3c : fetch_word AsanUbsan.M.loaded_segments (0x5ee84 : word) = Some W_5ee3c.
Proof. vm_refl. Qed.
Lemma D_5ee3c : decode_any W_5ee3c = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee40 : bv 32 := 0x03a5d593.
Lemma F_5ee40 : fetch_word AsanUbsan.M.loaded_segments (0x5ee88 : word) = Some W_5ee40.
Proof. vm_refl. Qed.
Lemma D_5ee40 : decode_any W_5ee40 = Some (ShiftImm ALU_SRL 11 11 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee44 : bv 32 := 0x00b705b3.
Lemma F_5ee44 : fetch_word AsanUbsan.M.loaded_segments (0x5ee8c : word) = Some W_5ee44.
Proof. vm_refl. Qed.
Lemma D_5ee44 : decode_any W_5ee44 = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee48 : bv 32 := 0x0005c603.
Lemma F_5ee48 : fetch_word AsanUbsan.M.loaded_segments (0x5ee90 : word) = Some W_5ee48.
Proof. vm_refl. Qed.
Lemma D_5ee48 : decode_any W_5ee48 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee4c : bv 32 := 0xffc60593.
Lemma F_5ee4c : fetch_word AsanUbsan.M.loaded_segments (0x5ee94 : word) = Some W_5ee4c.
Proof. vm_refl. Qed.
Lemma D_5ee4c : decode_any W_5ee4c = Some (OpImm ALU_ADD 11 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee50 : bv 32 := 0x00800713.
Lemma F_5ee50 : fetch_word AsanUbsan.M.loaded_segments (0x5ee98 : word) = Some W_5ee50.
Proof. vm_refl. Qed.
Lemma D_5ee50 : decode_any W_5ee50 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee54 : bv 32 := 0x06e5fe63.
Lemma F_5ee54 : fetch_word AsanUbsan.M.loaded_segments (0x5ee9c : word) = Some W_5ee54.
Proof. vm_refl. Qed.
Lemma D_5ee54 : decode_any W_5ee54 = Some (Branch BC_GEU 11 14 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee58 : bv 32 := 0x00100713.
Lemma F_5ee58 : fetch_word AsanUbsan.M.loaded_segments (0x5eea0 : word) = Some W_5ee58.
Proof. vm_refl. Qed.
Lemma D_5ee58 : decode_any W_5ee58 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee5c : bv 32 := 0x00c7173b.
Lemma F_5ee5c : fetch_word AsanUbsan.M.loaded_segments (0x5eea4 : word) = Some W_5ee5c.
Proof. vm_refl. Qed.
Lemma D_5ee5c : decode_any W_5ee5c = Some (Op32 ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee60 : bv 32 := 0x08e51a63.
Lemma F_5ee60 : fetch_word AsanUbsan.M.loaded_segments (0x5eea8 : word) = Some W_5ee60.
Proof. vm_refl. Qed.
Lemma D_5ee60 : decode_any W_5ee60 = Some (Branch BC_NE 10 14 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee64 : bv 32 := 0x00058513.
Lemma F_5ee64 : fetch_word AsanUbsan.M.loaded_segments (0x5eeac : word) = Some W_5ee64.
Proof. vm_refl. Qed.
Lemma D_5ee64 : decode_any W_5ee64 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee68 : bv 32 := 0x00813083.
Lemma F_5ee68 : fetch_word AsanUbsan.M.loaded_segments (0x5eeb0 : word) = Some W_5ee68.
Proof. vm_refl. Qed.
Lemma D_5ee68 : decode_any W_5ee68 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee6c : bv 32 := 0x01010113.
Lemma F_5ee6c : fetch_word AsanUbsan.M.loaded_segments (0x5eeb4 : word) = Some W_5ee6c.
Proof. vm_refl. Qed.
Lemma D_5ee6c : decode_any W_5ee6c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee70 : bv 32 := 0x00008067.
Lemma F_5ee70 : fetch_word AsanUbsan.M.loaded_segments (0x5eeb8 : word) = Some W_5ee70.
Proof. vm_refl. Qed.
Lemma D_5ee70 : decode_any W_5ee70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

