(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5f000 : bv 32 := 0x5557879b.
Lemma F_5f000 : fetch_word Asan.M.loaded_segments (0x5f050 : word) = Some W_5f000.
Proof. vm_refl. Qed.
Lemma D_5f000 : decode_any W_5f000 = Some (OpImm32 15 15 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f004 : bv 32 := 0x3338081b.
Lemma F_5f004 : fetch_word Asan.M.loaded_segments (0x5f054 : word) = Some W_5f004.
Proof. vm_refl. Qed.
Lemma D_5f004 : decode_any W_5f004 = Some (OpImm32 16 16 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f008 : bv 32 := 0xf0f8889b.
Lemma F_5f008 : fetch_word Asan.M.loaded_segments (0x5f058 : word) = Some W_5f008.
Proof. vm_refl. Qed.
Lemma D_5f008 : decode_any W_5f008 = Some (OpImm32 17 17 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f00c : bv 32 := 0x1012829b.
Lemma F_5f00c : fetch_word Asan.M.loaded_segments (0x5f05c : word) = Some W_5f00c.
Proof. vm_refl. Qed.
Lemma D_5f00c : decode_any W_5f00c = Some (OpImm32 5 5 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f010 : bv 32 := 0x00265313.
Lemma F_5f010 : fetch_word Asan.M.loaded_segments (0x5f060 : word) = Some W_5f010.
Proof. vm_refl. Qed.
Lemma D_5f010 : decode_any W_5f010 = Some (ShiftImm ALU_SRL 6 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f014 : bv 32 := 0x00666633.
Lemma F_5f014 : fetch_word Asan.M.loaded_segments (0x5f064 : word) = Some W_5f014.
Proof. vm_refl. Qed.
Lemma D_5f014 : decode_any W_5f014 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f018 : bv 32 := 0x02079313.
Lemma F_5f018 : fetch_word Asan.M.loaded_segments (0x5f068 : word) = Some W_5f018.
Proof. vm_refl. Qed.
Lemma D_5f018 : decode_any W_5f018 = Some (ShiftImm ALU_SLL 6 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f01c : bv 32 := 0x006787b3.
Lemma F_5f01c : fetch_word Asan.M.loaded_segments (0x5f06c : word) = Some W_5f01c.
Proof. vm_refl. Qed.
Lemma D_5f01c : decode_any W_5f01c = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f020 : bv 32 := 0x02081313.
Lemma F_5f020 : fetch_word Asan.M.loaded_segments (0x5f070 : word) = Some W_5f020.
Proof. vm_refl. Qed.
Lemma D_5f020 : decode_any W_5f020 = Some (ShiftImm ALU_SLL 6 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f024 : bv 32 := 0x00680833.
Lemma F_5f024 : fetch_word Asan.M.loaded_segments (0x5f074 : word) = Some W_5f024.
Proof. vm_refl. Qed.
Lemma D_5f024 : decode_any W_5f024 = Some (Op ALU_ADD 16 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f028 : bv 32 := 0x02089313.
Lemma F_5f028 : fetch_word Asan.M.loaded_segments (0x5f078 : word) = Some W_5f028.
Proof. vm_refl. Qed.
Lemma D_5f028 : decode_any W_5f028 = Some (ShiftImm ALU_SLL 6 17 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f02c : bv 32 := 0x006888b3.
Lemma F_5f02c : fetch_word Asan.M.loaded_segments (0x5f07c : word) = Some W_5f02c.
Proof. vm_refl. Qed.
Lemma D_5f02c : decode_any W_5f02c = Some (Op ALU_ADD 17 17 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f030 : bv 32 := 0x02029313.
Lemma F_5f030 : fetch_word Asan.M.loaded_segments (0x5f080 : word) = Some W_5f030.
Proof. vm_refl. Qed.
Lemma D_5f030 : decode_any W_5f030 = Some (ShiftImm ALU_SLL 6 5 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f034 : bv 32 := 0x006282b3.
Lemma F_5f034 : fetch_word Asan.M.loaded_segments (0x5f084 : word) = Some W_5f034.
Proof. vm_refl. Qed.
Lemma D_5f034 : decode_any W_5f034 = Some (Op ALU_ADD 5 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f038 : bv 32 := 0x00465313.
Lemma F_5f038 : fetch_word Asan.M.loaded_segments (0x5f088 : word) = Some W_5f038.
Proof. vm_refl. Qed.
Lemma D_5f038 : decode_any W_5f038 = Some (ShiftImm ALU_SRL 6 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f03c : bv 32 := 0x00666633.
Lemma F_5f03c : fetch_word Asan.M.loaded_segments (0x5f08c : word) = Some W_5f03c.
Proof. vm_refl. Qed.
Lemma D_5f03c : decode_any W_5f03c = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f040 : bv 32 := 0x00865313.
Lemma F_5f040 : fetch_word Asan.M.loaded_segments (0x5f090 : word) = Some W_5f040.
Proof. vm_refl. Qed.
Lemma D_5f040 : decode_any W_5f040 = Some (ShiftImm ALU_SRL 6 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f044 : bv 32 := 0x00666633.
Lemma F_5f044 : fetch_word Asan.M.loaded_segments (0x5f094 : word) = Some W_5f044.
Proof. vm_refl. Qed.
Lemma D_5f044 : decode_any W_5f044 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f048 : bv 32 := 0x01065313.
Lemma F_5f048 : fetch_word Asan.M.loaded_segments (0x5f098 : word) = Some W_5f048.
Proof. vm_refl. Qed.
Lemma D_5f048 : decode_any W_5f048 = Some (ShiftImm ALU_SRL 6 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f04c : bv 32 := 0x00666633.
Lemma F_5f04c : fetch_word Asan.M.loaded_segments (0x5f09c : word) = Some W_5f04c.
Proof. vm_refl. Qed.
Lemma D_5f04c : decode_any W_5f04c = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f050 : bv 32 := 0x02065313.
Lemma F_5f050 : fetch_word Asan.M.loaded_segments (0x5f0a0 : word) = Some W_5f050.
Proof. vm_refl. Qed.
Lemma D_5f050 : decode_any W_5f050 = Some (ShiftImm ALU_SRL 6 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f054 : bv 32 := 0x00666633.
Lemma F_5f054 : fetch_word Asan.M.loaded_segments (0x5f0a4 : word) = Some W_5f054.
Proof. vm_refl. Qed.
Lemma D_5f054 : decode_any W_5f054 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f058 : bv 32 := 0xfff64613.
Lemma F_5f058 : fetch_word Asan.M.loaded_segments (0x5f0a8 : word) = Some W_5f058.
Proof. vm_refl. Qed.
Lemma D_5f058 : decode_any W_5f058 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f05c : bv 32 := 0x00165313.
Lemma F_5f05c : fetch_word Asan.M.loaded_segments (0x5f0ac : word) = Some W_5f05c.
Proof. vm_refl. Qed.
Lemma D_5f05c : decode_any W_5f05c = Some (ShiftImm ALU_SRL 6 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f060 : bv 32 := 0x00f377b3.
Lemma F_5f060 : fetch_word Asan.M.loaded_segments (0x5f0b0 : word) = Some W_5f060.
Proof. vm_refl. Qed.
Lemma D_5f060 : decode_any W_5f060 = Some (Op ALU_AND 15 6 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f064 : bv 32 := 0x40f60633.
Lemma F_5f064 : fetch_word Asan.M.loaded_segments (0x5f0b4 : word) = Some W_5f064.
Proof. vm_refl. Qed.
Lemma D_5f064 : decode_any W_5f064 = Some (Op ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f068 : bv 32 := 0x010677b3.
Lemma F_5f068 : fetch_word Asan.M.loaded_segments (0x5f0b8 : word) = Some W_5f068.
Proof. vm_refl. Qed.
Lemma D_5f068 : decode_any W_5f068 = Some (Op ALU_AND 15 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f06c : bv 32 := 0x00265613.
Lemma F_5f06c : fetch_word Asan.M.loaded_segments (0x5f0bc : word) = Some W_5f06c.
Proof. vm_refl. Qed.
Lemma D_5f06c : decode_any W_5f06c = Some (ShiftImm ALU_SRL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f070 : bv 32 := 0x01067633.
Lemma F_5f070 : fetch_word Asan.M.loaded_segments (0x5f0c0 : word) = Some W_5f070.
Proof. vm_refl. Qed.
Lemma D_5f070 : decode_any W_5f070 = Some (Op ALU_AND 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f074 : bv 32 := 0x00c78633.
Lemma F_5f074 : fetch_word Asan.M.loaded_segments (0x5f0c4 : word) = Some W_5f074.
Proof. vm_refl. Qed.
Lemma D_5f074 : decode_any W_5f074 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f078 : bv 32 := 0x00465793.
Lemma F_5f078 : fetch_word Asan.M.loaded_segments (0x5f0c8 : word) = Some W_5f078.
Proof. vm_refl. Qed.
Lemma D_5f078 : decode_any W_5f078 = Some (ShiftImm ALU_SRL 15 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f07c : bv 32 := 0x00f60633.
Lemma F_5f07c : fetch_word Asan.M.loaded_segments (0x5f0cc : word) = Some W_5f07c.
Proof. vm_refl. Qed.
Lemma D_5f07c : decode_any W_5f07c = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f080 : bv 32 := 0x03e00793.
Lemma F_5f080 : fetch_word Asan.M.loaded_segments (0x5f0d0 : word) = Some W_5f080.
Proof. vm_refl. Qed.
Lemma D_5f080 : decode_any W_5f080 = Some (OpImm ALU_ADD 15 0 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f084 : bv 32 := 0x01167633.
Lemma F_5f084 : fetch_word Asan.M.loaded_segments (0x5f0d4 : word) = Some W_5f084.
Proof. vm_refl. Qed.
Lemma D_5f084 : decode_any W_5f084 = Some (Op ALU_AND 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f088 : bv 32 := 0xfff00813.
Lemma F_5f088 : fetch_word Asan.M.loaded_segments (0x5f0d8 : word) = Some W_5f088.
Proof. vm_refl. Qed.
Lemma D_5f088 : decode_any W_5f088 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f08c : bv 32 := 0x02560633.
Lemma F_5f08c : fetch_word Asan.M.loaded_segments (0x5f0dc : word) = Some W_5f08c.
Proof. vm_refl. Qed.
Lemma D_5f08c : decode_any W_5f08c = Some (Mul M_MUL 12 12 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f090 : bv 32 := 0x03865613.
Lemma F_5f090 : fetch_word Asan.M.loaded_segments (0x5f0e0 : word) = Some W_5f090.
Proof. vm_refl. Qed.
Lemma D_5f090 : decode_any W_5f090 = Some (ShiftImm ALU_SRL 12 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f094 : bv 32 := 0x40c787bb.
Lemma F_5f094 : fetch_word Asan.M.loaded_segments (0x5f0e4 : word) = Some W_5f094.
Proof. vm_refl. Qed.
Lemma D_5f094 : decode_any W_5f094 = Some (Op32 ALU_SUB 15 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f098 : bv 32 := 0x00161613.
Lemma F_5f098 : fetch_word Asan.M.loaded_segments (0x5f0e8 : word) = Some W_5f098.
Proof. vm_refl. Qed.
Lemma D_5f098 : decode_any W_5f098 = Some (ShiftImm ALU_SLL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f09c : bv 32 := 0x00f758b3.
Lemma F_5f09c : fetch_word Asan.M.loaded_segments (0x5f0ec : word) = Some W_5f09c.
Proof. vm_refl. Qed.
Lemma D_5f09c : decode_any W_5f09c = Some (Op ALU_SRL 17 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0a0 : bv 32 := 0x00f817bb.
Lemma F_5f0a0 : fetch_word Asan.M.loaded_segments (0x5f0f0 : word) = Some W_5f0a0.
Proof. vm_refl. Qed.
Lemma D_5f0a0 : decode_any W_5f0a0 = Some (Op32 ALU_SLL 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0a4 : bv 32 := 0x07e64613.
Lemma F_5f0a4 : fetch_word Asan.M.loaded_segments (0x5f0f4 : word) = Some W_5f0a4.
Proof. vm_refl. Qed.
Lemma D_5f0a4 : decode_any W_5f0a4 = Some (OpImm ALU_XOR 12 12 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0a8 : bv 32 := 0x0018f813.
Lemma F_5f0a8 : fetch_word Asan.M.loaded_segments (0x5f0f8 : word) = Some W_5f0a8.
Proof. vm_refl. Qed.
Lemma D_5f0a8 : decode_any W_5f0a8 = Some (OpImm ALU_AND 16 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0ac : bv 32 := 0xfff7c793.
Lemma F_5f0ac : fetch_word Asan.M.loaded_segments (0x5f0fc : word) = Some W_5f0ac.
Proof. vm_refl. Qed.
Lemma D_5f0ac : decode_any W_5f0ac = Some (OpImm ALU_XOR 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0b0 : bv 32 := 0x00f77733.
Lemma F_5f0b0 : fetch_word Asan.M.loaded_segments (0x5f100 : word) = Some W_5f0b0.
Proof. vm_refl. Qed.
Lemma D_5f0b0 : decode_any W_5f0b0 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0b4 : bv 32 := 0x01066633.
Lemma F_5f0b4 : fetch_word Asan.M.loaded_segments (0x5f104 : word) = Some W_5f0b4.
Proof. vm_refl. Qed.
Lemma D_5f0b4 : decode_any W_5f0b4 = Some (Op ALU_OR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0b8 : bv 32 := 0x00e03733.
Lemma F_5f0b8 : fetch_word Asan.M.loaded_segments (0x5f108 : word) = Some W_5f0b8.
Proof. vm_refl. Qed.
Lemma D_5f0b8 : decode_any W_5f0b8 = Some (Op ALU_SLTU 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0bc : bv 32 := 0x00e60633.
Lemma F_5f0bc : fetch_word Asan.M.loaded_segments (0x5f10c : word) = Some W_5f0bc.
Proof. vm_refl. Qed.
Lemma D_5f0bc : decode_any W_5f0bc = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0c0 : bv 32 := 0xffe60413.
Lemma F_5f0c0 : fetch_word Asan.M.loaded_segments (0x5f110 : word) = Some W_5f0c0.
Proof. vm_refl. Qed.
Lemma D_5f0c0 : decode_any W_5f0c0 = Some (OpImm ALU_ADD 8 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0c4 : bv 32 := 0x0a040063.
Lemma F_5f0c4 : fetch_word Asan.M.loaded_segments (0x5f114 : word) = Some W_5f0c4.
Proof. vm_refl. Qed.
Lemma D_5f0c4 : decode_any W_5f0c4 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0c8 : bv 32 := 0x02000613.
Lemma F_5f0c8 : fetch_word Asan.M.loaded_segments (0x5f118 : word) = Some W_5f0c8.
Proof. vm_refl. Qed.
Lemma D_5f0c8 : decode_any W_5f0c8 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0cc : bv 32 := 0x0cc47a63.
Lemma F_5f0cc : fetch_word Asan.M.loaded_segments (0x5f11c : word) = Some W_5f0cc.
Proof. vm_refl. Qed.
Lemma D_5f0cc : decode_any W_5f0cc = Some (Branch BC_GEU 8 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0d0 : bv 32 := 0x05000613.
Lemma F_5f0d0 : fetch_word Asan.M.loaded_segments (0x5f120 : word) = Some W_5f0d0.
Proof. vm_refl. Qed.
Lemma D_5f0d0 : decode_any W_5f0d0 = Some (OpImm ALU_ADD 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0d4 : bv 32 := 0x02c404b3.
Lemma F_5f0d4 : fetch_word Asan.M.loaded_segments (0x5f124 : word) = Some W_5f0d4.
Proof. vm_refl. Qed.
Lemma D_5f0d4 : decode_any W_5f0d4 = Some (Mul M_MUL 9 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0d8 : bv 32 := 0x009584b3.
Lemma F_5f0d8 : fetch_word Asan.M.loaded_segments (0x5f128 : word) = Some W_5f0d8.
Proof. vm_refl. Qed.
Lemma D_5f0d8 : decode_any W_5f0d8 = Some (Op ALU_ADD 9 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0dc : bv 32 := 0x0004a603.
Lemma F_5f0dc : fetch_word Asan.M.loaded_segments (0x5f12c : word) = Some W_5f0dc.
Proof. vm_refl. Qed.
Lemma D_5f0dc : decode_any W_5f0dc = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0e0 : bv 32 := 0x0e060063.
Lemma F_5f0e0 : fetch_word Asan.M.loaded_segments (0x5f130 : word) = Some W_5f0e0.
Proof. vm_refl. Qed.
Lemma D_5f0e0 : decode_any W_5f0e0 = Some (Branch BC_EQ 12 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0e4 : bv 32 := 0xfff60613.
Lemma F_5f0e4 : fetch_word Asan.M.loaded_segments (0x5f134 : word) = Some W_5f0e4.
Proof. vm_refl. Qed.
Lemma D_5f0e4 : decode_any W_5f0e4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0e8 : bv 32 := 0x7ff58593.
Lemma F_5f0e8 : fetch_word Asan.M.loaded_segments (0x5f138 : word) = Some W_5f0e8.
Proof. vm_refl. Qed.
Lemma D_5f0e8 : decode_any W_5f0e8 = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0ec : bv 32 := 0x02061713.
Lemma F_5f0ec : fetch_word Asan.M.loaded_segments (0x5f13c : word) = Some W_5f0ec.
Proof. vm_refl. Qed.
Lemma D_5f0ec : decode_any W_5f0ec = Some (ShiftImm ALU_SLL 14 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0f0 : bv 32 := 0x00c4a023.
Lemma F_5f0f0 : fetch_word Asan.M.loaded_segments (0x5f140 : word) = Some W_5f0f0.
Proof. vm_refl. Qed.
Lemma D_5f0f0 : decode_any W_5f0f0 = Some (Store SZ4 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0f4 : bv 32 := 0x21158593.
Lemma F_5f0f4 : fetch_word Asan.M.loaded_segments (0x5f144 : word) = Some W_5f0f4.
Proof. vm_refl. Qed.
Lemma D_5f0f4 : decode_any W_5f0f4 = Some (OpImm ALU_ADD 11 11 529, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0f8 : bv 32 := 0x0084b603.
Lemma F_5f0f8 : fetch_word Asan.M.loaded_segments (0x5f148 : word) = Some W_5f0f8.
Proof. vm_refl. Qed.
Lemma D_5f0f8 : decode_any W_5f0f8 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f0fc : bv 32 := 0x01e75713.
Lemma F_5f0fc : fetch_word Asan.M.loaded_segments (0x5f14c : word) = Some W_5f0fc.
Proof. vm_refl. Qed.
Lemma D_5f0fc : decode_any W_5f0fc = Some (ShiftImm ALU_SRL 14 14 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f100 : bv 32 := 0x00e48733.
Lemma F_5f100 : fetch_word Asan.M.loaded_segments (0x5f150 : word) = Some W_5f100.
Proof. vm_refl. Qed.
Lemma D_5f100 : decode_any W_5f100 = Some (Op ALU_ADD 14 9 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f104 : bv 32 := 0x01076703.
Lemma F_5f104 : fetch_word Asan.M.loaded_segments (0x5f154 : word) = Some W_5f104.
Proof. vm_refl. Qed.
Lemma D_5f104 : decode_any W_5f104 = Some (Load SZ4 false 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f108 : bv 32 := 0x00c5b02f.
Lemma F_5f108 : fetch_word Asan.M.loaded_segments (0x5f158 : word) = Some W_5f108.
Proof. vm_refl. Qed.
Lemma D_5f108 : decode_any W_5f108 = Some (Amo AMO_ADD AD false false 0 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f10c : bv 32 := 0x02053503.
Lemma F_5f10c : fetch_word Asan.M.loaded_segments (0x5f15c : word) = Some W_5f10c.
Proof. vm_refl. Qed.
Lemma D_5f10c : decode_any W_5f10c = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f110 : bv 32 := 0x02041413.
Lemma F_5f110 : fetch_word Asan.M.loaded_segments (0x5f160 : word) = Some W_5f110.
Proof. vm_refl. Qed.
Lemma D_5f110 : decode_any W_5f110 = Some (ShiftImm ALU_SLL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f114 : bv 32 := 0x00471713.
Lemma F_5f114 : fetch_word Asan.M.loaded_segments (0x5f164 : word) = Some W_5f114.
Proof. vm_refl. Qed.
Lemma D_5f114 : decode_any W_5f114 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f118 : bv 32 := 0x00a40533.
Lemma F_5f118 : fetch_word Asan.M.loaded_segments (0x5f168 : word) = Some W_5f118.
Proof. vm_refl. Qed.
Lemma D_5f118 : decode_any W_5f118 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f11c : bv 32 := 0x00a70533.
Lemma F_5f11c : fetch_word Asan.M.loaded_segments (0x5f16c : word) = Some W_5f11c.
Proof. vm_refl. Qed.
Lemma D_5f11c : decode_any W_5f11c = Some (Op ALU_ADD 10 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f120 : bv 32 := 0x00900593.
Lemma F_5f120 : fetch_word Asan.M.loaded_segments (0x5f170 : word) = Some W_5f120.
Proof. vm_refl. Qed.
Lemma D_5f120 : decode_any W_5f120 = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f124 : bv 32 := 0x00b6e863.
Lemma F_5f124 : fetch_word Asan.M.loaded_segments (0x5f174 : word) = Some W_5f124.
Proof. vm_refl. Qed.
Lemma D_5f124 : decode_any W_5f124 = Some (Branch BC_LTU 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f128 : bv 32 := 0xfff68693.
Lemma F_5f128 : fetch_word Asan.M.loaded_segments (0x5f178 : word) = Some W_5f128.
Proof. vm_refl. Qed.
Lemma D_5f128 : decode_any W_5f128 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f12c : bv 32 := 0x00a6f6b3.
Lemma F_5f12c : fetch_word Asan.M.loaded_segments (0x5f17c : word) = Some W_5f12c.
Proof. vm_refl. Qed.
Lemma D_5f12c : decode_any W_5f12c = Some (Op ALU_AND 13 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f130 : bv 32 := 0x04069a63.
Lemma F_5f130 : fetch_word Asan.M.loaded_segments (0x5f180 : word) = Some W_5f130.
Proof. vm_refl. Qed.
Lemma D_5f130 : decode_any W_5f130 = Some (Branch BC_NE 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f134 : bv 32 := 0x02813083.
Lemma F_5f134 : fetch_word Asan.M.loaded_segments (0x5f184 : word) = Some W_5f134.
Proof. vm_refl. Qed.
Lemma D_5f134 : decode_any W_5f134 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f138 : bv 32 := 0x02013403.
Lemma F_5f138 : fetch_word Asan.M.loaded_segments (0x5f188 : word) = Some W_5f138.
Proof. vm_refl. Qed.
Lemma D_5f138 : decode_any W_5f138 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f13c : bv 32 := 0x01813483.
Lemma F_5f13c : fetch_word Asan.M.loaded_segments (0x5f18c : word) = Some W_5f13c.
Proof. vm_refl. Qed.
Lemma D_5f13c : decode_any W_5f13c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f140 : bv 32 := 0x01013903.
Lemma F_5f140 : fetch_word Asan.M.loaded_segments (0x5f190 : word) = Some W_5f140.
Proof. vm_refl. Qed.
Lemma D_5f140 : decode_any W_5f140 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f144 : bv 32 := 0x00813983.
Lemma F_5f144 : fetch_word Asan.M.loaded_segments (0x5f194 : word) = Some W_5f144.
Proof. vm_refl. Qed.
Lemma D_5f144 : decode_any W_5f144 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f148 : bv 32 := 0x00013a03.
Lemma F_5f148 : fetch_word Asan.M.loaded_segments (0x5f198 : word) = Some W_5f148.
Proof. vm_refl. Qed.
Lemma D_5f148 : decode_any W_5f148 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f14c : bv 32 := 0x03010113.
Lemma F_5f14c : fetch_word Asan.M.loaded_segments (0x5f19c : word) = Some W_5f14c.
Proof. vm_refl. Qed.
Lemma D_5f14c : decode_any W_5f14c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f150 : bv 32 := 0x00008067.
Lemma F_5f150 : fetch_word Asan.M.loaded_segments (0x5f1a0 : word) = Some W_5f150.
Proof. vm_refl. Qed.
Lemma D_5f150 : decode_any W_5f150 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1c0 : bv 32 := 0x00068913.
Lemma F_5f1c0 : fetch_word Asan.M.loaded_segments (0x5f210 : word) = Some W_5f1c0.
Proof. vm_refl. Qed.
Lemma D_5f1c0 : decode_any W_5f1c0 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1c4 : bv 32 := 0x00050613.
Lemma F_5f1c4 : fetch_word Asan.M.loaded_segments (0x5f214 : word) = Some W_5f1c4.
Proof. vm_refl. Qed.
Lemma D_5f1c4 : decode_any W_5f1c4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1c8 : bv 32 := 0x00058993.
Lemma F_5f1c8 : fetch_word Asan.M.loaded_segments (0x5f218 : word) = Some W_5f1c8.
Proof. vm_refl. Qed.
Lemma D_5f1c8 : decode_any W_5f1c8 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1cc : bv 32 := 0x00058513.
Lemma F_5f1cc : fetch_word Asan.M.loaded_segments (0x5f21c : word) = Some W_5f1cc.
Proof. vm_refl. Qed.
Lemma D_5f1cc : decode_any W_5f1cc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1d0 : bv 32 := 0x00048593.
Lemma F_5f1d0 : fetch_word Asan.M.loaded_segments (0x5f220 : word) = Some W_5f1d0.
Proof. vm_refl. Qed.
Lemma D_5f1d0 : decode_any W_5f1d0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1d4 : bv 32 := 0x00060a13.
Lemma F_5f1d4 : fetch_word Asan.M.loaded_segments (0x5f224 : word) = Some W_5f1d4.
Proof. vm_refl. Qed.
Lemma D_5f1d4 : decode_any W_5f1d4 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1d8 : bv 32 := 0x00040693.
Lemma F_5f1d8 : fetch_word Asan.M.loaded_segments (0x5f228 : word) = Some W_5f1d8.
Proof. vm_refl. Qed.
Lemma D_5f1d8 : decode_any W_5f1d8 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1dc : bv 32 := 0x4a4000ef.
Lemma F_5f1dc : fetch_word Asan.M.loaded_segments (0x5f22c : word) = Some W_5f1dc.
Proof. vm_refl. Qed.
Lemma D_5f1dc : decode_any W_5f1dc = Some (Jal 1 1188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1e0 : bv 32 := 0x00050c63.
Lemma F_5f1e0 : fetch_word Asan.M.loaded_segments (0x5f230 : word) = Some W_5f1e0.
Proof. vm_refl. Qed.
Lemma D_5f1e0 : decode_any W_5f1e0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1e4 : bv 32 := 0x0004a603.
Lemma F_5f1e4 : fetch_word Asan.M.loaded_segments (0x5f234 : word) = Some W_5f1e4.
Proof. vm_refl. Qed.
Lemma D_5f1e4 : decode_any W_5f1e4 = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1e8 : bv 32 := 0x00090693.
Lemma F_5f1e8 : fetch_word Asan.M.loaded_segments (0x5f238 : word) = Some W_5f1e8.
Proof. vm_refl. Qed.
Lemma D_5f1e8 : decode_any W_5f1e8 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1ec : bv 32 := 0x000a0513.
Lemma F_5f1ec : fetch_word Asan.M.loaded_segments (0x5f23c : word) = Some W_5f1ec.
Proof. vm_refl. Qed.
Lemma D_5f1ec : decode_any W_5f1ec = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1f0 : bv 32 := 0x00098593.
Lemma F_5f1f0 : fetch_word Asan.M.loaded_segments (0x5f240 : word) = Some W_5f1f0.
Proof. vm_refl. Qed.
Lemma D_5f1f0 : decode_any W_5f1f0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f1f4 : bv 32 := 0xef1ff06f.
Lemma F_5f1f4 : fetch_word Asan.M.loaded_segments (0x5f244 : word) = Some W_5f1f4.
Proof. vm_refl. Qed.
Lemma D_5f1f4 : decode_any W_5f1f4 = Some (Jal 0 2096880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f208 : bv 32 := 0xfa010113.
Lemma F_5f208 : fetch_word Asan.M.loaded_segments (0x5f258 : word) = Some W_5f208.
Proof. vm_refl. Qed.
Lemma D_5f208 : decode_any W_5f208 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f20c : bv 32 := 0x04113c23.
Lemma F_5f20c : fetch_word Asan.M.loaded_segments (0x5f25c : word) = Some W_5f20c.
Proof. vm_refl. Qed.
Lemma D_5f20c : decode_any W_5f20c = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f210 : bv 32 := 0x04813823.
Lemma F_5f210 : fetch_word Asan.M.loaded_segments (0x5f260 : word) = Some W_5f210.
Proof. vm_refl. Qed.
Lemma D_5f210 : decode_any W_5f210 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f214 : bv 32 := 0x04913423.
Lemma F_5f214 : fetch_word Asan.M.loaded_segments (0x5f264 : word) = Some W_5f214.
Proof. vm_refl. Qed.
Lemma D_5f214 : decode_any W_5f214 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f218 : bv 32 := 0x05213023.
Lemma F_5f218 : fetch_word Asan.M.loaded_segments (0x5f268 : word) = Some W_5f218.
Proof. vm_refl. Qed.
Lemma D_5f218 : decode_any W_5f218 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f21c : bv 32 := 0x03313c23.
Lemma F_5f21c : fetch_word Asan.M.loaded_segments (0x5f26c : word) = Some W_5f21c.
Proof. vm_refl. Qed.
Lemma D_5f21c : decode_any W_5f21c = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f220 : bv 32 := 0x03413823.
Lemma F_5f220 : fetch_word Asan.M.loaded_segments (0x5f270 : word) = Some W_5f220.
Proof. vm_refl. Qed.
Lemma D_5f220 : decode_any W_5f220 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f224 : bv 32 := 0x03513423.
Lemma F_5f224 : fetch_word Asan.M.loaded_segments (0x5f274 : word) = Some W_5f224.
Proof. vm_refl. Qed.
Lemma D_5f224 : decode_any W_5f224 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f228 : bv 32 := 0x03613023.
Lemma F_5f228 : fetch_word Asan.M.loaded_segments (0x5f278 : word) = Some W_5f228.
Proof. vm_refl. Qed.
Lemma D_5f228 : decode_any W_5f228 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f22c : bv 32 := 0x01713c23.
Lemma F_5f22c : fetch_word Asan.M.loaded_segments (0x5f27c : word) = Some W_5f22c.
Proof. vm_refl. Qed.
Lemma D_5f22c : decode_any W_5f22c = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f230 : bv 32 := 0x01813823.
Lemma F_5f230 : fetch_word Asan.M.loaded_segments (0x5f280 : word) = Some W_5f230.
Proof. vm_refl. Qed.
Lemma D_5f230 : decode_any W_5f230 = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f234 : bv 32 := 0x01913423.
Lemma F_5f234 : fetch_word Asan.M.loaded_segments (0x5f284 : word) = Some W_5f234.
Proof. vm_refl. Qed.
Lemma D_5f234 : decode_any W_5f234 = Some (Store SZ8 2 25 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f238 : bv 32 := 0x00058413.
Lemma F_5f238 : fetch_word Asan.M.loaded_segments (0x5f288 : word) = Some W_5f238.
Proof. vm_refl. Qed.
Lemma D_5f238 : decode_any W_5f238 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f23c : bv 32 := 0xfff68c13.
Lemma F_5f23c : fetch_word Asan.M.loaded_segments (0x5f28c : word) = Some W_5f23c.
Proof. vm_refl. Qed.
Lemma D_5f23c : decode_any W_5f23c = Some (OpImm ALU_ADD 24 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f240 : bv 32 := 0x0186f5b3.
Lemma F_5f240 : fetch_word Asan.M.loaded_segments (0x5f290 : word) = Some W_5f240.
Proof. vm_refl. Qed.
Lemma D_5f240 : decode_any W_5f240 = Some (Op ALU_AND 11 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f244 : bv 32 := 0x2c059a63.
Lemma F_5f244 : fetch_word Asan.M.loaded_segments (0x5f294 : word) = Some W_5f244.
Proof. vm_refl. Qed.
Lemma D_5f244 : decode_any W_5f244 = Some (Branch BC_NE 11 0 724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f248 : bv 32 := 0x00050493.
Lemma F_5f248 : fetch_word Asan.M.loaded_segments (0x5f298 : word) = Some W_5f248.
Proof. vm_refl. Qed.
Lemma D_5f248 : decode_any W_5f248 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f24c : bv 32 := 0x00053503.
Lemma F_5f24c : fetch_word Asan.M.loaded_segments (0x5f29c : word) = Some W_5f24c.
Proof. vm_refl. Qed.
Lemma D_5f24c : decode_any W_5f24c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f250 : bv 32 := 0xfff50593.
Lemma F_5f250 : fetch_word Asan.M.loaded_segments (0x5f2a0 : word) = Some W_5f250.
Proof. vm_refl. Qed.
Lemma D_5f250 : decode_any W_5f250 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f254 : bv 32 := 0x00b575b3.
Lemma F_5f254 : fetch_word Asan.M.loaded_segments (0x5f2a4 : word) = Some W_5f254.
Proof. vm_refl. Qed.
Lemma D_5f254 : decode_any W_5f254 = Some (Op ALU_AND 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f258 : bv 32 := 0x2e059063.
Lemma F_5f258 : fetch_word Asan.M.loaded_segments (0x5f2a8 : word) = Some W_5f258.
Proof. vm_refl. Qed.
Lemma D_5f258 : decode_any W_5f258 = Some (Branch BC_NE 11 0 736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f25c : bv 32 := 0x00060993.
Lemma F_5f25c : fetch_word Asan.M.loaded_segments (0x5f2ac : word) = Some W_5f25c.
Proof. vm_refl. Qed.
Lemma D_5f25c : decode_any W_5f25c = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f260 : bv 32 := 0x00a605b3.
Lemma F_5f260 : fetch_word Asan.M.loaded_segments (0x5f2b0 : word) = Some W_5f260.
Proof. vm_refl. Qed.
Lemma D_5f260 : decode_any W_5f260 = Some (Op ALU_ADD 11 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f264 : bv 32 := 0x40a00633.
Lemma F_5f264 : fetch_word Asan.M.loaded_segments (0x5f2b4 : word) = Some W_5f264.
Proof. vm_refl. Qed.
Lemma D_5f264 : decode_any W_5f264 = Some (Op ALU_SUB 12 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f268 : bv 32 := 0xfff58593.
Lemma F_5f268 : fetch_word Asan.M.loaded_segments (0x5f2b8 : word) = Some W_5f268.
Proof. vm_refl. Qed.
Lemma D_5f268 : decode_any W_5f268 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f26c : bv 32 := 0x00c5f5b3.
Lemma F_5f26c : fetch_word Asan.M.loaded_segments (0x5f2bc : word) = Some W_5f26c.
Proof. vm_refl. Qed.
Lemma D_5f26c : decode_any W_5f26c = Some (Op ALU_AND 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f270 : bv 32 := 0x00d53633.
Lemma F_5f270 : fetch_word Asan.M.loaded_segments (0x5f2c0 : word) = Some W_5f270.
Proof. vm_refl. Qed.
Lemma D_5f270 : decode_any W_5f270 = Some (Op ALU_SLTU 12 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f274 : bv 32 := 0x40c00633.
Lemma F_5f274 : fetch_word Asan.M.loaded_segments (0x5f2c4 : word) = Some W_5f274.
Proof. vm_refl. Qed.
Lemma D_5f274 : decode_any W_5f274 = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f278 : bv 32 := 0x00a58533.
Lemma F_5f278 : fetch_word Asan.M.loaded_segments (0x5f2c8 : word) = Some W_5f278.
Proof. vm_refl. Qed.
Lemma D_5f278 : decode_any W_5f278 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f27c : bv 32 := 0x00d67633.
Lemma F_5f27c : fetch_word Asan.M.loaded_segments (0x5f2cc : word) = Some W_5f27c.
Proof. vm_refl. Qed.
Lemma D_5f27c : decode_any W_5f27c = Some (Op ALU_AND 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f280 : bv 32 := 0x00c50933.
Lemma F_5f280 : fetch_word Asan.M.loaded_segments (0x5f2d0 : word) = Some W_5f280.
Proof. vm_refl. Qed.
Lemma D_5f280 : decode_any W_5f280 = Some (Op ALU_ADD 18 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f284 : bv 32 := 0x03397463.
Lemma F_5f284 : fetch_word Asan.M.loaded_segments (0x5f2d4 : word) = Some W_5f284.
Proof. vm_refl. Qed.
Lemma D_5f284 : decode_any W_5f284 = Some (Branch BC_GEU 18 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2ac : bv 32 := 0x00068a93.
Lemma F_5f2ac : fetch_word Asan.M.loaded_segments (0x5f2fc : word) = Some W_5f2ac.
Proof. vm_refl. Qed.
Lemma D_5f2ac : decode_any W_5f2ac = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2b0 : bv 32 := 0x00102517.
Lemma F_5f2b0 : fetch_word Asan.M.loaded_segments (0x5f300 : word) = Some W_5f2b0.
Proof. vm_refl. Qed.
Lemma D_5f2b0 : decode_any W_5f2b0 = Some (Auipc 10 258, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2b4 : bv 32 := 0x90053503.
Lemma F_5f2b4 : fetch_word Asan.M.loaded_segments (0x5f304 : word) = Some W_5f2b4.
Proof. vm_refl. Qed.
Lemma D_5f2b4 : decode_any W_5f2b4 = Some (Load SZ8 true 10 10 2304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2b8 : bv 32 := 0x00053583.
Lemma F_5f2b8 : fetch_word Asan.M.loaded_segments (0x5f308 : word) = Some W_5f2b8.
Proof. vm_refl. Qed.
Lemma D_5f2b8 : decode_any W_5f2b8 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2bc : bv 32 := 0x00090513.
Lemma F_5f2bc : fetch_word Asan.M.loaded_segments (0x5f30c : word) = Some W_5f2bc.
Proof. vm_refl. Qed.
Lemma D_5f2bc : decode_any W_5f2bc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2c0 : bv 32 := 0x7e4360ef.
Lemma F_5f2c0 : fetch_word Asan.M.loaded_segments (0x5f310 : word) = Some W_5f2c0.
Proof. vm_refl. Qed.
Lemma D_5f2c0 : decode_any W_5f2c0 = Some (Jal 1 223204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2c4 : bv 32 := 0x22050063.
Lemma F_5f2c4 : fetch_word Asan.M.loaded_segments (0x5f314 : word) = Some W_5f2c4.
Proof. vm_refl. Qed.
Lemma D_5f2c4 : decode_any W_5f2c4 = Some (Branch BC_EQ 10 0 544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2c8 : bv 32 := 0x00050a13.
Lemma F_5f2c8 : fetch_word Asan.M.loaded_segments (0x5f318 : word) = Some W_5f2c8.
Proof. vm_refl. Qed.
Lemma D_5f2c8 : decode_any W_5f2c8 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2cc : bv 32 := 0x0004b503.
Lemma F_5f2cc : fetch_word Asan.M.loaded_segments (0x5f31c : word) = Some W_5f2cc.
Proof. vm_refl. Qed.
Lemma D_5f2cc : decode_any W_5f2cc = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2d0 : bv 32 := 0xfff50593.
Lemma F_5f2d0 : fetch_word Asan.M.loaded_segments (0x5f320 : word) = Some W_5f2d0.
Proof. vm_refl. Qed.
Lemma D_5f2d0 : decode_any W_5f2d0 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2d4 : bv 32 := 0x0145f5b3.
Lemma F_5f2d4 : fetch_word Asan.M.loaded_segments (0x5f324 : word) = Some W_5f2d4.
Proof. vm_refl. Qed.
Lemma D_5f2d4 : decode_any W_5f2d4 = Some (Op ALU_AND 11 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2d8 : bv 32 := 0x26059863.
Lemma F_5f2d8 : fetch_word Asan.M.loaded_segments (0x5f328 : word) = Some W_5f2d8.
Proof. vm_refl. Qed.
Lemma D_5f2d8 : decode_any W_5f2d8 = Some (Branch BC_NE 11 0 624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2dc : bv 32 := 0x01490b33.
Lemma F_5f2dc : fetch_word Asan.M.loaded_segments (0x5f32c : word) = Some W_5f2dc.
Proof. vm_refl. Qed.
Lemma D_5f2dc : decode_any W_5f2dc = Some (Op ALU_ADD 22 18 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2e0 : bv 32 := 0x01450533.
Lemma F_5f2e0 : fetch_word Asan.M.loaded_segments (0x5f330 : word) = Some W_5f2e0.
Proof. vm_refl. Qed.
Lemma D_5f2e0 : decode_any W_5f2e0 = Some (Op ALU_ADD 10 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2e4 : bv 32 := 0x018575b3.
Lemma F_5f2e4 : fetch_word Asan.M.loaded_segments (0x5f334 : word) = Some W_5f2e4.
Proof. vm_refl. Qed.
Lemma D_5f2e4 : decode_any W_5f2e4 = Some (Op ALU_AND 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2e8 : bv 32 := 0x0015b613.
Lemma F_5f2e8 : fetch_word Asan.M.loaded_segments (0x5f338 : word) = Some W_5f2e8.
Proof. vm_refl. Qed.
Lemma D_5f2e8 : decode_any W_5f2e8 = Some (OpImm ALU_SLTU 12 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2ec : bv 32 := 0x40ba85b3.
Lemma F_5f2ec : fetch_word Asan.M.loaded_segments (0x5f33c : word) = Some W_5f2ec.
Proof. vm_refl. Qed.
Lemma D_5f2ec : decode_any W_5f2ec = Some (Op ALU_SUB 11 21 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2f0 : bv 32 := 0xfff60613.
Lemma F_5f2f0 : fetch_word Asan.M.loaded_segments (0x5f340 : word) = Some W_5f2f0.
Proof. vm_refl. Qed.
Lemma D_5f2f0 : decode_any W_5f2f0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2f4 : bv 32 := 0x00b675b3.
Lemma F_5f2f4 : fetch_word Asan.M.loaded_segments (0x5f344 : word) = Some W_5f2f4.
Proof. vm_refl. Qed.
Lemma D_5f2f4 : decode_any W_5f2f4 = Some (Op ALU_AND 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2f8 : bv 32 := 0x00a58cb3.
Lemma F_5f2f8 : fetch_word Asan.M.loaded_segments (0x5f348 : word) = Some W_5f2f8.
Proof. vm_refl. Qed.
Lemma D_5f2f8 : decode_any W_5f2f8 = Some (Op ALU_ADD 25 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f2fc : bv 32 := 0x013c8ab3.
Lemma F_5f2fc : fetch_word Asan.M.loaded_segments (0x5f34c : word) = Some W_5f2fc.
Proof. vm_refl. Qed.
Lemma D_5f2fc : decode_any W_5f2fc = Some (Op ALU_ADD 21 25 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f300 : bv 32 := 0x007c8513.
Lemma F_5f300 : fetch_word Asan.M.loaded_segments (0x5f350 : word) = Some W_5f300.
Proof. vm_refl. Qed.
Lemma D_5f300 : decode_any W_5f300 = Some (OpImm ALU_ADD 10 25 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f304 : bv 32 := 0xff8afb93.
Lemma F_5f304 : fetch_word Asan.M.loaded_segments (0x5f354 : word) = Some W_5f304.
Proof. vm_refl. Qed.
Lemma D_5f304 : decode_any W_5f304 = Some (OpImm ALU_AND 23 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f308 : bv 32 := 0xff857513.
Lemma F_5f308 : fetch_word Asan.M.loaded_segments (0x5f358 : word) = Some W_5f308.
Proof. vm_refl. Qed.
Lemma D_5f308 : decode_any W_5f308 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f30c : bv 32 := 0x414505b3.
Lemma F_5f30c : fetch_word Asan.M.loaded_segments (0x5f35c : word) = Some W_5f30c.
Proof. vm_refl. Qed.
Lemma D_5f30c : decode_any W_5f30c = Some (Op ALU_SUB 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f310 : bv 32 := 0x0fa00613.
Lemma F_5f310 : fetch_word Asan.M.loaded_segments (0x5f360 : word) = Some W_5f310.
Proof. vm_refl. Qed.
Lemma D_5f310 : decode_any W_5f310 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f314 : bv 32 := 0x000a0513.
Lemma F_5f314 : fetch_word Asan.M.loaded_segments (0x5f364 : word) = Some W_5f314.
Proof. vm_refl. Qed.
Lemma D_5f314 : decode_any W_5f314 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f318 : bv 32 := 0x57d230ef.
Lemma F_5f318 : fetch_word Asan.M.loaded_segments (0x5f368 : word) = Some W_5f318.
Proof. vm_refl. Qed.
Lemma D_5f318 : decode_any W_5f318 = Some (Jal 1 146812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f31c : bv 32 := 0x417b05b3.
Lemma F_5f31c : fetch_word Asan.M.loaded_segments (0x5f36c : word) = Some W_5f31c.
Proof. vm_refl. Qed.
Lemma D_5f31c : decode_any W_5f31c = Some (Op ALU_SUB 11 22 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f320 : bv 32 := 0x0fa00613.
Lemma F_5f320 : fetch_word Asan.M.loaded_segments (0x5f370 : word) = Some W_5f320.
Proof. vm_refl. Qed.
Lemma D_5f320 : decode_any W_5f320 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f324 : bv 32 := 0x000b8513.
Lemma F_5f324 : fetch_word Asan.M.loaded_segments (0x5f374 : word) = Some W_5f324.
Proof. vm_refl. Qed.
Lemma D_5f324 : decode_any W_5f324 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f328 : bv 32 := 0x56d230ef.
Lemma F_5f328 : fetch_word Asan.M.loaded_segments (0x5f378 : word) = Some W_5f328.
Proof. vm_refl. Qed.
Lemma D_5f328 : decode_any W_5f328 = Some (Jal 1 146796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f32c : bv 32 := 0x4e12b0ef.
Lemma F_5f32c : fetch_word Asan.M.loaded_segments (0x5f37c : word) = Some W_5f32c.
Proof. vm_refl. Qed.
Lemma D_5f32c : decode_any W_5f32c = Some (Jal 1 179424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f330 : bv 32 := 0x04853603.
Lemma F_5f330 : fetch_word Asan.M.loaded_segments (0x5f380 : word) = Some W_5f330.
Proof. vm_refl. Qed.
Lemma D_5f330 : decode_any W_5f330 = Some (Load SZ8 true 12 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f334 : bv 32 := 0x05053683.
Lemma F_5f334 : fetch_word Asan.M.loaded_segments (0x5f384 : word) = Some W_5f334.
Proof. vm_refl. Qed.
Lemma D_5f334 : decode_any W_5f334 = Some (Load SZ8 true 13 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f338 : bv 32 := 0x018cf733.
Lemma F_5f338 : fetch_word Asan.M.loaded_segments (0x5f388 : word) = Some W_5f338.
Proof. vm_refl. Qed.
Lemma D_5f338 : decode_any W_5f338 = Some (Op ALU_AND 14 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f33c : bv 32 := 0x00160613.
Lemma F_5f33c : fetch_word Asan.M.loaded_segments (0x5f38c : word) = Some W_5f33c.
Proof. vm_refl. Qed.
Lemma D_5f33c : decode_any W_5f33c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f340 : bv 32 := 0x012686b3.
Lemma F_5f340 : fetch_word Asan.M.loaded_segments (0x5f390 : word) = Some W_5f340.
Proof. vm_refl. Qed.
Lemma D_5f340 : decode_any W_5f340 = Some (Op ALU_ADD 13 13 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f344 : bv 32 := 0x04c53423.
Lemma F_5f344 : fetch_word Asan.M.loaded_segments (0x5f394 : word) = Some W_5f344.
Proof. vm_refl. Qed.
Lemma D_5f344 : decode_any W_5f344 = Some (Store SZ8 10 12 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f348 : bv 32 := 0x04d53823.
Lemma F_5f348 : fetch_word Asan.M.loaded_segments (0x5f398 : word) = Some W_5f348.
Proof. vm_refl. Qed.
Lemma D_5f348 : decode_any W_5f348 = Some (Store SZ8 10 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f34c : bv 32 := 0x20071e63.
Lemma F_5f34c : fetch_word Asan.M.loaded_segments (0x5f39c : word) = Some W_5f34c.
Proof. vm_refl. Qed.
Lemma D_5f34c : decode_any W_5f34c = Some (Branch BC_NE 14 0 540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f350 : bv 32 := 0x000c8513.
Lemma F_5f350 : fetch_word Asan.M.loaded_segments (0x5f3a0 : word) = Some W_5f350.
Proof. vm_refl. Qed.
Lemma D_5f350 : decode_any W_5f350 = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f354 : bv 32 := 0x0004b583.
Lemma F_5f354 : fetch_word Asan.M.loaded_segments (0x5f3a4 : word) = Some W_5f354.
Proof. vm_refl. Qed.
Lemma D_5f354 : decode_any W_5f354 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f358 : bv 32 := 0xfff58613.
Lemma F_5f358 : fetch_word Asan.M.loaded_segments (0x5f3a8 : word) = Some W_5f358.
Proof. vm_refl. Qed.
Lemma D_5f358 : decode_any W_5f358 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f35c : bv 32 := 0x01967633.
Lemma F_5f35c : fetch_word Asan.M.loaded_segments (0x5f3ac : word) = Some W_5f35c.
Proof. vm_refl. Qed.
Lemma D_5f35c : decode_any W_5f35c = Some (Op ALU_AND 12 12 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f360 : bv 32 := 0x22061463.
Lemma F_5f360 : fetch_word Asan.M.loaded_segments (0x5f3b0 : word) = Some W_5f360.
Proof. vm_refl. Qed.
Lemma D_5f360 : decode_any W_5f360 = Some (Branch BC_NE 12 0 552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f364 : bv 32 := 0x254ae263.
Lemma F_5f364 : fetch_word Asan.M.loaded_segments (0x5f3b4 : word) = Some W_5f364.
Proof. vm_refl. Qed.
Lemma D_5f364 : decode_any W_5f364 = Some (Branch BC_LTU 21 20 580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f368 : bv 32 := 0x275b6063.
Lemma F_5f368 : fetch_word Asan.M.loaded_segments (0x5f3b8 : word) = Some W_5f368.
Proof. vm_refl. Qed.
Lemma D_5f368 : decode_any W_5f368 = Some (Branch BC_LTU 22 21 608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f36c : bv 32 := 0x40b50ab3.
Lemma F_5f36c : fetch_word Asan.M.loaded_segments (0x5f3bc : word) = Some W_5f36c.
Proof. vm_refl. Qed.
Lemma D_5f36c : decode_any W_5f36c = Some (Op ALU_SUB 21 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f370 : bv 32 := 0x014ab023.
Lemma F_5f370 : fetch_word Asan.M.loaded_segments (0x5f3c0 : word) = Some W_5f370.
Proof. vm_refl. Qed.
Lemma D_5f370 : decode_any W_5f370 = Some (Store SZ8 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f374 : bv 32 := 0x012ab423.
Lemma F_5f374 : fetch_word Asan.M.loaded_segments (0x5f3c4 : word) = Some W_5f374.
Proof. vm_refl. Qed.
Lemma D_5f374 : decode_any W_5f374 = Some (Store SZ8 21 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f378 : bv 32 := 0x013ab823.
Lemma F_5f378 : fetch_word Asan.M.loaded_segments (0x5f3c8 : word) = Some W_5f378.
Proof. vm_refl. Qed.
Lemma D_5f378 : decode_any W_5f378 = Some (Store SZ8 21 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f37c : bv 32 := 0x26090663.
Lemma F_5f37c : fetch_word Asan.M.loaded_segments (0x5f3cc : word) = Some W_5f37c.
Proof. vm_refl. Qed.
Lemma D_5f37c : decode_any W_5f37c = Some (Branch BC_EQ 18 0 620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f380 : bv 32 := 0x26848593.
Lemma F_5f380 : fetch_word Asan.M.loaded_segments (0x5f3d0 : word) = Some W_5f380.
Proof. vm_refl. Qed.
Lemma D_5f380 : decode_any W_5f380 = Some (OpImm ALU_ADD 11 9 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f384 : bv 32 := 0x0ff00613.
Lemma F_5f384 : fetch_word Asan.M.loaded_segments (0x5f3d4 : word) = Some W_5f384.
Proof. vm_refl. Qed.
Lemma D_5f384 : decode_any W_5f384 = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f388 : bv 32 := 0xffc5f693.
Lemma F_5f388 : fetch_word Asan.M.loaded_segments (0x5f3d8 : word) = Some W_5f388.
Proof. vm_refl. Qed.
Lemma D_5f388 : decode_any W_5f388 = Some (OpImm ALU_AND 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f38c : bv 32 := 0x00100713.
Lemma F_5f38c : fetch_word Asan.M.loaded_segments (0x5f3dc : word) = Some W_5f38c.
Proof. vm_refl. Qed.
Lemma D_5f38c : decode_any W_5f38c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f390 : bv 32 := 0x1406a7af.
Lemma F_5f390 : fetch_word Asan.M.loaded_segments (0x5f3e0 : word) = Some W_5f390.
Proof. vm_refl. Qed.
Lemma D_5f390 : decode_any W_5f390 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f394 : bv 32 := 0x00070813.
Lemma F_5f394 : fetch_word Asan.M.loaded_segments (0x5f3e4 : word) = Some W_5f394.
Proof. vm_refl. Qed.
Lemma D_5f394 : decode_any W_5f394 = Some (OpImm ALU_ADD 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f398 : bv 32 := 0x0107c833.
Lemma F_5f398 : fetch_word Asan.M.loaded_segments (0x5f3e8 : word) = Some W_5f398.
Proof. vm_refl. Qed.
Lemma D_5f398 : decode_any W_5f398 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f39c : bv 32 := 0x00c87833.
Lemma F_5f39c : fetch_word Asan.M.loaded_segments (0x5f3ec : word) = Some W_5f39c.
Proof. vm_refl. Qed.
Lemma D_5f39c : decode_any W_5f39c = Some (Op ALU_AND 16 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3a0 : bv 32 := 0x0107c833.
Lemma F_5f3a0 : fetch_word Asan.M.loaded_segments (0x5f3f0 : word) = Some W_5f3a0.
Proof. vm_refl. Qed.
Lemma D_5f3a0 : decode_any W_5f3a0 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3a4 : bv 32 := 0x1906a82f.
Lemma F_5f3a4 : fetch_word Asan.M.loaded_segments (0x5f3f4 : word) = Some W_5f3a4.
Proof. vm_refl. Qed.
Lemma D_5f3a4 : decode_any W_5f3a4 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3a8 : bv 32 := 0xfe0814e3.
Lemma F_5f3a8 : fetch_word Asan.M.loaded_segments (0x5f3f8 : word) = Some W_5f3a8.
Proof. vm_refl. Qed.
Lemma D_5f3a8 : decode_any W_5f3a8 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3ac : bv 32 := 0x0ff7f613.
Lemma F_5f3ac : fetch_word Asan.M.loaded_segments (0x5f3fc : word) = Some W_5f3ac.
Proof. vm_refl. Qed.
Lemma D_5f3ac : decode_any W_5f3ac = Some (OpImm ALU_AND 12 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3b0 : bv 32 := 0x24061c63.
Lemma F_5f3b0 : fetch_word Asan.M.loaded_segments (0x5f400 : word) = Some W_5f3b0.
Proof. vm_refl. Qed.
Lemma D_5f3b0 : decode_any W_5f3b0 = Some (Branch BC_NE 12 0 600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3b4 : bv 32 := 0x0384b683.
Lemma F_5f3b4 : fetch_word Asan.M.loaded_segments (0x5f404 : word) = Some W_5f3b4.
Proof. vm_refl. Qed.
Lemma D_5f3b4 : decode_any W_5f3b4 = Some (Load SZ8 true 13 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3b8 : bv 32 := 0x0146d593.
Lemma F_5f3b8 : fetch_word Asan.M.loaded_segments (0x5f408 : word) = Some W_5f3b8.
Proof. vm_refl. Qed.
Lemma D_5f3b8 : decode_any W_5f3b8 = Some (ShiftImm ALU_SRL 11 13 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3bc : bv 32 := 0x26059463.
Lemma F_5f3bc : fetch_word Asan.M.loaded_segments (0x5f40c : word) = Some W_5f3bc.
Proof. vm_refl. Qed.
Lemma D_5f3bc : decode_any W_5f3bc = Some (Branch BC_NE 11 0 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3c0 : bv 32 := 0x00195593.
Lemma F_5f3c0 : fetch_word Asan.M.loaded_segments (0x5f410 : word) = Some W_5f3c0.
Proof. vm_refl. Qed.
Lemma D_5f3c0 : decode_any W_5f3c0 = Some (ShiftImm ALU_SRL 11 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3c4 : bv 32 := 0x55555637.
Lemma F_5f3c4 : fetch_word Asan.M.loaded_segments (0x5f414 : word) = Some W_5f3c4.
Proof. vm_refl. Qed.
Lemma D_5f3c4 : decode_any W_5f3c4 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3c8 : bv 32 := 0x33333737.
Lemma F_5f3c8 : fetch_word Asan.M.loaded_segments (0x5f418 : word) = Some W_5f3c8.
Proof. vm_refl. Qed.
Lemma D_5f3c8 : decode_any W_5f3c8 = Some (Lui 14 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3cc : bv 32 := 0x0f0f17b7.
Lemma F_5f3cc : fetch_word Asan.M.loaded_segments (0x5f41c : word) = Some W_5f3cc.
Proof. vm_refl. Qed.
Lemma D_5f3cc : decode_any W_5f3cc = Some (Lui 15 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3d0 : bv 32 := 0x00b965b3.
Lemma F_5f3d0 : fetch_word Asan.M.loaded_segments (0x5f420 : word) = Some W_5f3d0.
Proof. vm_refl. Qed.
Lemma D_5f3d0 : decode_any W_5f3d0 = Some (Op ALU_OR 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3d4 : bv 32 := 0x5556061b.
Lemma F_5f3d4 : fetch_word Asan.M.loaded_segments (0x5f424 : word) = Some W_5f3d4.
Proof. vm_refl. Qed.
Lemma D_5f3d4 : decode_any W_5f3d4 = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3d8 : bv 32 := 0x3337071b.
Lemma F_5f3d8 : fetch_word Asan.M.loaded_segments (0x5f428 : word) = Some W_5f3d8.
Proof. vm_refl. Qed.
Lemma D_5f3d8 : decode_any W_5f3d8 = Some (OpImm32 14 14 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3dc : bv 32 := 0xf0f7879b.
Lemma F_5f3dc : fetch_word Asan.M.loaded_segments (0x5f42c : word) = Some W_5f3dc.
Proof. vm_refl. Qed.
Lemma D_5f3dc : decode_any W_5f3dc = Some (OpImm32 15 15 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3e0 : bv 32 := 0x0025d813.
Lemma F_5f3e0 : fetch_word Asan.M.loaded_segments (0x5f430 : word) = Some W_5f3e0.
Proof. vm_refl. Qed.
Lemma D_5f3e0 : decode_any W_5f3e0 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3e4 : bv 32 := 0x0105e5b3.
Lemma F_5f3e4 : fetch_word Asan.M.loaded_segments (0x5f434 : word) = Some W_5f3e4.
Proof. vm_refl. Qed.
Lemma D_5f3e4 : decode_any W_5f3e4 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3e8 : bv 32 := 0x02061813.
Lemma F_5f3e8 : fetch_word Asan.M.loaded_segments (0x5f438 : word) = Some W_5f3e8.
Proof. vm_refl. Qed.
Lemma D_5f3e8 : decode_any W_5f3e8 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3ec : bv 32 := 0x01060633.
Lemma F_5f3ec : fetch_word Asan.M.loaded_segments (0x5f43c : word) = Some W_5f3ec.
Proof. vm_refl. Qed.
Lemma D_5f3ec : decode_any W_5f3ec = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3f0 : bv 32 := 0x02071813.
Lemma F_5f3f0 : fetch_word Asan.M.loaded_segments (0x5f440 : word) = Some W_5f3f0.
Proof. vm_refl. Qed.
Lemma D_5f3f0 : decode_any W_5f3f0 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3f4 : bv 32 := 0x01070733.
Lemma F_5f3f4 : fetch_word Asan.M.loaded_segments (0x5f444 : word) = Some W_5f3f4.
Proof. vm_refl. Qed.
Lemma D_5f3f4 : decode_any W_5f3f4 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3f8 : bv 32 := 0x02079813.
Lemma F_5f3f8 : fetch_word Asan.M.loaded_segments (0x5f448 : word) = Some W_5f3f8.
Proof. vm_refl. Qed.
Lemma D_5f3f8 : decode_any W_5f3f8 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f3fc : bv 32 := 0x010787b3.
Lemma F_5f3fc : fetch_word Asan.M.loaded_segments (0x5f44c : word) = Some W_5f3fc.
Proof. vm_refl. Qed.
Lemma D_5f3fc : decode_any W_5f3fc = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f400 : bv 32 := 0x0045d813.
Lemma F_5f400 : fetch_word Asan.M.loaded_segments (0x5f450 : word) = Some W_5f400.
Proof. vm_refl. Qed.
Lemma D_5f400 : decode_any W_5f400 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f404 : bv 32 := 0x0105e5b3.
Lemma F_5f404 : fetch_word Asan.M.loaded_segments (0x5f454 : word) = Some W_5f404.
Proof. vm_refl. Qed.
Lemma D_5f404 : decode_any W_5f404 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f408 : bv 32 := 0x0085d813.
Lemma F_5f408 : fetch_word Asan.M.loaded_segments (0x5f458 : word) = Some W_5f408.
Proof. vm_refl. Qed.
Lemma D_5f408 : decode_any W_5f408 = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f40c : bv 32 := 0x0105e5b3.
Lemma F_5f40c : fetch_word Asan.M.loaded_segments (0x5f45c : word) = Some W_5f40c.
Proof. vm_refl. Qed.
Lemma D_5f40c : decode_any W_5f40c = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f410 : bv 32 := 0x0105d813.
Lemma F_5f410 : fetch_word Asan.M.loaded_segments (0x5f460 : word) = Some W_5f410.
Proof. vm_refl. Qed.
Lemma D_5f410 : decode_any W_5f410 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f414 : bv 32 := 0x0105e5b3.
Lemma F_5f414 : fetch_word Asan.M.loaded_segments (0x5f464 : word) = Some W_5f414.
Proof. vm_refl. Qed.
Lemma D_5f414 : decode_any W_5f414 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f418 : bv 32 := 0x0205d813.
Lemma F_5f418 : fetch_word Asan.M.loaded_segments (0x5f468 : word) = Some W_5f418.
Proof. vm_refl. Qed.
Lemma D_5f418 : decode_any W_5f418 = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f41c : bv 32 := 0x0105e5b3.
Lemma F_5f41c : fetch_word Asan.M.loaded_segments (0x5f46c : word) = Some W_5f41c.
Proof. vm_refl. Qed.
Lemma D_5f41c : decode_any W_5f41c = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f420 : bv 32 := 0xfff5c593.
Lemma F_5f420 : fetch_word Asan.M.loaded_segments (0x5f470 : word) = Some W_5f420.
Proof. vm_refl. Qed.
Lemma D_5f420 : decode_any W_5f420 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f424 : bv 32 := 0x0015d813.
Lemma F_5f424 : fetch_word Asan.M.loaded_segments (0x5f474 : word) = Some W_5f424.
Proof. vm_refl. Qed.
Lemma D_5f424 : decode_any W_5f424 = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f428 : bv 32 := 0x00c87633.
Lemma F_5f428 : fetch_word Asan.M.loaded_segments (0x5f478 : word) = Some W_5f428.
Proof. vm_refl. Qed.
Lemma D_5f428 : decode_any W_5f428 = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f42c : bv 32 := 0x01010837.
Lemma F_5f42c : fetch_word Asan.M.loaded_segments (0x5f47c : word) = Some W_5f42c.
Proof. vm_refl. Qed.
Lemma D_5f42c : decode_any W_5f42c = Some (Lui 16 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f430 : bv 32 := 0x40c585b3.
Lemma F_5f430 : fetch_word Asan.M.loaded_segments (0x5f480 : word) = Some W_5f430.
Proof. vm_refl. Qed.
Lemma D_5f430 : decode_any W_5f430 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f434 : bv 32 := 0x0025d613.
Lemma F_5f434 : fetch_word Asan.M.loaded_segments (0x5f484 : word) = Some W_5f434.
Proof. vm_refl. Qed.
Lemma D_5f434 : decode_any W_5f434 = Some (ShiftImm ALU_SRL 12 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f438 : bv 32 := 0x00e5f5b3.
Lemma F_5f438 : fetch_word Asan.M.loaded_segments (0x5f488 : word) = Some W_5f438.
Proof. vm_refl. Qed.
Lemma D_5f438 : decode_any W_5f438 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f43c : bv 32 := 0x00e67633.
Lemma F_5f43c : fetch_word Asan.M.loaded_segments (0x5f48c : word) = Some W_5f43c.
Proof. vm_refl. Qed.
Lemma D_5f43c : decode_any W_5f43c = Some (Op ALU_AND 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f440 : bv 32 := 0x0304b703.
Lemma F_5f440 : fetch_word Asan.M.loaded_segments (0x5f490 : word) = Some W_5f440.
Proof. vm_refl. Qed.
Lemma D_5f440 : decode_any W_5f440 = Some (Load SZ8 true 14 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f444 : bv 32 := 0x1018081b.
Lemma F_5f444 : fetch_word Asan.M.loaded_segments (0x5f494 : word) = Some W_5f444.
Proof. vm_refl. Qed.
Lemma D_5f444 : decode_any W_5f444 = Some (OpImm32 16 16 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f448 : bv 32 := 0x00c585b3.
Lemma F_5f448 : fetch_word Asan.M.loaded_segments (0x5f498 : word) = Some W_5f448.
Proof. vm_refl. Qed.
Lemma D_5f448 : decode_any W_5f448 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f44c : bv 32 := 0x0045d613.
Lemma F_5f44c : fetch_word Asan.M.loaded_segments (0x5f49c : word) = Some W_5f44c.
Proof. vm_refl. Qed.
Lemma D_5f44c : decode_any W_5f44c = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f450 : bv 32 := 0x00c585b3.
Lemma F_5f450 : fetch_word Asan.M.loaded_segments (0x5f4a0 : word) = Some W_5f450.
Proof. vm_refl. Qed.
Lemma D_5f450 : decode_any W_5f450 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f454 : bv 32 := 0x02081613.
Lemma F_5f454 : fetch_word Asan.M.loaded_segments (0x5f4a4 : word) = Some W_5f454.
Proof. vm_refl. Qed.
Lemma D_5f454 : decode_any W_5f454 = Some (ShiftImm ALU_SLL 12 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f458 : bv 32 := 0x00f5f5b3.
Lemma F_5f458 : fetch_word Asan.M.loaded_segments (0x5f4a8 : word) = Some W_5f458.
Proof. vm_refl. Qed.
Lemma D_5f458 : decode_any W_5f458 = Some (Op ALU_AND 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f45c : bv 32 := 0x00c80633.
Lemma F_5f45c : fetch_word Asan.M.loaded_segments (0x5f4ac : word) = Some W_5f45c.
Proof. vm_refl. Qed.
Lemma D_5f45c : decode_any W_5f45c = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f460 : bv 32 := 0x02c585b3.
Lemma F_5f460 : fetch_word Asan.M.loaded_segments (0x5f4b0 : word) = Some W_5f460.
Proof. vm_refl. Qed.
Lemma D_5f460 : decode_any W_5f460 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f464 : bv 32 := 0x0385d993.
Lemma F_5f464 : fetch_word Asan.M.loaded_segments (0x5f4b4 : word) = Some W_5f464.
Proof. vm_refl. Qed.
Lemma D_5f464 : decode_any W_5f464 = Some (ShiftImm ALU_SRL 19 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f468 : bv 32 := 0x1ce68c63.
Lemma F_5f468 : fetch_word Asan.M.loaded_segments (0x5f4b8 : word) = Some W_5f468.
Proof. vm_refl. Qed.
Lemma D_5f468 : decode_any W_5f468 = Some (Branch BC_EQ 13 14 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f46c : bv 32 := 0x0084b603.
Lemma F_5f46c : fetch_word Asan.M.loaded_segments (0x5f4bc : word) = Some W_5f46c.
Proof. vm_refl. Qed.
Lemma D_5f46c : decode_any W_5f46c = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f470 : bv 32 := 0x03f9c593.
Lemma F_5f470 : fetch_word Asan.M.loaded_segments (0x5f4c0 : word) = Some W_5f470.
Proof. vm_refl. Qed.
Lemma D_5f470 : decode_any W_5f470 = Some (OpImm ALU_XOR 11 19 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f474 : bv 32 := 0x00dabc23.
Lemma F_5f474 : fetch_word Asan.M.loaded_segments (0x5f4c4 : word) = Some W_5f474.
Proof. vm_refl. Qed.
Lemma D_5f474 : decode_any W_5f474 = Some (Store SZ8 21 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f478 : bv 32 := 0x00369713.
Lemma F_5f478 : fetch_word Asan.M.loaded_segments (0x5f4c8 : word) = Some W_5f478.
Proof. vm_refl. Qed.
Lemma D_5f478 : decode_any W_5f478 = Some (ShiftImm ALU_SLL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f47c : bv 32 := 0x00e60633.
Lemma F_5f47c : fetch_word Asan.M.loaded_segments (0x5f4cc : word) = Some W_5f47c.
Proof. vm_refl. Qed.
Lemma D_5f47c : decode_any W_5f47c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f480 : bv 32 := 0x01563023.
Lemma F_5f480 : fetch_word Asan.M.loaded_segments (0x5f4d0 : word) = Some W_5f480.
Proof. vm_refl. Qed.
Lemma D_5f480 : decode_any W_5f480 = Some (Store SZ8 12 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f484 : bv 32 := 0x0484b703.
Lemma F_5f484 : fetch_word Asan.M.loaded_segments (0x5f4d4 : word) = Some W_5f484.
Proof. vm_refl. Qed.
Lemma D_5f484 : decode_any W_5f484 = Some (Load SZ8 true 14 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f488 : bv 32 := 0x0584b783.
Lemma F_5f488 : fetch_word Asan.M.loaded_segments (0x5f4d8 : word) = Some W_5f488.
Proof. vm_refl. Qed.
Lemma D_5f488 : decode_any W_5f488 = Some (Load SZ8 true 15 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f48c : bv 32 := 0x00168813.
Lemma F_5f48c : fetch_word Asan.M.loaded_segments (0x5f4dc : word) = Some W_5f48c.
Proof. vm_refl. Qed.
Lemma D_5f48c : decode_any W_5f48c = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f490 : bv 32 := 0x0604b603.
Lemma F_5f490 : fetch_word Asan.M.loaded_segments (0x5f4e0 : word) = Some W_5f490.
Proof. vm_refl. Qed.
Lemma D_5f490 : decode_any W_5f490 = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f494 : bv 32 := 0x00170713.
Lemma F_5f494 : fetch_word Asan.M.loaded_segments (0x5f4e4 : word) = Some W_5f494.
Proof. vm_refl. Qed.
Lemma D_5f494 : decode_any W_5f494 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f498 : bv 32 := 0x012786b3.
Lemma F_5f498 : fetch_word Asan.M.loaded_segments (0x5f4e8 : word) = Some W_5f498.
Proof. vm_refl. Qed.
Lemma D_5f498 : decode_any W_5f498 = Some (Op ALU_ADD 13 15 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f49c : bv 32 := 0x0304bc23.
Lemma F_5f49c : fetch_word Asan.M.loaded_segments (0x5f4ec : word) = Some W_5f49c.
Proof. vm_refl. Qed.
Lemma D_5f49c : decode_any W_5f49c = Some (Store SZ8 9 16 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4a0 : bv 32 := 0x04048023.
Lemma F_5f4a0 : fetch_word Asan.M.loaded_segments (0x5f4f0 : word) = Some W_5f4a0.
Proof. vm_refl. Qed.
Lemma D_5f4a0 : decode_any W_5f4a0 = Some (Store SZ1 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4a4 : bv 32 := 0x04e4b423.
Lemma F_5f4a4 : fetch_word Asan.M.loaded_segments (0x5f4f4 : word) = Some W_5f4a4.
Proof. vm_refl. Qed.
Lemma D_5f4a4 : decode_any W_5f4a4 = Some (Store SZ8 9 14 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4a8 : bv 32 := 0x04d4bc23.
Lemma F_5f4a8 : fetch_word Asan.M.loaded_segments (0x5f4f8 : word) = Some W_5f4a8.
Proof. vm_refl. Qed.
Lemma D_5f4a8 : decode_any W_5f4a8 = Some (Store SZ8 9 13 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4ac : bv 32 := 0x00c6e463.
Lemma F_5f4ac : fetch_word Asan.M.loaded_segments (0x5f4fc : word) = Some W_5f4ac.
Proof. vm_refl. Qed.
Lemma D_5f4ac : decode_any W_5f4ac = Some (Branch BC_LTU 13 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4b0 : bv 32 := 0x00068613.
Lemma F_5f4b0 : fetch_word Asan.M.loaded_segments (0x5f500 : word) = Some W_5f4b0.
Proof. vm_refl. Qed.
Lemma D_5f4b0 : decode_any W_5f4b0 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4b4 : bv 32 := 0x00359593.
Lemma F_5f4b4 : fetch_word Asan.M.loaded_segments (0x5f504 : word) = Some W_5f4b4.
Proof. vm_refl. Qed.
Lemma D_5f4b4 : decode_any W_5f4b4 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4b8 : bv 32 := 0x00b485b3.
Lemma F_5f4b8 : fetch_word Asan.M.loaded_segments (0x5f508 : word) = Some W_5f4b8.
Proof. vm_refl. Qed.
Lemma D_5f4b8 : decode_any W_5f4b8 = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4bc : bv 32 := 0x0685b683.
Lemma F_5f4bc : fetch_word Asan.M.loaded_segments (0x5f50c : word) = Some W_5f4bc.
Proof. vm_refl. Qed.
Lemma D_5f4bc : decode_any W_5f4bc = Some (Load SZ8 true 13 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4c0 : bv 32 := 0x00168693.
Lemma F_5f4c0 : fetch_word Asan.M.loaded_segments (0x5f510 : word) = Some W_5f4c0.
Proof. vm_refl. Qed.
Lemma D_5f4c0 : decode_any W_5f4c0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4c4 : bv 32 := 0x06c4b023.
Lemma F_5f4c4 : fetch_word Asan.M.loaded_segments (0x5f514 : word) = Some W_5f4c4.
Proof. vm_refl. Qed.
Lemma D_5f4c4 : decode_any W_5f4c4 = Some (Store SZ8 9 12 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4c8 : bv 32 := 0x06d5b423.
Lemma F_5f4c8 : fetch_word Asan.M.loaded_segments (0x5f518 : word) = Some W_5f4c8.
Proof. vm_refl. Qed.
Lemma D_5f4c8 : decode_any W_5f4c8 = Some (Store SZ8 11 13 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4cc : bv 32 := 0x01040593.
Lemma F_5f4cc : fetch_word Asan.M.loaded_segments (0x5f51c : word) = Some W_5f4cc.
Proof. vm_refl. Qed.
Lemma D_5f4cc : decode_any W_5f4cc = Some (OpImm ALU_ADD 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4d0 : bv 32 := 0x0125b02f.
Lemma F_5f4d0 : fetch_word Asan.M.loaded_segments (0x5f520 : word) = Some W_5f4d0.
Proof. vm_refl. Qed.
Lemma D_5f4d0 : decode_any W_5f4d0 = Some (Amo AMO_ADD AD false false 0 11 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4d4 : bv 32 := 0x01840413.
Lemma F_5f4d4 : fetch_word Asan.M.loaded_segments (0x5f524 : word) = Some W_5f4d4.
Proof. vm_refl. Qed.
Lemma D_5f4d4 : decode_any W_5f4d4 = Some (OpImm ALU_ADD 8 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4d8 : bv 32 := 0x0124302f.
Lemma F_5f4d8 : fetch_word Asan.M.loaded_segments (0x5f528 : word) = Some W_5f4d8.
Proof. vm_refl. Qed.
Lemma D_5f4d8 : decode_any W_5f4d8 = Some (Amo AMO_ADD AD false false 0 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4dc : bv 32 := 0x0310000f.
Lemma F_5f4dc : fetch_word Asan.M.loaded_segments (0x5f52c : word) = Some W_5f4dc.
Proof. vm_refl. Qed.
Lemma D_5f4dc : decode_any W_5f4dc = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4e0 : bv 32 := 0x26048423.
Lemma F_5f4e0 : fetch_word Asan.M.loaded_segments (0x5f530 : word) = Some W_5f4e0.
Proof. vm_refl. Qed.
Lemma D_5f4e0 : decode_any W_5f4e0 = Some (Store SZ1 9 0 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4e4 : bv 32 := 0x05813083.
Lemma F_5f4e4 : fetch_word Asan.M.loaded_segments (0x5f534 : word) = Some W_5f4e4.
Proof. vm_refl. Qed.
Lemma D_5f4e4 : decode_any W_5f4e4 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4e8 : bv 32 := 0x05013403.
Lemma F_5f4e8 : fetch_word Asan.M.loaded_segments (0x5f538 : word) = Some W_5f4e8.
Proof. vm_refl. Qed.
Lemma D_5f4e8 : decode_any W_5f4e8 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4ec : bv 32 := 0x04813483.
Lemma F_5f4ec : fetch_word Asan.M.loaded_segments (0x5f53c : word) = Some W_5f4ec.
Proof. vm_refl. Qed.
Lemma D_5f4ec : decode_any W_5f4ec = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4f0 : bv 32 := 0x04013903.
Lemma F_5f4f0 : fetch_word Asan.M.loaded_segments (0x5f540 : word) = Some W_5f4f0.
Proof. vm_refl. Qed.
Lemma D_5f4f0 : decode_any W_5f4f0 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4f4 : bv 32 := 0x03813983.
Lemma F_5f4f4 : fetch_word Asan.M.loaded_segments (0x5f544 : word) = Some W_5f4f4.
Proof. vm_refl. Qed.
Lemma D_5f4f4 : decode_any W_5f4f4 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4f8 : bv 32 := 0x03013a03.
Lemma F_5f4f8 : fetch_word Asan.M.loaded_segments (0x5f548 : word) = Some W_5f4f8.
Proof. vm_refl. Qed.
Lemma D_5f4f8 : decode_any W_5f4f8 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f4fc : bv 32 := 0x02813a83.
Lemma F_5f4fc : fetch_word Asan.M.loaded_segments (0x5f54c : word) = Some W_5f4fc.
Proof. vm_refl. Qed.
Lemma D_5f4fc : decode_any W_5f4fc = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f500 : bv 32 := 0x02013b03.
Lemma F_5f500 : fetch_word Asan.M.loaded_segments (0x5f550 : word) = Some W_5f500.
Proof. vm_refl. Qed.
Lemma D_5f500 : decode_any W_5f500 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f504 : bv 32 := 0x01813b83.
Lemma F_5f504 : fetch_word Asan.M.loaded_segments (0x5f554 : word) = Some W_5f504.
Proof. vm_refl. Qed.
Lemma D_5f504 : decode_any W_5f504 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f508 : bv 32 := 0x01013c03.
Lemma F_5f508 : fetch_word Asan.M.loaded_segments (0x5f558 : word) = Some W_5f508.
Proof. vm_refl. Qed.
Lemma D_5f508 : decode_any W_5f508 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f50c : bv 32 := 0x00813c83.
Lemma F_5f50c : fetch_word Asan.M.loaded_segments (0x5f55c : word) = Some W_5f50c.
Proof. vm_refl. Qed.
Lemma D_5f50c : decode_any W_5f50c = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f510 : bv 32 := 0x06010113.
Lemma F_5f510 : fetch_word Asan.M.loaded_segments (0x5f560 : word) = Some W_5f510.
Proof. vm_refl. Qed.
Lemma D_5f510 : decode_any W_5f510 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f514 : bv 32 := 0x00008067.
Lemma F_5f514 : fetch_word Asan.M.loaded_segments (0x5f564 : word) = Some W_5f514.
Proof. vm_refl. Qed.
Lemma D_5f514 : decode_any W_5f514 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f640 : bv 32 := 0x0104b583.
Lemma F_5f640 : fetch_word Asan.M.loaded_segments (0x5f690 : word) = Some W_5f640.
Proof. vm_refl. Qed.
Lemma D_5f640 : decode_any W_5f640 = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f644 : bv 32 := 0x01048713.
Lemma F_5f644 : fetch_word Asan.M.loaded_segments (0x5f694 : word) = Some W_5f644.
Proof. vm_refl. Qed.
Lemma D_5f644 : decode_any W_5f644 = Some (OpImm ALU_ADD 14 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f648 : bv 32 := 0x00369693.
Lemma F_5f648 : fetch_word Asan.M.loaded_segments (0x5f698 : word) = Some W_5f648.
Proof. vm_refl. Qed.
Lemma D_5f648 : decode_any W_5f648 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f64c : bv 32 := 0x00b685b3.
Lemma F_5f64c : fetch_word Asan.M.loaded_segments (0x5f69c : word) = Some W_5f64c.
Proof. vm_refl. Qed.
Lemma D_5f64c : decode_any W_5f64c = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f650 : bv 32 := 0x00020637.
Lemma F_5f650 : fetch_word Asan.M.loaded_segments (0x5f6a0 : word) = Some W_5f650.
Proof. vm_refl. Qed.
Lemma D_5f650 : decode_any W_5f650 = Some (Lui 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f654 : bv 32 := 0x00050a13.
Lemma F_5f654 : fetch_word Asan.M.loaded_segments (0x5f6a4 : word) = Some W_5f654.
Proof. vm_refl. Qed.
Lemma D_5f654 : decode_any W_5f654 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f658 : bv 32 := 0x00070513.
Lemma F_5f658 : fetch_word Asan.M.loaded_segments (0x5f6a8 : word) = Some W_5f658.
Proof. vm_refl. Qed.
Lemma D_5f658 : decode_any W_5f658 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f65c : bv 32 := 0x00000693.
Lemma F_5f65c : fetch_word Asan.M.loaded_segments (0x5f6ac : word) = Some W_5f65c.
Proof. vm_refl. Qed.
Lemma D_5f65c : decode_any W_5f65c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f660 : bv 32 := 0x4153e0ef.
Lemma F_5f660 : fetch_word Asan.M.loaded_segments (0x5f6b0 : word) = Some W_5f660.
Proof. vm_refl. Qed.
Lemma D_5f660 : decode_any W_5f660 = Some (Jal 1 257044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f664 : bv 32 := 0x000a0513.
Lemma F_5f664 : fetch_word Asan.M.loaded_segments (0x5f6b4 : word) = Some W_5f664.
Proof. vm_refl. Qed.
Lemma D_5f664 : decode_any W_5f664 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f668 : bv 32 := 0x0304b583.
Lemma F_5f668 : fetch_word Asan.M.loaded_segments (0x5f6b8 : word) = Some W_5f668.
Proof. vm_refl. Qed.
Lemma D_5f668 : decode_any W_5f668 = Some (Load SZ8 true 11 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f66c : bv 32 := 0x0384b683.
Lemma F_5f66c : fetch_word Asan.M.loaded_segments (0x5f6bc : word) = Some W_5f66c.
Proof. vm_refl. Qed.
Lemma D_5f66c : decode_any W_5f66c = Some (Load SZ8 true 13 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f670 : bv 32 := 0x00004637.
Lemma F_5f670 : fetch_word Asan.M.loaded_segments (0x5f6c0 : word) = Some W_5f670.
Proof. vm_refl. Qed.
Lemma D_5f670 : decode_any W_5f670 = Some (Lui 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f674 : bv 32 := 0x00c585b3.
Lemma F_5f674 : fetch_word Asan.M.loaded_segments (0x5f6c4 : word) = Some W_5f674.
Proof. vm_refl. Qed.
Lemma D_5f674 : decode_any W_5f674 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f678 : bv 32 := 0x02b4b823.
Lemma F_5f678 : fetch_word Asan.M.loaded_segments (0x5f6c8 : word) = Some W_5f678.
Proof. vm_refl. Qed.
Lemma D_5f678 : decode_any W_5f678 = Some (Store SZ8 9 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f67c : bv 32 := 0xdf1ff06f.
Lemma F_5f67c : fetch_word Asan.M.loaded_segments (0x5f6cc : word) = Some W_5f67c.
Proof. vm_refl. Qed.
Lemma D_5f67c : decode_any W_5f67c = Some (Jal 0 2096624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f680 : bv 32 := 0xfe010113.
Lemma F_5f680 : fetch_word Asan.M.loaded_segments (0x5f6d0 : word) = Some W_5f680.
Proof. vm_refl. Qed.
Lemma D_5f680 : decode_any W_5f680 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f684 : bv 32 := 0x00113c23.
Lemma F_5f684 : fetch_word Asan.M.loaded_segments (0x5f6d4 : word) = Some W_5f684.
Proof. vm_refl. Qed.
Lemma D_5f684 : decode_any W_5f684 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f688 : bv 32 := 0x00813823.
Lemma F_5f688 : fetch_word Asan.M.loaded_segments (0x5f6d8 : word) = Some W_5f688.
Proof. vm_refl. Qed.
Lemma D_5f688 : decode_any W_5f688 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f68c : bv 32 := 0x00913423.
Lemma F_5f68c : fetch_word Asan.M.loaded_segments (0x5f6dc : word) = Some W_5f68c.
Proof. vm_refl. Qed.
Lemma D_5f68c : decode_any W_5f68c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f690 : bv 32 := 0x00068713.
Lemma F_5f690 : fetch_word Asan.M.loaded_segments (0x5f6e0 : word) = Some W_5f690.
Proof. vm_refl. Qed.
Lemma D_5f690 : decode_any W_5f690 = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f694 : bv 32 := 0x00058413.
Lemma F_5f694 : fetch_word Asan.M.loaded_segments (0x5f6e4 : word) = Some W_5f694.
Proof. vm_refl. Qed.
Lemma D_5f694 : decode_any W_5f694 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f698 : bv 32 := 0x0045a583.
Lemma F_5f698 : fetch_word Asan.M.loaded_segments (0x5f6e8 : word) = Some W_5f698.
Proof. vm_refl. Qed.
Lemma D_5f698 : decode_any W_5f698 = Some (Load SZ4 true 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f69c : bv 32 := 0x04058063.
Lemma F_5f69c : fetch_word Asan.M.loaded_segments (0x5f6ec : word) = Some W_5f69c.
Proof. vm_refl. Qed.
Lemma D_5f69c : decode_any W_5f69c = Some (Branch BC_EQ 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6a0 : bv 32 := 0x0015d49b.
Lemma F_5f6a0 : fetch_word Asan.M.loaded_segments (0x5f6f0 : word) = Some W_5f6a0.
Proof. vm_refl. Qed.
Lemma D_5f6a0 : decode_any W_5f6a0 = Some (ShiftImm32 ALU_SRL 9 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6a4 : bv 32 := 0x7ff50513.
Lemma F_5f6a4 : fetch_word Asan.M.loaded_segments (0x5f6f4 : word) = Some W_5f6a4.
Proof. vm_refl. Qed.
Lemma D_5f6a4 : decode_any W_5f6a4 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6a8 : bv 32 := 0x20150593.
Lemma F_5f6a8 : fetch_word Asan.M.loaded_segments (0x5f6f8 : word) = Some W_5f6a8.
Proof. vm_refl. Qed.
Lemma D_5f6a8 : decode_any W_5f6a8 = Some (OpImm ALU_ADD 11 10 513, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6ac : bv 32 := 0x01040693.
Lemma F_5f6ac : fetch_word Asan.M.loaded_segments (0x5f6fc : word) = Some W_5f6ac.
Proof. vm_refl. Qed.
Lemma D_5f6ac : decode_any W_5f6ac = Some (OpImm ALU_ADD 13 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6b0 : bv 32 := 0x00060513.
Lemma F_5f6b0 : fetch_word Asan.M.loaded_segments (0x5f700 : word) = Some W_5f6b0.
Proof. vm_refl. Qed.
Lemma D_5f6b0 : decode_any W_5f6b0 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6b4 : bv 32 := 0x00070613.
Lemma F_5f6b4 : fetch_word Asan.M.loaded_segments (0x5f704 : word) = Some W_5f6b4.
Proof. vm_refl. Qed.
Lemma D_5f6b4 : decode_any W_5f6b4 = Some (OpImm ALU_ADD 12 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6b8 : bv 32 := 0x00048713.
Lemma F_5f6b8 : fetch_word Asan.M.loaded_segments (0x5f708 : word) = Some W_5f6b8.
Proof. vm_refl. Qed.
Lemma D_5f6b8 : decode_any W_5f6b8 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6bc : bv 32 := 0x0c4000ef.
Lemma F_5f6bc : fetch_word Asan.M.loaded_segments (0x5f70c : word) = Some W_5f6bc.
Proof. vm_refl. Qed.
Lemma D_5f6bc : decode_any W_5f6bc = Some (Jal 1 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6c0 : bv 32 := 0x00050463.
Lemma F_5f6c0 : fetch_word Asan.M.loaded_segments (0x5f710 : word) = Some W_5f6c0.
Proof. vm_refl. Qed.
Lemma D_5f6c0 : decode_any W_5f6c0 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6c4 : bv 32 := 0x00942023.
Lemma F_5f6c4 : fetch_word Asan.M.loaded_segments (0x5f714 : word) = Some W_5f6c4.
Proof. vm_refl. Qed.
Lemma D_5f6c4 : decode_any W_5f6c4 = Some (Store SZ4 8 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6c8 : bv 32 := 0x01813083.
Lemma F_5f6c8 : fetch_word Asan.M.loaded_segments (0x5f718 : word) = Some W_5f6c8.
Proof. vm_refl. Qed.
Lemma D_5f6c8 : decode_any W_5f6c8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6cc : bv 32 := 0x01013403.
Lemma F_5f6cc : fetch_word Asan.M.loaded_segments (0x5f71c : word) = Some W_5f6cc.
Proof. vm_refl. Qed.
Lemma D_5f6cc : decode_any W_5f6cc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6d0 : bv 32 := 0x00813483.
Lemma F_5f6d0 : fetch_word Asan.M.loaded_segments (0x5f720 : word) = Some W_5f6d0.
Proof. vm_refl. Qed.
Lemma D_5f6d0 : decode_any W_5f6d0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6d4 : bv 32 := 0x02010113.
Lemma F_5f6d4 : fetch_word Asan.M.loaded_segments (0x5f724 : word) = Some W_5f6d4.
Proof. vm_refl. Qed.
Lemma D_5f6d4 : decode_any W_5f6d4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6d8 : bv 32 := 0x00008067.
Lemma F_5f6d8 : fetch_word Asan.M.loaded_segments (0x5f728 : word) = Some W_5f6d8.
Proof. vm_refl. Qed.
Lemma D_5f6d8 : decode_any W_5f6d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6dc : bv 32 := 0x05850593.
Lemma F_5f6dc : fetch_word Asan.M.loaded_segments (0x5f72c : word) = Some W_5f6dc.
Proof. vm_refl. Qed.
Lemma D_5f6dc : decode_any W_5f6dc = Some (OpImm ALU_ADD 11 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6e0 : bv 32 := 0x02000693.
Lemma F_5f6e0 : fetch_word Asan.M.loaded_segments (0x5f730 : word) = Some W_5f6e0.
Proof. vm_refl. Qed.
Lemma D_5f6e0 : decode_any W_5f6e0 = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6e4 : bv 32 := 0xff100793.
Lemma F_5f6e4 : fetch_word Asan.M.loaded_segments (0x5f734 : word) = Some W_5f6e4.
Proof. vm_refl. Qed.
Lemma D_5f6e4 : decode_any W_5f6e4 = Some (OpImm ALU_ADD 15 0 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6e8 : bv 32 := 0x00f00813.
Lemma F_5f6e8 : fetch_word Asan.M.loaded_segments (0x5f738 : word) = Some W_5f6e8.
Proof. vm_refl. Qed.
Lemma D_5f6e8 : decode_any W_5f6e8 = Some (OpImm ALU_ADD 16 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6ec : bv 32 := 0x40000893.
Lemma F_5f6ec : fetch_word Asan.M.loaded_segments (0x5f73c : word) = Some W_5f6ec.
Proof. vm_refl. Qed.
Lemma D_5f6ec : decode_any W_5f6ec = Some (OpImm ALU_ADD 17 0 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6f0 : bv 32 := 0x01000293.
Lemma F_5f6f0 : fetch_word Asan.M.loaded_segments (0x5f740 : word) = Some W_5f6f0.
Proof. vm_refl. Qed.
Lemma D_5f6f0 : decode_any W_5f6f0 = Some (OpImm ALU_ADD 5 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6f4 : bv 32 := 0x01100313.
Lemma F_5f6f4 : fetch_word Asan.M.loaded_segments (0x5f744 : word) = Some W_5f6f4.
Proof. vm_refl. Qed.
Lemma D_5f6f4 : decode_any W_5f6f4 = Some (OpImm ALU_ADD 6 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6f8 : bv 32 := 0x20000393.
Lemma F_5f6f8 : fetch_word Asan.M.loaded_segments (0x5f748 : word) = Some W_5f6f8.
Proof. vm_refl. Qed.
Lemma D_5f6f8 : decode_any W_5f6f8 = Some (OpImm ALU_ADD 7 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f6fc : bv 32 := 0x0280006f.
Lemma F_5f6fc : fetch_word Asan.M.loaded_segments (0x5f74c : word) = Some W_5f6fc.
Proof. vm_refl. Qed.
Lemma D_5f6fc : decode_any W_5f6fc = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f700 : bv 32 := 0x001ebf13.
Lemma F_5f700 : fetch_word Asan.M.loaded_segments (0x5f750 : word) = Some W_5f700.
Proof. vm_refl. Qed.
Lemma D_5f700 : decode_any W_5f700 = Some (OpImm ALU_SLTU 30 29 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f704 : bv 32 := 0x02068693.
Lemma F_5f704 : fetch_word Asan.M.loaded_segments (0x5f754 : word) = Some W_5f704.
Proof. vm_refl. Qed.
Lemma D_5f704 : decode_any W_5f704 = Some (OpImm ALU_ADD 13 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f708 : bv 32 := 0x00178793.
Lemma F_5f708 : fetch_word Asan.M.loaded_segments (0x5f758 : word) = Some W_5f708.
Proof. vm_refl. Qed.
Lemma D_5f708 : decode_any W_5f708 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f70c : bv 32 := 0x01ee8eb3.
Lemma F_5f70c : fetch_word Asan.M.loaded_segments (0x5f75c : word) = Some W_5f70c.
Proof. vm_refl. Qed.
Lemma D_5f70c : decode_any W_5f70c = Some (Op ALU_ADD 29 29 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f710 : bv 32 := 0x001e9e93.
Lemma F_5f710 : fetch_word Asan.M.loaded_segments (0x5f760 : word) = Some W_5f710.
Proof. vm_refl. Qed.
Lemma D_5f710 : decode_any W_5f710 = Some (ShiftImm ALU_SLL 29 29 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f714 : bv 32 := 0xffd5ae23.
Lemma F_5f714 : fetch_word Asan.M.loaded_segments (0x5f764 : word) = Some W_5f714.
Proof. vm_refl. Qed.
Lemma D_5f714 : decode_any W_5f714 = Some (Store SZ4 11 29 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f718 : bv 32 := 0x01c5b023.
Lemma F_5f718 : fetch_word Asan.M.loaded_segments (0x5f768 : word) = Some W_5f718.
Proof. vm_refl. Qed.
Lemma D_5f718 : decode_any W_5f718 = Some (Store SZ8 11 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f71c : bv 32 := 0x05058593.
Lemma F_5f71c : fetch_word Asan.M.loaded_segments (0x5f76c : word) = Some W_5f71c.
Proof. vm_refl. Qed.
Lemma D_5f71c : decode_any W_5f71c = Some (OpImm ALU_ADD 11 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f720 : bv 32 := 0x04578c63.
Lemma F_5f720 : fetch_word Asan.M.loaded_segments (0x5f770 : word) = Some W_5f720.
Proof. vm_refl. Qed.
Lemma D_5f720 : decode_any W_5f720 = Some (Branch BC_EQ 15 5 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f724 : bv 32 := 0x05078063.
Lemma F_5f724 : fetch_word Asan.M.loaded_segments (0x5f774 : word) = Some W_5f724.
Proof. vm_refl. Qed.
Lemma D_5f724 : decode_any W_5f724 = Some (Branch BC_EQ 15 16 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f728 : bv 32 := 0x01078e93.
Lemma F_5f728 : fetch_word Asan.M.loaded_segments (0x5f778 : word) = Some W_5f728.
Proof. vm_refl. Qed.
Lemma D_5f728 : decode_any W_5f728 = Some (OpImm ALU_ADD 29 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f72c : bv 32 := 0x00068e13.
Lemma F_5f72c : fetch_word Asan.M.loaded_segments (0x5f77c : word) = Some W_5f72c.
Proof. vm_refl. Qed.
Lemma D_5f72c : decode_any W_5f72c = Some (OpImm ALU_ADD 28 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f730 : bv 32 := 0x026ee063.
Lemma F_5f730 : fetch_word Asan.M.loaded_segments (0x5f780 : word) = Some W_5f730.
Proof. vm_refl. Qed.
Lemma D_5f730 : decode_any W_5f730 = Some (Branch BC_LTU 29 6 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f734 : bv 32 := 0x0017de13.
Lemma F_5f734 : fetch_word Asan.M.loaded_segments (0x5f784 : word) = Some W_5f734.
Proof. vm_refl. Qed.
Lemma D_5f734 : decode_any W_5f734 = Some (ShiftImm ALU_SRL 28 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f738 : bv 32 := 0x03fe9e93.
Lemma F_5f738 : fetch_word Asan.M.loaded_segments (0x5f788 : word) = Some W_5f738.
Proof. vm_refl. Qed.
Lemma D_5f738 : decode_any W_5f738 = Some (ShiftImm ALU_SLL 29 29 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f73c : bv 32 := 0x01c39e33.
Lemma F_5f73c : fetch_word Asan.M.loaded_segments (0x5f78c : word) = Some W_5f73c.
Proof. vm_refl. Qed.
Lemma D_5f73c : decode_any W_5f73c = Some (Op ALU_SLL 28 7 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f740 : bv 32 := 0x001e5f13.
Lemma F_5f740 : fetch_word Asan.M.loaded_segments (0x5f790 : word) = Some W_5f740.
Proof. vm_refl. Qed.
Lemma D_5f740 : decode_any W_5f740 = Some (ShiftImm ALU_SRL 30 28 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f744 : bv 32 := 0x43fede93.
Lemma F_5f744 : fetch_word Asan.M.loaded_segments (0x5f794 : word) = Some W_5f744.
Proof. vm_refl. Qed.
Lemma D_5f744 : decode_any W_5f744 = Some (ShiftImm ALU_SRA 29 29 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f748 : bv 32 := 0x01eefeb3.
Lemma F_5f748 : fetch_word Asan.M.loaded_segments (0x5f798 : word) = Some W_5f748.
Proof. vm_refl. Qed.
Lemma D_5f748 : decode_any W_5f748 = Some (Op ALU_AND 29 29 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f74c : bv 32 := 0x01ce8e33.
Lemma F_5f74c : fetch_word Asan.M.loaded_segments (0x5f79c : word) = Some W_5f74c.
Proof. vm_refl. Qed.
Lemma D_5f74c : decode_any W_5f74c = Some (Op ALU_ADD 28 29 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f750 : bv 32 := 0x03c8debb.
Lemma F_5f750 : fetch_word Asan.M.loaded_segments (0x5f7a0 : word) = Some W_5f750.
Proof. vm_refl. Qed.
Lemma D_5f750 : decode_any W_5f750 = Some (Mul32 M_DIVU 29 17 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f754 : bv 32 := 0x00800f13.
Lemma F_5f754 : fetch_word Asan.M.loaded_segments (0x5f7a4 : word) = Some W_5f754.
Proof. vm_refl. Qed.
Lemma D_5f754 : decode_any W_5f754 = Some (OpImm ALU_ADD 30 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f758 : bv 32 := 0xfbeee4e3.
Lemma F_5f758 : fetch_word Asan.M.loaded_segments (0x5f7a8 : word) = Some W_5f758.
Proof. vm_refl. Qed.
Lemma D_5f758 : decode_any W_5f758 = Some (Branch BC_LTU 29 30 8104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f75c : bv 32 := 0x00800e93.
Lemma F_5f75c : fetch_word Asan.M.loaded_segments (0x5f7ac : word) = Some W_5f75c.
Proof. vm_refl. Qed.
Lemma D_5f75c : decode_any W_5f75c = Some (OpImm ALU_ADD 29 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f760 : bv 32 := 0xfa1ff06f.
Lemma F_5f760 : fetch_word Asan.M.loaded_segments (0x5f7b0 : word) = Some W_5f760.
Proof. vm_refl. Qed.
Lemma D_5f760 : decode_any W_5f760 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f764 : bv 32 := 0x04000e13.
Lemma F_5f764 : fetch_word Asan.M.loaded_segments (0x5f7b4 : word) = Some W_5f764.
Proof. vm_refl. Qed.
Lemma D_5f764 : decode_any W_5f764 = Some (OpImm ALU_ADD 28 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f768 : bv 32 := 0x03c8debb.
Lemma F_5f768 : fetch_word Asan.M.loaded_segments (0x5f7b8 : word) = Some W_5f768.
Proof. vm_refl. Qed.
Lemma D_5f768 : decode_any W_5f768 = Some (Mul32 M_DIVU 29 17 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f76c : bv 32 := 0x00800f13.
Lemma F_5f76c : fetch_word Asan.M.loaded_segments (0x5f7bc : word) = Some W_5f76c.
Proof. vm_refl. Qed.
Lemma D_5f76c : decode_any W_5f76c = Some (OpImm ALU_ADD 30 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f770 : bv 32 := 0xf9eee8e3.
Lemma F_5f770 : fetch_word Asan.M.loaded_segments (0x5f7c0 : word) = Some W_5f770.
Proof. vm_refl. Qed.
Lemma D_5f770 : decode_any W_5f770 = Some (Branch BC_LTU 29 30 8080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f774 : bv 32 := 0xfe9ff06f.
Lemma F_5f774 : fetch_word Asan.M.loaded_segments (0x5f7c4 : word) = Some W_5f774.
Proof. vm_refl. Qed.
Lemma D_5f774 : decode_any W_5f774 = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f778 : bv 32 := 0x00442583.
Lemma F_5f778 : fetch_word Asan.M.loaded_segments (0x5f7c8 : word) = Some W_5f778.
Proof. vm_refl. Qed.
Lemma D_5f778 : decode_any W_5f778 = Some (Load SZ4 true 11 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f77c : bv 32 := 0xf25ff06f.
Lemma F_5f77c : fetch_word Asan.M.loaded_segments (0x5f7cc : word) = Some W_5f77c.
Proof. vm_refl. Qed.
Lemma D_5f77c : decode_any W_5f77c = Some (Jal 0 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f780 : bv 32 := 0xf8010113.
Lemma F_5f780 : fetch_word Asan.M.loaded_segments (0x5f7d0 : word) = Some W_5f780.
Proof. vm_refl. Qed.
Lemma D_5f780 : decode_any W_5f780 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f784 : bv 32 := 0x06113c23.
Lemma F_5f784 : fetch_word Asan.M.loaded_segments (0x5f7d4 : word) = Some W_5f784.
Proof. vm_refl. Qed.
Lemma D_5f784 : decode_any W_5f784 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f788 : bv 32 := 0x06813823.
Lemma F_5f788 : fetch_word Asan.M.loaded_segments (0x5f7d8 : word) = Some W_5f788.
Proof. vm_refl. Qed.
Lemma D_5f788 : decode_any W_5f788 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f78c : bv 32 := 0x06913423.
Lemma F_5f78c : fetch_word Asan.M.loaded_segments (0x5f7dc : word) = Some W_5f78c.
Proof. vm_refl. Qed.
Lemma D_5f78c : decode_any W_5f78c = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f790 : bv 32 := 0x07213023.
Lemma F_5f790 : fetch_word Asan.M.loaded_segments (0x5f7e0 : word) = Some W_5f790.
Proof. vm_refl. Qed.
Lemma D_5f790 : decode_any W_5f790 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f794 : bv 32 := 0x05313c23.
Lemma F_5f794 : fetch_word Asan.M.loaded_segments (0x5f7e4 : word) = Some W_5f794.
Proof. vm_refl. Qed.
Lemma D_5f794 : decode_any W_5f794 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f798 : bv 32 := 0x05413823.
Lemma F_5f798 : fetch_word Asan.M.loaded_segments (0x5f7e8 : word) = Some W_5f798.
Proof. vm_refl. Qed.
Lemma D_5f798 : decode_any W_5f798 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f79c : bv 32 := 0x05513423.
Lemma F_5f79c : fetch_word Asan.M.loaded_segments (0x5f7ec : word) = Some W_5f79c.
Proof. vm_refl. Qed.
Lemma D_5f79c : decode_any W_5f79c = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7a0 : bv 32 := 0x05613023.
Lemma F_5f7a0 : fetch_word Asan.M.loaded_segments (0x5f7f0 : word) = Some W_5f7a0.
Proof. vm_refl. Qed.
Lemma D_5f7a0 : decode_any W_5f7a0 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7a4 : bv 32 := 0x03713c23.
Lemma F_5f7a4 : fetch_word Asan.M.loaded_segments (0x5f7f4 : word) = Some W_5f7a4.
Proof. vm_refl. Qed.
Lemma D_5f7a4 : decode_any W_5f7a4 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7a8 : bv 32 := 0x03813823.
Lemma F_5f7a8 : fetch_word Asan.M.loaded_segments (0x5f7f8 : word) = Some W_5f7a8.
Proof. vm_refl. Qed.
Lemma D_5f7a8 : decode_any W_5f7a8 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7ac : bv 32 := 0x03913423.
Lemma F_5f7ac : fetch_word Asan.M.loaded_segments (0x5f7fc : word) = Some W_5f7ac.
Proof. vm_refl. Qed.
Lemma D_5f7ac : decode_any W_5f7ac = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7b0 : bv 32 := 0x03a13023.
Lemma F_5f7b0 : fetch_word Asan.M.loaded_segments (0x5f800 : word) = Some W_5f7b0.
Proof. vm_refl. Qed.
Lemma D_5f7b0 : decode_any W_5f7b0 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7b4 : bv 32 := 0x01b13c23.
Lemma F_5f7b4 : fetch_word Asan.M.loaded_segments (0x5f804 : word) = Some W_5f7b4.
Proof. vm_refl. Qed.
Lemma D_5f7b4 : decode_any W_5f7b4 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7b8 : bv 32 := 0x00050493.
Lemma F_5f7b8 : fetch_word Asan.M.loaded_segments (0x5f808 : word) = Some W_5f7b8.
Proof. vm_refl. Qed.
Lemma D_5f7b8 : decode_any W_5f7b8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7bc : bv 32 := 0x00000793.
Lemma F_5f7bc : fetch_word Asan.M.loaded_segments (0x5f80c : word) = Some W_5f7bc.
Proof. vm_refl. Qed.
Lemma D_5f7bc : decode_any W_5f7bc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7c0 : bv 32 := 0x00100b93.
Lemma F_5f7c0 : fetch_word Asan.M.loaded_segments (0x5f810 : word) = Some W_5f7c0.
Proof. vm_refl. Qed.
Lemma D_5f7c0 : decode_any W_5f7c0 = Some (OpImm ALU_ADD 23 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7c4 : bv 32 := 0x02053a03.
Lemma F_5f7c4 : fetch_word Asan.M.loaded_segments (0x5f814 : word) = Some W_5f7c4.
Proof. vm_refl. Qed.
Lemma D_5f7c4 : decode_any W_5f7c4 = Some (Load SZ8 true 20 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7c8 : bv 32 := 0x03053403.
Lemma F_5f7c8 : fetch_word Asan.M.loaded_segments (0x5f818 : word) = Some W_5f7c8.
Proof. vm_refl. Qed.
Lemma D_5f7c8 : decode_any W_5f7c8 = Some (Load SZ8 true 8 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7cc : bv 32 := 0x00761513.
Lemma F_5f7cc : fetch_word Asan.M.loaded_segments (0x5f81c : word) = Some W_5f7cc.
Proof. vm_refl. Qed.
Lemma D_5f7cc : decode_any W_5f7cc = Some (ShiftImm ALU_SLL 10 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7d0 : bv 32 := 0x02061893.
Lemma F_5f7d0 : fetch_word Asan.M.loaded_segments (0x5f820 : word) = Some W_5f7d0.
Proof. vm_refl. Qed.
Lemma D_5f7d0 : decode_any W_5f7d0 = Some (ShiftImm ALU_SLL 17 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7d4 : bv 32 := 0x00700293.
Lemma F_5f7d4 : fetch_word Asan.M.loaded_segments (0x5f824 : word) = Some W_5f7d4.
Proof. vm_refl. Qed.
Lemma D_5f7d4 : decode_any W_5f7d4 = Some (OpImm ALU_ADD 5 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7d8 : bv 32 := 0xfff00813.
Lemma F_5f7d8 : fetch_word Asan.M.loaded_segments (0x5f828 : word) = Some W_5f7d8.
Proof. vm_refl. Qed.
Lemma D_5f7d8 : decode_any W_5f7d8 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7dc : bv 32 := 0x03db9993.
Lemma F_5f7dc : fetch_word Asan.M.loaded_segments (0x5f82c : word) = Some W_5f7dc.
Proof. vm_refl. Qed.
Lemma D_5f7dc : decode_any W_5f7dc = Some (ShiftImm ALU_SLL 19 23 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7e0 : bv 32 := 0x01d29293.
Lemma F_5f7e0 : fetch_word Asan.M.loaded_segments (0x5f830 : word) = Some W_5f7e0.
Proof. vm_refl. Qed.
Lemma D_5f7e0 : decode_any W_5f7e0 = Some (ShiftImm ALU_SLL 5 5 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7e4 : bv 32 := 0x028b9a93.
Lemma F_5f7e4 : fetch_word Asan.M.loaded_segments (0x5f834 : word) = Some W_5f7e4.
Proof. vm_refl. Qed.
Lemma D_5f7e4 : decode_any W_5f7e4 = Some (ShiftImm ALU_SLL 21 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7e8 : bv 32 := 0x005888b3.
Lemma F_5f7e8 : fetch_word Asan.M.loaded_segments (0x5f838 : word) = Some W_5f7e8.
Proof. vm_refl. Qed.
Lemma D_5f7e8 : decode_any W_5f7e8 = Some (Op ALU_ADD 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7ec : bv 32 := 0x001a8293.
Lemma F_5f7ec : fetch_word Asan.M.loaded_segments (0x5f83c : word) = Some W_5f7ec.
Proof. vm_refl. Qed.
Lemma D_5f7ec : decode_any W_5f7ec = Some (OpImm ALU_ADD 5 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7f0 : bv 32 := 0x01429293.
Lemma F_5f7f0 : fetch_word Asan.M.loaded_segments (0x5f840 : word) = Some W_5f7f0.
Proof. vm_refl. Qed.
Lemma D_5f7f0 : decode_any W_5f7f0 = Some (ShiftImm ALU_SLL 5 5 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7f4 : bv 32 := 0x00a40433.
Lemma F_5f7f4 : fetch_word Asan.M.loaded_segments (0x5f844 : word) = Some W_5f7f4.
Proof. vm_refl. Qed.
Lemma D_5f7f4 : decode_any W_5f7f4 = Some (Op ALU_ADD 8 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7f8 : bv 32 := 0x011a0a33.
Lemma F_5f7f8 : fetch_word Asan.M.loaded_segments (0x5f848 : word) = Some W_5f7f8.
Proof. vm_refl. Qed.
Lemma D_5f7f8 : decode_any W_5f7f8 = Some (Op ALU_ADD 20 20 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f7fc : bv 32 := 0xfff28b13.
Lemma F_5f7fc : fetch_word Asan.M.loaded_segments (0x5f84c : word) = Some W_5f7fc.
Proof. vm_refl. Qed.
Lemma D_5f7fc : decode_any W_5f7fc = Some (OpImm ALU_ADD 22 5 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f800 : bv 32 := 0x00043883.
Lemma F_5f800 : fetch_word Asan.M.loaded_segments (0x5f850 : word) = Some W_5f800.
Proof. vm_refl. Qed.
Lemma D_5f800 : decode_any W_5f800 = Some (Load SZ8 true 17 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f804 : bv 32 := 0x00840513.
Lemma F_5f804 : fetch_word Asan.M.loaded_segments (0x5f854 : word) = Some W_5f804.
Proof. vm_refl. Qed.
Lemma D_5f804 : decode_any W_5f804 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f808 : bv 32 := 0x03cb9b93.
Lemma F_5f808 : fetch_word Asan.M.loaded_segments (0x5f858 : word) = Some W_5f808.
Proof. vm_refl. Qed.
Lemma D_5f808 : decode_any W_5f808 = Some (ShiftImm ALU_SLL 23 23 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f80c : bv 32 := 0x5dc00c13.
Lemma F_5f80c : fetch_word Asan.M.loaded_segments (0x5f85c : word) = Some W_5f80c.
Proof. vm_refl. Qed.
Lemma D_5f80c : decode_any W_5f80c = Some (OpImm ALU_ADD 24 0 1500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f810 : bv 32 := 0x03d81c93.
Lemma F_5f810 : fetch_word Asan.M.loaded_segments (0x5f860 : word) = Some W_5f810.
Proof. vm_refl. Qed.
Lemma D_5f810 : decode_any W_5f810 = Some (ShiftImm ALU_SLL 25 16 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f814 : bv 32 := 0xfffc8c93.
Lemma F_5f814 : fetch_word Asan.M.loaded_segments (0x5f864 : word) = Some W_5f814.
Proof. vm_refl. Qed.
Lemma D_5f814 : decode_any W_5f814 = Some (OpImm ALU_ADD 25 25 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f818 : bv 32 := 0x0168f2b3.
Lemma F_5f818 : fetch_word Asan.M.loaded_segments (0x5f868 : word) = Some W_5f818.
Proof. vm_refl. Qed.
Lemma D_5f818 : decode_any W_5f818 = Some (Op ALU_AND 5 17 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f81c : bv 32 := 0x02029663.
Lemma F_5f81c : fetch_word Asan.M.loaded_segments (0x5f86c : word) = Some W_5f81c.
Proof. vm_refl. Qed.
Lemma D_5f81c : decode_any W_5f81c = Some (Branch BC_NE 5 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f820 : bv 32 := 0x0178e2b3.
Lemma F_5f820 : fetch_word Asan.M.loaded_segments (0x5f870 : word) = Some W_5f820.
Proof. vm_refl. Qed.
Lemma D_5f820 : decode_any W_5f820 = Some (Op ALU_OR 5 17 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f824 : bv 32 := 0x00587333.
Lemma F_5f824 : fetch_word Asan.M.loaded_segments (0x5f874 : word) = Some W_5f824.
Proof. vm_refl. Qed.
Lemma D_5f824 : decode_any W_5f824 = Some (Op ALU_AND 6 16 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f828 : bv 32 := 0x160432af.
Lemma F_5f828 : fetch_word Asan.M.loaded_segments (0x5f878 : word) = Some W_5f828.
Proof. vm_refl. Qed.
Lemma D_5f828 : decode_any W_5f828 = Some (Lr AD true true 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f82c : bv 32 := 0x01129663.
Lemma F_5f82c : fetch_word Asan.M.loaded_segments (0x5f87c : word) = Some W_5f82c.
Proof. vm_refl. Qed.
Lemma D_5f82c : decode_any W_5f82c = Some (Branch BC_NE 5 17 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f830 : bv 32 := 0x1a6433af.
Lemma F_5f830 : fetch_word Asan.M.loaded_segments (0x5f880 : word) = Some W_5f830.
Proof. vm_refl. Qed.
Lemma D_5f830 : decode_any W_5f830 = Some (Sc AD false true 7 8 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f834 : bv 32 := 0xfe039ae3.
Lemma F_5f834 : fetch_word Asan.M.loaded_segments (0x5f884 : word) = Some W_5f834.
Proof. vm_refl. Qed.
Lemma D_5f834 : decode_any W_5f834 = Some (Branch BC_NE 7 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f838 : bv 32 := 0x09128c63.
Lemma F_5f838 : fetch_word Asan.M.loaded_segments (0x5f888 : word) = Some W_5f838.
Proof. vm_refl. Qed.
Lemma D_5f838 : decode_any W_5f838 = Some (Branch BC_EQ 5 17 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8d0 : bv 32 := 0x01043783.
Lemma F_5f8d0 : fetch_word Asan.M.loaded_segments (0x5f920 : word) = Some W_5f8d0.
Proof. vm_refl. Qed.
Lemma D_5f8d0 : decode_any W_5f8d0 = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8d4 : bv 32 := 0x14e7e663.
Lemma F_5f8d4 : fetch_word Asan.M.loaded_segments (0x5f924 : word) = Some W_5f8d4.
Proof. vm_refl. Qed.
Lemma D_5f8d4 : decode_any W_5f8d4 = Some (Branch BC_LTU 15 14 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8d8 : bv 32 := 0x40e787b3.
Lemma F_5f8d8 : fetch_word Asan.M.loaded_segments (0x5f928 : word) = Some W_5f8d8.
Proof. vm_refl. Qed.
Lemma D_5f8d8 : decode_any W_5f8d8 = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8dc : bv 32 := 0x00f43823.
Lemma F_5f8dc : fetch_word Asan.M.loaded_segments (0x5f92c : word) = Some W_5f8dc.
Proof. vm_refl. Qed.
Lemma D_5f8dc : decode_any W_5f8dc = Some (Store SZ8 8 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8e0 : bv 32 := 0x02070463.
Lemma F_5f8e0 : fetch_word Asan.M.loaded_segments (0x5f930 : word) = Some W_5f8e0.
Proof. vm_refl. Qed.
Lemma D_5f8e0 : decode_any W_5f8e0 = Some (Branch BC_EQ 14 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8e4 : bv 32 := 0x00279793.
Lemma F_5f8e4 : fetch_word Asan.M.loaded_segments (0x5f934 : word) = Some W_5f8e4.
Proof. vm_refl. Qed.
Lemma D_5f8e4 : decode_any W_5f8e4 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8e8 : bv 32 := 0x00fa0a33.
Lemma F_5f8e8 : fetch_word Asan.M.loaded_segments (0x5f938 : word) = Some W_5f8e8.
Proof. vm_refl. Qed.
Lemma D_5f8e8 : decode_any W_5f8e8 = Some (Op ALU_ADD 20 20 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8ec : bv 32 := 0x00271593.
Lemma F_5f8ec : fetch_word Asan.M.loaded_segments (0x5f93c : word) = Some W_5f8ec.
Proof. vm_refl. Qed.
Lemma D_5f8ec : decode_any W_5f8ec = Some (ShiftImm ALU_SLL 11 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8f0 : bv 32 := 0x00b685b3.
Lemma F_5f8f0 : fetch_word Asan.M.loaded_segments (0x5f940 : word) = Some W_5f8f0.
Proof. vm_refl. Qed.
Lemma D_5f8f0 : decode_any W_5f8f0 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8f4 : bv 32 := 0x000a2603.
Lemma F_5f8f4 : fetch_word Asan.M.loaded_segments (0x5f944 : word) = Some W_5f8f4.
Proof. vm_refl. Qed.
Lemma D_5f8f4 : decode_any W_5f8f4 = Some (Load SZ4 true 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8f8 : bv 32 := 0x00c6a023.
Lemma F_5f8f8 : fetch_word Asan.M.loaded_segments (0x5f948 : word) = Some W_5f8f8.
Proof. vm_refl. Qed.
Lemma D_5f8f8 : decode_any W_5f8f8 = Some (Store SZ4 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f8fc : bv 32 := 0x00468693.
Lemma F_5f8fc : fetch_word Asan.M.loaded_segments (0x5f94c : word) = Some W_5f8fc.
Proof. vm_refl. Qed.
Lemma D_5f8fc : decode_any W_5f8fc = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f900 : bv 32 := 0x004a0a13.
Lemma F_5f900 : fetch_word Asan.M.loaded_segments (0x5f950 : word) = Some W_5f900.
Proof. vm_refl. Qed.
Lemma D_5f900 : decode_any W_5f900 = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f904 : bv 32 := 0xfeb698e3.
Lemma F_5f904 : fetch_word Asan.M.loaded_segments (0x5f954 : word) = Some W_5f904.
Proof. vm_refl. Qed.
Lemma D_5f904 : decode_any W_5f904 = Some (Branch BC_NE 13 11 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f908 : bv 32 := 0x04843583.
Lemma F_5f908 : fetch_word Asan.M.loaded_segments (0x5f958 : word) = Some W_5f908.
Proof. vm_refl. Qed.
Lemma D_5f908 : decode_any W_5f908 = Some (Load SZ8 true 11 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f90c : bv 32 := 0x00e585b3.
Lemma F_5f90c : fetch_word Asan.M.loaded_segments (0x5f95c : word) = Some W_5f90c.
Proof. vm_refl. Qed.
Lemma D_5f90c : decode_any W_5f90c = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f910 : bv 32 := 0x04b43423.
Lemma F_5f910 : fetch_word Asan.M.loaded_segments (0x5f960 : word) = Some W_5f910.
Proof. vm_refl. Qed.
Lemma D_5f910 : decode_any W_5f910 = Some (Store SZ8 8 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f914 : bv 32 := 0x00100493.
Lemma F_5f914 : fetch_word Asan.M.loaded_segments (0x5f964 : word) = Some W_5f914.
Proof. vm_refl. Qed.
Lemma D_5f914 : decode_any W_5f914 = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f918 : bv 32 := 0x00043603.
Lemma F_5f918 : fetch_word Asan.M.loaded_segments (0x5f968 : word) = Some W_5f918.
Proof. vm_refl. Qed.
Lemma D_5f918 : decode_any W_5f918 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f91c : bv 32 := 0xfff00893.
Lemma F_5f91c : fetch_word Asan.M.loaded_segments (0x5f96c : word) = Some W_5f91c.
Proof. vm_refl. Qed.
Lemma D_5f91c : decode_any W_5f91c = Some (OpImm ALU_ADD 17 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f920 : bv 32 := 0x00300693.
Lemma F_5f920 : fetch_word Asan.M.loaded_segments (0x5f970 : word) = Some W_5f920.
Proof. vm_refl. Qed.
Lemma D_5f920 : decode_any W_5f920 = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f924 : bv 32 := 0x001005b7.
Lemma F_5f924 : fetch_word Asan.M.loaded_segments (0x5f974 : word) = Some W_5f924.
Proof. vm_refl. Qed.
Lemma D_5f924 : decode_any W_5f924 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f928 : bv 32 := 0xfffb1717.
Lemma F_5f928 : fetch_word Asan.M.loaded_segments (0x5f978 : word) = Some W_5f928.
Proof. vm_refl. Qed.
Lemma D_5f928 : decode_any W_5f928 = Some (Auipc 14 1048497, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f92c : bv 32 := 0x03c89793.
Lemma F_5f92c : fetch_word Asan.M.loaded_segments (0x5f97c : word) = Some W_5f92c.
Proof. vm_refl. Qed.
Lemma D_5f92c : decode_any W_5f92c = Some (ShiftImm ALU_SLL 15 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f930 : bv 32 := 0x03d69693.
Lemma F_5f930 : fetch_word Asan.M.loaded_segments (0x5f980 : word) = Some W_5f930.
Proof. vm_refl. Qed.
Lemma D_5f930 : decode_any W_5f930 = Some (ShiftImm ALU_SLL 13 13 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f934 : bv 32 := 0xfff58593.
Lemma F_5f934 : fetch_word Asan.M.loaded_segments (0x5f984 : word) = Some W_5f934.
Proof. vm_refl. Qed.
Lemma D_5f934 : decode_any W_5f934 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f938 : bv 32 := 0xac873703.
Lemma F_5f938 : fetch_word Asan.M.loaded_segments (0x5f988 : word) = Some W_5f938.
Proof. vm_refl. Qed.
Lemma D_5f938 : decode_any W_5f938 = Some (Load SZ8 true 14 14 2760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f93c : bv 32 := 0xfff78793.
Lemma F_5f93c : fetch_word Asan.M.loaded_segments (0x5f98c : word) = Some W_5f93c.
Proof. vm_refl. Qed.
Lemma D_5f93c : decode_any W_5f93c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f940 : bv 32 := 0x02859813.
Lemma F_5f940 : fetch_word Asan.M.loaded_segments (0x5f990 : word) = Some W_5f940.
Proof. vm_refl. Qed.
Lemma D_5f940 : decode_any W_5f940 = Some (ShiftImm ALU_SLL 16 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f944 : bv 32 := 0x02889893.
Lemma F_5f944 : fetch_word Asan.M.loaded_segments (0x5f994 : word) = Some W_5f944.
Proof. vm_refl. Qed.
Lemma D_5f944 : decode_any W_5f944 = Some (ShiftImm ALU_SLL 17 17 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f948 : bv 32 := 0x00100293.
Lemma F_5f948 : fetch_word Asan.M.loaded_segments (0x5f998 : word) = Some W_5f948.
Proof. vm_refl. Qed.
Lemma D_5f948 : decode_any W_5f948 = Some (OpImm ALU_ADD 5 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f94c : bv 32 := 0x03e29293.
Lemma F_5f94c : fetch_word Asan.M.loaded_segments (0x5f99c : word) = Some W_5f94c.
Proof. vm_refl. Qed.
Lemma D_5f94c : decode_any W_5f94c = Some (ShiftImm ALU_SLL 5 5 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f950 : bv 32 := 0x01c0006f.
Lemma F_5f950 : fetch_word Asan.M.loaded_segments (0x5f9a0 : word) = Some W_5f950.
Proof. vm_refl. Qed.
Lemma D_5f950 : decode_any W_5f950 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f954 : bv 32 := 0x160433af.
Lemma F_5f954 : fetch_word Asan.M.loaded_segments (0x5f9a4 : word) = Some W_5f954.
Proof. vm_refl. Qed.
Lemma D_5f954 : decode_any W_5f954 = Some (Lr AD true true 7 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f958 : bv 32 := 0x00c39663.
Lemma F_5f958 : fetch_word Asan.M.loaded_segments (0x5f9a8 : word) = Some W_5f958.
Proof. vm_refl. Qed.
Lemma D_5f958 : decode_any W_5f958 = Some (Branch BC_NE 7 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f95c : bv 32 := 0x1a643e2f.
Lemma F_5f95c : fetch_word Asan.M.loaded_segments (0x5f9ac : word) = Some W_5f95c.
Proof. vm_refl. Qed.
Lemma D_5f95c : decode_any W_5f95c = Some (Sc AD false true 28 8 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f960 : bv 32 := 0xfe0e1ae3.
Lemma F_5f960 : fetch_word Asan.M.loaded_segments (0x5f9b0 : word) = Some W_5f960.
Proof. vm_refl. Qed.
Lemma D_5f960 : decode_any W_5f960 = Some (Branch BC_NE 28 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f964 : bv 32 := 0x06c38463.
Lemma F_5f964 : fetch_word Asan.M.loaded_segments (0x5f9b4 : word) = Some W_5f964.
Proof. vm_refl. Qed.
Lemma D_5f964 : decode_any W_5f964 = Some (Branch BC_EQ 7 12 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f96c : bv 32 := 0x00d675b3.
Lemma F_5f96c : fetch_word Asan.M.loaded_segments (0x5f9bc : word) = Some W_5f96c.
Proof. vm_refl. Qed.
Lemma D_5f96c : decode_any W_5f96c = Some (Op ALU_AND 11 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f970 : bv 32 := 0x00f67333.
Lemma F_5f970 : fetch_word Asan.M.loaded_segments (0x5f9c0 : word) = Some W_5f970.
Proof. vm_refl. Qed.
Lemma D_5f970 : decode_any W_5f970 = Some (Op ALU_AND 6 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f974 : bv 32 := 0x02059663.
Lemma F_5f974 : fetch_word Asan.M.loaded_segments (0x5f9c4 : word) = Some W_5f974.
Proof. vm_refl. Qed.
Lemma D_5f974 : decode_any W_5f974 = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f978 : bv 32 := 0x010675b3.
Lemma F_5f978 : fetch_word Asan.M.loaded_segments (0x5f9c8 : word) = Some W_5f978.
Proof. vm_refl. Qed.
Lemma D_5f978 : decode_any W_5f978 = Some (Op ALU_AND 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f97c : bv 32 := 0x02058263.
Lemma F_5f97c : fetch_word Asan.M.loaded_segments (0x5f9cc : word) = Some W_5f97c.
Proof. vm_refl. Qed.
Lemma D_5f97c : decode_any W_5f97c = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9a0 : bv 32 := 0x013675b3.
Lemma F_5f9a0 : fetch_word Asan.M.loaded_segments (0x5f9f0 : word) = Some W_5f9a0.
Proof. vm_refl. Qed.
Lemma D_5f9a0 : decode_any W_5f9a0 = Some (Op ALU_AND 11 12 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9a4 : bv 32 := 0x00b035b3.
Lemma F_5f9a4 : fetch_word Asan.M.loaded_segments (0x5f9f4 : word) = Some W_5f9a4.
Proof. vm_refl. Qed.
Lemma D_5f9a4 : decode_any W_5f9a4 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9a8 : bv 32 := 0x01465393.
Lemma F_5f9a8 : fetch_word Asan.M.loaded_segments (0x5f9f8 : word) = Some W_5f9a8.
Proof. vm_refl. Qed.
Lemma D_5f9a8 : decode_any W_5f9a8 = Some (ShiftImm ALU_SRL 7 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9ac : bv 32 := 0xfff58593.
Lemma F_5f9ac : fetch_word Asan.M.loaded_segments (0x5f9fc : word) = Some W_5f9ac.
Proof. vm_refl. Qed.
Lemma D_5f9ac : decode_any W_5f9ac = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9b0 : bv 32 := 0x00b3f5b3.
Lemma F_5f9b0 : fetch_word Asan.M.loaded_segments (0x5fa00 : word) = Some W_5f9b0.
Proof. vm_refl. Qed.
Lemma D_5f9b0 : decode_any W_5f9b0 = Some (Op ALU_AND 11 7 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9b4 : bv 32 := 0x02c59593.
Lemma F_5f9b4 : fetch_word Asan.M.loaded_segments (0x5fa04 : word) = Some W_5f9b4.
Proof. vm_refl. Qed.
Lemma D_5f9b4 : decode_any W_5f9b4 = Some (ShiftImm ALU_SLL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9b8 : bv 32 := 0x02c5d593.
Lemma F_5f9b8 : fetch_word Asan.M.loaded_segments (0x5fa08 : word) = Some W_5f9b8.
Proof. vm_refl. Qed.
Lemma D_5f9b8 : decode_any W_5f9b8 = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9bc : bv 32 := 0xf8058ce3.
Lemma F_5f9bc : fetch_word Asan.M.loaded_segments (0x5fa0c : word) = Some W_5f9bc.
Proof. vm_refl. Qed.
Lemma D_5f9bc : decode_any W_5f9bc = Some (Branch BC_EQ 11 0 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9cc : bv 32 := 0x00058a63.
Lemma F_5f9cc : fetch_word Asan.M.loaded_segments (0x5fa1c : word) = Some W_5f9cc.
Proof. vm_refl. Qed.
Lemma D_5f9cc : decode_any W_5f9cc = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9e0 : bv 32 := 0x00048513.
Lemma F_5f9e0 : fetch_word Asan.M.loaded_segments (0x5fa30 : word) = Some W_5f9e0.
Proof. vm_refl. Qed.
Lemma D_5f9e0 : decode_any W_5f9e0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9e4 : bv 32 := 0x07813083.
Lemma F_5f9e4 : fetch_word Asan.M.loaded_segments (0x5fa34 : word) = Some W_5f9e4.
Proof. vm_refl. Qed.
Lemma D_5f9e4 : decode_any W_5f9e4 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9e8 : bv 32 := 0x07013403.
Lemma F_5f9e8 : fetch_word Asan.M.loaded_segments (0x5fa38 : word) = Some W_5f9e8.
Proof. vm_refl. Qed.
Lemma D_5f9e8 : decode_any W_5f9e8 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9ec : bv 32 := 0x06813483.
Lemma F_5f9ec : fetch_word Asan.M.loaded_segments (0x5fa3c : word) = Some W_5f9ec.
Proof. vm_refl. Qed.
Lemma D_5f9ec : decode_any W_5f9ec = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9f0 : bv 32 := 0x06013903.
Lemma F_5f9f0 : fetch_word Asan.M.loaded_segments (0x5fa40 : word) = Some W_5f9f0.
Proof. vm_refl. Qed.
Lemma D_5f9f0 : decode_any W_5f9f0 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9f4 : bv 32 := 0x05813983.
Lemma F_5f9f4 : fetch_word Asan.M.loaded_segments (0x5fa44 : word) = Some W_5f9f4.
Proof. vm_refl. Qed.
Lemma D_5f9f4 : decode_any W_5f9f4 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9f8 : bv 32 := 0x05013a03.
Lemma F_5f9f8 : fetch_word Asan.M.loaded_segments (0x5fa48 : word) = Some W_5f9f8.
Proof. vm_refl. Qed.
Lemma D_5f9f8 : decode_any W_5f9f8 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f9fc : bv 32 := 0x04813a83.
Lemma F_5f9fc : fetch_word Asan.M.loaded_segments (0x5fa4c : word) = Some W_5f9fc.
Proof. vm_refl. Qed.
Lemma D_5f9fc : decode_any W_5f9fc = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa00 : bv 32 := 0x04013b03.
Lemma F_5fa00 : fetch_word Asan.M.loaded_segments (0x5fa50 : word) = Some W_5fa00.
Proof. vm_refl. Qed.
Lemma D_5fa00 : decode_any W_5fa00 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa04 : bv 32 := 0x03813b83.
Lemma F_5fa04 : fetch_word Asan.M.loaded_segments (0x5fa54 : word) = Some W_5fa04.
Proof. vm_refl. Qed.
Lemma D_5fa04 : decode_any W_5fa04 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa08 : bv 32 := 0x03013c03.
Lemma F_5fa08 : fetch_word Asan.M.loaded_segments (0x5fa58 : word) = Some W_5fa08.
Proof. vm_refl. Qed.
Lemma D_5fa08 : decode_any W_5fa08 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa0c : bv 32 := 0x02813c83.
Lemma F_5fa0c : fetch_word Asan.M.loaded_segments (0x5fa5c : word) = Some W_5fa0c.
Proof. vm_refl. Qed.
Lemma D_5fa0c : decode_any W_5fa0c = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa10 : bv 32 := 0x02013d03.
Lemma F_5fa10 : fetch_word Asan.M.loaded_segments (0x5fa60 : word) = Some W_5fa10.
Proof. vm_refl. Qed.
Lemma D_5fa10 : decode_any W_5fa10 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa14 : bv 32 := 0x01813d83.
Lemma F_5fa14 : fetch_word Asan.M.loaded_segments (0x5fa64 : word) = Some W_5fa14.
Proof. vm_refl. Qed.
Lemma D_5fa14 : decode_any W_5fa14 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa18 : bv 32 := 0x08010113.
Lemma F_5fa18 : fetch_word Asan.M.loaded_segments (0x5fa68 : word) = Some W_5fa18.
Proof. vm_refl. Qed.
Lemma D_5fa18 : decode_any W_5fa18 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa1c : bv 32 := 0x00008067.
Lemma F_5fa1c : fetch_word Asan.M.loaded_segments (0x5fa6c : word) = Some W_5fa1c.
Proof. vm_refl. Qed.
Lemma D_5fa1c : decode_any W_5fa1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa20 : bv 32 := 0x00068a93.
Lemma F_5fa20 : fetch_word Asan.M.loaded_segments (0x5fa70 : word) = Some W_5fa20.
Proof. vm_refl. Qed.
Lemma D_5fa20 : decode_any W_5fa20 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa24 : bv 32 := 0x00050913.
Lemma F_5fa24 : fetch_word Asan.M.loaded_segments (0x5fa74 : word) = Some W_5fa24.
Proof. vm_refl. Qed.
Lemma D_5fa24 : decode_any W_5fa24 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa28 : bv 32 := 0x00070b13.
Lemma F_5fa28 : fetch_word Asan.M.loaded_segments (0x5fa78 : word) = Some W_5fa28.
Proof. vm_refl. Qed.
Lemma D_5fa28 : decode_any W_5fa28 = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa2c : bv 32 := 0x40f70733.
Lemma F_5fa2c : fetch_word Asan.M.loaded_segments (0x5fa7c : word) = Some W_5fa2c.
Proof. vm_refl. Qed.
Lemma D_5fa2c : decode_any W_5fa2c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa30 : bv 32 := 0x00048513.
Lemma F_5fa30 : fetch_word Asan.M.loaded_segments (0x5fa80 : word) = Some W_5fa30.
Proof. vm_refl. Qed.
Lemma D_5fa30 : decode_any W_5fa30 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa34 : bv 32 := 0x00040693.
Lemma F_5fa34 : fetch_word Asan.M.loaded_segments (0x5fa84 : word) = Some W_5fa34.
Proof. vm_refl. Qed.
Lemma D_5fa34 : decode_any W_5fa34 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa38 : bv 32 := 0x050000ef.
Lemma F_5fa38 : fetch_word Asan.M.loaded_segments (0x5fa88 : word) = Some W_5fa38.
Proof. vm_refl. Qed.
Lemma D_5fa38 : decode_any W_5fa38 = Some (Jal 1 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa3c : bv 32 := 0x02050263.
Lemma F_5fa3c : fetch_word Asan.M.loaded_segments (0x5fa8c : word) = Some W_5fa3c.
Proof. vm_refl. Qed.
Lemma D_5fa3c : decode_any W_5fa3c = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa40 : bv 32 := 0x01043783.
Lemma F_5fa40 : fetch_word Asan.M.loaded_segments (0x5fa90 : word) = Some W_5fa40.
Proof. vm_refl. Qed.
Lemma D_5fa40 : decode_any W_5fa40 = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa44 : bv 32 := 0x000b0713.
Lemma F_5fa44 : fetch_word Asan.M.loaded_segments (0x5fa94 : word) = Some W_5fa44.
Proof. vm_refl. Qed.
Lemma D_5fa44 : decode_any W_5fa44 = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa48 : bv 32 := 0x0367e263.
Lemma F_5fa48 : fetch_word Asan.M.loaded_segments (0x5fa98 : word) = Some W_5fa48.
Proof. vm_refl. Qed.
Lemma D_5fa48 : decode_any W_5fa48 = Some (Branch BC_LTU 15 22 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa4c : bv 32 := 0x000a8693.
Lemma F_5fa4c : fetch_word Asan.M.loaded_segments (0x5fa9c : word) = Some W_5fa4c.
Proof. vm_refl. Qed.
Lemma D_5fa4c : decode_any W_5fa4c = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa50 : bv 32 := 0x40e787b3.
Lemma F_5fa50 : fetch_word Asan.M.loaded_segments (0x5faa0 : word) = Some W_5fa50.
Proof. vm_refl. Qed.
Lemma D_5fa50 : decode_any W_5fa50 = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa54 : bv 32 := 0x00f43823.
Lemma F_5fa54 : fetch_word Asan.M.loaded_segments (0x5faa4 : word) = Some W_5fa54.
Proof. vm_refl. Qed.
Lemma D_5fa54 : decode_any W_5fa54 = Some (Store SZ8 8 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa58 : bv 32 := 0x00090513.
Lemma F_5fa58 : fetch_word Asan.M.loaded_segments (0x5faa8 : word) = Some W_5fa58.
Proof. vm_refl. Qed.
Lemma D_5fa58 : decode_any W_5fa58 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa5c : bv 32 := 0xe89ff06f.
Lemma F_5fa5c : fetch_word Asan.M.loaded_segments (0x5faac : word) = Some W_5fa5c.
Proof. vm_refl. Qed.
Lemma D_5fa5c : decode_any W_5fa5c = Some (Jal 0 2096776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa88 : bv 32 := 0xfc010113.
Lemma F_5fa88 : fetch_word Asan.M.loaded_segments (0x5fad8 : word) = Some W_5fa88.
Proof. vm_refl. Qed.
Lemma D_5fa88 : decode_any W_5fa88 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa8c : bv 32 := 0x02113c23.
Lemma F_5fa8c : fetch_word Asan.M.loaded_segments (0x5fadc : word) = Some W_5fa8c.
Proof. vm_refl. Qed.
Lemma D_5fa8c : decode_any W_5fa8c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa90 : bv 32 := 0x02813823.
Lemma F_5fa90 : fetch_word Asan.M.loaded_segments (0x5fae0 : word) = Some W_5fa90.
Proof. vm_refl. Qed.
Lemma D_5fa90 : decode_any W_5fa90 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa94 : bv 32 := 0x02913423.
Lemma F_5fa94 : fetch_word Asan.M.loaded_segments (0x5fae4 : word) = Some W_5fa94.
Proof. vm_refl. Qed.
Lemma D_5fa94 : decode_any W_5fa94 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa98 : bv 32 := 0x03213023.
Lemma F_5fa98 : fetch_word Asan.M.loaded_segments (0x5fae8 : word) = Some W_5fa98.
Proof. vm_refl. Qed.
Lemma D_5fa98 : decode_any W_5fa98 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fa9c : bv 32 := 0x01313c23.
Lemma F_5fa9c : fetch_word Asan.M.loaded_segments (0x5faec : word) = Some W_5fa9c.
Proof. vm_refl. Qed.
Lemma D_5fa9c : decode_any W_5fa9c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faa0 : bv 32 := 0x01413823.
Lemma F_5faa0 : fetch_word Asan.M.loaded_segments (0x5faf0 : word) = Some W_5faa0.
Proof. vm_refl. Qed.
Lemma D_5faa0 : decode_any W_5faa0 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faa4 : bv 32 := 0x01513423.
Lemma F_5faa4 : fetch_word Asan.M.loaded_segments (0x5faf4 : word) = Some W_5faa4.
Proof. vm_refl. Qed.
Lemma D_5faa4 : decode_any W_5faa4 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faa8 : bv 32 := 0x01613023.
Lemma F_5faa8 : fetch_word Asan.M.loaded_segments (0x5faf8 : word) = Some W_5faa8.
Proof. vm_refl. Qed.
Lemma D_5faa8 : decode_any W_5faa8 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faac : bv 32 := 0x00068413.
Lemma F_5faac : fetch_word Asan.M.loaded_segments (0x5fafc : word) = Some W_5faac.
Proof. vm_refl. Qed.
Lemma D_5faac : decode_any W_5faac = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fab0 : bv 32 := 0x00058493.
Lemma F_5fab0 : fetch_word Asan.M.loaded_segments (0x5fb00 : word) = Some W_5fab0.
Proof. vm_refl. Qed.
Lemma D_5fab0 : decode_any W_5fab0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fab4 : bv 32 := 0x02053903.
Lemma F_5fab4 : fetch_word Asan.M.loaded_segments (0x5fb04 : word) = Some W_5fab4.
Proof. vm_refl. Qed.
Lemma D_5fab4 : decode_any W_5fab4 = Some (Load SZ8 true 18 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fab8 : bv 32 := 0x01f00693.
Lemma F_5fab8 : fetch_word Asan.M.loaded_segments (0x5fb08 : word) = Some W_5fab8.
Proof. vm_refl. Qed.
Lemma D_5fab8 : decode_any W_5fab8 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fabc : bv 32 := 0x02061593.
Lemma F_5fabc : fetch_word Asan.M.loaded_segments (0x5fb0c : word) = Some W_5fabc.
Proof. vm_refl. Qed.
Lemma D_5fabc : decode_any W_5fabc = Some (ShiftImm ALU_SLL 11 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fac0 : bv 32 := 0x20d60263.
Lemma F_5fac0 : fetch_word Asan.M.loaded_segments (0x5fb10 : word) = Some W_5fac0.
Proof. vm_refl. Qed.
Lemma D_5fac0 : decode_any W_5fac0 = Some (Branch BC_EQ 12 13 516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fac4 : bv 32 := 0x01000693.
Lemma F_5fac4 : fetch_word Asan.M.loaded_segments (0x5fb14 : word) = Some W_5fac4.
Proof. vm_refl. Qed.
Lemma D_5fac4 : decode_any W_5fac4 = Some (OpImm ALU_ADD 13 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fac8 : bv 32 := 0x02c6e263.
Lemma F_5fac8 : fetch_word Asan.M.loaded_segments (0x5fb18 : word) = Some W_5fac8.
Proof. vm_refl. Qed.
Lemma D_5fac8 : decode_any W_5fac8 = Some (Branch BC_LTU 13 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5facc : bv 32 := 0x00561a93.
Lemma F_5facc : fetch_word Asan.M.loaded_segments (0x5fb1c : word) = Some W_5facc.
Proof. vm_refl. Qed.
Lemma D_5facc : decode_any W_5facc = Some (ShiftImm ALU_SLL 21 12 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fad0 : bv 32 := 0x02043683.
Lemma F_5fad0 : fetch_word Asan.M.loaded_segments (0x5fb20 : word) = Some W_5fad0.
Proof. vm_refl. Qed.
Lemma D_5fad0 : decode_any W_5fad0 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fad4 : bv 32 := 0x03043a03.
Lemma F_5fad4 : fetch_word Asan.M.loaded_segments (0x5fb24 : word) = Some W_5fad4.
Proof. vm_refl. Qed.
Lemma D_5fad4 : decode_any W_5fad4 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fad8 : bv 32 := 0x02ea89b3.
Lemma F_5fad8 : fetch_word Asan.M.loaded_segments (0x5fb28 : word) = Some W_5fad8.
Proof. vm_refl. Qed.
Lemma D_5fad8 : decode_any W_5fad8 = Some (Mul M_MUL 19 21 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fadc : bv 32 := 0x013689b3.
Lemma F_5fadc : fetch_word Asan.M.loaded_segments (0x5fb2c : word) = Some W_5fadc.
Proof. vm_refl. Qed.
Lemma D_5fadc : decode_any W_5fadc = Some (Op ALU_ADD 19 13 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fae0 : bv 32 := 0x00b90933.
Lemma F_5fae0 : fetch_word Asan.M.loaded_segments (0x5fb30 : word) = Some W_5fae0.
Proof. vm_refl. Qed.
Lemma D_5fae0 : decode_any W_5fae0 = Some (Op ALU_ADD 18 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fae4 : bv 32 := 0x053a6263.
Lemma F_5fae4 : fetch_word Asan.M.loaded_segments (0x5fb34 : word) = Some W_5fae4.
Proof. vm_refl. Qed.
Lemma D_5fae4 : decode_any W_5fae4 = Some (Branch BC_LTU 20 19 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faec : bv 32 := 0xff060693.
Lemma F_5faec : fetch_word Asan.M.loaded_segments (0x5fb3c : word) = Some W_5faec.
Proof. vm_refl. Qed.
Lemma D_5faec : decode_any W_5faec = Some (OpImm ALU_ADD 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faf0 : bv 32 := 0x20000793.
Lemma F_5faf0 : fetch_word Asan.M.loaded_segments (0x5fb40 : word) = Some W_5faf0.
Proof. vm_refl. Qed.
Lemma D_5faf0 : decode_any W_5faf0 = Some (OpImm ALU_ADD 15 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faf4 : bv 32 := 0x03f61813.
Lemma F_5faf4 : fetch_word Asan.M.loaded_segments (0x5fb44 : word) = Some W_5faf4.
Proof. vm_refl. Qed.
Lemma D_5faf4 : decode_any W_5faf4 = Some (ShiftImm ALU_SLL 16 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5faf8 : bv 32 := 0x0016d693.
Lemma F_5faf8 : fetch_word Asan.M.loaded_segments (0x5fb48 : word) = Some W_5faf8.
Proof. vm_refl. Qed.
Lemma D_5faf8 : decode_any W_5faf8 = Some (ShiftImm ALU_SRL 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fafc : bv 32 := 0x00d79ab3.
Lemma F_5fafc : fetch_word Asan.M.loaded_segments (0x5fb4c : word) = Some W_5fafc.
Proof. vm_refl. Qed.
Lemma D_5fafc : decode_any W_5fafc = Some (Op ALU_SLL 21 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb00 : bv 32 := 0x001ad693.
Lemma F_5fb00 : fetch_word Asan.M.loaded_segments (0x5fb50 : word) = Some W_5fb00.
Proof. vm_refl. Qed.
Lemma D_5fb00 : decode_any W_5fb00 = Some (ShiftImm ALU_SRL 13 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb04 : bv 32 := 0x43f85793.
Lemma F_5fb04 : fetch_word Asan.M.loaded_segments (0x5fb54 : word) = Some W_5fb04.
Proof. vm_refl. Qed.
Lemma D_5fb04 : decode_any W_5fb04 = Some (ShiftImm ALU_SRA 15 16 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb08 : bv 32 := 0x00d7f6b3.
Lemma F_5fb08 : fetch_word Asan.M.loaded_segments (0x5fb58 : word) = Some W_5fb08.
Proof. vm_refl. Qed.
Lemma D_5fb08 : decode_any W_5fb08 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb0c : bv 32 := 0x01568ab3.
Lemma F_5fb0c : fetch_word Asan.M.loaded_segments (0x5fb5c : word) = Some W_5fb0c.
Proof. vm_refl. Qed.
Lemma D_5fb0c : decode_any W_5fb0c = Some (Op ALU_ADD 21 13 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb10 : bv 32 := 0x02043683.
Lemma F_5fb10 : fetch_word Asan.M.loaded_segments (0x5fb60 : word) = Some W_5fb10.
Proof. vm_refl. Qed.
Lemma D_5fb10 : decode_any W_5fb10 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb14 : bv 32 := 0x03043a03.
Lemma F_5fb14 : fetch_word Asan.M.loaded_segments (0x5fb64 : word) = Some W_5fb14.
Proof. vm_refl. Qed.
Lemma D_5fb14 : decode_any W_5fb14 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb18 : bv 32 := 0x02ea89b3.
Lemma F_5fb18 : fetch_word Asan.M.loaded_segments (0x5fb68 : word) = Some W_5fb18.
Proof. vm_refl. Qed.
Lemma D_5fb18 : decode_any W_5fb18 = Some (Mul M_MUL 19 21 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb1c : bv 32 := 0x013689b3.
Lemma F_5fb1c : fetch_word Asan.M.loaded_segments (0x5fb6c : word) = Some W_5fb1c.
Proof. vm_refl. Qed.
Lemma D_5fb1c : decode_any W_5fb1c = Some (Op ALU_ADD 19 13 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb20 : bv 32 := 0x00b90933.
Lemma F_5fb20 : fetch_word Asan.M.loaded_segments (0x5fb70 : word) = Some W_5fb20.
Proof. vm_refl. Qed.
Lemma D_5fb20 : decode_any W_5fb20 = Some (Op ALU_ADD 18 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb24 : bv 32 := 0x0d3a7c63.
Lemma F_5fb24 : fetch_word Asan.M.loaded_segments (0x5fb74 : word) = Some W_5fb24.
Proof. vm_refl. Qed.
Lemma D_5fb24 : decode_any W_5fb24 = Some (Branch BC_GEU 20 19 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb28 : bv 32 := 0x1a0a0e63.
Lemma F_5fb28 : fetch_word Asan.M.loaded_segments (0x5fb78 : word) = Some W_5fb28.
Proof. vm_refl. Qed.
Lemma D_5fb28 : decode_any W_5fb28 = Some (Branch BC_EQ 20 0 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb2c : bv 32 := 0xfffa4593.
Lemma F_5fb2c : fetch_word Asan.M.loaded_segments (0x5fb7c : word) = Some W_5fb2c.
Proof. vm_refl. Qed.
Lemma D_5fb2c : decode_any W_5fb2c = Some (OpImm ALU_XOR 11 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb30 : bv 32 := 0xfffc06b7.
Lemma F_5fb30 : fetch_word Asan.M.loaded_segments (0x5fb80 : word) = Some W_5fb30.
Proof. vm_refl. Qed.
Lemma D_5fb30 : decode_any W_5fb30 = Some (Lui 13 1048512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb34 : bv 32 := 0x00b985b3.
Lemma F_5fb34 : fetch_word Asan.M.loaded_segments (0x5fb84 : word) = Some W_5fb34.
Proof. vm_refl. Qed.
Lemma D_5fb34 : decode_any W_5fb34 = Some (Op ALU_ADD 11 19 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb38 : bv 32 := 0x000409b7.
Lemma F_5fb38 : fetch_word Asan.M.loaded_segments (0x5fb88 : word) = Some W_5fb38.
Proof. vm_refl. Qed.
Lemma D_5fb38 : decode_any W_5fb38 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb3c : bv 32 := 0x00d5f5b3.
Lemma F_5fb3c : fetch_word Asan.M.loaded_segments (0x5fb8c : word) = Some W_5fb3c.
Proof. vm_refl. Qed.
Lemma D_5fb3c : decode_any W_5fb3c = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb40 : bv 32 := 0x03843683.
Lemma F_5fb40 : fetch_word Asan.M.loaded_segments (0x5fb90 : word) = Some W_5fb40.
Proof. vm_refl. Qed.
Lemma D_5fb40 : decode_any W_5fb40 = Some (Load SZ8 true 13 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb44 : bv 32 := 0x013589b3.
Lemma F_5fb44 : fetch_word Asan.M.loaded_segments (0x5fb94 : word) = Some W_5fb44.
Proof. vm_refl. Qed.
Lemma D_5fb44 : decode_any W_5fb44 = Some (Op ALU_ADD 19 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb48 : bv 32 := 0x00700593.
Lemma F_5fb48 : fetch_word Asan.M.loaded_segments (0x5fb98 : word) = Some W_5fb48.
Proof. vm_refl. Qed.
Lemma D_5fb48 : decode_any W_5fb48 = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb4c : bv 32 := 0x01d59593.
Lemma F_5fb4c : fetch_word Asan.M.loaded_segments (0x5fb9c : word) = Some W_5fb4c.
Proof. vm_refl. Qed.
Lemma D_5fb4c : decode_any W_5fb4c = Some (ShiftImm ALU_SLL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb50 : bv 32 := 0x014686b3.
Lemma F_5fb50 : fetch_word Asan.M.loaded_segments (0x5fba0 : word) = Some W_5fb50.
Proof. vm_refl. Qed.
Lemma D_5fb50 : decode_any W_5fb50 = Some (Op ALU_ADD 13 13 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb54 : bv 32 := 0x013686b3.
Lemma F_5fb54 : fetch_word Asan.M.loaded_segments (0x5fba4 : word) = Some W_5fb54.
Proof. vm_refl. Qed.
Lemma D_5fb54 : decode_any W_5fb54 = Some (Op ALU_ADD 13 13 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb58 : bv 32 := 0x00158593.
Lemma F_5fb58 : fetch_word Asan.M.loaded_segments (0x5fba8 : word) = Some W_5fb58.
Proof. vm_refl. Qed.
Lemma D_5fb58 : decode_any W_5fb58 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb5c : bv 32 := 0x1ab6fa63.
Lemma F_5fb5c : fetch_word Asan.M.loaded_segments (0x5fbac : word) = Some W_5fb5c.
Proof. vm_refl. Qed.
Lemma D_5fb5c : decode_any W_5fb5c = Some (Branch BC_GEU 13 11 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb60 : bv 32 := 0x03854583.
Lemma F_5fb60 : fetch_word Asan.M.loaded_segments (0x5fbb0 : word) = Some W_5fb60.
Proof. vm_refl. Qed.
Lemma D_5fb60 : decode_any W_5fb60 = Some (Load SZ1 false 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb64 : bv 32 := 0x012a0a33.
Lemma F_5fb64 : fetch_word Asan.M.loaded_segments (0x5fbb4 : word) = Some W_5fb64.
Proof. vm_refl. Qed.
Lemma D_5fb64 : decode_any W_5fb64 = Some (Op ALU_ADD 20 20 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb68 : bv 32 := 0x02058463.
Lemma F_5fb68 : fetch_word Asan.M.loaded_segments (0x5fbb8 : word) = Some W_5fb68.
Proof. vm_refl. Qed.
Lemma D_5fb68 : decode_any W_5fb68 = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb90 : bv 32 := 0xfffb8597.
Lemma F_5fb90 : fetch_word Asan.M.loaded_segments (0x5fbe0 : word) = Some W_5fb90.
Proof. vm_refl. Qed.
Lemma D_5fb90 : decode_any W_5fb90 = Some (Auipc 11 1048504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb94 : bv 32 := 0x55f58693.
Lemma F_5fb94 : fetch_word Asan.M.loaded_segments (0x5fbe4 : word) = Some W_5fb94.
Proof. vm_refl. Qed.
Lemma D_5fb94 : decode_any W_5fb94 = Some (OpImm ALU_ADD 13 11 1375, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb98 : bv 32 := 0x00050b13.
Lemma F_5fb98 : fetch_word Asan.M.loaded_segments (0x5fbe8 : word) = Some W_5fb98.
Proof. vm_refl. Qed.
Lemma D_5fb98 : decode_any W_5fb98 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fb9c : bv 32 := 0x000a0593.
Lemma F_5fb9c : fetch_word Asan.M.loaded_segments (0x5fbec : word) = Some W_5fb9c.
Proof. vm_refl. Qed.
Lemma D_5fb9c : decode_any W_5fb9c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fba0 : bv 32 := 0x00098613.
Lemma F_5fba0 : fetch_word Asan.M.loaded_segments (0x5fbf0 : word) = Some W_5fba0.
Proof. vm_refl. Qed.
Lemma D_5fba0 : decode_any W_5fba0 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fba4 : bv 32 := 0x5843e0ef.
Lemma F_5fba4 : fetch_word Asan.M.loaded_segments (0x5fbf4 : word) = Some W_5fba4.
Proof. vm_refl. Qed.
Lemma D_5fba4 : decode_any W_5fba4 = Some (Jal 1 255364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fba8 : bv 32 := 0x16050863.
Lemma F_5fba8 : fetch_word Asan.M.loaded_segments (0x5fbf8 : word) = Some W_5fba8.
Proof. vm_refl. Qed.
Lemma D_5fba8 : decode_any W_5fba8 = Some (Branch BC_EQ 10 0 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbac : bv 32 := 0x00050713.
Lemma F_5fbac : fetch_word Asan.M.loaded_segments (0x5fbfc : word) = Some W_5fbac.
Proof. vm_refl. Qed.
Lemma D_5fbac : decode_any W_5fbac = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbb0 : bv 32 := 0x1eaa1063.
Lemma F_5fbb0 : fetch_word Asan.M.loaded_segments (0x5fc00 : word) = Some W_5fbb0.
Proof. vm_refl. Qed.
Lemma D_5fbb0 : decode_any W_5fbb0 = Some (Branch BC_NE 20 10 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbb4 : bv 32 := 0x0fa00613.
Lemma F_5fbb4 : fetch_word Asan.M.loaded_segments (0x5fc04 : word) = Some W_5fbb4.
Proof. vm_refl. Qed.
Lemma D_5fbb4 : decode_any W_5fbb4 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbb8 : bv 32 := 0x000a0513.
Lemma F_5fbb8 : fetch_word Asan.M.loaded_segments (0x5fc08 : word) = Some W_5fbb8.
Proof. vm_refl. Qed.
Lemma D_5fbb8 : decode_any W_5fbb8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbbc : bv 32 := 0x00098593.
Lemma F_5fbbc : fetch_word Asan.M.loaded_segments (0x5fc0c : word) = Some W_5fbbc.
Proof. vm_refl. Qed.
Lemma D_5fbbc : decode_any W_5fbbc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbc0 : bv 32 := 0x4d4230ef.
Lemma F_5fbc0 : fetch_word Asan.M.loaded_segments (0x5fc10 : word) = Some W_5fbc0.
Proof. vm_refl. Qed.
Lemma D_5fbc0 : decode_any W_5fbc0 = Some (Jal 1 144596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbc4 : bv 32 := 0x4482b0ef.
Lemma F_5fbc4 : fetch_word Asan.M.loaded_segments (0x5fc14 : word) = Some W_5fbc4.
Proof. vm_refl. Qed.
Lemma D_5fbc4 : decode_any W_5fbc4 = Some (Jal 1 177224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbc8 : bv 32 := 0x04853583.
Lemma F_5fbc8 : fetch_word Asan.M.loaded_segments (0x5fc18 : word) = Some W_5fbc8.
Proof. vm_refl. Qed.
Lemma D_5fbc8 : decode_any W_5fbc8 = Some (Load SZ8 true 11 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbcc : bv 32 := 0x05053603.
Lemma F_5fbcc : fetch_word Asan.M.loaded_segments (0x5fc1c : word) = Some W_5fbcc.
Proof. vm_refl. Qed.
Lemma D_5fbcc : decode_any W_5fbcc = Some (Load SZ8 true 12 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbd0 : bv 32 := 0x00158593.
Lemma F_5fbd0 : fetch_word Asan.M.loaded_segments (0x5fc20 : word) = Some W_5fbd0.
Proof. vm_refl. Qed.
Lemma D_5fbd0 : decode_any W_5fbd0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbd4 : bv 32 := 0x01360633.
Lemma F_5fbd4 : fetch_word Asan.M.loaded_segments (0x5fc24 : word) = Some W_5fbd4.
Proof. vm_refl. Qed.
Lemma D_5fbd4 : decode_any W_5fbd4 = Some (Op ALU_ADD 12 12 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbd8 : bv 32 := 0x04b53423.
Lemma F_5fbd8 : fetch_word Asan.M.loaded_segments (0x5fc28 : word) = Some W_5fbd8.
Proof. vm_refl. Qed.
Lemma D_5fbd8 : decode_any W_5fbd8 = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbdc : bv 32 := 0x04c53823.
Lemma F_5fbdc : fetch_word Asan.M.loaded_segments (0x5fc2c : word) = Some W_5fbdc.
Proof. vm_refl. Qed.
Lemma D_5fbdc : decode_any W_5fbdc = Some (Store SZ8 10 12 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbe0 : bv 32 := 0x000b0513.
Lemma F_5fbe0 : fetch_word Asan.M.loaded_segments (0x5fc30 : word) = Some W_5fbe0.
Proof. vm_refl. Qed.
Lemma D_5fbe0 : decode_any W_5fbe0 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbe4 : bv 32 := 0x01848493.
Lemma F_5fbe4 : fetch_word Asan.M.loaded_segments (0x5fc34 : word) = Some W_5fbe4.
Proof. vm_refl. Qed.
Lemma D_5fbe4 : decode_any W_5fbe4 = Some (OpImm ALU_ADD 9 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbe8 : bv 32 := 0x0134b02f.
Lemma F_5fbe8 : fetch_word Asan.M.loaded_segments (0x5fc38 : word) = Some W_5fbe8.
Proof. vm_refl. Qed.
Lemma D_5fbe8 : decode_any W_5fbe8 = Some (Amo AMO_ADD AD false false 0 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbec : bv 32 := 0x03043a03.
Lemma F_5fbec : fetch_word Asan.M.loaded_segments (0x5fc3c : word) = Some W_5fbec.
Proof. vm_refl. Qed.
Lemma D_5fbec : decode_any W_5fbec = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbf0 : bv 32 := 0x02043683.
Lemma F_5fbf0 : fetch_word Asan.M.loaded_segments (0x5fc40 : word) = Some W_5fbf0.
Proof. vm_refl. Qed.
Lemma D_5fbf0 : decode_any W_5fbf0 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbf4 : bv 32 := 0x013a0a33.
Lemma F_5fbf4 : fetch_word Asan.M.loaded_segments (0x5fc44 : word) = Some W_5fbf4.
Proof. vm_refl. Qed.
Lemma D_5fbf4 : decode_any W_5fbf4 = Some (Op ALU_ADD 20 20 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbf8 : bv 32 := 0x03443823.
Lemma F_5fbf8 : fetch_word Asan.M.loaded_segments (0x5fc48 : word) = Some W_5fbf8.
Proof. vm_refl. Qed.
Lemma D_5fbf8 : decode_any W_5fbf8 = Some (Store SZ8 8 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fbfc : bv 32 := 0x01043483.
Lemma F_5fbfc : fetch_word Asan.M.loaded_segments (0x5fc4c : word) = Some W_5fbfc.
Proof. vm_refl. Qed.
Lemma D_5fbfc : decode_any W_5fbfc = Some (Load SZ8 true 9 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc00 : bv 32 := 0x40da0a33.
Lemma F_5fc00 : fetch_word Asan.M.loaded_segments (0x5fc50 : word) = Some W_5fc00.
Proof. vm_refl. Qed.
Lemma D_5fc00 : decode_any W_5fc00 = Some (Op ALU_SUB 20 20 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc04 : bv 32 := 0x035a59b3.
Lemma F_5fc04 : fetch_word Asan.M.loaded_segments (0x5fc54 : word) = Some W_5fc04.
Proof. vm_refl. Qed.
Lemma D_5fc04 : decode_any W_5fc04 = Some (Mul M_DIVU 19 20 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc08 : bv 32 := 0x013484b3.
Lemma F_5fc08 : fetch_word Asan.M.loaded_segments (0x5fc58 : word) = Some W_5fc08.
Proof. vm_refl. Qed.
Lemma D_5fc08 : decode_any W_5fc08 = Some (Op ALU_ADD 9 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc0c : bv 32 := 0x00040593.
Lemma F_5fc0c : fetch_word Asan.M.loaded_segments (0x5fc5c : word) = Some W_5fc0c.
Proof. vm_refl. Qed.
Lemma D_5fc0c : decode_any W_5fc0c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc10 : bv 32 := 0x00090613.
Lemma F_5fc10 : fetch_word Asan.M.loaded_segments (0x5fc60 : word) = Some W_5fc10.
Proof. vm_refl. Qed.
Lemma D_5fc10 : decode_any W_5fc10 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc14 : bv 32 := 0x00048693.
Lemma F_5fc14 : fetch_word Asan.M.loaded_segments (0x5fc64 : word) = Some W_5fc14.
Proof. vm_refl. Qed.
Lemma D_5fc14 : decode_any W_5fc14 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc18 : bv 32 := 0xb35fd0ef.
Lemma F_5fc18 : fetch_word Asan.M.loaded_segments (0x5fc68 : word) = Some W_5fc18.
Proof. vm_refl. Qed.
Lemma D_5fc18 : decode_any W_5fc18 = Some (Jal 1 2087732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc1c : bv 32 := 0x0e050e63.
Lemma F_5fc1c : fetch_word Asan.M.loaded_segments (0x5fc6c : word) = Some W_5fc1c.
Proof. vm_refl. Qed.
Lemma D_5fc1c : decode_any W_5fc1c = Some (Branch BC_EQ 10 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc20 : bv 32 := 0x02043683.
Lemma F_5fc20 : fetch_word Asan.M.loaded_segments (0x5fc70 : word) = Some W_5fc20.
Proof. vm_refl. Qed.
Lemma D_5fc20 : decode_any W_5fc20 = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc24 : bv 32 := 0x055a6063.
Lemma F_5fc24 : fetch_word Asan.M.loaded_segments (0x5fc74 : word) = Some W_5fc24.
Proof. vm_refl. Qed.
Lemma D_5fc24 : decode_any W_5fc24 = Some (Branch BC_LTU 20 21 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc28 : bv 32 := 0x00000513.
Lemma F_5fc28 : fetch_word Asan.M.loaded_segments (0x5fc78 : word) = Some W_5fc28.
Proof. vm_refl. Qed.
Lemma D_5fc28 : decode_any W_5fc28 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc2c : bv 32 := 0x00700593.
Lemma F_5fc2c : fetch_word Asan.M.loaded_segments (0x5fc7c : word) = Some W_5fc2c.
Proof. vm_refl. Qed.
Lemma D_5fc2c : decode_any W_5fc2c = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc30 : bv 32 := 0x01d59593.
Lemma F_5fc30 : fetch_word Asan.M.loaded_segments (0x5fc80 : word) = Some W_5fc30.
Proof. vm_refl. Qed.
Lemma D_5fc30 : decode_any W_5fc30 = Some (ShiftImm ALU_SLL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc34 : bv 32 := 0x00b905b3.
Lemma F_5fc34 : fetch_word Asan.M.loaded_segments (0x5fc84 : word) = Some W_5fc34.
Proof. vm_refl. Qed.
Lemma D_5fc34 : decode_any W_5fc34 = Some (Op ALU_ADD 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc38 : bv 32 := 0x00249493.
Lemma F_5fc38 : fetch_word Asan.M.loaded_segments (0x5fc88 : word) = Some W_5fc38.
Proof. vm_refl. Qed.
Lemma D_5fc38 : decode_any W_5fc38 = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc3c : bv 32 := 0x009585b3.
Lemma F_5fc3c : fetch_word Asan.M.loaded_segments (0x5fc8c : word) = Some W_5fc3c.
Proof. vm_refl. Qed.
Lemma D_5fc3c : decode_any W_5fc3c = Some (Op ALU_ADD 11 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc40 : bv 32 := 0x00068613.
Lemma F_5fc40 : fetch_word Asan.M.loaded_segments (0x5fc90 : word) = Some W_5fc40.
Proof. vm_refl. Qed.
Lemma D_5fc40 : decode_any W_5fc40 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc44 : bv 32 := 0x00465713.
Lemma F_5fc44 : fetch_word Asan.M.loaded_segments (0x5fc94 : word) = Some W_5fc44.
Proof. vm_refl. Qed.
Lemma D_5fc44 : decode_any W_5fc44 = Some (ShiftImm ALU_SRL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc48 : bv 32 := 0xfff54793.
Lemma F_5fc48 : fetch_word Asan.M.loaded_segments (0x5fc98 : word) = Some W_5fc48.
Proof. vm_refl. Qed.
Lemma D_5fc48 : decode_any W_5fc48 = Some (OpImm ALU_XOR 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc4c : bv 32 := 0x00150513.
Lemma F_5fc4c : fetch_word Asan.M.loaded_segments (0x5fc9c : word) = Some W_5fc4c.
Proof. vm_refl. Qed.
Lemma D_5fc4c : decode_any W_5fc4c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc50 : bv 32 := 0x00279793.
Lemma F_5fc50 : fetch_word Asan.M.loaded_segments (0x5fca0 : word) = Some W_5fc50.
Proof. vm_refl. Qed.
Lemma D_5fc50 : decode_any W_5fc50 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc54 : bv 32 := 0x00f587b3.
Lemma F_5fc54 : fetch_word Asan.M.loaded_segments (0x5fca4 : word) = Some W_5fc54.
Proof. vm_refl. Qed.
Lemma D_5fc54 : decode_any W_5fc54 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc58 : bv 32 := 0x00e7a023.
Lemma F_5fc58 : fetch_word Asan.M.loaded_segments (0x5fca8 : word) = Some W_5fc58.
Proof. vm_refl. Qed.
Lemma D_5fc58 : decode_any W_5fc58 = Some (Store SZ4 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc5c : bv 32 := 0x01560633.
Lemma F_5fc5c : fetch_word Asan.M.loaded_segments (0x5fcac : word) = Some W_5fc5c.
Proof. vm_refl. Qed.
Lemma D_5fc5c : decode_any W_5fc5c = Some (Op ALU_ADD 12 12 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc60 : bv 32 := 0xff3562e3.
Lemma F_5fc60 : fetch_word Asan.M.loaded_segments (0x5fcb0 : word) = Some W_5fc60.
Proof. vm_refl. Qed.
Lemma D_5fc60 : decode_any W_5fc60 = Some (Branch BC_LTU 10 19 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc64 : bv 32 := 0x01043503.
Lemma F_5fc64 : fetch_word Asan.M.loaded_segments (0x5fcb4 : word) = Some W_5fc64.
Proof. vm_refl. Qed.
Lemma D_5fc64 : decode_any W_5fc64 = Some (Load SZ8 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc68 : bv 32 := 0x035985b3.
Lemma F_5fc68 : fetch_word Asan.M.loaded_segments (0x5fcb8 : word) = Some W_5fc68.
Proof. vm_refl. Qed.
Lemma D_5fc68 : decode_any W_5fc68 = Some (Mul M_MUL 11 19 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc6c : bv 32 := 0x03043703.
Lemma F_5fc6c : fetch_word Asan.M.loaded_segments (0x5fcbc : word) = Some W_5fc6c.
Proof. vm_refl. Qed.
Lemma D_5fc6c : decode_any W_5fc6c = Some (Load SZ8 true 14 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc70 : bv 32 := 0x00b686b3.
Lemma F_5fc70 : fetch_word Asan.M.loaded_segments (0x5fcc0 : word) = Some W_5fc70.
Proof. vm_refl. Qed.
Lemma D_5fc70 : decode_any W_5fc70 = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc74 : bv 32 := 0x01350533.
Lemma F_5fc74 : fetch_word Asan.M.loaded_segments (0x5fcc4 : word) = Some W_5fc74.
Proof. vm_refl. Qed.
Lemma D_5fc74 : decode_any W_5fc74 = Some (Op ALU_ADD 10 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc78 : bv 32 := 0x00a43823.
Lemma F_5fc78 : fetch_word Asan.M.loaded_segments (0x5fcc8 : word) = Some W_5fc78.
Proof. vm_refl. Qed.
Lemma D_5fc78 : decode_any W_5fc78 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc7c : bv 32 := 0x02d43023.
Lemma F_5fc7c : fetch_word Asan.M.loaded_segments (0x5fccc : word) = Some W_5fc7c.
Proof. vm_refl. Qed.
Lemma D_5fc7c : decode_any W_5fc7c = Some (Store SZ8 8 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc80 : bv 32 := 0x0ad76063.
Lemma F_5fc80 : fetch_word Asan.M.loaded_segments (0x5fcd0 : word) = Some W_5fc80.
Proof. vm_refl. Qed.
Lemma D_5fc80 : decode_any W_5fc80 = Some (Branch BC_LTU 14 13 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc84 : bv 32 := 0x02843683.
Lemma F_5fc84 : fetch_word Asan.M.loaded_segments (0x5fcd4 : word) = Some W_5fc84.
Proof. vm_refl. Qed.
Lemma D_5fc84 : decode_any W_5fc84 = Some (Load SZ8 true 13 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc88 : bv 32 := 0x03843703.
Lemma F_5fc88 : fetch_word Asan.M.loaded_segments (0x5fcd8 : word) = Some W_5fc88.
Proof. vm_refl. Qed.
Lemma D_5fc88 : decode_any W_5fc88 = Some (Load SZ8 true 14 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc8c : bv 32 := 0x0ad76663.
Lemma F_5fc8c : fetch_word Asan.M.loaded_segments (0x5fcdc : word) = Some W_5fc8c.
Proof. vm_refl. Qed.
Lemma D_5fc8c : decode_any W_5fc8c = Some (Branch BC_LTU 14 13 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc90 : bv 32 := 0x04040223.
Lemma F_5fc90 : fetch_word Asan.M.loaded_segments (0x5fce0 : word) = Some W_5fc90.
Proof. vm_refl. Qed.
Lemma D_5fc90 : decode_any W_5fc90 = Some (Store SZ1 8 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc94 : bv 32 := 0x00100593.
Lemma F_5fc94 : fetch_word Asan.M.loaded_segments (0x5fce4 : word) = Some W_5fc94.
Proof. vm_refl. Qed.
Lemma D_5fc94 : decode_any W_5fc94 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc98 : bv 32 := 0x00058513.
Lemma F_5fc98 : fetch_word Asan.M.loaded_segments (0x5fce8 : word) = Some W_5fc98.
Proof. vm_refl. Qed.
Lemma D_5fc98 : decode_any W_5fc98 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fc9c : bv 32 := 0x03813083.
Lemma F_5fc9c : fetch_word Asan.M.loaded_segments (0x5fcec : word) = Some W_5fc9c.
Proof. vm_refl. Qed.
Lemma D_5fc9c : decode_any W_5fc9c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fca0 : bv 32 := 0x03013403.
Lemma F_5fca0 : fetch_word Asan.M.loaded_segments (0x5fcf0 : word) = Some W_5fca0.
Proof. vm_refl. Qed.
Lemma D_5fca0 : decode_any W_5fca0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fca4 : bv 32 := 0x02813483.
Lemma F_5fca4 : fetch_word Asan.M.loaded_segments (0x5fcf4 : word) = Some W_5fca4.
Proof. vm_refl. Qed.
Lemma D_5fca4 : decode_any W_5fca4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fca8 : bv 32 := 0x02013903.
Lemma F_5fca8 : fetch_word Asan.M.loaded_segments (0x5fcf8 : word) = Some W_5fca8.
Proof. vm_refl. Qed.
Lemma D_5fca8 : decode_any W_5fca8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcac : bv 32 := 0x01813983.
Lemma F_5fcac : fetch_word Asan.M.loaded_segments (0x5fcfc : word) = Some W_5fcac.
Proof. vm_refl. Qed.
Lemma D_5fcac : decode_any W_5fcac = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcb0 : bv 32 := 0x01013a03.
Lemma F_5fcb0 : fetch_word Asan.M.loaded_segments (0x5fd00 : word) = Some W_5fcb0.
Proof. vm_refl. Qed.
Lemma D_5fcb0 : decode_any W_5fcb0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcb4 : bv 32 := 0x00813a83.
Lemma F_5fcb4 : fetch_word Asan.M.loaded_segments (0x5fd04 : word) = Some W_5fcb4.
Proof. vm_refl. Qed.
Lemma D_5fcb4 : decode_any W_5fcb4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcb8 : bv 32 := 0x00013b03.
Lemma F_5fcb8 : fetch_word Asan.M.loaded_segments (0x5fd08 : word) = Some W_5fcb8.
Proof. vm_refl. Qed.
Lemma D_5fcb8 : decode_any W_5fcb8 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcbc : bv 32 := 0x04010113.
Lemma F_5fcbc : fetch_word Asan.M.loaded_segments (0x5fd0c : word) = Some W_5fcbc.
Proof. vm_refl. Qed.
Lemma D_5fcbc : decode_any W_5fcbc = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fcc0 : bv 32 := 0x00008067.
Lemma F_5fcc0 : fetch_word Asan.M.loaded_segments (0x5fd10 : word) = Some W_5fcc0.
Proof. vm_refl. Qed.
Lemma D_5fcc0 : decode_any W_5fcc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fce4 : bv 32 := 0x02852583.
Lemma F_5fce4 : fetch_word Asan.M.loaded_segments (0x5fd34 : word) = Some W_5fce4.
Proof. vm_refl. Qed.
Lemma D_5fce4 : decode_any W_5fce4 = Some (Load SZ4 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fce8 : bv 32 := 0x0c05c263.
Lemma F_5fce8 : fetch_word Asan.M.loaded_segments (0x5fd38 : word) = Some W_5fce8.
Proof. vm_refl. Qed.
Lemma D_5fce8 : decode_any W_5fce8 = Some (Branch BC_LT 11 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdac : bv 32 := 0x00000a13.
Lemma F_5fdac : fetch_word Asan.M.loaded_segments (0x5fdfc : word) = Some W_5fdac.
Proof. vm_refl. Qed.
Lemma D_5fdac : decode_any W_5fdac = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdb0 : bv 32 := 0xd7dff06f.
Lemma F_5fdb0 : fetch_word Asan.M.loaded_segments (0x5fe00 : word) = Some W_5fdb0.
Proof. vm_refl. Qed.
Lemma D_5fdb0 : decode_any W_5fdb0 = Some (Jal 0 2096508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdf8 : bv 32 := 0xff010113.
Lemma F_5fdf8 : fetch_word Asan.M.loaded_segments (0x5fe48 : word) = Some W_5fdf8.
Proof. vm_refl. Qed.
Lemma D_5fdf8 : decode_any W_5fdf8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fdfc : bv 32 := 0x00113423.
Lemma F_5fdfc : fetch_word Asan.M.loaded_segments (0x5fe4c : word) = Some W_5fdfc.
Proof. vm_refl. Qed.
Lemma D_5fdfc : decode_any W_5fdfc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe00 : bv 32 := 0x02051693.
Lemma F_5fe00 : fetch_word Asan.M.loaded_segments (0x5fe50 : word) = Some W_5fe00.
Proof. vm_refl. Qed.
Lemma D_5fe00 : decode_any W_5fe00 = Some (ShiftImm ALU_SLL 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe04 : bv 32 := 0x00f00593.
Lemma F_5fe04 : fetch_word Asan.M.loaded_segments (0x5fe54 : word) = Some W_5fe04.
Proof. vm_refl. Qed.
Lemma D_5fe04 : decode_any W_5fe04 = Some (OpImm ALU_ADD 11 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe08 : bv 32 := 0x0206d693.
Lemma F_5fe08 : fetch_word Asan.M.loaded_segments (0x5fe58 : word) = Some W_5fe08.
Proof. vm_refl. Qed.
Lemma D_5fe08 : decode_any W_5fe08 = Some (ShiftImm ALU_SRL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe0c : bv 32 := 0x06a5f663.
Lemma F_5fe0c : fetch_word Asan.M.loaded_segments (0x5fe5c : word) = Some W_5fe0c.
Proof. vm_refl. Qed.
Lemma D_5fe0c : decode_any W_5fe0c = Some (Branch BC_GEU 11 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe10 : bv 32 := 0x000015b7.
Lemma F_5fe10 : fetch_word Asan.M.loaded_segments (0x5fe60 : word) = Some W_5fe10.
Proof. vm_refl. Qed.
Lemma D_5fe10 : decode_any W_5fe10 = Some (Lui 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe14 : bv 32 := 0x8015859b.
Lemma F_5fe14 : fetch_word Asan.M.loaded_segments (0x5fe64 : word) = Some W_5fe14.
Proof. vm_refl. Qed.
Lemma D_5fe14 : decode_any W_5fe14 = Some (OpImm32 11 11 2049, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe18 : bv 32 := 0x06b57e63.
Lemma F_5fe18 : fetch_word Asan.M.loaded_segments (0x5fe68 : word) = Some W_5fe18.
Proof. vm_refl. Qed.
Lemma D_5fe18 : decode_any W_5fe18 = Some (Branch BC_GEU 10 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe1c : bv 32 := 0xfff68593.
Lemma F_5fe1c : fetch_word Asan.M.loaded_segments (0x5fe6c : word) = Some W_5fe1c.
Proof. vm_refl. Qed.
Lemma D_5fe1c : decode_any W_5fe1c = Some (OpImm ALU_ADD 11 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe20 : bv 32 := 0x00b6f5b3.
Lemma F_5fe20 : fetch_word Asan.M.loaded_segments (0x5fe70 : word) = Some W_5fe20.
Proof. vm_refl. Qed.
Lemma D_5fe20 : decode_any W_5fe20 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe24 : bv 32 := 0x08059863.
Lemma F_5fe24 : fetch_word Asan.M.loaded_segments (0x5fe74 : word) = Some W_5fe24.
Proof. vm_refl. Qed.
Lemma D_5fe24 : decode_any W_5fe24 = Some (Branch BC_NE 11 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe28 : bv 32 := 0x40d005b3.
Lemma F_5fe28 : fetch_word Asan.M.loaded_segments (0x5fe78 : word) = Some W_5fe28.
Proof. vm_refl. Qed.
Lemma D_5fe28 : decode_any W_5fe28 = Some (Op ALU_SUB 11 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe2c : bv 32 := 0xfffb0617.
Lemma F_5fe2c : fetch_word Asan.M.loaded_segments (0x5fe7c : word) = Some W_5fe2c.
Proof. vm_refl. Qed.
Lemma D_5fe2c : decode_any W_5fe2c = Some (Auipc 12 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe30 : bv 32 := 0x5e463603.
Lemma F_5fe30 : fetch_word Asan.M.loaded_segments (0x5fe80 : word) = Some W_5fe30.
Proof. vm_refl. Qed.
Lemma D_5fe30 : decode_any W_5fe30 = Some (Load SZ8 true 12 12 1508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe34 : bv 32 := 0xfffb0717.
Lemma F_5fe34 : fetch_word Asan.M.loaded_segments (0x5fe84 : word) = Some W_5fe34.
Proof. vm_refl. Qed.
Lemma D_5fe34 : decode_any W_5fe34 = Some (Auipc 14 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe38 : bv 32 := 0x00b6f5b3.
Lemma F_5fe38 : fetch_word Asan.M.loaded_segments (0x5fe88 : word) = Some W_5fe38.
Proof. vm_refl. Qed.
Lemma D_5fe38 : decode_any W_5fe38 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe3c : bv 32 := 0x75470713.
Lemma F_5fe3c : fetch_word Asan.M.loaded_segments (0x5fe8c : word) = Some W_5fe3c.
Proof. vm_refl. Qed.
Lemma D_5fe3c : decode_any W_5fe3c = Some (OpImm ALU_ADD 14 14 1876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe40 : bv 32 := 0x02c585b3.
Lemma F_5fe40 : fetch_word Asan.M.loaded_segments (0x5fe90 : word) = Some W_5fe40.
Proof. vm_refl. Qed.
Lemma D_5fe40 : decode_any W_5fe40 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe44 : bv 32 := 0x03a5d593.
Lemma F_5fe44 : fetch_word Asan.M.loaded_segments (0x5fe94 : word) = Some W_5fe44.
Proof. vm_refl. Qed.
Lemma D_5fe44 : decode_any W_5fe44 = Some (ShiftImm ALU_SRL 11 11 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe48 : bv 32 := 0x00b705b3.
Lemma F_5fe48 : fetch_word Asan.M.loaded_segments (0x5fe98 : word) = Some W_5fe48.
Proof. vm_refl. Qed.
Lemma D_5fe48 : decode_any W_5fe48 = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe4c : bv 32 := 0x0005c603.
Lemma F_5fe4c : fetch_word Asan.M.loaded_segments (0x5fe9c : word) = Some W_5fe4c.
Proof. vm_refl. Qed.
Lemma D_5fe4c : decode_any W_5fe4c = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe50 : bv 32 := 0xffc60593.
Lemma F_5fe50 : fetch_word Asan.M.loaded_segments (0x5fea0 : word) = Some W_5fe50.
Proof. vm_refl. Qed.
Lemma D_5fe50 : decode_any W_5fe50 = Some (OpImm ALU_ADD 11 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe54 : bv 32 := 0x00800713.
Lemma F_5fe54 : fetch_word Asan.M.loaded_segments (0x5fea4 : word) = Some W_5fe54.
Proof. vm_refl. Qed.
Lemma D_5fe54 : decode_any W_5fe54 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe58 : bv 32 := 0x06e5fe63.
Lemma F_5fe58 : fetch_word Asan.M.loaded_segments (0x5fea8 : word) = Some W_5fe58.
Proof. vm_refl. Qed.
Lemma D_5fe58 : decode_any W_5fe58 = Some (Branch BC_GEU 11 14 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe5c : bv 32 := 0x00100713.
Lemma F_5fe5c : fetch_word Asan.M.loaded_segments (0x5feac : word) = Some W_5fe5c.
Proof. vm_refl. Qed.
Lemma D_5fe5c : decode_any W_5fe5c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe60 : bv 32 := 0x00c7173b.
Lemma F_5fe60 : fetch_word Asan.M.loaded_segments (0x5feb0 : word) = Some W_5fe60.
Proof. vm_refl. Qed.
Lemma D_5fe60 : decode_any W_5fe60 = Some (Op32 ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe64 : bv 32 := 0x08e51a63.
Lemma F_5fe64 : fetch_word Asan.M.loaded_segments (0x5feb4 : word) = Some W_5fe64.
Proof. vm_refl. Qed.
Lemma D_5fe64 : decode_any W_5fe64 = Some (Branch BC_NE 10 14 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe68 : bv 32 := 0x00058513.
Lemma F_5fe68 : fetch_word Asan.M.loaded_segments (0x5feb8 : word) = Some W_5fe68.
Proof. vm_refl. Qed.
Lemma D_5fe68 : decode_any W_5fe68 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe6c : bv 32 := 0x00813083.
Lemma F_5fe6c : fetch_word Asan.M.loaded_segments (0x5febc : word) = Some W_5fe6c.
Proof. vm_refl. Qed.
Lemma D_5fe6c : decode_any W_5fe6c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe70 : bv 32 := 0x01010113.
Lemma F_5fe70 : fetch_word Asan.M.loaded_segments (0x5fec0 : word) = Some W_5fe70.
Proof. vm_refl. Qed.
Lemma D_5fe70 : decode_any W_5fe70 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5fe74 : bv 32 := 0x00008067.
Lemma F_5fe74 : fetch_word Asan.M.loaded_segments (0x5fec4 : word) = Some W_5fe74.
Proof. vm_refl. Qed.
Lemma D_5fe74 : decode_any W_5fe74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

