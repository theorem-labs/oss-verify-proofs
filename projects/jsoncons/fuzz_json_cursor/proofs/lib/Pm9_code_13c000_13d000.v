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

Definition W_13cd90 : bv 32 := 0x0284b503.
Lemma F_13cd90 : fetch_word AsanUbsan.M.loaded_segments (0x13cdcc : word) = Some W_13cd90.
Proof. vm_refl. Qed.
Lemma D_13cd90 : decode_any W_13cd90 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cd94 : bv 32 := 0x0384b603.
Lemma F_13cd94 : fetch_word AsanUbsan.M.loaded_segments (0x13cdd0 : word) = Some W_13cd94.
Proof. vm_refl. Qed.
Lemma D_13cd94 : decode_any W_13cd94 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cd98 : bv 32 := 0x40c50b33.
Lemma F_13cd98 : fetch_word AsanUbsan.M.loaded_segments (0x13cdd4 : word) = Some W_13cd98.
Proof. vm_refl. Qed.
Lemma D_13cd98 : decode_any W_13cd98 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cd9c : bv 32 := 0x00c546b3.
Lemma F_13cd9c : fetch_word AsanUbsan.M.loaded_segments (0x13cdd8 : word) = Some W_13cd9c.
Proof. vm_refl. Qed.
Lemma D_13cd9c : decode_any W_13cd9c = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cda0 : bv 32 := 0x00c13423.
Lemma F_13cda0 : fetch_word AsanUbsan.M.loaded_segments (0x13cddc : word) = Some W_13cda0.
Proof. vm_refl. Qed.
Lemma D_13cda0 : decode_any W_13cda0 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cda4 : bv 32 := 0x01613823.
Lemma F_13cda4 : fetch_word AsanUbsan.M.loaded_segments (0x13cde0 : word) = Some W_13cda4.
Proof. vm_refl. Qed.
Lemma D_13cda4 : decode_any W_13cda4 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cda8 : bv 32 := 0x00b13c23.
Lemma F_13cda8 : fetch_word AsanUbsan.M.loaded_segments (0x13cde4 : word) = Some W_13cda8.
Proof. vm_refl. Qed.
Lemma D_13cda8 : decode_any W_13cda8 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdac : bv 32 := 0x02813023.
Lemma F_13cdac : fetch_word AsanUbsan.M.loaded_segments (0x13cde8 : word) = Some W_13cdac.
Proof. vm_refl. Qed.
Lemma D_13cdac : decode_any W_13cdac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdb0 : bv 32 := 0x008b0b33.
Lemma F_13cdb0 : fetch_word AsanUbsan.M.loaded_segments (0x13cdec : word) = Some W_13cdb0.
Proof. vm_refl. Qed.
Lemma D_13cdb0 : decode_any W_13cdb0 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdb4 : bv 32 := 0x00d03933.
Lemma F_13cdb4 : fetch_word AsanUbsan.M.loaded_segments (0x13cdf0 : word) = Some W_13cdb4.
Proof. vm_refl. Qed.
Lemma D_13cdb4 : decode_any W_13cdb4 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdb8 : bv 32 := 0x00c50663.
Lemma F_13cdb8 : fetch_word AsanUbsan.M.loaded_segments (0x13cdf4 : word) = Some W_13cdb8.
Proof. vm_refl. Qed.
Lemma D_13cdb8 : decode_any W_13cdb8 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdbc : bv 32 := 0x00810993.
Lemma F_13cdbc : fetch_word AsanUbsan.M.loaded_segments (0x13cdf8 : word) = Some W_13cdbc.
Proof. vm_refl. Qed.
Lemma D_13cdbc : decode_any W_13cdbc = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdc0 : bv 32 := 0x0080006f.
Lemma F_13cdc0 : fetch_word AsanUbsan.M.loaded_segments (0x13cdfc : word) = Some W_13cdc0.
Proof. vm_refl. Qed.
Lemma D_13cdc0 : decode_any W_13cdc0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdc4 : bv 32 := 0x01810993.
Lemma F_13cdc4 : fetch_word AsanUbsan.M.loaded_segments (0x13ce00 : word) = Some W_13cdc4.
Proof. vm_refl. Qed.
Lemma D_13cdc4 : decode_any W_13cdc4 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdc8 : bv 32 := 0x0784a503.
Lemma F_13cdc8 : fetch_word AsanUbsan.M.loaded_segments (0x13ce04 : word) = Some W_13cdc8.
Proof. vm_refl. Qed.
Lemma D_13cdc8 : decode_any W_13cdc8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdcc : bv 32 := 0x00190913.
Lemma F_13cdcc : fetch_word AsanUbsan.M.loaded_segments (0x13ce08 : word) = Some W_13cdcc.
Proof. vm_refl. Qed.
Lemma D_13cdcc : decode_any W_13cdcc = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdd0 : bv 32 := 0x04200893.
Lemma F_13cdd0 : fetch_word AsanUbsan.M.loaded_segments (0x13ce0c : word) = Some W_13cdd0.
Proof. vm_refl. Qed.
Lemma D_13cdd0 : decode_any W_13cdd0 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdd4 : bv 32 := 0x00098593.
Lemma F_13cdd4 : fetch_word AsanUbsan.M.loaded_segments (0x13ce10 : word) = Some W_13cdd4.
Proof. vm_refl. Qed.
Lemma D_13cdd4 : decode_any W_13cdd4 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdd8 : bv 32 := 0x00090613.
Lemma F_13cdd8 : fetch_word AsanUbsan.M.loaded_segments (0x13ce14 : word) = Some W_13cdd8.
Proof. vm_refl. Qed.
Lemma D_13cdd8 : decode_any W_13cdd8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cde0 : bv 32 := 0x8d1f80ef.
Lemma F_13cde0 : fetch_word AsanUbsan.M.loaded_segments (0x13ce1c : word) = Some W_13cde0.
Proof. vm_refl. Qed.
Lemma D_13cde0 : decode_any W_13cde0 = Some (Jal 1 2066640, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cde4 : bv 32 := 0x09651863.
Lemma F_13cde4 : fetch_word AsanUbsan.M.loaded_segments (0x13ce20 : word) = Some W_13cde4.
Proof. vm_refl. Qed.
Lemma D_13cde4 : decode_any W_13cde4 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce38 : bv 32 := 0x00800713.
Lemma F_13ce38 : fetch_word AsanUbsan.M.loaded_segments (0x13ce74 : word) = Some W_13ce38.
Proof. vm_refl. Qed.
Lemma D_13ce38 : decode_any W_13ce38 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce3c : bv 32 := 0x000a0593.
Lemma F_13ce3c : fetch_word AsanUbsan.M.loaded_segments (0x13ce78 : word) = Some W_13ce3c.
Proof. vm_refl. Qed.
Lemma D_13ce3c : decode_any W_13ce3c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce40 : bv 32 := 0x00e98733.
Lemma F_13ce40 : fetch_word AsanUbsan.M.loaded_segments (0x13ce7c : word) = Some W_13ce40.
Proof. vm_refl. Qed.
Lemma D_13ce40 : decode_any W_13ce40 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce44 : bv 32 := 0x00073783.
Lemma F_13ce44 : fetch_word AsanUbsan.M.loaded_segments (0x13ce80 : word) = Some W_13ce44.
Proof. vm_refl. Qed.
Lemma D_13ce44 : decode_any W_13ce44 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce48 : bv 32 := 0x40ab0b33.
Lemma F_13ce48 : fetch_word AsanUbsan.M.loaded_segments (0x13ce84 : word) = Some W_13ce48.
Proof. vm_refl. Qed.
Lemma D_13ce48 : decode_any W_13ce48 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce4c : bv 32 := 0x0784a503.
Lemma F_13ce4c : fetch_word AsanUbsan.M.loaded_segments (0x13ce88 : word) = Some W_13ce4c.
Proof. vm_refl. Qed.
Lemma D_13ce4c : decode_any W_13ce4c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce50 : bv 32 := 0x40c9093b.
Lemma F_13ce50 : fetch_word AsanUbsan.M.loaded_segments (0x13ce8c : word) = Some W_13ce50.
Proof. vm_refl. Qed.
Lemma D_13ce50 : decode_any W_13ce50 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce54 : bv 32 := 0x40d787b3.
Lemma F_13ce54 : fetch_word AsanUbsan.M.loaded_segments (0x13ce90 : word) = Some W_13ce54.
Proof. vm_refl. Qed.
Lemma D_13ce54 : decode_any W_13ce54 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce58 : bv 32 := 0x00f73023.
Lemma F_13ce58 : fetch_word AsanUbsan.M.loaded_segments (0x13ce94 : word) = Some W_13ce58.
Proof. vm_refl. Qed.
Lemma D_13ce58 : decode_any W_13ce58 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce5c : bv 32 := 0x04200893.
Lemma F_13ce5c : fetch_word AsanUbsan.M.loaded_segments (0x13ce98 : word) = Some W_13ce5c.
Proof. vm_refl. Qed.
Lemma D_13ce5c : decode_any W_13ce5c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce60 : bv 32 := 0x00090613.
Lemma F_13ce60 : fetch_word AsanUbsan.M.loaded_segments (0x13ce9c : word) = Some W_13ce60.
Proof. vm_refl. Qed.
Lemma D_13ce60 : decode_any W_13ce60 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce68 : bv 32 := 0x849f80ef.
Lemma F_13ce68 : fetch_word AsanUbsan.M.loaded_segments (0x13cea4 : word) = Some W_13ce68.
Proof. vm_refl. Qed.
Lemma D_13ce68 : decode_any W_13ce68 = Some (Jal 1 2066504, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce6c : bv 32 := 0x000a0993.
Lemma F_13ce6c : fetch_word AsanUbsan.M.loaded_segments (0x13cea8 : word) = Some W_13ce6c.
Proof. vm_refl. Qed.
Lemma D_13ce6c : decode_any W_13ce6c = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce70 : bv 32 := 0xf7650ce3.
Lemma F_13ce70 : fetch_word AsanUbsan.M.loaded_segments (0x13ceac : word) = Some W_13ce70.
Proof. vm_refl. Qed.
Lemma D_13ce70 : decode_any W_13ce70 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce74 : bv 32 := 0x02054c63.
Lemma F_13ce74 : fetch_word AsanUbsan.M.loaded_segments (0x13ceb0 : word) = Some W_13ce74.
Proof. vm_refl. Qed.
Lemma D_13ce74 : decode_any W_13ce74 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce78 : bv 32 := 0x0089b583.
Lemma F_13ce78 : fetch_word AsanUbsan.M.loaded_segments (0x13ceb4 : word) = Some W_13ce78.
Proof. vm_refl. Qed.
Lemma D_13ce78 : decode_any W_13ce78 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce7c : bv 32 := 0x00a5b633.
Lemma F_13ce7c : fetch_word AsanUbsan.M.loaded_segments (0x13ceb8 : word) = Some W_13ce7c.
Proof. vm_refl. Qed.
Lemma D_13ce7c : decode_any W_13ce7c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce80 : bv 32 := 0x00461a13.
Lemma F_13ce80 : fetch_word AsanUbsan.M.loaded_segments (0x13cebc : word) = Some W_13ce80.
Proof. vm_refl. Qed.
Lemma D_13ce80 : decode_any W_13ce80 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce84 : bv 32 := 0x01498a33.
Lemma F_13ce84 : fetch_word AsanUbsan.M.loaded_segments (0x13cec0 : word) = Some W_13ce84.
Proof. vm_refl. Qed.
Lemma D_13ce84 : decode_any W_13ce84 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce88 : bv 32 := 0x000a3703.
Lemma F_13ce88 : fetch_word AsanUbsan.M.loaded_segments (0x13cec4 : word) = Some W_13ce88.
Proof. vm_refl. Qed.
Lemma D_13ce88 : decode_any W_13ce88 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce8c : bv 32 := 0x40c006b3.
Lemma F_13ce8c : fetch_word AsanUbsan.M.loaded_segments (0x13cec8 : word) = Some W_13ce8c.
Proof. vm_refl. Qed.
Lemma D_13ce8c : decode_any W_13ce8c = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce90 : bv 32 := 0x00b6f6b3.
Lemma F_13ce90 : fetch_word AsanUbsan.M.loaded_segments (0x13cecc : word) = Some W_13ce90.
Proof. vm_refl. Qed.
Lemma D_13ce90 : decode_any W_13ce90 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce94 : bv 32 := 0x40d506b3.
Lemma F_13ce94 : fetch_word AsanUbsan.M.loaded_segments (0x13ced0 : word) = Some W_13ce94.
Proof. vm_refl. Qed.
Lemma D_13ce94 : decode_any W_13ce94 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce98 : bv 32 := 0x00d70733.
Lemma F_13ce98 : fetch_word AsanUbsan.M.loaded_segments (0x13ced4 : word) = Some W_13ce98.
Proof. vm_refl. Qed.
Lemma D_13ce98 : decode_any W_13ce98 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce9c : bv 32 := 0x00ea3023.
Lemma F_13ce9c : fetch_word AsanUbsan.M.loaded_segments (0x13ced8 : word) = Some W_13ce9c.
Proof. vm_refl. Qed.
Lemma D_13ce9c : decode_any W_13ce9c = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cea0 : bv 32 := 0xf8a5fce3.
Lemma F_13cea0 : fetch_word AsanUbsan.M.loaded_segments (0x13cedc : word) = Some W_13cea0.
Proof. vm_refl. Qed.
Lemma D_13cea0 : decode_any W_13cea0 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cea4 : bv 32 := 0x01800713.
Lemma F_13cea4 : fetch_word AsanUbsan.M.loaded_segments (0x13cee0 : word) = Some W_13cea4.
Proof. vm_refl. Qed.
Lemma D_13cea4 : decode_any W_13cea4 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cea8 : bv 32 := 0xf95ff06f.
Lemma F_13cea8 : fetch_word AsanUbsan.M.loaded_segments (0x13cee4 : word) = Some W_13cea8.
Proof. vm_refl. Qed.
Lemma D_13cea8 : decode_any W_13cea8 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

