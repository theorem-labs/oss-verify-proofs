(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_14cd88 : bv 32 := 0x0284b503.
Lemma F_14cd88 : fetch_word AsanUbsan.M.loaded_segments (0x14cdc4 : word) = Some W_14cd88.
Proof. vm_refl. Qed.
Lemma D_14cd88 : decode_any W_14cd88 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd8c : bv 32 := 0x0384b603.
Lemma F_14cd8c : fetch_word AsanUbsan.M.loaded_segments (0x14cdc8 : word) = Some W_14cd8c.
Proof. vm_refl. Qed.
Lemma D_14cd8c : decode_any W_14cd8c = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd90 : bv 32 := 0x40c50b33.
Lemma F_14cd90 : fetch_word AsanUbsan.M.loaded_segments (0x14cdcc : word) = Some W_14cd90.
Proof. vm_refl. Qed.
Lemma D_14cd90 : decode_any W_14cd90 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd94 : bv 32 := 0x00c546b3.
Lemma F_14cd94 : fetch_word AsanUbsan.M.loaded_segments (0x14cdd0 : word) = Some W_14cd94.
Proof. vm_refl. Qed.
Lemma D_14cd94 : decode_any W_14cd94 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd98 : bv 32 := 0x00c13423.
Lemma F_14cd98 : fetch_word AsanUbsan.M.loaded_segments (0x14cdd4 : word) = Some W_14cd98.
Proof. vm_refl. Qed.
Lemma D_14cd98 : decode_any W_14cd98 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cd9c : bv 32 := 0x01613823.
Lemma F_14cd9c : fetch_word AsanUbsan.M.loaded_segments (0x14cdd8 : word) = Some W_14cd9c.
Proof. vm_refl. Qed.
Lemma D_14cd9c : decode_any W_14cd9c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cda0 : bv 32 := 0x00b13c23.
Lemma F_14cda0 : fetch_word AsanUbsan.M.loaded_segments (0x14cddc : word) = Some W_14cda0.
Proof. vm_refl. Qed.
Lemma D_14cda0 : decode_any W_14cda0 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cda4 : bv 32 := 0x02813023.
Lemma F_14cda4 : fetch_word AsanUbsan.M.loaded_segments (0x14cde0 : word) = Some W_14cda4.
Proof. vm_refl. Qed.
Lemma D_14cda4 : decode_any W_14cda4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cda8 : bv 32 := 0x008b0b33.
Lemma F_14cda8 : fetch_word AsanUbsan.M.loaded_segments (0x14cde4 : word) = Some W_14cda8.
Proof. vm_refl. Qed.
Lemma D_14cda8 : decode_any W_14cda8 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdac : bv 32 := 0x00d03933.
Lemma F_14cdac : fetch_word AsanUbsan.M.loaded_segments (0x14cde8 : word) = Some W_14cdac.
Proof. vm_refl. Qed.
Lemma D_14cdac : decode_any W_14cdac = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdb0 : bv 32 := 0x00c50663.
Lemma F_14cdb0 : fetch_word AsanUbsan.M.loaded_segments (0x14cdec : word) = Some W_14cdb0.
Proof. vm_refl. Qed.
Lemma D_14cdb0 : decode_any W_14cdb0 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdb4 : bv 32 := 0x00810993.
Lemma F_14cdb4 : fetch_word AsanUbsan.M.loaded_segments (0x14cdf0 : word) = Some W_14cdb4.
Proof. vm_refl. Qed.
Lemma D_14cdb4 : decode_any W_14cdb4 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdb8 : bv 32 := 0x0080006f.
Lemma F_14cdb8 : fetch_word AsanUbsan.M.loaded_segments (0x14cdf4 : word) = Some W_14cdb8.
Proof. vm_refl. Qed.
Lemma D_14cdb8 : decode_any W_14cdb8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdbc : bv 32 := 0x01810993.
Lemma F_14cdbc : fetch_word AsanUbsan.M.loaded_segments (0x14cdf8 : word) = Some W_14cdbc.
Proof. vm_refl. Qed.
Lemma D_14cdbc : decode_any W_14cdbc = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdc0 : bv 32 := 0x0784a503.
Lemma F_14cdc0 : fetch_word AsanUbsan.M.loaded_segments (0x14cdfc : word) = Some W_14cdc0.
Proof. vm_refl. Qed.
Lemma D_14cdc0 : decode_any W_14cdc0 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdc4 : bv 32 := 0x00190913.
Lemma F_14cdc4 : fetch_word AsanUbsan.M.loaded_segments (0x14ce00 : word) = Some W_14cdc4.
Proof. vm_refl. Qed.
Lemma D_14cdc4 : decode_any W_14cdc4 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdc8 : bv 32 := 0x04200893.
Lemma F_14cdc8 : fetch_word AsanUbsan.M.loaded_segments (0x14ce04 : word) = Some W_14cdc8.
Proof. vm_refl. Qed.
Lemma D_14cdc8 : decode_any W_14cdc8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdcc : bv 32 := 0x00098593.
Lemma F_14cdcc : fetch_word AsanUbsan.M.loaded_segments (0x14ce08 : word) = Some W_14cdcc.
Proof. vm_refl. Qed.
Lemma D_14cdcc : decode_any W_14cdcc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdd0 : bv 32 := 0x00090613.
Lemma F_14cdd0 : fetch_word AsanUbsan.M.loaded_segments (0x14ce0c : word) = Some W_14cdd0.
Proof. vm_refl. Qed.
Lemma D_14cdd0 : decode_any W_14cdd0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cdd8 : bv 32 := 0x8d1f80ef.
Lemma F_14cdd8 : fetch_word AsanUbsan.M.loaded_segments (0x14ce14 : word) = Some W_14cdd8.
Proof. vm_refl. Qed.
Lemma D_14cdd8 : decode_any W_14cdd8 = Some (Jal 1 2066640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cddc : bv 32 := 0x09651863.
Lemma F_14cddc : fetch_word AsanUbsan.M.loaded_segments (0x14ce18 : word) = Some W_14cddc.
Proof. vm_refl. Qed.
Lemma D_14cddc : decode_any W_14cddc = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce30 : bv 32 := 0x00800713.
Lemma F_14ce30 : fetch_word AsanUbsan.M.loaded_segments (0x14ce6c : word) = Some W_14ce30.
Proof. vm_refl. Qed.
Lemma D_14ce30 : decode_any W_14ce30 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce34 : bv 32 := 0x000a0593.
Lemma F_14ce34 : fetch_word AsanUbsan.M.loaded_segments (0x14ce70 : word) = Some W_14ce34.
Proof. vm_refl. Qed.
Lemma D_14ce34 : decode_any W_14ce34 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce38 : bv 32 := 0x00e98733.
Lemma F_14ce38 : fetch_word AsanUbsan.M.loaded_segments (0x14ce74 : word) = Some W_14ce38.
Proof. vm_refl. Qed.
Lemma D_14ce38 : decode_any W_14ce38 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce3c : bv 32 := 0x00073783.
Lemma F_14ce3c : fetch_word AsanUbsan.M.loaded_segments (0x14ce78 : word) = Some W_14ce3c.
Proof. vm_refl. Qed.
Lemma D_14ce3c : decode_any W_14ce3c = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce40 : bv 32 := 0x40ab0b33.
Lemma F_14ce40 : fetch_word AsanUbsan.M.loaded_segments (0x14ce7c : word) = Some W_14ce40.
Proof. vm_refl. Qed.
Lemma D_14ce40 : decode_any W_14ce40 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce44 : bv 32 := 0x0784a503.
Lemma F_14ce44 : fetch_word AsanUbsan.M.loaded_segments (0x14ce80 : word) = Some W_14ce44.
Proof. vm_refl. Qed.
Lemma D_14ce44 : decode_any W_14ce44 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce48 : bv 32 := 0x40c9093b.
Lemma F_14ce48 : fetch_word AsanUbsan.M.loaded_segments (0x14ce84 : word) = Some W_14ce48.
Proof. vm_refl. Qed.
Lemma D_14ce48 : decode_any W_14ce48 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce4c : bv 32 := 0x40d787b3.
Lemma F_14ce4c : fetch_word AsanUbsan.M.loaded_segments (0x14ce88 : word) = Some W_14ce4c.
Proof. vm_refl. Qed.
Lemma D_14ce4c : decode_any W_14ce4c = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce50 : bv 32 := 0x00f73023.
Lemma F_14ce50 : fetch_word AsanUbsan.M.loaded_segments (0x14ce8c : word) = Some W_14ce50.
Proof. vm_refl. Qed.
Lemma D_14ce50 : decode_any W_14ce50 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce54 : bv 32 := 0x04200893.
Lemma F_14ce54 : fetch_word AsanUbsan.M.loaded_segments (0x14ce90 : word) = Some W_14ce54.
Proof. vm_refl. Qed.
Lemma D_14ce54 : decode_any W_14ce54 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce58 : bv 32 := 0x00090613.
Lemma F_14ce58 : fetch_word AsanUbsan.M.loaded_segments (0x14ce94 : word) = Some W_14ce58.
Proof. vm_refl. Qed.
Lemma D_14ce58 : decode_any W_14ce58 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce60 : bv 32 := 0x849f80ef.
Lemma F_14ce60 : fetch_word AsanUbsan.M.loaded_segments (0x14ce9c : word) = Some W_14ce60.
Proof. vm_refl. Qed.
Lemma D_14ce60 : decode_any W_14ce60 = Some (Jal 1 2066504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce64 : bv 32 := 0x000a0993.
Lemma F_14ce64 : fetch_word AsanUbsan.M.loaded_segments (0x14cea0 : word) = Some W_14ce64.
Proof. vm_refl. Qed.
Lemma D_14ce64 : decode_any W_14ce64 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce68 : bv 32 := 0xf7650ce3.
Lemma F_14ce68 : fetch_word AsanUbsan.M.loaded_segments (0x14cea4 : word) = Some W_14ce68.
Proof. vm_refl. Qed.
Lemma D_14ce68 : decode_any W_14ce68 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce6c : bv 32 := 0x02054c63.
Lemma F_14ce6c : fetch_word AsanUbsan.M.loaded_segments (0x14cea8 : word) = Some W_14ce6c.
Proof. vm_refl. Qed.
Lemma D_14ce6c : decode_any W_14ce6c = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce70 : bv 32 := 0x0089b583.
Lemma F_14ce70 : fetch_word AsanUbsan.M.loaded_segments (0x14ceac : word) = Some W_14ce70.
Proof. vm_refl. Qed.
Lemma D_14ce70 : decode_any W_14ce70 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce74 : bv 32 := 0x00a5b633.
Lemma F_14ce74 : fetch_word AsanUbsan.M.loaded_segments (0x14ceb0 : word) = Some W_14ce74.
Proof. vm_refl. Qed.
Lemma D_14ce74 : decode_any W_14ce74 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce78 : bv 32 := 0x00461a13.
Lemma F_14ce78 : fetch_word AsanUbsan.M.loaded_segments (0x14ceb4 : word) = Some W_14ce78.
Proof. vm_refl. Qed.
Lemma D_14ce78 : decode_any W_14ce78 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce7c : bv 32 := 0x01498a33.
Lemma F_14ce7c : fetch_word AsanUbsan.M.loaded_segments (0x14ceb8 : word) = Some W_14ce7c.
Proof. vm_refl. Qed.
Lemma D_14ce7c : decode_any W_14ce7c = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce80 : bv 32 := 0x000a3703.
Lemma F_14ce80 : fetch_word AsanUbsan.M.loaded_segments (0x14cebc : word) = Some W_14ce80.
Proof. vm_refl. Qed.
Lemma D_14ce80 : decode_any W_14ce80 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce84 : bv 32 := 0x40c006b3.
Lemma F_14ce84 : fetch_word AsanUbsan.M.loaded_segments (0x14cec0 : word) = Some W_14ce84.
Proof. vm_refl. Qed.
Lemma D_14ce84 : decode_any W_14ce84 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce88 : bv 32 := 0x00b6f6b3.
Lemma F_14ce88 : fetch_word AsanUbsan.M.loaded_segments (0x14cec4 : word) = Some W_14ce88.
Proof. vm_refl. Qed.
Lemma D_14ce88 : decode_any W_14ce88 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce8c : bv 32 := 0x40d506b3.
Lemma F_14ce8c : fetch_word AsanUbsan.M.loaded_segments (0x14cec8 : word) = Some W_14ce8c.
Proof. vm_refl. Qed.
Lemma D_14ce8c : decode_any W_14ce8c = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce90 : bv 32 := 0x00d70733.
Lemma F_14ce90 : fetch_word AsanUbsan.M.loaded_segments (0x14cecc : word) = Some W_14ce90.
Proof. vm_refl. Qed.
Lemma D_14ce90 : decode_any W_14ce90 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce94 : bv 32 := 0x00ea3023.
Lemma F_14ce94 : fetch_word AsanUbsan.M.loaded_segments (0x14ced0 : word) = Some W_14ce94.
Proof. vm_refl. Qed.
Lemma D_14ce94 : decode_any W_14ce94 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce98 : bv 32 := 0xf8a5fce3.
Lemma F_14ce98 : fetch_word AsanUbsan.M.loaded_segments (0x14ced4 : word) = Some W_14ce98.
Proof. vm_refl. Qed.
Lemma D_14ce98 : decode_any W_14ce98 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ce9c : bv 32 := 0x01800713.
Lemma F_14ce9c : fetch_word AsanUbsan.M.loaded_segments (0x14ced8 : word) = Some W_14ce9c.
Proof. vm_refl. Qed.
Lemma D_14ce9c : decode_any W_14ce9c = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cea0 : bv 32 := 0xf95ff06f.
Lemma F_14cea0 : fetch_word AsanUbsan.M.loaded_segments (0x14cedc : word) = Some W_14cea0.
Proof. vm_refl. Qed.
Lemma D_14cea0 : decode_any W_14cea0 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

