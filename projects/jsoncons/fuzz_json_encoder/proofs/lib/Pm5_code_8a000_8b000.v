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
Definition W_8a01c : bv 32 := 0xfb010113.
Lemma F_8a01c : fetch_word AsanUbsan.M.loaded_segments (0x8a064 : word) = Some W_8a01c.
Proof. vm_refl. Qed.
Lemma D_8a01c : decode_any W_8a01c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a020 : bv 32 := 0x04113423.
Lemma F_8a020 : fetch_word AsanUbsan.M.loaded_segments (0x8a068 : word) = Some W_8a020.
Proof. vm_refl. Qed.
Lemma D_8a020 : decode_any W_8a020 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a024 : bv 32 := 0x04813023.
Lemma F_8a024 : fetch_word AsanUbsan.M.loaded_segments (0x8a06c : word) = Some W_8a024.
Proof. vm_refl. Qed.
Lemma D_8a024 : decode_any W_8a024 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a028 : bv 32 := 0x02913c23.
Lemma F_8a028 : fetch_word AsanUbsan.M.loaded_segments (0x8a070 : word) = Some W_8a028.
Proof. vm_refl. Qed.
Lemma D_8a028 : decode_any W_8a028 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a02c : bv 32 := 0x03213823.
Lemma F_8a02c : fetch_word AsanUbsan.M.loaded_segments (0x8a074 : word) = Some W_8a02c.
Proof. vm_refl. Qed.
Lemma D_8a02c : decode_any W_8a02c = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a030 : bv 32 := 0x03313423.
Lemma F_8a030 : fetch_word AsanUbsan.M.loaded_segments (0x8a078 : word) = Some W_8a030.
Proof. vm_refl. Qed.
Lemma D_8a030 : decode_any W_8a030 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a034 : bv 32 := 0x000e4517.
Lemma F_8a034 : fetch_word AsanUbsan.M.loaded_segments (0x8a07c : word) = Some W_8a034.
Proof. vm_refl. Qed.
Lemma D_8a034 : decode_any W_8a034 = Some (Auipc 10 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a038 : bv 32 := 0x41c50493.
Lemma F_8a038 : fetch_word AsanUbsan.M.loaded_segments (0x8a080 : word) = Some W_8a038.
Proof. vm_refl. Qed.
Lemma D_8a038 : decode_any W_8a038 = Some (OpImm ALU_ADD 9 10 1052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a03c : bv 32 := 0x00048503.
Lemma F_8a03c : fetch_word AsanUbsan.M.loaded_segments (0x8a084 : word) = Some W_8a03c.
Proof. vm_refl. Qed.
Lemma D_8a03c : decode_any W_8a03c = Some (Load SZ1 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a040 : bv 32 := 0x00100593.
Lemma F_8a040 : fetch_word AsanUbsan.M.loaded_segments (0x8a088 : word) = Some W_8a040.
Proof. vm_refl. Qed.
Lemma D_8a040 : decode_any W_8a040 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a044 : bv 32 := 0x0230000f.
Lemma F_8a044 : fetch_word AsanUbsan.M.loaded_segments (0x8a08c : word) = Some W_8a044.
Proof. vm_refl. Qed.
Lemma D_8a044 : decode_any W_8a044 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a048 : bv 32 := 0x10b51e63.
Lemma F_8a048 : fetch_word AsanUbsan.M.loaded_segments (0x8a090 : word) = Some W_8a048.
Proof. vm_refl. Qed.
Lemma D_8a048 : decode_any W_8a048 = Some (Branch BC_NE 10 11 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a04c : bv 32 := 0xbe1fa0ef.
Lemma F_8a04c : fetch_word AsanUbsan.M.loaded_segments (0x8a094 : word) = Some W_8a04c.
Proof. vm_refl. Qed.
Lemma D_8a04c : decode_any W_8a04c = Some (Jal 1 2075616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a050 : bv 32 := 0x0e051663.
Lemma F_8a050 : fetch_word AsanUbsan.M.loaded_segments (0x8a098 : word) = Some W_8a050.
Proof. vm_refl. Qed.
Lemma D_8a050 : decode_any W_8a050 = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a054 : bv 32 := 0xfff86517.
Lemma F_8a054 : fetch_word AsanUbsan.M.loaded_segments (0x8a09c : word) = Some W_8a054.
Proof. vm_refl. Qed.
Lemma D_8a054 : decode_any W_8a054 = Some (Auipc 10 1048454, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a058 : bv 32 := 0x3fc53403.
Lemma F_8a058 : fetch_word AsanUbsan.M.loaded_segments (0x8a0a0 : word) = Some W_8a058.
Proof. vm_refl. Qed.
Lemma D_8a058 : decode_any W_8a058 = Some (Load SZ8 true 8 10 1020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a05c : bv 32 := 0x02813023.
Lemma F_8a05c : fetch_word AsanUbsan.M.loaded_segments (0x8a0a4 : word) = Some W_8a05c.
Proof. vm_refl. Qed.
Lemma D_8a05c : decode_any W_8a05c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a060 : bv 32 := 0x00813c23.
Lemma F_8a060 : fetch_word AsanUbsan.M.loaded_segments (0x8a0a8 : word) = Some W_8a060.
Proof. vm_refl. Qed.
Lemma D_8a060 : decode_any W_8a060 = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a064 : bv 32 := 0x6b4020ef.
Lemma F_8a064 : fetch_word AsanUbsan.M.loaded_segments (0x8a0ac : word) = Some W_8a064.
Proof. vm_refl. Qed.
Lemma D_8a064 : decode_any W_8a064 = Some (Jal 1 9908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a068 : bv 32 := 0x08050263.
Lemma F_8a068 : fetch_word AsanUbsan.M.loaded_segments (0x8a0b0 : word) = Some W_8a068.
Proof. vm_refl. Qed.
Lemma D_8a068 : decode_any W_8a068 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a06c : bv 32 := 0x000da597.
Lemma F_8a06c : fetch_word AsanUbsan.M.loaded_segments (0x8a0b4 : word) = Some W_8a06c.
Proof. vm_refl. Qed.
Lemma D_8a06c : decode_any W_8a06c = Some (Auipc 11 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a070 : bv 32 := 0x4445b903.
Lemma F_8a070 : fetch_word AsanUbsan.M.loaded_segments (0x8a0b8 : word) = Some W_8a070.
Proof. vm_refl. Qed.
Lemma D_8a070 : decode_any W_8a070 = Some (Load SZ8 true 18 11 1092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a074 : bv 32 := 0x00093403.
Lemma F_8a074 : fetch_word AsanUbsan.M.loaded_segments (0x8a0bc : word) = Some W_8a074.
Proof. vm_refl. Qed.
Lemma D_8a074 : decode_any W_8a074 = Some (Load SZ8 true 8 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a078 : bv 32 := 0x00041c63.
Lemma F_8a078 : fetch_word AsanUbsan.M.loaded_segments (0x8a0c0 : word) = Some W_8a078.
Proof. vm_refl. Qed.
Lemma D_8a078 : decode_any W_8a078 = Some (Branch BC_NE 8 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a090 : bv 32 := 0x04d020ef.
Lemma F_8a090 : fetch_word AsanUbsan.M.loaded_segments (0x8a0d8 : word) = Some W_8a090.
Proof. vm_refl. Qed.
Lemma D_8a090 : decode_any W_8a090 = Some (Jal 1 10316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a094 : bv 32 := 0x00050613.
Lemma F_8a094 : fetch_word AsanUbsan.M.loaded_segments (0x8a0dc : word) = Some W_8a094.
Proof. vm_refl. Qed.
Lemma D_8a094 : decode_any W_8a094 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a098 : bv 32 := 0x00a13c23.
Lemma F_8a098 : fetch_word AsanUbsan.M.loaded_segments (0x8a0e0 : word) = Some W_8a098.
Proof. vm_refl. Qed.
Lemma D_8a098 : decode_any W_8a098 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a09c : bv 32 := 0x01010513.
Lemma F_8a09c : fetch_word AsanUbsan.M.loaded_segments (0x8a0e4 : word) = Some W_8a09c.
Proof. vm_refl. Qed.
Lemma D_8a09c : decode_any W_8a09c = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a0a0 : bv 32 := 0x40850533.
Lemma F_8a0a0 : fetch_word AsanUbsan.M.loaded_segments (0x8a0e8 : word) = Some W_8a0a0.
Proof. vm_refl. Qed.
Lemma D_8a0a0 : decode_any W_8a0a0 = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a0a4 : bv 32 := 0x408006b3.
Lemma F_8a0a4 : fetch_word AsanUbsan.M.loaded_segments (0x8a0ec : word) = Some W_8a0a4.
Proof. vm_refl. Qed.
Lemma D_8a0a4 : decode_any W_8a0a4 = Some (Op ALU_SUB 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a0a8 : bv 32 := 0x00d576b3.
Lemma F_8a0a8 : fetch_word AsanUbsan.M.loaded_segments (0x8a0f0 : word) = Some W_8a0a8.
Proof. vm_refl. Qed.
Lemma D_8a0a8 : decode_any W_8a0a8 = Some (Op ALU_AND 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a0ac : bv 32 := 0x02d13023.
Lemma F_8a0ac : fetch_word AsanUbsan.M.loaded_segments (0x8a0f4 : word) = Some W_8a0ac.
Proof. vm_refl. Qed.
Lemma D_8a0ac : decode_any W_8a0ac = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a0b0 : bv 32 := 0x40d60733.
Lemma F_8a0b0 : fetch_word AsanUbsan.M.loaded_segments (0x8a0f8 : word) = Some W_8a0b0.
Proof. vm_refl. Qed.
Lemma D_8a0b0 : decode_any W_8a0b0 = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a0b4 : bv 32 := 0x04000537.
Lemma F_8a0b4 : fetch_word AsanUbsan.M.loaded_segments (0x8a0fc : word) = Some W_8a0b4.
Proof. vm_refl. Qed.
Lemma D_8a0b4 : decode_any W_8a0b4 = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a0b8 : bv 32 := 0x0015051b.
Lemma F_8a0b8 : fetch_word AsanUbsan.M.loaded_segments (0x8a100 : word) = Some W_8a0b8.
Proof. vm_refl. Qed.
Lemma D_8a0b8 : decode_any W_8a0b8 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a0bc : bv 32 := 0x06a76263.
Lemma F_8a0bc : fetch_word AsanUbsan.M.loaded_segments (0x8a104 : word) = Some W_8a0bc.
Proof. vm_refl. Qed.
Lemma D_8a0bc : decode_any W_8a0bc = Some (Branch BC_LTU 14 10 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a120 : bv 32 := 0x00770713.
Lemma F_8a120 : fetch_word AsanUbsan.M.loaded_segments (0x8a168 : word) = Some W_8a120.
Proof. vm_refl. Qed.
Lemma D_8a120 : decode_any W_8a120 = Some (OpImm ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a124 : bv 32 := 0x10000537.
Lemma F_8a124 : fetch_word AsanUbsan.M.loaded_segments (0x8a16c : word) = Some W_8a124.
Proof. vm_refl. Qed.
Lemma D_8a124 : decode_any W_8a124 = Some (Lui 10 65536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a128 : bv 32 := 0xff85051b.
Lemma F_8a128 : fetch_word AsanUbsan.M.loaded_segments (0x8a170 : word) = Some W_8a128.
Proof. vm_refl. Qed.
Lemma D_8a128 : decode_any W_8a128 = Some (OpImm32 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a12c : bv 32 := 0x00a775b3.
Lemma F_8a12c : fetch_word AsanUbsan.M.loaded_segments (0x8a174 : word) = Some W_8a12c.
Proof. vm_refl. Qed.
Lemma D_8a12c : decode_any W_8a12c = Some (Op ALU_AND 11 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a130 : bv 32 := 0x00068513.
Lemma F_8a130 : fetch_word AsanUbsan.M.loaded_segments (0x8a178 : word) = Some W_8a130.
Proof. vm_refl. Qed.
Lemma D_8a130 : decode_any W_8a130 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a134 : bv 32 := 0x00000613.
Lemma F_8a134 : fetch_word AsanUbsan.M.loaded_segments (0x8a17c : word) = Some W_8a134.
Proof. vm_refl. Qed.
Lemma D_8a134 : decode_any W_8a134 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a138 : bv 32 := 0x835f90ef.
Lemma F_8a138 : fetch_word AsanUbsan.M.loaded_segments (0x8a180 : word) = Some W_8a138.
Proof. vm_refl. Qed.
Lemma D_8a138 : decode_any W_8a138 = Some (Jal 1 2070580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a13c : bv 32 := 0x5dc020ef.
Lemma F_8a13c : fetch_word AsanUbsan.M.loaded_segments (0x8a184 : word) = Some W_8a13c.
Proof. vm_refl. Qed.
Lemma D_8a13c : decode_any W_8a13c = Some (Jal 1 9692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a140 : bv 32 := 0x02050263.
Lemma F_8a140 : fetch_word AsanUbsan.M.loaded_segments (0x8a188 : word) = Some W_8a140.
Proof. vm_refl. Qed.
Lemma D_8a140 : decode_any W_8a140 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a144 : bv 32 := 0x02850583.
Lemma F_8a144 : fetch_word AsanUbsan.M.loaded_segments (0x8a18c : word) = Some W_8a144.
Proof. vm_refl. Qed.
Lemma D_8a144 : decode_any W_8a144 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a148 : bv 32 := 0x00059e63.
Lemma F_8a148 : fetch_word AsanUbsan.M.loaded_segments (0x8a190 : word) = Some W_8a148.
Proof. vm_refl. Qed.
Lemma D_8a148 : decode_any W_8a148 = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a14c : bv 32 := 0x04853503.
Lemma F_8a14c : fetch_word AsanUbsan.M.loaded_segments (0x8a194 : word) = Some W_8a14c.
Proof. vm_refl. Qed.
Lemma D_8a14c : decode_any W_8a14c = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a150 : bv 32 := 0x00253593.
Lemma F_8a150 : fetch_word AsanUbsan.M.loaded_segments (0x8a198 : word) = Some W_8a150.
Proof. vm_refl. Qed.
Lemma D_8a150 : decode_any W_8a150 = Some (OpImm ALU_SLTU 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a154 : bv 32 := 0xfff58593.
Lemma F_8a154 : fetch_word AsanUbsan.M.loaded_segments (0x8a19c : word) = Some W_8a154.
Proof. vm_refl. Qed.
Lemma D_8a154 : decode_any W_8a154 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a158 : bv 32 := 0x00a5f533.
Lemma F_8a158 : fetch_word AsanUbsan.M.loaded_segments (0x8a1a0 : word) = Some W_8a158.
Proof. vm_refl. Qed.
Lemma D_8a158 : decode_any W_8a158 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a15c : bv 32 := 0x00050463.
Lemma F_8a15c : fetch_word AsanUbsan.M.loaded_segments (0x8a1a4 : word) = Some W_8a15c.
Proof. vm_refl. Qed.
Lemma D_8a15c : decode_any W_8a15c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a160 : bv 32 := 0xc34dc0ef.
Lemma F_8a160 : fetch_word AsanUbsan.M.loaded_segments (0x8a1a8 : word) = Some W_8a160.
Proof. vm_refl. Qed.
Lemma D_8a160 : decode_any W_8a160 = Some (Jal 1 1950772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a164 : bv 32 := 0x04813083.
Lemma F_8a164 : fetch_word AsanUbsan.M.loaded_segments (0x8a1ac : word) = Some W_8a164.
Proof. vm_refl. Qed.
Lemma D_8a164 : decode_any W_8a164 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a168 : bv 32 := 0x04013403.
Lemma F_8a168 : fetch_word AsanUbsan.M.loaded_segments (0x8a1b0 : word) = Some W_8a168.
Proof. vm_refl. Qed.
Lemma D_8a168 : decode_any W_8a168 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a16c : bv 32 := 0x03813483.
Lemma F_8a16c : fetch_word AsanUbsan.M.loaded_segments (0x8a1b4 : word) = Some W_8a16c.
Proof. vm_refl. Qed.
Lemma D_8a16c : decode_any W_8a16c = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a170 : bv 32 := 0x03013903.
Lemma F_8a170 : fetch_word AsanUbsan.M.loaded_segments (0x8a1b8 : word) = Some W_8a170.
Proof. vm_refl. Qed.
Lemma D_8a170 : decode_any W_8a170 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a174 : bv 32 := 0x02813983.
Lemma F_8a174 : fetch_word AsanUbsan.M.loaded_segments (0x8a1bc : word) = Some W_8a174.
Proof. vm_refl. Qed.
Lemma D_8a174 : decode_any W_8a174 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a178 : bv 32 := 0x05010113.
Lemma F_8a178 : fetch_word AsanUbsan.M.loaded_segments (0x8a1c0 : word) = Some W_8a178.
Proof. vm_refl. Qed.
Lemma D_8a178 : decode_any W_8a178 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a17c : bv 32 := 0x00008067.
Lemma F_8a17c : fetch_word AsanUbsan.M.loaded_segments (0x8a1c4 : word) = Some W_8a17c.
Proof. vm_refl. Qed.
Lemma D_8a17c : decode_any W_8a17c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8aca0 : bv 32 := 0x000e3517.
Lemma F_8aca0 : fetch_word AsanUbsan.M.loaded_segments (0x8ace8 : word) = Some W_8aca0.
Proof. vm_refl. Qed.
Lemma D_8aca0 : decode_any W_8aca0 = Some (Auipc 10 227, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8aca4 : bv 32 := 0x7d452503.
Lemma F_8aca4 : fetch_word AsanUbsan.M.loaded_segments (0x8acec : word) = Some W_8aca4.
Proof. vm_refl. Qed.
Lemma D_8aca4 : decode_any W_8aca4 = Some (Load SZ4 true 10 10 2004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8aca8 : bv 32 := 0x0230000f.
Lemma F_8aca8 : fetch_word AsanUbsan.M.loaded_segments (0x8acf0 : word) = Some W_8aca8.
Proof. vm_refl. Qed.
Lemma D_8aca8 : decode_any W_8aca8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acac : bv 32 := 0x00008067.
Lemma F_8acac : fetch_word AsanUbsan.M.loaded_segments (0x8acf4 : word) = Some W_8acac.
Proof. vm_refl. Qed.
Lemma D_8acac : decode_any W_8acac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acb0 : bv 32 := 0xfb010113.
Lemma F_8acb0 : fetch_word AsanUbsan.M.loaded_segments (0x8acf8 : word) = Some W_8acb0.
Proof. vm_refl. Qed.
Lemma D_8acb0 : decode_any W_8acb0 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acb4 : bv 32 := 0x04113423.
Lemma F_8acb4 : fetch_word AsanUbsan.M.loaded_segments (0x8acfc : word) = Some W_8acb4.
Proof. vm_refl. Qed.
Lemma D_8acb4 : decode_any W_8acb4 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acb8 : bv 32 := 0x04813023.
Lemma F_8acb8 : fetch_word AsanUbsan.M.loaded_segments (0x8ad00 : word) = Some W_8acb8.
Proof. vm_refl. Qed.
Lemma D_8acb8 : decode_any W_8acb8 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acbc : bv 32 := 0x02913c23.
Lemma F_8acbc : fetch_word AsanUbsan.M.loaded_segments (0x8ad04 : word) = Some W_8acbc.
Proof. vm_refl. Qed.
Lemma D_8acbc : decode_any W_8acbc = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acc0 : bv 32 := 0x03213823.
Lemma F_8acc0 : fetch_word AsanUbsan.M.loaded_segments (0x8ad08 : word) = Some W_8acc0.
Proof. vm_refl. Qed.
Lemma D_8acc0 : decode_any W_8acc0 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acc4 : bv 32 := 0x03313423.
Lemma F_8acc4 : fetch_word AsanUbsan.M.loaded_segments (0x8ad0c : word) = Some W_8acc4.
Proof. vm_refl. Qed.
Lemma D_8acc4 : decode_any W_8acc4 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acc8 : bv 32 := 0x03413023.
Lemma F_8acc8 : fetch_word AsanUbsan.M.loaded_segments (0x8ad10 : word) = Some W_8acc8.
Proof. vm_refl. Qed.
Lemma D_8acc8 : decode_any W_8acc8 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8accc : bv 32 := 0x01513c23.
Lemma F_8accc : fetch_word AsanUbsan.M.loaded_segments (0x8ad14 : word) = Some W_8accc.
Proof. vm_refl. Qed.
Lemma D_8accc : decode_any W_8accc = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acd0 : bv 32 := 0x01613823.
Lemma F_8acd0 : fetch_word AsanUbsan.M.loaded_segments (0x8ad18 : word) = Some W_8acd0.
Proof. vm_refl. Qed.
Lemma D_8acd0 : decode_any W_8acd0 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acd4 : bv 32 := 0x01713423.
Lemma F_8acd4 : fetch_word AsanUbsan.M.loaded_segments (0x8ad1c : word) = Some W_8acd4.
Proof. vm_refl. Qed.
Lemma D_8acd4 : decode_any W_8acd4 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acd8 : bv 32 := 0x01813023.
Lemma F_8acd8 : fetch_word AsanUbsan.M.loaded_segments (0x8ad20 : word) = Some W_8acd8.
Proof. vm_refl. Qed.
Lemma D_8acd8 : decode_any W_8acd8 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acdc : bv 32 := 0x00078493.
Lemma F_8acdc : fetch_word AsanUbsan.M.loaded_segments (0x8ad24 : word) = Some W_8acdc.
Proof. vm_refl. Qed.
Lemma D_8acdc : decode_any W_8acdc = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ace0 : bv 32 := 0x00070a93.
Lemma F_8ace0 : fetch_word AsanUbsan.M.loaded_segments (0x8ad28 : word) = Some W_8ace0.
Proof. vm_refl. Qed.
Lemma D_8ace0 : decode_any W_8ace0 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ace4 : bv 32 := 0x00068a13.
Lemma F_8ace4 : fetch_word AsanUbsan.M.loaded_segments (0x8ad2c : word) = Some W_8ace4.
Proof. vm_refl. Qed.
Lemma D_8ace4 : decode_any W_8ace4 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ace8 : bv 32 := 0x00060413.
Lemma F_8ace8 : fetch_word AsanUbsan.M.loaded_segments (0x8ad30 : word) = Some W_8ace8.
Proof. vm_refl. Qed.
Lemma D_8ace8 : decode_any W_8ace8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acec : bv 32 := 0x00058913.
Lemma F_8acec : fetch_word AsanUbsan.M.loaded_segments (0x8ad34 : word) = Some W_8acec.
Proof. vm_refl. Qed.
Lemma D_8acec : decode_any W_8acec = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acf0 : bv 32 := 0x00050993.
Lemma F_8acf0 : fetch_word AsanUbsan.M.loaded_segments (0x8ad38 : word) = Some W_8acf0.
Proof. vm_refl. Qed.
Lemma D_8acf0 : decode_any W_8acf0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acf4 : bv 32 := 0x00052423.
Lemma F_8acf4 : fetch_word AsanUbsan.M.loaded_segments (0x8ad3c : word) = Some W_8acf4.
Proof. vm_refl. Qed.
Lemma D_8acf4 : decode_any W_8acf4 = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acf8 : bv 32 := 0xb10fe0ef.
Lemma F_8acf8 : fetch_word AsanUbsan.M.loaded_segments (0x8ad40 : word) = Some W_8acf8.
Proof. vm_refl. Qed.
Lemma D_8acf8 : decode_any W_8acf8 = Some (Jal 1 2089744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8acfc : bv 32 := 0x0c050a63.
Lemma F_8acfc : fetch_word AsanUbsan.M.loaded_segments (0x8ad44 : word) = Some W_8acfc.
Proof. vm_refl. Qed.
Lemma D_8acfc : decode_any W_8acfc = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad00 : bv 32 := 0x219010ef.
Lemma F_8ad00 : fetch_word AsanUbsan.M.loaded_segments (0x8ad48 : word) = Some W_8ad00.
Proof. vm_refl. Qed.
Lemma D_8ad00 : decode_any W_8ad00 = Some (Jal 1 6680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad04 : bv 32 := 0x04050a63.
Lemma F_8ad04 : fetch_word AsanUbsan.M.loaded_segments (0x8ad4c : word) = Some W_8ad04.
Proof. vm_refl. Qed.
Lemma D_8ad04 : decode_any W_8ad04 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad08 : bv 32 := 0x7ff50c13.
Lemma F_8ad08 : fetch_word AsanUbsan.M.loaded_segments (0x8ad50 : word) = Some W_8ad08.
Proof. vm_refl. Qed.
Lemma D_8ad08 : decode_any W_8ad08 = Some (OpImm ALU_ADD 24 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad0c : bv 32 := 0x461c4583.
Lemma F_8ad0c : fetch_word AsanUbsan.M.loaded_segments (0x8ad54 : word) = Some W_8ad0c.
Proof. vm_refl. Qed.
Lemma D_8ad0c : decode_any W_8ad0c = Some (Load SZ1 false 11 24 1121, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad10 : bv 32 := 0x00100613.
Lemma F_8ad10 : fetch_word AsanUbsan.M.loaded_segments (0x8ad58 : word) = Some W_8ad10.
Proof. vm_refl. Qed.
Lemma D_8ad10 : decode_any W_8ad10 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad14 : bv 32 := 0x46cc00a3.
Lemma F_8ad14 : fetch_word AsanUbsan.M.loaded_segments (0x8ad5c : word) = Some W_8ad14.
Proof. vm_refl. Qed.
Lemma D_8ad14 : decode_any W_8ad14 = Some (Store SZ1 24 12 1121, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad18 : bv 32 := 0x0a059a63.
Lemma F_8ad18 : fetch_word AsanUbsan.M.loaded_segments (0x8ad60 : word) = Some W_8ad18.
Proof. vm_refl. Qed.
Lemma D_8ad18 : decode_any W_8ad18 = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad1c : bv 32 := 0x00050b93.
Lemma F_8ad1c : fetch_word AsanUbsan.M.loaded_segments (0x8ad64 : word) = Some W_8ad1c.
Proof. vm_refl. Qed.
Lemma D_8ad1c : decode_any W_8ad1c = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad20 : bv 32 := 0x3bd010ef.
Lemma F_8ad20 : fetch_word AsanUbsan.M.loaded_segments (0x8ad68 : word) = Some W_8ad20.
Proof. vm_refl. Qed.
Lemma D_8ad20 : decode_any W_8ad20 = Some (Jal 1 7100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad24 : bv 32 := 0x00050b13.
Lemma F_8ad24 : fetch_word AsanUbsan.M.loaded_segments (0x8ad6c : word) = Some W_8ad24.
Proof. vm_refl. Qed.
Lemma D_8ad24 : decode_any W_8ad24 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad28 : bv 32 := 0x000b8513.
Lemma F_8ad28 : fetch_word AsanUbsan.M.loaded_segments (0x8ad70 : word) = Some W_8ad28.
Proof. vm_refl. Qed.
Lemma D_8ad28 : decode_any W_8ad28 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad2c : bv 32 := 0x409010ef.
Lemma F_8ad2c : fetch_word AsanUbsan.M.loaded_segments (0x8ad74 : word) = Some W_8ad2c.
Proof. vm_refl. Qed.
Lemma D_8ad2c : decode_any W_8ad2c = Some (Jal 1 7176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad30 : bv 32 := 0x00050813.
Lemma F_8ad30 : fetch_word AsanUbsan.M.loaded_segments (0x8ad78 : word) = Some W_8ad30.
Proof. vm_refl. Qed.
Lemma D_8ad30 : decode_any W_8ad30 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad34 : bv 32 := 0x060a8c63.
Lemma F_8ad34 : fetch_word AsanUbsan.M.loaded_segments (0x8ad7c : word) = Some W_8ad34.
Proof. vm_refl. Qed.
Lemma D_8ad34 : decode_any W_8ad34 = Some (Branch BC_EQ 21 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad38 : bv 32 := 0x00100893.
Lemma F_8ad38 : fetch_word AsanUbsan.M.loaded_segments (0x8ad80 : word) = Some W_8ad38.
Proof. vm_refl. Qed.
Lemma D_8ad38 : decode_any W_8ad38 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad3c : bv 32 := 0x00098513.
Lemma F_8ad3c : fetch_word AsanUbsan.M.loaded_segments (0x8ad84 : word) = Some W_8ad3c.
Proof. vm_refl. Qed.
Lemma D_8ad3c : decode_any W_8ad3c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad40 : bv 32 := 0x00048593.
Lemma F_8ad40 : fetch_word AsanUbsan.M.loaded_segments (0x8ad88 : word) = Some W_8ad40.
Proof. vm_refl. Qed.
Lemma D_8ad40 : decode_any W_8ad40 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad44 : bv 32 := 0x00090613.
Lemma F_8ad44 : fetch_word AsanUbsan.M.loaded_segments (0x8ad8c : word) = Some W_8ad44.
Proof. vm_refl. Qed.
Lemma D_8ad44 : decode_any W_8ad44 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad48 : bv 32 := 0x00040693.
Lemma F_8ad48 : fetch_word AsanUbsan.M.loaded_segments (0x8ad90 : word) = Some W_8ad48.
Proof. vm_refl. Qed.
Lemma D_8ad48 : decode_any W_8ad48 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad4c : bv 32 := 0x00000713.
Lemma F_8ad4c : fetch_word AsanUbsan.M.loaded_segments (0x8ad94 : word) = Some W_8ad4c.
Proof. vm_refl. Qed.
Lemma D_8ad4c : decode_any W_8ad4c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad50 : bv 32 := 0x000b0793.
Lemma F_8ad50 : fetch_word AsanUbsan.M.loaded_segments (0x8ad98 : word) = Some W_8ad50.
Proof. vm_refl. Qed.
Lemma D_8ad50 : decode_any W_8ad50 = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ad54 : bv 32 := 0x0740006f.
Lemma F_8ad54 : fetch_word AsanUbsan.M.loaded_segments (0x8ad9c : word) = Some W_8ad54.
Proof. vm_refl. Qed.
Lemma D_8ad54 : decode_any W_8ad54 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8adc8 : bv 32 := 0x018190ef.
Lemma F_8adc8 : fetch_word AsanUbsan.M.loaded_segments (0x8ae10 : word) = Some W_8adc8.
Proof. vm_refl. Qed.
Lemma D_8adc8 : decode_any W_8adc8 = Some (Jal 1 102424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8adcc : bv 32 := 0x460c00a3.
Lemma F_8adcc : fetch_word AsanUbsan.M.loaded_segments (0x8ae14 : word) = Some W_8adcc.
Proof. vm_refl. Qed.
Lemma D_8adcc : decode_any W_8adcc = Some (Store SZ1 24 0 1121, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8add0 : bv 32 := 0x04813083.
Lemma F_8add0 : fetch_word AsanUbsan.M.loaded_segments (0x8ae18 : word) = Some W_8add0.
Proof. vm_refl. Qed.
Lemma D_8add0 : decode_any W_8add0 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8add4 : bv 32 := 0x04013403.
Lemma F_8add4 : fetch_word AsanUbsan.M.loaded_segments (0x8ae1c : word) = Some W_8add4.
Proof. vm_refl. Qed.
Lemma D_8add4 : decode_any W_8add4 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8add8 : bv 32 := 0x03813483.
Lemma F_8add8 : fetch_word AsanUbsan.M.loaded_segments (0x8ae20 : word) = Some W_8add8.
Proof. vm_refl. Qed.
Lemma D_8add8 : decode_any W_8add8 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8addc : bv 32 := 0x03013903.
Lemma F_8addc : fetch_word AsanUbsan.M.loaded_segments (0x8ae24 : word) = Some W_8addc.
Proof. vm_refl. Qed.
Lemma D_8addc : decode_any W_8addc = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ade0 : bv 32 := 0x02813983.
Lemma F_8ade0 : fetch_word AsanUbsan.M.loaded_segments (0x8ae28 : word) = Some W_8ade0.
Proof. vm_refl. Qed.
Lemma D_8ade0 : decode_any W_8ade0 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ade4 : bv 32 := 0x02013a03.
Lemma F_8ade4 : fetch_word AsanUbsan.M.loaded_segments (0x8ae2c : word) = Some W_8ade4.
Proof. vm_refl. Qed.
Lemma D_8ade4 : decode_any W_8ade4 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ade8 : bv 32 := 0x01813a83.
Lemma F_8ade8 : fetch_word AsanUbsan.M.loaded_segments (0x8ae30 : word) = Some W_8ade8.
Proof. vm_refl. Qed.
Lemma D_8ade8 : decode_any W_8ade8 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8adec : bv 32 := 0x01013b03.
Lemma F_8adec : fetch_word AsanUbsan.M.loaded_segments (0x8ae34 : word) = Some W_8adec.
Proof. vm_refl. Qed.
Lemma D_8adec : decode_any W_8adec = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8adf0 : bv 32 := 0x00813b83.
Lemma F_8adf0 : fetch_word AsanUbsan.M.loaded_segments (0x8ae38 : word) = Some W_8adf0.
Proof. vm_refl. Qed.
Lemma D_8adf0 : decode_any W_8adf0 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8adf4 : bv 32 := 0x00013c03.
Lemma F_8adf4 : fetch_word AsanUbsan.M.loaded_segments (0x8ae3c : word) = Some W_8adf4.
Proof. vm_refl. Qed.
Lemma D_8adf4 : decode_any W_8adf4 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8adf8 : bv 32 := 0x05010113.
Lemma F_8adf8 : fetch_word AsanUbsan.M.loaded_segments (0x8ae40 : word) = Some W_8adf8.
Proof. vm_refl. Qed.
Lemma D_8adf8 : decode_any W_8adf8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8adfc : bv 32 := 0x00008067.
Lemma F_8adfc : fetch_word AsanUbsan.M.loaded_segments (0x8ae44 : word) = Some W_8adfc.
Proof. vm_refl. Qed.
Lemma D_8adfc : decode_any W_8adfc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

