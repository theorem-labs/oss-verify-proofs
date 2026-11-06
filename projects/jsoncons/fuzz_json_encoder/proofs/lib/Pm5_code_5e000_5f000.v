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
Definition W_5e024 : bv 32 := 0xfd010113.
Lemma F_5e024 : fetch_word AsanUbsan.M.loaded_segments (0x5e06c : word) = Some W_5e024.
Proof. vm_refl. Qed.
Lemma D_5e024 : decode_any W_5e024 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e028 : bv 32 := 0x02113423.
Lemma F_5e028 : fetch_word AsanUbsan.M.loaded_segments (0x5e070 : word) = Some W_5e028.
Proof. vm_refl. Qed.
Lemma D_5e028 : decode_any W_5e028 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e02c : bv 32 := 0x02813023.
Lemma F_5e02c : fetch_word AsanUbsan.M.loaded_segments (0x5e074 : word) = Some W_5e02c.
Proof. vm_refl. Qed.
Lemma D_5e02c : decode_any W_5e02c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e030 : bv 32 := 0x00913c23.
Lemma F_5e030 : fetch_word AsanUbsan.M.loaded_segments (0x5e078 : word) = Some W_5e030.
Proof. vm_refl. Qed.
Lemma D_5e030 : decode_any W_5e030 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e034 : bv 32 := 0x01213823.
Lemma F_5e034 : fetch_word AsanUbsan.M.loaded_segments (0x5e07c : word) = Some W_5e034.
Proof. vm_refl. Qed.
Lemma D_5e034 : decode_any W_5e034 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e038 : bv 32 := 0x01313423.
Lemma F_5e038 : fetch_word AsanUbsan.M.loaded_segments (0x5e080 : word) = Some W_5e038.
Proof. vm_refl. Qed.
Lemma D_5e038 : decode_any W_5e038 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e03c : bv 32 := 0x0185b703.
Lemma F_5e03c : fetch_word AsanUbsan.M.loaded_segments (0x5e084 : word) = Some W_5e03c.
Proof. vm_refl. Qed.
Lemma D_5e03c : decode_any W_5e03c = Some (Load SZ8 true 14 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e040 : bv 32 := 0x00269793.
Lemma F_5e040 : fetch_word AsanUbsan.M.loaded_segments (0x5e088 : word) = Some W_5e040.
Proof. vm_refl. Qed.
Lemma D_5e040 : decode_any W_5e040 = Some (ShiftImm ALU_SLL 15 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e044 : bv 32 := 0x00100693.
Lemma F_5e044 : fetch_word AsanUbsan.M.loaded_segments (0x5e08c : word) = Some W_5e044.
Proof. vm_refl. Qed.
Lemma D_5e044 : decode_any W_5e044 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e048 : bv 32 := 0x0cf77063.
Lemma F_5e048 : fetch_word AsanUbsan.M.loaded_segments (0x5e090 : word) = Some W_5e048.
Proof. vm_refl. Qed.
Lemma D_5e048 : decode_any W_5e048 = Some (Branch BC_GEU 14 15 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e04c : bv 32 := 0x000406b7.
Lemma F_5e04c : fetch_word AsanUbsan.M.loaded_segments (0x5e094 : word) = Some W_5e04c.
Proof. vm_refl. Qed.
Lemma D_5e04c : decode_any W_5e04c = Some (Lui 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e050 : bv 32 := 0xfff6869b.
Lemma F_5e050 : fetch_word AsanUbsan.M.loaded_segments (0x5e098 : word) = Some W_5e050.
Proof. vm_refl. Qed.
Lemma D_5e050 : decode_any W_5e050 = Some (OpImm32 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e054 : bv 32 := 0x00d786b3.
Lemma F_5e054 : fetch_word AsanUbsan.M.loaded_segments (0x5e09c : word) = Some W_5e054.
Proof. vm_refl. Qed.
Lemma D_5e054 : decode_any W_5e054 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e058 : bv 32 := 0xfffc0437.
Lemma F_5e058 : fetch_word AsanUbsan.M.loaded_segments (0x5e0a0 : word) = Some W_5e058.
Proof. vm_refl. Qed.
Lemma D_5e058 : decode_any W_5e058 = Some (Lui 8 1048512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e05c : bv 32 := 0x0086f433.
Lemma F_5e05c : fetch_word AsanUbsan.M.loaded_segments (0x5e0a4 : word) = Some W_5e05c.
Proof. vm_refl. Qed.
Lemma D_5e05c : decode_any W_5e05c = Some (Op ALU_AND 8 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e060 : bv 32 := 0x200006b7.
Lemma F_5e060 : fetch_word AsanUbsan.M.loaded_segments (0x5e0a8 : word) = Some W_5e060.
Proof. vm_refl. Qed.
Lemma D_5e060 : decode_any W_5e060 = Some (Lui 13 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e064 : bv 32 := 0x0016869b.
Lemma F_5e064 : fetch_word AsanUbsan.M.loaded_segments (0x5e0ac : word) = Some W_5e064.
Proof. vm_refl. Qed.
Lemma D_5e064 : decode_any W_5e064 = Some (OpImm32 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e068 : bv 32 := 0x0cd47063.
Lemma F_5e068 : fetch_word AsanUbsan.M.loaded_segments (0x5e0b0 : word) = Some W_5e068.
Proof. vm_refl. Qed.
Lemma D_5e068 : decode_any W_5e068 = Some (Branch BC_GEU 8 13 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e06c : bv 32 := 0x03854683.
Lemma F_5e06c : fetch_word AsanUbsan.M.loaded_segments (0x5e0b4 : word) = Some W_5e06c.
Proof. vm_refl. Qed.
Lemma D_5e06c : decode_any W_5e06c = Some (Load SZ1 false 13 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e070 : bv 32 := 0x00700793.
Lemma F_5e070 : fetch_word AsanUbsan.M.loaded_segments (0x5e0b8 : word) = Some W_5e070.
Proof. vm_refl. Qed.
Lemma D_5e070 : decode_any W_5e070 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e074 : bv 32 := 0x01d79793.
Lemma F_5e074 : fetch_word AsanUbsan.M.loaded_segments (0x5e0bc : word) = Some W_5e074.
Proof. vm_refl. Qed.
Lemma D_5e074 : decode_any W_5e074 = Some (ShiftImm ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e078 : bv 32 := 0x00f60633.
Lemma F_5e078 : fetch_word AsanUbsan.M.loaded_segments (0x5e0c0 : word) = Some W_5e078.
Proof. vm_refl. Qed.
Lemma D_5e078 : decode_any W_5e078 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e07c : bv 32 := 0x00c704b3.
Lemma F_5e07c : fetch_word AsanUbsan.M.loaded_segments (0x5e0c4 : word) = Some W_5e07c.
Proof. vm_refl. Qed.
Lemma D_5e07c : decode_any W_5e07c = Some (Op ALU_ADD 9 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e080 : bv 32 := 0x02068463.
Lemma F_5e080 : fetch_word AsanUbsan.M.loaded_segments (0x5e0c8 : word) = Some W_5e080.
Proof. vm_refl. Qed.
Lemma D_5e080 : decode_any W_5e080 = Some (Branch BC_EQ 13 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0a8 : bv 32 := 0x00058993.
Lemma F_5e0a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e0f0 : word) = Some W_5e0a8.
Proof. vm_refl. Qed.
Lemma D_5e0a8 : decode_any W_5e0a8 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0ac : bv 32 := 0x40e40933.
Lemma F_5e0ac : fetch_word AsanUbsan.M.loaded_segments (0x5e0f4 : word) = Some W_5e0ac.
Proof. vm_refl. Qed.
Lemma D_5e0ac : decode_any W_5e0ac = Some (Op ALU_SUB 18 8 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0b0 : bv 32 := 0xfffbc597.
Lemma F_5e0b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e0f8 : word) = Some W_5e0b0.
Proof. vm_refl. Qed.
Lemma D_5e0b0 : decode_any W_5e0b0 = Some (Auipc 11 1048508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0b4 : bv 32 := 0x4d658693.
Lemma F_5e0b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e0fc : word) = Some W_5e0b4.
Proof. vm_refl. Qed.
Lemma D_5e0b4 : decode_any W_5e0b4 = Some (OpImm ALU_ADD 13 11 1238, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0b8 : bv 32 := 0x00048593.
Lemma F_5e0b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e100 : word) = Some W_5e0b8.
Proof. vm_refl. Qed.
Lemma D_5e0b8 : decode_any W_5e0b8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0bc : bv 32 := 0x00090613.
Lemma F_5e0bc : fetch_word AsanUbsan.M.loaded_segments (0x5e104 : word) = Some W_5e0bc.
Proof. vm_refl. Qed.
Lemma D_5e0bc : decode_any W_5e0bc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0c0 : bv 32 := 0x141400ef.
Lemma F_5e0c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e108 : word) = Some W_5e0c0.
Proof. vm_refl. Qed.
Lemma D_5e0c0 : decode_any W_5e0c0 = Some (Jal 1 264512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0c4 : bv 32 := 0x08050263.
Lemma F_5e0c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e10c : word) = Some W_5e0c4.
Proof. vm_refl. Qed.
Lemma D_5e0c4 : decode_any W_5e0c4 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0c8 : bv 32 := 0x00050713.
Lemma F_5e0c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e110 : word) = Some W_5e0c8.
Proof. vm_refl. Qed.
Lemma D_5e0c8 : decode_any W_5e0c8 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0cc : bv 32 := 0x08a49263.
Lemma F_5e0cc : fetch_word AsanUbsan.M.loaded_segments (0x5e114 : word) = Some W_5e0cc.
Proof. vm_refl. Qed.
Lemma D_5e0cc : decode_any W_5e0cc = Some (Branch BC_NE 9 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0d0 : bv 32 := 0x0fa00613.
Lemma F_5e0d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e118 : word) = Some W_5e0d0.
Proof. vm_refl. Qed.
Lemma D_5e0d0 : decode_any W_5e0d0 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0d4 : bv 32 := 0x00048513.
Lemma F_5e0d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e11c : word) = Some W_5e0d4.
Proof. vm_refl. Qed.
Lemma D_5e0d4 : decode_any W_5e0d4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0d8 : bv 32 := 0x00090593.
Lemma F_5e0d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e120 : word) = Some W_5e0d8.
Proof. vm_refl. Qed.
Lemma D_5e0d8 : decode_any W_5e0d8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0dc : bv 32 := 0x091250ef.
Lemma F_5e0dc : fetch_word AsanUbsan.M.loaded_segments (0x5e124 : word) = Some W_5e0dc.
Proof. vm_refl. Qed.
Lemma D_5e0dc : decode_any W_5e0dc = Some (Jal 1 153744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0e0 : bv 32 := 0x0052d0ef.
Lemma F_5e0e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e128 : word) = Some W_5e0e0.
Proof. vm_refl. Qed.
Lemma D_5e0e0 : decode_any W_5e0e0 = Some (Jal 1 186372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0e4 : bv 32 := 0x05053583.
Lemma F_5e0e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e12c : word) = Some W_5e0e4.
Proof. vm_refl. Qed.
Lemma D_5e0e4 : decode_any W_5e0e4 = Some (Load SZ8 true 11 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0e8 : bv 32 := 0x04853603.
Lemma F_5e0e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e130 : word) = Some W_5e0e8.
Proof. vm_refl. Qed.
Lemma D_5e0e8 : decode_any W_5e0e8 = Some (Load SZ8 true 12 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0ec : bv 32 := 0x012585b3.
Lemma F_5e0ec : fetch_word AsanUbsan.M.loaded_segments (0x5e134 : word) = Some W_5e0ec.
Proof. vm_refl. Qed.
Lemma D_5e0ec : decode_any W_5e0ec = Some (Op ALU_ADD 11 11 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0f0 : bv 32 := 0x00160613.
Lemma F_5e0f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e138 : word) = Some W_5e0f0.
Proof. vm_refl. Qed.
Lemma D_5e0f0 : decode_any W_5e0f0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0f4 : bv 32 := 0x04c53423.
Lemma F_5e0f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e13c : word) = Some W_5e0f4.
Proof. vm_refl. Qed.
Lemma D_5e0f4 : decode_any W_5e0f4 = Some (Store SZ8 10 12 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0f8 : bv 32 := 0x04b53823.
Lemma F_5e0f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e140 : word) = Some W_5e0f8.
Proof. vm_refl. Qed.
Lemma D_5e0f8 : decode_any W_5e0f8 = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e0fc : bv 32 := 0x00098593.
Lemma F_5e0fc : fetch_word AsanUbsan.M.loaded_segments (0x5e144 : word) = Some W_5e0fc.
Proof. vm_refl. Qed.
Lemma D_5e0fc : decode_any W_5e0fc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e100 : bv 32 := 0x0085bc23.
Lemma F_5e100 : fetch_word AsanUbsan.M.loaded_segments (0x5e148 : word) = Some W_5e100.
Proof. vm_refl. Qed.
Lemma D_5e100 : decode_any W_5e100 = Some (Store SZ8 11 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e104 : bv 32 := 0x00100693.
Lemma F_5e104 : fetch_word AsanUbsan.M.loaded_segments (0x5e14c : word) = Some W_5e104.
Proof. vm_refl. Qed.
Lemma D_5e104 : decode_any W_5e104 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e108 : bv 32 := 0x00068513.
Lemma F_5e108 : fetch_word AsanUbsan.M.loaded_segments (0x5e150 : word) = Some W_5e108.
Proof. vm_refl. Qed.
Lemma D_5e108 : decode_any W_5e108 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e10c : bv 32 := 0x02813083.
Lemma F_5e10c : fetch_word AsanUbsan.M.loaded_segments (0x5e154 : word) = Some W_5e10c.
Proof. vm_refl. Qed.
Lemma D_5e10c : decode_any W_5e10c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e110 : bv 32 := 0x02013403.
Lemma F_5e110 : fetch_word AsanUbsan.M.loaded_segments (0x5e158 : word) = Some W_5e110.
Proof. vm_refl. Qed.
Lemma D_5e110 : decode_any W_5e110 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e114 : bv 32 := 0x01813483.
Lemma F_5e114 : fetch_word AsanUbsan.M.loaded_segments (0x5e15c : word) = Some W_5e114.
Proof. vm_refl. Qed.
Lemma D_5e114 : decode_any W_5e114 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e118 : bv 32 := 0x01013903.
Lemma F_5e118 : fetch_word AsanUbsan.M.loaded_segments (0x5e160 : word) = Some W_5e118.
Proof. vm_refl. Qed.
Lemma D_5e118 : decode_any W_5e118 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e11c : bv 32 := 0x00813983.
Lemma F_5e11c : fetch_word AsanUbsan.M.loaded_segments (0x5e164 : word) = Some W_5e11c.
Proof. vm_refl. Qed.
Lemma D_5e11c : decode_any W_5e11c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e120 : bv 32 := 0x03010113.
Lemma F_5e120 : fetch_word AsanUbsan.M.loaded_segments (0x5e168 : word) = Some W_5e120.
Proof. vm_refl. Qed.
Lemma D_5e120 : decode_any W_5e120 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e124 : bv 32 := 0x00008067.
Lemma F_5e124 : fetch_word AsanUbsan.M.loaded_segments (0x5e16c : word) = Some W_5e124.
Proof. vm_refl. Qed.
Lemma D_5e124 : decode_any W_5e124 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1a4 : bv 32 := 0xfb010113.
Lemma F_5e1a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e1ec : word) = Some W_5e1a4.
Proof. vm_refl. Qed.
Lemma D_5e1a4 : decode_any W_5e1a4 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1a8 : bv 32 := 0x04113423.
Lemma F_5e1a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e1f0 : word) = Some W_5e1a8.
Proof. vm_refl. Qed.
Lemma D_5e1a8 : decode_any W_5e1a8 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1ac : bv 32 := 0x04813023.
Lemma F_5e1ac : fetch_word AsanUbsan.M.loaded_segments (0x5e1f4 : word) = Some W_5e1ac.
Proof. vm_refl. Qed.
Lemma D_5e1ac : decode_any W_5e1ac = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1b0 : bv 32 := 0x02913c23.
Lemma F_5e1b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e1f8 : word) = Some W_5e1b0.
Proof. vm_refl. Qed.
Lemma D_5e1b0 : decode_any W_5e1b0 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1b4 : bv 32 := 0x03213823.
Lemma F_5e1b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e1fc : word) = Some W_5e1b4.
Proof. vm_refl. Qed.
Lemma D_5e1b4 : decode_any W_5e1b4 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1b8 : bv 32 := 0x03313423.
Lemma F_5e1b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e200 : word) = Some W_5e1b8.
Proof. vm_refl. Qed.
Lemma D_5e1b8 : decode_any W_5e1b8 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1bc : bv 32 := 0x03413023.
Lemma F_5e1bc : fetch_word AsanUbsan.M.loaded_segments (0x5e204 : word) = Some W_5e1bc.
Proof. vm_refl. Qed.
Lemma D_5e1bc : decode_any W_5e1bc = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1c0 : bv 32 := 0x01513c23.
Lemma F_5e1c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e208 : word) = Some W_5e1c0.
Proof. vm_refl. Qed.
Lemma D_5e1c0 : decode_any W_5e1c0 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1c4 : bv 32 := 0x01613823.
Lemma F_5e1c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e20c : word) = Some W_5e1c4.
Proof. vm_refl. Qed.
Lemma D_5e1c4 : decode_any W_5e1c4 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1c8 : bv 32 := 0x01713423.
Lemma F_5e1c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e210 : word) = Some W_5e1c8.
Proof. vm_refl. Qed.
Lemma D_5e1c8 : decode_any W_5e1c8 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1cc : bv 32 := 0x00068a93.
Lemma F_5e1cc : fetch_word AsanUbsan.M.loaded_segments (0x5e214 : word) = Some W_5e1cc.
Proof. vm_refl. Qed.
Lemma D_5e1cc : decode_any W_5e1cc = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1d0 : bv 32 := 0x00060493.
Lemma F_5e1d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e218 : word) = Some W_5e1d0.
Proof. vm_refl. Qed.
Lemma D_5e1d0 : decode_any W_5e1d0 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1d4 : bv 32 := 0x00058413.
Lemma F_5e1d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e21c : word) = Some W_5e1d4.
Proof. vm_refl. Qed.
Lemma D_5e1d4 : decode_any W_5e1d4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1d8 : bv 32 := 0x00050993.
Lemma F_5e1d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e220 : word) = Some W_5e1d8.
Proof. vm_refl. Qed.
Lemma D_5e1d8 : decode_any W_5e1d8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1dc : bv 32 := 0x03053b03.
Lemma F_5e1dc : fetch_word AsanUbsan.M.loaded_segments (0x5e224 : word) = Some W_5e1dc.
Proof. vm_refl. Qed.
Lemma D_5e1dc : decode_any W_5e1dc = Some (Load SZ8 true 22 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1e0 : bv 32 := 0x01f00513.
Lemma F_5e1e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e228 : word) = Some W_5e1e0.
Proof. vm_refl. Qed.
Lemma D_5e1e0 : decode_any W_5e1e0 = Some (OpImm ALU_ADD 10 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1e4 : bv 32 := 0x00761593.
Lemma F_5e1e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e22c : word) = Some W_5e1e4.
Proof. vm_refl. Qed.
Lemma D_5e1e4 : decode_any W_5e1e4 = Some (ShiftImm ALU_SLL 11 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1e8 : bv 32 := 0x18a60863.
Lemma F_5e1e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e230 : word) = Some W_5e1e8.
Proof. vm_refl. Qed.
Lemma D_5e1e8 : decode_any W_5e1e8 = Some (Branch BC_EQ 12 10 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1ec : bv 32 := 0x01000513.
Lemma F_5e1ec : fetch_word AsanUbsan.M.loaded_segments (0x5e234 : word) = Some W_5e1ec.
Proof. vm_refl. Qed.
Lemma D_5e1ec : decode_any W_5e1ec = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1f0 : bv 32 := 0x00956663.
Lemma F_5e1f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e238 : word) = Some W_5e1f0.
Proof. vm_refl. Qed.
Lemma D_5e1f0 : decode_any W_5e1f0 = Some (Branch BC_LTU 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1f4 : bv 32 := 0x00549913.
Lemma F_5e1f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e23c : word) = Some W_5e1f4.
Proof. vm_refl. Qed.
Lemma D_5e1f4 : decode_any W_5e1f4 = Some (ShiftImm ALU_SLL 18 9 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1f8 : bv 32 := 0x0280006f.
Lemma F_5e1f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e240 : word) = Some W_5e1f8.
Proof. vm_refl. Qed.
Lemma D_5e1f8 : decode_any W_5e1f8 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1fc : bv 32 := 0xff048513.
Lemma F_5e1fc : fetch_word AsanUbsan.M.loaded_segments (0x5e244 : word) = Some W_5e1fc.
Proof. vm_refl. Qed.
Lemma D_5e1fc : decode_any W_5e1fc = Some (OpImm ALU_ADD 10 9 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e200 : bv 32 := 0x20000613.
Lemma F_5e200 : fetch_word AsanUbsan.M.loaded_segments (0x5e248 : word) = Some W_5e200.
Proof. vm_refl. Qed.
Lemma D_5e200 : decode_any W_5e200 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e204 : bv 32 := 0x03f49693.
Lemma F_5e204 : fetch_word AsanUbsan.M.loaded_segments (0x5e24c : word) = Some W_5e204.
Proof. vm_refl. Qed.
Lemma D_5e204 : decode_any W_5e204 = Some (ShiftImm ALU_SLL 13 9 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e208 : bv 32 := 0x00155513.
Lemma F_5e208 : fetch_word AsanUbsan.M.loaded_segments (0x5e250 : word) = Some W_5e208.
Proof. vm_refl. Qed.
Lemma D_5e208 : decode_any W_5e208 = Some (ShiftImm ALU_SRL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e20c : bv 32 := 0x00a61933.
Lemma F_5e20c : fetch_word AsanUbsan.M.loaded_segments (0x5e254 : word) = Some W_5e20c.
Proof. vm_refl. Qed.
Lemma D_5e20c : decode_any W_5e20c = Some (Op ALU_SLL 18 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e210 : bv 32 := 0x00195513.
Lemma F_5e210 : fetch_word AsanUbsan.M.loaded_segments (0x5e258 : word) = Some W_5e210.
Proof. vm_refl. Qed.
Lemma D_5e210 : decode_any W_5e210 = Some (ShiftImm ALU_SRL 10 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e214 : bv 32 := 0x43f6d693.
Lemma F_5e214 : fetch_word AsanUbsan.M.loaded_segments (0x5e25c : word) = Some W_5e214.
Proof. vm_refl. Qed.
Lemma D_5e214 : decode_any W_5e214 = Some (ShiftImm ALU_SRA 13 13 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e218 : bv 32 := 0x00a6f533.
Lemma F_5e218 : fetch_word AsanUbsan.M.loaded_segments (0x5e260 : word) = Some W_5e218.
Proof. vm_refl. Qed.
Lemma D_5e218 : decode_any W_5e218 = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e21c : bv 32 := 0x01250933.
Lemma F_5e21c : fetch_word AsanUbsan.M.loaded_segments (0x5e264 : word) = Some W_5e21c.
Proof. vm_refl. Qed.
Lemma D_5e21c : decode_any W_5e21c = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e220 : bv 32 := 0x00106517.
Lemma F_5e220 : fetch_word AsanUbsan.M.loaded_segments (0x5e268 : word) = Some W_5e220.
Proof. vm_refl. Qed.
Lemma D_5e220 : decode_any W_5e220 = Some (Auipc 10 262, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e224 : bv 32 := 0x29053a03.
Lemma F_5e224 : fetch_word AsanUbsan.M.loaded_segments (0x5e26c : word) = Some W_5e224.
Proof. vm_refl. Qed.
Lemma D_5e224 : decode_any W_5e224 = Some (Load SZ8 true 20 10 656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e228 : bv 32 := 0x000a3503.
Lemma F_5e228 : fetch_word AsanUbsan.M.loaded_segments (0x5e270 : word) = Some W_5e228.
Proof. vm_refl. Qed.
Lemma D_5e228 : decode_any W_5e228 = Some (Load SZ8 true 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e22c : bv 32 := 0x00bb0b33.
Lemma F_5e22c : fetch_word AsanUbsan.M.loaded_segments (0x5e274 : word) = Some W_5e22c.
Proof. vm_refl. Qed.
Lemma D_5e22c : decode_any W_5e22c = Some (Op ALU_ADD 22 22 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e230 : bv 32 := 0x00050a63.
Lemma F_5e230 : fetch_word AsanUbsan.M.loaded_segments (0x5e278 : word) = Some W_5e230.
Proof. vm_refl. Qed.
Lemma D_5e230 : decode_any W_5e230 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e234 : bv 32 := 0x010b3a03.
Lemma F_5e234 : fetch_word AsanUbsan.M.loaded_segments (0x5e27c : word) = Some W_5e234.
Proof. vm_refl. Qed.
Lemma D_5e234 : decode_any W_5e234 = Some (Load SZ8 true 20 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e238 : bv 32 := 0x032a05b3.
Lemma F_5e238 : fetch_word AsanUbsan.M.loaded_segments (0x5e280 : word) = Some W_5e238.
Proof. vm_refl. Qed.
Lemma D_5e238 : decode_any W_5e238 = Some (Mul M_MUL 11 20 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e23c : bv 32 := 0x00a5fe63.
Lemma F_5e23c : fetch_word AsanUbsan.M.loaded_segments (0x5e284 : word) = Some W_5e23c.
Proof. vm_refl. Qed.
Lemma D_5e23c : decode_any W_5e23c = Some (Branch BC_GEU 11 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e240 : bv 32 := 0x10c0006f.
Lemma F_5e240 : fetch_word AsanUbsan.M.loaded_segments (0x5e288 : word) = Some W_5e240.
Proof. vm_refl. Qed.
Lemma D_5e240 : decode_any W_5e240 = Some (Jal 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e258 : bv 32 := 0x050b3583.
Lemma F_5e258 : fetch_word AsanUbsan.M.loaded_segments (0x5e2a0 : word) = Some W_5e258.
Proof. vm_refl. Qed.
Lemma D_5e258 : decode_any W_5e258 = Some (Load SZ8 true 11 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e25c : bv 32 := 0x058b3603.
Lemma F_5e25c : fetch_word AsanUbsan.M.loaded_segments (0x5e2a4 : word) = Some W_5e25c.
Proof. vm_refl. Qed.
Lemma D_5e25c : decode_any W_5e25c = Some (Load SZ8 true 12 22 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e260 : bv 32 := 0x40c585b3.
Lemma F_5e260 : fetch_word AsanUbsan.M.loaded_segments (0x5e2a8 : word) = Some W_5e260.
Proof. vm_refl. Qed.
Lemma D_5e260 : decode_any W_5e260 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e264 : bv 32 := 0x032585b3.
Lemma F_5e264 : fetch_word AsanUbsan.M.loaded_segments (0x5e2ac : word) = Some W_5e264.
Proof. vm_refl. Qed.
Lemma D_5e264 : decode_any W_5e264 = Some (Mul M_MUL 11 11 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e268 : bv 32 := 0x0ea5e263.
Lemma F_5e268 : fetch_word AsanUbsan.M.loaded_segments (0x5e2b0 : word) = Some W_5e268.
Proof. vm_refl. Qed.
Lemma D_5e268 : decode_any W_5e268 = Some (Branch BC_LTU 11 10 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e26c : bv 32 := 0x020a9a63.
Lemma F_5e26c : fetch_word AsanUbsan.M.loaded_segments (0x5e2b4 : word) = Some W_5e26c.
Proof. vm_refl. Qed.
Lemma D_5e26c : decode_any W_5e26c = Some (Branch BC_NE 21 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e270 : bv 32 := 0x0289a583.
Lemma F_5e270 : fetch_word AsanUbsan.M.loaded_segments (0x5e2b8 : word) = Some W_5e270.
Proof. vm_refl. Qed.
Lemma D_5e270 : decode_any W_5e270 = Some (Load SZ4 true 11 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e274 : bv 32 := 0x0c05cc63.
Lemma F_5e274 : fetch_word AsanUbsan.M.loaded_segments (0x5e2bc : word) = Some W_5e274.
Proof. vm_refl. Qed.
Lemma D_5e274 : decode_any W_5e274 = Some (Branch BC_LT 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e34c : bv 32 := 0x04813083.
Lemma F_5e34c : fetch_word AsanUbsan.M.loaded_segments (0x5e394 : word) = Some W_5e34c.
Proof. vm_refl. Qed.
Lemma D_5e34c : decode_any W_5e34c = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e350 : bv 32 := 0x04013403.
Lemma F_5e350 : fetch_word AsanUbsan.M.loaded_segments (0x5e398 : word) = Some W_5e350.
Proof. vm_refl. Qed.
Lemma D_5e350 : decode_any W_5e350 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e354 : bv 32 := 0x03813483.
Lemma F_5e354 : fetch_word AsanUbsan.M.loaded_segments (0x5e39c : word) = Some W_5e354.
Proof. vm_refl. Qed.
Lemma D_5e354 : decode_any W_5e354 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e358 : bv 32 := 0x03013903.
Lemma F_5e358 : fetch_word AsanUbsan.M.loaded_segments (0x5e3a0 : word) = Some W_5e358.
Proof. vm_refl. Qed.
Lemma D_5e358 : decode_any W_5e358 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e35c : bv 32 := 0x02813983.
Lemma F_5e35c : fetch_word AsanUbsan.M.loaded_segments (0x5e3a4 : word) = Some W_5e35c.
Proof. vm_refl. Qed.
Lemma D_5e35c : decode_any W_5e35c = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e360 : bv 32 := 0x02013a03.
Lemma F_5e360 : fetch_word AsanUbsan.M.loaded_segments (0x5e3a8 : word) = Some W_5e360.
Proof. vm_refl. Qed.
Lemma D_5e360 : decode_any W_5e360 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e364 : bv 32 := 0x01813a83.
Lemma F_5e364 : fetch_word AsanUbsan.M.loaded_segments (0x5e3ac : word) = Some W_5e364.
Proof. vm_refl. Qed.
Lemma D_5e364 : decode_any W_5e364 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e368 : bv 32 := 0x01013b03.
Lemma F_5e368 : fetch_word AsanUbsan.M.loaded_segments (0x5e3b0 : word) = Some W_5e368.
Proof. vm_refl. Qed.
Lemma D_5e368 : decode_any W_5e368 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e36c : bv 32 := 0x00813b83.
Lemma F_5e36c : fetch_word AsanUbsan.M.loaded_segments (0x5e3b4 : word) = Some W_5e36c.
Proof. vm_refl. Qed.
Lemma D_5e36c : decode_any W_5e36c = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e370 : bv 32 := 0x05010113.
Lemma F_5e370 : fetch_word AsanUbsan.M.loaded_segments (0x5e3b8 : word) = Some W_5e370.
Proof. vm_refl. Qed.
Lemma D_5e370 : decode_any W_5e370 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e374 : bv 32 := 0x00008067.
Lemma F_5e374 : fetch_word AsanUbsan.M.loaded_segments (0x5e3bc : word) = Some W_5e374.
Proof. vm_refl. Qed.
Lemma D_5e374 : decode_any W_5e374 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

