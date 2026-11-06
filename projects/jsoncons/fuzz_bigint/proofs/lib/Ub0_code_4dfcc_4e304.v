(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_4dfcc : bv 32 := 0x00050593.
Lemma F_4dfcc : fetch_word Ubsan.M.loaded_segments (0x4dfcc : word) = Some W_4dfcc.
Proof. vm_refl. Qed.
Lemma D_4dfcc : decode_any W_4dfcc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfec : bv 32 := 0x00060463.
Lemma F_4dfec : fetch_word Ubsan.M.loaded_segments (0x4dfec : word) = Some W_4dfec.
Proof. vm_refl. Qed.
Lemma D_4dfec : decode_any W_4dfec = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dffc : bv 32 := 0xffe55803.
Lemma F_4dffc : fetch_word Ubsan.M.loaded_segments (0x4dffc : word) = Some W_4dffc.
Proof. vm_refl. Qed.
Lemma D_4dffc : decode_any W_4dffc = Some (Load SZ2 false 16 10 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e000 : bv 32 := 0x00060e63.
Lemma F_4e000 : fetch_word Ubsan.M.loaded_segments (0x4e000 : word) = Some W_4e000.
Proof. vm_refl. Qed.
Lemma D_4e000 : decode_any W_4e000 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e028 : bv 32 := 0x0104b603.
Lemma F_4e028 : fetch_word Ubsan.M.loaded_segments (0x4e028 : word) = Some W_4e028.
Proof. vm_refl. Qed.
Lemma D_4e028 : decode_any W_4e028 = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e064 : bv 32 := 0x01c4a783.
Lemma F_4e064 : fetch_word Ubsan.M.loaded_segments (0x4e064 : word) = Some W_4e064.
Proof. vm_refl. Qed.
Lemma D_4e064 : decode_any W_4e064 = Some (Load SZ4 true 15 9 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e070 : bv 32 := 0x00000023.
Lemma F_4e070 : fetch_word Ubsan.M.loaded_segments (0x4e070 : word) = Some W_4e070.
Proof. vm_refl. Qed.
Lemma D_4e070 : decode_any W_4e070 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e074 : bv 32 := 0xfffff6b7.
Lemma F_4e074 : fetch_word Ubsan.M.loaded_segments (0x4e074 : word) = Some W_4e074.
Proof. vm_refl. Qed.
Lemma D_4e074 : decode_any W_4e074 = Some (Lui 13 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e078 : bv 32 := 0x00043797.
Lemma F_4e078 : fetch_word Ubsan.M.loaded_segments (0x4e078 : word) = Some W_4e078.
Proof. vm_refl. Qed.
Lemma D_4e078 : decode_any W_4e078 = Some (Auipc 15 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e07c : bv 32 := 0x00d4f6b3.
Lemma F_4e07c : fetch_word Ubsan.M.loaded_segments (0x4e07c : word) = Some W_4e07c.
Proof. vm_refl. Qed.
Lemma D_4e07c : decode_any W_4e07c = Some (Op ALU_AND 13 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e080 : bv 32 := 0x0006b683.
Lemma F_4e080 : fetch_word Ubsan.M.loaded_segments (0x4e080 : word) = Some W_4e080.
Proof. vm_refl. Qed.
Lemma D_4e080 : decode_any W_4e080 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e084 : bv 32 := 0x1c87b783.
Lemma F_4e084 : fetch_word Ubsan.M.loaded_segments (0x4e084 : word) = Some W_4e084.
Proof. vm_refl. Qed.
Lemma D_4e084 : decode_any W_4e084 = Some (Load SZ8 true 15 15 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e088 : bv 32 := 0x00f68463.
Lemma F_4e088 : fetch_word Ubsan.M.loaded_segments (0x4e088 : word) = Some W_4e088.
Proof. vm_refl. Qed.
Lemma D_4e088 : decode_any W_4e088 = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e08c : bv 32 := 0x00000023.
Lemma F_4e08c : fetch_word Ubsan.M.loaded_segments (0x4e08c : word) = Some W_4e08c.
Proof. vm_refl. Qed.
Lemma D_4e08c : decode_any W_4e08c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e090 : bv 32 := 0x03471693.
Lemma F_4e090 : fetch_word Ubsan.M.loaded_segments (0x4e090 : word) = Some W_4e090.
Proof. vm_refl. Qed.
Lemma D_4e090 : decode_any W_4e090 = Some (ShiftImm ALU_SLL 13 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e094 : bv 32 := 0x02f00e13.
Lemma F_4e094 : fetch_word Ubsan.M.loaded_segments (0x4e094 : word) = Some W_4e094.
Proof. vm_refl. Qed.
Lemma D_4e094 : decode_any W_4e094 = Some (OpImm ALU_ADD 28 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e098 : bv 32 := 0xfffc7797.
Lemma F_4e098 : fetch_word Ubsan.M.loaded_segments (0x4e098 : word) = Some W_4e098.
Proof. vm_refl. Qed.
Lemma D_4e098 : decode_any W_4e098 = Some (Auipc 15 1048519, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e09c : bv 32 := 0x03a6d693.
Lemma F_4e09c : fetch_word Ubsan.M.loaded_segments (0x4e09c : word) = Some W_4e09c.
Proof. vm_refl. Qed.
Lemma D_4e09c : decode_any W_4e09c = Some (ShiftImm ALU_SRL 13 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a0 : bv 32 := 0x00169393.
Lemma F_4e0a0 : fetch_word Ubsan.M.loaded_segments (0x4e0a0 : word) = Some W_4e0a0.
Proof. vm_refl. Qed.
Lemma D_4e0a0 : decode_any W_4e0a0 = Some (ShiftImm ALU_SLL 7 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a4 : bv 32 := 0x43478793.
Lemma F_4e0a4 : fetch_word Ubsan.M.loaded_segments (0x4e0a4 : word) = Some W_4e0a4.
Proof. vm_refl. Qed.
Lemma D_4e0a4 : decode_any W_4e0a4 = Some (OpImm ALU_ADD 15 15 1076, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a8 : bv 32 := 0x02de6463.
Lemma F_4e0a8 : fetch_word Ubsan.M.loaded_segments (0x4e0a8 : word) = Some W_4e0a8.
Proof. vm_refl. Qed.
Lemma D_4e0a8 : decode_any W_4e0a8 = Some (Branch BC_LTU 28 13 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0ac : bv 32 := 0x00778e33.
Lemma F_4e0ac : fetch_word Ubsan.M.loaded_segments (0x4e0ac : word) = Some W_4e0ac.
Proof. vm_refl. Qed.
Lemma D_4e0ac : decode_any W_4e0ac = Some (Op ALU_ADD 28 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b0 : bv 32 := 0x000e5e03.
Lemma F_4e0b0 : fetch_word Ubsan.M.loaded_segments (0x4e0b0 : word) = Some W_4e0b0.
Proof. vm_refl. Qed.
Lemma D_4e0b0 : decode_any W_4e0b0 = Some (Load SZ2 false 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b4 : bv 32 := 0x025e0eb3.
Lemma F_4e0b4 : fetch_word Ubsan.M.loaded_segments (0x4e0b4 : word) = Some W_4e0b4.
Proof. vm_refl. Qed.
Lemma D_4e0b4 : decode_any W_4e0b4 = Some (Mul M_MUL 29 28 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b8 : bv 32 := 0x01d87463.
Lemma F_4e0b8 : fetch_word Ubsan.M.loaded_segments (0x4e0b8 : word) = Some W_4e0b8.
Proof. vm_refl. Qed.
Lemma D_4e0b8 : decode_any W_4e0b8 = Some (Branch BC_GEU 16 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0bc : bv 32 := 0x00000023.
Lemma F_4e0bc : fetch_word Ubsan.M.loaded_segments (0x4e0bc : word) = Some W_4e0bc.
Proof. vm_refl. Qed.
Lemma D_4e0bc : decode_any W_4e0bc = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0c0 : bv 32 := 0x00128e93.
Lemma F_4e0c0 : fetch_word Ubsan.M.loaded_segments (0x4e0c0 : word) = Some W_4e0c0.
Proof. vm_refl. Qed.
Lemma D_4e0c0 : decode_any W_4e0c0 = Some (OpImm ALU_ADD 29 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0c4 : bv 32 := 0x03ce8e33.
Lemma F_4e0c4 : fetch_word Ubsan.M.loaded_segments (0x4e0c4 : word) = Some W_4e0c4.
Proof. vm_refl. Qed.
Lemma D_4e0c4 : decode_any W_4e0c4 = Some (Mul M_MUL 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0c8 : bv 32 := 0x01c87863.
Lemma F_4e0c8 : fetch_word Ubsan.M.loaded_segments (0x4e0c8 : word) = Some W_4e0c8.
Proof. vm_refl. Qed.
Lemma D_4e0c8 : decode_any W_4e0c8 = Some (Branch BC_GEU 16 28 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0cc : bv 32 := 0x0100006f.
Lemma F_4e0cc : fetch_word Ubsan.M.loaded_segments (0x4e0cc : word) = Some W_4e0cc.
Proof. vm_refl. Qed.
Lemma D_4e0cc : decode_any W_4e0cc = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0d0 : bv 32 := 0x03f00e13.
Lemma F_4e0d0 : fetch_word Ubsan.M.loaded_segments (0x4e0d0 : word) = Some W_4e0d0.
Proof. vm_refl. Qed.
Lemma D_4e0d0 : decode_any W_4e0d0 = Some (OpImm ALU_ADD 28 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0d4 : bv 32 := 0x01c68463.
Lemma F_4e0d4 : fetch_word Ubsan.M.loaded_segments (0x4e0d4 : word) = Some W_4e0d4.
Proof. vm_refl. Qed.
Lemma D_4e0d4 : decode_any W_4e0d4 = Some (Branch BC_EQ 13 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0d8 : bv 32 := 0x00000023.
Lemma F_4e0d8 : fetch_word Ubsan.M.loaded_segments (0x4e0d8 : word) = Some W_4e0d8.
Proof. vm_refl. Qed.
Lemma D_4e0d8 : decode_any W_4e0d8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0dc : bv 32 := 0x00c75e13.
Lemma F_4e0dc : fetch_word Ubsan.M.loaded_segments (0x4e0dc : word) = Some W_4e0dc.
Proof. vm_refl. Qed.
Lemma D_4e0dc : decode_any W_4e0dc = Some (ShiftImm ALU_SRL 28 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0e0 : bv 32 := 0x000e0c63.
Lemma F_4e0e0 : fetch_word Ubsan.M.loaded_segments (0x4e0e0 : word) = Some W_4e0e0.
Proof. vm_refl. Qed.
Lemma D_4e0e0 : decode_any W_4e0e0 = Some (Branch BC_EQ 28 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0e4 : bv 32 := 0x008e1e13.
Lemma F_4e0e4 : fetch_word Ubsan.M.loaded_segments (0x4e0e4 : word) = Some W_4e0e4.
Proof. vm_refl. Qed.
Lemma D_4e0e4 : decode_any W_4e0e4 = Some (ShiftImm ALU_SLL 28 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0e8 : bv 32 := 0xfffe0e13.
Lemma F_4e0e8 : fetch_word Ubsan.M.loaded_segments (0x4e0e8 : word) = Some W_4e0e8.
Proof. vm_refl. Qed.
Lemma D_4e0e8 : decode_any W_4e0e8 = Some (OpImm ALU_ADD 28 28 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0ec : bv 32 := 0x010e7463.
Lemma F_4e0ec : fetch_word Ubsan.M.loaded_segments (0x4e0ec : word) = Some W_4e0ec.
Proof. vm_refl. Qed.
Lemma D_4e0ec : decode_any W_4e0ec = Some (Branch BC_GEU 28 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0f0 : bv 32 := 0x00000023.
Lemma F_4e0f0 : fetch_word Ubsan.M.loaded_segments (0x4e0f0 : word) = Some W_4e0f0.
Proof. vm_refl. Qed.
Lemma D_4e0f0 : decode_any W_4e0f0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0f4 : bv 32 := 0x1e030663.
Lemma F_4e0f4 : fetch_word Ubsan.M.loaded_segments (0x4e0f4 : word) = Some W_4e0f4.
Proof. vm_refl. Qed.
Lemma D_4e0f4 : decode_any W_4e0f4 = Some (Branch BC_EQ 6 0 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0f8 : bv 32 := 0x007783b3.
Lemma F_4e0f8 : fetch_word Ubsan.M.loaded_segments (0x4e0f8 : word) = Some W_4e0f8.
Proof. vm_refl. Qed.
Lemma D_4e0f8 : decode_any W_4e0f8 = Some (Op ALU_ADD 7 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0fc : bv 32 := 0x0003d803.
Lemma F_4e0fc : fetch_word Ubsan.M.loaded_segments (0x4e0fc : word) = Some W_4e0fc.
Proof. vm_refl. Qed.
Lemma D_4e0fc : decode_any W_4e0fc = Some (Load SZ2 false 16 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e100 : bv 32 := 0x00481813.
Lemma F_4e100 : fetch_word Ubsan.M.loaded_segments (0x4e100 : word) = Some W_4e100.
Proof. vm_refl. Qed.
Lemma D_4e100 : decode_any W_4e100 = Some (ShiftImm ALU_SLL 16 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e104 : bv 32 := 0x025802b3.
Lemma F_4e104 : fetch_word Ubsan.M.loaded_segments (0x4e104 : word) = Some W_4e104.
Proof. vm_refl. Qed.
Lemma D_4e104 : decode_any W_4e104 = Some (Mul M_MUL 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e108 : bv 32 := 0x0a000e13.
Lemma F_4e108 : fetch_word Ubsan.M.loaded_segments (0x4e108 : word) = Some W_4e108.
Proof. vm_refl. Qed.
Lemma D_4e108 : decode_any W_4e108 = Some (OpImm ALU_ADD 28 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e10c : bv 32 := 0x005602b3.
Lemma F_4e10c : fetch_word Ubsan.M.loaded_segments (0x4e10c : word) = Some W_4e10c.
Proof. vm_refl. Qed.
Lemma D_4e10c : decode_any W_4e10c = Some (Op ALU_ADD 5 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e110 : bv 32 := 0x01028313.
Lemma F_4e110 : fetch_word Ubsan.M.loaded_segments (0x4e110 : word) = Some W_4e110.
Proof. vm_refl. Qed.
Lemma D_4e110 : decode_any W_4e110 = Some (OpImm ALU_ADD 6 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e114 : bv 32 := 0x01030833.
Lemma F_4e114 : fetch_word Ubsan.M.loaded_segments (0x4e114 : word) = Some W_4e114.
Proof. vm_refl. Qed.
Lemma D_4e114 : decode_any W_4e114 = Some (Op ALU_ADD 16 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e118 : bv 32 := 0xffc80293.
Lemma F_4e118 : fetch_word Ubsan.M.loaded_segments (0x4e118 : word) = Some W_4e118.
Proof. vm_refl. Qed.
Lemma D_4e118 : decode_any W_4e118 = Some (OpImm ALU_ADD 5 16 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e11c : bv 32 := 0x0058d393.
Lemma F_4e11c : fetch_word Ubsan.M.loaded_segments (0x4e11c : word) = Some W_4e11c.
Proof. vm_refl. Qed.
Lemma D_4e11c : decode_any W_4e11c = Some (ShiftImm ALU_SRL 7 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e120 : bv 32 := 0x03c8e663.
Lemma F_4e120 : fetch_word Ubsan.M.loaded_segments (0x4e120 : word) = Some W_4e120.
Proof. vm_refl. Qed.
Lemma D_4e120 : decode_any W_4e120 = Some (Branch BC_LTU 17 28 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e124 : bv 32 := 0x00500893.
Lemma F_4e124 : fetch_word Ubsan.M.loaded_segments (0x4e124 : word) = Some W_4e124.
Proof. vm_refl. Qed.
Lemma D_4e124 : decode_any W_4e124 = Some (OpImm ALU_ADD 17 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e128 : bv 32 := 0x01138463.
Lemma F_4e128 : fetch_word Ubsan.M.loaded_segments (0x4e128 : word) = Some W_4e128.
Proof. vm_refl. Qed.
Lemma D_4e128 : decode_any W_4e128 = Some (Branch BC_EQ 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e12c : bv 32 := 0x00000023.
Lemma F_4e12c : fetch_word Ubsan.M.loaded_segments (0x4e12c : word) = Some W_4e12c.
Proof. vm_refl. Qed.
Lemma D_4e12c : decode_any W_4e12c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e130 : bv 32 := 0xff886383.
Lemma F_4e130 : fetch_word Ubsan.M.loaded_segments (0x4e130 : word) = Some W_4e130.
Proof. vm_refl. Qed.
Lemma D_4e130 : decode_any W_4e130 = Some (Load SZ4 false 7 16 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e134 : bv 32 := 0x00400893.
Lemma F_4e134 : fetch_word Ubsan.M.loaded_segments (0x4e134 : word) = Some W_4e134.
Proof. vm_refl. Qed.
Lemma D_4e134 : decode_any W_4e134 = Some (OpImm ALU_ADD 17 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e138 : bv 32 := 0x0078e463.
Lemma F_4e138 : fetch_word Ubsan.M.loaded_segments (0x4e138 : word) = Some W_4e138.
Proof. vm_refl. Qed.
Lemma D_4e138 : decode_any W_4e138 = Some (Branch BC_LTU 17 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e13c : bv 32 := 0x00000023.
Lemma F_4e13c : fetch_word Ubsan.M.loaded_segments (0x4e13c : word) = Some W_4e13c.
Proof. vm_refl. Qed.
Lemma D_4e13c : decode_any W_4e13c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e140 : bv 32 := 0xff784883.
Lemma F_4e140 : fetch_word Ubsan.M.loaded_segments (0x4e140 : word) = Some W_4e140.
Proof. vm_refl. Qed.
Lemma D_4e140 : decode_any W_4e140 = Some (Load SZ1 false 17 16 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e144 : bv 32 := 0x00088463.
Lemma F_4e144 : fetch_word Ubsan.M.loaded_segments (0x4e144 : word) = Some W_4e144.
Proof. vm_refl. Qed.
Lemma D_4e144 : decode_any W_4e144 = Some (Branch BC_EQ 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e148 : bv 32 := 0x00000023.
Lemma F_4e148 : fetch_word Ubsan.M.loaded_segments (0x4e148 : word) = Some W_4e148.
Proof. vm_refl. Qed.
Lemma D_4e148 : decode_any W_4e148 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e14c : bv 32 := 0x40a288b3.
Lemma F_4e14c : fetch_word Ubsan.M.loaded_segments (0x4e14c : word) = Some W_4e14c.
Proof. vm_refl. Qed.
Lemma D_4e14c : decode_any W_4e14c = Some (Op ALU_SUB 17 5 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e150 : bv 32 := 0x0078f463.
Lemma F_4e150 : fetch_word Ubsan.M.loaded_segments (0x4e150 : word) = Some W_4e150.
Proof. vm_refl. Qed.
Lemma D_4e150 : decode_any W_4e150 = Some (Branch BC_GEU 17 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1f0 : bv 32 := 0x07c74713.
Lemma F_4e1f0 : fetch_word Ubsan.M.loaded_segments (0x4e1f0 : word) = Some W_4e1f0.
Proof. vm_refl. Qed.
Lemma D_4e1f0 : decode_any W_4e1f0 = Some (OpImm ALU_XOR 14 14 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1f4 : bv 32 := 0x07900893.
Lemma F_4e1f4 : fetch_word Ubsan.M.loaded_segments (0x4e1f4 : word) = Some W_4e1f4.
Proof. vm_refl. Qed.
Lemma D_4e1f4 : decode_any W_4e1f4 = Some (OpImm ALU_ADD 17 0 121, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e200 : bv 32 := 0x011788b3.
Lemma F_4e200 : fetch_word Ubsan.M.loaded_segments (0x4e200 : word) = Some W_4e200.
Proof. vm_refl. Qed.
Lemma D_4e200 : decode_any W_4e200 = Some (Op ALU_ADD 17 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e204 : bv 32 := 0x0008d883.
Lemma F_4e204 : fetch_word Ubsan.M.loaded_segments (0x4e204 : word) = Some W_4e204.
Proof. vm_refl. Qed.
Lemma D_4e204 : decode_any W_4e204 = Some (Load SZ2 false 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e208 : bv 32 := 0x0f166463.
Lemma F_4e208 : fetch_word Ubsan.M.loaded_segments (0x4e208 : word) = Some W_4e208.
Proof. vm_refl. Qed.
Lemma D_4e208 : decode_any W_4e208 = Some (Branch BC_LTU 12 17 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e20c : bv 32 := 0x07a00893.
Lemma F_4e20c : fetch_word Ubsan.M.loaded_segments (0x4e20c : word) = Some W_4e20c.
Proof. vm_refl. Qed.
Lemma D_4e20c : decode_any W_4e20c = Some (OpImm ALU_ADD 17 0 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e210 : bv 32 := 0x0e40006f.
Lemma F_4e210 : fetch_word Ubsan.M.loaded_segments (0x4e210 : word) = Some W_4e210.
Proof. vm_refl. Qed.
Lemma D_4e210 : decode_any W_4e210 = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e214 : bv 32 := 0xfec3839b.
Lemma F_4e214 : fetch_word Ubsan.M.loaded_segments (0x4e214 : word) = Some W_4e214.
Proof. vm_refl. Qed.
Lemma D_4e214 : decode_any W_4e214 = Some (OpImm32 7 7 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e218 : bv 32 := 0x1075e063.
Lemma F_4e218 : fetch_word Ubsan.M.loaded_segments (0x4e218 : word) = Some W_4e218.
Proof. vm_refl. Qed.
Lemma D_4e218 : decode_any W_4e218 = Some (Branch BC_LTU 11 7 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e21c : bv 32 := 0x03000793.
Lemma F_4e21c : fetch_word Ubsan.M.loaded_segments (0x4e21c : word) = Some W_4e21c.
Proof. vm_refl. Qed.
Lemma D_4e21c : decode_any W_4e21c = Some (OpImm ALU_ADD 15 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e220 : bv 32 := 0x0ef6ec63.
Lemma F_4e220 : fetch_word Ubsan.M.loaded_segments (0x4e220 : word) = Some W_4e220.
Proof. vm_refl. Qed.
Lemma D_4e220 : decode_any W_4e220 = Some (Branch BC_LTU 13 15 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e224 : bv 32 := 0x03f00793.
Lemma F_4e224 : fetch_word Ubsan.M.loaded_segments (0x4e224 : word) = Some W_4e224.
Proof. vm_refl. Qed.
Lemma D_4e224 : decode_any W_4e224 = Some (OpImm ALU_ADD 15 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e228 : bv 32 := 0x00f68463.
Lemma F_4e228 : fetch_word Ubsan.M.loaded_segments (0x4e228 : word) = Some W_4e228.
Proof. vm_refl. Qed.
Lemma D_4e228 : decode_any W_4e228 = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e22c : bv 32 := 0x00000023.
Lemma F_4e22c : fetch_word Ubsan.M.loaded_segments (0x4e22c : word) = Some W_4e22c.
Proof. vm_refl. Qed.
Lemma D_4e22c : decode_any W_4e22c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e230 : bv 32 := 0x00001a37.
Lemma F_4e230 : fetch_word Ubsan.M.loaded_segments (0x4e230 : word) = Some W_4e230.
Proof. vm_refl. Qed.
Lemma D_4e230 : decode_any W_4e230 = Some (Lui 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e234 : bv 32 := 0x406509b3.
Lemma F_4e234 : fetch_word Ubsan.M.loaded_segments (0x4e234 : word) = Some W_4e234.
Proof. vm_refl. Qed.
Lemma D_4e234 : decode_any W_4e234 = Some (Op ALU_SUB 19 10 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e238 : bv 32 := 0xfffff6b7.
Lemma F_4e238 : fetch_word Ubsan.M.loaded_segments (0x4e238 : word) = Some W_4e238.
Proof. vm_refl. Qed.
Lemma D_4e238 : decode_any W_4e238 = Some (Lui 13 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e23c : bv 32 := 0xfffa0a1b.
Lemma F_4e23c : fetch_word Ubsan.M.loaded_segments (0x4e23c : word) = Some W_4e23c.
Proof. vm_refl. Qed.
Lemma D_4e23c : decode_any W_4e23c = Some (OpImm32 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e240 : bv 32 := 0x014587b3.
Lemma F_4e240 : fetch_word Ubsan.M.loaded_segments (0x4e240 : word) = Some W_4e240.
Proof. vm_refl. Qed.
Lemma D_4e240 : decode_any W_4e240 = Some (Op ALU_ADD 15 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e244 : bv 32 := 0x013787b3.
Lemma F_4e244 : fetch_word Ubsan.M.loaded_segments (0x4e244 : word) = Some W_4e244.
Proof. vm_refl. Qed.
Lemma D_4e244 : decode_any W_4e244 = Some (Op ALU_ADD 15 15 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2fc : bv 32 := 0x011787b3.
Lemma F_4e2fc : fetch_word Ubsan.M.loaded_segments (0x4e2fc : word) = Some W_4e2fc.
Proof. vm_refl. Qed.
Lemma D_4e2fc : decode_any W_4e2fc = Some (Op ALU_ADD 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e300 : bv 32 := 0x0007d783.
Lemma F_4e300 : fetch_word Ubsan.M.loaded_segments (0x4e300 : word) = Some W_4e300.
Proof. vm_refl. Qed.
Lemma D_4e300 : decode_any W_4e300 = Some (Load SZ2 false 15 15 0, 4%Z).
Proof. vm_refl. Qed.
