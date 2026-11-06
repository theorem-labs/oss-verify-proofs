(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_4dfcc : bv 32 := 0x02d61863.
Lemma F_4dfcc : fetch_word Plain.M.loaded_segments (0x4dfcc : word) = Some W_4dfcc.
Proof. vm_refl. Qed.
Lemma D_4dfcc : decode_any W_4dfcc = Some (Branch BC_NE 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfec : bv 32 := 0x02e5b423.
Lemma F_4dfec : fetch_word Plain.M.loaded_segments (0x4dfec : word) = Some W_4dfec.
Proof. vm_refl. Qed.
Lemma D_4dfec : decode_any W_4dfec = Some (Store SZ8 11 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dffc : bv 32 := 0x0100006f.
Lemma F_4dffc : fetch_word Plain.M.loaded_segments (0x4dffc : word) = Some W_4dffc.
Proof. vm_refl. Qed.
Lemma D_4dffc : decode_any W_4dffc = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e000 : bv 32 := 0x00058513.
Lemma F_4e000 : fetch_word Plain.M.loaded_segments (0x4e000 : word) = Some W_4e000.
Proof. vm_refl. Qed.
Lemma D_4e000 : decode_any W_4e000 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e028 : bv 32 := 0x08c48413.
Lemma F_4e028 : fetch_word Plain.M.loaded_segments (0x4e028 : word) = Some W_4e028.
Proof. vm_refl. Qed.
Lemma D_4e028 : decode_any W_4e028 = Some (OpImm ALU_ADD 8 9 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e064 : bv 32 := 0x0204b583.
Lemma F_4e064 : fetch_word Plain.M.loaded_segments (0x4e064 : word) = Some W_4e064.
Proof. vm_refl. Qed.
Lemma D_4e064 : decode_any W_4e064 = Some (Load SZ8 true 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e070 : bv 32 := 0x00150593.
Lemma F_4e070 : fetch_word Plain.M.loaded_segments (0x4e070 : word) = Some W_4e070.
Proof. vm_refl. Qed.
Lemma D_4e070 : decode_any W_4e070 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e074 : bv 32 := 0x02b4b423.
Lemma F_4e074 : fetch_word Plain.M.loaded_segments (0x4e074 : word) = Some W_4e074.
Proof. vm_refl. Qed.
Lemma D_4e074 : decode_any W_4e074 = Some (Store SZ8 9 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e078 : bv 32 := 0x01250023.
Lemma F_4e078 : fetch_word Plain.M.loaded_segments (0x4e078 : word) = Some W_4e078.
Proof. vm_refl. Qed.
Lemma D_4e078 : decode_any W_4e078 = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e07c : bv 32 := 0x0140006f.
Lemma F_4e07c : fetch_word Plain.M.loaded_segments (0x4e07c : word) = Some W_4e07c.
Proof. vm_refl. Qed.
Lemma D_4e07c : decode_any W_4e07c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e080 : bv 32 := 0x00048513.
Lemma F_4e080 : fetch_word Plain.M.loaded_segments (0x4e080 : word) = Some W_4e080.
Proof. vm_refl. Qed.
Lemma D_4e080 : decode_any W_4e080 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e084 : bv 32 := 0x00068593.
Lemma F_4e084 : fetch_word Plain.M.loaded_segments (0x4e084 : word) = Some W_4e084.
Proof. vm_refl. Qed.
Lemma D_4e084 : decode_any W_4e084 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e088 : bv 32 := 0x07c000ef.
Lemma F_4e088 : fetch_word Plain.M.loaded_segments (0x4e088 : word) = Some W_4e088.
Proof. vm_refl. Qed.
Lemma D_4e088 : decode_any W_4e088 = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e08c : bv 32 := 0x00050693.
Lemma F_4e08c : fetch_word Plain.M.loaded_segments (0x4e08c : word) = Some W_4e08c.
Proof. vm_refl. Qed.
Lemma D_4e08c : decode_any W_4e08c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e090 : bv 32 := 0x00000513.
Lemma F_4e090 : fetch_word Plain.M.loaded_segments (0x4e090 : word) = Some W_4e090.
Proof. vm_refl. Qed.
Lemma D_4e090 : decode_any W_4e090 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e094 : bv 32 := 0x00042583.
Lemma F_4e094 : fetch_word Plain.M.loaded_segments (0x4e094 : word) = Some W_4e094.
Proof. vm_refl. Qed.
Lemma D_4e094 : decode_any W_4e094 = Some (Load SZ4 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e098 : bv 32 := 0x1604262f.
Lemma F_4e098 : fetch_word Plain.M.loaded_segments (0x4e098 : word) = Some W_4e098.
Proof. vm_refl. Qed.
Lemma D_4e098 : decode_any W_4e098 = Some (Lr AW true true 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e09c : bv 32 := 0x00b61663.
Lemma F_4e09c : fetch_word Plain.M.loaded_segments (0x4e09c : word) = Some W_4e09c.
Proof. vm_refl. Qed.
Lemma D_4e09c : decode_any W_4e09c = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a0 : bv 32 := 0x1ea4272f.
Lemma F_4e0a0 : fetch_word Plain.M.loaded_segments (0x4e0a0 : word) = Some W_4e0a0.
Proof. vm_refl. Qed.
Lemma D_4e0a0 : decode_any W_4e0a0 = Some (Sc AW true true 14 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a4 : bv 32 := 0xfe071ae3.
Lemma F_4e0a4 : fetch_word Plain.M.loaded_segments (0x4e0a4 : word) = Some W_4e0a4.
Proof. vm_refl. Qed.
Lemma D_4e0a4 : decode_any W_4e0a4 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a8 : bv 32 := 0x0006061b.
Lemma F_4e0a8 : fetch_word Plain.M.loaded_segments (0x4e0a8 : word) = Some W_4e0a8.
Proof. vm_refl. Qed.
Lemma D_4e0a8 : decode_any W_4e0a8 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0ac : bv 32 := 0xfeb614e3.
Lemma F_4e0ac : fetch_word Plain.M.loaded_segments (0x4e0ac : word) = Some W_4e0ac.
Proof. vm_refl. Qed.
Lemma D_4e0ac : decode_any W_4e0ac = Some (Branch BC_NE 12 11 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b0 : bv 32 := 0x02159593.
Lemma F_4e0b0 : fetch_word Plain.M.loaded_segments (0x4e0b0 : word) = Some W_4e0b0.
Proof. vm_refl. Qed.
Lemma D_4e0b0 : decode_any W_4e0b0 = Some (ShiftImm ALU_SLL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b4 : bv 32 := 0x0205da63.
Lemma F_4e0b4 : fetch_word Plain.M.loaded_segments (0x4e0b4 : word) = Some W_4e0b4.
Proof. vm_refl. Qed.
Lemma D_4e0b4 : decode_any W_4e0b4 = Some (Branch BC_GE 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b8 : bv 32 := 0x06200893.
Lemma F_4e0b8 : fetch_word Plain.M.loaded_segments (0x4e0b8 : word) = Some W_4e0b8.
Proof. vm_refl. Qed.
Lemma D_4e0b8 : decode_any W_4e0b8 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0bc : bv 32 := 0x08100593.
Lemma F_4e0bc : fetch_word Plain.M.loaded_segments (0x4e0bc : word) = Some W_4e0bc.
Proof. vm_refl. Qed.
Lemma D_4e0bc : decode_any W_4e0bc = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0c0 : bv 32 := 0x00100613.
Lemma F_4e0c0 : fetch_word Plain.M.loaded_segments (0x4e0c0 : word) = Some W_4e0c0.
Proof. vm_refl. Qed.
Lemma D_4e0c0 : decode_any W_4e0c0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0c4 : bv 32 := 0xfda00713.
Lemma F_4e0c4 : fetch_word Plain.M.loaded_segments (0x4e0c4 : word) = Some W_4e0c4.
Proof. vm_refl. Qed.
Lemma D_4e0c4 : decode_any W_4e0c4 = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0c8 : bv 32 := 0x00040513.
Lemma F_4e0c8 : fetch_word Plain.M.loaded_segments (0x4e0c8 : word) = Some W_4e0c8.
Proof. vm_refl. Qed.
Lemma D_4e0c8 : decode_any W_4e0c8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0cc : bv 32 := 0x00000073.
Lemma F_4e0cc : fetch_word Plain.M.loaded_segments (0x4e0cc : word) = Some W_4e0cc.
Proof. vm_refl. Qed.
Lemma D_4e0cc : decode_any W_4e0cc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_4e0cc : is_ecall W_4e0cc = true.
Proof. reflexivity. Qed.

Definition W_4e0d0 : bv 32 := 0x00e51c63.
Lemma F_4e0d0 : fetch_word Plain.M.loaded_segments (0x4e0d0 : word) = Some W_4e0d0.
Proof. vm_refl. Qed.
Lemma D_4e0d0 : decode_any W_4e0d0 = Some (Branch BC_NE 10 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0d4 : bv 32 := 0x06200893.
Lemma F_4e0d4 : fetch_word Plain.M.loaded_segments (0x4e0d4 : word) = Some W_4e0d4.
Proof. vm_refl. Qed.
Lemma D_4e0d4 : decode_any W_4e0d4 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0d8 : bv 32 := 0x00100593.
Lemma F_4e0d8 : fetch_word Plain.M.loaded_segments (0x4e0d8 : word) = Some W_4e0d8.
Proof. vm_refl. Qed.
Lemma D_4e0d8 : decode_any W_4e0d8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0dc : bv 32 := 0x00100613.
Lemma F_4e0dc : fetch_word Plain.M.loaded_segments (0x4e0dc : word) = Some W_4e0dc.
Proof. vm_refl. Qed.
Lemma D_4e0dc : decode_any W_4e0dc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0e0 : bv 32 := 0x00040513.
Lemma F_4e0e0 : fetch_word Plain.M.loaded_segments (0x4e0e0 : word) = Some W_4e0e0.
Proof. vm_refl. Qed.
Lemma D_4e0e0 : decode_any W_4e0e0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0e4 : bv 32 := 0x00000073.
Lemma F_4e0e4 : fetch_word Plain.M.loaded_segments (0x4e0e4 : word) = Some W_4e0e4.
Proof. vm_refl. Qed.
Lemma D_4e0e4 : decode_any W_4e0e4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_4e0e4 : is_ecall W_4e0e4 = true.
Proof. reflexivity. Qed.

Definition W_4e0e8 : bv 32 := 0x00068513.
Lemma F_4e0e8 : fetch_word Plain.M.loaded_segments (0x4e0e8 : word) = Some W_4e0e8.
Proof. vm_refl. Qed.
Lemma D_4e0e8 : decode_any W_4e0e8 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0ec : bv 32 := 0x01813083.
Lemma F_4e0ec : fetch_word Plain.M.loaded_segments (0x4e0ec : word) = Some W_4e0ec.
Proof. vm_refl. Qed.
Lemma D_4e0ec : decode_any W_4e0ec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0f0 : bv 32 := 0x01013403.
Lemma F_4e0f0 : fetch_word Plain.M.loaded_segments (0x4e0f0 : word) = Some W_4e0f0.
Proof. vm_refl. Qed.
Lemma D_4e0f0 : decode_any W_4e0f0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0f4 : bv 32 := 0x00813483.
Lemma F_4e0f4 : fetch_word Plain.M.loaded_segments (0x4e0f4 : word) = Some W_4e0f4.
Proof. vm_refl. Qed.
Lemma D_4e0f4 : decode_any W_4e0f4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0f8 : bv 32 := 0x00013903.
Lemma F_4e0f8 : fetch_word Plain.M.loaded_segments (0x4e0f8 : word) = Some W_4e0f8.
Proof. vm_refl. Qed.
Lemma D_4e0f8 : decode_any W_4e0f8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0fc : bv 32 := 0x02010113.
Lemma F_4e0fc : fetch_word Plain.M.loaded_segments (0x4e0fc : word) = Some W_4e0fc.
Proof. vm_refl. Qed.
Lemma D_4e0fc : decode_any W_4e0fc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e100 : bv 32 := 0x00008067.
Lemma F_4e100 : fetch_word Plain.M.loaded_segments (0x4e100 : word) = Some W_4e100.
Proof. vm_refl. Qed.
Lemma D_4e100 : decode_any W_4e100 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e104 : bv 32 := 0xfd010113.
Lemma F_4e104 : fetch_word Plain.M.loaded_segments (0x4e104 : word) = Some W_4e104.
Proof. vm_refl. Qed.
Lemma D_4e104 : decode_any W_4e104 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e108 : bv 32 := 0x02113423.
Lemma F_4e108 : fetch_word Plain.M.loaded_segments (0x4e108 : word) = Some W_4e108.
Proof. vm_refl. Qed.
Lemma D_4e108 : decode_any W_4e108 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e10c : bv 32 := 0x02813023.
Lemma F_4e10c : fetch_word Plain.M.loaded_segments (0x4e10c : word) = Some W_4e10c.
Proof. vm_refl. Qed.
Lemma D_4e10c : decode_any W_4e10c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e110 : bv 32 := 0x00913c23.
Lemma F_4e110 : fetch_word Plain.M.loaded_segments (0x4e110 : word) = Some W_4e110.
Proof. vm_refl. Qed.
Lemma D_4e110 : decode_any W_4e110 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e114 : bv 32 := 0x01213823.
Lemma F_4e114 : fetch_word Plain.M.loaded_segments (0x4e114 : word) = Some W_4e114.
Proof. vm_refl. Qed.
Lemma D_4e114 : decode_any W_4e114 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e118 : bv 32 := 0x00010617.
Lemma F_4e118 : fetch_word Plain.M.loaded_segments (0x4e118 : word) = Some W_4e118.
Proof. vm_refl. Qed.
Lemma D_4e118 : decode_any W_4e118 = Some (Auipc 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e11c : bv 32 := 0x4d863403.
Lemma F_4e11c : fetch_word Plain.M.loaded_segments (0x4e11c : word) = Some W_4e11c.
Proof. vm_refl. Qed.
Lemma D_4e11c : decode_any W_4e11c = Some (Load SZ8 true 8 12 1240, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e120 : bv 32 := 0x00043603.
Lemma F_4e120 : fetch_word Plain.M.loaded_segments (0x4e120 : word) = Some W_4e120.
Proof. vm_refl. Qed.
Lemma D_4e120 : decode_any W_4e120 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e124 : bv 32 := 0x00c13423.
Lemma F_4e124 : fetch_word Plain.M.loaded_segments (0x4e124 : word) = Some W_4e124.
Proof. vm_refl. Qed.
Lemma D_4e124 : decode_any W_4e124 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e128 : bv 32 := 0x02053683.
Lemma F_4e128 : fetch_word Plain.M.loaded_segments (0x4e128 : word) = Some W_4e128.
Proof. vm_refl. Qed.
Lemma D_4e128 : decode_any W_4e128 = Some (Load SZ8 true 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e12c : bv 32 := 0x00b103a3.
Lemma F_4e12c : fetch_word Plain.M.loaded_segments (0x4e12c : word) = Some W_4e12c.
Proof. vm_refl. Qed.
Lemma D_4e12c : decode_any W_4e12c = Some (Store SZ1 2 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e130 : bv 32 := 0x02068c63.
Lemma F_4e130 : fetch_word Plain.M.loaded_segments (0x4e130 : word) = Some W_4e130.
Proof. vm_refl. Qed.
Lemma D_4e130 : decode_any W_4e130 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e134 : bv 32 := 0x02853603.
Lemma F_4e134 : fetch_word Plain.M.loaded_segments (0x4e134 : word) = Some W_4e134.
Proof. vm_refl. Qed.
Lemma D_4e134 : decode_any W_4e134 = Some (Load SZ8 true 12 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e138 : bv 32 := 0x00d60863.
Lemma F_4e138 : fetch_word Plain.M.loaded_segments (0x4e138 : word) = Some W_4e138.
Proof. vm_refl. Qed.
Lemma D_4e138 : decode_any W_4e138 = Some (Branch BC_EQ 12 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e13c : bv 32 := 0x09052703.
Lemma F_4e13c : fetch_word Plain.M.loaded_segments (0x4e13c : word) = Some W_4e13c.
Proof. vm_refl. Qed.
Lemma D_4e13c : decode_any W_4e13c = Some (Load SZ4 true 14 10 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e140 : bv 32 := 0x0ff5f793.
Lemma F_4e140 : fetch_word Plain.M.loaded_segments (0x4e140 : word) = Some W_4e140.
Proof. vm_refl. Qed.
Lemma D_4e140 : decode_any W_4e140 = Some (OpImm ALU_AND 15 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e144 : bv 32 := 0x02f71e63.
Lemma F_4e144 : fetch_word Plain.M.loaded_segments (0x4e144 : word) = Some W_4e144.
Proof. vm_refl. Qed.
Lemma D_4e144 : decode_any W_4e144 = Some (Branch BC_NE 14 15 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e148 : bv 32 := 0x04853683.
Lemma F_4e148 : fetch_word Plain.M.loaded_segments (0x4e148 : word) = Some W_4e148.
Proof. vm_refl. Qed.
Lemma D_4e148 : decode_any W_4e148 = Some (Load SZ8 true 13 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e14c : bv 32 := 0x00710593.
Lemma F_4e14c : fetch_word Plain.M.loaded_segments (0x4e14c : word) = Some W_4e14c.
Proof. vm_refl. Qed.
Lemma D_4e14c : decode_any W_4e14c = Some (OpImm ALU_ADD 11 2 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e150 : bv 32 := 0x00100613.
Lemma F_4e150 : fetch_word Plain.M.loaded_segments (0x4e150 : word) = Some W_4e150.
Proof. vm_refl. Qed.
Lemma D_4e150 : decode_any W_4e150 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1f0 : bv 32 := 0x06053683.
Lemma F_4e1f0 : fetch_word Plain.M.loaded_segments (0x4e1f0 : word) = Some W_4e1f0.
Proof. vm_refl. Qed.
Lemma D_4e1f0 : decode_any W_4e1f0 = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1f4 : bv 32 := 0x02c53c23.
Lemma F_4e1f4 : fetch_word Plain.M.loaded_segments (0x4e1f4 : word) = Some W_4e1f4.
Proof. vm_refl. Qed.
Lemma D_4e1f4 : decode_any W_4e1f4 = Some (Store SZ8 10 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e200 : bv 32 := 0x00053823.
Lemma F_4e200 : fetch_word Plain.M.loaded_segments (0x4e200 : word) = Some W_4e200.
Proof. vm_refl. Qed.
Lemma D_4e200 : decode_any W_4e200 = Some (Store SZ8 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e204 : bv 32 := 0x02d53023.
Lemma F_4e204 : fetch_word Plain.M.loaded_segments (0x4e204 : word) = Some W_4e204.
Proof. vm_refl. Qed.
Lemma D_4e204 : decode_any W_4e204 = Some (Store SZ8 10 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e208 : bv 32 := 0x02c53423.
Lemma F_4e208 : fetch_word Plain.M.loaded_segments (0x4e208 : word) = Some W_4e208.
Proof. vm_refl. Qed.
Lemma D_4e208 : decode_any W_4e208 = Some (Store SZ8 10 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e20c : bv 32 := 0x00000513.
Lemma F_4e20c : fetch_word Plain.M.loaded_segments (0x4e20c : word) = Some W_4e20c.
Proof. vm_refl. Qed.
Lemma D_4e20c : decode_any W_4e20c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e210 : bv 32 := 0x00008067.
Lemma F_4e210 : fetch_word Plain.M.loaded_segments (0x4e210 : word) = Some W_4e210.
Proof. vm_refl. Qed.
Lemma D_4e210 : decode_any W_4e210 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e214 : bv 32 := 0x0205e593.
Lemma F_4e214 : fetch_word Plain.M.loaded_segments (0x4e214 : word) = Some W_4e214.
Proof. vm_refl. Qed.
Lemma D_4e214 : decode_any W_4e214 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e218 : bv 32 := 0x00b52023.
Lemma F_4e218 : fetch_word Plain.M.loaded_segments (0x4e218 : word) = Some W_4e218.
Proof. vm_refl. Qed.
Lemma D_4e218 : decode_any W_4e218 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e21c : bv 32 := 0xfff00513.
Lemma F_4e21c : fetch_word Plain.M.loaded_segments (0x4e21c : word) = Some W_4e21c.
Proof. vm_refl. Qed.
Lemma D_4e21c : decode_any W_4e21c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e220 : bv 32 := 0x00008067.
Lemma F_4e220 : fetch_word Plain.M.loaded_segments (0x4e220 : word) = Some W_4e220.
Proof. vm_refl. Qed.
Lemma D_4e220 : decode_any W_4e220 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e224 : bv 32 := 0xff010113.
Lemma F_4e224 : fetch_word Plain.M.loaded_segments (0x4e224 : word) = Some W_4e224.
Proof. vm_refl. Qed.
Lemma D_4e224 : decode_any W_4e224 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e228 : bv 32 := 0x00113423.
Lemma F_4e228 : fetch_word Plain.M.loaded_segments (0x4e228 : word) = Some W_4e228.
Proof. vm_refl. Qed.
Lemma D_4e228 : decode_any W_4e228 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e22c : bv 32 := 0x00813023.
Lemma F_4e22c : fetch_word Plain.M.loaded_segments (0x4e22c : word) = Some W_4e22c.
Proof. vm_refl. Qed.
Lemma D_4e22c : decode_any W_4e22c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e230 : bv 32 := 0x388000ef.
Lemma F_4e230 : fetch_word Plain.M.loaded_segments (0x4e230 : word) = Some W_4e230.
Proof. vm_refl. Qed.
Lemma D_4e230 : decode_any W_4e230 = Some (Jal 1 904, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e234 : bv 32 := 0x00053403.
Lemma F_4e234 : fetch_word Plain.M.loaded_segments (0x4e234 : word) = Some W_4e234.
Proof. vm_refl. Qed.
Lemma D_4e234 : decode_any W_4e234 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e238 : bv 32 := 0x12041663.
Lemma F_4e238 : fetch_word Plain.M.loaded_segments (0x4e238 : word) = Some W_4e238.
Proof. vm_refl. Qed.
Lemma D_4e238 : decode_any W_4e238 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e23c : bv 32 := 0x00043517.
Lemma F_4e23c : fetch_word Plain.M.loaded_segments (0x4e23c : word) = Some W_4e23c.
Proof. vm_refl. Qed.
Lemma D_4e23c : decode_any W_4e23c = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e240 : bv 32 := 0x8ac53403.
Lemma F_4e240 : fetch_word Plain.M.loaded_segments (0x4e240 : word) = Some W_4e240.
Proof. vm_refl. Qed.
Lemma D_4e240 : decode_any W_4e240 = Some (Load SZ8 true 8 10 2220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e244 : bv 32 := 0x04040a63.
Lemma F_4e244 : fetch_word Plain.M.loaded_segments (0x4e244 : word) = Some W_4e244.
Proof. vm_refl. Qed.
Lemma D_4e244 : decode_any W_4e244 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e298 : bv 32 := 0x00011517.
Lemma F_4e298 : fetch_word Plain.M.loaded_segments (0x4e298 : word) = Some W_4e298.
Proof. vm_refl. Qed.
Lemma D_4e298 : decode_any W_4e298 = Some (Auipc 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e29c : bv 32 := 0x5c053403.
Lemma F_4e29c : fetch_word Plain.M.loaded_segments (0x4e29c : word) = Some W_4e29c.
Proof. vm_refl. Qed.
Lemma D_4e29c : decode_any W_4e29c = Some (Load SZ8 true 8 10 1472, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2a0 : bv 32 := 0x04040a63.
Lemma F_4e2a0 : fetch_word Plain.M.loaded_segments (0x4e2a0 : word) = Some W_4e2a0.
Proof. vm_refl. Qed.
Lemma D_4e2a0 : decode_any W_4e2a0 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2a4 : bv 32 := 0x08c42503.
Lemma F_4e2a4 : fetch_word Plain.M.loaded_segments (0x4e2a4 : word) = Some W_4e2a4.
Proof. vm_refl. Qed.
Lemma D_4e2a4 : decode_any W_4e2a4 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2a8 : bv 32 := 0x00054663.
Lemma F_4e2a8 : fetch_word Plain.M.loaded_segments (0x4e2a8 : word) = Some W_4e2a8.
Proof. vm_refl. Qed.
Lemma D_4e2a8 : decode_any W_4e2a8 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2b4 : bv 32 := 0x02843503.
Lemma F_4e2b4 : fetch_word Plain.M.loaded_segments (0x4e2b4 : word) = Some W_4e2b4.
Proof. vm_refl. Qed.
Lemma D_4e2b4 : decode_any W_4e2b4 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2b8 : bv 32 := 0x03843583.
Lemma F_4e2b8 : fetch_word Plain.M.loaded_segments (0x4e2b8 : word) = Some W_4e2b8.
Proof. vm_refl. Qed.
Lemma D_4e2b8 : decode_any W_4e2b8 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2bc : bv 32 := 0x00b50c63.
Lemma F_4e2bc : fetch_word Plain.M.loaded_segments (0x4e2bc : word) = Some W_4e2bc.
Proof. vm_refl. Qed.
Lemma D_4e2bc : decode_any W_4e2bc = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2c0 : bv 32 := 0x04843683.
Lemma F_4e2c0 : fetch_word Plain.M.loaded_segments (0x4e2c0 : word) = Some W_4e2c0.
Proof. vm_refl. Qed.
Lemma D_4e2c0 : decode_any W_4e2c0 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2c4 : bv 32 := 0x00040513.
Lemma F_4e2c4 : fetch_word Plain.M.loaded_segments (0x4e2c4 : word) = Some W_4e2c4.
Proof. vm_refl. Qed.
Lemma D_4e2c4 : decode_any W_4e2c4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2c8 : bv 32 := 0x00000593.
Lemma F_4e2c8 : fetch_word Plain.M.loaded_segments (0x4e2c8 : word) = Some W_4e2c8.
Proof. vm_refl. Qed.
Lemma D_4e2c8 : decode_any W_4e2c8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2cc : bv 32 := 0x00000613.
Lemma F_4e2cc : fetch_word Plain.M.loaded_segments (0x4e2cc : word) = Some W_4e2cc.
Proof. vm_refl. Qed.
Lemma D_4e2cc : decode_any W_4e2cc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2d0 : bv 32 := 0x000680e7.
Lemma F_4e2d0 : fetch_word Plain.M.loaded_segments (0x4e2d0 : word) = Some W_4e2d0.
Proof. vm_refl. Qed.
Lemma D_4e2d0 : decode_any W_4e2d0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2d4 : bv 32 := 0x00843503.
Lemma F_4e2d4 : fetch_word Plain.M.loaded_segments (0x4e2d4 : word) = Some W_4e2d4.
Proof. vm_refl. Qed.
Lemma D_4e2d4 : decode_any W_4e2d4 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2d8 : bv 32 := 0x01043583.
Lemma F_4e2d8 : fetch_word Plain.M.loaded_segments (0x4e2d8 : word) = Some W_4e2d8.
Proof. vm_refl. Qed.
Lemma D_4e2d8 : decode_any W_4e2d8 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2dc : bv 32 := 0x00b50c63.
Lemma F_4e2dc : fetch_word Plain.M.loaded_segments (0x4e2dc : word) = Some W_4e2dc.
Proof. vm_refl. Qed.
Lemma D_4e2dc : decode_any W_4e2dc = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2f4 : bv 32 := 0x00011517.
Lemma F_4e2f4 : fetch_word Plain.M.loaded_segments (0x4e2f4 : word) = Some W_4e2f4.
Proof. vm_refl. Qed.
Lemma D_4e2f4 : decode_any W_4e2f4 = Some (Auipc 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2f8 : bv 32 := 0x47453403.
Lemma F_4e2f8 : fetch_word Plain.M.loaded_segments (0x4e2f8 : word) = Some W_4e2f8.
Proof. vm_refl. Qed.
Lemma D_4e2f8 : decode_any W_4e2f8 = Some (Load SZ8 true 8 10 1140, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2fc : bv 32 := 0x0a040e63.
Lemma F_4e2fc : fetch_word Plain.M.loaded_segments (0x4e2fc : word) = Some W_4e2fc.
Proof. vm_refl. Qed.
Lemma D_4e2fc : decode_any W_4e2fc = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e300 : bv 32 := 0x08c42503.
Lemma F_4e300 : fetch_word Plain.M.loaded_segments (0x4e300 : word) = Some W_4e300.
Proof. vm_refl. Qed.
Lemma D_4e300 : decode_any W_4e300 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e304 : bv 32 := 0x00054663.
Lemma F_4e304 : fetch_word Plain.M.loaded_segments (0x4e304 : word) = Some W_4e304.
Proof. vm_refl. Qed.
Lemma D_4e304 : decode_any W_4e304 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e310 : bv 32 := 0x02843503.
Lemma F_4e310 : fetch_word Plain.M.loaded_segments (0x4e310 : word) = Some W_4e310.
Proof. vm_refl. Qed.
Lemma D_4e310 : decode_any W_4e310 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e314 : bv 32 := 0x03843583.
Lemma F_4e314 : fetch_word Plain.M.loaded_segments (0x4e314 : word) = Some W_4e314.
Proof. vm_refl. Qed.
Lemma D_4e314 : decode_any W_4e314 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e318 : bv 32 := 0x00b50c63.
Lemma F_4e318 : fetch_word Plain.M.loaded_segments (0x4e318 : word) = Some W_4e318.
Proof. vm_refl. Qed.
Lemma D_4e318 : decode_any W_4e318 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e330 : bv 32 := 0x00843503.
Lemma F_4e330 : fetch_word Plain.M.loaded_segments (0x4e330 : word) = Some W_4e330.
Proof. vm_refl. Qed.
Lemma D_4e330 : decode_any W_4e330 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e334 : bv 32 := 0x01043583.
Lemma F_4e334 : fetch_word Plain.M.loaded_segments (0x4e334 : word) = Some W_4e334.
Proof. vm_refl. Qed.
Lemma D_4e334 : decode_any W_4e334 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e338 : bv 32 := 0x08b50063.
Lemma F_4e338 : fetch_word Plain.M.loaded_segments (0x4e338 : word) = Some W_4e338.
Proof. vm_refl. Qed.
Lemma D_4e338 : decode_any W_4e338 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e3b8 : bv 32 := 0x00813083.
Lemma F_4e3b8 : fetch_word Plain.M.loaded_segments (0x4e3b8 : word) = Some W_4e3b8.
Proof. vm_refl. Qed.
Lemma D_4e3b8 : decode_any W_4e3b8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e3bc : bv 32 := 0x00013403.
Lemma F_4e3bc : fetch_word Plain.M.loaded_segments (0x4e3bc : word) = Some W_4e3bc.
Proof. vm_refl. Qed.
Lemma D_4e3bc : decode_any W_4e3bc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e3c0 : bv 32 := 0x01010113.
Lemma F_4e3c0 : fetch_word Plain.M.loaded_segments (0x4e3c0 : word) = Some W_4e3c0.
Proof. vm_refl. Qed.
Lemma D_4e3c0 : decode_any W_4e3c0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e3c4 : bv 32 := 0x00008067.
Lemma F_4e3c4 : fetch_word Plain.M.loaded_segments (0x4e3c4 : word) = Some W_4e3c4.
Proof. vm_refl. Qed.
Lemma D_4e3c4 : decode_any W_4e3c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
