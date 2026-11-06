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

Definition W_4ed20 : bv 32 := 0xff010113.
Lemma F_4ed20 : fetch_word Ubsan.M.loaded_segments (0x4ed20 : word) = Some W_4ed20.
Proof. vm_refl. Qed.
Lemma D_4ed20 : decode_any W_4ed20 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed24 : bv 32 := 0x00113423.
Lemma F_4ed24 : fetch_word Ubsan.M.loaded_segments (0x4ed24 : word) = Some W_4ed24.
Proof. vm_refl. Qed.
Lemma D_4ed24 : decode_any W_4ed24 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed28 : bv 32 := 0x00813023.
Lemma F_4ed28 : fetch_word Ubsan.M.loaded_segments (0x4ed28 : word) = Some W_4ed28.
Proof. vm_refl. Qed.
Lemma D_4ed28 : decode_any W_4ed28 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed2c : bv 32 := 0x388000ef.
Lemma F_4ed2c : fetch_word Ubsan.M.loaded_segments (0x4ed2c : word) = Some W_4ed2c.
Proof. vm_refl. Qed.
Lemma D_4ed2c : decode_any W_4ed2c = Some (Jal 1 904, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed30 : bv 32 := 0x00053403.
Lemma F_4ed30 : fetch_word Ubsan.M.loaded_segments (0x4ed30 : word) = Some W_4ed30.
Proof. vm_refl. Qed.
Lemma D_4ed30 : decode_any W_4ed30 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed34 : bv 32 := 0x12041663.
Lemma F_4ed34 : fetch_word Ubsan.M.loaded_segments (0x4ed34 : word) = Some W_4ed34.
Proof. vm_refl. Qed.
Lemma D_4ed34 : decode_any W_4ed34 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed38 : bv 32 := 0x00043517.
Lemma F_4ed38 : fetch_word Ubsan.M.loaded_segments (0x4ed38 : word) = Some W_4ed38.
Proof. vm_refl. Qed.
Lemma D_4ed38 : decode_any W_4ed38 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed3c : bv 32 := 0x8b053403.
Lemma F_4ed3c : fetch_word Ubsan.M.loaded_segments (0x4ed3c : word) = Some W_4ed3c.
Proof. vm_refl. Qed.
Lemma D_4ed3c : decode_any W_4ed3c = Some (Load SZ8 true 8 10 2224, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed40 : bv 32 := 0x04040a63.
Lemma F_4ed40 : fetch_word Ubsan.M.loaded_segments (0x4ed40 : word) = Some W_4ed40.
Proof. vm_refl. Qed.
Lemma D_4ed40 : decode_any W_4ed40 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed94 : bv 32 := 0x00011517.
Lemma F_4ed94 : fetch_word Ubsan.M.loaded_segments (0x4ed94 : word) = Some W_4ed94.
Proof. vm_refl. Qed.
Lemma D_4ed94 : decode_any W_4ed94 = Some (Auipc 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed98 : bv 32 := 0x5bc53403.
Lemma F_4ed98 : fetch_word Ubsan.M.loaded_segments (0x4ed98 : word) = Some W_4ed98.
Proof. vm_refl. Qed.
Lemma D_4ed98 : decode_any W_4ed98 = Some (Load SZ8 true 8 10 1468, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed9c : bv 32 := 0x04040a63.
Lemma F_4ed9c : fetch_word Ubsan.M.loaded_segments (0x4ed9c : word) = Some W_4ed9c.
Proof. vm_refl. Qed.
Lemma D_4ed9c : decode_any W_4ed9c = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eda0 : bv 32 := 0x08c42503.
Lemma F_4eda0 : fetch_word Ubsan.M.loaded_segments (0x4eda0 : word) = Some W_4eda0.
Proof. vm_refl. Qed.
Lemma D_4eda0 : decode_any W_4eda0 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eda4 : bv 32 := 0x00054663.
Lemma F_4eda4 : fetch_word Ubsan.M.loaded_segments (0x4eda4 : word) = Some W_4eda4.
Proof. vm_refl. Qed.
Lemma D_4eda4 : decode_any W_4eda4 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edb0 : bv 32 := 0x02843503.
Lemma F_4edb0 : fetch_word Ubsan.M.loaded_segments (0x4edb0 : word) = Some W_4edb0.
Proof. vm_refl. Qed.
Lemma D_4edb0 : decode_any W_4edb0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edb4 : bv 32 := 0x03843583.
Lemma F_4edb4 : fetch_word Ubsan.M.loaded_segments (0x4edb4 : word) = Some W_4edb4.
Proof. vm_refl. Qed.
Lemma D_4edb4 : decode_any W_4edb4 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edb8 : bv 32 := 0x00b50c63.
Lemma F_4edb8 : fetch_word Ubsan.M.loaded_segments (0x4edb8 : word) = Some W_4edb8.
Proof. vm_refl. Qed.
Lemma D_4edb8 : decode_any W_4edb8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edbc : bv 32 := 0x04843683.
Lemma F_4edbc : fetch_word Ubsan.M.loaded_segments (0x4edbc : word) = Some W_4edbc.
Proof. vm_refl. Qed.
Lemma D_4edbc : decode_any W_4edbc = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edc0 : bv 32 := 0x00040513.
Lemma F_4edc0 : fetch_word Ubsan.M.loaded_segments (0x4edc0 : word) = Some W_4edc0.
Proof. vm_refl. Qed.
Lemma D_4edc0 : decode_any W_4edc0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edc4 : bv 32 := 0x00000593.
Lemma F_4edc4 : fetch_word Ubsan.M.loaded_segments (0x4edc4 : word) = Some W_4edc4.
Proof. vm_refl. Qed.
Lemma D_4edc4 : decode_any W_4edc4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edc8 : bv 32 := 0x00000613.
Lemma F_4edc8 : fetch_word Ubsan.M.loaded_segments (0x4edc8 : word) = Some W_4edc8.
Proof. vm_refl. Qed.
Lemma D_4edc8 : decode_any W_4edc8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edcc : bv 32 := 0x000680e7.
Lemma F_4edcc : fetch_word Ubsan.M.loaded_segments (0x4edcc : word) = Some W_4edcc.
Proof. vm_refl. Qed.
Lemma D_4edcc : decode_any W_4edcc = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edd0 : bv 32 := 0x00843503.
Lemma F_4edd0 : fetch_word Ubsan.M.loaded_segments (0x4edd0 : word) = Some W_4edd0.
Proof. vm_refl. Qed.
Lemma D_4edd0 : decode_any W_4edd0 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edd4 : bv 32 := 0x01043583.
Lemma F_4edd4 : fetch_word Ubsan.M.loaded_segments (0x4edd4 : word) = Some W_4edd4.
Proof. vm_refl. Qed.
Lemma D_4edd4 : decode_any W_4edd4 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edd8 : bv 32 := 0x00b50c63.
Lemma F_4edd8 : fetch_word Ubsan.M.loaded_segments (0x4edd8 : word) = Some W_4edd8.
Proof. vm_refl. Qed.
Lemma D_4edd8 : decode_any W_4edd8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edf0 : bv 32 := 0x00011517.
Lemma F_4edf0 : fetch_word Ubsan.M.loaded_segments (0x4edf0 : word) = Some W_4edf0.
Proof. vm_refl. Qed.
Lemma D_4edf0 : decode_any W_4edf0 = Some (Auipc 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edf4 : bv 32 := 0x47053403.
Lemma F_4edf4 : fetch_word Ubsan.M.loaded_segments (0x4edf4 : word) = Some W_4edf4.
Proof. vm_refl. Qed.
Lemma D_4edf4 : decode_any W_4edf4 = Some (Load SZ8 true 8 10 1136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edf8 : bv 32 := 0x0a040e63.
Lemma F_4edf8 : fetch_word Ubsan.M.loaded_segments (0x4edf8 : word) = Some W_4edf8.
Proof. vm_refl. Qed.
Lemma D_4edf8 : decode_any W_4edf8 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edfc : bv 32 := 0x08c42503.
Lemma F_4edfc : fetch_word Ubsan.M.loaded_segments (0x4edfc : word) = Some W_4edfc.
Proof. vm_refl. Qed.
Lemma D_4edfc : decode_any W_4edfc = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ee00 : bv 32 := 0x00054663.
Lemma F_4ee00 : fetch_word Ubsan.M.loaded_segments (0x4ee00 : word) = Some W_4ee00.
Proof. vm_refl. Qed.
Lemma D_4ee00 : decode_any W_4ee00 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ee0c : bv 32 := 0x02843503.
Lemma F_4ee0c : fetch_word Ubsan.M.loaded_segments (0x4ee0c : word) = Some W_4ee0c.
Proof. vm_refl. Qed.
Lemma D_4ee0c : decode_any W_4ee0c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ee10 : bv 32 := 0x03843583.
Lemma F_4ee10 : fetch_word Ubsan.M.loaded_segments (0x4ee10 : word) = Some W_4ee10.
Proof. vm_refl. Qed.
Lemma D_4ee10 : decode_any W_4ee10 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ee14 : bv 32 := 0x00b50c63.
Lemma F_4ee14 : fetch_word Ubsan.M.loaded_segments (0x4ee14 : word) = Some W_4ee14.
Proof. vm_refl. Qed.
Lemma D_4ee14 : decode_any W_4ee14 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ee2c : bv 32 := 0x00843503.
Lemma F_4ee2c : fetch_word Ubsan.M.loaded_segments (0x4ee2c : word) = Some W_4ee2c.
Proof. vm_refl. Qed.
Lemma D_4ee2c : decode_any W_4ee2c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ee30 : bv 32 := 0x01043583.
Lemma F_4ee30 : fetch_word Ubsan.M.loaded_segments (0x4ee30 : word) = Some W_4ee30.
Proof. vm_refl. Qed.
Lemma D_4ee30 : decode_any W_4ee30 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ee34 : bv 32 := 0x08b50063.
Lemma F_4ee34 : fetch_word Ubsan.M.loaded_segments (0x4ee34 : word) = Some W_4ee34.
Proof. vm_refl. Qed.
Lemma D_4ee34 : decode_any W_4ee34 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eeb4 : bv 32 := 0x00813083.
Lemma F_4eeb4 : fetch_word Ubsan.M.loaded_segments (0x4eeb4 : word) = Some W_4eeb4.
Proof. vm_refl. Qed.
Lemma D_4eeb4 : decode_any W_4eeb4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eeb8 : bv 32 := 0x00013403.
Lemma F_4eeb8 : fetch_word Ubsan.M.loaded_segments (0x4eeb8 : word) = Some W_4eeb8.
Proof. vm_refl. Qed.
Lemma D_4eeb8 : decode_any W_4eeb8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eebc : bv 32 := 0x01010113.
Lemma F_4eebc : fetch_word Ubsan.M.loaded_segments (0x4eebc : word) = Some W_4eebc.
Proof. vm_refl. Qed.
Lemma D_4eebc : decode_any W_4eebc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eec0 : bv 32 := 0x00008067.
Lemma F_4eec0 : fetch_word Ubsan.M.loaded_segments (0x4eec0 : word) = Some W_4eec0.
Proof. vm_refl. Qed.
Lemma D_4eec0 : decode_any W_4eec0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0b4 : bv 32 := 0xff010113.
Lemma F_4f0b4 : fetch_word Ubsan.M.loaded_segments (0x4f0b4 : word) = Some W_4f0b4.
Proof. vm_refl. Qed.
Lemma D_4f0b4 : decode_any W_4f0b4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0b8 : bv 32 := 0x00113423.
Lemma F_4f0b8 : fetch_word Ubsan.M.loaded_segments (0x4f0b8 : word) = Some W_4f0b8.
Proof. vm_refl. Qed.
Lemma D_4f0b8 : decode_any W_4f0b8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0bc : bv 32 := 0x00813023.
Lemma F_4f0bc : fetch_word Ubsan.M.loaded_segments (0x4f0bc : word) = Some W_4f0bc.
Proof. vm_refl. Qed.
Lemma D_4f0bc : decode_any W_4f0bc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0c0 : bv 32 := 0x00042517.
Lemma F_4f0c0 : fetch_word Ubsan.M.loaded_segments (0x4f0c0 : word) = Some W_4f0c0.
Proof. vm_refl. Qed.
Lemma D_4f0c0 : decode_any W_4f0c0 = Some (Auipc 10 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0c4 : bv 32 := 0x53050413.
Lemma F_4f0c4 : fetch_word Ubsan.M.loaded_segments (0x4f0c4 : word) = Some W_4f0c4.
Proof. vm_refl. Qed.
Lemma D_4f0c4 : decode_any W_4f0c4 = Some (OpImm ALU_ADD 8 10 1328, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0c8 : bv 32 := 0x00040513.
Lemma F_4f0c8 : fetch_word Ubsan.M.loaded_segments (0x4f0c8 : word) = Some W_4f0c8.
Proof. vm_refl. Qed.
Lemma D_4f0c8 : decode_any W_4f0c8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0cc : bv 32 := 0x4590a0ef.
Lemma F_4f0cc : fetch_word Ubsan.M.loaded_segments (0x4f0cc : word) = Some W_4f0cc.
Proof. vm_refl. Qed.
Lemma D_4f0cc : decode_any W_4f0cc = Some (Jal 1 44120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0d0 : bv 32 := 0x00840513.
Lemma F_4f0d0 : fetch_word Ubsan.M.loaded_segments (0x4f0d0 : word) = Some W_4f0d0.
Proof. vm_refl. Qed.
Lemma D_4f0d0 : decode_any W_4f0d0 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0d4 : bv 32 := 0x00813083.
Lemma F_4f0d4 : fetch_word Ubsan.M.loaded_segments (0x4f0d4 : word) = Some W_4f0d4.
Proof. vm_refl. Qed.
Lemma D_4f0d4 : decode_any W_4f0d4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0d8 : bv 32 := 0x00013403.
Lemma F_4f0d8 : fetch_word Ubsan.M.loaded_segments (0x4f0d8 : word) = Some W_4f0d8.
Proof. vm_refl. Qed.
Lemma D_4f0d8 : decode_any W_4f0d8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0dc : bv 32 := 0x01010113.
Lemma F_4f0dc : fetch_word Ubsan.M.loaded_segments (0x4f0dc : word) = Some W_4f0dc.
Proof. vm_refl. Qed.
Lemma D_4f0dc : decode_any W_4f0dc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0e0 : bv 32 := 0x00008067.
Lemma F_4f0e0 : fetch_word Ubsan.M.loaded_segments (0x4f0e0 : word) = Some W_4f0e0.
Proof. vm_refl. Qed.
Lemma D_4f0e0 : decode_any W_4f0e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f150 : bv 32 := 0x00008067.
Lemma F_4f150 : fetch_word Ubsan.M.loaded_segments (0x4f150 : word) = Some W_4f150.
Proof. vm_refl. Qed.
Lemma D_4f150 : decode_any W_4f150 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f180 : bv 32 := 0xf9010113.
Lemma F_4f180 : fetch_word Ubsan.M.loaded_segments (0x4f180 : word) = Some W_4f180.
Proof. vm_refl. Qed.
Lemma D_4f180 : decode_any W_4f180 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f184 : bv 32 := 0x06113423.
Lemma F_4f184 : fetch_word Ubsan.M.loaded_segments (0x4f184 : word) = Some W_4f184.
Proof. vm_refl. Qed.
Lemma D_4f184 : decode_any W_4f184 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f188 : bv 32 := 0x06813023.
Lemma F_4f188 : fetch_word Ubsan.M.loaded_segments (0x4f188 : word) = Some W_4f188.
Proof. vm_refl. Qed.
Lemma D_4f188 : decode_any W_4f188 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f18c : bv 32 := 0x04913c23.
Lemma F_4f18c : fetch_word Ubsan.M.loaded_segments (0x4f18c : word) = Some W_4f18c.
Proof. vm_refl. Qed.
Lemma D_4f18c : decode_any W_4f18c = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f190 : bv 32 := 0x05213823.
Lemma F_4f190 : fetch_word Ubsan.M.loaded_segments (0x4f190 : word) = Some W_4f190.
Proof. vm_refl. Qed.
Lemma D_4f190 : decode_any W_4f190 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f194 : bv 32 := 0x05313423.
Lemma F_4f194 : fetch_word Ubsan.M.loaded_segments (0x4f194 : word) = Some W_4f194.
Proof. vm_refl. Qed.
Lemma D_4f194 : decode_any W_4f194 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f198 : bv 32 := 0x05413023.
Lemma F_4f198 : fetch_word Ubsan.M.loaded_segments (0x4f198 : word) = Some W_4f198.
Proof. vm_refl. Qed.
Lemma D_4f198 : decode_any W_4f198 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f19c : bv 32 := 0x03513c23.
Lemma F_4f19c : fetch_word Ubsan.M.loaded_segments (0x4f19c : word) = Some W_4f19c.
Proof. vm_refl. Qed.
Lemma D_4f19c : decode_any W_4f19c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1a0 : bv 32 := 0x03613823.
Lemma F_4f1a0 : fetch_word Ubsan.M.loaded_segments (0x4f1a0 : word) = Some W_4f1a0.
Proof. vm_refl. Qed.
Lemma D_4f1a0 : decode_any W_4f1a0 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1a4 : bv 32 := 0x00060413.
Lemma F_4f1a4 : fetch_word Ubsan.M.loaded_segments (0x4f1a4 : word) = Some W_4f1a4.
Proof. vm_refl. Qed.
Lemma D_4f1a4 : decode_any W_4f1a4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1a8 : bv 32 := 0x00050493.
Lemma F_4f1a8 : fetch_word Ubsan.M.loaded_segments (0x4f1a8 : word) = Some W_4f1a8.
Proof. vm_refl. Qed.
Lemma D_4f1a8 : decode_any W_4f1a8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1ac : bv 32 := 0x00010517.
Lemma F_4f1ac : fetch_word Ubsan.M.loaded_segments (0x4f1ac : word) = Some W_4f1ac.
Proof. vm_refl. Qed.
Lemma D_4f1ac : decode_any W_4f1ac = Some (Auipc 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1b0 : bv 32 := 0xf3c53a83.
Lemma F_4f1b0 : fetch_word Ubsan.M.loaded_segments (0x4f1b0 : word) = Some W_4f1b0.
Proof. vm_refl. Qed.
Lemma D_4f1b0 : decode_any W_4f1b0 = Some (Load SZ8 true 21 10 3900, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1b4 : bv 32 := 0x000ab503.
Lemma F_4f1b4 : fetch_word Ubsan.M.loaded_segments (0x4f1b4 : word) = Some W_4f1b4.
Proof. vm_refl. Qed.
Lemma D_4f1b4 : decode_any W_4f1b4 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1b8 : bv 32 := 0x02a13423.
Lemma F_4f1b8 : fetch_word Ubsan.M.loaded_segments (0x4f1b8 : word) = Some W_4f1b8.
Proof. vm_refl. Qed.
Lemma D_4f1b8 : decode_any W_4f1b8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1bc : bv 32 := 0x0284b503.
Lemma F_4f1bc : fetch_word Ubsan.M.loaded_segments (0x4f1bc : word) = Some W_4f1bc.
Proof. vm_refl. Qed.
Lemma D_4f1bc : decode_any W_4f1bc = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1c0 : bv 32 := 0x0384b603.
Lemma F_4f1c0 : fetch_word Ubsan.M.loaded_segments (0x4f1c0 : word) = Some W_4f1c0.
Proof. vm_refl. Qed.
Lemma D_4f1c0 : decode_any W_4f1c0 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1c4 : bv 32 := 0x40c50b33.
Lemma F_4f1c4 : fetch_word Ubsan.M.loaded_segments (0x4f1c4 : word) = Some W_4f1c4.
Proof. vm_refl. Qed.
Lemma D_4f1c4 : decode_any W_4f1c4 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1c8 : bv 32 := 0x00c546b3.
Lemma F_4f1c8 : fetch_word Ubsan.M.loaded_segments (0x4f1c8 : word) = Some W_4f1c8.
Proof. vm_refl. Qed.
Lemma D_4f1c8 : decode_any W_4f1c8 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1cc : bv 32 := 0x00c13423.
Lemma F_4f1cc : fetch_word Ubsan.M.loaded_segments (0x4f1cc : word) = Some W_4f1cc.
Proof. vm_refl. Qed.
Lemma D_4f1cc : decode_any W_4f1cc = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1d0 : bv 32 := 0x01613823.
Lemma F_4f1d0 : fetch_word Ubsan.M.loaded_segments (0x4f1d0 : word) = Some W_4f1d0.
Proof. vm_refl. Qed.
Lemma D_4f1d0 : decode_any W_4f1d0 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1d4 : bv 32 := 0x00b13c23.
Lemma F_4f1d4 : fetch_word Ubsan.M.loaded_segments (0x4f1d4 : word) = Some W_4f1d4.
Proof. vm_refl. Qed.
Lemma D_4f1d4 : decode_any W_4f1d4 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1d8 : bv 32 := 0x02813023.
Lemma F_4f1d8 : fetch_word Ubsan.M.loaded_segments (0x4f1d8 : word) = Some W_4f1d8.
Proof. vm_refl. Qed.
Lemma D_4f1d8 : decode_any W_4f1d8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1dc : bv 32 := 0x008b0b33.
Lemma F_4f1dc : fetch_word Ubsan.M.loaded_segments (0x4f1dc : word) = Some W_4f1dc.
Proof. vm_refl. Qed.
Lemma D_4f1dc : decode_any W_4f1dc = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1e0 : bv 32 := 0x00d03933.
Lemma F_4f1e0 : fetch_word Ubsan.M.loaded_segments (0x4f1e0 : word) = Some W_4f1e0.
Proof. vm_refl. Qed.
Lemma D_4f1e0 : decode_any W_4f1e0 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1e4 : bv 32 := 0x00c50663.
Lemma F_4f1e4 : fetch_word Ubsan.M.loaded_segments (0x4f1e4 : word) = Some W_4f1e4.
Proof. vm_refl. Qed.
Lemma D_4f1e4 : decode_any W_4f1e4 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1e8 : bv 32 := 0x00810993.
Lemma F_4f1e8 : fetch_word Ubsan.M.loaded_segments (0x4f1e8 : word) = Some W_4f1e8.
Proof. vm_refl. Qed.
Lemma D_4f1e8 : decode_any W_4f1e8 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1ec : bv 32 := 0x0080006f.
Lemma F_4f1ec : fetch_word Ubsan.M.loaded_segments (0x4f1ec : word) = Some W_4f1ec.
Proof. vm_refl. Qed.
Lemma D_4f1ec : decode_any W_4f1ec = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1f0 : bv 32 := 0x01810993.
Lemma F_4f1f0 : fetch_word Ubsan.M.loaded_segments (0x4f1f0 : word) = Some W_4f1f0.
Proof. vm_refl. Qed.
Lemma D_4f1f0 : decode_any W_4f1f0 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1f4 : bv 32 := 0x0784a503.
Lemma F_4f1f4 : fetch_word Ubsan.M.loaded_segments (0x4f1f4 : word) = Some W_4f1f4.
Proof. vm_refl. Qed.
Lemma D_4f1f4 : decode_any W_4f1f4 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1f8 : bv 32 := 0x00190913.
Lemma F_4f1f8 : fetch_word Ubsan.M.loaded_segments (0x4f1f8 : word) = Some W_4f1f8.
Proof. vm_refl. Qed.
Lemma D_4f1f8 : decode_any W_4f1f8 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1fc : bv 32 := 0x04200893.
Lemma F_4f1fc : fetch_word Ubsan.M.loaded_segments (0x4f1fc : word) = Some W_4f1fc.
Proof. vm_refl. Qed.
Lemma D_4f1fc : decode_any W_4f1fc = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f200 : bv 32 := 0x00098593.
Lemma F_4f200 : fetch_word Ubsan.M.loaded_segments (0x4f200 : word) = Some W_4f200.
Proof. vm_refl. Qed.
Lemma D_4f200 : decode_any W_4f200 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f204 : bv 32 := 0x00090613.
Lemma F_4f204 : fetch_word Ubsan.M.loaded_segments (0x4f204 : word) = Some W_4f204.
Proof. vm_refl. Qed.
Lemma D_4f204 : decode_any W_4f204 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f208 : bv 32 := 0x00000073.
Lemma F_4f208 : fetch_word Ubsan.M.loaded_segments (0x4f208 : word) = Some W_4f208.
Proof. vm_refl. Qed.
Lemma D_4f208 : decode_any W_4f208 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_4f208 : is_ecall W_4f208 = true.
Proof. reflexivity. Qed.

Definition W_4f20c : bv 32 := 0xf0dfc0ef.
Lemma F_4f20c : fetch_word Ubsan.M.loaded_segments (0x4f20c : word) = Some W_4f20c.
Proof. vm_refl. Qed.
Lemma D_4f20c : decode_any W_4f20c = Some (Jal 1 2084620, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f210 : bv 32 := 0x09651863.
Lemma F_4f210 : fetch_word Ubsan.M.loaded_segments (0x4f210 : word) = Some W_4f210.
Proof. vm_refl. Qed.
Lemma D_4f210 : decode_any W_4f210 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f214 : bv 32 := 0x0584b503.
Lemma F_4f214 : fetch_word Ubsan.M.loaded_segments (0x4f214 : word) = Some W_4f214.
Proof. vm_refl. Qed.
Lemma D_4f214 : decode_any W_4f214 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f218 : bv 32 := 0x0604b583.
Lemma F_4f218 : fetch_word Ubsan.M.loaded_segments (0x4f218 : word) = Some W_4f218.
Proof. vm_refl. Qed.
Lemma D_4f218 : decode_any W_4f218 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f21c : bv 32 := 0x00b505b3.
Lemma F_4f21c : fetch_word Ubsan.M.loaded_segments (0x4f21c : word) = Some W_4f21c.
Proof. vm_refl. Qed.
Lemma D_4f21c : decode_any W_4f21c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f220 : bv 32 := 0x02b4b023.
Lemma F_4f220 : fetch_word Ubsan.M.loaded_segments (0x4f220 : word) = Some W_4f220.
Proof. vm_refl. Qed.
Lemma D_4f220 : decode_any W_4f220 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f224 : bv 32 := 0x02a4b423.
Lemma F_4f224 : fetch_word Ubsan.M.loaded_segments (0x4f224 : word) = Some W_4f224.
Proof. vm_refl. Qed.
Lemma D_4f224 : decode_any W_4f224 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f228 : bv 32 := 0x02a4bc23.
Lemma F_4f228 : fetch_word Ubsan.M.loaded_segments (0x4f228 : word) = Some W_4f228.
Proof. vm_refl. Qed.
Lemma D_4f228 : decode_any W_4f228 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f22c : bv 32 := 0x00040513.
Lemma F_4f22c : fetch_word Ubsan.M.loaded_segments (0x4f22c : word) = Some W_4f22c.
Proof. vm_refl. Qed.
Lemma D_4f22c : decode_any W_4f22c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f230 : bv 32 := 0x000ab583.
Lemma F_4f230 : fetch_word Ubsan.M.loaded_segments (0x4f230 : word) = Some W_4f230.
Proof. vm_refl. Qed.
Lemma D_4f230 : decode_any W_4f230 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f234 : bv 32 := 0x02813603.
Lemma F_4f234 : fetch_word Ubsan.M.loaded_segments (0x4f234 : word) = Some W_4f234.
Proof. vm_refl. Qed.
Lemma D_4f234 : decode_any W_4f234 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f238 : bv 32 := 0x0cc59a63.
Lemma F_4f238 : fetch_word Ubsan.M.loaded_segments (0x4f238 : word) = Some W_4f238.
Proof. vm_refl. Qed.
Lemma D_4f238 : decode_any W_4f238 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f23c : bv 32 := 0x06813083.
Lemma F_4f23c : fetch_word Ubsan.M.loaded_segments (0x4f23c : word) = Some W_4f23c.
Proof. vm_refl. Qed.
Lemma D_4f23c : decode_any W_4f23c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f240 : bv 32 := 0x06013403.
Lemma F_4f240 : fetch_word Ubsan.M.loaded_segments (0x4f240 : word) = Some W_4f240.
Proof. vm_refl. Qed.
Lemma D_4f240 : decode_any W_4f240 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f244 : bv 32 := 0x05813483.
Lemma F_4f244 : fetch_word Ubsan.M.loaded_segments (0x4f244 : word) = Some W_4f244.
Proof. vm_refl. Qed.
Lemma D_4f244 : decode_any W_4f244 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f248 : bv 32 := 0x05013903.
Lemma F_4f248 : fetch_word Ubsan.M.loaded_segments (0x4f248 : word) = Some W_4f248.
Proof. vm_refl. Qed.
Lemma D_4f248 : decode_any W_4f248 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f24c : bv 32 := 0x04813983.
Lemma F_4f24c : fetch_word Ubsan.M.loaded_segments (0x4f24c : word) = Some W_4f24c.
Proof. vm_refl. Qed.
Lemma D_4f24c : decode_any W_4f24c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f250 : bv 32 := 0x04013a03.
Lemma F_4f250 : fetch_word Ubsan.M.loaded_segments (0x4f250 : word) = Some W_4f250.
Proof. vm_refl. Qed.
Lemma D_4f250 : decode_any W_4f250 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f254 : bv 32 := 0x03813a83.
Lemma F_4f254 : fetch_word Ubsan.M.loaded_segments (0x4f254 : word) = Some W_4f254.
Proof. vm_refl. Qed.
Lemma D_4f254 : decode_any W_4f254 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f258 : bv 32 := 0x03013b03.
Lemma F_4f258 : fetch_word Ubsan.M.loaded_segments (0x4f258 : word) = Some W_4f258.
Proof. vm_refl. Qed.
Lemma D_4f258 : decode_any W_4f258 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f25c : bv 32 := 0x07010113.
Lemma F_4f25c : fetch_word Ubsan.M.loaded_segments (0x4f25c : word) = Some W_4f25c.
Proof. vm_refl. Qed.
Lemma D_4f25c : decode_any W_4f25c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f260 : bv 32 := 0x00008067.
Lemma F_4f260 : fetch_word Ubsan.M.loaded_segments (0x4f260 : word) = Some W_4f260.
Proof. vm_refl. Qed.
Lemma D_4f260 : decode_any W_4f260 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f264 : bv 32 := 0x00800713.
Lemma F_4f264 : fetch_word Ubsan.M.loaded_segments (0x4f264 : word) = Some W_4f264.
Proof. vm_refl. Qed.
Lemma D_4f264 : decode_any W_4f264 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f268 : bv 32 := 0x000a0593.
Lemma F_4f268 : fetch_word Ubsan.M.loaded_segments (0x4f268 : word) = Some W_4f268.
Proof. vm_refl. Qed.
Lemma D_4f268 : decode_any W_4f268 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f26c : bv 32 := 0x00e98733.
Lemma F_4f26c : fetch_word Ubsan.M.loaded_segments (0x4f26c : word) = Some W_4f26c.
Proof. vm_refl. Qed.
Lemma D_4f26c : decode_any W_4f26c = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f270 : bv 32 := 0x00073783.
Lemma F_4f270 : fetch_word Ubsan.M.loaded_segments (0x4f270 : word) = Some W_4f270.
Proof. vm_refl. Qed.
Lemma D_4f270 : decode_any W_4f270 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f274 : bv 32 := 0x40ab0b33.
Lemma F_4f274 : fetch_word Ubsan.M.loaded_segments (0x4f274 : word) = Some W_4f274.
Proof. vm_refl. Qed.
Lemma D_4f274 : decode_any W_4f274 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f278 : bv 32 := 0x0784a503.
Lemma F_4f278 : fetch_word Ubsan.M.loaded_segments (0x4f278 : word) = Some W_4f278.
Proof. vm_refl. Qed.
Lemma D_4f278 : decode_any W_4f278 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f27c : bv 32 := 0x40c9093b.
Lemma F_4f27c : fetch_word Ubsan.M.loaded_segments (0x4f27c : word) = Some W_4f27c.
Proof. vm_refl. Qed.
Lemma D_4f27c : decode_any W_4f27c = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f280 : bv 32 := 0x40d787b3.
Lemma F_4f280 : fetch_word Ubsan.M.loaded_segments (0x4f280 : word) = Some W_4f280.
Proof. vm_refl. Qed.
Lemma D_4f280 : decode_any W_4f280 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f284 : bv 32 := 0x00f73023.
Lemma F_4f284 : fetch_word Ubsan.M.loaded_segments (0x4f284 : word) = Some W_4f284.
Proof. vm_refl. Qed.
Lemma D_4f284 : decode_any W_4f284 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f288 : bv 32 := 0x04200893.
Lemma F_4f288 : fetch_word Ubsan.M.loaded_segments (0x4f288 : word) = Some W_4f288.
Proof. vm_refl. Qed.
Lemma D_4f288 : decode_any W_4f288 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f28c : bv 32 := 0x00090613.
Lemma F_4f28c : fetch_word Ubsan.M.loaded_segments (0x4f28c : word) = Some W_4f28c.
Proof. vm_refl. Qed.
Lemma D_4f28c : decode_any W_4f28c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f290 : bv 32 := 0x00000073.
Lemma F_4f290 : fetch_word Ubsan.M.loaded_segments (0x4f290 : word) = Some W_4f290.
Proof. vm_refl. Qed.
Lemma D_4f290 : decode_any W_4f290 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_4f290 : is_ecall W_4f290 = true.
Proof. reflexivity. Qed.

Definition W_4f294 : bv 32 := 0xe85fc0ef.
Lemma F_4f294 : fetch_word Ubsan.M.loaded_segments (0x4f294 : word) = Some W_4f294.
Proof. vm_refl. Qed.
Lemma D_4f294 : decode_any W_4f294 = Some (Jal 1 2084484, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f298 : bv 32 := 0x000a0993.
Lemma F_4f298 : fetch_word Ubsan.M.loaded_segments (0x4f298 : word) = Some W_4f298.
Proof. vm_refl. Qed.
Lemma D_4f298 : decode_any W_4f298 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f29c : bv 32 := 0xf7650ce3.
Lemma F_4f29c : fetch_word Ubsan.M.loaded_segments (0x4f29c : word) = Some W_4f29c.
Proof. vm_refl. Qed.
Lemma D_4f29c : decode_any W_4f29c = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2a0 : bv 32 := 0x02054c63.
Lemma F_4f2a0 : fetch_word Ubsan.M.loaded_segments (0x4f2a0 : word) = Some W_4f2a0.
Proof. vm_refl. Qed.
Lemma D_4f2a0 : decode_any W_4f2a0 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2a4 : bv 32 := 0x0089b583.
Lemma F_4f2a4 : fetch_word Ubsan.M.loaded_segments (0x4f2a4 : word) = Some W_4f2a4.
Proof. vm_refl. Qed.
Lemma D_4f2a4 : decode_any W_4f2a4 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2a8 : bv 32 := 0x00a5b633.
Lemma F_4f2a8 : fetch_word Ubsan.M.loaded_segments (0x4f2a8 : word) = Some W_4f2a8.
Proof. vm_refl. Qed.
Lemma D_4f2a8 : decode_any W_4f2a8 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2ac : bv 32 := 0x00461a13.
Lemma F_4f2ac : fetch_word Ubsan.M.loaded_segments (0x4f2ac : word) = Some W_4f2ac.
Proof. vm_refl. Qed.
Lemma D_4f2ac : decode_any W_4f2ac = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2b0 : bv 32 := 0x01498a33.
Lemma F_4f2b0 : fetch_word Ubsan.M.loaded_segments (0x4f2b0 : word) = Some W_4f2b0.
Proof. vm_refl. Qed.
Lemma D_4f2b0 : decode_any W_4f2b0 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2b4 : bv 32 := 0x000a3703.
Lemma F_4f2b4 : fetch_word Ubsan.M.loaded_segments (0x4f2b4 : word) = Some W_4f2b4.
Proof. vm_refl. Qed.
Lemma D_4f2b4 : decode_any W_4f2b4 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2b8 : bv 32 := 0x40c006b3.
Lemma F_4f2b8 : fetch_word Ubsan.M.loaded_segments (0x4f2b8 : word) = Some W_4f2b8.
Proof. vm_refl. Qed.
Lemma D_4f2b8 : decode_any W_4f2b8 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2bc : bv 32 := 0x00b6f6b3.
Lemma F_4f2bc : fetch_word Ubsan.M.loaded_segments (0x4f2bc : word) = Some W_4f2bc.
Proof. vm_refl. Qed.
Lemma D_4f2bc : decode_any W_4f2bc = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2c0 : bv 32 := 0x40d506b3.
Lemma F_4f2c0 : fetch_word Ubsan.M.loaded_segments (0x4f2c0 : word) = Some W_4f2c0.
Proof. vm_refl. Qed.
Lemma D_4f2c0 : decode_any W_4f2c0 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2c4 : bv 32 := 0x00d70733.
Lemma F_4f2c4 : fetch_word Ubsan.M.loaded_segments (0x4f2c4 : word) = Some W_4f2c4.
Proof. vm_refl. Qed.
Lemma D_4f2c4 : decode_any W_4f2c4 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2c8 : bv 32 := 0x00ea3023.
Lemma F_4f2c8 : fetch_word Ubsan.M.loaded_segments (0x4f2c8 : word) = Some W_4f2c8.
Proof. vm_refl. Qed.
Lemma D_4f2c8 : decode_any W_4f2c8 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2cc : bv 32 := 0xf8a5fce3.
Lemma F_4f2cc : fetch_word Ubsan.M.loaded_segments (0x4f2cc : word) = Some W_4f2cc.
Proof. vm_refl. Qed.
Lemma D_4f2cc : decode_any W_4f2cc = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2d0 : bv 32 := 0x01800713.
Lemma F_4f2d0 : fetch_word Ubsan.M.loaded_segments (0x4f2d0 : word) = Some W_4f2d0.
Proof. vm_refl. Qed.
Lemma D_4f2d0 : decode_any W_4f2d0 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f2d4 : bv 32 := 0xf95ff06f.
Lemma F_4f2d4 : fetch_word Ubsan.M.loaded_segments (0x4f2d4 : word) = Some W_4f2d4.
Proof. vm_refl. Qed.
Lemma D_4f2d4 : decode_any W_4f2d4 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
