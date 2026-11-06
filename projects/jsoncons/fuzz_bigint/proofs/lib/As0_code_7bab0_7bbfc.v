(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7bab0 : bv 32 := 0xfe010113.
Lemma F_7bab0 : fetch_word Asan.M.loaded_segments (0x7bab0 : word) = Some W_7bab0.
Proof. vm_refl. Qed.
Lemma D_7bab0 : decode_any W_7bab0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bab4 : bv 32 := 0x00113c23.
Lemma F_7bab4 : fetch_word Asan.M.loaded_segments (0x7bab4 : word) = Some W_7bab4.
Proof. vm_refl. Qed.
Lemma D_7bab4 : decode_any W_7bab4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bab8 : bv 32 := 0x00813823.
Lemma F_7bab8 : fetch_word Asan.M.loaded_segments (0x7bab8 : word) = Some W_7bab8.
Proof. vm_refl. Qed.
Lemma D_7bab8 : decode_any W_7bab8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7babc : bv 32 := 0x00913423.
Lemma F_7babc : fetch_word Asan.M.loaded_segments (0x7babc : word) = Some W_7babc.
Proof. vm_refl. Qed.
Lemma D_7babc : decode_any W_7babc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bac0 : bv 32 := 0x01213023.
Lemma F_7bac0 : fetch_word Asan.M.loaded_segments (0x7bac0 : word) = Some W_7bac0.
Proof. vm_refl. Qed.
Lemma D_7bac0 : decode_any W_7bac0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bac4 : bv 32 := 0x00060413.
Lemma F_7bac4 : fetch_word Asan.M.loaded_segments (0x7bac4 : word) = Some W_7bac4.
Proof. vm_refl. Qed.
Lemma D_7bac4 : decode_any W_7bac4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bac8 : bv 32 := 0x00058493.
Lemma F_7bac8 : fetch_word Asan.M.loaded_segments (0x7bac8 : word) = Some W_7bac8.
Proof. vm_refl. Qed.
Lemma D_7bac8 : decode_any W_7bac8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bacc : bv 32 := 0x00058513.
Lemma F_7bacc : fetch_word Asan.M.loaded_segments (0x7bacc : word) = Some W_7bacc.
Proof. vm_refl. Qed.
Lemma D_7bacc : decode_any W_7bacc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bad0 : bv 32 := 0x00060593.
Lemma F_7bad0 : fetch_word Asan.M.loaded_segments (0x7bad0 : word) = Some W_7bad0.
Proof. vm_refl. Qed.
Lemma D_7bad0 : decode_any W_7bad0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bad4 : bv 32 := 0x00068613.
Lemma F_7bad4 : fetch_word Asan.M.loaded_segments (0x7bad4 : word) = Some W_7bad4.
Proof. vm_refl. Qed.
Lemma D_7bad4 : decode_any W_7bad4 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bad8 : bv 32 := 0xf19f70ef.
Lemma F_7bad8 : fetch_word Asan.M.loaded_segments (0x7bad8 : word) = Some W_7bad8.
Proof. vm_refl. Qed.
Lemma D_7bad8 : decode_any W_7bad8 = Some (Jal 1 2064152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7badc : bv 32 := 0x00050e63.
Lemma F_7badc : fetch_word Asan.M.loaded_segments (0x7badc : word) = Some W_7badc.
Proof. vm_refl. Qed.
Lemma D_7badc : decode_any W_7badc = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bae0 : bv 32 := 0x01813083.
Lemma F_7bae0 : fetch_word Asan.M.loaded_segments (0x7bae0 : word) = Some W_7bae0.
Proof. vm_refl. Qed.
Lemma D_7bae0 : decode_any W_7bae0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bae4 : bv 32 := 0x01013403.
Lemma F_7bae4 : fetch_word Asan.M.loaded_segments (0x7bae4 : word) = Some W_7bae4.
Proof. vm_refl. Qed.
Lemma D_7bae4 : decode_any W_7bae4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bae8 : bv 32 := 0x00813483.
Lemma F_7bae8 : fetch_word Asan.M.loaded_segments (0x7bae8 : word) = Some W_7bae8.
Proof. vm_refl. Qed.
Lemma D_7bae8 : decode_any W_7bae8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7baec : bv 32 := 0x00013903.
Lemma F_7baec : fetch_word Asan.M.loaded_segments (0x7baec : word) = Some W_7baec.
Proof. vm_refl. Qed.
Lemma D_7baec : decode_any W_7baec = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7baf0 : bv 32 := 0x02010113.
Lemma F_7baf0 : fetch_word Asan.M.loaded_segments (0x7baf0 : word) = Some W_7baf0.
Proof. vm_refl. Qed.
Lemma D_7baf0 : decode_any W_7baf0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7baf4 : bv 32 := 0x00008067.
Lemma F_7baf4 : fetch_word Asan.M.loaded_segments (0x7baf4 : word) = Some W_7baf4.
Proof. vm_refl. Qed.
Lemma D_7baf4 : decode_any W_7baf4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7baf8 : bv 32 := 0x00050913.
Lemma F_7baf8 : fetch_word Asan.M.loaded_segments (0x7baf8 : word) = Some W_7baf8.
Proof. vm_refl. Qed.
Lemma D_7baf8 : decode_any W_7baf8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bafc : bv 32 := 0x00048513.
Lemma F_7bafc : fetch_word Asan.M.loaded_segments (0x7bafc : word) = Some W_7bafc.
Proof. vm_refl. Qed.
Lemma D_7bafc : decode_any W_7bafc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb00 : bv 32 := 0x00040593.
Lemma F_7bb00 : fetch_word Asan.M.loaded_segments (0x7bb00 : word) = Some W_7bb00.
Proof. vm_refl. Qed.
Lemma D_7bb00 : decode_any W_7bb00 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb04 : bv 32 := 0x020000ef.
Lemma F_7bb04 : fetch_word Asan.M.loaded_segments (0x7bb04 : word) = Some W_7bb04.
Proof. vm_refl. Qed.
Lemma D_7bb04 : decode_any W_7bb04 = Some (Jal 1 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb08 : bv 32 := 0x00090513.
Lemma F_7bb08 : fetch_word Asan.M.loaded_segments (0x7bb08 : word) = Some W_7bb08.
Proof. vm_refl. Qed.
Lemma D_7bb08 : decode_any W_7bb08 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb0c : bv 32 := 0x01813083.
Lemma F_7bb0c : fetch_word Asan.M.loaded_segments (0x7bb0c : word) = Some W_7bb0c.
Proof. vm_refl. Qed.
Lemma D_7bb0c : decode_any W_7bb0c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb10 : bv 32 := 0x01013403.
Lemma F_7bb10 : fetch_word Asan.M.loaded_segments (0x7bb10 : word) = Some W_7bb10.
Proof. vm_refl. Qed.
Lemma D_7bb10 : decode_any W_7bb10 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb14 : bv 32 := 0x00813483.
Lemma F_7bb14 : fetch_word Asan.M.loaded_segments (0x7bb14 : word) = Some W_7bb14.
Proof. vm_refl. Qed.
Lemma D_7bb14 : decode_any W_7bb14 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb18 : bv 32 := 0x00013903.
Lemma F_7bb18 : fetch_word Asan.M.loaded_segments (0x7bb18 : word) = Some W_7bb18.
Proof. vm_refl. Qed.
Lemma D_7bb18 : decode_any W_7bb18 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb1c : bv 32 := 0x02010113.
Lemma F_7bb1c : fetch_word Asan.M.loaded_segments (0x7bb1c : word) = Some W_7bb1c.
Proof. vm_refl. Qed.
Lemma D_7bb1c : decode_any W_7bb1c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb20 : bv 32 := 0x00008067.
Lemma F_7bb20 : fetch_word Asan.M.loaded_segments (0x7bb20 : word) = Some W_7bb20.
Proof. vm_refl. Qed.
Lemma D_7bb20 : decode_any W_7bb20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb24 : bv 32 := 0xfe010113.
Lemma F_7bb24 : fetch_word Asan.M.loaded_segments (0x7bb24 : word) = Some W_7bb24.
Proof. vm_refl. Qed.
Lemma D_7bb24 : decode_any W_7bb24 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb28 : bv 32 := 0x00113c23.
Lemma F_7bb28 : fetch_word Asan.M.loaded_segments (0x7bb28 : word) = Some W_7bb28.
Proof. vm_refl. Qed.
Lemma D_7bb28 : decode_any W_7bb28 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb2c : bv 32 := 0x00813823.
Lemma F_7bb2c : fetch_word Asan.M.loaded_segments (0x7bb2c : word) = Some W_7bb2c.
Proof. vm_refl. Qed.
Lemma D_7bb2c : decode_any W_7bb2c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb30 : bv 32 := 0x00913423.
Lemma F_7bb30 : fetch_word Asan.M.loaded_segments (0x7bb30 : word) = Some W_7bb30.
Proof. vm_refl. Qed.
Lemma D_7bb30 : decode_any W_7bb30 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb34 : bv 32 := 0x01213023.
Lemma F_7bb34 : fetch_word Asan.M.loaded_segments (0x7bb34 : word) = Some W_7bb34.
Proof. vm_refl. Qed.
Lemma D_7bb34 : decode_any W_7bb34 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb38 : bv 32 := 0x0005a617.
Lemma F_7bb38 : fetch_word Asan.M.loaded_segments (0x7bb38 : word) = Some W_7bb38.
Proof. vm_refl. Qed.
Lemma D_7bb38 : decode_any W_7bb38 = Some (Auipc 12 90, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb3c : bv 32 := 0xdc063603.
Lemma F_7bb3c : fetch_word Asan.M.loaded_segments (0x7bb3c : word) = Some W_7bb3c.
Proof. vm_refl. Qed.
Lemma D_7bb3c : decode_any W_7bb3c = Some (Load SZ8 true 12 12 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb40 : bv 32 := 0x06060e63.
Lemma F_7bb40 : fetch_word Asan.M.loaded_segments (0x7bb40 : word) = Some W_7bb40.
Proof. vm_refl. Qed.
Lemma D_7bb40 : decode_any W_7bb40 = Some (Branch BC_EQ 12 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb44 : bv 32 := 0x00050413.
Lemma F_7bb44 : fetch_word Asan.M.loaded_segments (0x7bb44 : word) = Some W_7bb44.
Proof. vm_refl. Qed.
Lemma D_7bb44 : decode_any W_7bb44 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb48 : bv 32 := 0x0005a517.
Lemma F_7bb48 : fetch_word Asan.M.loaded_segments (0x7bb48 : word) = Some W_7bb48.
Proof. vm_refl. Qed.
Lemma D_7bb48 : decode_any W_7bb48 = Some (Auipc 10 90, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb4c : bv 32 := 0xd5053903.
Lemma F_7bb4c : fetch_word Asan.M.loaded_segments (0x7bb4c : word) = Some W_7bb4c.
Proof. vm_refl. Qed.
Lemma D_7bb4c : decode_any W_7bb4c = Some (Load SZ8 true 18 10 3408, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb50 : bv 32 := 0x00093503.
Lemma F_7bb50 : fetch_word Asan.M.loaded_segments (0x7bb50 : word) = Some W_7bb50.
Proof. vm_refl. Qed.
Lemma D_7bb50 : decode_any W_7bb50 = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb54 : bv 32 := 0x00051a63.
Lemma F_7bb54 : fetch_word Asan.M.loaded_segments (0x7bb54 : word) = Some W_7bb54.
Proof. vm_refl. Qed.
Lemma D_7bb54 : decode_any W_7bb54 = Some (Branch BC_NE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb58 : bv 32 := 0x00058493.
Lemma F_7bb58 : fetch_word Asan.M.loaded_segments (0x7bb58 : word) = Some W_7bb58.
Proof. vm_refl. Qed.
Lemma D_7bb58 : decode_any W_7bb58 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb5c : bv 32 := 0xf31f60ef.
Lemma F_7bb5c : fetch_word Asan.M.loaded_segments (0x7bb5c : word) = Some W_7bb5c.
Proof. vm_refl. Qed.
Lemma D_7bb5c : decode_any W_7bb5c = Some (Jal 1 2060080, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb60 : bv 32 := 0x00048593.
Lemma F_7bb60 : fetch_word Asan.M.loaded_segments (0x7bb60 : word) = Some W_7bb60.
Proof. vm_refl. Qed.
Lemma D_7bb60 : decode_any W_7bb60 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb64 : bv 32 := 0x00a93023.
Lemma F_7bb64 : fetch_word Asan.M.loaded_segments (0x7bb64 : word) = Some W_7bb64.
Proof. vm_refl. Qed.
Lemma D_7bb64 : decode_any W_7bb64 = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb68 : bv 32 := 0xfff50613.
Lemma F_7bb68 : fetch_word Asan.M.loaded_segments (0x7bb68 : word) = Some W_7bb68.
Proof. vm_refl. Qed.
Lemma D_7bb68 : decode_any W_7bb68 = Some (OpImm ALU_ADD 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb6c : bv 32 := 0x00c57633.
Lemma F_7bb6c : fetch_word Asan.M.loaded_segments (0x7bb6c : word) = Some W_7bb6c.
Proof. vm_refl. Qed.
Lemma D_7bb6c : decode_any W_7bb6c = Some (Op ALU_AND 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb70 : bv 32 := 0x06061c63.
Lemma F_7bb70 : fetch_word Asan.M.loaded_segments (0x7bb70 : word) = Some W_7bb70.
Proof. vm_refl. Qed.
Lemma D_7bb70 : decode_any W_7bb70 = Some (Branch BC_NE 12 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb74 : bv 32 := 0x00a585b3.
Lemma F_7bb74 : fetch_word Asan.M.loaded_segments (0x7bb74 : word) = Some W_7bb74.
Proof. vm_refl. Qed.
Lemma D_7bb74 : decode_any W_7bb74 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb78 : bv 32 := 0xfff58493.
Lemma F_7bb78 : fetch_word Asan.M.loaded_segments (0x7bb78 : word) = Some W_7bb78.
Proof. vm_refl. Qed.
Lemma D_7bb78 : decode_any W_7bb78 = Some (OpImm ALU_ADD 9 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb7c : bv 32 := 0x40a005b3.
Lemma F_7bb7c : fetch_word Asan.M.loaded_segments (0x7bb7c : word) = Some W_7bb7c.
Proof. vm_refl. Qed.
Lemma D_7bb7c : decode_any W_7bb7c = Some (Op ALU_SUB 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb80 : bv 32 := 0x00b4f4b3.
Lemma F_7bb80 : fetch_word Asan.M.loaded_segments (0x7bb80 : word) = Some W_7bb80.
Proof. vm_refl. Qed.
Lemma D_7bb80 : decode_any W_7bb80 = Some (Op ALU_AND 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb84 : bv 32 := 0x00051863.
Lemma F_7bb84 : fetch_word Asan.M.loaded_segments (0x7bb84 : word) = Some W_7bb84.
Proof. vm_refl. Qed.
Lemma D_7bb84 : decode_any W_7bb84 = Some (Branch BC_NE 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb88 : bv 32 := 0xf05f60ef.
Lemma F_7bb88 : fetch_word Asan.M.loaded_segments (0x7bb88 : word) = Some W_7bb88.
Proof. vm_refl. Qed.
Lemma D_7bb88 : decode_any W_7bb88 = Some (Jal 1 2060036, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb8c : bv 32 := 0x00a93023.
Lemma F_7bb8c : fetch_word Asan.M.loaded_segments (0x7bb8c : word) = Some W_7bb8c.
Proof. vm_refl. Qed.
Lemma D_7bb8c : decode_any W_7bb8c = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb90 : bv 32 := 0x40a005b3.
Lemma F_7bb90 : fetch_word Asan.M.loaded_segments (0x7bb90 : word) = Some W_7bb90.
Proof. vm_refl. Qed.
Lemma D_7bb90 : decode_any W_7bb90 = Some (Op ALU_SUB 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb94 : bv 32 := 0x00b47433.
Lemma F_7bb94 : fetch_word Asan.M.loaded_segments (0x7bb94 : word) = Some W_7bb94.
Proof. vm_refl. Qed.
Lemma D_7bb94 : decode_any W_7bb94 = Some (Op ALU_AND 8 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb98 : bv 32 := 0x00104537.
Lemma F_7bb98 : fetch_word Asan.M.loaded_segments (0x7bb98 : word) = Some W_7bb98.
Proof. vm_refl. Qed.
Lemma D_7bb98 : decode_any W_7bb98 = Some (Lui 10 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bb9c : bv 32 := 0x0225069b.
Lemma F_7bb9c : fetch_word Asan.M.loaded_segments (0x7bb9c : word) = Some W_7bb9c.
Proof. vm_refl. Qed.
Lemma D_7bb9c : decode_any W_7bb9c = Some (OpImm32 13 10 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bba0 : bv 32 := 0xfff00713.
Lemma F_7bba0 : fetch_word Asan.M.loaded_segments (0x7bba0 : word) = Some W_7bba0.
Proof. vm_refl. Qed.
Lemma D_7bba0 : decode_any W_7bba0 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bba4 : bv 32 := 0x00040513.
Lemma F_7bba4 : fetch_word Asan.M.loaded_segments (0x7bba4 : word) = Some W_7bba4.
Proof. vm_refl. Qed.
Lemma D_7bba4 : decode_any W_7bba4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bba8 : bv 32 := 0x00048593.
Lemma F_7bba8 : fetch_word Asan.M.loaded_segments (0x7bba8 : word) = Some W_7bba8.
Proof. vm_refl. Qed.
Lemma D_7bba8 : decode_any W_7bba8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbac : bv 32 := 0x00000613.
Lemma F_7bbac : fetch_word Asan.M.loaded_segments (0x7bbac : word) = Some W_7bbac.
Proof. vm_refl. Qed.
Lemma D_7bbac : decode_any W_7bbac = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbb0 : bv 32 := 0x00000793.
Lemma F_7bbb0 : fetch_word Asan.M.loaded_segments (0x7bbb0 : word) = Some W_7bbb0.
Proof. vm_refl. Qed.
Lemma D_7bbb0 : decode_any W_7bbb0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbb4 : bv 32 := 0xfadf50ef.
Lemma F_7bbb4 : fetch_word Asan.M.loaded_segments (0x7bbb4 : word) = Some W_7bbb4.
Proof. vm_refl. Qed.
Lemma D_7bbb4 : decode_any W_7bbb4 = Some (Jal 1 2056108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbb8 : bv 32 := 0x00851e63.
Lemma F_7bbb8 : fetch_word Asan.M.loaded_segments (0x7bbb8 : word) = Some W_7bbb8.
Proof. vm_refl. Qed.
Lemma D_7bbb8 : decode_any W_7bbb8 = Some (Branch BC_NE 10 8 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbbc : bv 32 := 0x01813083.
Lemma F_7bbbc : fetch_word Asan.M.loaded_segments (0x7bbbc : word) = Some W_7bbbc.
Proof. vm_refl. Qed.
Lemma D_7bbbc : decode_any W_7bbbc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbc0 : bv 32 := 0x01013403.
Lemma F_7bbc0 : fetch_word Asan.M.loaded_segments (0x7bbc0 : word) = Some W_7bbc0.
Proof. vm_refl. Qed.
Lemma D_7bbc0 : decode_any W_7bbc0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbc4 : bv 32 := 0x00813483.
Lemma F_7bbc4 : fetch_word Asan.M.loaded_segments (0x7bbc4 : word) = Some W_7bbc4.
Proof. vm_refl. Qed.
Lemma D_7bbc4 : decode_any W_7bbc4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbc8 : bv 32 := 0x00013903.
Lemma F_7bbc8 : fetch_word Asan.M.loaded_segments (0x7bbc8 : word) = Some W_7bbc8.
Proof. vm_refl. Qed.
Lemma D_7bbc8 : decode_any W_7bbc8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbcc : bv 32 := 0x02010113.
Lemma F_7bbcc : fetch_word Asan.M.loaded_segments (0x7bbcc : word) = Some W_7bbcc.
Proof. vm_refl. Qed.
Lemma D_7bbcc : decode_any W_7bbcc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbd0 : bv 32 := 0x00008067.
Lemma F_7bbd0 : fetch_word Asan.M.loaded_segments (0x7bbd0 : word) = Some W_7bbd0.
Proof. vm_refl. Qed.
Lemma D_7bbd0 : decode_any W_7bbd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbd4 : bv 32 := 0x0005a517.
Lemma F_7bbd4 : fetch_word Asan.M.loaded_segments (0x7bbd4 : word) = Some W_7bbd4.
Proof. vm_refl. Qed.
Lemma D_7bbd4 : decode_any W_7bbd4 = Some (Auipc 10 90, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbd8 : bv 32 := 0xd2c53503.
Lemma F_7bbd8 : fetch_word Asan.M.loaded_segments (0x7bbd8 : word) = Some W_7bbd8.
Proof. vm_refl. Qed.
Lemma D_7bbd8 : decode_any W_7bbd8 = Some (Load SZ8 true 10 10 3372, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbdc : bv 32 := 0x00052503.
Lemma F_7bbdc : fetch_word Asan.M.loaded_segments (0x7bbdc : word) = Some W_7bbdc.
Proof. vm_refl. Qed.
Lemma D_7bbdc : decode_any W_7bbdc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbe0 : bv 32 := 0x00051c63.
Lemma F_7bbe0 : fetch_word Asan.M.loaded_segments (0x7bbe0 : word) = Some W_7bbe0.
Proof. vm_refl. Qed.
Lemma D_7bbe0 : decode_any W_7bbe0 = Some (Branch BC_NE 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbe4 : bv 32 := 0x0000006f.
Lemma F_7bbe4 : fetch_word Asan.M.loaded_segments (0x7bbe4 : word) = Some W_7bbe4.
Proof. vm_refl. Qed.
Lemma D_7bbe4 : decode_any W_7bbe4 = Some (Jal 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbe8 : bv 32 := 0xfff97517.
Lemma F_7bbe8 : fetch_word Asan.M.loaded_segments (0x7bbe8 : word) = Some W_7bbe8.
Proof. vm_refl. Qed.
Lemma D_7bbe8 : decode_any W_7bbe8 = Some (Auipc 10 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbec : bv 32 := 0xb8250513.
Lemma F_7bbec : fetch_word Asan.M.loaded_segments (0x7bbec : word) = Some W_7bbec.
Proof. vm_refl. Qed.
Lemma D_7bbec : decode_any W_7bbec = Some (OpImm ALU_ADD 10 10 2946, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbf0 : bv 32 := 0xe24f20ef.
Lemma F_7bbf0 : fetch_word Asan.M.loaded_segments (0x7bbf0 : word) = Some W_7bbf0.
Proof. vm_refl. Qed.
Lemma D_7bbf0 : decode_any W_7bbf0 = Some (Jal 1 2041380, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbf4 : bv 32 := 0xba8fd0ef.
Lemma F_7bbf4 : fetch_word Asan.M.loaded_segments (0x7bbf4 : word) = Some W_7bbf4.
Proof. vm_refl. Qed.
Lemma D_7bbf4 : decode_any W_7bbf4 = Some (Jal 1 2085800, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bbf8 : bv 32 := 0xcccff0ef.
Lemma F_7bbf8 : fetch_word Asan.M.loaded_segments (0x7bbf8 : word) = Some W_7bbf8.
Proof. vm_refl. Qed.
Lemma D_7bbf8 : decode_any W_7bbf8 = Some (Jal 1 2094284, 4%Z).
Proof. vm_refl. Qed.
