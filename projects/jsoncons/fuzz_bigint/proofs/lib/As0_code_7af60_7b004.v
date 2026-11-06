(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7af60 : bv 32 := 0xfe010113.
Lemma F_7af60 : fetch_word Asan.M.loaded_segments (0x7af60 : word) = Some W_7af60.
Proof. vm_refl. Qed.
Lemma D_7af60 : decode_any W_7af60 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af64 : bv 32 := 0x00113c23.
Lemma F_7af64 : fetch_word Asan.M.loaded_segments (0x7af64 : word) = Some W_7af64.
Proof. vm_refl. Qed.
Lemma D_7af64 : decode_any W_7af64 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af68 : bv 32 := 0x00813823.
Lemma F_7af68 : fetch_word Asan.M.loaded_segments (0x7af68 : word) = Some W_7af68.
Proof. vm_refl. Qed.
Lemma D_7af68 : decode_any W_7af68 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af6c : bv 32 := 0x00913423.
Lemma F_7af6c : fetch_word Asan.M.loaded_segments (0x7af6c : word) = Some W_7af6c.
Proof. vm_refl. Qed.
Lemma D_7af6c : decode_any W_7af6c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af70 : bv 32 := 0x01213023.
Lemma F_7af70 : fetch_word Asan.M.loaded_segments (0x7af70 : word) = Some W_7af70.
Proof. vm_refl. Qed.
Lemma D_7af70 : decode_any W_7af70 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af74 : bv 32 := 0x00058413.
Lemma F_7af74 : fetch_word Asan.M.loaded_segments (0x7af74 : word) = Some W_7af74.
Proof. vm_refl. Qed.
Lemma D_7af74 : decode_any W_7af74 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af78 : bv 32 := 0x0005b597.
Lemma F_7af78 : fetch_word Asan.M.loaded_segments (0x7af78 : word) = Some W_7af78.
Proof. vm_refl. Qed.
Lemma D_7af78 : decode_any W_7af78 = Some (Auipc 11 91, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af7c : bv 32 := 0x9205b903.
Lemma F_7af7c : fetch_word Asan.M.loaded_segments (0x7af7c : word) = Some W_7af7c.
Proof. vm_refl. Qed.
Lemma D_7af7c : decode_any W_7af7c = Some (Load SZ8 true 18 11 2336, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af80 : bv 32 := 0x00093583.
Lemma F_7af80 : fetch_word Asan.M.loaded_segments (0x7af80 : word) = Some W_7af80.
Proof. vm_refl. Qed.
Lemma D_7af80 : decode_any W_7af80 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af84 : bv 32 := 0x00050493.
Lemma F_7af84 : fetch_word Asan.M.loaded_segments (0x7af84 : word) = Some W_7af84.
Proof. vm_refl. Qed.
Lemma D_7af84 : decode_any W_7af84 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af88 : bv 32 := 0x00059863.
Lemma F_7af88 : fetch_word Asan.M.loaded_segments (0x7af88 : word) = Some W_7af88.
Proof. vm_refl. Qed.
Lemma D_7af88 : decode_any W_7af88 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af8c : bv 32 := 0xb01f70ef.
Lemma F_7af8c : fetch_word Asan.M.loaded_segments (0x7af8c : word) = Some W_7af8c.
Proof. vm_refl. Qed.
Lemma D_7af8c : decode_any W_7af8c = Some (Jal 1 2063104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af90 : bv 32 := 0x00050593.
Lemma F_7af90 : fetch_word Asan.M.loaded_segments (0x7af90 : word) = Some W_7af90.
Proof. vm_refl. Qed.
Lemma D_7af90 : decode_any W_7af90 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af94 : bv 32 := 0x00a93023.
Lemma F_7af94 : fetch_word Asan.M.loaded_segments (0x7af94 : word) = Some W_7af94.
Proof. vm_refl. Qed.
Lemma D_7af94 : decode_any W_7af94 = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af98 : bv 32 := 0xfff58513.
Lemma F_7af98 : fetch_word Asan.M.loaded_segments (0x7af98 : word) = Some W_7af98.
Proof. vm_refl. Qed.
Lemma D_7af98 : decode_any W_7af98 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7af9c : bv 32 := 0x00a5f533.
Lemma F_7af9c : fetch_word Asan.M.loaded_segments (0x7af9c : word) = Some W_7af9c.
Proof. vm_refl. Qed.
Lemma D_7af9c : decode_any W_7af9c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afa0 : bv 32 := 0x04051a63.
Lemma F_7afa0 : fetch_word Asan.M.loaded_segments (0x7afa0 : word) = Some W_7afa0.
Proof. vm_refl. Qed.
Lemma D_7afa0 : decode_any W_7afa0 = Some (Branch BC_NE 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afa4 : bv 32 := 0x00b484b3.
Lemma F_7afa4 : fetch_word Asan.M.loaded_segments (0x7afa4 : word) = Some W_7afa4.
Proof. vm_refl. Qed.
Lemma D_7afa4 : decode_any W_7afa4 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afa8 : bv 32 := 0x40b005b3.
Lemma F_7afa8 : fetch_word Asan.M.loaded_segments (0x7afa8 : word) = Some W_7afa8.
Proof. vm_refl. Qed.
Lemma D_7afa8 : decode_any W_7afa8 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afac : bv 32 := 0xfff48513.
Lemma F_7afac : fetch_word Asan.M.loaded_segments (0x7afac : word) = Some W_7afac.
Proof. vm_refl. Qed.
Lemma D_7afac : decode_any W_7afac = Some (OpImm ALU_ADD 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afb0 : bv 32 := 0x00b57533.
Lemma F_7afb0 : fetch_word Asan.M.loaded_segments (0x7afb0 : word) = Some W_7afb0.
Proof. vm_refl. Qed.
Lemma D_7afb0 : decode_any W_7afb0 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afb4 : bv 32 := 0x00b475b3.
Lemma F_7afb4 : fetch_word Asan.M.loaded_segments (0x7afb4 : word) = Some W_7afb4.
Proof. vm_refl. Qed.
Lemma D_7afb4 : decode_any W_7afb4 = Some (Op ALU_AND 11 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afb8 : bv 32 := 0x02b57263.
Lemma F_7afb8 : fetch_word Asan.M.loaded_segments (0x7afb8 : word) = Some W_7afb8.
Proof. vm_refl. Qed.
Lemma D_7afb8 : decode_any W_7afb8 = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afbc : bv 32 := 0x40a585b3.
Lemma F_7afbc : fetch_word Asan.M.loaded_segments (0x7afbc : word) = Some W_7afbc.
Proof. vm_refl. Qed.
Lemma D_7afbc : decode_any W_7afbc = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afc0 : bv 32 := 0x00400613.
Lemma F_7afc0 : fetch_word Asan.M.loaded_segments (0x7afc0 : word) = Some W_7afc0.
Proof. vm_refl. Qed.
Lemma D_7afc0 : decode_any W_7afc0 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afc4 : bv 32 := 0x01813083.
Lemma F_7afc4 : fetch_word Asan.M.loaded_segments (0x7afc4 : word) = Some W_7afc4.
Proof. vm_refl. Qed.
Lemma D_7afc4 : decode_any W_7afc4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afc8 : bv 32 := 0x01013403.
Lemma F_7afc8 : fetch_word Asan.M.loaded_segments (0x7afc8 : word) = Some W_7afc8.
Proof. vm_refl. Qed.
Lemma D_7afc8 : decode_any W_7afc8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afcc : bv 32 := 0x00813483.
Lemma F_7afcc : fetch_word Asan.M.loaded_segments (0x7afcc : word) = Some W_7afcc.
Proof. vm_refl. Qed.
Lemma D_7afcc : decode_any W_7afcc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afd0 : bv 32 := 0x00013903.
Lemma F_7afd0 : fetch_word Asan.M.loaded_segments (0x7afd0 : word) = Some W_7afd0.
Proof. vm_refl. Qed.
Lemma D_7afd0 : decode_any W_7afd0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afd4 : bv 32 := 0x02010113.
Lemma F_7afd4 : fetch_word Asan.M.loaded_segments (0x7afd4 : word) = Some W_7afd4.
Proof. vm_refl. Qed.
Lemma D_7afd4 : decode_any W_7afd4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afd8 : bv 32 := 0xbb1f606f.
Lemma F_7afd8 : fetch_word Asan.M.loaded_segments (0x7afd8 : word) = Some W_7afd8.
Proof. vm_refl. Qed.
Lemma D_7afd8 : decode_any W_7afd8 = Some (Jal 0 2059184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afdc : bv 32 := 0x01813083.
Lemma F_7afdc : fetch_word Asan.M.loaded_segments (0x7afdc : word) = Some W_7afdc.
Proof. vm_refl. Qed.
Lemma D_7afdc : decode_any W_7afdc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afe0 : bv 32 := 0x01013403.
Lemma F_7afe0 : fetch_word Asan.M.loaded_segments (0x7afe0 : word) = Some W_7afe0.
Proof. vm_refl. Qed.
Lemma D_7afe0 : decode_any W_7afe0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afe4 : bv 32 := 0x00813483.
Lemma F_7afe4 : fetch_word Asan.M.loaded_segments (0x7afe4 : word) = Some W_7afe4.
Proof. vm_refl. Qed.
Lemma D_7afe4 : decode_any W_7afe4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afe8 : bv 32 := 0x00013903.
Lemma F_7afe8 : fetch_word Asan.M.loaded_segments (0x7afe8 : word) = Some W_7afe8.
Proof. vm_refl. Qed.
Lemma D_7afe8 : decode_any W_7afe8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7afec : bv 32 := 0x02010113.
Lemma F_7afec : fetch_word Asan.M.loaded_segments (0x7afec : word) = Some W_7afec.
Proof. vm_refl. Qed.
Lemma D_7afec : decode_any W_7afec = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aff0 : bv 32 := 0x00008067.
Lemma F_7aff0 : fetch_word Asan.M.loaded_segments (0x7aff0 : word) = Some W_7aff0.
Proof. vm_refl. Qed.
Lemma D_7aff0 : decode_any W_7aff0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aff4 : bv 32 := 0xfff97517.
Lemma F_7aff4 : fetch_word Asan.M.loaded_segments (0x7aff4 : word) = Some W_7aff4.
Proof. vm_refl. Qed.
Lemma D_7aff4 : decode_any W_7aff4 = Some (Auipc 10 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aff8 : bv 32 := 0x77650513.
Lemma F_7aff8 : fetch_word Asan.M.loaded_segments (0x7aff8 : word) = Some W_7aff8.
Proof. vm_refl. Qed.
Lemma D_7aff8 : decode_any W_7aff8 = Some (OpImm ALU_ADD 10 10 1910, 4%Z).
Proof. vm_refl. Qed.

Definition W_7affc : bv 32 := 0xa18f30ef.
Lemma F_7affc : fetch_word Asan.M.loaded_segments (0x7affc : word) = Some W_7affc.
Proof. vm_refl. Qed.
Lemma D_7affc : decode_any W_7affc = Some (Jal 1 2044440, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b000 : bv 32 := 0xf9dfd0ef.
Lemma F_7b000 : fetch_word Asan.M.loaded_segments (0x7b000 : word) = Some W_7b000.
Proof. vm_refl. Qed.
Lemma D_7b000 : decode_any W_7b000 = Some (Jal 1 2088860, 4%Z).
Proof. vm_refl. Qed.
