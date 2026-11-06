(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9bb00 : bv 32 := 0xfd010113.
Lemma F_9bb00 : fetch_word Plain.M.loaded_segments (0x9bb4c : word) = Some W_9bb00.
Proof. vm_refl. Qed.
Lemma D_9bb00 : decode_any W_9bb00 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb04 : bv 32 := 0x02113423.
Lemma F_9bb04 : fetch_word Plain.M.loaded_segments (0x9bb50 : word) = Some W_9bb04.
Proof. vm_refl. Qed.
Lemma D_9bb04 : decode_any W_9bb04 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb08 : bv 32 := 0x02813023.
Lemma F_9bb08 : fetch_word Plain.M.loaded_segments (0x9bb54 : word) = Some W_9bb08.
Proof. vm_refl. Qed.
Lemma D_9bb08 : decode_any W_9bb08 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb0c : bv 32 := 0x00913c23.
Lemma F_9bb0c : fetch_word Plain.M.loaded_segments (0x9bb58 : word) = Some W_9bb0c.
Proof. vm_refl. Qed.
Lemma D_9bb0c : decode_any W_9bb0c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb10 : bv 32 := 0x01213823.
Lemma F_9bb10 : fetch_word Plain.M.loaded_segments (0x9bb5c : word) = Some W_9bb10.
Proof. vm_refl. Qed.
Lemma D_9bb10 : decode_any W_9bb10 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb14 : bv 32 := 0x01313423.
Lemma F_9bb14 : fetch_word Plain.M.loaded_segments (0x9bb60 : word) = Some W_9bb14.
Proof. vm_refl. Qed.
Lemma D_9bb14 : decode_any W_9bb14 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb18 : bv 32 := 0x0004f517.
Lemma F_9bb18 : fetch_word Plain.M.loaded_segments (0x9bb64 : word) = Some W_9bb18.
Proof. vm_refl. Qed.
Lemma D_9bb18 : decode_any W_9bb18 = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb1c : bv 32 := 0x52450913.
Lemma F_9bb1c : fetch_word Plain.M.loaded_segments (0x9bb68 : word) = Some W_9bb1c.
Proof. vm_refl. Qed.
Lemma D_9bb1c : decode_any W_9bb1c = Some (OpImm ALU_ADD 18 10 1316, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb20 : bv 32 := 0x00490413.
Lemma F_9bb20 : fetch_word Plain.M.loaded_segments (0x9bb6c : word) = Some W_9bb20.
Proof. vm_refl. Qed.
Lemma D_9bb20 : decode_any W_9bb20 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb24 : bv 32 := 0x00040513.
Lemma F_9bb24 : fetch_word Plain.M.loaded_segments (0x9bb70 : word) = Some W_9bb24.
Proof. vm_refl. Qed.
Lemma D_9bb24 : decode_any W_9bb24 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb28 : bv 32 := 0x5a8110ef.
Lemma F_9bb28 : fetch_word Plain.M.loaded_segments (0x9bb74 : word) = Some W_9bb28.
Proof. vm_refl. Qed.
Lemma D_9bb28 : decode_any W_9bb28 = Some (Jal 1 71080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb2c : bv 32 := 0x01093503.
Lemma F_9bb2c : fetch_word Plain.M.loaded_segments (0x9bb78 : word) = Some W_9bb2c.
Proof. vm_refl. Qed.
Lemma D_9bb2c : decode_any W_9bb2c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb30 : bv 32 := 0x06050863.
Lemma F_9bb30 : fetch_word Plain.M.loaded_segments (0x9bb7c : word) = Some W_9bb30.
Proof. vm_refl. Qed.
Lemma D_9bb30 : decode_any W_9bb30 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb34 : bv 32 := 0x00892583.
Lemma F_9bb34 : fetch_word Plain.M.loaded_segments (0x9bb80 : word) = Some W_9bb34.
Proof. vm_refl. Qed.
Lemma D_9bb34 : decode_any W_9bb34 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb38 : bv 32 := 0x0180006f.
Lemma F_9bb38 : fetch_word Plain.M.loaded_segments (0x9bb84 : word) = Some W_9bb38.
Proof. vm_refl. Qed.
Lemma D_9bb38 : decode_any W_9bb38 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb3c : bv 32 := 0x00053503.
Lemma F_9bb3c : fetch_word Plain.M.loaded_segments (0x9bb88 : word) = Some W_9bb3c.
Proof. vm_refl. Qed.
Lemma D_9bb3c : decode_any W_9bb3c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb40 : bv 32 := 0x02000593.
Lemma F_9bb40 : fetch_word Plain.M.loaded_segments (0x9bb8c : word) = Some W_9bb40.
Proof. vm_refl. Qed.
Lemma D_9bb40 : decode_any W_9bb40 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb44 : bv 32 := 0x00b92423.
Lemma F_9bb44 : fetch_word Plain.M.loaded_segments (0x9bb90 : word) = Some W_9bb44.
Proof. vm_refl. Qed.
Lemma D_9bb44 : decode_any W_9bb44 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb48 : bv 32 := 0x00a93823.
Lemma F_9bb48 : fetch_word Plain.M.loaded_segments (0x9bb94 : word) = Some W_9bb48.
Proof. vm_refl. Qed.
Lemma D_9bb48 : decode_any W_9bb48 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb4c : bv 32 := 0x04050a63.
Lemma F_9bb4c : fetch_word Plain.M.loaded_segments (0x9bb98 : word) = Some W_9bb4c.
Proof. vm_refl. Qed.
Lemma D_9bb4c : decode_any W_9bb4c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb50 : bv 32 := 0xfff5861b.
Lemma F_9bb50 : fetch_word Plain.M.loaded_segments (0x9bb9c : word) = Some W_9bb50.
Proof. vm_refl. Qed.
Lemma D_9bb50 : decode_any W_9bb50 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb54 : bv 32 := 0x00c92423.
Lemma F_9bb54 : fetch_word Plain.M.loaded_segments (0x9bba0 : word) = Some W_9bb54.
Proof. vm_refl. Qed.
Lemma D_9bb54 : decode_any W_9bb54 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb58 : bv 32 := 0xfeb052e3.
Lemma F_9bb58 : fetch_word Plain.M.loaded_segments (0x9bba4 : word) = Some W_9bb58.
Proof. vm_refl. Qed.
Lemma D_9bb58 : decode_any W_9bb58 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb5c : bv 32 := 0x01093503.
Lemma F_9bb5c : fetch_word Plain.M.loaded_segments (0x9bba8 : word) = Some W_9bb5c.
Proof. vm_refl. Qed.
Lemma D_9bb5c : decode_any W_9bb5c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb60 : bv 32 := 0x00361613.
Lemma F_9bb60 : fetch_word Plain.M.loaded_segments (0x9bbac : word) = Some W_9bb60.
Proof. vm_refl. Qed.
Lemma D_9bb60 : decode_any W_9bb60 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb64 : bv 32 := 0x00c50533.
Lemma F_9bb64 : fetch_word Plain.M.loaded_segments (0x9bbb0 : word) = Some W_9bb64.
Proof. vm_refl. Qed.
Lemma D_9bb64 : decode_any W_9bb64 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb68 : bv 32 := 0x00853983.
Lemma F_9bb68 : fetch_word Plain.M.loaded_segments (0x9bbb4 : word) = Some W_9bb68.
Proof. vm_refl. Qed.
Lemma D_9bb68 : decode_any W_9bb68 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb6c : bv 32 := 0x10853483.
Lemma F_9bb6c : fetch_word Plain.M.loaded_segments (0x9bbb8 : word) = Some W_9bb6c.
Proof. vm_refl. Qed.
Lemma D_9bb6c : decode_any W_9bb6c = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb70 : bv 32 := 0x00040513.
Lemma F_9bb70 : fetch_word Plain.M.loaded_segments (0x9bbbc : word) = Some W_9bb70.
Proof. vm_refl. Qed.
Lemma D_9bb70 : decode_any W_9bb70 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb74 : bv 32 := 0x7e4110ef.
Lemma F_9bb74 : fetch_word Plain.M.loaded_segments (0x9bbc0 : word) = Some W_9bb74.
Proof. vm_refl. Qed.
Lemma D_9bb74 : decode_any W_9bb74 = Some (Jal 1 71652, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb78 : bv 32 := 0x00048513.
Lemma F_9bb78 : fetch_word Plain.M.loaded_segments (0x9bbc4 : word) = Some W_9bb78.
Proof. vm_refl. Qed.
Lemma D_9bb78 : decode_any W_9bb78 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb7c : bv 32 := 0x000980e7.
Lemma F_9bb7c : fetch_word Plain.M.loaded_segments (0x9bbc8 : word) = Some W_9bb7c.
Proof. vm_refl. Qed.
Lemma D_9bb7c : decode_any W_9bb7c = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb80 : bv 32 := 0x00040513.
Lemma F_9bb80 : fetch_word Plain.M.loaded_segments (0x9bbcc : word) = Some W_9bb80.
Proof. vm_refl. Qed.
Lemma D_9bb80 : decode_any W_9bb80 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb84 : bv 32 := 0x54c110ef.
Lemma F_9bb84 : fetch_word Plain.M.loaded_segments (0x9bbd0 : word) = Some W_9bb84.
Proof. vm_refl. Qed.
Lemma D_9bb84 : decode_any W_9bb84 = Some (Jal 1 70988, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb88 : bv 32 := 0x00892503.
Lemma F_9bb88 : fetch_word Plain.M.loaded_segments (0x9bbd4 : word) = Some W_9bb88.
Proof. vm_refl. Qed.
Lemma D_9bb88 : decode_any W_9bb88 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb8c : bv 32 := 0xfff5061b.
Lemma F_9bb8c : fetch_word Plain.M.loaded_segments (0x9bbd8 : word) = Some W_9bb8c.
Proof. vm_refl. Qed.
Lemma D_9bb8c : decode_any W_9bb8c = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb90 : bv 32 := 0x00c92423.
Lemma F_9bb90 : fetch_word Plain.M.loaded_segments (0x9bbdc : word) = Some W_9bb90.
Proof. vm_refl. Qed.
Lemma D_9bb90 : decode_any W_9bb90 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb94 : bv 32 := 0xfca044e3.
Lemma F_9bb94 : fetch_word Plain.M.loaded_segments (0x9bbe0 : word) = Some W_9bb94.
Proof. vm_refl. Qed.
Lemma D_9bb94 : decode_any W_9bb94 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb98 : bv 32 := 0x01093503.
Lemma F_9bb98 : fetch_word Plain.M.loaded_segments (0x9bbe4 : word) = Some W_9bb98.
Proof. vm_refl. Qed.
Lemma D_9bb98 : decode_any W_9bb98 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb9c : bv 32 := 0xfa1ff06f.
Lemma F_9bb9c : fetch_word Plain.M.loaded_segments (0x9bbe8 : word) = Some W_9bb9c.
Proof. vm_refl. Qed.
Lemma D_9bb9c : decode_any W_9bb9c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bba0 : bv 32 := 0x00100513.
Lemma F_9bba0 : fetch_word Plain.M.loaded_segments (0x9bbec : word) = Some W_9bba0.
Proof. vm_refl. Qed.
Lemma D_9bba0 : decode_any W_9bba0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bba4 : bv 32 := 0x00a90023.
Lemma F_9bba4 : fetch_word Plain.M.loaded_segments (0x9bbf0 : word) = Some W_9bba4.
Proof. vm_refl. Qed.
Lemma D_9bba4 : decode_any W_9bba4 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bba8 : bv 32 := 0x00040513.
Lemma F_9bba8 : fetch_word Plain.M.loaded_segments (0x9bbf4 : word) = Some W_9bba8.
Proof. vm_refl. Qed.
Lemma D_9bba8 : decode_any W_9bba8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbac : bv 32 := 0x02813083.
Lemma F_9bbac : fetch_word Plain.M.loaded_segments (0x9bbf8 : word) = Some W_9bbac.
Proof. vm_refl. Qed.
Lemma D_9bbac : decode_any W_9bbac = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbb0 : bv 32 := 0x02013403.
Lemma F_9bbb0 : fetch_word Plain.M.loaded_segments (0x9bbfc : word) = Some W_9bbb0.
Proof. vm_refl. Qed.
Lemma D_9bbb0 : decode_any W_9bbb0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbb4 : bv 32 := 0x01813483.
Lemma F_9bbb4 : fetch_word Plain.M.loaded_segments (0x9bc00 : word) = Some W_9bbb4.
Proof. vm_refl. Qed.
Lemma D_9bbb4 : decode_any W_9bbb4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbb8 : bv 32 := 0x01013903.
Lemma F_9bbb8 : fetch_word Plain.M.loaded_segments (0x9bc04 : word) = Some W_9bbb8.
Proof. vm_refl. Qed.
Lemma D_9bbb8 : decode_any W_9bbb8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbbc : bv 32 := 0x00813983.
Lemma F_9bbbc : fetch_word Plain.M.loaded_segments (0x9bc08 : word) = Some W_9bbbc.
Proof. vm_refl. Qed.
Lemma D_9bbbc : decode_any W_9bbbc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbc0 : bv 32 := 0x03010113.
Lemma F_9bbc0 : fetch_word Plain.M.loaded_segments (0x9bc0c : word) = Some W_9bbc0.
Proof. vm_refl. Qed.
Lemma D_9bbc0 : decode_any W_9bbc0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbc4 : bv 32 := 0x7941106f.
Lemma F_9bbc4 : fetch_word Plain.M.loaded_segments (0x9bc10 : word) = Some W_9bbc4.
Proof. vm_refl. Qed.
Lemma D_9bbc4 : decode_any W_9bbc4 = Some (Jal 0 71572, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbc8 : bv 32 := 0x00008067.
Lemma F_9bbc8 : fetch_word Plain.M.loaded_segments (0x9bc14 : word) = Some W_9bbc8.
Proof. vm_refl. Qed.
Lemma D_9bbc8 : decode_any W_9bbc8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
