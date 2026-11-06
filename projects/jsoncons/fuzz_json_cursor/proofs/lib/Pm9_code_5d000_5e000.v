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

Definition W_5da20 : bv 32 := 0xfd010113.
Lemma F_5da20 : fetch_word AsanUbsan.M.loaded_segments (0x5da68 : word) = Some W_5da20.
Proof. vm_refl. Qed.
Lemma D_5da20 : decode_any W_5da20 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da24 : bv 32 := 0x02113423.
Lemma F_5da24 : fetch_word AsanUbsan.M.loaded_segments (0x5da6c : word) = Some W_5da24.
Proof. vm_refl. Qed.
Lemma D_5da24 : decode_any W_5da24 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da28 : bv 32 := 0x02813023.
Lemma F_5da28 : fetch_word AsanUbsan.M.loaded_segments (0x5da70 : word) = Some W_5da28.
Proof. vm_refl. Qed.
Lemma D_5da28 : decode_any W_5da28 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da2c : bv 32 := 0x00913c23.
Lemma F_5da2c : fetch_word AsanUbsan.M.loaded_segments (0x5da74 : word) = Some W_5da2c.
Proof. vm_refl. Qed.
Lemma D_5da2c : decode_any W_5da2c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da30 : bv 32 := 0x01213823.
Lemma F_5da30 : fetch_word AsanUbsan.M.loaded_segments (0x5da78 : word) = Some W_5da30.
Proof. vm_refl. Qed.
Lemma D_5da30 : decode_any W_5da30 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da34 : bv 32 := 0x01313423.
Lemma F_5da34 : fetch_word AsanUbsan.M.loaded_segments (0x5da7c : word) = Some W_5da34.
Proof. vm_refl. Qed.
Lemma D_5da34 : decode_any W_5da34 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da38 : bv 32 := 0x01413023.
Lemma F_5da38 : fetch_word AsanUbsan.M.loaded_segments (0x5da80 : word) = Some W_5da38.
Proof. vm_refl. Qed.
Lemma D_5da38 : decode_any W_5da38 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da3c : bv 32 := 0x00058413.
Lemma F_5da3c : fetch_word AsanUbsan.M.loaded_segments (0x5da84 : word) = Some W_5da3c.
Proof. vm_refl. Qed.
Lemma D_5da3c : decode_any W_5da3c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da40 : bv 32 := 0x00058583.
Lemma F_5da40 : fetch_word AsanUbsan.M.loaded_segments (0x5da88 : word) = Some W_5da40.
Proof. vm_refl. Qed.
Lemma D_5da40 : decode_any W_5da40 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da44 : bv 32 := 0x00300613.
Lemma F_5da44 : fetch_word AsanUbsan.M.loaded_segments (0x5da8c : word) = Some W_5da44.
Proof. vm_refl. Qed.
Lemma D_5da44 : decode_any W_5da44 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da48 : bv 32 := 0x12c59463.
Lemma F_5da48 : fetch_word AsanUbsan.M.loaded_segments (0x5da90 : word) = Some W_5da48.
Proof. vm_refl. Qed.
Lemma D_5da48 : decode_any W_5da48 = Some (Branch BC_NE 11 12 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da4c : bv 32 := 0x00068493.
Lemma F_5da4c : fetch_word AsanUbsan.M.loaded_segments (0x5da94 : word) = Some W_5da4c.
Proof. vm_refl. Qed.
Lemma D_5da4c : decode_any W_5da4c = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da50 : bv 32 := 0x00050913.
Lemma F_5da50 : fetch_word AsanUbsan.M.loaded_segments (0x5da98 : word) = Some W_5da50.
Proof. vm_refl. Qed.
Lemma D_5da50 : decode_any W_5da50 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da54 : bv 32 := 0x3e82d0ef.
Lemma F_5da54 : fetch_word AsanUbsan.M.loaded_segments (0x5da9c : word) = Some W_5da54.
Proof. vm_refl. Qed.
Lemma D_5da54 : decode_any W_5da54 = Some (Jal 1 185320, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da58 : bv 32 := 0x06050c63.
Lemma F_5da58 : fetch_word AsanUbsan.M.loaded_segments (0x5daa0 : word) = Some W_5da58.
Proof. vm_refl. Qed.
Lemma D_5da58 : decode_any W_5da58 = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da5c : bv 32 := 0x00053683.
Lemma F_5da5c : fetch_word AsanUbsan.M.loaded_segments (0x5daa4 : word) = Some W_5da5c.
Proof. vm_refl. Qed.
Lemma D_5da5c : decode_any W_5da5c = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da60 : bv 32 := 0x0004b603.
Lemma F_5da60 : fetch_word AsanUbsan.M.loaded_segments (0x5daa8 : word) = Some W_5da60.
Proof. vm_refl. Qed.
Lemma D_5da60 : decode_any W_5da60 = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da64 : bv 32 := 0x0084b583.
Lemma F_5da64 : fetch_word AsanUbsan.M.loaded_segments (0x5daac : word) = Some W_5da64.
Proof. vm_refl. Qed.
Lemma D_5da64 : decode_any W_5da64 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da68 : bv 32 := 0x0086a983.
Lemma F_5da68 : fetch_word AsanUbsan.M.loaded_segments (0x5dab0 : word) = Some W_5da68.
Proof. vm_refl. Qed.
Lemma D_5da68 : decode_any W_5da68 = Some (Load SZ4 true 19 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da6c : bv 32 := 0x00050a13.
Lemma F_5da6c : fetch_word AsanUbsan.M.loaded_segments (0x5dab4 : word) = Some W_5da6c.
Proof. vm_refl. Qed.
Lemma D_5da6c : decode_any W_5da6c = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da70 : bv 32 := 0x00060513.
Lemma F_5da70 : fetch_word AsanUbsan.M.loaded_segments (0x5dab8 : word) = Some W_5da70.
Proof. vm_refl. Qed.
Lemma D_5da70 : decode_any W_5da70 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da74 : bv 32 := 0x2a9430ef.
Lemma F_5da74 : fetch_word AsanUbsan.M.loaded_segments (0x5dabc : word) = Some W_5da74.
Proof. vm_refl. Qed.
Lemma D_5da74 : decode_any W_5da74 = Some (Jal 1 277160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da78 : bv 32 := 0x02099993.
Lemma F_5da78 : fetch_word AsanUbsan.M.loaded_segments (0x5dac0 : word) = Some W_5da78.
Proof. vm_refl. Qed.
Lemma D_5da78 : decode_any W_5da78 = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da7c : bv 32 := 0x02051513.
Lemma F_5da7c : fetch_word AsanUbsan.M.loaded_segments (0x5dac4 : word) = Some W_5da7c.
Proof. vm_refl. Qed.
Lemma D_5da7c : decode_any W_5da7c = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da80 : bv 32 := 0x02055513.
Lemma F_5da80 : fetch_word AsanUbsan.M.loaded_segments (0x5dac8 : word) = Some W_5da80.
Proof. vm_refl. Qed.
Lemma D_5da80 : decode_any W_5da80 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da84 : bv 32 := 0x00a9e533.
Lemma F_5da84 : fetch_word AsanUbsan.M.loaded_segments (0x5dacc : word) = Some W_5da84.
Proof. vm_refl. Qed.
Lemma D_5da84 : decode_any W_5da84 = Some (Op ALU_OR 10 19 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da88 : bv 32 := 0x00a43823.
Lemma F_5da88 : fetch_word AsanUbsan.M.loaded_segments (0x5dad0 : word) = Some W_5da88.
Proof. vm_refl. Qed.
Lemma D_5da88 : decode_any W_5da88 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da8c : bv 32 := 0x050a0593.
Lemma F_5da8c : fetch_word AsanUbsan.M.loaded_segments (0x5dad4 : word) = Some W_5da8c.
Proof. vm_refl. Qed.
Lemma D_5da8c : decode_any W_5da8c = Some (OpImm ALU_ADD 11 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da90 : bv 32 := 0x00245683.
Lemma F_5da90 : fetch_word AsanUbsan.M.loaded_segments (0x5dad8 : word) = Some W_5da90.
Proof. vm_refl. Qed.
Lemma D_5da90 : decode_any W_5da90 = Some (Load SZ2 false 13 8 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da94 : bv 32 := 0x00446703.
Lemma F_5da94 : fetch_word AsanUbsan.M.loaded_segments (0x5dadc : word) = Some W_5da94.
Proof. vm_refl. Qed.
Lemma D_5da94 : decode_any W_5da94 = Some (Load SZ4 false 14 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da98 : bv 32 := 0x0d0a0613.
Lemma F_5da98 : fetch_word AsanUbsan.M.loaded_segments (0x5dae0 : word) = Some W_5da98.
Proof. vm_refl. Qed.
Lemma D_5da98 : decode_any W_5da98 = Some (OpImm ALU_ADD 12 20 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da9c : bv 32 := 0x2d890513.
Lemma F_5da9c : fetch_word AsanUbsan.M.loaded_segments (0x5dae4 : word) = Some W_5da9c.
Proof. vm_refl. Qed.
Lemma D_5da9c : decode_any W_5da9c = Some (OpImm ALU_ADD 10 18 728, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daa0 : bv 32 := 0x02069693.
Lemma F_5daa0 : fetch_word AsanUbsan.M.loaded_segments (0x5dae8 : word) = Some W_5daa0.
Proof. vm_refl. Qed.
Lemma D_5daa0 : decode_any W_5daa0 = Some (ShiftImm ALU_SLL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daa4 : bv 32 := 0x00e6e7b3.
Lemma F_5daa4 : fetch_word AsanUbsan.M.loaded_segments (0x5daec : word) = Some W_5daa4.
Proof. vm_refl. Qed.
Lemma D_5daa4 : decode_any W_5daa4 = Some (Op ALU_OR 15 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daa8 : bv 32 := 0x00048693.
Lemma F_5daa8 : fetch_word AsanUbsan.M.loaded_segments (0x5daf0 : word) = Some W_5daa8.
Proof. vm_refl. Qed.
Lemma D_5daa8 : decode_any W_5daa8 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daac : bv 32 := 0x00040713.
Lemma F_5daac : fetch_word AsanUbsan.M.loaded_segments (0x5daf4 : word) = Some W_5daac.
Proof. vm_refl. Qed.
Lemma D_5daac : decode_any W_5daac = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dab0 : bv 32 := 0x02813083.
Lemma F_5dab0 : fetch_word AsanUbsan.M.loaded_segments (0x5daf8 : word) = Some W_5dab0.
Proof. vm_refl. Qed.
Lemma D_5dab0 : decode_any W_5dab0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dab4 : bv 32 := 0x02013403.
Lemma F_5dab4 : fetch_word AsanUbsan.M.loaded_segments (0x5dafc : word) = Some W_5dab4.
Proof. vm_refl. Qed.
Lemma D_5dab4 : decode_any W_5dab4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dab8 : bv 32 := 0x01813483.
Lemma F_5dab8 : fetch_word AsanUbsan.M.loaded_segments (0x5db00 : word) = Some W_5dab8.
Proof. vm_refl. Qed.
Lemma D_5dab8 : decode_any W_5dab8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dabc : bv 32 := 0x01013903.
Lemma F_5dabc : fetch_word AsanUbsan.M.loaded_segments (0x5db04 : word) = Some W_5dabc.
Proof. vm_refl. Qed.
Lemma D_5dabc : decode_any W_5dabc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dac0 : bv 32 := 0x00813983.
Lemma F_5dac0 : fetch_word AsanUbsan.M.loaded_segments (0x5db08 : word) = Some W_5dac0.
Proof. vm_refl. Qed.
Lemma D_5dac0 : decode_any W_5dac0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dac4 : bv 32 := 0x00013a03.
Lemma F_5dac4 : fetch_word AsanUbsan.M.loaded_segments (0x5db0c : word) = Some W_5dac4.
Proof. vm_refl. Qed.
Lemma D_5dac4 : decode_any W_5dac4 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dac8 : bv 32 := 0x03010113.
Lemma F_5dac8 : fetch_word AsanUbsan.M.loaded_segments (0x5db10 : word) = Some W_5dac8.
Proof. vm_refl. Qed.
Lemma D_5dac8 : decode_any W_5dac8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dacc : bv 32 := 0x0cc0006f.
Lemma F_5dacc : fetch_word AsanUbsan.M.loaded_segments (0x5db14 : word) = Some W_5dacc.
Proof. vm_refl. Qed.
Lemma D_5dacc : decode_any W_5dacc = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db98 : bv 32 := 0xfb010113.
Lemma F_5db98 : fetch_word AsanUbsan.M.loaded_segments (0x5dbe0 : word) = Some W_5db98.
Proof. vm_refl. Qed.
Lemma D_5db98 : decode_any W_5db98 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db9c : bv 32 := 0x04113423.
Lemma F_5db9c : fetch_word AsanUbsan.M.loaded_segments (0x5dbe4 : word) = Some W_5db9c.
Proof. vm_refl. Qed.
Lemma D_5db9c : decode_any W_5db9c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dba0 : bv 32 := 0x04813023.
Lemma F_5dba0 : fetch_word AsanUbsan.M.loaded_segments (0x5dbe8 : word) = Some W_5dba0.
Proof. vm_refl. Qed.
Lemma D_5dba0 : decode_any W_5dba0 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dba4 : bv 32 := 0x02913c23.
Lemma F_5dba4 : fetch_word AsanUbsan.M.loaded_segments (0x5dbec : word) = Some W_5dba4.
Proof. vm_refl. Qed.
Lemma D_5dba4 : decode_any W_5dba4 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dba8 : bv 32 := 0x03213823.
Lemma F_5dba8 : fetch_word AsanUbsan.M.loaded_segments (0x5dbf0 : word) = Some W_5dba8.
Proof. vm_refl. Qed.
Lemma D_5dba8 : decode_any W_5dba8 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbac : bv 32 := 0x03313423.
Lemma F_5dbac : fetch_word AsanUbsan.M.loaded_segments (0x5dbf4 : word) = Some W_5dbac.
Proof. vm_refl. Qed.
Lemma D_5dbac : decode_any W_5dbac = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbb0 : bv 32 := 0x03413023.
Lemma F_5dbb0 : fetch_word AsanUbsan.M.loaded_segments (0x5dbf8 : word) = Some W_5dbb0.
Proof. vm_refl. Qed.
Lemma D_5dbb0 : decode_any W_5dbb0 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbb4 : bv 32 := 0x01513c23.
Lemma F_5dbb4 : fetch_word AsanUbsan.M.loaded_segments (0x5dbfc : word) = Some W_5dbb4.
Proof. vm_refl. Qed.
Lemma D_5dbb4 : decode_any W_5dbb4 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbb8 : bv 32 := 0x01613823.
Lemma F_5dbb8 : fetch_word AsanUbsan.M.loaded_segments (0x5dc00 : word) = Some W_5dbb8.
Proof. vm_refl. Qed.
Lemma D_5dbb8 : decode_any W_5dbb8 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbbc : bv 32 := 0x00050413.
Lemma F_5dbbc : fetch_word AsanUbsan.M.loaded_segments (0x5dc04 : word) = Some W_5dbbc.
Proof. vm_refl. Qed.
Lemma D_5dbbc : decode_any W_5dbbc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbc0 : bv 32 := 0x00c13023.
Lemma F_5dbc0 : fetch_word AsanUbsan.M.loaded_segments (0x5dc08 : word) = Some W_5dbc0.
Proof. vm_refl. Qed.
Lemma D_5dbc0 : decode_any W_5dbc0 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbc4 : bv 32 := 0x00d13423.
Lemma F_5dbc4 : fetch_word AsanUbsan.M.loaded_segments (0x5dc0c : word) = Some W_5dbc4.
Proof. vm_refl. Qed.
Lemma D_5dbc4 : decode_any W_5dbc4 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbc8 : bv 32 := 0x05053b03.
Lemma F_5dbc8 : fetch_word AsanUbsan.M.loaded_segments (0x5dc10 : word) = Some W_5dbc8.
Proof. vm_refl. Qed.
Lemma D_5dbc8 : decode_any W_5dbc8 = Some (Load SZ8 true 22 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbcc : bv 32 := 0x00058493.
Lemma F_5dbcc : fetch_word AsanUbsan.M.loaded_segments (0x5dc14 : word) = Some W_5dbcc.
Proof. vm_refl. Qed.
Lemma D_5dbcc : decode_any W_5dbcc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbd0 : bv 32 := 0x000b0663.
Lemma F_5dbd0 : fetch_word AsanUbsan.M.loaded_segments (0x5dc18 : word) = Some W_5dbd0.
Proof. vm_refl. Qed.
Lemma D_5dbd0 : decode_any W_5dbd0 = Some (Branch BC_EQ 22 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbd4 : bv 32 := 0x04043503.
Lemma F_5dbd4 : fetch_word AsanUbsan.M.loaded_segments (0x5dc1c : word) = Some W_5dbd4.
Proof. vm_refl. Qed.
Lemma D_5dbd4 : decode_any W_5dbd4 = Some (Load SZ8 true 10 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbd8 : bv 32 := 0x0cf57263.
Lemma F_5dbd8 : fetch_word AsanUbsan.M.loaded_segments (0x5dc20 : word) = Some W_5dbd8.
Proof. vm_refl. Qed.
Lemma D_5dbd8 : decode_any W_5dbd8 = Some (Branch BC_GEU 10 15 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc60 : bv 32 := 0x00013603.
Lemma F_5dc60 : fetch_word AsanUbsan.M.loaded_segments (0x5dca8 : word) = Some W_5dc60.
Proof. vm_refl. Qed.
Lemma D_5dc60 : decode_any W_5dc60 = Some (Load SZ8 true 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc64 : bv 32 := 0x00813683.
Lemma F_5dc64 : fetch_word AsanUbsan.M.loaded_segments (0x5dcac : word) = Some W_5dc64.
Proof. vm_refl. Qed.
Lemma D_5dc64 : decode_any W_5dc64 = Some (Load SZ8 true 13 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc68 : bv 32 := 0x00040513.
Lemma F_5dc68 : fetch_word AsanUbsan.M.loaded_segments (0x5dcb0 : word) = Some W_5dc68.
Proof. vm_refl. Qed.
Lemma D_5dc68 : decode_any W_5dc68 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc6c : bv 32 := 0x00048593.
Lemma F_5dc6c : fetch_word AsanUbsan.M.loaded_segments (0x5dcb4 : word) = Some W_5dc6c.
Proof. vm_refl. Qed.
Lemma D_5dc6c : decode_any W_5dc6c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc70 : bv 32 := 0x831fd0ef.
Lemma F_5dc70 : fetch_word AsanUbsan.M.loaded_segments (0x5dcb8 : word) = Some W_5dc70.
Proof. vm_refl. Qed.
Lemma D_5dc70 : decode_any W_5dc70 = Some (Jal 1 2086960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc74 : bv 32 := 0x04813083.
Lemma F_5dc74 : fetch_word AsanUbsan.M.loaded_segments (0x5dcbc : word) = Some W_5dc74.
Proof. vm_refl. Qed.
Lemma D_5dc74 : decode_any W_5dc74 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc78 : bv 32 := 0x04013403.
Lemma F_5dc78 : fetch_word AsanUbsan.M.loaded_segments (0x5dcc0 : word) = Some W_5dc78.
Proof. vm_refl. Qed.
Lemma D_5dc78 : decode_any W_5dc78 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc7c : bv 32 := 0x03813483.
Lemma F_5dc7c : fetch_word AsanUbsan.M.loaded_segments (0x5dcc4 : word) = Some W_5dc7c.
Proof. vm_refl. Qed.
Lemma D_5dc7c : decode_any W_5dc7c = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc80 : bv 32 := 0x03013903.
Lemma F_5dc80 : fetch_word AsanUbsan.M.loaded_segments (0x5dcc8 : word) = Some W_5dc80.
Proof. vm_refl. Qed.
Lemma D_5dc80 : decode_any W_5dc80 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc84 : bv 32 := 0x02813983.
Lemma F_5dc84 : fetch_word AsanUbsan.M.loaded_segments (0x5dccc : word) = Some W_5dc84.
Proof. vm_refl. Qed.
Lemma D_5dc84 : decode_any W_5dc84 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc88 : bv 32 := 0x02013a03.
Lemma F_5dc88 : fetch_word AsanUbsan.M.loaded_segments (0x5dcd0 : word) = Some W_5dc88.
Proof. vm_refl. Qed.
Lemma D_5dc88 : decode_any W_5dc88 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc8c : bv 32 := 0x01813a83.
Lemma F_5dc8c : fetch_word AsanUbsan.M.loaded_segments (0x5dcd4 : word) = Some W_5dc8c.
Proof. vm_refl. Qed.
Lemma D_5dc8c : decode_any W_5dc8c = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc90 : bv 32 := 0x01013b03.
Lemma F_5dc90 : fetch_word AsanUbsan.M.loaded_segments (0x5dcd8 : word) = Some W_5dc90.
Proof. vm_refl. Qed.
Lemma D_5dc90 : decode_any W_5dc90 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc94 : bv 32 := 0x05010113.
Lemma F_5dc94 : fetch_word AsanUbsan.M.loaded_segments (0x5dcdc : word) = Some W_5dc94.
Proof. vm_refl. Qed.
Lemma D_5dc94 : decode_any W_5dc94 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc98 : bv 32 := 0x00008067.
Lemma F_5dc98 : fetch_word AsanUbsan.M.loaded_segments (0x5dce0 : word) = Some W_5dc98.
Proof. vm_refl. Qed.
Lemma D_5dc98 : decode_any W_5dc98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc9c : bv 32 := 0x00060a13.
Lemma F_5dc9c : fetch_word AsanUbsan.M.loaded_segments (0x5dce4 : word) = Some W_5dc9c.
Proof. vm_refl. Qed.
Lemma D_5dc9c : decode_any W_5dc9c = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca0 : bv 32 := 0x00068993.
Lemma F_5dca0 : fetch_word AsanUbsan.M.loaded_segments (0x5dce8 : word) = Some W_5dca0.
Proof. vm_refl. Qed.
Lemma D_5dca0 : decode_any W_5dca0 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca4 : bv 32 := 0x00078913.
Lemma F_5dca4 : fetch_word AsanUbsan.M.loaded_segments (0x5dcec : word) = Some W_5dca4.
Proof. vm_refl. Qed.
Lemma D_5dca4 : decode_any W_5dca4 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca8 : bv 32 := 0x000f7517.
Lemma F_5dca8 : fetch_word AsanUbsan.M.loaded_segments (0x5dcf0 : word) = Some W_5dca8.
Proof. vm_refl. Qed.
Lemma D_5dca8 : decode_any W_5dca8 = Some (Auipc 10 247, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcac : bv 32 := 0x80853583.
Lemma F_5dcac : fetch_word AsanUbsan.M.loaded_segments (0x5dcf4 : word) = Some W_5dcac.
Proof. vm_refl. Qed.
Lemma D_5dcac : decode_any W_5dcac = Some (Load SZ8 true 11 10 2056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb0 : bv 32 := 0x0305a683.
Lemma F_5dcb0 : fetch_word AsanUbsan.M.loaded_segments (0x5dcf8 : word) = Some W_5dcb0.
Proof. vm_refl. Qed.
Lemma D_5dcb0 : decode_any W_5dcb0 = Some (Load SZ4 true 13 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb4 : bv 32 := 0x04d05463.
Lemma F_5dcb4 : fetch_word AsanUbsan.M.loaded_segments (0x5dcfc : word) = Some W_5dcb4.
Proof. vm_refl. Qed.
Lemma D_5dcb4 : decode_any W_5dcb4 = Some (Branch BC_GE 0 13 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcfc : bv 32 := 0x00275583.
Lemma F_5dcfc : fetch_word AsanUbsan.M.loaded_segments (0x5dd44 : word) = Some W_5dcfc.
Proof. vm_refl. Qed.
Lemma D_5dcfc : decode_any W_5dcfc = Some (Load SZ2 false 11 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd00 : bv 32 := 0x00476603.
Lemma F_5dd00 : fetch_word AsanUbsan.M.loaded_segments (0x5dd48 : word) = Some W_5dd00.
Proof. vm_refl. Qed.
Lemma D_5dd00 : decode_any W_5dd00 = Some (Load SZ4 false 12 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd04 : bv 32 := 0x01070513.
Lemma F_5dd04 : fetch_word AsanUbsan.M.loaded_segments (0x5dd4c : word) = Some W_5dd04.
Proof. vm_refl. Qed.
Lemma D_5dd04 : decode_any W_5dd04 = Some (OpImm ALU_ADD 10 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd08 : bv 32 := 0x02059593.
Lemma F_5dd08 : fetch_word AsanUbsan.M.loaded_segments (0x5dd50 : word) = Some W_5dd08.
Proof. vm_refl. Qed.
Lemma D_5dd08 : decode_any W_5dd08 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd0c : bv 32 := 0x00c5e5b3.
Lemma F_5dd0c : fetch_word AsanUbsan.M.loaded_segments (0x5dd54 : word) = Some W_5dd0c.
Proof. vm_refl. Qed.
Lemma D_5dd0c : decode_any W_5dd0c = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd10 : bv 32 := 0x00758593.
Lemma F_5dd10 : fetch_word AsanUbsan.M.loaded_segments (0x5dd58 : word) = Some W_5dd10.
Proof. vm_refl. Qed.
Lemma D_5dd10 : decode_any W_5dd10 = Some (OpImm ALU_ADD 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd14 : bv 32 := 0xff85f593.
Lemma F_5dd14 : fetch_word AsanUbsan.M.loaded_segments (0x5dd5c : word) = Some W_5dd14.
Proof. vm_refl. Qed.
Lemma D_5dd14 : decode_any W_5dd14 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd18 : bv 32 := 0x0fd00613.
Lemma F_5dd18 : fetch_word AsanUbsan.M.loaded_segments (0x5dd60 : word) = Some W_5dd18.
Proof. vm_refl. Qed.
Lemma D_5dd18 : decode_any W_5dd18 = Some (OpImm ALU_ADD 12 0 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd1c : bv 32 := 0x00070a93.
Lemma F_5dd1c : fetch_word AsanUbsan.M.loaded_segments (0x5dd64 : word) = Some W_5dd1c.
Proof. vm_refl. Qed.
Lemma D_5dd1c : decode_any W_5dd1c = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd20 : bv 32 := 0x370240ef.
Lemma F_5dd20 : fetch_word AsanUbsan.M.loaded_segments (0x5dd68 : word) = Some W_5dd20.
Proof. vm_refl. Qed.
Lemma D_5dd20 : decode_any W_5dd20 = Some (Jal 1 148336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd24 : bv 32 := 0x00048513.
Lemma F_5dd24 : fetch_word AsanUbsan.M.loaded_segments (0x5dd6c : word) = Some W_5dd24.
Proof. vm_refl. Qed.
Lemma D_5dd24 : decode_any W_5dd24 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd28 : bv 32 := 0x000a0593.
Lemma F_5dd28 : fetch_word AsanUbsan.M.loaded_segments (0x5dd70 : word) = Some W_5dd28.
Proof. vm_refl. Qed.
Lemma D_5dd28 : decode_any W_5dd28 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd2c : bv 32 := 0x00098613.
Lemma F_5dd2c : fetch_word AsanUbsan.M.loaded_segments (0x5dd74 : word) = Some W_5dd2c.
Proof. vm_refl. Qed.
Lemma D_5dd2c : decode_any W_5dd2c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd30 : bv 32 := 0x000a8693.
Lemma F_5dd30 : fetch_word AsanUbsan.M.loaded_segments (0x5dd78 : word) = Some W_5dd30.
Proof. vm_refl. Qed.
Lemma D_5dd30 : decode_any W_5dd30 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd34 : bv 32 := 0x00090713.
Lemma F_5dd34 : fetch_word AsanUbsan.M.loaded_segments (0x5dd7c : word) = Some W_5dd34.
Proof. vm_refl. Qed.
Lemma D_5dd34 : decode_any W_5dd34 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd38 : bv 32 := 0x010000ef.
Lemma F_5dd38 : fetch_word AsanUbsan.M.loaded_segments (0x5dd80 : word) = Some W_5dd38.
Proof. vm_refl. Qed.
Lemma D_5dd38 : decode_any W_5dd38 = Some (Jal 1 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd3c : bv 32 := 0x0184b503.
Lemma F_5dd3c : fetch_word AsanUbsan.M.loaded_segments (0x5dd84 : word) = Some W_5dd3c.
Proof. vm_refl. Qed.
Lemma D_5dd3c : decode_any W_5dd3c = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd40 : bv 32 := 0xf2ab60e3.
Lemma F_5dd40 : fetch_word AsanUbsan.M.loaded_segments (0x5dd88 : word) = Some W_5dd40.
Proof. vm_refl. Qed.
Lemma D_5dd40 : decode_any W_5dd40 = Some (Branch BC_LTU 22 10 7968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd44 : bv 32 := 0xf31ff06f.
Lemma F_5dd44 : fetch_word AsanUbsan.M.loaded_segments (0x5dd8c : word) = Some W_5dd44.
Proof. vm_refl. Qed.
Lemma D_5dd44 : decode_any W_5dd44 = Some (Jal 0 2096944, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd48 : bv 32 := 0xfc010113.
Lemma F_5dd48 : fetch_word AsanUbsan.M.loaded_segments (0x5dd90 : word) = Some W_5dd48.
Proof. vm_refl. Qed.
Lemma D_5dd48 : decode_any W_5dd48 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd4c : bv 32 := 0x02113c23.
Lemma F_5dd4c : fetch_word AsanUbsan.M.loaded_segments (0x5dd94 : word) = Some W_5dd4c.
Proof. vm_refl. Qed.
Lemma D_5dd4c : decode_any W_5dd4c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd50 : bv 32 := 0x02813823.
Lemma F_5dd50 : fetch_word AsanUbsan.M.loaded_segments (0x5dd98 : word) = Some W_5dd50.
Proof. vm_refl. Qed.
Lemma D_5dd50 : decode_any W_5dd50 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd54 : bv 32 := 0x02913423.
Lemma F_5dd54 : fetch_word AsanUbsan.M.loaded_segments (0x5dd9c : word) = Some W_5dd54.
Proof. vm_refl. Qed.
Lemma D_5dd54 : decode_any W_5dd54 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd58 : bv 32 := 0x03213023.
Lemma F_5dd58 : fetch_word AsanUbsan.M.loaded_segments (0x5dda0 : word) = Some W_5dd58.
Proof. vm_refl. Qed.
Lemma D_5dd58 : decode_any W_5dd58 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd5c : bv 32 := 0x01313c23.
Lemma F_5dd5c : fetch_word AsanUbsan.M.loaded_segments (0x5dda4 : word) = Some W_5dd5c.
Proof. vm_refl. Qed.
Lemma D_5dd5c : decode_any W_5dd5c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd60 : bv 32 := 0x01413823.
Lemma F_5dd60 : fetch_word AsanUbsan.M.loaded_segments (0x5dda8 : word) = Some W_5dd60.
Proof. vm_refl. Qed.
Lemma D_5dd60 : decode_any W_5dd60 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd64 : bv 32 := 0x01513423.
Lemma F_5dd64 : fetch_word AsanUbsan.M.loaded_segments (0x5ddac : word) = Some W_5dd64.
Proof. vm_refl. Qed.
Lemma D_5dd64 : decode_any W_5dd64 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd68 : bv 32 := 0x00053783.
Lemma F_5dd68 : fetch_word AsanUbsan.M.loaded_segments (0x5ddb0 : word) = Some W_5dd68.
Proof. vm_refl. Qed.
Lemma D_5dd68 : decode_any W_5dd68 = Some (Load SZ8 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd6c : bv 32 := 0x00078a63.
Lemma F_5dd6c : fetch_word AsanUbsan.M.loaded_segments (0x5ddb4 : word) = Some W_5dd6c.
Proof. vm_refl. Qed.
Lemma D_5dd6c : decode_any W_5dd6c = Some (Branch BC_EQ 15 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd70 : bv 32 := 0x01053803.
Lemma F_5dd70 : fetch_word AsanUbsan.M.loaded_segments (0x5ddb8 : word) = Some W_5dd70.
Proof. vm_refl. Qed.
Lemma D_5dd70 : decode_any W_5dd70 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd74 : bv 32 := 0x01083783.
Lemma F_5dd74 : fetch_word AsanUbsan.M.loaded_segments (0x5ddbc : word) = Some W_5dd74.
Proof. vm_refl. Qed.
Lemma D_5dd74 : decode_any W_5dd74 = Some (Load SZ8 true 15 16 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd78 : bv 32 := 0x3fd00893.
Lemma F_5dd78 : fetch_word AsanUbsan.M.loaded_segments (0x5ddc0 : word) = Some W_5dd78.
Proof. vm_refl. Qed.
Lemma D_5dd78 : decode_any W_5dd78 = Some (OpImm ALU_ADD 17 0 1021, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd7c : bv 32 := 0x09179463.
Lemma F_5dd7c : fetch_word AsanUbsan.M.loaded_segments (0x5ddc4 : word) = Some W_5dd7c.
Proof. vm_refl. Qed.
Lemma D_5dd7c : decode_any W_5dd7c = Some (Branch BC_NE 15 17 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd80 : bv 32 := 0x7805a783.
Lemma F_5dd80 : fetch_word AsanUbsan.M.loaded_segments (0x5ddc8 : word) = Some W_5dd80.
Proof. vm_refl. Qed.
Lemma D_5dd80 : decode_any W_5dd80 = Some (Load SZ4 true 15 11 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd84 : bv 32 := 0x0e078263.
Lemma F_5dd84 : fetch_word AsanUbsan.M.loaded_segments (0x5ddcc : word) = Some W_5dd84.
Proof. vm_refl. Qed.
Lemma D_5dd84 : decode_any W_5dd84 = Some (Branch BC_EQ 15 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd88 : bv 32 := 0xfff78793.
Lemma F_5dd88 : fetch_word AsanUbsan.M.loaded_segments (0x5ddd0 : word) = Some W_5dd88.
Proof. vm_refl. Qed.
Lemma D_5dd88 : decode_any W_5dd88 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd8c : bv 32 := 0x02079813.
Lemma F_5dd8c : fetch_word AsanUbsan.M.loaded_segments (0x5ddd4 : word) = Some W_5dd8c.
Proof. vm_refl. Qed.
Lemma D_5dd8c : decode_any W_5dd8c = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd90 : bv 32 := 0x78f5a023.
Lemma F_5dd90 : fetch_word AsanUbsan.M.loaded_segments (0x5ddd8 : word) = Some W_5dd90.
Proof. vm_refl. Qed.
Lemma D_5dd90 : decode_any W_5dd90 = Some (Store SZ4 11 15 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd94 : bv 32 := 0x01e85793.
Lemma F_5dd94 : fetch_word AsanUbsan.M.loaded_segments (0x5dddc : word) = Some W_5dd94.
Proof. vm_refl. Qed.
Lemma D_5dd94 : decode_any W_5dd94 = Some (ShiftImm ALU_SRL 15 16 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd98 : bv 32 := 0x00f587b3.
Lemma F_5dd98 : fetch_word AsanUbsan.M.loaded_segments (0x5dde0 : word) = Some W_5dd98.
Proof. vm_refl. Qed.
Lemma D_5dd98 : decode_any W_5dd98 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd9c : bv 32 := 0x7885b803.
Lemma F_5dd9c : fetch_word AsanUbsan.M.loaded_segments (0x5dde4 : word) = Some W_5dd9c.
Proof. vm_refl. Qed.
Lemma D_5dd9c : decode_any W_5dd9c = Some (Load SZ8 true 16 11 1928, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dda0 : bv 32 := 0x7ff58593.
Lemma F_5dda0 : fetch_word AsanUbsan.M.loaded_segments (0x5dde8 : word) = Some W_5dda0.
Proof. vm_refl. Qed.
Lemma D_5dda0 : decode_any W_5dda0 = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dda4 : bv 32 := 0x21158593.
Lemma F_5dda4 : fetch_word AsanUbsan.M.loaded_segments (0x5ddec : word) = Some W_5dda4.
Proof. vm_refl. Qed.
Lemma D_5dda4 : decode_any W_5dda4 = Some (OpImm ALU_ADD 11 11 529, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dda8 : bv 32 := 0x7907e783.
Lemma F_5dda8 : fetch_word AsanUbsan.M.loaded_segments (0x5ddf0 : word) = Some W_5dda8.
Proof. vm_refl. Qed.
Lemma D_5dda8 : decode_any W_5dda8 = Some (Load SZ4 false 15 15 1936, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddac : bv 32 := 0x0105b02f.
Lemma F_5ddac : fetch_word AsanUbsan.M.loaded_segments (0x5ddf4 : word) = Some W_5ddac.
Proof. vm_refl. Qed.
Lemma D_5ddac : decode_any W_5ddac = Some (Amo AMO_ADD AD false false 0 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddb0 : bv 32 := 0x000fd597.
Lemma F_5ddb0 : fetch_word AsanUbsan.M.loaded_segments (0x5ddf8 : word) = Some W_5ddb0.
Proof. vm_refl. Qed.
Lemma D_5ddb0 : decode_any W_5ddb0 = Some (Auipc 11 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddb4 : bv 32 := 0x8c05b583.
Lemma F_5ddb4 : fetch_word AsanUbsan.M.loaded_segments (0x5ddfc : word) = Some W_5ddb4.
Proof. vm_refl. Qed.
Lemma D_5ddb4 : decode_any W_5ddb4 = Some (Load SZ8 true 11 11 2240, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddb8 : bv 32 := 0x00300813.
Lemma F_5ddb8 : fetch_word AsanUbsan.M.loaded_segments (0x5de00 : word) = Some W_5ddb8.
Proof. vm_refl. Qed.
Lemma D_5ddb8 : decode_any W_5ddb8 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddbc : bv 32 := 0x00479793.
Lemma F_5ddbc : fetch_word AsanUbsan.M.loaded_segments (0x5de04 : word) = Some W_5ddbc.
Proof. vm_refl. Qed.
Lemma D_5ddbc : decode_any W_5ddbc = Some (ShiftImm ALU_SLL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddc0 : bv 32 := 0x02381813.
Lemma F_5ddc0 : fetch_word AsanUbsan.M.loaded_segments (0x5de08 : word) = Some W_5ddc0.
Proof. vm_refl. Qed.
Lemma D_5ddc0 : decode_any W_5ddc0 = Some (ShiftImm ALU_SLL 16 16 35, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddc4 : bv 32 := 0x010585b3.
Lemma F_5ddc4 : fetch_word AsanUbsan.M.loaded_segments (0x5de0c : word) = Some W_5ddc4.
Proof. vm_refl. Qed.
Lemma D_5ddc4 : decode_any W_5ddc4 = Some (Op ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddc8 : bv 32 := 0x00b785b3.
Lemma F_5ddc8 : fetch_word AsanUbsan.M.loaded_segments (0x5de10 : word) = Some W_5ddc8.
Proof. vm_refl. Qed.
Lemma D_5ddc8 : decode_any W_5ddc8 = Some (Op ALU_ADD 11 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddcc : bv 32 := 0x0e058863.
Lemma F_5ddcc : fetch_word AsanUbsan.M.loaded_segments (0x5de14 : word) = Some W_5ddcc.
Proof. vm_refl. Qed.
Lemma D_5ddcc : decode_any W_5ddcc = Some (Branch BC_EQ 11 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddd0 : bv 32 := 0x00100613.
Lemma F_5ddd0 : fetch_word AsanUbsan.M.loaded_segments (0x5de18 : word) = Some W_5ddd0.
Proof. vm_refl. Qed.
Lemma D_5ddd0 : decode_any W_5ddd0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddd4 : bv 32 := 0x000027b7.
Lemma F_5ddd4 : fetch_word AsanUbsan.M.loaded_segments (0x5de1c : word) = Some W_5ddd4.
Proof. vm_refl. Qed.
Lemma D_5ddd4 : decode_any W_5ddd4 = Some (Lui 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddd8 : bv 32 := 0x00f70733.
Lemma F_5ddd8 : fetch_word AsanUbsan.M.loaded_segments (0x5de20 : word) = Some W_5ddd8.
Proof. vm_refl. Qed.
Lemma D_5ddd8 : decode_any W_5ddd8 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dddc : bv 32 := 0x00053783.
Lemma F_5dddc : fetch_word AsanUbsan.M.loaded_segments (0x5de24 : word) = Some W_5dddc.
Proof. vm_refl. Qed.
Lemma D_5dddc : decode_any W_5dddc = Some (Load SZ8 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dde0 : bv 32 := 0x0005b023.
Lemma F_5dde0 : fetch_word AsanUbsan.M.loaded_segments (0x5de28 : word) = Some W_5dde0.
Proof. vm_refl. Qed.
Lemma D_5dde0 : decode_any W_5dde0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dde4 : bv 32 := 0x00e5b423.
Lemma F_5dde4 : fetch_word AsanUbsan.M.loaded_segments (0x5de2c : word) = Some W_5dde4.
Proof. vm_refl. Qed.
Lemma D_5dde4 : decode_any W_5dde4 = Some (Store SZ8 11 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dde8 : bv 32 := 0x00c5b823.
Lemma F_5dde8 : fetch_word AsanUbsan.M.loaded_segments (0x5de30 : word) = Some W_5dde8.
Proof. vm_refl. Qed.
Lemma D_5dde8 : decode_any W_5dde8 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddec : bv 32 := 0x00d5bc23.
Lemma F_5ddec : fetch_word AsanUbsan.M.loaded_segments (0x5de34 : word) = Some W_5ddec.
Proof. vm_refl. Qed.
Lemma D_5ddec : decode_any W_5ddec = Some (Store SZ8 11 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddf0 : bv 32 := 0x02078e63.
Lemma F_5ddf0 : fetch_word AsanUbsan.M.loaded_segments (0x5de38 : word) = Some W_5ddf0.
Proof. vm_refl. Qed.
Lemma D_5ddf0 : decode_any W_5ddf0 = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddf4 : bv 32 := 0x01053603.
Lemma F_5ddf4 : fetch_word AsanUbsan.M.loaded_segments (0x5de3c : word) = Some W_5ddf4.
Proof. vm_refl. Qed.
Lemma D_5ddf4 : decode_any W_5ddf4 = Some (Load SZ8 true 12 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddf8 : bv 32 := 0x00b63023.
Lemma F_5ddf8 : fetch_word AsanUbsan.M.loaded_segments (0x5de40 : word) = Some W_5ddf8.
Proof. vm_refl. Qed.
Lemma D_5ddf8 : decode_any W_5ddf8 = Some (Store SZ8 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddfc : bv 32 := 0x00178613.
Lemma F_5ddfc : fetch_word AsanUbsan.M.loaded_segments (0x5de44 : word) = Some W_5ddfc.
Proof. vm_refl. Qed.
Lemma D_5ddfc : decode_any W_5ddfc = Some (OpImm ALU_ADD 12 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de00 : bv 32 := 0x0300006f.
Lemma F_5de00 : fetch_word AsanUbsan.M.loaded_segments (0x5de48 : word) = Some W_5de00.
Proof. vm_refl. Qed.
Lemma D_5de00 : decode_any W_5de00 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de04 : bv 32 := 0x0d17fc63.
Lemma F_5de04 : fetch_word AsanUbsan.M.loaded_segments (0x5de4c : word) = Some W_5de04.
Proof. vm_refl. Qed.
Lemma D_5de04 : decode_any W_5de04 = Some (Branch BC_GEU 15 17 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de08 : bv 32 := 0x00883583.
Lemma F_5de08 : fetch_word AsanUbsan.M.loaded_segments (0x5de50 : word) = Some W_5de08.
Proof. vm_refl. Qed.
Lemma D_5de08 : decode_any W_5de08 = Some (Load SZ8 true 11 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de0c : bv 32 := 0x00379613.
Lemma F_5de0c : fetch_word AsanUbsan.M.loaded_segments (0x5de54 : word) = Some W_5de0c.
Proof. vm_refl. Qed.
Lemma D_5de0c : decode_any W_5de0c = Some (ShiftImm ALU_SLL 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de10 : bv 32 := 0x00178793.
Lemma F_5de10 : fetch_word AsanUbsan.M.loaded_segments (0x5de58 : word) = Some W_5de10.
Proof. vm_refl. Qed.
Lemma D_5de10 : decode_any W_5de10 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de14 : bv 32 := 0x00c80633.
Lemma F_5de14 : fetch_word AsanUbsan.M.loaded_segments (0x5de5c : word) = Some W_5de14.
Proof. vm_refl. Qed.
Lemma D_5de14 : decode_any W_5de14 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de18 : bv 32 := 0x00e585b3.
Lemma F_5de18 : fetch_word AsanUbsan.M.loaded_segments (0x5de60 : word) = Some W_5de18.
Proof. vm_refl. Qed.
Lemma D_5de18 : decode_any W_5de18 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de1c : bv 32 := 0x00b83423.
Lemma F_5de1c : fetch_word AsanUbsan.M.loaded_segments (0x5de64 : word) = Some W_5de1c.
Proof. vm_refl. Qed.
Lemma D_5de1c : decode_any W_5de1c = Some (Store SZ8 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de20 : bv 32 := 0x00f83823.
Lemma F_5de20 : fetch_word AsanUbsan.M.loaded_segments (0x5de68 : word) = Some W_5de20.
Proof. vm_refl. Qed.
Lemma D_5de20 : decode_any W_5de20 = Some (Store SZ8 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de24 : bv 32 := 0x00d63c23.
Lemma F_5de24 : fetch_word AsanUbsan.M.loaded_segments (0x5de6c : word) = Some W_5de24.
Proof. vm_refl. Qed.
Lemma D_5de24 : decode_any W_5de24 = Some (Store SZ8 12 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de28 : bv 32 := 0x0100006f.
Lemma F_5de28 : fetch_word AsanUbsan.M.loaded_segments (0x5de70 : word) = Some W_5de28.
Proof. vm_refl. Qed.
Lemma D_5de28 : decode_any W_5de28 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de2c : bv 32 := 0x00b53423.
Lemma F_5de2c : fetch_word AsanUbsan.M.loaded_segments (0x5de74 : word) = Some W_5de2c.
Proof. vm_refl. Qed.
Lemma D_5de2c : decode_any W_5de2c = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de30 : bv 32 := 0x00c53023.
Lemma F_5de30 : fetch_word AsanUbsan.M.loaded_segments (0x5de78 : word) = Some W_5de30.
Proof. vm_refl. Qed.
Lemma D_5de30 : decode_any W_5de30 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de34 : bv 32 := 0x00b53823.
Lemma F_5de34 : fetch_word AsanUbsan.M.loaded_segments (0x5de7c : word) = Some W_5de34.
Proof. vm_refl. Qed.
Lemma D_5de34 : decode_any W_5de34 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de38 : bv 32 := 0x01853583.
Lemma F_5de38 : fetch_word AsanUbsan.M.loaded_segments (0x5de80 : word) = Some W_5de38.
Proof. vm_refl. Qed.
Lemma D_5de38 : decode_any W_5de38 = Some (Load SZ8 true 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de3c : bv 32 := 0x00e585b3.
Lemma F_5de3c : fetch_word AsanUbsan.M.loaded_segments (0x5de84 : word) = Some W_5de3c.
Proof. vm_refl. Qed.
Lemma D_5de3c : decode_any W_5de3c = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de40 : bv 32 := 0x00b53c23.
Lemma F_5de40 : fetch_word AsanUbsan.M.loaded_segments (0x5de88 : word) = Some W_5de40.
Proof. vm_refl. Qed.
Lemma D_5de40 : decode_any W_5de40 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de44 : bv 32 := 0x03813083.
Lemma F_5de44 : fetch_word AsanUbsan.M.loaded_segments (0x5de8c : word) = Some W_5de44.
Proof. vm_refl. Qed.
Lemma D_5de44 : decode_any W_5de44 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de48 : bv 32 := 0x03013403.
Lemma F_5de48 : fetch_word AsanUbsan.M.loaded_segments (0x5de90 : word) = Some W_5de48.
Proof. vm_refl. Qed.
Lemma D_5de48 : decode_any W_5de48 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de4c : bv 32 := 0x02813483.
Lemma F_5de4c : fetch_word AsanUbsan.M.loaded_segments (0x5de94 : word) = Some W_5de4c.
Proof. vm_refl. Qed.
Lemma D_5de4c : decode_any W_5de4c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de50 : bv 32 := 0x02013903.
Lemma F_5de50 : fetch_word AsanUbsan.M.loaded_segments (0x5de98 : word) = Some W_5de50.
Proof. vm_refl. Qed.
Lemma D_5de50 : decode_any W_5de50 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de54 : bv 32 := 0x01813983.
Lemma F_5de54 : fetch_word AsanUbsan.M.loaded_segments (0x5de9c : word) = Some W_5de54.
Proof. vm_refl. Qed.
Lemma D_5de54 : decode_any W_5de54 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de58 : bv 32 := 0x01013a03.
Lemma F_5de58 : fetch_word AsanUbsan.M.loaded_segments (0x5dea0 : word) = Some W_5de58.
Proof. vm_refl. Qed.
Lemma D_5de58 : decode_any W_5de58 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de5c : bv 32 := 0x00813a83.
Lemma F_5de5c : fetch_word AsanUbsan.M.loaded_segments (0x5dea4 : word) = Some W_5de5c.
Proof. vm_refl. Qed.
Lemma D_5de5c : decode_any W_5de5c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de60 : bv 32 := 0x04010113.
Lemma F_5de60 : fetch_word AsanUbsan.M.loaded_segments (0x5dea8 : word) = Some W_5de60.
Proof. vm_refl. Qed.
Lemma D_5de60 : decode_any W_5de60 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de64 : bv 32 := 0x00008067.
Lemma F_5de64 : fetch_word AsanUbsan.M.loaded_segments (0x5deac : word) = Some W_5de64.
Proof. vm_refl. Qed.
Lemma D_5de64 : decode_any W_5de64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de68 : bv 32 := 0x78058413.
Lemma F_5de68 : fetch_word AsanUbsan.M.loaded_segments (0x5deb0 : word) = Some W_5de68.
Proof. vm_refl. Qed.
Lemma D_5de68 : decode_any W_5de68 = Some (OpImm ALU_ADD 8 11 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de6c : bv 32 := 0x000fc797.
Lemma F_5de6c : fetch_word AsanUbsan.M.loaded_segments (0x5deb4 : word) = Some W_5de6c.
Proof. vm_refl. Qed.
Lemma D_5de6c : decode_any W_5de6c = Some (Auipc 15 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de70 : bv 32 := 0x7e478793.
Lemma F_5de70 : fetch_word AsanUbsan.M.loaded_segments (0x5deb8 : word) = Some W_5de70.
Proof. vm_refl. Qed.
Lemma D_5de70 : decode_any W_5de70 = Some (OpImm ALU_ADD 15 15 2020, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de74 : bv 32 := 0x00068913.
Lemma F_5de74 : fetch_word AsanUbsan.M.loaded_segments (0x5debc : word) = Some W_5de74.
Proof. vm_refl. Qed.
Lemma D_5de74 : decode_any W_5de74 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de78 : bv 32 := 0x01800693.
Lemma F_5de78 : fetch_word AsanUbsan.M.loaded_segments (0x5dec0 : word) = Some W_5de78.
Proof. vm_refl. Qed.
Lemma D_5de78 : decode_any W_5de78 = Some (OpImm ALU_ADD 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de7c : bv 32 := 0x00050993.
Lemma F_5de7c : fetch_word AsanUbsan.M.loaded_segments (0x5dec4 : word) = Some W_5de7c.
Proof. vm_refl. Qed.
Lemma D_5de7c : decode_any W_5de7c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de80 : bv 32 := 0x00058493.
Lemma F_5de80 : fetch_word AsanUbsan.M.loaded_segments (0x5dec8 : word) = Some W_5de80.
Proof. vm_refl. Qed.
Lemma D_5de80 : decode_any W_5de80 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de84 : bv 32 := 0x00058513.
Lemma F_5de84 : fetch_word AsanUbsan.M.loaded_segments (0x5decc : word) = Some W_5de84.
Proof. vm_refl. Qed.
Lemma D_5de84 : decode_any W_5de84 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de88 : bv 32 := 0x00040593.
Lemma F_5de88 : fetch_word AsanUbsan.M.loaded_segments (0x5ded0 : word) = Some W_5de88.
Proof. vm_refl. Qed.
Lemma D_5de88 : decode_any W_5de88 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de8c : bv 32 := 0x00060a13.
Lemma F_5de8c : fetch_word AsanUbsan.M.loaded_segments (0x5ded4 : word) = Some W_5de8c.
Proof. vm_refl. Qed.
Lemma D_5de8c : decode_any W_5de8c = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de90 : bv 32 := 0x00078613.
Lemma F_5de90 : fetch_word AsanUbsan.M.loaded_segments (0x5ded8 : word) = Some W_5de90.
Proof. vm_refl. Qed.
Lemma D_5de90 : decode_any W_5de90 = Some (OpImm ALU_ADD 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de94 : bv 32 := 0x00070a93.
Lemma F_5de94 : fetch_word AsanUbsan.M.loaded_segments (0x5dedc : word) = Some W_5de94.
Proof. vm_refl. Qed.
Lemma D_5de94 : decode_any W_5de94 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de98 : bv 32 := 0x7e4000ef.
Lemma F_5de98 : fetch_word AsanUbsan.M.loaded_segments (0x5dee0 : word) = Some W_5de98.
Proof. vm_refl. Qed.
Lemma D_5de98 : decode_any W_5de98 = Some (Jal 1 2020, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de9c : bv 32 := 0x000a0613.
Lemma F_5de9c : fetch_word AsanUbsan.M.loaded_segments (0x5dee4 : word) = Some W_5de9c.
Proof. vm_refl. Qed.
Lemma D_5de9c : decode_any W_5de9c = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dea0 : bv 32 := 0x00050e63.
Lemma F_5dea0 : fetch_word AsanUbsan.M.loaded_segments (0x5dee8 : word) = Some W_5dea0.
Proof. vm_refl. Qed.
Lemma D_5dea0 : decode_any W_5dea0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dea4 : bv 32 := 0x00090693.
Lemma F_5dea4 : fetch_word AsanUbsan.M.loaded_segments (0x5deec : word) = Some W_5dea4.
Proof. vm_refl. Qed.
Lemma D_5dea4 : decode_any W_5dea4 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dea8 : bv 32 := 0x000a8713.
Lemma F_5dea8 : fetch_word AsanUbsan.M.loaded_segments (0x5def0 : word) = Some W_5dea8.
Proof. vm_refl. Qed.
Lemma D_5dea8 : decode_any W_5dea8 = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5deac : bv 32 := 0x00098513.
Lemma F_5deac : fetch_word AsanUbsan.M.loaded_segments (0x5def4 : word) = Some W_5deac.
Proof. vm_refl. Qed.
Lemma D_5deac : decode_any W_5deac = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5deb0 : bv 32 := 0x00042783.
Lemma F_5deb0 : fetch_word AsanUbsan.M.loaded_segments (0x5def8 : word) = Some W_5deb0.
Proof. vm_refl. Qed.
Lemma D_5deb0 : decode_any W_5deb0 = Some (Load SZ4 true 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5deb4 : bv 32 := 0x00048593.
Lemma F_5deb4 : fetch_word AsanUbsan.M.loaded_segments (0x5defc : word) = Some W_5deb4.
Proof. vm_refl. Qed.
Lemma D_5deb4 : decode_any W_5deb4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5deb8 : bv 32 := 0xed1ff06f.
Lemma F_5deb8 : fetch_word AsanUbsan.M.loaded_segments (0x5df00 : word) = Some W_5deb8.
Proof. vm_refl. Qed.
Lemma D_5deb8 : decode_any W_5deb8 = Some (Jal 0 2096848, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df2c : bv 32 := 0xfd010113.
Lemma F_5df2c : fetch_word AsanUbsan.M.loaded_segments (0x5df74 : word) = Some W_5df2c.
Proof. vm_refl. Qed.
Lemma D_5df2c : decode_any W_5df2c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df30 : bv 32 := 0x02113423.
Lemma F_5df30 : fetch_word AsanUbsan.M.loaded_segments (0x5df78 : word) = Some W_5df30.
Proof. vm_refl. Qed.
Lemma D_5df30 : decode_any W_5df30 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df34 : bv 32 := 0x02813023.
Lemma F_5df34 : fetch_word AsanUbsan.M.loaded_segments (0x5df7c : word) = Some W_5df34.
Proof. vm_refl. Qed.
Lemma D_5df34 : decode_any W_5df34 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df38 : bv 32 := 0x00913c23.
Lemma F_5df38 : fetch_word AsanUbsan.M.loaded_segments (0x5df80 : word) = Some W_5df38.
Proof. vm_refl. Qed.
Lemma D_5df38 : decode_any W_5df38 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df3c : bv 32 := 0x01213823.
Lemma F_5df3c : fetch_word AsanUbsan.M.loaded_segments (0x5df84 : word) = Some W_5df3c.
Proof. vm_refl. Qed.
Lemma D_5df3c : decode_any W_5df3c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df40 : bv 32 := 0x01313423.
Lemma F_5df40 : fetch_word AsanUbsan.M.loaded_segments (0x5df88 : word) = Some W_5df40.
Proof. vm_refl. Qed.
Lemma D_5df40 : decode_any W_5df40 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df44 : bv 32 := 0x01413023.
Lemma F_5df44 : fetch_word AsanUbsan.M.loaded_segments (0x5df8c : word) = Some W_5df44.
Proof. vm_refl. Qed.
Lemma D_5df44 : decode_any W_5df44 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df48 : bv 32 := 0x00163713.
Lemma F_5df48 : fetch_word AsanUbsan.M.loaded_segments (0x5df90 : word) = Some W_5df48.
Proof. vm_refl. Qed.
Lemma D_5df48 : decode_any W_5df48 = Some (OpImm ALU_SLTU 14 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df4c : bv 32 := 0x00e60633.
Lemma F_5df4c : fetch_word AsanUbsan.M.loaded_segments (0x5df94 : word) = Some W_5df4c.
Proof. vm_refl. Qed.
Lemma D_5df4c : decode_any W_5df4c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df50 : bv 32 := 0xfff64713.
Lemma F_5df50 : fetch_word AsanUbsan.M.loaded_segments (0x5df98 : word) = Some W_5df50.
Proof. vm_refl. Qed.
Lemma D_5df50 : decode_any W_5df50 = Some (OpImm ALU_XOR 14 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df54 : bv 32 := 0x02d77263.
Lemma F_5df54 : fetch_word AsanUbsan.M.loaded_segments (0x5df9c : word) = Some W_5df54.
Proof. vm_refl. Qed.
Lemma D_5df54 : decode_any W_5df54 = Some (Branch BC_GEU 14 13 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df78 : bv 32 := 0x00900793.
Lemma F_5df78 : fetch_word AsanUbsan.M.loaded_segments (0x5dfc0 : word) = Some W_5df78.
Proof. vm_refl. Qed.
Lemma D_5df78 : decode_any W_5df78 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df7c : bv 32 := 0x00060713.
Lemma F_5df7c : fetch_word AsanUbsan.M.loaded_segments (0x5dfc4 : word) = Some W_5df7c.
Proof. vm_refl. Qed.
Lemma D_5df7c : decode_any W_5df7c = Some (OpImm ALU_ADD 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df80 : bv 32 := 0x02f6e063.
Lemma F_5df80 : fetch_word AsanUbsan.M.loaded_segments (0x5dfc8 : word) = Some W_5df80.
Proof. vm_refl. Qed.
Lemma D_5df80 : decode_any W_5df80 = Some (Branch BC_LTU 13 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfa0 : bv 32 := 0x000107b7.
Lemma F_5dfa0 : fetch_word AsanUbsan.M.loaded_segments (0x5dfe8 : word) = Some W_5dfa0.
Proof. vm_refl. Qed.
Lemma D_5dfa0 : decode_any W_5dfa0 = Some (Lui 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfa4 : bv 32 := 0x00d7ee63.
Lemma F_5dfa4 : fetch_word AsanUbsan.M.loaded_segments (0x5dfec : word) = Some W_5dfa4.
Proof. vm_refl. Qed.
Lemma D_5dfa4 : decode_any W_5dfa4 = Some (Branch BC_LTU 15 13 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfa8 : bv 32 := 0x00e7ec63.
Lemma F_5dfa8 : fetch_word AsanUbsan.M.loaded_segments (0x5dff0 : word) = Some W_5dfa8.
Proof. vm_refl. Qed.
Lemma D_5dfa8 : decode_any W_5dfa8 = Some (Branch BC_LTU 15 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfac : bv 32 := 0x20000613.
Lemma F_5dfac : fetch_word AsanUbsan.M.loaded_segments (0x5dff4 : word) = Some W_5dfac.
Proof. vm_refl. Qed.
Lemma D_5dfac : decode_any W_5dfac = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfb0 : bv 32 := 0x02e66a63.
Lemma F_5dfb0 : fetch_word AsanUbsan.M.loaded_segments (0x5dff8 : word) = Some W_5dfb0.
Proof. vm_refl. Qed.
Lemma D_5dfb0 : decode_any W_5dfb0 = Some (Branch BC_LTU 12 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfb4 : bv 32 := 0x01f70713.
Lemma F_5dfb4 : fetch_word AsanUbsan.M.loaded_segments (0x5dffc : word) = Some W_5dfb4.
Proof. vm_refl. Qed.
Lemma D_5dfb4 : decode_any W_5dfb4 = Some (OpImm ALU_ADD 14 14 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfb8 : bv 32 := 0x00575413.
Lemma F_5dfb8 : fetch_word AsanUbsan.M.loaded_segments (0x5e000 : word) = Some W_5dfb8.
Proof. vm_refl. Qed.
Lemma D_5dfb8 : decode_any W_5dfb8 = Some (ShiftImm ALU_SRL 8 14 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfbc : bv 32 := 0x1040006f.
Lemma F_5dfbc : fetch_word AsanUbsan.M.loaded_segments (0x5e004 : word) = Some W_5dfbc.
Proof. vm_refl. Qed.
Lemma D_5dfbc : decode_any W_5dfbc = Some (Jal 0 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc0 : bv 32 := 0x04050713.
Lemma F_5dfc0 : fetch_word AsanUbsan.M.loaded_segments (0x5e008 : word) = Some W_5dfc0.
Proof. vm_refl. Qed.
Lemma D_5dfc0 : decode_any W_5dfc0 = Some (OpImm ALU_ADD 14 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc4 : bv 32 := 0x2b050593.
Lemma F_5dfc4 : fetch_word AsanUbsan.M.loaded_segments (0x5e00c : word) = Some W_5dfc4.
Proof. vm_refl. Qed.
Lemma D_5dfc4 : decode_any W_5dfc4 = Some (OpImm ALU_ADD 11 10 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc8 : bv 32 := 0x00070513.
Lemma F_5dfc8 : fetch_word AsanUbsan.M.loaded_segments (0x5e010 : word) = Some W_5dfc8.
Proof. vm_refl. Qed.
Lemma D_5dfc8 : decode_any W_5dfc8 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfcc : bv 32 := 0x00068413.
Lemma F_5dfcc : fetch_word AsanUbsan.M.loaded_segments (0x5e014 : word) = Some W_5dfcc.
Proof. vm_refl. Qed.
Lemma D_5dfcc : decode_any W_5dfcc = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd0 : bv 32 := 0x234000ef.
Lemma F_5dfd0 : fetch_word AsanUbsan.M.loaded_segments (0x5e018 : word) = Some W_5dfd0.
Proof. vm_refl. Qed.
Lemma D_5dfd0 : decode_any W_5dfd0 = Some (Jal 1 564, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd4 : bv 32 := 0x00040693.
Lemma F_5dfd4 : fetch_word AsanUbsan.M.loaded_segments (0x5e01c : word) = Some W_5dfd4.
Proof. vm_refl. Qed.
Lemma D_5dfd4 : decode_any W_5dfd4 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd8 : bv 32 := 0x00900593.
Lemma F_5dfd8 : fetch_word AsanUbsan.M.loaded_segments (0x5e020 : word) = Some W_5dfd8.
Proof. vm_refl. Qed.
Lemma D_5dfd8 : decode_any W_5dfd8 = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfdc : bv 32 := 0x14b47463.
Lemma F_5dfdc : fetch_word AsanUbsan.M.loaded_segments (0x5e024 : word) = Some W_5dfdc.
Proof. vm_refl. Qed.
Lemma D_5dfdc : decode_any W_5dfdc = Some (Branch BC_GEU 8 11 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe0 : bv 32 := 0x1500006f.
Lemma F_5dfe0 : fetch_word AsanUbsan.M.loaded_segments (0x5e028 : word) = Some W_5dfe0.
Proof. vm_refl. Qed.
Lemma D_5dfe0 : decode_any W_5dfe0 = Some (Jal 0 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe4 : bv 32 := 0x00175613.
Lemma F_5dfe4 : fetch_word AsanUbsan.M.loaded_segments (0x5e02c : word) = Some W_5dfe4.
Proof. vm_refl. Qed.
Lemma D_5dfe4 : decode_any W_5dfe4 = Some (ShiftImm ALU_SRL 12 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe8 : bv 32 := 0x555557b7.
Lemma F_5dfe8 : fetch_word AsanUbsan.M.loaded_segments (0x5e030 : word) = Some W_5dfe8.
Proof. vm_refl. Qed.
Lemma D_5dfe8 : decode_any W_5dfe8 = Some (Lui 15 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfec : bv 32 := 0x33333837.
Lemma F_5dfec : fetch_word AsanUbsan.M.loaded_segments (0x5e034 : word) = Some W_5dfec.
Proof. vm_refl. Qed.
Lemma D_5dfec : decode_any W_5dfec = Some (Lui 16 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff0 : bv 32 := 0x0f0f18b7.
Lemma F_5dff0 : fetch_word AsanUbsan.M.loaded_segments (0x5e038 : word) = Some W_5dff0.
Proof. vm_refl. Qed.
Lemma D_5dff0 : decode_any W_5dff0 = Some (Lui 17 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff4 : bv 32 := 0x010102b7.
Lemma F_5dff4 : fetch_word AsanUbsan.M.loaded_segments (0x5e03c : word) = Some W_5dff4.
Proof. vm_refl. Qed.
Lemma D_5dff4 : decode_any W_5dff4 = Some (Lui 5 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff8 : bv 32 := 0x00c76633.
Lemma F_5dff8 : fetch_word AsanUbsan.M.loaded_segments (0x5e040 : word) = Some W_5dff8.
Proof. vm_refl. Qed.
Lemma D_5dff8 : decode_any W_5dff8 = Some (Op ALU_OR 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dffc : bv 32 := 0x5557879b.
Lemma F_5dffc : fetch_word AsanUbsan.M.loaded_segments (0x5e044 : word) = Some W_5dffc.
Proof. vm_refl. Qed.
Lemma D_5dffc : decode_any W_5dffc = Some (OpImm32 15 15 1365, 4%Z).
Proof. vm_refl. Qed.

