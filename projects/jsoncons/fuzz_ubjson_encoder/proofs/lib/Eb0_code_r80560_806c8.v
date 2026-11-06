(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9baa4 : bv 32 := 0x00008513.
Lemma F_9baa4 : fetch_word AsanUbsan.M.loaded_segments (0x9baf4 : word) = Some W_9baa4.
Proof. vm_refl. Qed.
Lemma D_9baa4 : decode_any W_9baa4 = Some (OpImm ALU_ADD 10 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9baa8 : bv 32 := 0x00008067.
Lemma F_9baa8 : fetch_word AsanUbsan.M.loaded_segments (0x9baf8 : word) = Some W_9baa8.
Proof. vm_refl. Qed.
Lemma D_9baa8 : decode_any W_9baa8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9baac : bv 32 := 0xfc010113.
Lemma F_9baac : fetch_word AsanUbsan.M.loaded_segments (0x9bafc : word) = Some W_9baac.
Proof. vm_refl. Qed.
Lemma D_9baac : decode_any W_9baac = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bab0 : bv 32 := 0x02113c23.
Lemma F_9bab0 : fetch_word AsanUbsan.M.loaded_segments (0x9bb00 : word) = Some W_9bab0.
Proof. vm_refl. Qed.
Lemma D_9bab0 : decode_any W_9bab0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bab4 : bv 32 := 0x02813823.
Lemma F_9bab4 : fetch_word AsanUbsan.M.loaded_segments (0x9bb04 : word) = Some W_9bab4.
Proof. vm_refl. Qed.
Lemma D_9bab4 : decode_any W_9bab4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bab8 : bv 32 := 0x02913423.
Lemma F_9bab8 : fetch_word AsanUbsan.M.loaded_segments (0x9bb08 : word) = Some W_9bab8.
Proof. vm_refl. Qed.
Lemma D_9bab8 : decode_any W_9bab8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9babc : bv 32 := 0x03213023.
Lemma F_9babc : fetch_word AsanUbsan.M.loaded_segments (0x9bb0c : word) = Some W_9babc.
Proof. vm_refl. Qed.
Lemma D_9babc : decode_any W_9babc = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bac0 : bv 32 := 0x01313c23.
Lemma F_9bac0 : fetch_word AsanUbsan.M.loaded_segments (0x9bb10 : word) = Some W_9bac0.
Proof. vm_refl. Qed.
Lemma D_9bac0 : decode_any W_9bac0 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bac4 : bv 32 := 0x01413823.
Lemma F_9bac4 : fetch_word AsanUbsan.M.loaded_segments (0x9bb14 : word) = Some W_9bac4.
Proof. vm_refl. Qed.
Lemma D_9bac4 : decode_any W_9bac4 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bac8 : bv 32 := 0x01513423.
Lemma F_9bac8 : fetch_word AsanUbsan.M.loaded_segments (0x9bb18 : word) = Some W_9bac8.
Proof. vm_refl. Qed.
Lemma D_9bac8 : decode_any W_9bac8 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bacc : bv 32 := 0x01613023.
Lemma F_9bacc : fetch_word AsanUbsan.M.loaded_segments (0x9bb1c : word) = Some W_9bacc.
Proof. vm_refl. Qed.
Lemma D_9bacc : decode_any W_9bacc = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bad0 : bv 32 := 0x00068493.
Lemma F_9bad0 : fetch_word AsanUbsan.M.loaded_segments (0x9bb20 : word) = Some W_9bad0.
Proof. vm_refl. Qed.
Lemma D_9bad0 : decode_any W_9bad0 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bad4 : bv 32 := 0x02079413.
Lemma F_9bad4 : fetch_word AsanUbsan.M.loaded_segments (0x9bb24 : word) = Some W_9bad4.
Proof. vm_refl. Qed.
Lemma D_9bad4 : decode_any W_9bad4 = Some (ShiftImm ALU_SLL 8 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bad8 : bv 32 := 0x00100693.
Lemma F_9bad8 : fetch_word AsanUbsan.M.loaded_segments (0x9bb28 : word) = Some W_9bad8.
Proof. vm_refl. Qed.
Lemma D_9bad8 : decode_any W_9bad8 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9badc : bv 32 := 0x02045413.
Lemma F_9badc : fetch_word AsanUbsan.M.loaded_segments (0x9bb2c : word) = Some W_9badc.
Proof. vm_refl. Qed.
Lemma D_9badc : decode_any W_9badc = Some (ShiftImm ALU_SRL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bae0 : bv 32 := 0x0ef6f863.
Lemma F_9bae0 : fetch_word AsanUbsan.M.loaded_segments (0x9bb30 : word) = Some W_9bae0.
Proof. vm_refl. Qed.
Lemma D_9bae0 : decode_any W_9bae0 = Some (Branch BC_GEU 13 15 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bae4 : bv 32 := 0x000a2697.
Lemma F_9bae4 : fetch_word AsanUbsan.M.loaded_segments (0x9bb34 : word) = Some W_9bae4.
Proof. vm_refl. Qed.
Lemma D_9bae4 : decode_any W_9bae4 = Some (Auipc 13 162, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bae8 : bv 32 := 0xd746b903.
Lemma F_9bae8 : fetch_word AsanUbsan.M.loaded_segments (0x9bb38 : word) = Some W_9bae8.
Proof. vm_refl. Qed.
Lemma D_9bae8 : decode_any W_9bae8 = Some (Load SZ8 true 18 13 3444, 4%Z).
Proof. vm_refl. Qed.

Definition W_9baec : bv 32 := 0x00093683.
Lemma F_9baec : fetch_word AsanUbsan.M.loaded_segments (0x9bb3c : word) = Some W_9baec.
Proof. vm_refl. Qed.
Lemma D_9baec : decode_any W_9baec = Some (Load SZ8 true 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9baf0 : bv 32 := 0x00068e63.
Lemma F_9baf0 : fetch_word AsanUbsan.M.loaded_segments (0x9bb40 : word) = Some W_9baf0.
Proof. vm_refl. Qed.
Lemma D_9baf0 : decode_any W_9baf0 = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9baf4 : bv 32 := 0x00100793.
Lemma F_9baf4 : fetch_word AsanUbsan.M.loaded_segments (0x9bb44 : word) = Some W_9baf4.
Proof. vm_refl. Qed.
Lemma D_9baf4 : decode_any W_9baf4 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9baf8 : bv 32 := 0x00c4d813.
Lemma F_9baf8 : fetch_word AsanUbsan.M.loaded_segments (0x9bb48 : word) = Some W_9baf8.
Proof. vm_refl. Qed.
Lemma D_9baf8 : decode_any W_9baf8 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bafc : bv 32 := 0x00f52423.
Lemma F_9bafc : fetch_word AsanUbsan.M.loaded_segments (0x9bb4c : word) = Some W_9bafc.
Proof. vm_refl. Qed.
Lemma D_9bafc : decode_any W_9bafc = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb00 : bv 32 := 0x00b53823.
Lemma F_9bb00 : fetch_word AsanUbsan.M.loaded_segments (0x9bb50 : word) = Some W_9bb00.
Proof. vm_refl. Qed.
Lemma D_9bb00 : decode_any W_9bb00 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb04 : bv 32 := 0x04081463.
Lemma F_9bb04 : fetch_word AsanUbsan.M.loaded_segments (0x9bb54 : word) = Some W_9bb04.
Proof. vm_refl. Qed.
Lemma D_9bb04 : decode_any W_9bb04 = Some (Branch BC_NE 16 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb4c : bv 32 := 0x0a977263.
Lemma F_9bb4c : fetch_word AsanUbsan.M.loaded_segments (0x9bb9c : word) = Some W_9bb4c.
Proof. vm_refl. Qed.
Lemma D_9bb4c : decode_any W_9bb4c = Some (Branch BC_GEU 14 9 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb50 : bv 32 := 0x04c77c63.
Lemma F_9bb50 : fetch_word AsanUbsan.M.loaded_segments (0x9bba0 : word) = Some W_9bb50.
Proof. vm_refl. Qed.
Lemma D_9bb50 : decode_any W_9bb50 = Some (Branch BC_GEU 14 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb54 : bv 32 := 0xff048493.
Lemma F_9bb54 : fetch_word AsanUbsan.M.loaded_segments (0x9bba4 : word) = Some W_9bb54.
Proof. vm_refl. Qed.
Lemma D_9bb54 : decode_any W_9bb54 = Some (OpImm ALU_ADD 9 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb58 : bv 32 := 0x04967863.
Lemma F_9bb58 : fetch_word AsanUbsan.M.loaded_segments (0x9bba8 : word) = Some W_9bb58.
Proof. vm_refl. Qed.
Lemma D_9bb58 : decode_any W_9bb58 = Some (Branch BC_GEU 12 9 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb5c : bv 32 := 0x00767713.
Lemma F_9bb5c : fetch_word AsanUbsan.M.loaded_segments (0x9bbac : word) = Some W_9bb5c.
Proof. vm_refl. Qed.
Lemma D_9bb5c : decode_any W_9bb5c = Some (OpImm ALU_AND 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb60 : bv 32 := 0x04071463.
Lemma F_9bb60 : fetch_word AsanUbsan.M.loaded_segments (0x9bbb0 : word) = Some W_9bb60.
Proof. vm_refl. Qed.
Lemma D_9bb60 : decode_any W_9bb60 = Some (Branch BC_NE 14 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb64 : bv 32 := 0x01050713.
Lemma F_9bb64 : fetch_word AsanUbsan.M.loaded_segments (0x9bbb4 : word) = Some W_9bb64.
Proof. vm_refl. Qed.
Lemma D_9bb64 : decode_any W_9bb64 = Some (OpImm ALU_ADD 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb68 : bv 32 := 0x00100793.
Lemma F_9bb68 : fetch_word AsanUbsan.M.loaded_segments (0x9bbb8 : word) = Some W_9bb68.
Proof. vm_refl. Qed.
Lemma D_9bb68 : decode_any W_9bb68 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb6c : bv 32 := 0x0287fe63.
Lemma F_9bb6c : fetch_word AsanUbsan.M.loaded_segments (0x9bbbc : word) = Some W_9bb6c.
Proof. vm_refl. Qed.
Lemma D_9bb6c : decode_any W_9bb6c = Some (Branch BC_GEU 15 8 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb70 : bv 32 := 0xff863803.
Lemma F_9bb70 : fetch_word AsanUbsan.M.loaded_segments (0x9bbc0 : word) = Some W_9bb70.
Proof. vm_refl. Qed.
Lemma D_9bb70 : decode_any W_9bb70 = Some (Load SZ8 true 16 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb74 : bv 32 := 0x02d86a63.
Lemma F_9bb74 : fetch_word AsanUbsan.M.loaded_segments (0x9bbc4 : word) = Some W_9bb74.
Proof. vm_refl. Qed.
Lemma D_9bb74 : decode_any W_9bb74 = Some (Branch BC_LTU 16 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb78 : bv 32 := 0x00b80c63.
Lemma F_9bb78 : fetch_word AsanUbsan.M.loaded_segments (0x9bbc8 : word) = Some W_9bb78.
Proof. vm_refl. Qed.
Lemma D_9bb78 : decode_any W_9bb78 = Some (Branch BC_EQ 16 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb7c : bv 32 := 0x00379893.
Lemma F_9bb7c : fetch_word AsanUbsan.M.loaded_segments (0x9bbcc : word) = Some W_9bb7c.
Proof. vm_refl. Qed.
Lemma D_9bb7c : decode_any W_9bb7c = Some (ShiftImm ALU_SLL 17 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb80 : bv 32 := 0x00178793.
Lemma F_9bb80 : fetch_word AsanUbsan.M.loaded_segments (0x9bbd0 : word) = Some W_9bb80.
Proof. vm_refl. Qed.
Lemma D_9bb80 : decode_any W_9bb80 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb84 : bv 32 := 0x011708b3.
Lemma F_9bb84 : fetch_word AsanUbsan.M.loaded_segments (0x9bbd4 : word) = Some W_9bb84.
Proof. vm_refl. Qed.
Lemma D_9bb84 : decode_any W_9bb84 = Some (Op ALU_ADD 17 14 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb88 : bv 32 := 0x00f52423.
Lemma F_9bb88 : fetch_word AsanUbsan.M.loaded_segments (0x9bbd8 : word) = Some W_9bb88.
Proof. vm_refl. Qed.
Lemma D_9bb88 : decode_any W_9bb88 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb8c : bv 32 := 0x0108b023.
Lemma F_9bb8c : fetch_word AsanUbsan.M.loaded_segments (0x9bbdc : word) = Some W_9bb8c.
Proof. vm_refl. Qed.
Lemma D_9bb8c : decode_any W_9bb8c = Some (Store SZ8 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb90 : bv 32 := 0xff063803.
Lemma F_9bb90 : fetch_word AsanUbsan.M.loaded_segments (0x9bbe0 : word) = Some W_9bb90.
Proof. vm_refl. Qed.
Lemma D_9bb90 : decode_any W_9bb90 = Some (Load SZ8 true 16 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb94 : bv 32 := 0x01067a63.
Lemma F_9bb94 : fetch_word AsanUbsan.M.loaded_segments (0x9bbe4 : word) = Some W_9bb94.
Proof. vm_refl. Qed.
Lemma D_9bb94 : decode_any W_9bb94 = Some (Branch BC_GEU 12 16 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb98 : bv 32 := 0x00987863.
Lemma F_9bb98 : fetch_word AsanUbsan.M.loaded_segments (0x9bbe8 : word) = Some W_9bb98.
Proof. vm_refl. Qed.
Lemma D_9bb98 : decode_any W_9bb98 = Some (Branch BC_GEU 16 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bb9c : bv 32 := 0x00787893.
Lemma F_9bb9c : fetch_word AsanUbsan.M.loaded_segments (0x9bbec : word) = Some W_9bb9c.
Proof. vm_refl. Qed.
Lemma D_9bb9c : decode_any W_9bb9c = Some (OpImm ALU_AND 17 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bba0 : bv 32 := 0x00080613.
Lemma F_9bba0 : fetch_word AsanUbsan.M.loaded_segments (0x9bbf0 : word) = Some W_9bba0.
Proof. vm_refl. Qed.
Lemma D_9bba0 : decode_any W_9bba0 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bba4 : bv 32 := 0xfc0884e3.
Lemma F_9bba4 : fetch_word AsanUbsan.M.loaded_segments (0x9bbf4 : word) = Some W_9bba4.
Proof. vm_refl. Qed.
Lemma D_9bba4 : decode_any W_9bba4 = Some (Branch BC_EQ 17 0 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bba8 : bv 32 := 0x03813083.
Lemma F_9bba8 : fetch_word AsanUbsan.M.loaded_segments (0x9bbf8 : word) = Some W_9bba8.
Proof. vm_refl. Qed.
Lemma D_9bba8 : decode_any W_9bba8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbac : bv 32 := 0x03013403.
Lemma F_9bbac : fetch_word AsanUbsan.M.loaded_segments (0x9bbfc : word) = Some W_9bbac.
Proof. vm_refl. Qed.
Lemma D_9bbac : decode_any W_9bbac = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbb0 : bv 32 := 0x02813483.
Lemma F_9bbb0 : fetch_word AsanUbsan.M.loaded_segments (0x9bc00 : word) = Some W_9bbb0.
Proof. vm_refl. Qed.
Lemma D_9bbb0 : decode_any W_9bbb0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbb4 : bv 32 := 0x02013903.
Lemma F_9bbb4 : fetch_word AsanUbsan.M.loaded_segments (0x9bc04 : word) = Some W_9bbb4.
Proof. vm_refl. Qed.
Lemma D_9bbb4 : decode_any W_9bbb4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbb8 : bv 32 := 0x01813983.
Lemma F_9bbb8 : fetch_word AsanUbsan.M.loaded_segments (0x9bc08 : word) = Some W_9bbb8.
Proof. vm_refl. Qed.
Lemma D_9bbb8 : decode_any W_9bbb8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbbc : bv 32 := 0x01013a03.
Lemma F_9bbbc : fetch_word AsanUbsan.M.loaded_segments (0x9bc0c : word) = Some W_9bbbc.
Proof. vm_refl. Qed.
Lemma D_9bbbc : decode_any W_9bbbc = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbc0 : bv 32 := 0x00813a83.
Lemma F_9bbc0 : fetch_word AsanUbsan.M.loaded_segments (0x9bc10 : word) = Some W_9bbc0.
Proof. vm_refl. Qed.
Lemma D_9bbc0 : decode_any W_9bbc0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbc4 : bv 32 := 0x00013b03.
Lemma F_9bbc4 : fetch_word AsanUbsan.M.loaded_segments (0x9bc14 : word) = Some W_9bbc4.
Proof. vm_refl. Qed.
Lemma D_9bbc4 : decode_any W_9bbc4 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbc8 : bv 32 := 0x04010113.
Lemma F_9bbc8 : fetch_word AsanUbsan.M.loaded_segments (0x9bc18 : word) = Some W_9bbc8.
Proof. vm_refl. Qed.
Lemma D_9bbc8 : decode_any W_9bbc8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9bbcc : bv 32 := 0x00008067.
Lemma F_9bbcc : fetch_word AsanUbsan.M.loaded_segments (0x9bc1c : word) = Some W_9bbcc.
Proof. vm_refl. Qed.
Lemma D_9bbcc : decode_any W_9bbcc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
