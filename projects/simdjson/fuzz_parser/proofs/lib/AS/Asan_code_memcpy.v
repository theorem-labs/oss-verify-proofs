(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_parser.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_fcf5c : bv 32 := 0x0035f693.
Lemma F_fcf5c : fetch_word Asan.M.loaded_segments (0xfd118 : word) = Some W_fcf5c.
Proof. vm_refl. Qed.
Lemma D_fcf5c : decode_any W_fcf5c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf60 : bv 32 := 0x10068863.
Lemma F_fcf60 : fetch_word Asan.M.loaded_segments (0xfd11c : word) = Some W_fcf60.
Proof. vm_refl. Qed.
Lemma D_fcf60 : decode_any W_fcf60 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf64 : bv 32 := 0x02060e63.
Lemma F_fcf64 : fetch_word Asan.M.loaded_segments (0xfd120 : word) = Some W_fcf64.
Proof. vm_refl. Qed.
Lemma D_fcf64 : decode_any W_fcf64 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf68 : bv 32 := 0x00158713.
Lemma F_fcf68 : fetch_word Asan.M.loaded_segments (0xfd124 : word) = Some W_fcf68.
Proof. vm_refl. Qed.
Lemma D_fcf68 : decode_any W_fcf68 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf6c : bv 32 := 0x00100793.
Lemma F_fcf6c : fetch_word Asan.M.loaded_segments (0xfd128 : word) = Some W_fcf6c.
Proof. vm_refl. Qed.
Lemma D_fcf6c : decode_any W_fcf6c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf70 : bv 32 := 0x00050693.
Lemma F_fcf70 : fetch_word Asan.M.loaded_segments (0xfd12c : word) = Some W_fcf70.
Proof. vm_refl. Qed.
Lemma D_fcf70 : decode_any W_fcf70 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf74 : bv 32 := 0x0005c883.
Lemma F_fcf74 : fetch_word Asan.M.loaded_segments (0xfd130 : word) = Some W_fcf74.
Proof. vm_refl. Qed.
Lemma D_fcf74 : decode_any W_fcf74 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf78 : bv 32 := 0x00060813.
Lemma F_fcf78 : fetch_word Asan.M.loaded_segments (0xfd134 : word) = Some W_fcf78.
Proof. vm_refl. Qed.
Lemma D_fcf78 : decode_any W_fcf78 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf7c : bv 32 := 0x00158593.
Lemma F_fcf7c : fetch_word Asan.M.loaded_segments (0xfd138 : word) = Some W_fcf7c.
Proof. vm_refl. Qed.
Lemma D_fcf7c : decode_any W_fcf7c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf80 : bv 32 := 0x00377293.
Lemma F_fcf80 : fetch_word Asan.M.loaded_segments (0xfd13c : word) = Some W_fcf80.
Proof. vm_refl. Qed.
Lemma D_fcf80 : decode_any W_fcf80 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf84 : bv 32 := 0x01168023.
Lemma F_fcf84 : fetch_word Asan.M.loaded_segments (0xfd140 : word) = Some W_fcf84.
Proof. vm_refl. Qed.
Lemma D_fcf84 : decode_any W_fcf84 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf88 : bv 32 := 0x00168693.
Lemma F_fcf88 : fetch_word Asan.M.loaded_segments (0xfd144 : word) = Some W_fcf88.
Proof. vm_refl. Qed.
Lemma D_fcf88 : decode_any W_fcf88 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf8c : bv 32 := 0xfff60613.
Lemma F_fcf8c : fetch_word Asan.M.loaded_segments (0xfd148 : word) = Some W_fcf8c.
Proof. vm_refl. Qed.
Lemma D_fcf8c : decode_any W_fcf8c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf90 : bv 32 := 0x00028a63.
Lemma F_fcf90 : fetch_word Asan.M.loaded_segments (0xfd14c : word) = Some W_fcf90.
Proof. vm_refl. Qed.
Lemma D_fcf90 : decode_any W_fcf90 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf94 : bv 32 := 0x00170713.
Lemma F_fcf94 : fetch_word Asan.M.loaded_segments (0xfd150 : word) = Some W_fcf94.
Proof. vm_refl. Qed.
Lemma D_fcf94 : decode_any W_fcf94 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf98 : bv 32 := 0xfcf81ee3.
Lemma F_fcf98 : fetch_word Asan.M.loaded_segments (0xfd154 : word) = Some W_fcf98.
Proof. vm_refl. Qed.
Lemma D_fcf98 : decode_any W_fcf98 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcf9c : bv 32 := 0x0080006f.
Lemma F_fcf9c : fetch_word Asan.M.loaded_segments (0xfd158 : word) = Some W_fcf9c.
Proof. vm_refl. Qed.
Lemma D_fcf9c : decode_any W_fcf9c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfa0 : bv 32 := 0x00050693.
Lemma F_fcfa0 : fetch_word Asan.M.loaded_segments (0xfd15c : word) = Some W_fcfa0.
Proof. vm_refl. Qed.
Lemma D_fcfa0 : decode_any W_fcfa0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfa4 : bv 32 := 0x0036f793.
Lemma F_fcfa4 : fetch_word Asan.M.loaded_segments (0xfd160 : word) = Some W_fcfa4.
Proof. vm_refl. Qed.
Lemma D_fcfa4 : decode_any W_fcfa4 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfa8 : bv 32 := 0x0c078a63.
Lemma F_fcfa8 : fetch_word Asan.M.loaded_segments (0xfd164 : word) = Some W_fcfa8.
Proof. vm_refl. Qed.
Lemma D_fcfa8 : decode_any W_fcfa8 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfac : bv 32 := 0x02000713.
Lemma F_fcfac : fetch_word Asan.M.loaded_segments (0xfd168 : word) = Some W_fcfac.
Proof. vm_refl. Qed.
Lemma D_fcfac : decode_any W_fcfac = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfb0 : bv 32 := 0x02e67063.
Lemma F_fcfb0 : fetch_word Asan.M.loaded_segments (0xfd16c : word) = Some W_fcfb0.
Proof. vm_refl. Qed.
Lemma D_fcfb0 : decode_any W_fcfb0 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfb4 : bv 32 := 0x01000713.
Lemma F_fcfb4 : fetch_word Asan.M.loaded_segments (0xfd170 : word) = Some W_fcfb4.
Proof. vm_refl. Qed.
Lemma D_fcfb4 : decode_any W_fcfb4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfb8 : bv 32 := 0x24e67863.
Lemma F_fcfb8 : fetch_word Asan.M.loaded_segments (0xfd174 : word) = Some W_fcfb8.
Proof. vm_refl. Qed.
Lemma D_fcfb8 : decode_any W_fcfb8 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfbc : bv 32 := 0x00867713.
Lemma F_fcfbc : fetch_word Asan.M.loaded_segments (0xfd178 : word) = Some W_fcfbc.
Proof. vm_refl. Qed.
Lemma D_fcfbc : decode_any W_fcfbc = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfc0 : bv 32 := 0x2c071e63.
Lemma F_fcfc0 : fetch_word Asan.M.loaded_segments (0xfd17c : word) = Some W_fcfc0.
Proof. vm_refl. Qed.
Lemma D_fcfc0 : decode_any W_fcfc0 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfc4 : bv 32 := 0x00467713.
Lemma F_fcfc4 : fetch_word Asan.M.loaded_segments (0xfd180 : word) = Some W_fcfc4.
Proof. vm_refl. Qed.
Lemma D_fcfc4 : decode_any W_fcfc4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfc8 : bv 32 := 0x32071463.
Lemma F_fcfc8 : fetch_word Asan.M.loaded_segments (0xfd184 : word) = Some W_fcfc8.
Proof. vm_refl. Qed.
Lemma D_fcfc8 : decode_any W_fcfc8 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfcc : bv 32 := 0x3500006f.
Lemma F_fcfcc : fetch_word Asan.M.loaded_segments (0xfd188 : word) = Some W_fcfcc.
Proof. vm_refl. Qed.
Lemma D_fcfcc : decode_any W_fcfcc = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfd0 : bv 32 := 0x0005a703.
Lemma F_fcfd0 : fetch_word Asan.M.loaded_segments (0xfd18c : word) = Some W_fcfd0.
Proof. vm_refl. Qed.
Lemma D_fcfd0 : decode_any W_fcfd0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfd4 : bv 32 := 0x00300813.
Lemma F_fcfd4 : fetch_word Asan.M.loaded_segments (0xfd190 : word) = Some W_fcfd4.
Proof. vm_refl. Qed.
Lemma D_fcfd4 : decode_any W_fcfd4 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfd8 : bv 32 := 0x11078e63.
Lemma F_fcfd8 : fetch_word Asan.M.loaded_segments (0xfd194 : word) = Some W_fcfd8.
Proof. vm_refl. Qed.
Lemma D_fcfd8 : decode_any W_fcfd8 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfdc : bv 32 := 0x00200813.
Lemma F_fcfdc : fetch_word Asan.M.loaded_segments (0xfd198 : word) = Some W_fcfdc.
Proof. vm_refl. Qed.
Lemma D_fcfdc : decode_any W_fcfdc = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfe0 : bv 32 := 0x19079c63.
Lemma F_fcfe0 : fetch_word Asan.M.loaded_segments (0xfd19c : word) = Some W_fcfe0.
Proof. vm_refl. Qed.
Lemma D_fcfe0 : decode_any W_fcfe0 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfe4 : bv 32 := 0x00875793.
Lemma F_fcfe4 : fetch_word Asan.M.loaded_segments (0xfd1a0 : word) = Some W_fcfe4.
Proof. vm_refl. Qed.
Lemma D_fcfe4 : decode_any W_fcfe4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfe8 : bv 32 := 0xffe60613.
Lemma F_fcfe8 : fetch_word Asan.M.loaded_segments (0xfd1a4 : word) = Some W_fcfe8.
Proof. vm_refl. Qed.
Lemma D_fcfe8 : decode_any W_fcfe8 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcfec : bv 32 := 0x00e68023.
Lemma F_fcfec : fetch_word Asan.M.loaded_segments (0xfd1a8 : word) = Some W_fcfec.
Proof. vm_refl. Qed.
Lemma D_fcfec : decode_any W_fcfec = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcff0 : bv 32 := 0x00f680a3.
Lemma F_fcff0 : fetch_word Asan.M.loaded_segments (0xfd1ac : word) = Some W_fcff0.
Proof. vm_refl. Qed.
Lemma D_fcff0 : decode_any W_fcff0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcff4 : bv 32 := 0x00268693.
Lemma F_fcff4 : fetch_word Asan.M.loaded_segments (0xfd1b0 : word) = Some W_fcff4.
Proof. vm_refl. Qed.
Lemma D_fcff4 : decode_any W_fcff4 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcff8 : bv 32 := 0x01058593.
Lemma F_fcff8 : fetch_word Asan.M.loaded_segments (0xfd1b4 : word) = Some W_fcff8.
Proof. vm_refl. Qed.
Lemma D_fcff8 : decode_any W_fcff8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fcffc : bv 32 := 0x01100793.
Lemma F_fcffc : fetch_word Asan.M.loaded_segments (0xfd1b8 : word) = Some W_fcffc.
Proof. vm_refl. Qed.
Lemma D_fcffc : decode_any W_fcffc = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd000 : bv 32 := 0x0107581b.
Lemma F_fd000 : fetch_word Asan.M.loaded_segments (0xfd1bc : word) = Some W_fd000.
Proof. vm_refl. Qed.
Lemma D_fd000 : decode_any W_fd000 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd004 : bv 32 := 0xff45a883.
Lemma F_fd004 : fetch_word Asan.M.loaded_segments (0xfd1c0 : word) = Some W_fd004.
Proof. vm_refl. Qed.
Lemma D_fd004 : decode_any W_fd004 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd008 : bv 32 := 0xff85a283.
Lemma F_fd008 : fetch_word Asan.M.loaded_segments (0xfd1c4 : word) = Some W_fd008.
Proof. vm_refl. Qed.
Lemma D_fd008 : decode_any W_fd008 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd00c : bv 32 := 0xffc5a303.
Lemma F_fd00c : fetch_word Asan.M.loaded_segments (0xfd1c8 : word) = Some W_fd00c.
Proof. vm_refl. Qed.
Lemma D_fd00c : decode_any W_fd00c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd010 : bv 32 := 0x0005a703.
Lemma F_fd010 : fetch_word Asan.M.loaded_segments (0xfd1cc : word) = Some W_fd010.
Proof. vm_refl. Qed.
Lemma D_fd010 : decode_any W_fd010 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd014 : bv 32 := 0x01089393.
Lemma F_fd014 : fetch_word Asan.M.loaded_segments (0xfd1d0 : word) = Some W_fd014.
Proof. vm_refl. Qed.
Lemma D_fd014 : decode_any W_fd014 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd018 : bv 32 := 0x0108d89b.
Lemma F_fd018 : fetch_word Asan.M.loaded_segments (0xfd1d4 : word) = Some W_fd018.
Proof. vm_refl. Qed.
Lemma D_fd018 : decode_any W_fd018 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd01c : bv 32 := 0x0103e833.
Lemma F_fd01c : fetch_word Asan.M.loaded_segments (0xfd1d8 : word) = Some W_fd01c.
Proof. vm_refl. Qed.
Lemma D_fd01c : decode_any W_fd01c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd020 : bv 32 := 0x01029393.
Lemma F_fd020 : fetch_word Asan.M.loaded_segments (0xfd1dc : word) = Some W_fd020.
Proof. vm_refl. Qed.
Lemma D_fd020 : decode_any W_fd020 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd024 : bv 32 := 0x0102d29b.
Lemma F_fd024 : fetch_word Asan.M.loaded_segments (0xfd1e0 : word) = Some W_fd024.
Proof. vm_refl. Qed.
Lemma D_fd024 : decode_any W_fd024 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd028 : bv 32 := 0x0113e8b3.
Lemma F_fd028 : fetch_word Asan.M.loaded_segments (0xfd1e4 : word) = Some W_fd028.
Proof. vm_refl. Qed.
Lemma D_fd028 : decode_any W_fd028 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd02c : bv 32 := 0x01031393.
Lemma F_fd02c : fetch_word Asan.M.loaded_segments (0xfd1e8 : word) = Some W_fd02c.
Proof. vm_refl. Qed.
Lemma D_fd02c : decode_any W_fd02c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd030 : bv 32 := 0x0103531b.
Lemma F_fd030 : fetch_word Asan.M.loaded_segments (0xfd1ec : word) = Some W_fd030.
Proof. vm_refl. Qed.
Lemma D_fd030 : decode_any W_fd030 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd034 : bv 32 := 0x0053e2b3.
Lemma F_fd034 : fetch_word Asan.M.loaded_segments (0xfd1f0 : word) = Some W_fd034.
Proof. vm_refl. Qed.
Lemma D_fd034 : decode_any W_fd034 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd038 : bv 32 := 0x01071393.
Lemma F_fd038 : fetch_word Asan.M.loaded_segments (0xfd1f4 : word) = Some W_fd038.
Proof. vm_refl. Qed.
Lemma D_fd038 : decode_any W_fd038 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd03c : bv 32 := 0x0063e333.
Lemma F_fd03c : fetch_word Asan.M.loaded_segments (0xfd1f8 : word) = Some W_fd03c.
Proof. vm_refl. Qed.
Lemma D_fd03c : decode_any W_fd03c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd040 : bv 32 := 0xff060613.
Lemma F_fd040 : fetch_word Asan.M.loaded_segments (0xfd1fc : word) = Some W_fd040.
Proof. vm_refl. Qed.
Lemma D_fd040 : decode_any W_fd040 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd044 : bv 32 := 0x0106a023.
Lemma F_fd044 : fetch_word Asan.M.loaded_segments (0xfd200 : word) = Some W_fd044.
Proof. vm_refl. Qed.
Lemma D_fd044 : decode_any W_fd044 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd048 : bv 32 := 0x0116a223.
Lemma F_fd048 : fetch_word Asan.M.loaded_segments (0xfd204 : word) = Some W_fd048.
Proof. vm_refl. Qed.
Lemma D_fd048 : decode_any W_fd048 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd04c : bv 32 := 0x0056a423.
Lemma F_fd04c : fetch_word Asan.M.loaded_segments (0xfd208 : word) = Some W_fd04c.
Proof. vm_refl. Qed.
Lemma D_fd04c : decode_any W_fd04c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd050 : bv 32 := 0x0066a623.
Lemma F_fd050 : fetch_word Asan.M.loaded_segments (0xfd20c : word) = Some W_fd050.
Proof. vm_refl. Qed.
Lemma D_fd050 : decode_any W_fd050 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd054 : bv 32 := 0x01068693.
Lemma F_fd054 : fetch_word Asan.M.loaded_segments (0xfd210 : word) = Some W_fd054.
Proof. vm_refl. Qed.
Lemma D_fd054 : decode_any W_fd054 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd058 : bv 32 := 0x01058593.
Lemma F_fd058 : fetch_word Asan.M.loaded_segments (0xfd214 : word) = Some W_fd058.
Proof. vm_refl. Qed.
Lemma D_fd058 : decode_any W_fd058 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd05c : bv 32 := 0xfac7e2e3.
Lemma F_fd05c : fetch_word Asan.M.loaded_segments (0xfd218 : word) = Some W_fd05c.
Proof. vm_refl. Qed.
Lemma D_fd05c : decode_any W_fd05c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd060 : bv 32 := 0xff258593.
Lemma F_fd060 : fetch_word Asan.M.loaded_segments (0xfd21c : word) = Some W_fd060.
Proof. vm_refl. Qed.
Lemma D_fd060 : decode_any W_fd060 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd064 : bv 32 := 0x01000713.
Lemma F_fd064 : fetch_word Asan.M.loaded_segments (0xfd220 : word) = Some W_fd064.
Proof. vm_refl. Qed.
Lemma D_fd064 : decode_any W_fd064 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd068 : bv 32 := 0xf4e66ae3.
Lemma F_fd068 : fetch_word Asan.M.loaded_segments (0xfd224 : word) = Some W_fd068.
Proof. vm_refl. Qed.
Lemma D_fd068 : decode_any W_fd068 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd06c : bv 32 := 0x19c0006f.
Lemma F_fd06c : fetch_word Asan.M.loaded_segments (0xfd228 : word) = Some W_fd06c.
Proof. vm_refl. Qed.
Lemma D_fd06c : decode_any W_fd06c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd070 : bv 32 := 0x00050693.
Lemma F_fd070 : fetch_word Asan.M.loaded_segments (0xfd22c : word) = Some W_fd070.
Proof. vm_refl. Qed.
Lemma D_fd070 : decode_any W_fd070 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd074 : bv 32 := 0x00357793.
Lemma F_fd074 : fetch_word Asan.M.loaded_segments (0xfd230 : word) = Some W_fd074.
Proof. vm_refl. Qed.
Lemma D_fd074 : decode_any W_fd074 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd078 : bv 32 := 0xf2079ae3.
Lemma F_fd078 : fetch_word Asan.M.loaded_segments (0xfd234 : word) = Some W_fd078.
Proof. vm_refl. Qed.
Lemma D_fd078 : decode_any W_fd078 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd07c : bv 32 := 0x01000713.
Lemma F_fd07c : fetch_word Asan.M.loaded_segments (0xfd238 : word) = Some W_fd07c.
Proof. vm_refl. Qed.
Lemma D_fd07c : decode_any W_fd07c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd080 : bv 32 := 0x02e66c63.
Lemma F_fd080 : fetch_word Asan.M.loaded_segments (0xfd23c : word) = Some W_fd080.
Proof. vm_refl. Qed.
Lemma D_fd080 : decode_any W_fd080 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd084 : bv 32 := 0x00f00713.
Lemma F_fd084 : fetch_word Asan.M.loaded_segments (0xfd240 : word) = Some W_fd084.
Proof. vm_refl. Qed.
Lemma D_fd084 : decode_any W_fd084 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd088 : bv 32 := 0x0005a783.
Lemma F_fd088 : fetch_word Asan.M.loaded_segments (0xfd244 : word) = Some W_fd088.
Proof. vm_refl. Qed.
Lemma D_fd088 : decode_any W_fd088 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd08c : bv 32 := 0x0045a803.
Lemma F_fd08c : fetch_word Asan.M.loaded_segments (0xfd248 : word) = Some W_fd08c.
Proof. vm_refl. Qed.
Lemma D_fd08c : decode_any W_fd08c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd090 : bv 32 := 0x0085a883.
Lemma F_fd090 : fetch_word Asan.M.loaded_segments (0xfd24c : word) = Some W_fd090.
Proof. vm_refl. Qed.
Lemma D_fd090 : decode_any W_fd090 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd094 : bv 32 := 0x00c5a283.
Lemma F_fd094 : fetch_word Asan.M.loaded_segments (0xfd250 : word) = Some W_fd094.
Proof. vm_refl. Qed.
Lemma D_fd094 : decode_any W_fd094 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd098 : bv 32 := 0x01058593.
Lemma F_fd098 : fetch_word Asan.M.loaded_segments (0xfd254 : word) = Some W_fd098.
Proof. vm_refl. Qed.
Lemma D_fd098 : decode_any W_fd098 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd09c : bv 32 := 0xff060613.
Lemma F_fd09c : fetch_word Asan.M.loaded_segments (0xfd258 : word) = Some W_fd09c.
Proof. vm_refl. Qed.
Lemma D_fd09c : decode_any W_fd09c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0a0 : bv 32 := 0x00f6a023.
Lemma F_fd0a0 : fetch_word Asan.M.loaded_segments (0xfd25c : word) = Some W_fd0a0.
Proof. vm_refl. Qed.
Lemma D_fd0a0 : decode_any W_fd0a0 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0a4 : bv 32 := 0x0106a223.
Lemma F_fd0a4 : fetch_word Asan.M.loaded_segments (0xfd260 : word) = Some W_fd0a4.
Proof. vm_refl. Qed.
Lemma D_fd0a4 : decode_any W_fd0a4 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0a8 : bv 32 := 0x0116a423.
Lemma F_fd0a8 : fetch_word Asan.M.loaded_segments (0xfd264 : word) = Some W_fd0a8.
Proof. vm_refl. Qed.
Lemma D_fd0a8 : decode_any W_fd0a8 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0ac : bv 32 := 0x0056a623.
Lemma F_fd0ac : fetch_word Asan.M.loaded_segments (0xfd268 : word) = Some W_fd0ac.
Proof. vm_refl. Qed.
Lemma D_fd0ac : decode_any W_fd0ac = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0b0 : bv 32 := 0x01068693.
Lemma F_fd0b0 : fetch_word Asan.M.loaded_segments (0xfd26c : word) = Some W_fd0b0.
Proof. vm_refl. Qed.
Lemma D_fd0b0 : decode_any W_fd0b0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0b4 : bv 32 := 0xfcc76ae3.
Lemma F_fd0b4 : fetch_word Asan.M.loaded_segments (0xfd270 : word) = Some W_fd0b4.
Proof. vm_refl. Qed.
Lemma D_fd0b4 : decode_any W_fd0b4 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0b8 : bv 32 := 0x00800713.
Lemma F_fd0b8 : fetch_word Asan.M.loaded_segments (0xfd274 : word) = Some W_fd0b8.
Proof. vm_refl. Qed.
Lemma D_fd0b8 : decode_any W_fd0b8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0bc : bv 32 := 0x00e66e63.
Lemma F_fd0bc : fetch_word Asan.M.loaded_segments (0xfd278 : word) = Some W_fd0bc.
Proof. vm_refl. Qed.
Lemma D_fd0bc : decode_any W_fd0bc = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0c0 : bv 32 := 0x0005a703.
Lemma F_fd0c0 : fetch_word Asan.M.loaded_segments (0xfd27c : word) = Some W_fd0c0.
Proof. vm_refl. Qed.
Lemma D_fd0c0 : decode_any W_fd0c0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0c4 : bv 32 := 0x0045a783.
Lemma F_fd0c4 : fetch_word Asan.M.loaded_segments (0xfd280 : word) = Some W_fd0c4.
Proof. vm_refl. Qed.
Lemma D_fd0c4 : decode_any W_fd0c4 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0c8 : bv 32 := 0x00e6a023.
Lemma F_fd0c8 : fetch_word Asan.M.loaded_segments (0xfd284 : word) = Some W_fd0c8.
Proof. vm_refl. Qed.
Lemma D_fd0c8 : decode_any W_fd0c8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0cc : bv 32 := 0x00f6a223.
Lemma F_fd0cc : fetch_word Asan.M.loaded_segments (0xfd288 : word) = Some W_fd0cc.
Proof. vm_refl. Qed.
Lemma D_fd0cc : decode_any W_fd0cc = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0d0 : bv 32 := 0x00868693.
Lemma F_fd0d0 : fetch_word Asan.M.loaded_segments (0xfd28c : word) = Some W_fd0d0.
Proof. vm_refl. Qed.
Lemma D_fd0d0 : decode_any W_fd0d0 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0d4 : bv 32 := 0x00858593.
Lemma F_fd0d4 : fetch_word Asan.M.loaded_segments (0xfd290 : word) = Some W_fd0d4.
Proof. vm_refl. Qed.
Lemma D_fd0d4 : decode_any W_fd0d4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0d8 : bv 32 := 0x00467713.
Lemma F_fd0d8 : fetch_word Asan.M.loaded_segments (0xfd294 : word) = Some W_fd0d8.
Proof. vm_refl. Qed.
Lemma D_fd0d8 : decode_any W_fd0d8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0dc : bv 32 := 0x24070063.
Lemma F_fd0dc : fetch_word Asan.M.loaded_segments (0xfd298 : word) = Some W_fd0dc.
Proof. vm_refl. Qed.
Lemma D_fd0dc : decode_any W_fd0dc = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0e0 : bv 32 := 0x0005a703.
Lemma F_fd0e0 : fetch_word Asan.M.loaded_segments (0xfd29c : word) = Some W_fd0e0.
Proof. vm_refl. Qed.
Lemma D_fd0e0 : decode_any W_fd0e0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0e4 : bv 32 := 0x00458593.
Lemma F_fd0e4 : fetch_word Asan.M.loaded_segments (0xfd2a0 : word) = Some W_fd0e4.
Proof. vm_refl. Qed.
Lemma D_fd0e4 : decode_any W_fd0e4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0e8 : bv 32 := 0x00e6a023.
Lemma F_fd0e8 : fetch_word Asan.M.loaded_segments (0xfd2a4 : word) = Some W_fd0e8.
Proof. vm_refl. Qed.
Lemma D_fd0e8 : decode_any W_fd0e8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0ec : bv 32 := 0x00468693.
Lemma F_fd0ec : fetch_word Asan.M.loaded_segments (0xfd2a8 : word) = Some W_fd0ec.
Proof. vm_refl. Qed.
Lemma D_fd0ec : decode_any W_fd0ec = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0f0 : bv 32 := 0x22c0006f.
Lemma F_fd0f0 : fetch_word Asan.M.loaded_segments (0xfd2ac : word) = Some W_fd0f0.
Proof. vm_refl. Qed.
Lemma D_fd0f0 : decode_any W_fd0f0 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0f4 : bv 32 := 0x00e68023.
Lemma F_fd0f4 : fetch_word Asan.M.loaded_segments (0xfd2b0 : word) = Some W_fd0f4.
Proof. vm_refl. Qed.
Lemma D_fd0f4 : decode_any W_fd0f4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0f8 : bv 32 := 0x00168693.
Lemma F_fd0f8 : fetch_word Asan.M.loaded_segments (0xfd2b4 : word) = Some W_fd0f8.
Proof. vm_refl. Qed.
Lemma D_fd0f8 : decode_any W_fd0f8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd0fc : bv 32 := 0xfff60613.
Lemma F_fd0fc : fetch_word Asan.M.loaded_segments (0xfd2b8 : word) = Some W_fd0fc.
Proof. vm_refl. Qed.
Lemma D_fd0fc : decode_any W_fd0fc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd100 : bv 32 := 0x01058593.
Lemma F_fd100 : fetch_word Asan.M.loaded_segments (0xfd2bc : word) = Some W_fd100.
Proof. vm_refl. Qed.
Lemma D_fd100 : decode_any W_fd100 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd104 : bv 32 := 0x01200793.
Lemma F_fd104 : fetch_word Asan.M.loaded_segments (0xfd2c0 : word) = Some W_fd104.
Proof. vm_refl. Qed.
Lemma D_fd104 : decode_any W_fd104 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd108 : bv 32 := 0x0087581b.
Lemma F_fd108 : fetch_word Asan.M.loaded_segments (0xfd2c4 : word) = Some W_fd108.
Proof. vm_refl. Qed.
Lemma D_fd108 : decode_any W_fd108 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd10c : bv 32 := 0xff45a883.
Lemma F_fd10c : fetch_word Asan.M.loaded_segments (0xfd2c8 : word) = Some W_fd10c.
Proof. vm_refl. Qed.
Lemma D_fd10c : decode_any W_fd10c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd110 : bv 32 := 0xff85a283.
Lemma F_fd110 : fetch_word Asan.M.loaded_segments (0xfd2cc : word) = Some W_fd110.
Proof. vm_refl. Qed.
Lemma D_fd110 : decode_any W_fd110 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd114 : bv 32 := 0xffc5a303.
Lemma F_fd114 : fetch_word Asan.M.loaded_segments (0xfd2d0 : word) = Some W_fd114.
Proof. vm_refl. Qed.
Lemma D_fd114 : decode_any W_fd114 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd118 : bv 32 := 0x0005a703.
Lemma F_fd118 : fetch_word Asan.M.loaded_segments (0xfd2d4 : word) = Some W_fd118.
Proof. vm_refl. Qed.
Lemma D_fd118 : decode_any W_fd118 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd11c : bv 32 := 0x01889393.
Lemma F_fd11c : fetch_word Asan.M.loaded_segments (0xfd2d8 : word) = Some W_fd11c.
Proof. vm_refl. Qed.
Lemma D_fd11c : decode_any W_fd11c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd120 : bv 32 := 0x0088d89b.
Lemma F_fd120 : fetch_word Asan.M.loaded_segments (0xfd2dc : word) = Some W_fd120.
Proof. vm_refl. Qed.
Lemma D_fd120 : decode_any W_fd120 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd124 : bv 32 := 0x0103e833.
Lemma F_fd124 : fetch_word Asan.M.loaded_segments (0xfd2e0 : word) = Some W_fd124.
Proof. vm_refl. Qed.
Lemma D_fd124 : decode_any W_fd124 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd128 : bv 32 := 0x01829393.
Lemma F_fd128 : fetch_word Asan.M.loaded_segments (0xfd2e4 : word) = Some W_fd128.
Proof. vm_refl. Qed.
Lemma D_fd128 : decode_any W_fd128 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd12c : bv 32 := 0x0082d29b.
Lemma F_fd12c : fetch_word Asan.M.loaded_segments (0xfd2e8 : word) = Some W_fd12c.
Proof. vm_refl. Qed.
Lemma D_fd12c : decode_any W_fd12c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd130 : bv 32 := 0x0113e8b3.
Lemma F_fd130 : fetch_word Asan.M.loaded_segments (0xfd2ec : word) = Some W_fd130.
Proof. vm_refl. Qed.
Lemma D_fd130 : decode_any W_fd130 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd134 : bv 32 := 0x01831393.
Lemma F_fd134 : fetch_word Asan.M.loaded_segments (0xfd2f0 : word) = Some W_fd134.
Proof. vm_refl. Qed.
Lemma D_fd134 : decode_any W_fd134 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd138 : bv 32 := 0x0083531b.
Lemma F_fd138 : fetch_word Asan.M.loaded_segments (0xfd2f4 : word) = Some W_fd138.
Proof. vm_refl. Qed.
Lemma D_fd138 : decode_any W_fd138 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd13c : bv 32 := 0x0053e2b3.
Lemma F_fd13c : fetch_word Asan.M.loaded_segments (0xfd2f8 : word) = Some W_fd13c.
Proof. vm_refl. Qed.
Lemma D_fd13c : decode_any W_fd13c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd140 : bv 32 := 0x01871393.
Lemma F_fd140 : fetch_word Asan.M.loaded_segments (0xfd2fc : word) = Some W_fd140.
Proof. vm_refl. Qed.
Lemma D_fd140 : decode_any W_fd140 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd144 : bv 32 := 0x0063e333.
Lemma F_fd144 : fetch_word Asan.M.loaded_segments (0xfd300 : word) = Some W_fd144.
Proof. vm_refl. Qed.
Lemma D_fd144 : decode_any W_fd144 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd148 : bv 32 := 0xff060613.
Lemma F_fd148 : fetch_word Asan.M.loaded_segments (0xfd304 : word) = Some W_fd148.
Proof. vm_refl. Qed.
Lemma D_fd148 : decode_any W_fd148 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd14c : bv 32 := 0x0106a023.
Lemma F_fd14c : fetch_word Asan.M.loaded_segments (0xfd308 : word) = Some W_fd14c.
Proof. vm_refl. Qed.
Lemma D_fd14c : decode_any W_fd14c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd150 : bv 32 := 0x0116a223.
Lemma F_fd150 : fetch_word Asan.M.loaded_segments (0xfd30c : word) = Some W_fd150.
Proof. vm_refl. Qed.
Lemma D_fd150 : decode_any W_fd150 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd154 : bv 32 := 0x0056a423.
Lemma F_fd154 : fetch_word Asan.M.loaded_segments (0xfd310 : word) = Some W_fd154.
Proof. vm_refl. Qed.
Lemma D_fd154 : decode_any W_fd154 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd158 : bv 32 := 0x0066a623.
Lemma F_fd158 : fetch_word Asan.M.loaded_segments (0xfd314 : word) = Some W_fd158.
Proof. vm_refl. Qed.
Lemma D_fd158 : decode_any W_fd158 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd15c : bv 32 := 0x01068693.
Lemma F_fd15c : fetch_word Asan.M.loaded_segments (0xfd318 : word) = Some W_fd15c.
Proof. vm_refl. Qed.
Lemma D_fd15c : decode_any W_fd15c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd160 : bv 32 := 0x01058593.
Lemma F_fd160 : fetch_word Asan.M.loaded_segments (0xfd31c : word) = Some W_fd160.
Proof. vm_refl. Qed.
Lemma D_fd160 : decode_any W_fd160 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd164 : bv 32 := 0xfac7e2e3.
Lemma F_fd164 : fetch_word Asan.M.loaded_segments (0xfd320 : word) = Some W_fd164.
Proof. vm_refl. Qed.
Lemma D_fd164 : decode_any W_fd164 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd168 : bv 32 := 0xff158593.
Lemma F_fd168 : fetch_word Asan.M.loaded_segments (0xfd324 : word) = Some W_fd168.
Proof. vm_refl. Qed.
Lemma D_fd168 : decode_any W_fd168 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd16c : bv 32 := 0x01000713.
Lemma F_fd16c : fetch_word Asan.M.loaded_segments (0xfd328 : word) = Some W_fd16c.
Proof. vm_refl. Qed.
Lemma D_fd16c : decode_any W_fd16c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd170 : bv 32 := 0xe4e666e3.
Lemma F_fd170 : fetch_word Asan.M.loaded_segments (0xfd32c : word) = Some W_fd170.
Proof. vm_refl. Qed.
Lemma D_fd170 : decode_any W_fd170 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd174 : bv 32 := 0x0940006f.
Lemma F_fd174 : fetch_word Asan.M.loaded_segments (0xfd330 : word) = Some W_fd174.
Proof. vm_refl. Qed.
Lemma D_fd174 : decode_any W_fd174 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd178 : bv 32 := 0x00875793.
Lemma F_fd178 : fetch_word Asan.M.loaded_segments (0xfd334 : word) = Some W_fd178.
Proof. vm_refl. Qed.
Lemma D_fd178 : decode_any W_fd178 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd17c : bv 32 := 0x01075813.
Lemma F_fd17c : fetch_word Asan.M.loaded_segments (0xfd338 : word) = Some W_fd17c.
Proof. vm_refl. Qed.
Lemma D_fd17c : decode_any W_fd17c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd180 : bv 32 := 0xffd60613.
Lemma F_fd180 : fetch_word Asan.M.loaded_segments (0xfd33c : word) = Some W_fd180.
Proof. vm_refl. Qed.
Lemma D_fd180 : decode_any W_fd180 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd184 : bv 32 := 0x00e68023.
Lemma F_fd184 : fetch_word Asan.M.loaded_segments (0xfd340 : word) = Some W_fd184.
Proof. vm_refl. Qed.
Lemma D_fd184 : decode_any W_fd184 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd188 : bv 32 := 0x00f680a3.
Lemma F_fd188 : fetch_word Asan.M.loaded_segments (0xfd344 : word) = Some W_fd188.
Proof. vm_refl. Qed.
Lemma D_fd188 : decode_any W_fd188 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd18c : bv 32 := 0x01068123.
Lemma F_fd18c : fetch_word Asan.M.loaded_segments (0xfd348 : word) = Some W_fd18c.
Proof. vm_refl. Qed.
Lemma D_fd18c : decode_any W_fd18c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd190 : bv 32 := 0x00368693.
Lemma F_fd190 : fetch_word Asan.M.loaded_segments (0xfd34c : word) = Some W_fd190.
Proof. vm_refl. Qed.
Lemma D_fd190 : decode_any W_fd190 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd194 : bv 32 := 0x01058593.
Lemma F_fd194 : fetch_word Asan.M.loaded_segments (0xfd350 : word) = Some W_fd194.
Proof. vm_refl. Qed.
Lemma D_fd194 : decode_any W_fd194 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd198 : bv 32 := 0x01000793.
Lemma F_fd198 : fetch_word Asan.M.loaded_segments (0xfd354 : word) = Some W_fd198.
Proof. vm_refl. Qed.
Lemma D_fd198 : decode_any W_fd198 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd19c : bv 32 := 0x0187581b.
Lemma F_fd19c : fetch_word Asan.M.loaded_segments (0xfd358 : word) = Some W_fd19c.
Proof. vm_refl. Qed.
Lemma D_fd19c : decode_any W_fd19c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1a0 : bv 32 := 0xff45a883.
Lemma F_fd1a0 : fetch_word Asan.M.loaded_segments (0xfd35c : word) = Some W_fd1a0.
Proof. vm_refl. Qed.
Lemma D_fd1a0 : decode_any W_fd1a0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1a4 : bv 32 := 0xff85a283.
Lemma F_fd1a4 : fetch_word Asan.M.loaded_segments (0xfd360 : word) = Some W_fd1a4.
Proof. vm_refl. Qed.
Lemma D_fd1a4 : decode_any W_fd1a4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1a8 : bv 32 := 0xffc5a303.
Lemma F_fd1a8 : fetch_word Asan.M.loaded_segments (0xfd364 : word) = Some W_fd1a8.
Proof. vm_refl. Qed.
Lemma D_fd1a8 : decode_any W_fd1a8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1ac : bv 32 := 0x0005a703.
Lemma F_fd1ac : fetch_word Asan.M.loaded_segments (0xfd368 : word) = Some W_fd1ac.
Proof. vm_refl. Qed.
Lemma D_fd1ac : decode_any W_fd1ac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1b0 : bv 32 := 0x00889393.
Lemma F_fd1b0 : fetch_word Asan.M.loaded_segments (0xfd36c : word) = Some W_fd1b0.
Proof. vm_refl. Qed.
Lemma D_fd1b0 : decode_any W_fd1b0 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1b4 : bv 32 := 0x0188d89b.
Lemma F_fd1b4 : fetch_word Asan.M.loaded_segments (0xfd370 : word) = Some W_fd1b4.
Proof. vm_refl. Qed.
Lemma D_fd1b4 : decode_any W_fd1b4 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1b8 : bv 32 := 0x0103e833.
Lemma F_fd1b8 : fetch_word Asan.M.loaded_segments (0xfd374 : word) = Some W_fd1b8.
Proof. vm_refl. Qed.
Lemma D_fd1b8 : decode_any W_fd1b8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1bc : bv 32 := 0x00829393.
Lemma F_fd1bc : fetch_word Asan.M.loaded_segments (0xfd378 : word) = Some W_fd1bc.
Proof. vm_refl. Qed.
Lemma D_fd1bc : decode_any W_fd1bc = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1c0 : bv 32 := 0x0182d29b.
Lemma F_fd1c0 : fetch_word Asan.M.loaded_segments (0xfd37c : word) = Some W_fd1c0.
Proof. vm_refl. Qed.
Lemma D_fd1c0 : decode_any W_fd1c0 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1c4 : bv 32 := 0x0113e8b3.
Lemma F_fd1c4 : fetch_word Asan.M.loaded_segments (0xfd380 : word) = Some W_fd1c4.
Proof. vm_refl. Qed.
Lemma D_fd1c4 : decode_any W_fd1c4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1c8 : bv 32 := 0x00831393.
Lemma F_fd1c8 : fetch_word Asan.M.loaded_segments (0xfd384 : word) = Some W_fd1c8.
Proof. vm_refl. Qed.
Lemma D_fd1c8 : decode_any W_fd1c8 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1cc : bv 32 := 0x0183531b.
Lemma F_fd1cc : fetch_word Asan.M.loaded_segments (0xfd388 : word) = Some W_fd1cc.
Proof. vm_refl. Qed.
Lemma D_fd1cc : decode_any W_fd1cc = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1d0 : bv 32 := 0x0053e2b3.
Lemma F_fd1d0 : fetch_word Asan.M.loaded_segments (0xfd38c : word) = Some W_fd1d0.
Proof. vm_refl. Qed.
Lemma D_fd1d0 : decode_any W_fd1d0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1d4 : bv 32 := 0x00871393.
Lemma F_fd1d4 : fetch_word Asan.M.loaded_segments (0xfd390 : word) = Some W_fd1d4.
Proof. vm_refl. Qed.
Lemma D_fd1d4 : decode_any W_fd1d4 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1d8 : bv 32 := 0x0063e333.
Lemma F_fd1d8 : fetch_word Asan.M.loaded_segments (0xfd394 : word) = Some W_fd1d8.
Proof. vm_refl. Qed.
Lemma D_fd1d8 : decode_any W_fd1d8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1dc : bv 32 := 0xff060613.
Lemma F_fd1dc : fetch_word Asan.M.loaded_segments (0xfd398 : word) = Some W_fd1dc.
Proof. vm_refl. Qed.
Lemma D_fd1dc : decode_any W_fd1dc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1e0 : bv 32 := 0x0106a023.
Lemma F_fd1e0 : fetch_word Asan.M.loaded_segments (0xfd39c : word) = Some W_fd1e0.
Proof. vm_refl. Qed.
Lemma D_fd1e0 : decode_any W_fd1e0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1e4 : bv 32 := 0x0116a223.
Lemma F_fd1e4 : fetch_word Asan.M.loaded_segments (0xfd3a0 : word) = Some W_fd1e4.
Proof. vm_refl. Qed.
Lemma D_fd1e4 : decode_any W_fd1e4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1e8 : bv 32 := 0x0056a423.
Lemma F_fd1e8 : fetch_word Asan.M.loaded_segments (0xfd3a4 : word) = Some W_fd1e8.
Proof. vm_refl. Qed.
Lemma D_fd1e8 : decode_any W_fd1e8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1ec : bv 32 := 0x0066a623.
Lemma F_fd1ec : fetch_word Asan.M.loaded_segments (0xfd3a8 : word) = Some W_fd1ec.
Proof. vm_refl. Qed.
Lemma D_fd1ec : decode_any W_fd1ec = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1f0 : bv 32 := 0x01068693.
Lemma F_fd1f0 : fetch_word Asan.M.loaded_segments (0xfd3ac : word) = Some W_fd1f0.
Proof. vm_refl. Qed.
Lemma D_fd1f0 : decode_any W_fd1f0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1f4 : bv 32 := 0x01058593.
Lemma F_fd1f4 : fetch_word Asan.M.loaded_segments (0xfd3b0 : word) = Some W_fd1f4.
Proof. vm_refl. Qed.
Lemma D_fd1f4 : decode_any W_fd1f4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1f8 : bv 32 := 0xfac7e2e3.
Lemma F_fd1f8 : fetch_word Asan.M.loaded_segments (0xfd3b4 : word) = Some W_fd1f8.
Proof. vm_refl. Qed.
Lemma D_fd1f8 : decode_any W_fd1f8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd1fc : bv 32 := 0xff358593.
Lemma F_fd1fc : fetch_word Asan.M.loaded_segments (0xfd3b8 : word) = Some W_fd1fc.
Proof. vm_refl. Qed.
Lemma D_fd1fc : decode_any W_fd1fc = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd200 : bv 32 := 0x01000713.
Lemma F_fd200 : fetch_word Asan.M.loaded_segments (0xfd3bc : word) = Some W_fd200.
Proof. vm_refl. Qed.
Lemma D_fd200 : decode_any W_fd200 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd204 : bv 32 := 0xdae66ce3.
Lemma F_fd204 : fetch_word Asan.M.loaded_segments (0xfd3c0 : word) = Some W_fd204.
Proof. vm_refl. Qed.
Lemma D_fd204 : decode_any W_fd204 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd208 : bv 32 := 0x0005c703.
Lemma F_fd208 : fetch_word Asan.M.loaded_segments (0xfd3c4 : word) = Some W_fd208.
Proof. vm_refl. Qed.
Lemma D_fd208 : decode_any W_fd208 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd20c : bv 32 := 0x0015c783.
Lemma F_fd20c : fetch_word Asan.M.loaded_segments (0xfd3c8 : word) = Some W_fd20c.
Proof. vm_refl. Qed.
Lemma D_fd20c : decode_any W_fd20c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd210 : bv 32 := 0x0025c803.
Lemma F_fd210 : fetch_word Asan.M.loaded_segments (0xfd3cc : word) = Some W_fd210.
Proof. vm_refl. Qed.
Lemma D_fd210 : decode_any W_fd210 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd214 : bv 32 := 0x0035c883.
Lemma F_fd214 : fetch_word Asan.M.loaded_segments (0xfd3d0 : word) = Some W_fd214.
Proof. vm_refl. Qed.
Lemma D_fd214 : decode_any W_fd214 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd218 : bv 32 := 0x0045c283.
Lemma F_fd218 : fetch_word Asan.M.loaded_segments (0xfd3d4 : word) = Some W_fd218.
Proof. vm_refl. Qed.
Lemma D_fd218 : decode_any W_fd218 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd21c : bv 32 := 0x0055c303.
Lemma F_fd21c : fetch_word Asan.M.loaded_segments (0xfd3d8 : word) = Some W_fd21c.
Proof. vm_refl. Qed.
Lemma D_fd21c : decode_any W_fd21c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd220 : bv 32 := 0x0065c383.
Lemma F_fd220 : fetch_word Asan.M.loaded_segments (0xfd3dc : word) = Some W_fd220.
Proof. vm_refl. Qed.
Lemma D_fd220 : decode_any W_fd220 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd224 : bv 32 := 0x0075ce03.
Lemma F_fd224 : fetch_word Asan.M.loaded_segments (0xfd3e0 : word) = Some W_fd224.
Proof. vm_refl. Qed.
Lemma D_fd224 : decode_any W_fd224 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd228 : bv 32 := 0x00e68023.
Lemma F_fd228 : fetch_word Asan.M.loaded_segments (0xfd3e4 : word) = Some W_fd228.
Proof. vm_refl. Qed.
Lemma D_fd228 : decode_any W_fd228 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd22c : bv 32 := 0x00f680a3.
Lemma F_fd22c : fetch_word Asan.M.loaded_segments (0xfd3e8 : word) = Some W_fd22c.
Proof. vm_refl. Qed.
Lemma D_fd22c : decode_any W_fd22c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd230 : bv 32 := 0x01068123.
Lemma F_fd230 : fetch_word Asan.M.loaded_segments (0xfd3ec : word) = Some W_fd230.
Proof. vm_refl. Qed.
Lemma D_fd230 : decode_any W_fd230 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd234 : bv 32 := 0x011681a3.
Lemma F_fd234 : fetch_word Asan.M.loaded_segments (0xfd3f0 : word) = Some W_fd234.
Proof. vm_refl. Qed.
Lemma D_fd234 : decode_any W_fd234 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd238 : bv 32 := 0x0085c703.
Lemma F_fd238 : fetch_word Asan.M.loaded_segments (0xfd3f4 : word) = Some W_fd238.
Proof. vm_refl. Qed.
Lemma D_fd238 : decode_any W_fd238 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd23c : bv 32 := 0x0095c783.
Lemma F_fd23c : fetch_word Asan.M.loaded_segments (0xfd3f8 : word) = Some W_fd23c.
Proof. vm_refl. Qed.
Lemma D_fd23c : decode_any W_fd23c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd240 : bv 32 := 0x00a5c803.
Lemma F_fd240 : fetch_word Asan.M.loaded_segments (0xfd3fc : word) = Some W_fd240.
Proof. vm_refl. Qed.
Lemma D_fd240 : decode_any W_fd240 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd244 : bv 32 := 0x00b5c883.
Lemma F_fd244 : fetch_word Asan.M.loaded_segments (0xfd400 : word) = Some W_fd244.
Proof. vm_refl. Qed.
Lemma D_fd244 : decode_any W_fd244 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd248 : bv 32 := 0x00568223.
Lemma F_fd248 : fetch_word Asan.M.loaded_segments (0xfd404 : word) = Some W_fd248.
Proof. vm_refl. Qed.
Lemma D_fd248 : decode_any W_fd248 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd24c : bv 32 := 0x006682a3.
Lemma F_fd24c : fetch_word Asan.M.loaded_segments (0xfd408 : word) = Some W_fd24c.
Proof. vm_refl. Qed.
Lemma D_fd24c : decode_any W_fd24c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd250 : bv 32 := 0x00768323.
Lemma F_fd250 : fetch_word Asan.M.loaded_segments (0xfd40c : word) = Some W_fd250.
Proof. vm_refl. Qed.
Lemma D_fd250 : decode_any W_fd250 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd254 : bv 32 := 0x01c683a3.
Lemma F_fd254 : fetch_word Asan.M.loaded_segments (0xfd410 : word) = Some W_fd254.
Proof. vm_refl. Qed.
Lemma D_fd254 : decode_any W_fd254 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd258 : bv 32 := 0x00c5c283.
Lemma F_fd258 : fetch_word Asan.M.loaded_segments (0xfd414 : word) = Some W_fd258.
Proof. vm_refl. Qed.
Lemma D_fd258 : decode_any W_fd258 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd25c : bv 32 := 0x00d5c303.
Lemma F_fd25c : fetch_word Asan.M.loaded_segments (0xfd418 : word) = Some W_fd25c.
Proof. vm_refl. Qed.
Lemma D_fd25c : decode_any W_fd25c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd260 : bv 32 := 0x00e5c383.
Lemma F_fd260 : fetch_word Asan.M.loaded_segments (0xfd41c : word) = Some W_fd260.
Proof. vm_refl. Qed.
Lemma D_fd260 : decode_any W_fd260 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd264 : bv 32 := 0x00f5ce03.
Lemma F_fd264 : fetch_word Asan.M.loaded_segments (0xfd420 : word) = Some W_fd264.
Proof. vm_refl. Qed.
Lemma D_fd264 : decode_any W_fd264 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd268 : bv 32 := 0x01058593.
Lemma F_fd268 : fetch_word Asan.M.loaded_segments (0xfd424 : word) = Some W_fd268.
Proof. vm_refl. Qed.
Lemma D_fd268 : decode_any W_fd268 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd26c : bv 32 := 0x00e68423.
Lemma F_fd26c : fetch_word Asan.M.loaded_segments (0xfd428 : word) = Some W_fd26c.
Proof. vm_refl. Qed.
Lemma D_fd26c : decode_any W_fd26c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd270 : bv 32 := 0x00f684a3.
Lemma F_fd270 : fetch_word Asan.M.loaded_segments (0xfd42c : word) = Some W_fd270.
Proof. vm_refl. Qed.
Lemma D_fd270 : decode_any W_fd270 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd274 : bv 32 := 0x01068523.
Lemma F_fd274 : fetch_word Asan.M.loaded_segments (0xfd430 : word) = Some W_fd274.
Proof. vm_refl. Qed.
Lemma D_fd274 : decode_any W_fd274 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd278 : bv 32 := 0x011685a3.
Lemma F_fd278 : fetch_word Asan.M.loaded_segments (0xfd434 : word) = Some W_fd278.
Proof. vm_refl. Qed.
Lemma D_fd278 : decode_any W_fd278 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd27c : bv 32 := 0x01068713.
Lemma F_fd27c : fetch_word Asan.M.loaded_segments (0xfd438 : word) = Some W_fd27c.
Proof. vm_refl. Qed.
Lemma D_fd27c : decode_any W_fd27c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd280 : bv 32 := 0x00568623.
Lemma F_fd280 : fetch_word Asan.M.loaded_segments (0xfd43c : word) = Some W_fd280.
Proof. vm_refl. Qed.
Lemma D_fd280 : decode_any W_fd280 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd284 : bv 32 := 0x006686a3.
Lemma F_fd284 : fetch_word Asan.M.loaded_segments (0xfd440 : word) = Some W_fd284.
Proof. vm_refl. Qed.
Lemma D_fd284 : decode_any W_fd284 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd288 : bv 32 := 0x00768723.
Lemma F_fd288 : fetch_word Asan.M.loaded_segments (0xfd444 : word) = Some W_fd288.
Proof. vm_refl. Qed.
Lemma D_fd288 : decode_any W_fd288 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd28c : bv 32 := 0x01c687a3.
Lemma F_fd28c : fetch_word Asan.M.loaded_segments (0xfd448 : word) = Some W_fd28c.
Proof. vm_refl. Qed.
Lemma D_fd28c : decode_any W_fd28c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd290 : bv 32 := 0x00070693.
Lemma F_fd290 : fetch_word Asan.M.loaded_segments (0xfd44c : word) = Some W_fd290.
Proof. vm_refl. Qed.
Lemma D_fd290 : decode_any W_fd290 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd294 : bv 32 := 0x00867713.
Lemma F_fd294 : fetch_word Asan.M.loaded_segments (0xfd450 : word) = Some W_fd294.
Proof. vm_refl. Qed.
Lemma D_fd294 : decode_any W_fd294 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd298 : bv 32 := 0xd20706e3.
Lemma F_fd298 : fetch_word Asan.M.loaded_segments (0xfd454 : word) = Some W_fd298.
Proof. vm_refl. Qed.
Lemma D_fd298 : decode_any W_fd298 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd29c : bv 32 := 0x0005c703.
Lemma F_fd29c : fetch_word Asan.M.loaded_segments (0xfd458 : word) = Some W_fd29c.
Proof. vm_refl. Qed.
Lemma D_fd29c : decode_any W_fd29c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2a0 : bv 32 := 0x0015c783.
Lemma F_fd2a0 : fetch_word Asan.M.loaded_segments (0xfd45c : word) = Some W_fd2a0.
Proof. vm_refl. Qed.
Lemma D_fd2a0 : decode_any W_fd2a0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2a4 : bv 32 := 0x0025c803.
Lemma F_fd2a4 : fetch_word Asan.M.loaded_segments (0xfd460 : word) = Some W_fd2a4.
Proof. vm_refl. Qed.
Lemma D_fd2a4 : decode_any W_fd2a4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2a8 : bv 32 := 0x0035c883.
Lemma F_fd2a8 : fetch_word Asan.M.loaded_segments (0xfd464 : word) = Some W_fd2a8.
Proof. vm_refl. Qed.
Lemma D_fd2a8 : decode_any W_fd2a8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2ac : bv 32 := 0x0045c283.
Lemma F_fd2ac : fetch_word Asan.M.loaded_segments (0xfd468 : word) = Some W_fd2ac.
Proof. vm_refl. Qed.
Lemma D_fd2ac : decode_any W_fd2ac = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2b0 : bv 32 := 0x0055c303.
Lemma F_fd2b0 : fetch_word Asan.M.loaded_segments (0xfd46c : word) = Some W_fd2b0.
Proof. vm_refl. Qed.
Lemma D_fd2b0 : decode_any W_fd2b0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2b4 : bv 32 := 0x0065c383.
Lemma F_fd2b4 : fetch_word Asan.M.loaded_segments (0xfd470 : word) = Some W_fd2b4.
Proof. vm_refl. Qed.
Lemma D_fd2b4 : decode_any W_fd2b4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2b8 : bv 32 := 0x0075ce03.
Lemma F_fd2b8 : fetch_word Asan.M.loaded_segments (0xfd474 : word) = Some W_fd2b8.
Proof. vm_refl. Qed.
Lemma D_fd2b8 : decode_any W_fd2b8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2bc : bv 32 := 0x00858593.
Lemma F_fd2bc : fetch_word Asan.M.loaded_segments (0xfd478 : word) = Some W_fd2bc.
Proof. vm_refl. Qed.
Lemma D_fd2bc : decode_any W_fd2bc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2c0 : bv 32 := 0x00e68023.
Lemma F_fd2c0 : fetch_word Asan.M.loaded_segments (0xfd47c : word) = Some W_fd2c0.
Proof. vm_refl. Qed.
Lemma D_fd2c0 : decode_any W_fd2c0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2c4 : bv 32 := 0x00f680a3.
Lemma F_fd2c4 : fetch_word Asan.M.loaded_segments (0xfd480 : word) = Some W_fd2c4.
Proof. vm_refl. Qed.
Lemma D_fd2c4 : decode_any W_fd2c4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2c8 : bv 32 := 0x01068123.
Lemma F_fd2c8 : fetch_word Asan.M.loaded_segments (0xfd484 : word) = Some W_fd2c8.
Proof. vm_refl. Qed.
Lemma D_fd2c8 : decode_any W_fd2c8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2cc : bv 32 := 0x011681a3.
Lemma F_fd2cc : fetch_word Asan.M.loaded_segments (0xfd488 : word) = Some W_fd2cc.
Proof. vm_refl. Qed.
Lemma D_fd2cc : decode_any W_fd2cc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2d0 : bv 32 := 0x00868713.
Lemma F_fd2d0 : fetch_word Asan.M.loaded_segments (0xfd48c : word) = Some W_fd2d0.
Proof. vm_refl. Qed.
Lemma D_fd2d0 : decode_any W_fd2d0 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2d4 : bv 32 := 0x00568223.
Lemma F_fd2d4 : fetch_word Asan.M.loaded_segments (0xfd490 : word) = Some W_fd2d4.
Proof. vm_refl. Qed.
Lemma D_fd2d4 : decode_any W_fd2d4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2d8 : bv 32 := 0x006682a3.
Lemma F_fd2d8 : fetch_word Asan.M.loaded_segments (0xfd494 : word) = Some W_fd2d8.
Proof. vm_refl. Qed.
Lemma D_fd2d8 : decode_any W_fd2d8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2dc : bv 32 := 0x00768323.
Lemma F_fd2dc : fetch_word Asan.M.loaded_segments (0xfd498 : word) = Some W_fd2dc.
Proof. vm_refl. Qed.
Lemma D_fd2dc : decode_any W_fd2dc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2e0 : bv 32 := 0x01c683a3.
Lemma F_fd2e0 : fetch_word Asan.M.loaded_segments (0xfd49c : word) = Some W_fd2e0.
Proof. vm_refl. Qed.
Lemma D_fd2e0 : decode_any W_fd2e0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2e4 : bv 32 := 0x00070693.
Lemma F_fd2e4 : fetch_word Asan.M.loaded_segments (0xfd4a0 : word) = Some W_fd2e4.
Proof. vm_refl. Qed.
Lemma D_fd2e4 : decode_any W_fd2e4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2e8 : bv 32 := 0x00467713.
Lemma F_fd2e8 : fetch_word Asan.M.loaded_segments (0xfd4a4 : word) = Some W_fd2e8.
Proof. vm_refl. Qed.
Lemma D_fd2e8 : decode_any W_fd2e8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2ec : bv 32 := 0x02070863.
Lemma F_fd2ec : fetch_word Asan.M.loaded_segments (0xfd4a8 : word) = Some W_fd2ec.
Proof. vm_refl. Qed.
Lemma D_fd2ec : decode_any W_fd2ec = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2f0 : bv 32 := 0x0005c703.
Lemma F_fd2f0 : fetch_word Asan.M.loaded_segments (0xfd4ac : word) = Some W_fd2f0.
Proof. vm_refl. Qed.
Lemma D_fd2f0 : decode_any W_fd2f0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2f4 : bv 32 := 0x0015c783.
Lemma F_fd2f4 : fetch_word Asan.M.loaded_segments (0xfd4b0 : word) = Some W_fd2f4.
Proof. vm_refl. Qed.
Lemma D_fd2f4 : decode_any W_fd2f4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2f8 : bv 32 := 0x0025c803.
Lemma F_fd2f8 : fetch_word Asan.M.loaded_segments (0xfd4b4 : word) = Some W_fd2f8.
Proof. vm_refl. Qed.
Lemma D_fd2f8 : decode_any W_fd2f8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd2fc : bv 32 := 0x0035c883.
Lemma F_fd2fc : fetch_word Asan.M.loaded_segments (0xfd4b8 : word) = Some W_fd2fc.
Proof. vm_refl. Qed.
Lemma D_fd2fc : decode_any W_fd2fc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd300 : bv 32 := 0x00458593.
Lemma F_fd300 : fetch_word Asan.M.loaded_segments (0xfd4bc : word) = Some W_fd300.
Proof. vm_refl. Qed.
Lemma D_fd300 : decode_any W_fd300 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd304 : bv 32 := 0x00468293.
Lemma F_fd304 : fetch_word Asan.M.loaded_segments (0xfd4c0 : word) = Some W_fd304.
Proof. vm_refl. Qed.
Lemma D_fd304 : decode_any W_fd304 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd308 : bv 32 := 0x00e68023.
Lemma F_fd308 : fetch_word Asan.M.loaded_segments (0xfd4c4 : word) = Some W_fd308.
Proof. vm_refl. Qed.
Lemma D_fd308 : decode_any W_fd308 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd30c : bv 32 := 0x00f680a3.
Lemma F_fd30c : fetch_word Asan.M.loaded_segments (0xfd4c8 : word) = Some W_fd30c.
Proof. vm_refl. Qed.
Lemma D_fd30c : decode_any W_fd30c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd310 : bv 32 := 0x01068123.
Lemma F_fd310 : fetch_word Asan.M.loaded_segments (0xfd4cc : word) = Some W_fd310.
Proof. vm_refl. Qed.
Lemma D_fd310 : decode_any W_fd310 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd314 : bv 32 := 0x011681a3.
Lemma F_fd314 : fetch_word Asan.M.loaded_segments (0xfd4d0 : word) = Some W_fd314.
Proof. vm_refl. Qed.
Lemma D_fd314 : decode_any W_fd314 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd318 : bv 32 := 0x00028693.
Lemma F_fd318 : fetch_word Asan.M.loaded_segments (0xfd4d4 : word) = Some W_fd318.
Proof. vm_refl. Qed.
Lemma D_fd318 : decode_any W_fd318 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd31c : bv 32 := 0x00267713.
Lemma F_fd31c : fetch_word Asan.M.loaded_segments (0xfd4d8 : word) = Some W_fd31c.
Proof. vm_refl. Qed.
Lemma D_fd31c : decode_any W_fd31c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd320 : bv 32 := 0x00071863.
Lemma F_fd320 : fetch_word Asan.M.loaded_segments (0xfd4dc : word) = Some W_fd320.
Proof. vm_refl. Qed.
Lemma D_fd320 : decode_any W_fd320 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd324 : bv 32 := 0x00167613.
Lemma F_fd324 : fetch_word Asan.M.loaded_segments (0xfd4e0 : word) = Some W_fd324.
Proof. vm_refl. Qed.
Lemma D_fd324 : decode_any W_fd324 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd328 : bv 32 := 0x02061663.
Lemma F_fd328 : fetch_word Asan.M.loaded_segments (0xfd4e4 : word) = Some W_fd328.
Proof. vm_refl. Qed.
Lemma D_fd328 : decode_any W_fd328 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd32c : bv 32 := 0x00008067.
Lemma F_fd32c : fetch_word Asan.M.loaded_segments (0xfd4e8 : word) = Some W_fd32c.
Proof. vm_refl. Qed.
Lemma D_fd32c : decode_any W_fd32c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd330 : bv 32 := 0x0005c703.
Lemma F_fd330 : fetch_word Asan.M.loaded_segments (0xfd4ec : word) = Some W_fd330.
Proof. vm_refl. Qed.
Lemma D_fd330 : decode_any W_fd330 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd334 : bv 32 := 0x0015c783.
Lemma F_fd334 : fetch_word Asan.M.loaded_segments (0xfd4f0 : word) = Some W_fd334.
Proof. vm_refl. Qed.
Lemma D_fd334 : decode_any W_fd334 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd338 : bv 32 := 0x00258593.
Lemma F_fd338 : fetch_word Asan.M.loaded_segments (0xfd4f4 : word) = Some W_fd338.
Proof. vm_refl. Qed.
Lemma D_fd338 : decode_any W_fd338 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd33c : bv 32 := 0x00268813.
Lemma F_fd33c : fetch_word Asan.M.loaded_segments (0xfd4f8 : word) = Some W_fd33c.
Proof. vm_refl. Qed.
Lemma D_fd33c : decode_any W_fd33c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd340 : bv 32 := 0x00e68023.
Lemma F_fd340 : fetch_word Asan.M.loaded_segments (0xfd4fc : word) = Some W_fd340.
Proof. vm_refl. Qed.
Lemma D_fd340 : decode_any W_fd340 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd344 : bv 32 := 0x00f680a3.
Lemma F_fd344 : fetch_word Asan.M.loaded_segments (0xfd500 : word) = Some W_fd344.
Proof. vm_refl. Qed.
Lemma D_fd344 : decode_any W_fd344 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd348 : bv 32 := 0x00080693.
Lemma F_fd348 : fetch_word Asan.M.loaded_segments (0xfd504 : word) = Some W_fd348.
Proof. vm_refl. Qed.
Lemma D_fd348 : decode_any W_fd348 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd34c : bv 32 := 0x00167613.
Lemma F_fd34c : fetch_word Asan.M.loaded_segments (0xfd508 : word) = Some W_fd34c.
Proof. vm_refl. Qed.
Lemma D_fd34c : decode_any W_fd34c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd350 : bv 32 := 0xfc060ee3.
Lemma F_fd350 : fetch_word Asan.M.loaded_segments (0xfd50c : word) = Some W_fd350.
Proof. vm_refl. Qed.
Lemma D_fd350 : decode_any W_fd350 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd354 : bv 32 := 0x0005c583.
Lemma F_fd354 : fetch_word Asan.M.loaded_segments (0xfd510 : word) = Some W_fd354.
Proof. vm_refl. Qed.
Lemma D_fd354 : decode_any W_fd354 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd358 : bv 32 := 0x00b68023.
Lemma F_fd358 : fetch_word Asan.M.loaded_segments (0xfd514 : word) = Some W_fd358.
Proof. vm_refl. Qed.
Lemma D_fd358 : decode_any W_fd358 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd35c : bv 32 := 0x00008067.
Lemma F_fd35c : fetch_word Asan.M.loaded_segments (0xfd518 : word) = Some W_fd35c.
Proof. vm_refl. Qed.
Lemma D_fd35c : decode_any W_fd35c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
