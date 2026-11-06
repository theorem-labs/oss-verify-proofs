(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_542bc : bv 32 := 0x81010113.
Lemma F_542bc : fetch_word AsanUbsan.M.loaded_segments (0x542bc : word) = Some W_542bc.
Proof. vm_refl. Qed.
Lemma D_542bc : decode_any W_542bc = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542c0 : bv 32 := 0x7e113423.
Lemma F_542c0 : fetch_word AsanUbsan.M.loaded_segments (0x542c0 : word) = Some W_542c0.
Proof. vm_refl. Qed.
Lemma D_542c0 : decode_any W_542c0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542c4 : bv 32 := 0x7e813023.
Lemma F_542c4 : fetch_word AsanUbsan.M.loaded_segments (0x542c4 : word) = Some W_542c4.
Proof. vm_refl. Qed.
Lemma D_542c4 : decode_any W_542c4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542c8 : bv 32 := 0x7c913c23.
Lemma F_542c8 : fetch_word AsanUbsan.M.loaded_segments (0x542c8 : word) = Some W_542c8.
Proof. vm_refl. Qed.
Lemma D_542c8 : decode_any W_542c8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542cc : bv 32 := 0x7d213823.
Lemma F_542cc : fetch_word AsanUbsan.M.loaded_segments (0x542cc : word) = Some W_542cc.
Proof. vm_refl. Qed.
Lemma D_542cc : decode_any W_542cc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542d0 : bv 32 := 0x7d313423.
Lemma F_542d0 : fetch_word AsanUbsan.M.loaded_segments (0x542d0 : word) = Some W_542d0.
Proof. vm_refl. Qed.
Lemma D_542d0 : decode_any W_542d0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542d4 : bv 32 := 0x7d413023.
Lemma F_542d4 : fetch_word AsanUbsan.M.loaded_segments (0x542d4 : word) = Some W_542d4.
Proof. vm_refl. Qed.
Lemma D_542d4 : decode_any W_542d4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542d8 : bv 32 := 0x7b513c23.
Lemma F_542d8 : fetch_word AsanUbsan.M.loaded_segments (0x542d8 : word) = Some W_542d8.
Proof. vm_refl. Qed.
Lemma D_542d8 : decode_any W_542d8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542dc : bv 32 := 0x7f010413.
Lemma F_542dc : fetch_word AsanUbsan.M.loaded_segments (0x542dc : word) = Some W_542dc.
Proof. vm_refl. Qed.
Lemma D_542dc : decode_any W_542dc = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542e0 : bv 32 := 0xfa010113.
Lemma F_542e0 : fetch_word AsanUbsan.M.loaded_segments (0x542e0 : word) = Some W_542e0.
Proof. vm_refl. Qed.
Lemma D_542e0 : decode_any W_542e0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542e4 : bv 32 := 0x00056697.
Lemma F_542e4 : fetch_word AsanUbsan.M.loaded_segments (0x542e4 : word) = Some W_542e4.
Proof. vm_refl. Qed.
Lemma D_542e4 : decode_any W_542e4 = Some (Auipc 13 86, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542e8 : bv 32 := 0xd3c6b683.
Lemma F_542e8 : fetch_word AsanUbsan.M.loaded_segments (0x542e8 : word) = Some W_542e8.
Proof. vm_refl. Qed.
Lemma D_542e8 : decode_any W_542e8 = Some (Load SZ8 true 13 13 3388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542ec : bv 32 := 0x0006c683.
Lemma F_542ec : fetch_word AsanUbsan.M.loaded_segments (0x542ec : word) = Some W_542ec.
Proof. vm_refl. Qed.
Lemma D_542ec : decode_any W_542ec = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542f0 : bv 32 := 0x08068863.
Lemma F_542f0 : fetch_word AsanUbsan.M.loaded_segments (0x542f0 : word) = Some W_542f0.
Proof. vm_refl. Qed.
Lemma D_542f0 : decode_any W_542f0 = Some (Branch BC_EQ 13 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542f4 : bv 32 := 0xfff54693.
Lemma F_542f4 : fetch_word AsanUbsan.M.loaded_segments (0x542f4 : word) = Some W_542f4.
Proof. vm_refl. Qed.
Lemma D_542f4 : decode_any W_542f4 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542f8 : bv 32 := 0x80040a13.
Lemma F_542f8 : fetch_word AsanUbsan.M.loaded_segments (0x542f8 : word) = Some W_542f8.
Proof. vm_refl. Qed.
Lemma D_542f8 : decode_any W_542f8 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_542fc : bv 32 := 0xfb0a0a13.
Lemma F_542fc : fetch_word AsanUbsan.M.loaded_segments (0x542fc : word) = Some W_542fc.
Proof. vm_refl. Qed.
Lemma D_542fc : decode_any W_542fc = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54300 : bv 32 := 0x0cc6e663.
Lemma F_54300 : fetch_word AsanUbsan.M.loaded_segments (0x54300 : word) = Some W_54300.
Proof. vm_refl. Qed.
Lemma D_54300 : decode_any W_54300 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54304 : bv 32 := 0xfbf60693.
Lemma F_54304 : fetch_word AsanUbsan.M.loaded_segments (0x54304 : word) = Some W_54304.
Proof. vm_refl. Qed.
Lemma D_54304 : decode_any W_54304 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54308 : bv 32 := 0xfbf00713.
Lemma F_54308 : fetch_word AsanUbsan.M.loaded_segments (0x54308 : word) = Some W_54308.
Proof. vm_refl. Qed.
Lemma D_54308 : decode_any W_54308 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5430c : bv 32 := 0x14d77463.
Lemma F_5430c : fetch_word AsanUbsan.M.loaded_segments (0x5430c : word) = Some W_5430c.
Proof. vm_refl. Qed.
Lemma D_5430c : decode_any W_5430c = Some (Branch BC_GEU 14 13 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54310 : bv 32 := 0x00055697.
Lemma F_54310 : fetch_word AsanUbsan.M.loaded_segments (0x54310 : word) = Some W_54310.
Proof. vm_refl. Qed.
Lemma D_54310 : decode_any W_54310 = Some (Auipc 13 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54314 : bv 32 := 0x1a86b683.
Lemma F_54314 : fetch_word AsanUbsan.M.loaded_segments (0x54314 : word) = Some W_54314.
Proof. vm_refl. Qed.
Lemma D_54314 : decode_any W_54314 = Some (Load SZ8 true 13 13 424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54318 : bv 32 := 0x00c507b3.
Lemma F_54318 : fetch_word AsanUbsan.M.loaded_segments (0x54318 : word) = Some W_54318.
Proof. vm_refl. Qed.
Lemma D_54318 : decode_any W_54318 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5431c : bv 32 := 0x0006b703.
Lemma F_5431c : fetch_word AsanUbsan.M.loaded_segments (0x5431c : word) = Some W_5431c.
Proof. vm_refl. Qed.
Lemma D_5431c : decode_any W_5431c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54320 : bv 32 := 0x00355693.
Lemma F_54320 : fetch_word AsanUbsan.M.loaded_segments (0x54320 : word) = Some W_54320.
Proof. vm_refl. Qed.
Lemma D_54320 : decode_any W_54320 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54324 : bv 32 := 0xfff78793.
Lemma F_54324 : fetch_word AsanUbsan.M.loaded_segments (0x54324 : word) = Some W_54324.
Proof. vm_refl. Qed.
Lemma D_54324 : decode_any W_54324 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54328 : bv 32 := 0x0037d813.
Lemma F_54328 : fetch_word AsanUbsan.M.loaded_segments (0x54328 : word) = Some W_54328.
Proof. vm_refl. Qed.
Lemma D_54328 : decode_any W_54328 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5432c : bv 32 := 0x00d706b3.
Lemma F_5432c : fetch_word AsanUbsan.M.loaded_segments (0x5432c : word) = Some W_5432c.
Proof. vm_refl. Qed.
Lemma D_5432c : decode_any W_5432c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54330 : bv 32 := 0x01070733.
Lemma F_54330 : fetch_word AsanUbsan.M.loaded_segments (0x54330 : word) = Some W_54330.
Proof. vm_refl. Qed.
Lemma D_54330 : decode_any W_54330 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54334 : bv 32 := 0xff86f813.
Lemma F_54334 : fetch_word AsanUbsan.M.loaded_segments (0x54334 : word) = Some W_54334.
Proof. vm_refl. Qed.
Lemma D_54334 : decode_any W_54334 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54338 : bv 32 := 0xff877893.
Lemma F_54338 : fetch_word AsanUbsan.M.loaded_segments (0x54338 : word) = Some W_54338.
Proof. vm_refl. Qed.
Lemma D_54338 : decode_any W_54338 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5433c : bv 32 := 0x00083803.
Lemma F_5433c : fetch_word AsanUbsan.M.loaded_segments (0x5433c : word) = Some W_5433c.
Proof. vm_refl. Qed.
Lemma D_5433c : decode_any W_5433c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54340 : bv 32 := 0x0008b883.
Lemma F_54340 : fetch_word AsanUbsan.M.loaded_segments (0x54340 : word) = Some W_54340.
Proof. vm_refl. Qed.
Lemma D_54340 : decode_any W_54340 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54344 : bv 32 := 0x0108e833.
Lemma F_54344 : fetch_word AsanUbsan.M.loaded_segments (0x54344 : word) = Some W_54344.
Proof. vm_refl. Qed.
Lemma D_54344 : decode_any W_54344 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54348 : bv 32 := 0x10081a63.
Lemma F_54348 : fetch_word AsanUbsan.M.loaded_segments (0x54348 : word) = Some W_54348.
Proof. vm_refl. Qed.
Lemma D_54348 : decode_any W_54348 = Some (Branch BC_NE 16 0 276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5434c : bv 32 := 0x00057697.
Lemma F_5434c : fetch_word AsanUbsan.M.loaded_segments (0x5434c : word) = Some W_5434c.
Proof. vm_refl. Qed.
Lemma D_5434c : decode_any W_5434c = Some (Auipc 13 87, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54350 : bv 32 := 0xfe46b683.
Lemma F_54350 : fetch_word AsanUbsan.M.loaded_segments (0x54350 : word) = Some W_54350.
Proof. vm_refl. Qed.
Lemma D_54350 : decode_any W_54350 = Some (Load SZ8 true 13 13 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54354 : bv 32 := 0x000680e7.
Lemma F_54354 : fetch_word AsanUbsan.M.loaded_segments (0x54354 : word) = Some W_54354.
Proof. vm_refl. Qed.
Lemma D_54354 : decode_any W_54354 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54358 : bv 32 := 0x06010113.
Lemma F_54358 : fetch_word AsanUbsan.M.loaded_segments (0x54358 : word) = Some W_54358.
Proof. vm_refl. Qed.
Lemma D_54358 : decode_any W_54358 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5435c : bv 32 := 0x7e813083.
Lemma F_5435c : fetch_word AsanUbsan.M.loaded_segments (0x5435c : word) = Some W_5435c.
Proof. vm_refl. Qed.
Lemma D_5435c : decode_any W_5435c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54360 : bv 32 := 0x7e013403.
Lemma F_54360 : fetch_word AsanUbsan.M.loaded_segments (0x54360 : word) = Some W_54360.
Proof. vm_refl. Qed.
Lemma D_54360 : decode_any W_54360 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54364 : bv 32 := 0x7d813483.
Lemma F_54364 : fetch_word AsanUbsan.M.loaded_segments (0x54364 : word) = Some W_54364.
Proof. vm_refl. Qed.
Lemma D_54364 : decode_any W_54364 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54368 : bv 32 := 0x7d013903.
Lemma F_54368 : fetch_word AsanUbsan.M.loaded_segments (0x54368 : word) = Some W_54368.
Proof. vm_refl. Qed.
Lemma D_54368 : decode_any W_54368 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5436c : bv 32 := 0x7c813983.
Lemma F_5436c : fetch_word AsanUbsan.M.loaded_segments (0x5436c : word) = Some W_5436c.
Proof. vm_refl. Qed.
Lemma D_5436c : decode_any W_5436c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54370 : bv 32 := 0x7c013a03.
Lemma F_54370 : fetch_word AsanUbsan.M.loaded_segments (0x54370 : word) = Some W_54370.
Proof. vm_refl. Qed.
Lemma D_54370 : decode_any W_54370 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54374 : bv 32 := 0x7b813a83.
Lemma F_54374 : fetch_word AsanUbsan.M.loaded_segments (0x54374 : word) = Some W_54374.
Proof. vm_refl. Qed.
Lemma D_54374 : decode_any W_54374 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54378 : bv 32 := 0x7f010113.
Lemma F_54378 : fetch_word AsanUbsan.M.loaded_segments (0x54378 : word) = Some W_54378.
Proof. vm_refl. Qed.
Lemma D_54378 : decode_any W_54378 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5437c : bv 32 := 0x00008067.
Lemma F_5437c : fetch_word AsanUbsan.M.loaded_segments (0x5437c : word) = Some W_5437c.
Proof. vm_refl. Qed.
Lemma D_5437c : decode_any W_5437c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54380 : bv 32 := 0x00060913.
Lemma F_54380 : fetch_word AsanUbsan.M.loaded_segments (0x54380 : word) = Some W_54380.
Proof. vm_refl. Qed.
Lemma D_54380 : decode_any W_54380 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54384 : bv 32 := 0x00058993.
Lemma F_54384 : fetch_word AsanUbsan.M.loaded_segments (0x54384 : word) = Some W_54384.
Proof. vm_refl. Qed.
Lemma D_54384 : decode_any W_54384 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54388 : bv 32 := 0x00050493.
Lemma F_54388 : fetch_word AsanUbsan.M.loaded_segments (0x54388 : word) = Some W_54388.
Proof. vm_refl. Qed.
Lemma D_54388 : decode_any W_54388 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5438c : bv 32 := 0x395060ef.
Lemma F_5438c : fetch_word AsanUbsan.M.loaded_segments (0x5438c : word) = Some W_5438c.
Proof. vm_refl. Qed.
Lemma D_5438c : decode_any W_5438c = Some (Jal 1 27540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54390 : bv 32 := 0x00098593.
Lemma F_54390 : fetch_word AsanUbsan.M.loaded_segments (0x54390 : word) = Some W_54390.
Proof. vm_refl. Qed.
Lemma D_54390 : decode_any W_54390 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54394 : bv 32 := 0x00090613.
Lemma F_54394 : fetch_word AsanUbsan.M.loaded_segments (0x54394 : word) = Some W_54394.
Proof. vm_refl. Qed.
Lemma D_54394 : decode_any W_54394 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54398 : bv 32 := 0x00050693.
Lemma F_54398 : fetch_word AsanUbsan.M.loaded_segments (0x54398 : word) = Some W_54398.
Proof. vm_refl. Qed.
Lemma D_54398 : decode_any W_54398 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5439c : bv 32 := 0x00048513.
Lemma F_5439c : fetch_word AsanUbsan.M.loaded_segments (0x5439c : word) = Some W_5439c.
Proof. vm_refl. Qed.
Lemma D_5439c : decode_any W_5439c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543a0 : bv 32 := 0xfa0696e3.
Lemma F_543a0 : fetch_word AsanUbsan.M.loaded_segments (0x543a0 : word) = Some W_543a0.
Proof. vm_refl. Qed.
Lemma D_543a0 : decode_any W_543a0 = Some (Branch BC_NE 13 0 8108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543a4 : bv 32 := 0x06010113.
Lemma F_543a4 : fetch_word AsanUbsan.M.loaded_segments (0x543a4 : word) = Some W_543a4.
Proof. vm_refl. Qed.
Lemma D_543a4 : decode_any W_543a4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543a8 : bv 32 := 0x7e813083.
Lemma F_543a8 : fetch_word AsanUbsan.M.loaded_segments (0x543a8 : word) = Some W_543a8.
Proof. vm_refl. Qed.
Lemma D_543a8 : decode_any W_543a8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543ac : bv 32 := 0x7e013403.
Lemma F_543ac : fetch_word AsanUbsan.M.loaded_segments (0x543ac : word) = Some W_543ac.
Proof. vm_refl. Qed.
Lemma D_543ac : decode_any W_543ac = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543b0 : bv 32 := 0x7d813483.
Lemma F_543b0 : fetch_word AsanUbsan.M.loaded_segments (0x543b0 : word) = Some W_543b0.
Proof. vm_refl. Qed.
Lemma D_543b0 : decode_any W_543b0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543b4 : bv 32 := 0x7d013903.
Lemma F_543b4 : fetch_word AsanUbsan.M.loaded_segments (0x543b4 : word) = Some W_543b4.
Proof. vm_refl. Qed.
Lemma D_543b4 : decode_any W_543b4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543b8 : bv 32 := 0x7c813983.
Lemma F_543b8 : fetch_word AsanUbsan.M.loaded_segments (0x543b8 : word) = Some W_543b8.
Proof. vm_refl. Qed.
Lemma D_543b8 : decode_any W_543b8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543bc : bv 32 := 0x7c013a03.
Lemma F_543bc : fetch_word AsanUbsan.M.loaded_segments (0x543bc : word) = Some W_543bc.
Proof. vm_refl. Qed.
Lemma D_543bc : decode_any W_543bc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543c0 : bv 32 := 0x7b813a83.
Lemma F_543c0 : fetch_word AsanUbsan.M.loaded_segments (0x543c0 : word) = Some W_543c0.
Proof. vm_refl. Qed.
Lemma D_543c0 : decode_any W_543c0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543c4 : bv 32 := 0x7f010113.
Lemma F_543c4 : fetch_word AsanUbsan.M.loaded_segments (0x543c4 : word) = Some W_543c4.
Proof. vm_refl. Qed.
Lemma D_543c4 : decode_any W_543c4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543c8 : bv 32 := 0x5e51106f.
Lemma F_543c8 : fetch_word AsanUbsan.M.loaded_segments (0x543c8 : word) = Some W_543c8.
Proof. vm_refl. Qed.
Lemma D_543c8 : decode_any W_543c8 = Some (Jal 0 73188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543cc : bv 32 := 0x80040693.
Lemma F_543cc : fetch_word AsanUbsan.M.loaded_segments (0x543cc : word) = Some W_543cc.
Proof. vm_refl. Qed.
Lemma D_543cc : decode_any W_543cc = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543d0 : bv 32 := 0xfc068693.
Lemma F_543d0 : fetch_word AsanUbsan.M.loaded_segments (0x543d0 : word) = Some W_543d0.
Proof. vm_refl. Qed.
Lemma D_543d0 : decode_any W_543d0 = Some (OpImm ALU_ADD 13 13 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543d4 : bv 32 := 0x80040713.
Lemma F_543d4 : fetch_word AsanUbsan.M.loaded_segments (0x543d4 : word) = Some W_543d4.
Proof. vm_refl. Qed.
Lemma D_543d4 : decode_any W_543d4 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543d8 : bv 32 := 0xfb070713.
Lemma F_543d8 : fetch_word AsanUbsan.M.loaded_segments (0x543d8 : word) = Some W_543d8.
Proof. vm_refl. Qed.
Lemma D_543d8 : decode_any W_543d8 = Some (OpImm ALU_ADD 14 14 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543dc : bv 32 := 0x7ff70a93.
Lemma F_543dc : fetch_word AsanUbsan.M.loaded_segments (0x543dc : word) = Some W_543dc.
Proof. vm_refl. Qed.
Lemma D_543dc : decode_any W_543dc = Some (OpImm ALU_ADD 21 14 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543e0 : bv 32 := 0x000ab4a3.
Lemma F_543e0 : fetch_word AsanUbsan.M.loaded_segments (0x543e0 : word) = Some W_543e0.
Proof. vm_refl. Qed.
Lemma D_543e0 : decode_any W_543e0 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543e4 : bv 32 := 0x00da3023.
Lemma F_543e4 : fetch_word AsanUbsan.M.loaded_segments (0x543e4 : word) = Some W_543e4.
Proof. vm_refl. Qed.
Lemma D_543e4 : decode_any W_543e4 = Some (Store SZ8 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543e8 : bv 32 := 0x000a3423.
Lemma F_543e8 : fetch_word AsanUbsan.M.loaded_segments (0x543e8 : word) = Some W_543e8.
Proof. vm_refl. Qed.
Lemma D_543e8 : decode_any W_543e8 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543ec : bv 32 := 0x00060493.
Lemma F_543ec : fetch_word AsanUbsan.M.loaded_segments (0x543ec : word) = Some W_543ec.
Proof. vm_refl. Qed.
Lemma D_543ec : decode_any W_543ec = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543f0 : bv 32 := 0x00058993.
Lemma F_543f0 : fetch_word AsanUbsan.M.loaded_segments (0x543f0 : word) = Some W_543f0.
Proof. vm_refl. Qed.
Lemma D_543f0 : decode_any W_543f0 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543f4 : bv 32 := 0x00050913.
Lemma F_543f4 : fetch_word AsanUbsan.M.loaded_segments (0x543f4 : word) = Some W_543f4.
Proof. vm_refl. Qed.
Lemma D_543f4 : decode_any W_543f4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543f8 : bv 32 := 0x280210ef.
Lemma F_543f8 : fetch_word AsanUbsan.M.loaded_segments (0x543f8 : word) = Some W_543f8.
Proof. vm_refl. Qed.
Lemma D_543f8 : decode_any W_543f8 = Some (Jal 1 135808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_543fc : bv 32 := 0x00050593.
Lemma F_543fc : fetch_word AsanUbsan.M.loaded_segments (0x543fc : word) = Some W_543fc.
Proof. vm_refl. Qed.
Lemma D_543fc : decode_any W_543fc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54400 : bv 32 := 0x00055517.
Lemma F_54400 : fetch_word AsanUbsan.M.loaded_segments (0x54400 : word) = Some W_54400.
Proof. vm_refl. Qed.
Lemma D_54400 : decode_any W_54400 = Some (Auipc 10 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54404 : bv 32 := 0x0a853503.
Lemma F_54404 : fetch_word AsanUbsan.M.loaded_segments (0x54404 : word) = Some W_54404.
Proof. vm_refl. Qed.
Lemma D_54404 : decode_any W_54404 = Some (Load SZ8 true 10 10 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54408 : bv 32 := 0x02154703.
Lemma F_54408 : fetch_word AsanUbsan.M.loaded_segments (0x54408 : word) = Some W_54408.
Proof. vm_refl. Qed.
Lemma D_54408 : decode_any W_54408 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5440c : bv 32 := 0x008ab4a3.
Lemma F_5440c : fetch_word AsanUbsan.M.loaded_segments (0x5440c : word) = Some W_5440c.
Proof. vm_refl. Qed.
Lemma D_5440c : decode_any W_5440c = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54410 : bv 32 := 0x80040513.
Lemma F_54410 : fetch_word AsanUbsan.M.loaded_segments (0x54410 : word) = Some W_54410.
Proof. vm_refl. Qed.
Lemma D_54410 : decode_any W_54410 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54414 : bv 32 := 0xfb050513.
Lemma F_54414 : fetch_word AsanUbsan.M.loaded_segments (0x54414 : word) = Some W_54414.
Proof. vm_refl. Qed.
Lemma D_54414 : decode_any W_54414 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54418 : bv 32 := 0x0ff00793.
Lemma F_54418 : fetch_word AsanUbsan.M.loaded_segments (0x54418 : word) = Some W_54418.
Proof. vm_refl. Qed.
Lemma D_54418 : decode_any W_54418 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5441c : bv 32 := 0x00040613.
Lemma F_5441c : fetch_word AsanUbsan.M.loaded_segments (0x5441c : word) = Some W_5441c.
Proof. vm_refl. Qed.
Lemma D_5441c : decode_any W_5441c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54420 : bv 32 := 0x00000693.
Lemma F_54420 : fetch_word AsanUbsan.M.loaded_segments (0x54420 : word) = Some W_54420.
Proof. vm_refl. Qed.
Lemma D_54420 : decode_any W_54420 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54424 : bv 32 := 0x7a4080ef.
Lemma F_54424 : fetch_word AsanUbsan.M.loaded_segments (0x54424 : word) = Some W_54424.
Proof. vm_refl. Qed.
Lemma D_54424 : decode_any W_54424 = Some (Jal 1 34724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54428 : bv 32 := 0x80040613.
Lemma F_54428 : fetch_word AsanUbsan.M.loaded_segments (0x54428 : word) = Some W_54428.
Proof. vm_refl. Qed.
Lemma D_54428 : decode_any W_54428 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5442c : bv 32 := 0xfb060613.
Lemma F_5442c : fetch_word AsanUbsan.M.loaded_segments (0x5442c : word) = Some W_5442c.
Proof. vm_refl. Qed.
Lemma D_5442c : decode_any W_5442c = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54430 : bv 32 := 0x00090513.
Lemma F_54430 : fetch_word AsanUbsan.M.loaded_segments (0x54430 : word) = Some W_54430.
Proof. vm_refl. Qed.
Lemma D_54430 : decode_any W_54430 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54434 : bv 32 := 0x00048593.
Lemma F_54434 : fetch_word AsanUbsan.M.loaded_segments (0x54434 : word) = Some W_54434.
Proof. vm_refl. Qed.
Lemma D_54434 : decode_any W_54434 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54438 : bv 32 := 0x548050ef.
Lemma F_54438 : fetch_word AsanUbsan.M.loaded_segments (0x54438 : word) = Some W_54438.
Proof. vm_refl. Qed.
Lemma D_54438 : decode_any W_54438 = Some (Jal 1 21832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5443c : bv 32 := 0x00090513.
Lemma F_5443c : fetch_word AsanUbsan.M.loaded_segments (0x5443c : word) = Some W_5443c.
Proof. vm_refl. Qed.
Lemma D_5443c : decode_any W_5443c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54440 : bv 32 := 0x00098593.
Lemma F_54440 : fetch_word AsanUbsan.M.loaded_segments (0x54440 : word) = Some W_54440.
Proof. vm_refl. Qed.
Lemma D_54440 : decode_any W_54440 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54444 : bv 32 := 0x00048613.
Lemma F_54444 : fetch_word AsanUbsan.M.loaded_segments (0x54444 : word) = Some W_54444.
Proof. vm_refl. Qed.
Lemma D_54444 : decode_any W_54444 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54448 : bv 32 := 0xfbf48693.
Lemma F_54448 : fetch_word AsanUbsan.M.loaded_segments (0x54448 : word) = Some W_54448.
Proof. vm_refl. Qed.
Lemma D_54448 : decode_any W_54448 = Some (OpImm ALU_ADD 13 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5444c : bv 32 := 0xfbf00713.
Lemma F_5444c : fetch_word AsanUbsan.M.loaded_segments (0x5444c : word) = Some W_5444c.
Proof. vm_refl. Qed.
Lemma D_5444c : decode_any W_5444c = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54450 : bv 32 := 0xecd760e3.
Lemma F_54450 : fetch_word AsanUbsan.M.loaded_segments (0x54450 : word) = Some W_54450.
Proof. vm_refl. Qed.
Lemma D_54450 : decode_any W_54450 = Some (Branch BC_LTU 14 13 7872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54454 : bv 32 := 0x02061e63.
Lemma F_54454 : fetch_word AsanUbsan.M.loaded_segments (0x54454 : word) = Some W_54454.
Proof. vm_refl. Qed.
Lemma D_54454 : decode_any W_54454 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54458 : bv 32 := 0xef5ff06f.
Lemma F_54458 : fetch_word AsanUbsan.M.loaded_segments (0x54458 : word) = Some W_54458.
Proof. vm_refl. Qed.
Lemma D_54458 : decode_any W_54458 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5445c : bv 32 := 0x00070803.
Lemma F_5445c : fetch_word AsanUbsan.M.loaded_segments (0x5445c : word) = Some W_5445c.
Proof. vm_refl. Qed.
Lemma D_5445c : decode_any W_5445c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54460 : bv 32 := 0x0077f793.
Lemma F_54460 : fetch_word AsanUbsan.M.loaded_segments (0x54460 : word) = Some W_54460.
Proof. vm_refl. Qed.
Lemma D_54460 : decode_any W_54460 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54464 : bv 32 := 0x010038b3.
Lemma F_54464 : fetch_word AsanUbsan.M.loaded_segments (0x54464 : word) = Some W_54464.
Proof. vm_refl. Qed.
Lemma D_54464 : decode_any W_54464 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54468 : bv 32 := 0x0107a7b3.
Lemma F_54468 : fetch_word AsanUbsan.M.loaded_segments (0x54468 : word) = Some W_54468.
Proof. vm_refl. Qed.
Lemma D_54468 : decode_any W_54468 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5446c : bv 32 := 0x0017c793.
Lemma F_5446c : fetch_word AsanUbsan.M.loaded_segments (0x5446c : word) = Some W_5446c.
Proof. vm_refl. Qed.
Lemma D_5446c : decode_any W_5446c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54470 : bv 32 := 0x00f8f7b3.
Lemma F_54470 : fetch_word AsanUbsan.M.loaded_segments (0x54470 : word) = Some W_54470.
Proof. vm_refl. Qed.
Lemma D_54470 : decode_any W_54470 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54474 : bv 32 := 0x00e6fa63.
Lemma F_54474 : fetch_word AsanUbsan.M.loaded_segments (0x54474 : word) = Some W_54474.
Proof. vm_refl. Qed.
Lemma D_54474 : decode_any W_54474 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54478 : bv 32 := 0x0006c803.
Lemma F_54478 : fetch_word AsanUbsan.M.loaded_segments (0x54478 : word) = Some W_54478.
Proof. vm_refl. Qed.
Lemma D_54478 : decode_any W_54478 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5447c : bv 32 := 0x00168693.
Lemma F_5447c : fetch_word AsanUbsan.M.loaded_segments (0x5447c : word) = Some W_5447c.
Proof. vm_refl. Qed.
Lemma D_5447c : decode_any W_5447c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54480 : bv 32 := 0x00f867b3.
Lemma F_54480 : fetch_word AsanUbsan.M.loaded_segments (0x54480 : word) = Some W_54480.
Proof. vm_refl. Qed.
Lemma D_54480 : decode_any W_54480 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54484 : bv 32 := 0xfee69ae3.
Lemma F_54484 : fetch_word AsanUbsan.M.loaded_segments (0x54484 : word) = Some W_54484.
Proof. vm_refl. Qed.
Lemma D_54484 : decode_any W_54484 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54488 : bv 32 := 0x0ff7f693.
Lemma F_54488 : fetch_word AsanUbsan.M.loaded_segments (0x54488 : word) = Some W_54488.
Proof. vm_refl. Qed.
Lemma D_54488 : decode_any W_54488 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5448c : bv 32 := 0xec0680e3.
Lemma F_5448c : fetch_word AsanUbsan.M.loaded_segments (0x5448c : word) = Some W_5448c.
Proof. vm_refl. Qed.
Lemma D_5448c : decode_any W_5448c = Some (Branch BC_EQ 13 0 7872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54490 : bv 32 := 0x00050493.
Lemma F_54490 : fetch_word AsanUbsan.M.loaded_segments (0x54490 : word) = Some W_54490.
Proof. vm_refl. Qed.
Lemma D_54490 : decode_any W_54490 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54494 : bv 32 := 0x00058a93.
Lemma F_54494 : fetch_word AsanUbsan.M.loaded_segments (0x54494 : word) = Some W_54494.
Proof. vm_refl. Qed.
Lemma D_54494 : decode_any W_54494 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54498 : bv 32 := 0x00060593.
Lemma F_54498 : fetch_word AsanUbsan.M.loaded_segments (0x54498 : word) = Some W_54498.
Proof. vm_refl. Qed.
Lemma D_54498 : decode_any W_54498 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5449c : bv 32 := 0x00060913.
Lemma F_5449c : fetch_word AsanUbsan.M.loaded_segments (0x5449c : word) = Some W_5449c.
Proof. vm_refl. Qed.
Lemma D_5449c : decode_any W_5449c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_544a0 : bv 32 := 0x4fc020ef.
Lemma F_544a0 : fetch_word AsanUbsan.M.loaded_segments (0x544a0 : word) = Some W_544a0.
Proof. vm_refl. Qed.
Lemma D_544a0 : decode_any W_544a0 = Some (Jal 1 9468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_544a4 : bv 32 := 0x000a8593.
Lemma F_544a4 : fetch_word AsanUbsan.M.loaded_segments (0x544a4 : word) = Some W_544a4.
Proof. vm_refl. Qed.
Lemma D_544a4 : decode_any W_544a4 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_544a8 : bv 32 := 0x00090613.
Lemma F_544a8 : fetch_word AsanUbsan.M.loaded_segments (0x544a8 : word) = Some W_544a8.
Proof. vm_refl. Qed.
Lemma D_544a8 : decode_any W_544a8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_544ac : bv 32 := 0x00050993.
Lemma F_544ac : fetch_word AsanUbsan.M.loaded_segments (0x544ac : word) = Some W_544ac.
Proof. vm_refl. Qed.
Lemma D_544ac : decode_any W_544ac = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_544b0 : bv 32 := 0x00048513.
Lemma F_544b0 : fetch_word AsanUbsan.M.loaded_segments (0x544b0 : word) = Some W_544b0.
Proof. vm_refl. Qed.
Lemma D_544b0 : decode_any W_544b0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_544b4 : bv 32 := 0xe8098ce3.
Lemma F_544b4 : fetch_word AsanUbsan.M.loaded_segments (0x544b4 : word) = Some W_544b4.
Proof. vm_refl. Qed.
Lemma D_544b4 : decode_any W_544b4 = Some (Branch BC_EQ 19 0 7832, 4%Z).
Proof. vm_refl. Qed.
