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

Definition Wx_146384 : bv 32 := 0xd602406f.
Lemma Fx_146384 : fetch_word AsanUbsan.M.loaded_segments (0x1463c0 : word) = Some Wx_146384.
Proof. vm_refl. Qed.
Lemma Dx_146384 : decode_any Wx_146384 = Some (Jal 0 1197408, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_146454 : bv 32 := 0x02060063.
Lemma Fx_146454 : fetch_word AsanUbsan.M.loaded_segments (0x146490 : word) = Some Wx_146454.
Proof. vm_refl. Qed.
Lemma Dx_146454 : decode_any Wx_146454 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_146458 : bv 32 := 0x00054683.
Lemma Fx_146458 : fetch_word AsanUbsan.M.loaded_segments (0x146494 : word) = Some Wx_146458.
Proof. vm_refl. Qed.
Lemma Dx_146458 : decode_any Wx_146458 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_14645c : bv 32 := 0x0005c703.
Lemma Fx_14645c : fetch_word AsanUbsan.M.loaded_segments (0x146498 : word) = Some Wx_14645c.
Proof. vm_refl. Qed.
Lemma Dx_14645c : decode_any Wx_14645c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_146460 : bv 32 := 0x00e69e63.
Lemma Fx_146460 : fetch_word AsanUbsan.M.loaded_segments (0x14649c : word) = Some Wx_146460.
Proof. vm_refl. Qed.
Lemma Dx_146460 : decode_any Wx_146460 = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_146464 : bv 32 := 0xfff60613.
Lemma Fx_146464 : fetch_word AsanUbsan.M.loaded_segments (0x1464a0 : word) = Some Wx_146464.
Proof. vm_refl. Qed.
Lemma Dx_146464 : decode_any Wx_146464 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_146468 : bv 32 := 0x00150513.
Lemma Fx_146468 : fetch_word AsanUbsan.M.loaded_segments (0x1464a4 : word) = Some Wx_146468.
Proof. vm_refl. Qed.
Lemma Dx_146468 : decode_any Wx_146468 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_14646c : bv 32 := 0x00158593.
Lemma Fx_14646c : fetch_word AsanUbsan.M.loaded_segments (0x1464a8 : word) = Some Wx_14646c.
Proof. vm_refl. Qed.
Lemma Dx_14646c : decode_any Wx_14646c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_146470 : bv 32 := 0xfe0614e3.
Lemma Fx_146470 : fetch_word AsanUbsan.M.loaded_segments (0x1464ac : word) = Some Wx_146470.
Proof. vm_refl. Qed.
Lemma Dx_146470 : decode_any Wx_146470 = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_146474 : bv 32 := 0x00000513.
Lemma Fx_146474 : fetch_word AsanUbsan.M.loaded_segments (0x1464b0 : word) = Some Wx_146474.
Proof. vm_refl. Qed.
Lemma Dx_146474 : decode_any Wx_146474 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_146478 : bv 32 := 0x00008067.
Lemma Fx_146478 : fetch_word AsanUbsan.M.loaded_segments (0x1464b4 : word) = Some Wx_146478.
Proof. vm_refl. Qed.
Lemma Dx_146478 : decode_any Wx_146478 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_14647c : bv 32 := 0x40e68533.
Lemma Fx_14647c : fetch_word AsanUbsan.M.loaded_segments (0x1464b8 : word) = Some Wx_14647c.
Proof. vm_refl. Qed.
Lemma Dx_14647c : decode_any Wx_14647c = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_146480 : bv 32 := 0x00008067.
Lemma Fx_146480 : fetch_word AsanUbsan.M.loaded_segments (0x1464bc : word) = Some Wx_146480.
Proof. vm_refl. Qed.
Lemma Dx_146480 : decode_any Wx_146480 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6a8d8 : bv 32 := 0x32d0106f.
Lemma Fx_6a8d8 : fetch_word AsanUbsan.M.loaded_segments (0x6a920 : word) = Some Wx_6a8d8.
Proof. vm_refl. Qed.
Lemma Dx_6a8d8 : decode_any Wx_6a8d8 = Some (Jal 0 6956, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6a8dc : bv 32 := 0x3e50106f.
Lemma Fx_6a8dc : fetch_word AsanUbsan.M.loaded_segments (0x6a924 : word) = Some Wx_6a8dc.
Proof. vm_refl. Qed.
Lemma Dx_6a8dc : decode_any Wx_6a8dc = Some (Jal 0 7140, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb6c : bv 32 := 0x00008067.
Lemma Fx_6bb6c : fetch_word AsanUbsan.M.loaded_segments (0x6bbb4 : word) = Some Wx_6bb6c.
Proof. vm_refl. Qed.
Lemma Dx_6bb6c : decode_any Wx_6bb6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb70 : bv 32 := 0x81010113.
Lemma Fx_6bb70 : fetch_word AsanUbsan.M.loaded_segments (0x6bbb8 : word) = Some Wx_6bb70.
Proof. vm_refl. Qed.
Lemma Dx_6bb70 : decode_any Wx_6bb70 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb74 : bv 32 := 0x7e113423.
Lemma Fx_6bb74 : fetch_word AsanUbsan.M.loaded_segments (0x6bbbc : word) = Some Wx_6bb74.
Proof. vm_refl. Qed.
Lemma Dx_6bb74 : decode_any Wx_6bb74 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb78 : bv 32 := 0x7e813023.
Lemma Fx_6bb78 : fetch_word AsanUbsan.M.loaded_segments (0x6bbc0 : word) = Some Wx_6bb78.
Proof. vm_refl. Qed.
Lemma Dx_6bb78 : decode_any Wx_6bb78 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb7c : bv 32 := 0x7c913c23.
Lemma Fx_6bb7c : fetch_word AsanUbsan.M.loaded_segments (0x6bbc4 : word) = Some Wx_6bb7c.
Proof. vm_refl. Qed.
Lemma Dx_6bb7c : decode_any Wx_6bb7c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb80 : bv 32 := 0x7d213823.
Lemma Fx_6bb80 : fetch_word AsanUbsan.M.loaded_segments (0x6bbc8 : word) = Some Wx_6bb80.
Proof. vm_refl. Qed.
Lemma Dx_6bb80 : decode_any Wx_6bb80 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb84 : bv 32 := 0x7d313423.
Lemma Fx_6bb84 : fetch_word AsanUbsan.M.loaded_segments (0x6bbcc : word) = Some Wx_6bb84.
Proof. vm_refl. Qed.
Lemma Dx_6bb84 : decode_any Wx_6bb84 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb88 : bv 32 := 0x7d413023.
Lemma Fx_6bb88 : fetch_word AsanUbsan.M.loaded_segments (0x6bbd0 : word) = Some Wx_6bb88.
Proof. vm_refl. Qed.
Lemma Dx_6bb88 : decode_any Wx_6bb88 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb8c : bv 32 := 0x7b513c23.
Lemma Fx_6bb8c : fetch_word AsanUbsan.M.loaded_segments (0x6bbd4 : word) = Some Wx_6bb8c.
Proof. vm_refl. Qed.
Lemma Dx_6bb8c : decode_any Wx_6bb8c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb90 : bv 32 := 0x7b613823.
Lemma Fx_6bb90 : fetch_word AsanUbsan.M.loaded_segments (0x6bbd8 : word) = Some Wx_6bb90.
Proof. vm_refl. Qed.
Lemma Dx_6bb90 : decode_any Wx_6bb90 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb94 : bv 32 := 0x7b713423.
Lemma Fx_6bb94 : fetch_word AsanUbsan.M.loaded_segments (0x6bbdc : word) = Some Wx_6bb94.
Proof. vm_refl. Qed.
Lemma Dx_6bb94 : decode_any Wx_6bb94 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb98 : bv 32 := 0x7b813023.
Lemma Fx_6bb98 : fetch_word AsanUbsan.M.loaded_segments (0x6bbe0 : word) = Some Wx_6bb98.
Proof. vm_refl. Qed.
Lemma Dx_6bb98 : decode_any Wx_6bb98 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bb9c : bv 32 := 0x79913c23.
Lemma Fx_6bb9c : fetch_word AsanUbsan.M.loaded_segments (0x6bbe4 : word) = Some Wx_6bb9c.
Proof. vm_refl. Qed.
Lemma Dx_6bb9c : decode_any Wx_6bb9c = Some (Store SZ8 2 25 1944, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bba0 : bv 32 := 0x79a13823.
Lemma Fx_6bba0 : fetch_word AsanUbsan.M.loaded_segments (0x6bbe8 : word) = Some Wx_6bba0.
Proof. vm_refl. Qed.
Lemma Dx_6bba0 : decode_any Wx_6bba0 = Some (Store SZ8 2 26 1936, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bba4 : bv 32 := 0x79b13423.
Lemma Fx_6bba4 : fetch_word AsanUbsan.M.loaded_segments (0x6bbec : word) = Some Wx_6bba4.
Proof. vm_refl. Qed.
Lemma Dx_6bba4 : decode_any Wx_6bba4 = Some (Store SZ8 2 27 1928, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bba8 : bv 32 := 0x7f010413.
Lemma Fx_6bba8 : fetch_word AsanUbsan.M.loaded_segments (0x6bbf0 : word) = Some Wx_6bba8.
Proof. vm_refl. Qed.
Lemma Dx_6bba8 : decode_any Wx_6bba8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbac : bv 32 := 0xf6010113.
Lemma Fx_6bbac : fetch_word AsanUbsan.M.loaded_segments (0x6bbf4 : word) = Some Wx_6bbac.
Proof. vm_refl. Qed.
Lemma Dx_6bbac : decode_any Wx_6bbac = Some (OpImm ALU_ADD 2 2 3936, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbb0 : bv 32 := 0x00008993.
Lemma Fx_6bbb0 : fetch_word AsanUbsan.M.loaded_segments (0x6bbf8 : word) = Some Wx_6bbb0.
Proof. vm_refl. Qed.
Lemma Dx_6bbb0 : decode_any Wx_6bbb0 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbb4 : bv 32 := 0x00070493.
Lemma Fx_6bbb4 : fetch_word AsanUbsan.M.loaded_segments (0x6bbfc : word) = Some Wx_6bbb4.
Proof. vm_refl. Qed.
Lemma Dx_6bbb4 : decode_any Wx_6bbb4 = Some (OpImm ALU_ADD 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbb8 : bv 32 := 0x00068913.
Lemma Fx_6bbb8 : fetch_word AsanUbsan.M.loaded_segments (0x6bc00 : word) = Some Wx_6bbb8.
Proof. vm_refl. Qed.
Lemma Dx_6bbb8 : decode_any Wx_6bbb8 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbbc : bv 32 := 0x00060a13.
Lemma Fx_6bbbc : fetch_word AsanUbsan.M.loaded_segments (0x6bc04 : word) = Some Wx_6bbbc.
Proof. vm_refl. Qed.
Lemma Dx_6bbbc : decode_any Wx_6bbbc = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbc0 : bv 32 := 0x00058a93.
Lemma Fx_6bbc0 : fetch_word AsanUbsan.M.loaded_segments (0x6bc08 : word) = Some Wx_6bbc0.
Proof. vm_refl. Qed.
Lemma Dx_6bbc0 : decode_any Wx_6bbc0 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbc4 : bv 32 := 0x000e9597.
Lemma Fx_6bbc4 : fetch_word AsanUbsan.M.loaded_segments (0x6bc0c : word) = Some Wx_6bbc4.
Proof. vm_refl. Qed.
Lemma Dx_6bbc4 : decode_any Wx_6bbc4 = Some (Auipc 11 233, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbc8 : bv 32 := 0x8e45bc03.
Lemma Fx_6bbc8 : fetch_word AsanUbsan.M.loaded_segments (0x6bc10 : word) = Some Wx_6bbc8.
Proof. vm_refl. Qed.
Lemma Dx_6bbc8 : decode_any Wx_6bbc8 = Some (Load SZ8 true 24 11 2276, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbcc : bv 32 := 0x0fec4583.
Lemma Fx_6bbcc : fetch_word AsanUbsan.M.loaded_segments (0x6bc14 : word) = Some Wx_6bbcc.
Proof. vm_refl. Qed.
Lemma Dx_6bbcc : decode_any Wx_6bbcc = Some (Load SZ1 false 11 24 254, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbd0 : bv 32 := 0x0a058863.
Lemma Fx_6bbd0 : fetch_word AsanUbsan.M.loaded_segments (0x6bc18 : word) = Some Wx_6bbd0.
Proof. vm_refl. Qed.
Lemma Dx_6bbd0 : decode_any Wx_6bbd0 = Some (Branch BC_EQ 11 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbd4 : bv 32 := 0x0ffc4583.
Lemma Fx_6bbd4 : fetch_word AsanUbsan.M.loaded_segments (0x6bc1c : word) = Some Wx_6bbd4.
Proof. vm_refl. Qed.
Lemma Dx_6bbd4 : decode_any Wx_6bbd4 = Some (Load SZ1 false 11 24 255, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbd8 : bv 32 := 0x80040b93.
Lemma Fx_6bbd8 : fetch_word AsanUbsan.M.loaded_segments (0x6bc20 : word) = Some Wx_6bbd8.
Proof. vm_refl. Qed.
Lemma Dx_6bbd8 : decode_any Wx_6bbd8 = Some (OpImm ALU_ADD 23 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbdc : bv 32 := 0xf80b8b93.
Lemma Fx_6bbdc : fetch_word AsanUbsan.M.loaded_segments (0x6bc24 : word) = Some Wx_6bbdc.
Proof. vm_refl. Qed.
Lemma Dx_6bbdc : decode_any Wx_6bbdc = Some (OpImm ALU_ADD 23 23 3968, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbe0 : bv 32 := 0x0a058c63.
Lemma Fx_6bbe0 : fetch_word AsanUbsan.M.loaded_segments (0x6bc28 : word) = Some Wx_6bbe0.
Proof. vm_refl. Qed.
Lemma Dx_6bbe0 : decode_any Wx_6bbe0 = Some (Branch BC_EQ 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbe4 : bv 32 := 0xfffa4593.
Lemma Fx_6bbe4 : fetch_word AsanUbsan.M.loaded_segments (0x6bc2c : word) = Some Wx_6bbe4.
Proof. vm_refl. Qed.
Lemma Dx_6bbe4 : decode_any Wx_6bbe4 = Some (OpImm ALU_XOR 11 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbe8 : bv 32 := 0x2095e063.
Lemma Fx_6bbe8 : fetch_word AsanUbsan.M.loaded_segments (0x6bc30 : word) = Some Wx_6bbe8.
Proof. vm_refl. Qed.
Lemma Dx_6bbe8 : decode_any Wx_6bbe8 = Some (Branch BC_LTU 11 9 512, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbec : bv 32 := 0xfbf48c93.
Lemma Fx_6bbec : fetch_word AsanUbsan.M.loaded_segments (0x6bc34 : word) = Some Wx_6bbec.
Proof. vm_refl. Qed.
Lemma Dx_6bbec : decode_any Wx_6bbec = Some (OpImm ALU_ADD 25 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbf0 : bv 32 := 0xfbf00593.
Lemma Fx_6bbf0 : fetch_word AsanUbsan.M.loaded_segments (0x6bc38 : word) = Some Wx_6bbf0.
Proof. vm_refl. Qed.
Lemma Dx_6bbf0 : decode_any Wx_6bbf0 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbf4 : bv 32 := 0x2795f263.
Lemma Fx_6bbf4 : fetch_word AsanUbsan.M.loaded_segments (0x6bc3c : word) = Some Wx_6bbf4.
Proof. vm_refl. Qed.
Lemma Dx_6bbf4 : decode_any Wx_6bbf4 = Some (Branch BC_GEU 11 25 612, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbf8 : bv 32 := 0x000e9597.
Lemma Fx_6bbf8 : fetch_word AsanUbsan.M.loaded_segments (0x6bc40 : word) = Some Wx_6bbf8.
Proof. vm_refl. Qed.
Lemma Dx_6bbf8 : decode_any Wx_6bbf8 = Some (Auipc 11 233, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bbfc : bv 32 := 0x8c05b583.
Lemma Fx_6bbfc : fetch_word AsanUbsan.M.loaded_segments (0x6bc44 : word) = Some Wx_6bbfc.
Proof. vm_refl. Qed.
Lemma Dx_6bbfc : decode_any Wx_6bbfc = Some (Load SZ8 true 11 11 2240, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc00 : bv 32 := 0x009a06b3.
Lemma Fx_6bc00 : fetch_word AsanUbsan.M.loaded_segments (0x6bc48 : word) = Some Wx_6bc00.
Proof. vm_refl. Qed.
Lemma Dx_6bc00 : decode_any Wx_6bc00 = Some (Op ALU_ADD 13 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc04 : bv 32 := 0x0005b603.
Lemma Fx_6bc04 : fetch_word AsanUbsan.M.loaded_segments (0x6bc4c : word) = Some Wx_6bc04.
Proof. vm_refl. Qed.
Lemma Dx_6bc04 : decode_any Wx_6bc04 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc08 : bv 32 := 0x003a5593.
Lemma Fx_6bc08 : fetch_word AsanUbsan.M.loaded_segments (0x6bc50 : word) = Some Wx_6bc08.
Proof. vm_refl. Qed.
Lemma Dx_6bc08 : decode_any Wx_6bc08 = Some (ShiftImm ALU_SRL 11 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc0c : bv 32 := 0xfff68693.
Lemma Fx_6bc0c : fetch_word AsanUbsan.M.loaded_segments (0x6bc54 : word) = Some Wx_6bc0c.
Proof. vm_refl. Qed.
Lemma Dx_6bc0c : decode_any Wx_6bc0c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc10 : bv 32 := 0x0036d713.
Lemma Fx_6bc10 : fetch_word AsanUbsan.M.loaded_segments (0x6bc58 : word) = Some Wx_6bc10.
Proof. vm_refl. Qed.
Lemma Dx_6bc10 : decode_any Wx_6bc10 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc14 : bv 32 := 0x00b605b3.
Lemma Fx_6bc14 : fetch_word AsanUbsan.M.loaded_segments (0x6bc5c : word) = Some Wx_6bc14.
Proof. vm_refl. Qed.
Lemma Dx_6bc14 : decode_any Wx_6bc14 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc18 : bv 32 := 0x00e60633.
Lemma Fx_6bc18 : fetch_word AsanUbsan.M.loaded_segments (0x6bc60 : word) = Some Wx_6bc18.
Proof. vm_refl. Qed.
Lemma Dx_6bc18 : decode_any Wx_6bc18 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc1c : bv 32 := 0xff85f713.
Lemma Fx_6bc1c : fetch_word AsanUbsan.M.loaded_segments (0x6bc64 : word) = Some Wx_6bc1c.
Proof. vm_refl. Qed.
Lemma Dx_6bc1c : decode_any Wx_6bc1c = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc20 : bv 32 := 0xff867793.
Lemma Fx_6bc20 : fetch_word AsanUbsan.M.loaded_segments (0x6bc68 : word) = Some Wx_6bc20.
Proof. vm_refl. Qed.
Lemma Dx_6bc20 : decode_any Wx_6bc20 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc24 : bv 32 := 0x00073703.
Lemma Fx_6bc24 : fetch_word AsanUbsan.M.loaded_segments (0x6bc6c : word) = Some Wx_6bc24.
Proof. vm_refl. Qed.
Lemma Dx_6bc24 : decode_any Wx_6bc24 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc28 : bv 32 := 0x0007b783.
Lemma Fx_6bc28 : fetch_word AsanUbsan.M.loaded_segments (0x6bc70 : word) = Some Wx_6bc28.
Proof. vm_refl. Qed.
Lemma Dx_6bc28 : decode_any Wx_6bc28 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc2c : bv 32 := 0x00e7e733.
Lemma Fx_6bc2c : fetch_word AsanUbsan.M.loaded_segments (0x6bc74 : word) = Some Wx_6bc2c.
Proof. vm_refl. Qed.
Lemma Dx_6bc2c : decode_any Wx_6bc2c = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc30 : bv 32 := 0x3a071063.
Lemma Fx_6bc30 : fetch_word AsanUbsan.M.loaded_segments (0x6bc78 : word) = Some Wx_6bc30.
Proof. vm_refl. Qed.
Lemma Dx_6bc30 : decode_any Wx_6bc30 = Some (Branch BC_NE 14 0 928, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc34 : bv 32 := 0xfff94593.
Lemma Fx_6bc34 : fetch_word AsanUbsan.M.loaded_segments (0x6bc7c : word) = Some Wx_6bc34.
Proof. vm_refl. Qed.
Lemma Dx_6bc34 : decode_any Wx_6bc34 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc38 : bv 32 := 0x2295e463.
Lemma Fx_6bc38 : fetch_word AsanUbsan.M.loaded_segments (0x6bc80 : word) = Some Wx_6bc38.
Proof. vm_refl. Qed.
Lemma Dx_6bc38 : decode_any Wx_6bc38 = Some (Branch BC_LTU 11 9 552, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc3c : bv 32 := 0xfbf00593.
Lemma Fx_6bc3c : fetch_word AsanUbsan.M.loaded_segments (0x6bc84 : word) = Some Wx_6bc3c.
Proof. vm_refl. Qed.
Lemma Dx_6bc3c : decode_any Wx_6bc3c = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc40 : bv 32 := 0x2995f663.
Lemma Fx_6bc40 : fetch_word AsanUbsan.M.loaded_segments (0x6bc88 : word) = Some Wx_6bc40.
Proof. vm_refl. Qed.
Lemma Dx_6bc40 : decode_any Wx_6bc40 = Some (Branch BC_GEU 11 25 652, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc44 : bv 32 := 0x000e9597.
Lemma Fx_6bc44 : fetch_word AsanUbsan.M.loaded_segments (0x6bc8c : word) = Some Wx_6bc44.
Proof. vm_refl. Qed.
Lemma Dx_6bc44 : decode_any Wx_6bc44 = Some (Auipc 11 233, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc48 : bv 32 := 0x8745b583.
Lemma Fx_6bc48 : fetch_word AsanUbsan.M.loaded_segments (0x6bc90 : word) = Some Wx_6bc48.
Proof. vm_refl. Qed.
Lemma Dx_6bc48 : decode_any Wx_6bc48 = Some (Load SZ8 true 11 11 2164, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc4c : bv 32 := 0x009906b3.
Lemma Fx_6bc4c : fetch_word AsanUbsan.M.loaded_segments (0x6bc94 : word) = Some Wx_6bc4c.
Proof. vm_refl. Qed.
Lemma Dx_6bc4c : decode_any Wx_6bc4c = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc50 : bv 32 := 0x0005b603.
Lemma Fx_6bc50 : fetch_word AsanUbsan.M.loaded_segments (0x6bc98 : word) = Some Wx_6bc50.
Proof. vm_refl. Qed.
Lemma Dx_6bc50 : decode_any Wx_6bc50 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc54 : bv 32 := 0x00395593.
Lemma Fx_6bc54 : fetch_word AsanUbsan.M.loaded_segments (0x6bc9c : word) = Some Wx_6bc54.
Proof. vm_refl. Qed.
Lemma Dx_6bc54 : decode_any Wx_6bc54 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc58 : bv 32 := 0xfff68693.
Lemma Fx_6bc58 : fetch_word AsanUbsan.M.loaded_segments (0x6bca0 : word) = Some Wx_6bc58.
Proof. vm_refl. Qed.
Lemma Dx_6bc58 : decode_any Wx_6bc58 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc5c : bv 32 := 0x0036d713.
Lemma Fx_6bc5c : fetch_word AsanUbsan.M.loaded_segments (0x6bca4 : word) = Some Wx_6bc5c.
Proof. vm_refl. Qed.
Lemma Dx_6bc5c : decode_any Wx_6bc5c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc60 : bv 32 := 0x00b605b3.
Lemma Fx_6bc60 : fetch_word AsanUbsan.M.loaded_segments (0x6bca8 : word) = Some Wx_6bc60.
Proof. vm_refl. Qed.
Lemma Dx_6bc60 : decode_any Wx_6bc60 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc64 : bv 32 := 0x00e60633.
Lemma Fx_6bc64 : fetch_word AsanUbsan.M.loaded_segments (0x6bcac : word) = Some Wx_6bc64.
Proof. vm_refl. Qed.
Lemma Dx_6bc64 : decode_any Wx_6bc64 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc68 : bv 32 := 0xff85f713.
Lemma Fx_6bc68 : fetch_word AsanUbsan.M.loaded_segments (0x6bcb0 : word) = Some Wx_6bc68.
Proof. vm_refl. Qed.
Lemma Dx_6bc68 : decode_any Wx_6bc68 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc6c : bv 32 := 0xff867793.
Lemma Fx_6bc6c : fetch_word AsanUbsan.M.loaded_segments (0x6bcb4 : word) = Some Wx_6bc6c.
Proof. vm_refl. Qed.
Lemma Dx_6bc6c : decode_any Wx_6bc6c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc70 : bv 32 := 0x00073703.
Lemma Fx_6bc70 : fetch_word AsanUbsan.M.loaded_segments (0x6bcb8 : word) = Some Wx_6bc70.
Proof. vm_refl. Qed.
Lemma Dx_6bc70 : decode_any Wx_6bc70 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc74 : bv 32 := 0x0007b783.
Lemma Fx_6bc74 : fetch_word AsanUbsan.M.loaded_segments (0x6bcbc : word) = Some Wx_6bc74.
Proof. vm_refl. Qed.
Lemma Dx_6bc74 : decode_any Wx_6bc74 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc78 : bv 32 := 0x00e7e733.
Lemma Fx_6bc78 : fetch_word AsanUbsan.M.loaded_segments (0x6bcc0 : word) = Some Wx_6bc78.
Proof. vm_refl. Qed.
Lemma Dx_6bc78 : decode_any Wx_6bc78 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc7c : bv 32 := 0x46071063.
Lemma Fx_6bc7c : fetch_word AsanUbsan.M.loaded_segments (0x6bcc4 : word) = Some Wx_6bc7c.
Proof. vm_refl. Qed.
Lemma Dx_6bc7c : decode_any Wx_6bc7c = Some (Branch BC_NE 14 0 1120, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc80 : bv 32 := 0x000a0513.
Lemma Fx_6bc80 : fetch_word AsanUbsan.M.loaded_segments (0x6bcc8 : word) = Some Wx_6bc80.
Proof. vm_refl. Qed.
Lemma Dx_6bc80 : decode_any Wx_6bc80 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc84 : bv 32 := 0x00090593.
Lemma Fx_6bc84 : fetch_word AsanUbsan.M.loaded_segments (0x6bccc : word) = Some Wx_6bc84.
Proof. vm_refl. Qed.
Lemma Dx_6bc84 : decode_any Wx_6bc84 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc88 : bv 32 := 0x00048613.
Lemma Fx_6bc88 : fetch_word AsanUbsan.M.loaded_segments (0x6bcd0 : word) = Some Wx_6bc88.
Proof. vm_refl. Qed.
Lemma Dx_6bc88 : decode_any Wx_6bc88 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc8c : bv 32 := 0x000a80e7.
Lemma Fx_6bc8c : fetch_word AsanUbsan.M.loaded_segments (0x6bcd4 : word) = Some Wx_6bc8c.
Proof. vm_refl. Qed.
Lemma Dx_6bc8c : decode_any Wx_6bc8c = Some (Jalr 1 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc90 : bv 32 := 0x00050a93.
Lemma Fx_6bc90 : fetch_word AsanUbsan.M.loaded_segments (0x6bcd8 : word) = Some Wx_6bc90.
Proof. vm_refl. Qed.
Lemma Dx_6bc90 : decode_any Wx_6bc90 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bc94 : bv 32 := 0x0e40006f.
Lemma Fx_6bc94 : fetch_word AsanUbsan.M.loaded_segments (0x6bcdc : word) = Some Wx_6bc94.
Proof. vm_refl. Qed.
Lemma Dx_6bc94 : decode_any Wx_6bc94 = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd78 : bv 32 := 0x00098513.
Lemma Fx_6bd78 : fetch_word AsanUbsan.M.loaded_segments (0x6bdc0 : word) = Some Wx_6bd78.
Proof. vm_refl. Qed.
Lemma Dx_6bd78 : decode_any Wx_6bd78 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd7c : bv 32 := 0x000a0593.
Lemma Fx_6bd7c : fetch_word AsanUbsan.M.loaded_segments (0x6bdc4 : word) = Some Wx_6bd7c.
Proof. vm_refl. Qed.
Lemma Dx_6bd7c : decode_any Wx_6bd7c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd80 : bv 32 := 0x00090613.
Lemma Fx_6bd80 : fetch_word AsanUbsan.M.loaded_segments (0x6bdc8 : word) = Some Wx_6bd80.
Proof. vm_refl. Qed.
Lemma Dx_6bd80 : decode_any Wx_6bd80 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd84 : bv 32 := 0x00048693.
Lemma Fx_6bd84 : fetch_word AsanUbsan.M.loaded_segments (0x6bdcc : word) = Some Wx_6bd84.
Proof. vm_refl. Qed.
Lemma Dx_6bd84 : decode_any Wx_6bd84 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd88 : bv 32 := 0x000a8713.
Lemma Fx_6bd88 : fetch_word AsanUbsan.M.loaded_segments (0x6bdd0 : word) = Some Wx_6bd88.
Proof. vm_refl. Qed.
Lemma Dx_6bd88 : decode_any Wx_6bd88 = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd8c : bv 32 := 0xde1ff0ef.
Lemma Fx_6bd8c : fetch_word AsanUbsan.M.loaded_segments (0x6bdd4 : word) = Some Wx_6bd8c.
Proof. vm_refl. Qed.
Lemma Dx_6bd8c : decode_any Wx_6bd8c = Some (Jal 1 2096608, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd90 : bv 32 := 0x000a8513.
Lemma Fx_6bd90 : fetch_word AsanUbsan.M.loaded_segments (0x6bdd8 : word) = Some Wx_6bd90.
Proof. vm_refl. Qed.
Lemma Dx_6bd90 : decode_any Wx_6bd90 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd94 : bv 32 := 0x0a010113.
Lemma Fx_6bd94 : fetch_word AsanUbsan.M.loaded_segments (0x6bddc : word) = Some Wx_6bd94.
Proof. vm_refl. Qed.
Lemma Dx_6bd94 : decode_any Wx_6bd94 = Some (OpImm ALU_ADD 2 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd98 : bv 32 := 0x7e813083.
Lemma Fx_6bd98 : fetch_word AsanUbsan.M.loaded_segments (0x6bde0 : word) = Some Wx_6bd98.
Proof. vm_refl. Qed.
Lemma Dx_6bd98 : decode_any Wx_6bd98 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bd9c : bv 32 := 0x7e013403.
Lemma Fx_6bd9c : fetch_word AsanUbsan.M.loaded_segments (0x6bde4 : word) = Some Wx_6bd9c.
Proof. vm_refl. Qed.
Lemma Dx_6bd9c : decode_any Wx_6bd9c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bda0 : bv 32 := 0x7d813483.
Lemma Fx_6bda0 : fetch_word AsanUbsan.M.loaded_segments (0x6bde8 : word) = Some Wx_6bda0.
Proof. vm_refl. Qed.
Lemma Dx_6bda0 : decode_any Wx_6bda0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bda4 : bv 32 := 0x7d013903.
Lemma Fx_6bda4 : fetch_word AsanUbsan.M.loaded_segments (0x6bdec : word) = Some Wx_6bda4.
Proof. vm_refl. Qed.
Lemma Dx_6bda4 : decode_any Wx_6bda4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bda8 : bv 32 := 0x7c813983.
Lemma Fx_6bda8 : fetch_word AsanUbsan.M.loaded_segments (0x6bdf0 : word) = Some Wx_6bda8.
Proof. vm_refl. Qed.
Lemma Dx_6bda8 : decode_any Wx_6bda8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bdac : bv 32 := 0x7c013a03.
Lemma Fx_6bdac : fetch_word AsanUbsan.M.loaded_segments (0x6bdf4 : word) = Some Wx_6bdac.
Proof. vm_refl. Qed.
Lemma Dx_6bdac : decode_any Wx_6bdac = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bdb0 : bv 32 := 0x7b813a83.
Lemma Fx_6bdb0 : fetch_word AsanUbsan.M.loaded_segments (0x6bdf8 : word) = Some Wx_6bdb0.
Proof. vm_refl. Qed.
Lemma Dx_6bdb0 : decode_any Wx_6bdb0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bdb4 : bv 32 := 0x7b013b03.
Lemma Fx_6bdb4 : fetch_word AsanUbsan.M.loaded_segments (0x6bdfc : word) = Some Wx_6bdb4.
Proof. vm_refl. Qed.
Lemma Dx_6bdb4 : decode_any Wx_6bdb4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bdb8 : bv 32 := 0x7a813b83.
Lemma Fx_6bdb8 : fetch_word AsanUbsan.M.loaded_segments (0x6be00 : word) = Some Wx_6bdb8.
Proof. vm_refl. Qed.
Lemma Dx_6bdb8 : decode_any Wx_6bdb8 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bdbc : bv 32 := 0x7a013c03.
Lemma Fx_6bdbc : fetch_word AsanUbsan.M.loaded_segments (0x6be04 : word) = Some Wx_6bdbc.
Proof. vm_refl. Qed.
Lemma Dx_6bdbc : decode_any Wx_6bdbc = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bdc0 : bv 32 := 0x79813c83.
Lemma Fx_6bdc0 : fetch_word AsanUbsan.M.loaded_segments (0x6be08 : word) = Some Wx_6bdc0.
Proof. vm_refl. Qed.
Lemma Dx_6bdc0 : decode_any Wx_6bdc0 = Some (Load SZ8 true 25 2 1944, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bdc4 : bv 32 := 0x79013d03.
Lemma Fx_6bdc4 : fetch_word AsanUbsan.M.loaded_segments (0x6be0c : word) = Some Wx_6bdc4.
Proof. vm_refl. Qed.
Lemma Dx_6bdc4 : decode_any Wx_6bdc4 = Some (Load SZ8 true 26 2 1936, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bdc8 : bv 32 := 0x78813d83.
Lemma Fx_6bdc8 : fetch_word AsanUbsan.M.loaded_segments (0x6be10 : word) = Some Wx_6bdc8.
Proof. vm_refl. Qed.
Lemma Dx_6bdc8 : decode_any Wx_6bdc8 = Some (Load SZ8 true 27 2 1928, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bdcc : bv 32 := 0x7f010113.
Lemma Fx_6bdcc : fetch_word AsanUbsan.M.loaded_segments (0x6be14 : word) = Some Wx_6bdcc.
Proof. vm_refl. Qed.
Lemma Dx_6bdcc : decode_any Wx_6bdcc = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bdd0 : bv 32 := 0x00008067.
Lemma Fx_6bdd0 : fetch_word AsanUbsan.M.loaded_segments (0x6be18 : word) = Some Wx_6bdd0.
Proof. vm_refl. Qed.
Lemma Dx_6bdd0 : decode_any Wx_6bdd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6be58 : bv 32 := 0x1a049663.
Lemma Fx_6be58 : fetch_word AsanUbsan.M.loaded_segments (0x6bea0 : word) = Some Wx_6be58.
Proof. vm_refl. Qed.
Lemma Dx_6be58 : decode_any Wx_6be58 = Some (Branch BC_NE 9 0 428, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6be5c : bv 32 := 0xdd9ff06f.
Lemma Fx_6be5c : fetch_word AsanUbsan.M.loaded_segments (0x6bea4 : word) = Some Wx_6be5c.
Proof. vm_refl. Qed.
Lemma Dx_6be5c : decode_any Wx_6be5c = Some (Jal 0 2096600, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6becc : bv 32 := 0x24049263.
Lemma Fx_6becc : fetch_word AsanUbsan.M.loaded_segments (0x6bf14 : word) = Some Wx_6becc.
Proof. vm_refl. Qed.
Lemma Dx_6becc : decode_any Wx_6becc = Some (Branch BC_NE 9 0 580, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bed0 : bv 32 := 0xdb1ff06f.
Lemma Fx_6bed0 : fetch_word AsanUbsan.M.loaded_segments (0x6bf18 : word) = Some Wx_6bed0.
Proof. vm_refl. Qed.
Lemma Dx_6bed0 : decode_any Wx_6bed0 = Some (Jal 0 2096560, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bfd0 : bv 32 := 0x00060703.
Lemma Fx_6bfd0 : fetch_word AsanUbsan.M.loaded_segments (0x6c018 : word) = Some Wx_6bfd0.
Proof. vm_refl. Qed.
Lemma Dx_6bfd0 : decode_any Wx_6bfd0 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bfd4 : bv 32 := 0x0076f693.
Lemma Fx_6bfd4 : fetch_word AsanUbsan.M.loaded_segments (0x6c01c : word) = Some Wx_6bfd4.
Proof. vm_refl. Qed.
Lemma Dx_6bfd4 : decode_any Wx_6bfd4 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bfd8 : bv 32 := 0x00e037b3.
Lemma Fx_6bfd8 : fetch_word AsanUbsan.M.loaded_segments (0x6c020 : word) = Some Wx_6bfd8.
Proof. vm_refl. Qed.
Lemma Dx_6bfd8 : decode_any Wx_6bfd8 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bfdc : bv 32 := 0x00e6a6b3.
Lemma Fx_6bfdc : fetch_word AsanUbsan.M.loaded_segments (0x6c024 : word) = Some Wx_6bfdc.
Proof. vm_refl. Qed.
Lemma Dx_6bfdc : decode_any Wx_6bfdc = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bfe0 : bv 32 := 0x0016c693.
Lemma Fx_6bfe0 : fetch_word AsanUbsan.M.loaded_segments (0x6c028 : word) = Some Wx_6bfe0.
Proof. vm_refl. Qed.
Lemma Dx_6bfe0 : decode_any Wx_6bfe0 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bfe4 : bv 32 := 0x00d7f6b3.
Lemma Fx_6bfe4 : fetch_word AsanUbsan.M.loaded_segments (0x6c02c : word) = Some Wx_6bfe4.
Proof. vm_refl. Qed.
Lemma Dx_6bfe4 : decode_any Wx_6bfe4 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bfe8 : bv 32 := 0x00c5fa63.
Lemma Fx_6bfe8 : fetch_word AsanUbsan.M.loaded_segments (0x6c030 : word) = Some Wx_6bfe8.
Proof. vm_refl. Qed.
Lemma Dx_6bfe8 : decode_any Wx_6bfe8 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bfec : bv 32 := 0x0005c703.
Lemma Fx_6bfec : fetch_word AsanUbsan.M.loaded_segments (0x6c034 : word) = Some Wx_6bfec.
Proof. vm_refl. Qed.
Lemma Dx_6bfec : decode_any Wx_6bfec = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bff0 : bv 32 := 0x00158593.
Lemma Fx_6bff0 : fetch_word AsanUbsan.M.loaded_segments (0x6c038 : word) = Some Wx_6bff0.
Proof. vm_refl. Qed.
Lemma Dx_6bff0 : decode_any Wx_6bff0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bff4 : bv 32 := 0x00d766b3.
Lemma Fx_6bff4 : fetch_word AsanUbsan.M.loaded_segments (0x6c03c : word) = Some Wx_6bff4.
Proof. vm_refl. Qed.
Lemma Dx_6bff4 : decode_any Wx_6bff4 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bff8 : bv 32 := 0xfec59ae3.
Lemma Fx_6bff8 : fetch_word AsanUbsan.M.loaded_segments (0x6c040 : word) = Some Wx_6bff8.
Proof. vm_refl. Qed.
Lemma Dx_6bff8 : decode_any Wx_6bff8 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6bffc : bv 32 := 0x0ff6f593.
Lemma Fx_6bffc : fetch_word AsanUbsan.M.loaded_segments (0x6c044 : word) = Some Wx_6bffc.
Proof. vm_refl. Qed.
Lemma Dx_6bffc : decode_any Wx_6bffc = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c000 : bv 32 := 0xc2058ae3.
Lemma Fx_6c000 : fetch_word AsanUbsan.M.loaded_segments (0x6c048 : word) = Some Wx_6c000.
Proof. vm_refl. Qed.
Lemma Dx_6c000 : decode_any Wx_6c000 = Some (Branch BC_EQ 11 0 7220, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c004 : bv 32 := 0x00050d13.
Lemma Fx_6c004 : fetch_word AsanUbsan.M.loaded_segments (0x6c04c : word) = Some Wx_6c004.
Proof. vm_refl. Qed.
Lemma Dx_6c004 : decode_any Wx_6c004 = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c008 : bv 32 := 0x000a0513.
Lemma Fx_6c008 : fetch_word AsanUbsan.M.loaded_segments (0x6c050 : word) = Some Wx_6c008.
Proof. vm_refl. Qed.
Lemma Dx_6c008 : decode_any Wx_6c008 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c00c : bv 32 := 0x00048593.
Lemma Fx_6c00c : fetch_word AsanUbsan.M.loaded_segments (0x6c054 : word) = Some Wx_6c00c.
Proof. vm_refl. Qed.
Lemma Dx_6c00c : decode_any Wx_6c00c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c010 : bv 32 := 0x209160ef.
Lemma Fx_6c010 : fetch_word AsanUbsan.M.loaded_segments (0x6c058 : word) = Some Wx_6c010.
Proof. vm_refl. Qed.
Lemma Dx_6c010 : decode_any Wx_6c010 = Some (Jal 1 92680, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c014 : bv 32 := 0x00050b13.
Lemma Fx_6c014 : fetch_word AsanUbsan.M.loaded_segments (0x6c05c : word) = Some Wx_6c014.
Proof. vm_refl. Qed.
Lemma Dx_6c014 : decode_any Wx_6c014 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c018 : bv 32 := 0x000d0513.
Lemma Fx_6c018 : fetch_word AsanUbsan.M.loaded_segments (0x6c060 : word) = Some Wx_6c018.
Proof. vm_refl. Qed.
Lemma Dx_6c018 : decode_any Wx_6c018 = Some (OpImm ALU_ADD 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c01c : bv 32 := 0xc00b0ce3.
Lemma Fx_6c01c : fetch_word AsanUbsan.M.loaded_segments (0x6c064 : word) = Some Wx_6c01c.
Proof. vm_refl. Qed.
Lemma Dx_6c01c : decode_any Wx_6c01c = Some (Branch BC_EQ 22 0 7192, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0dc : bv 32 := 0x00060703.
Lemma Fx_6c0dc : fetch_word AsanUbsan.M.loaded_segments (0x6c124 : word) = Some Wx_6c0dc.
Proof. vm_refl. Qed.
Lemma Dx_6c0dc : decode_any Wx_6c0dc = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0e0 : bv 32 := 0x0076f693.
Lemma Fx_6c0e0 : fetch_word AsanUbsan.M.loaded_segments (0x6c128 : word) = Some Wx_6c0e0.
Proof. vm_refl. Qed.
Lemma Dx_6c0e0 : decode_any Wx_6c0e0 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0e4 : bv 32 := 0x00e037b3.
Lemma Fx_6c0e4 : fetch_word AsanUbsan.M.loaded_segments (0x6c12c : word) = Some Wx_6c0e4.
Proof. vm_refl. Qed.
Lemma Dx_6c0e4 : decode_any Wx_6c0e4 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0e8 : bv 32 := 0x00e6a6b3.
Lemma Fx_6c0e8 : fetch_word AsanUbsan.M.loaded_segments (0x6c130 : word) = Some Wx_6c0e8.
Proof. vm_refl. Qed.
Lemma Dx_6c0e8 : decode_any Wx_6c0e8 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0ec : bv 32 := 0x0016c693.
Lemma Fx_6c0ec : fetch_word AsanUbsan.M.loaded_segments (0x6c134 : word) = Some Wx_6c0ec.
Proof. vm_refl. Qed.
Lemma Dx_6c0ec : decode_any Wx_6c0ec = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0f0 : bv 32 := 0x00d7f6b3.
Lemma Fx_6c0f0 : fetch_word AsanUbsan.M.loaded_segments (0x6c138 : word) = Some Wx_6c0f0.
Proof. vm_refl. Qed.
Lemma Dx_6c0f0 : decode_any Wx_6c0f0 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0f4 : bv 32 := 0x00c5fa63.
Lemma Fx_6c0f4 : fetch_word AsanUbsan.M.loaded_segments (0x6c13c : word) = Some Wx_6c0f4.
Proof. vm_refl. Qed.
Lemma Dx_6c0f4 : decode_any Wx_6c0f4 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0f8 : bv 32 := 0x0005c703.
Lemma Fx_6c0f8 : fetch_word AsanUbsan.M.loaded_segments (0x6c140 : word) = Some Wx_6c0f8.
Proof. vm_refl. Qed.
Lemma Dx_6c0f8 : decode_any Wx_6c0f8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c0fc : bv 32 := 0x00158593.
Lemma Fx_6c0fc : fetch_word AsanUbsan.M.loaded_segments (0x6c144 : word) = Some Wx_6c0fc.
Proof. vm_refl. Qed.
Lemma Dx_6c0fc : decode_any Wx_6c0fc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c100 : bv 32 := 0x00d766b3.
Lemma Fx_6c100 : fetch_word AsanUbsan.M.loaded_segments (0x6c148 : word) = Some Wx_6c100.
Proof. vm_refl. Qed.
Lemma Dx_6c100 : decode_any Wx_6c100 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c104 : bv 32 := 0xfec59ae3.
Lemma Fx_6c104 : fetch_word AsanUbsan.M.loaded_segments (0x6c14c : word) = Some Wx_6c104.
Proof. vm_refl. Qed.
Lemma Dx_6c104 : decode_any Wx_6c104 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c108 : bv 32 := 0x0ff6f593.
Lemma Fx_6c108 : fetch_word AsanUbsan.M.loaded_segments (0x6c150 : word) = Some Wx_6c108.
Proof. vm_refl. Qed.
Lemma Dx_6c108 : decode_any Wx_6c108 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c10c : bv 32 := 0xb6058ae3.
Lemma Fx_6c10c : fetch_word AsanUbsan.M.loaded_segments (0x6c154 : word) = Some Wx_6c10c.
Proof. vm_refl. Qed.
Lemma Dx_6c10c : decode_any Wx_6c10c = Some (Branch BC_EQ 11 0 7028, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c110 : bv 32 := 0x00050c93.
Lemma Fx_6c110 : fetch_word AsanUbsan.M.loaded_segments (0x6c158 : word) = Some Wx_6c110.
Proof. vm_refl. Qed.
Lemma Dx_6c110 : decode_any Wx_6c110 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c114 : bv 32 := 0x00090513.
Lemma Fx_6c114 : fetch_word AsanUbsan.M.loaded_segments (0x6c15c : word) = Some Wx_6c114.
Proof. vm_refl. Qed.
Lemma Dx_6c114 : decode_any Wx_6c114 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c118 : bv 32 := 0x00048593.
Lemma Fx_6c118 : fetch_word AsanUbsan.M.loaded_segments (0x6c160 : word) = Some Wx_6c118.
Proof. vm_refl. Qed.
Lemma Dx_6c118 : decode_any Wx_6c118 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c11c : bv 32 := 0x0fd160ef.
Lemma Fx_6c11c : fetch_word AsanUbsan.M.loaded_segments (0x6c164 : word) = Some Wx_6c11c.
Proof. vm_refl. Qed.
Lemma Dx_6c11c : decode_any Wx_6c11c = Some (Jal 1 92412, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c120 : bv 32 := 0x00050b13.
Lemma Fx_6c120 : fetch_word AsanUbsan.M.loaded_segments (0x6c168 : word) = Some Wx_6c120.
Proof. vm_refl. Qed.
Lemma Dx_6c120 : decode_any Wx_6c120 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c124 : bv 32 := 0xb4050ee3.
Lemma Fx_6c124 : fetch_word AsanUbsan.M.loaded_segments (0x6c16c : word) = Some Wx_6c124.
Proof. vm_refl. Qed.
Lemma Dx_6c124 : decode_any Wx_6c124 = Some (Branch BC_EQ 10 0 7004, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c404 : bv 32 := 0xfd010113.
Lemma Fx_6c404 : fetch_word AsanUbsan.M.loaded_segments (0x6c44c : word) = Some Wx_6c404.
Proof. vm_refl. Qed.
Lemma Dx_6c404 : decode_any Wx_6c404 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c408 : bv 32 := 0x02113423.
Lemma Fx_6c408 : fetch_word AsanUbsan.M.loaded_segments (0x6c450 : word) = Some Wx_6c408.
Proof. vm_refl. Qed.
Lemma Dx_6c408 : decode_any Wx_6c408 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c40c : bv 32 := 0x02813023.
Lemma Fx_6c40c : fetch_word AsanUbsan.M.loaded_segments (0x6c454 : word) = Some Wx_6c40c.
Proof. vm_refl. Qed.
Lemma Dx_6c40c : decode_any Wx_6c40c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c410 : bv 32 := 0x00913c23.
Lemma Fx_6c410 : fetch_word AsanUbsan.M.loaded_segments (0x6c458 : word) = Some Wx_6c410.
Proof. vm_refl. Qed.
Lemma Dx_6c410 : decode_any Wx_6c410 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c414 : bv 32 := 0x01213823.
Lemma Fx_6c414 : fetch_word AsanUbsan.M.loaded_segments (0x6c45c : word) = Some Wx_6c414.
Proof. vm_refl. Qed.
Lemma Dx_6c414 : decode_any Wx_6c414 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c418 : bv 32 := 0x00060413.
Lemma Fx_6c418 : fetch_word AsanUbsan.M.loaded_segments (0x6c460 : word) = Some Wx_6c418.
Proof. vm_refl. Qed.
Lemma Dx_6c418 : decode_any Wx_6c418 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c41c : bv 32 := 0x00058493.
Lemma Fx_6c41c : fetch_word AsanUbsan.M.loaded_segments (0x6c464 : word) = Some Wx_6c41c.
Proof. vm_refl. Qed.
Lemma Dx_6c41c : decode_any Wx_6c41c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c420 : bv 32 := 0x00050913.
Lemma Fx_6c420 : fetch_word AsanUbsan.M.loaded_segments (0x6c468 : word) = Some Wx_6c420.
Proof. vm_refl. Qed.
Lemma Dx_6c420 : decode_any Wx_6c420 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c424 : bv 32 := 0x3081b0ef.
Lemma Fx_6c424 : fetch_word AsanUbsan.M.loaded_segments (0x6c46c : word) = Some Wx_6c424.
Proof. vm_refl. Qed.
Lemma Dx_6c424 : decode_any Wx_6c424 = Some (Jal 1 111368, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c428 : bv 32 := 0x04050863.
Lemma Fx_6c428 : fetch_word AsanUbsan.M.loaded_segments (0x6c470 : word) = Some Wx_6c428.
Proof. vm_refl. Qed.
Lemma Dx_6c428 : decode_any Wx_6c428 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c42c : bv 32 := 0xfffaf517.
Lemma Fx_6c42c : fetch_word AsanUbsan.M.loaded_segments (0x6c474 : word) = Some Wx_6c42c.
Proof. vm_refl. Qed.
Lemma Dx_6c42c : decode_any Wx_6c42c = Some (Auipc 10 1048495, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c430 : bv 32 := 0x1e850513.
Lemma Fx_6c430 : fetch_word AsanUbsan.M.loaded_segments (0x6c478 : word) = Some Wx_6c430.
Proof. vm_refl. Qed.
Lemma Dx_6c430 : decode_any Wx_6c430 = Some (OpImm ALU_ADD 10 10 488, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c434 : bv 32 := 0x00a13423.
Lemma Fx_6c434 : fetch_word AsanUbsan.M.loaded_segments (0x6c47c : word) = Some Wx_6c434.
Proof. vm_refl. Qed.
Lemma Dx_6c434 : decode_any Wx_6c434 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c438 : bv 32 := 0x2041c0ef.
Lemma Fx_6c438 : fetch_word AsanUbsan.M.loaded_segments (0x6c480 : word) = Some Wx_6c438.
Proof. vm_refl. Qed.
Lemma Dx_6c438 : decode_any Wx_6c438 = Some (Jal 1 115204, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c43c : bv 32 := 0x000ea597.
Lemma Fx_6c43c : fetch_word AsanUbsan.M.loaded_segments (0x6c484 : word) = Some Wx_6c43c.
Proof. vm_refl. Qed.
Lemma Dx_6c43c : decode_any Wx_6c43c = Some (Auipc 11 234, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c440 : bv 32 := 0xecc5b303.
Lemma Fx_6c440 : fetch_word AsanUbsan.M.loaded_segments (0x6c488 : word) = Some Wx_6c440.
Proof. vm_refl. Qed.
Lemma Dx_6c440 : decode_any Wx_6c440 = Some (Load SZ8 true 6 11 3788, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c444 : bv 32 := 0x04050c63.
Lemma Fx_6c444 : fetch_word AsanUbsan.M.loaded_segments (0x6c48c : word) = Some Wx_6c444.
Proof. vm_refl. Qed.
Lemma Dx_6c444 : decode_any Wx_6c444 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c448 : bv 32 := 0x00810513.
Lemma Fx_6c448 : fetch_word AsanUbsan.M.loaded_segments (0x6c490 : word) = Some Wx_6c448.
Proof. vm_refl. Qed.
Lemma Dx_6c448 : decode_any Wx_6c448 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c44c : bv 32 := 0x00030593.
Lemma Fx_6c44c : fetch_word AsanUbsan.M.loaded_segments (0x6c494 : word) = Some Wx_6c44c.
Proof. vm_refl. Qed.
Lemma Dx_6c44c : decode_any Wx_6c44c = Some (OpImm ALU_ADD 11 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c450 : bv 32 := 0x00090613.
Lemma Fx_6c450 : fetch_word AsanUbsan.M.loaded_segments (0x6c498 : word) = Some Wx_6c450.
Proof. vm_refl. Qed.
Lemma Dx_6c450 : decode_any Wx_6c450 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c454 : bv 32 := 0x00048693.
Lemma Fx_6c454 : fetch_word AsanUbsan.M.loaded_segments (0x6c49c : word) = Some Wx_6c454.
Proof. vm_refl. Qed.
Lemma Dx_6c454 : decode_any Wx_6c454 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c458 : bv 32 := 0x00040713.
Lemma Fx_6c458 : fetch_word AsanUbsan.M.loaded_segments (0x6c4a0 : word) = Some Wx_6c458.
Proof. vm_refl. Qed.
Lemma Dx_6c458 : decode_any Wx_6c458 = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c45c : bv 32 := 0xf14ff0ef.
Lemma Fx_6c45c : fetch_word AsanUbsan.M.loaded_segments (0x6c4a4 : word) = Some Wx_6c45c.
Proof. vm_refl. Qed.
Lemma Dx_6c45c : decode_any Wx_6c45c = Some (Jal 1 2094868, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c460 : bv 32 := 0x02813083.
Lemma Fx_6c460 : fetch_word AsanUbsan.M.loaded_segments (0x6c4a8 : word) = Some Wx_6c460.
Proof. vm_refl. Qed.
Lemma Dx_6c460 : decode_any Wx_6c460 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c464 : bv 32 := 0x02013403.
Lemma Fx_6c464 : fetch_word AsanUbsan.M.loaded_segments (0x6c4ac : word) = Some Wx_6c464.
Proof. vm_refl. Qed.
Lemma Dx_6c464 : decode_any Wx_6c464 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c468 : bv 32 := 0x01813483.
Lemma Fx_6c468 : fetch_word AsanUbsan.M.loaded_segments (0x6c4b0 : word) = Some Wx_6c468.
Proof. vm_refl. Qed.
Lemma Dx_6c468 : decode_any Wx_6c468 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c46c : bv 32 := 0x01013903.
Lemma Fx_6c46c : fetch_word AsanUbsan.M.loaded_segments (0x6c4b4 : word) = Some Wx_6c46c.
Proof. vm_refl. Qed.
Lemma Dx_6c46c : decode_any Wx_6c46c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c470 : bv 32 := 0x03010113.
Lemma Fx_6c470 : fetch_word AsanUbsan.M.loaded_segments (0x6c4b8 : word) = Some Wx_6c470.
Proof. vm_refl. Qed.
Lemma Dx_6c470 : decode_any Wx_6c470 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c474 : bv 32 := 0x00008067.
Lemma Fx_6c474 : fetch_word AsanUbsan.M.loaded_segments (0x6c4bc : word) = Some Wx_6c474.
Proof. vm_refl. Qed.
Lemma Dx_6c474 : decode_any Wx_6c474 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4c0 : bv 32 := 0xfd010113.
Lemma Fx_6c4c0 : fetch_word AsanUbsan.M.loaded_segments (0x6c508 : word) = Some Wx_6c4c0.
Proof. vm_refl. Qed.
Lemma Dx_6c4c0 : decode_any Wx_6c4c0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4c4 : bv 32 := 0x02113423.
Lemma Fx_6c4c4 : fetch_word AsanUbsan.M.loaded_segments (0x6c50c : word) = Some Wx_6c4c4.
Proof. vm_refl. Qed.
Lemma Dx_6c4c4 : decode_any Wx_6c4c4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4c8 : bv 32 := 0x02813023.
Lemma Fx_6c4c8 : fetch_word AsanUbsan.M.loaded_segments (0x6c510 : word) = Some Wx_6c4c8.
Proof. vm_refl. Qed.
Lemma Dx_6c4c8 : decode_any Wx_6c4c8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4cc : bv 32 := 0x00913c23.
Lemma Fx_6c4cc : fetch_word AsanUbsan.M.loaded_segments (0x6c514 : word) = Some Wx_6c4cc.
Proof. vm_refl. Qed.
Lemma Dx_6c4cc : decode_any Wx_6c4cc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4d0 : bv 32 := 0x01213823.
Lemma Fx_6c4d0 : fetch_word AsanUbsan.M.loaded_segments (0x6c518 : word) = Some Wx_6c4d0.
Proof. vm_refl. Qed.
Lemma Dx_6c4d0 : decode_any Wx_6c4d0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4d4 : bv 32 := 0x00060413.
Lemma Fx_6c4d4 : fetch_word AsanUbsan.M.loaded_segments (0x6c51c : word) = Some Wx_6c4d4.
Proof. vm_refl. Qed.
Lemma Dx_6c4d4 : decode_any Wx_6c4d4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4d8 : bv 32 := 0x00058493.
Lemma Fx_6c4d8 : fetch_word AsanUbsan.M.loaded_segments (0x6c520 : word) = Some Wx_6c4d8.
Proof. vm_refl. Qed.
Lemma Dx_6c4d8 : decode_any Wx_6c4d8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4dc : bv 32 := 0x00050913.
Lemma Fx_6c4dc : fetch_word AsanUbsan.M.loaded_segments (0x6c524 : word) = Some Wx_6c4dc.
Proof. vm_refl. Qed.
Lemma Dx_6c4dc : decode_any Wx_6c4dc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4e0 : bv 32 := 0x24c1b0ef.
Lemma Fx_6c4e0 : fetch_word AsanUbsan.M.loaded_segments (0x6c528 : word) = Some Wx_6c4e0.
Proof. vm_refl. Qed.
Lemma Dx_6c4e0 : decode_any Wx_6c4e0 = Some (Jal 1 111180, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4e4 : bv 32 := 0x04050863.
Lemma Fx_6c4e4 : fetch_word AsanUbsan.M.loaded_segments (0x6c52c : word) = Some Wx_6c4e4.
Proof. vm_refl. Qed.
Lemma Dx_6c4e4 : decode_any Wx_6c4e4 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4e8 : bv 32 := 0xfffaa517.
Lemma Fx_6c4e8 : fetch_word AsanUbsan.M.loaded_segments (0x6c530 : word) = Some Wx_6c4e8.
Proof. vm_refl. Qed.
Lemma Dx_6c4e8 : decode_any Wx_6c4e8 = Some (Auipc 10 1048490, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4ec : bv 32 := 0x89c50513.
Lemma Fx_6c4ec : fetch_word AsanUbsan.M.loaded_segments (0x6c534 : word) = Some Wx_6c4ec.
Proof. vm_refl. Qed.
Lemma Dx_6c4ec : decode_any Wx_6c4ec = Some (OpImm ALU_ADD 10 10 2204, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4f0 : bv 32 := 0x00a13423.
Lemma Fx_6c4f0 : fetch_word AsanUbsan.M.loaded_segments (0x6c538 : word) = Some Wx_6c4f0.
Proof. vm_refl. Qed.
Lemma Dx_6c4f0 : decode_any Wx_6c4f0 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4f4 : bv 32 := 0x1481c0ef.
Lemma Fx_6c4f4 : fetch_word AsanUbsan.M.loaded_segments (0x6c53c : word) = Some Wx_6c4f4.
Proof. vm_refl. Qed.
Lemma Dx_6c4f4 : decode_any Wx_6c4f4 = Some (Jal 1 115016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4f8 : bv 32 := 0x000ea597.
Lemma Fx_6c4f8 : fetch_word AsanUbsan.M.loaded_segments (0x6c540 : word) = Some Wx_6c4f8.
Proof. vm_refl. Qed.
Lemma Dx_6c4f8 : decode_any Wx_6c4f8 = Some (Auipc 11 234, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c4fc : bv 32 := 0xe185b303.
Lemma Fx_6c4fc : fetch_word AsanUbsan.M.loaded_segments (0x6c544 : word) = Some Wx_6c4fc.
Proof. vm_refl. Qed.
Lemma Dx_6c4fc : decode_any Wx_6c4fc = Some (Load SZ8 true 6 11 3608, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c500 : bv 32 := 0x04050c63.
Lemma Fx_6c500 : fetch_word AsanUbsan.M.loaded_segments (0x6c548 : word) = Some Wx_6c500.
Proof. vm_refl. Qed.
Lemma Dx_6c500 : decode_any Wx_6c500 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c504 : bv 32 := 0x00810513.
Lemma Fx_6c504 : fetch_word AsanUbsan.M.loaded_segments (0x6c54c : word) = Some Wx_6c504.
Proof. vm_refl. Qed.
Lemma Dx_6c504 : decode_any Wx_6c504 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c508 : bv 32 := 0x00030593.
Lemma Fx_6c508 : fetch_word AsanUbsan.M.loaded_segments (0x6c550 : word) = Some Wx_6c508.
Proof. vm_refl. Qed.
Lemma Dx_6c508 : decode_any Wx_6c508 = Some (OpImm ALU_ADD 11 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c50c : bv 32 := 0x00090613.
Lemma Fx_6c50c : fetch_word AsanUbsan.M.loaded_segments (0x6c554 : word) = Some Wx_6c50c.
Proof. vm_refl. Qed.
Lemma Dx_6c50c : decode_any Wx_6c50c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c510 : bv 32 := 0x00048693.
Lemma Fx_6c510 : fetch_word AsanUbsan.M.loaded_segments (0x6c558 : word) = Some Wx_6c510.
Proof. vm_refl. Qed.
Lemma Dx_6c510 : decode_any Wx_6c510 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c514 : bv 32 := 0x00040713.
Lemma Fx_6c514 : fetch_word AsanUbsan.M.loaded_segments (0x6c55c : word) = Some Wx_6c514.
Proof. vm_refl. Qed.
Lemma Dx_6c514 : decode_any Wx_6c514 = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c518 : bv 32 := 0xe58ff0ef.
Lemma Fx_6c518 : fetch_word AsanUbsan.M.loaded_segments (0x6c560 : word) = Some Wx_6c518.
Proof. vm_refl. Qed.
Lemma Dx_6c518 : decode_any Wx_6c518 = Some (Jal 1 2094680, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c51c : bv 32 := 0x02813083.
Lemma Fx_6c51c : fetch_word AsanUbsan.M.loaded_segments (0x6c564 : word) = Some Wx_6c51c.
Proof. vm_refl. Qed.
Lemma Dx_6c51c : decode_any Wx_6c51c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c520 : bv 32 := 0x02013403.
Lemma Fx_6c520 : fetch_word AsanUbsan.M.loaded_segments (0x6c568 : word) = Some Wx_6c520.
Proof. vm_refl. Qed.
Lemma Dx_6c520 : decode_any Wx_6c520 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c524 : bv 32 := 0x01813483.
Lemma Fx_6c524 : fetch_word AsanUbsan.M.loaded_segments (0x6c56c : word) = Some Wx_6c524.
Proof. vm_refl. Qed.
Lemma Dx_6c524 : decode_any Wx_6c524 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c528 : bv 32 := 0x01013903.
Lemma Fx_6c528 : fetch_word AsanUbsan.M.loaded_segments (0x6c570 : word) = Some Wx_6c528.
Proof. vm_refl. Qed.
Lemma Dx_6c528 : decode_any Wx_6c528 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c52c : bv 32 := 0x03010113.
Lemma Fx_6c52c : fetch_word AsanUbsan.M.loaded_segments (0x6c574 : word) = Some Wx_6c52c.
Proof. vm_refl. Qed.
Lemma Dx_6c52c : decode_any Wx_6c52c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_6c530 : bv 32 := 0x00008067.
Lemma Fx_6c530 : fetch_word AsanUbsan.M.loaded_segments (0x6c578 : word) = Some Wx_6c530.
Proof. vm_refl. Qed.
Lemma Dx_6c530 : decode_any Wx_6c530 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8772c : bv 32 := 0x000d7517.
Lemma Fx_8772c : fetch_word AsanUbsan.M.loaded_segments (0x87774 : word) = Some Wx_8772c.
Proof. vm_refl. Qed.
Lemma Dx_8772c : decode_any Wx_8772c = Some (Auipc 10 215, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87730 : bv 32 := 0x26450503.
Lemma Fx_87730 : fetch_word AsanUbsan.M.loaded_segments (0x87778 : word) = Some Wx_87730.
Proof. vm_refl. Qed.
Lemma Dx_87730 : decode_any Wx_87730 = Some (Load SZ1 true 10 10 612, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87734 : bv 32 := 0x0230000f.
Lemma Fx_87734 : fetch_word AsanUbsan.M.loaded_segments (0x8777c : word) = Some Wx_87734.
Proof. vm_refl. Qed.
Lemma Dx_87734 : decode_any Wx_87734 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87738 : bv 32 := 0xfff50513.
Lemma Fx_87738 : fetch_word AsanUbsan.M.loaded_segments (0x87780 : word) = Some Wx_87738.
Proof. vm_refl. Qed.
Lemma Dx_87738 : decode_any Wx_87738 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_8773c : bv 32 := 0x00153513.
Lemma Fx_8773c : fetch_word AsanUbsan.M.loaded_segments (0x87784 : word) = Some Wx_8773c.
Proof. vm_refl. Qed.
Lemma Dx_8773c : decode_any Wx_8773c = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_87740 : bv 32 := 0x00008067.
Lemma Fx_87740 : fetch_word AsanUbsan.M.loaded_segments (0x87788 : word) = Some Wx_87740.
Proof. vm_refl. Qed.
Lemma Dx_87740 : decode_any Wx_87740 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

