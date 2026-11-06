(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_56520 : bv 32 := 0x00055597.
Lemma F_56520 : fetch_word Asan.M.loaded_segments (0x56520 : word) = Some W_56520.
Proof. vm_refl. Qed.
Lemma D_56520 : decode_any W_56520 = Some (Auipc 11 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56524 : bv 32 := 0x9605b583.
Lemma F_56524 : fetch_word Asan.M.loaded_segments (0x56524 : word) = Some W_56524.
Proof. vm_refl. Qed.
Lemma D_56524 : decode_any W_56524 = Some (Load SZ8 true 11 11 2400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56528 : bv 32 := 0x0005b583.
Lemma F_56528 : fetch_word Asan.M.loaded_segments (0x56528 : word) = Some W_56528.
Proof. vm_refl. Qed.
Lemma D_56528 : decode_any W_56528 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5652c : bv 32 := 0xfff58613.
Lemma F_5652c : fetch_word Asan.M.loaded_segments (0x5652c : word) = Some W_5652c.
Proof. vm_refl. Qed.
Lemma D_5652c : decode_any W_5652c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56530 : bv 32 := 0x00c5b6b3.
Lemma F_56530 : fetch_word Asan.M.loaded_segments (0x56530 : word) = Some W_56530.
Proof. vm_refl. Qed.
Lemma D_56530 : decode_any W_56530 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56534 : bv 32 := 0xfff68693.
Lemma F_56534 : fetch_word Asan.M.loaded_segments (0x56534 : word) = Some W_56534.
Proof. vm_refl. Qed.
Lemma D_56534 : decode_any W_56534 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56538 : bv 32 := 0x00c6f6b3.
Lemma F_56538 : fetch_word Asan.M.loaded_segments (0x56538 : word) = Some W_56538.
Proof. vm_refl. Qed.
Lemma D_56538 : decode_any W_56538 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5653c : bv 32 := 0x04a6f263.
Lemma F_5653c : fetch_word Asan.M.loaded_segments (0x5653c : word) = Some W_5653c.
Proof. vm_refl. Qed.
Lemma D_5653c : decode_any W_5653c = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56540 : bv 32 := 0x00055697.
Lemma F_56540 : fetch_word Asan.M.loaded_segments (0x56540 : word) = Some W_56540.
Proof. vm_refl. Qed.
Lemma D_56540 : decode_any W_56540 = Some (Auipc 13 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56544 : bv 32 := 0x9486b683.
Lemma F_56544 : fetch_word Asan.M.loaded_segments (0x56544 : word) = Some W_56544.
Proof. vm_refl. Qed.
Lemma D_56544 : decode_any W_56544 = Some (Load SZ8 true 13 13 2376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56548 : bv 32 := 0x00055717.
Lemma F_56548 : fetch_word Asan.M.loaded_segments (0x56548 : word) = Some W_56548.
Proof. vm_refl. Qed.
Lemma D_56548 : decode_any W_56548 = Some (Auipc 14 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5654c : bv 32 := 0x94873703.
Lemma F_5654c : fetch_word Asan.M.loaded_segments (0x5654c : word) = Some W_5654c.
Proof. vm_refl. Qed.
Lemma D_5654c : decode_any W_5654c = Some (Load SZ8 true 14 14 2376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56550 : bv 32 := 0x0006b803.
Lemma F_56550 : fetch_word Asan.M.loaded_segments (0x56550 : word) = Some W_56550.
Proof. vm_refl. Qed.
Lemma D_56550 : decode_any W_56550 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56554 : bv 32 := 0x00073683.
Lemma F_56554 : fetch_word Asan.M.loaded_segments (0x56554 : word) = Some W_56554.
Proof. vm_refl. Qed.
Lemma D_56554 : decode_any W_56554 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56558 : bv 32 := 0xfff80793.
Lemma F_56558 : fetch_word Asan.M.loaded_segments (0x56558 : word) = Some W_56558.
Proof. vm_refl. Qed.
Lemma D_56558 : decode_any W_56558 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5655c : bv 32 := 0x00a7f463.
Lemma F_5655c : fetch_word Asan.M.loaded_segments (0x5655c : word) = Some W_5655c.
Proof. vm_refl. Qed.
Lemma D_5655c : decode_any W_5655c = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56560 : bv 32 := 0x02a6f063.
Lemma F_56560 : fetch_word Asan.M.loaded_segments (0x56560 : word) = Some W_56560.
Proof. vm_refl. Qed.
Lemma D_56560 : decode_any W_56560 = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56564 : bv 32 := 0x00055717.
Lemma F_56564 : fetch_word Asan.M.loaded_segments (0x56564 : word) = Some W_56564.
Proof. vm_refl. Qed.
Lemma D_56564 : decode_any W_56564 = Some (Auipc 14 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56568 : bv 32 := 0x93473703.
Lemma F_56568 : fetch_word Asan.M.loaded_segments (0x56568 : word) = Some W_56568.
Proof. vm_refl. Qed.
Lemma D_56568 : decode_any W_56568 = Some (Load SZ8 true 14 14 2356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5656c : bv 32 := 0x00073283.
Lemma F_5656c : fetch_word Asan.M.loaded_segments (0x5656c : word) = Some W_5656c.
Proof. vm_refl. Qed.
Lemma D_5656c : decode_any W_5656c = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56570 : bv 32 := 0x0032d713.
Lemma F_56570 : fetch_word Asan.M.loaded_segments (0x56570 : word) = Some W_56570.
Proof. vm_refl. Qed.
Lemma D_56570 : decode_any W_56570 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56574 : bv 32 := 0x00b708b3.
Lemma F_56574 : fetch_word Asan.M.loaded_segments (0x56574 : word) = Some W_56574.
Proof. vm_refl. Qed.
Lemma D_56574 : decode_any W_56574 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56578 : bv 32 := 0x00a2ea63.
Lemma F_56578 : fetch_word Asan.M.loaded_segments (0x56578 : word) = Some W_56578.
Proof. vm_refl. Qed.
Lemma D_56578 : decode_any W_56578 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5657c : bv 32 := 0x00a8f863.
Lemma F_5657c : fetch_word Asan.M.loaded_segments (0x5657c : word) = Some W_5657c.
Proof. vm_refl. Qed.
Lemma D_5657c : decode_any W_5657c = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56580 : bv 32 := 0x00355513.
Lemma F_56580 : fetch_word Asan.M.loaded_segments (0x56580 : word) = Some W_56580.
Proof. vm_refl. Qed.
Lemma D_56580 : decode_any W_56580 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56584 : bv 32 := 0x00a58533.
Lemma F_56584 : fetch_word Asan.M.loaded_segments (0x56584 : word) = Some W_56584.
Proof. vm_refl. Qed.
Lemma D_56584 : decode_any W_56584 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56588 : bv 32 := 0x00008067.
Lemma F_56588 : fetch_word Asan.M.loaded_segments (0x56588 : word) = Some W_56588.
Proof. vm_refl. Qed.
Lemma D_56588 : decode_any W_56588 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569ac : bv 32 := 0xfc010113.
Lemma F_569ac : fetch_word Asan.M.loaded_segments (0x569ac : word) = Some W_569ac.
Proof. vm_refl. Qed.
Lemma D_569ac : decode_any W_569ac = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569b0 : bv 32 := 0x02113c23.
Lemma F_569b0 : fetch_word Asan.M.loaded_segments (0x569b0 : word) = Some W_569b0.
Proof. vm_refl. Qed.
Lemma D_569b0 : decode_any W_569b0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569b4 : bv 32 := 0x02813823.
Lemma F_569b4 : fetch_word Asan.M.loaded_segments (0x569b4 : word) = Some W_569b4.
Proof. vm_refl. Qed.
Lemma D_569b4 : decode_any W_569b4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569b8 : bv 32 := 0x02913423.
Lemma F_569b8 : fetch_word Asan.M.loaded_segments (0x569b8 : word) = Some W_569b8.
Proof. vm_refl. Qed.
Lemma D_569b8 : decode_any W_569b8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569bc : bv 32 := 0x03213023.
Lemma F_569bc : fetch_word Asan.M.loaded_segments (0x569bc : word) = Some W_569bc.
Proof. vm_refl. Qed.
Lemma D_569bc : decode_any W_569bc = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569c0 : bv 32 := 0x01313c23.
Lemma F_569c0 : fetch_word Asan.M.loaded_segments (0x569c0 : word) = Some W_569c0.
Proof. vm_refl. Qed.
Lemma D_569c0 : decode_any W_569c0 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569c4 : bv 32 := 0x01413823.
Lemma F_569c4 : fetch_word Asan.M.loaded_segments (0x569c4 : word) = Some W_569c4.
Proof. vm_refl. Qed.
Lemma D_569c4 : decode_any W_569c4 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569c8 : bv 32 := 0x01513423.
Lemma F_569c8 : fetch_word Asan.M.loaded_segments (0x569c8 : word) = Some W_569c8.
Proof. vm_refl. Qed.
Lemma D_569c8 : decode_any W_569c8 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569cc : bv 32 := 0x14058c63.
Lemma F_569cc : fetch_word Asan.M.loaded_segments (0x569cc : word) = Some W_569cc.
Proof. vm_refl. Qed.
Lemma D_569cc : decode_any W_569cc = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569d0 : bv 32 := 0x00058493.
Lemma F_569d0 : fetch_word Asan.M.loaded_segments (0x569d0 : word) = Some W_569d0.
Proof. vm_refl. Qed.
Lemma D_569d0 : decode_any W_569d0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569d4 : bv 32 := 0x00050413.
Lemma F_569d4 : fetch_word Asan.M.loaded_segments (0x569d4 : word) = Some W_569d4.
Proof. vm_refl. Qed.
Lemma D_569d4 : decode_any W_569d4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569d8 : bv 32 := 0x00054517.
Lemma F_569d8 : fetch_word Asan.M.loaded_segments (0x569d8 : word) = Some W_569d8.
Proof. vm_refl. Qed.
Lemma D_569d8 : decode_any W_569d8 = Some (Auipc 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569dc : bv 32 := 0x4a853a83.
Lemma F_569dc : fetch_word Asan.M.loaded_segments (0x569dc : word) = Some W_569dc.
Proof. vm_refl. Qed.
Lemma D_569dc : decode_any W_569dc = Some (Load SZ8 true 21 10 1192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569e0 : bv 32 := 0x000ab583.
Lemma F_569e0 : fetch_word Asan.M.loaded_segments (0x569e0 : word) = Some W_569e0.
Proof. vm_refl. Qed.
Lemma D_569e0 : decode_any W_569e0 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569e4 : bv 32 := 0xfff58513.
Lemma F_569e4 : fetch_word Asan.M.loaded_segments (0x569e4 : word) = Some W_569e4.
Proof. vm_refl. Qed.
Lemma D_569e4 : decode_any W_569e4 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569e8 : bv 32 := 0x00a5b633.
Lemma F_569e8 : fetch_word Asan.M.loaded_segments (0x569e8 : word) = Some W_569e8.
Proof. vm_refl. Qed.
Lemma D_569e8 : decode_any W_569e8 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569ec : bv 32 := 0xfff60613.
Lemma F_569ec : fetch_word Asan.M.loaded_segments (0x569ec : word) = Some W_569ec.
Proof. vm_refl. Qed.
Lemma D_569ec : decode_any W_569ec = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569f0 : bv 32 := 0x00a67633.
Lemma F_569f0 : fetch_word Asan.M.loaded_segments (0x569f0 : word) = Some W_569f0.
Proof. vm_refl. Qed.
Lemma D_569f0 : decode_any W_569f0 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569f4 : bv 32 := 0x04867263.
Lemma F_569f4 : fetch_word Asan.M.loaded_segments (0x569f4 : word) = Some W_569f4.
Proof. vm_refl. Qed.
Lemma D_569f4 : decode_any W_569f4 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569f8 : bv 32 := 0x00054697.
Lemma F_569f8 : fetch_word Asan.M.loaded_segments (0x569f8 : word) = Some W_569f8.
Proof. vm_refl. Qed.
Lemma D_569f8 : decode_any W_569f8 = Some (Auipc 13 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_569fc : bv 32 := 0x4906b683.
Lemma F_569fc : fetch_word Asan.M.loaded_segments (0x569fc : word) = Some W_569fc.
Proof. vm_refl. Qed.
Lemma D_569fc : decode_any W_569fc = Some (Load SZ8 true 13 13 1168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a00 : bv 32 := 0x00054717.
Lemma F_56a00 : fetch_word Asan.M.loaded_segments (0x56a00 : word) = Some W_56a00.
Proof. vm_refl. Qed.
Lemma D_56a00 : decode_any W_56a00 = Some (Auipc 14 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a04 : bv 32 := 0x49073703.
Lemma F_56a04 : fetch_word Asan.M.loaded_segments (0x56a04 : word) = Some W_56a04.
Proof. vm_refl. Qed.
Lemma D_56a04 : decode_any W_56a04 = Some (Load SZ8 true 14 14 1168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a08 : bv 32 := 0x0006b803.
Lemma F_56a08 : fetch_word Asan.M.loaded_segments (0x56a08 : word) = Some W_56a08.
Proof. vm_refl. Qed.
Lemma D_56a08 : decode_any W_56a08 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a0c : bv 32 := 0x00073683.
Lemma F_56a0c : fetch_word Asan.M.loaded_segments (0x56a0c : word) = Some W_56a0c.
Proof. vm_refl. Qed.
Lemma D_56a0c : decode_any W_56a0c = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a10 : bv 32 := 0xfff80793.
Lemma F_56a10 : fetch_word Asan.M.loaded_segments (0x56a10 : word) = Some W_56a10.
Proof. vm_refl. Qed.
Lemma D_56a10 : decode_any W_56a10 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a14 : bv 32 := 0x0087f463.
Lemma F_56a14 : fetch_word Asan.M.loaded_segments (0x56a14 : word) = Some W_56a14.
Proof. vm_refl. Qed.
Lemma D_56a14 : decode_any W_56a14 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a18 : bv 32 := 0x0286f063.
Lemma F_56a18 : fetch_word Asan.M.loaded_segments (0x56a18 : word) = Some W_56a18.
Proof. vm_refl. Qed.
Lemma D_56a18 : decode_any W_56a18 = Some (Branch BC_GEU 13 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a1c : bv 32 := 0x00054717.
Lemma F_56a1c : fetch_word Asan.M.loaded_segments (0x56a1c : word) = Some W_56a1c.
Proof. vm_refl. Qed.
Lemma D_56a1c : decode_any W_56a1c = Some (Auipc 14 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a20 : bv 32 := 0x47c73703.
Lemma F_56a20 : fetch_word Asan.M.loaded_segments (0x56a20 : word) = Some W_56a20.
Proof. vm_refl. Qed.
Lemma D_56a20 : decode_any W_56a20 = Some (Load SZ8 true 14 14 1148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a24 : bv 32 := 0x00073283.
Lemma F_56a24 : fetch_word Asan.M.loaded_segments (0x56a24 : word) = Some W_56a24.
Proof. vm_refl. Qed.
Lemma D_56a24 : decode_any W_56a24 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a28 : bv 32 := 0x0032d713.
Lemma F_56a28 : fetch_word Asan.M.loaded_segments (0x56a28 : word) = Some W_56a28.
Proof. vm_refl. Qed.
Lemma D_56a28 : decode_any W_56a28 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a2c : bv 32 := 0x00b708b3.
Lemma F_56a2c : fetch_word Asan.M.loaded_segments (0x56a2c : word) = Some W_56a2c.
Proof. vm_refl. Qed.
Lemma D_56a2c : decode_any W_56a2c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a30 : bv 32 := 0x1282e063.
Lemma F_56a30 : fetch_word Asan.M.loaded_segments (0x56a30 : word) = Some W_56a30.
Proof. vm_refl. Qed.
Lemma D_56a30 : decode_any W_56a30 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a34 : bv 32 := 0x1088fe63.
Lemma F_56a34 : fetch_word Asan.M.loaded_segments (0x56a34 : word) = Some W_56a34.
Proof. vm_refl. Qed.
Lemma D_56a34 : decode_any W_56a34 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a38 : bv 32 := 0x00848933.
Lemma F_56a38 : fetch_word Asan.M.loaded_segments (0x56a38 : word) = Some W_56a38.
Proof. vm_refl. Qed.
Lemma D_56a38 : decode_any W_56a38 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a3c : bv 32 := 0x05267263.
Lemma F_56a3c : fetch_word Asan.M.loaded_segments (0x56a3c : word) = Some W_56a3c.
Proof. vm_refl. Qed.
Lemma D_56a3c : decode_any W_56a3c = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a40 : bv 32 := 0x00054617.
Lemma F_56a40 : fetch_word Asan.M.loaded_segments (0x56a40 : word) = Some W_56a40.
Proof. vm_refl. Qed.
Lemma D_56a40 : decode_any W_56a40 = Some (Auipc 12 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a44 : bv 32 := 0x44863603.
Lemma F_56a44 : fetch_word Asan.M.loaded_segments (0x56a44 : word) = Some W_56a44.
Proof. vm_refl. Qed.
Lemma D_56a44 : decode_any W_56a44 = Some (Load SZ8 true 12 12 1096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a48 : bv 32 := 0x00054697.
Lemma F_56a48 : fetch_word Asan.M.loaded_segments (0x56a48 : word) = Some W_56a48.
Proof. vm_refl. Qed.
Lemma D_56a48 : decode_any W_56a48 = Some (Auipc 13 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a4c : bv 32 := 0x4486b683.
Lemma F_56a4c : fetch_word Asan.M.loaded_segments (0x56a4c : word) = Some W_56a4c.
Proof. vm_refl. Qed.
Lemma D_56a4c : decode_any W_56a4c = Some (Load SZ8 true 13 13 1096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a50 : bv 32 := 0x00063783.
Lemma F_56a50 : fetch_word Asan.M.loaded_segments (0x56a50 : word) = Some W_56a50.
Proof. vm_refl. Qed.
Lemma D_56a50 : decode_any W_56a50 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a54 : bv 32 := 0x0006b603.
Lemma F_56a54 : fetch_word Asan.M.loaded_segments (0x56a54 : word) = Some W_56a54.
Proof. vm_refl. Qed.
Lemma D_56a54 : decode_any W_56a54 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a58 : bv 32 := 0xfff78713.
Lemma F_56a58 : fetch_word Asan.M.loaded_segments (0x56a58 : word) = Some W_56a58.
Proof. vm_refl. Qed.
Lemma D_56a58 : decode_any W_56a58 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a5c : bv 32 := 0x01277463.
Lemma F_56a5c : fetch_word Asan.M.loaded_segments (0x56a5c : word) = Some W_56a5c.
Proof. vm_refl. Qed.
Lemma D_56a5c : decode_any W_56a5c = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a60 : bv 32 := 0x03267063.
Lemma F_56a60 : fetch_word Asan.M.loaded_segments (0x56a60 : word) = Some W_56a60.
Proof. vm_refl. Qed.
Lemma D_56a60 : decode_any W_56a60 = Some (Branch BC_GEU 12 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a64 : bv 32 := 0x00054697.
Lemma F_56a64 : fetch_word Asan.M.loaded_segments (0x56a64 : word) = Some W_56a64.
Proof. vm_refl. Qed.
Lemma D_56a64 : decode_any W_56a64 = Some (Auipc 13 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a68 : bv 32 := 0x4346b683.
Lemma F_56a68 : fetch_word Asan.M.loaded_segments (0x56a68 : word) = Some W_56a68.
Proof. vm_refl. Qed.
Lemma D_56a68 : decode_any W_56a68 = Some (Load SZ8 true 13 13 1076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a6c : bv 32 := 0x0006b883.
Lemma F_56a6c : fetch_word Asan.M.loaded_segments (0x56a6c : word) = Some W_56a6c.
Proof. vm_refl. Qed.
Lemma D_56a6c : decode_any W_56a6c = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a70 : bv 32 := 0x0038d693.
Lemma F_56a70 : fetch_word Asan.M.loaded_segments (0x56a70 : word) = Some W_56a70.
Proof. vm_refl. Qed.
Lemma D_56a70 : decode_any W_56a70 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a74 : bv 32 := 0x00b68833.
Lemma F_56a74 : fetch_word Asan.M.loaded_segments (0x56a74 : word) = Some W_56a74.
Proof. vm_refl. Qed.
Lemma D_56a74 : decode_any W_56a74 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a78 : bv 32 := 0x1328e463.
Lemma F_56a78 : fetch_word Asan.M.loaded_segments (0x56a78 : word) = Some W_56a78.
Proof. vm_refl. Qed.
Lemma D_56a78 : decode_any W_56a78 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a7c : bv 32 := 0x13287263.
Lemma F_56a7c : fetch_word Asan.M.loaded_segments (0x56a7c : word) = Some W_56a7c.
Proof. vm_refl. Qed.
Lemma D_56a7c : decode_any W_56a7c = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a80 : bv 32 := 0x23247863.
Lemma F_56a80 : fetch_word Asan.M.loaded_segments (0x56a80 : word) = Some W_56a80.
Proof. vm_refl. Qed.
Lemma D_56a80 : decode_any W_56a80 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a84 : bv 32 := 0x00740513.
Lemma F_56a84 : fetch_word Asan.M.loaded_segments (0x56a84 : word) = Some W_56a84.
Proof. vm_refl. Qed.
Lemma D_56a84 : decode_any W_56a84 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a88 : bv 32 := 0xff857513.
Lemma F_56a88 : fetch_word Asan.M.loaded_segments (0x56a88 : word) = Some W_56a88.
Proof. vm_refl. Qed.
Lemma D_56a88 : decode_any W_56a88 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a8c : bv 32 := 0xff897a13.
Lemma F_56a8c : fetch_word Asan.M.loaded_segments (0x56a8c : word) = Some W_56a8c.
Proof. vm_refl. Qed.
Lemma D_56a8c : decode_any W_56a8c = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a90 : bv 32 := 0xa91ff0ef.
Lemma F_56a90 : fetch_word Asan.M.loaded_segments (0x56a90 : word) = Some W_56a90.
Proof. vm_refl. Qed.
Lemma D_56a90 : decode_any W_56a90 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a94 : bv 32 := 0x00050993.
Lemma F_56a94 : fetch_word Asan.M.loaded_segments (0x56a94 : word) = Some W_56a94.
Proof. vm_refl. Qed.
Lemma D_56a94 : decode_any W_56a94 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a98 : bv 32 := 0x000a0513.
Lemma F_56a98 : fetch_word Asan.M.loaded_segments (0x56a98 : word) = Some W_56a98.
Proof. vm_refl. Qed.
Lemma D_56a98 : decode_any W_56a98 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56a9c : bv 32 := 0xa85ff0ef.
Lemma F_56a9c : fetch_word Asan.M.loaded_segments (0x56a9c : word) = Some W_56a9c.
Proof. vm_refl. Qed.
Lemma D_56a9c : decode_any W_56a9c = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56aa0 : bv 32 := 0x000ab583.
Lemma F_56aa0 : fetch_word Asan.M.loaded_segments (0x56aa0 : word) = Some W_56aa0.
Proof. vm_refl. Qed.
Lemma D_56aa0 : decode_any W_56aa0 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56aa4 : bv 32 := 0x00345613.
Lemma F_56aa4 : fetch_word Asan.M.loaded_segments (0x56aa4 : word) = Some W_56aa4.
Proof. vm_refl. Qed.
Lemma D_56aa4 : decode_any W_56aa4 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56aa8 : bv 32 := 0x00c58633.
Lemma F_56aa8 : fetch_word Asan.M.loaded_segments (0x56aa8 : word) = Some W_56aa8.
Proof. vm_refl. Qed.
Lemma D_56aa8 : decode_any W_56aa8 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56aac : bv 32 := 0x00060603.
Lemma F_56aac : fetch_word Asan.M.loaded_segments (0x56aac : word) = Some W_56aac.
Proof. vm_refl. Qed.
Lemma D_56aac : decode_any W_56aac = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ab0 : bv 32 := 0x00060663.
Lemma F_56ab0 : fetch_word Asan.M.loaded_segments (0x56ab0 : word) = Some W_56ab0.
Proof. vm_refl. Qed.
Lemma D_56ab0 : decode_any W_56ab0 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ab4 : bv 32 := 0x00747693.
Lemma F_56ab4 : fetch_word Asan.M.loaded_segments (0x56ab4 : word) = Some W_56ab4.
Proof. vm_refl. Qed.
Lemma D_56ab4 : decode_any W_56ab4 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ab8 : bv 32 := 0x02c6d063.
Lemma F_56ab8 : fetch_word Asan.M.loaded_segments (0x56ab8 : word) = Some W_56ab8.
Proof. vm_refl. Qed.
Lemma D_56ab8 : decode_any W_56ab8 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56abc : bv 32 := 0xfff90913.
Lemma F_56abc : fetch_word Asan.M.loaded_segments (0x56abc : word) = Some W_56abc.
Proof. vm_refl. Qed.
Lemma D_56abc : decode_any W_56abc = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ac0 : bv 32 := 0x00395613.
Lemma F_56ac0 : fetch_word Asan.M.loaded_segments (0x56ac0 : word) = Some W_56ac0.
Proof. vm_refl. Qed.
Lemma D_56ac0 : decode_any W_56ac0 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ac4 : bv 32 := 0x00c585b3.
Lemma F_56ac4 : fetch_word Asan.M.loaded_segments (0x56ac4 : word) = Some W_56ac4.
Proof. vm_refl. Qed.
Lemma D_56ac4 : decode_any W_56ac4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ac8 : bv 32 := 0x00058583.
Lemma F_56ac8 : fetch_word Asan.M.loaded_segments (0x56ac8 : word) = Some W_56ac8.
Proof. vm_refl. Qed.
Lemma D_56ac8 : decode_any W_56ac8 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56acc : bv 32 := 0x04058263.
Lemma F_56acc : fetch_word Asan.M.loaded_segments (0x56acc : word) = Some W_56acc.
Proof. vm_refl. Qed.
Lemma D_56acc : decode_any W_56acc = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ad0 : bv 32 := 0x00797613.
Lemma F_56ad0 : fetch_word Asan.M.loaded_segments (0x56ad0 : word) = Some W_56ad0.
Proof. vm_refl. Qed.
Lemma D_56ad0 : decode_any W_56ad0 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ad4 : bv 32 := 0x02b64e63.
Lemma F_56ad4 : fetch_word Asan.M.loaded_segments (0x56ad4 : word) = Some W_56ad4.
Proof. vm_refl. Qed.
Lemma D_56ad4 : decode_any W_56ad4 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ad8 : bv 32 := 0x000ab503.
Lemma F_56ad8 : fetch_word Asan.M.loaded_segments (0x56ad8 : word) = Some W_56ad8.
Proof. vm_refl. Qed.
Lemma D_56ad8 : decode_any W_56ad8 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56adc : bv 32 := 0x00040593.
Lemma F_56adc : fetch_word Asan.M.loaded_segments (0x56adc : word) = Some W_56adc.
Proof. vm_refl. Qed.
Lemma D_56adc : decode_any W_56adc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ae0 : bv 32 := 0x0140006f.
Lemma F_56ae0 : fetch_word Asan.M.loaded_segments (0x56ae0 : word) = Some W_56ae0.
Proof. vm_refl. Qed.
Lemma D_56ae0 : decode_any W_56ae0 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ae4 : bv 32 := 0x00140413.
Lemma F_56ae4 : fetch_word Asan.M.loaded_segments (0x56ae4 : word) = Some W_56ae4.
Proof. vm_refl. Qed.
Lemma D_56ae4 : decode_any W_56ae4 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56ae8 : bv 32 := 0xfff48493.
Lemma F_56ae8 : fetch_word Asan.M.loaded_segments (0x56ae8 : word) = Some W_56ae8.
Proof. vm_refl. Qed.
Lemma D_56ae8 : decode_any W_56ae8 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56aec : bv 32 := 0x00158593.
Lemma F_56aec : fetch_word Asan.M.loaded_segments (0x56aec : word) = Some W_56aec.
Proof. vm_refl. Qed.
Lemma D_56aec : decode_any W_56aec = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56af0 : bv 32 := 0x1e048063.
Lemma F_56af0 : fetch_word Asan.M.loaded_segments (0x56af0 : word) = Some W_56af0.
Proof. vm_refl. Qed.
Lemma D_56af0 : decode_any W_56af0 = Some (Branch BC_EQ 9 0 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56af4 : bv 32 := 0x00345613.
Lemma F_56af4 : fetch_word Asan.M.loaded_segments (0x56af4 : word) = Some W_56af4.
Proof. vm_refl. Qed.
Lemma D_56af4 : decode_any W_56af4 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56af8 : bv 32 := 0x00c50633.
Lemma F_56af8 : fetch_word Asan.M.loaded_segments (0x56af8 : word) = Some W_56af8.
Proof. vm_refl. Qed.
Lemma D_56af8 : decode_any W_56af8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56afc : bv 32 := 0x00060603.
Lemma F_56afc : fetch_word Asan.M.loaded_segments (0x56afc : word) = Some W_56afc.
Proof. vm_refl. Qed.
Lemma D_56afc : decode_any W_56afc = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b00 : bv 32 := 0xfe0602e3.
Lemma F_56b00 : fetch_word Asan.M.loaded_segments (0x56b00 : word) = Some W_56b00.
Proof. vm_refl. Qed.
Lemma D_56b00 : decode_any W_56b00 = Some (Branch BC_EQ 12 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b04 : bv 32 := 0x0075f693.
Lemma F_56b04 : fetch_word Asan.M.loaded_segments (0x56b04 : word) = Some W_56b04.
Proof. vm_refl. Qed.
Lemma D_56b04 : decode_any W_56b04 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b08 : bv 32 := 0xfcc6cee3.
Lemma F_56b08 : fetch_word Asan.M.loaded_segments (0x56b08 : word) = Some W_56b08.
Proof. vm_refl. Qed.
Lemma D_56b08 : decode_any W_56b08 = Some (Branch BC_LT 13 12 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b0c : bv 32 := 0x01c0006f.
Lemma F_56b0c : fetch_word Asan.M.loaded_segments (0x56b0c : word) = Some W_56b0c.
Proof. vm_refl. Qed.
Lemma D_56b0c : decode_any W_56b0c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b10 : bv 32 := 0x00a9fa63.
Lemma F_56b10 : fetch_word Asan.M.loaded_segments (0x56b10 : word) = Some W_56b10.
Proof. vm_refl. Qed.
Lemma D_56b10 : decode_any W_56b10 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b14 : bv 32 := 0x413505b3.
Lemma F_56b14 : fetch_word Asan.M.loaded_segments (0x56b14 : word) = Some W_56b14.
Proof. vm_refl. Qed.
Lemma D_56b14 : decode_any W_56b14 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b18 : bv 32 := 0x00098513.
Lemma F_56b18 : fetch_word Asan.M.loaded_segments (0x56b18 : word) = Some W_56b18.
Proof. vm_refl. Qed.
Lemma D_56b18 : decode_any W_56b18 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b1c : bv 32 := 0x3d10f0ef.
Lemma F_56b1c : fetch_word Asan.M.loaded_segments (0x56b1c : word) = Some W_56b1c.
Proof. vm_refl. Qed.
Lemma D_56b1c : decode_any W_56b1c = Some (Jal 1 64464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b20 : bv 32 := 0xfa050ce3.
Lemma F_56b20 : fetch_word Asan.M.loaded_segments (0x56b20 : word) = Some W_56b20.
Proof. vm_refl. Qed.
Lemma D_56b20 : decode_any W_56b20 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b24 : bv 32 := 0x00000413.
Lemma F_56b24 : fetch_word Asan.M.loaded_segments (0x56b24 : word) = Some W_56b24.
Proof. vm_refl. Qed.
Lemma D_56b24 : decode_any W_56b24 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b28 : bv 32 := 0x00040513.
Lemma F_56b28 : fetch_word Asan.M.loaded_segments (0x56b28 : word) = Some W_56b28.
Proof. vm_refl. Qed.
Lemma D_56b28 : decode_any W_56b28 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b2c : bv 32 := 0x03813083.
Lemma F_56b2c : fetch_word Asan.M.loaded_segments (0x56b2c : word) = Some W_56b2c.
Proof. vm_refl. Qed.
Lemma D_56b2c : decode_any W_56b2c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b30 : bv 32 := 0x03013403.
Lemma F_56b30 : fetch_word Asan.M.loaded_segments (0x56b30 : word) = Some W_56b30.
Proof. vm_refl. Qed.
Lemma D_56b30 : decode_any W_56b30 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b34 : bv 32 := 0x02813483.
Lemma F_56b34 : fetch_word Asan.M.loaded_segments (0x56b34 : word) = Some W_56b34.
Proof. vm_refl. Qed.
Lemma D_56b34 : decode_any W_56b34 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b38 : bv 32 := 0x02013903.
Lemma F_56b38 : fetch_word Asan.M.loaded_segments (0x56b38 : word) = Some W_56b38.
Proof. vm_refl. Qed.
Lemma D_56b38 : decode_any W_56b38 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b3c : bv 32 := 0x01813983.
Lemma F_56b3c : fetch_word Asan.M.loaded_segments (0x56b3c : word) = Some W_56b3c.
Proof. vm_refl. Qed.
Lemma D_56b3c : decode_any W_56b3c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b40 : bv 32 := 0x01013a03.
Lemma F_56b40 : fetch_word Asan.M.loaded_segments (0x56b40 : word) = Some W_56b40.
Proof. vm_refl. Qed.
Lemma D_56b40 : decode_any W_56b40 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b44 : bv 32 := 0x00813a83.
Lemma F_56b44 : fetch_word Asan.M.loaded_segments (0x56b44 : word) = Some W_56b44.
Proof. vm_refl. Qed.
Lemma D_56b44 : decode_any W_56b44 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b48 : bv 32 := 0x04010113.
Lemma F_56b48 : fetch_word Asan.M.loaded_segments (0x56b48 : word) = Some W_56b48.
Proof. vm_refl. Qed.
Lemma D_56b48 : decode_any W_56b48 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b4c : bv 32 := 0x00008067.
Lemma F_56b4c : fetch_word Asan.M.loaded_segments (0x56b4c : word) = Some W_56b4c.
Proof. vm_refl. Qed.
Lemma D_56b4c : decode_any W_56b4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56b50 : bv 32 := 0x00054297.
Lemma F_56b50 : fetch_word Asan.M.loaded_segments (0x56b50 : word) = Some W_56b50.
Proof. vm_refl. Qed.
Lemma D_56b50 : decode_any W_56b50 = Some (Auipc 5 84, 4%Z).
Proof. vm_refl. Qed.
