(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_224ec : bv 32 := 0xfffee197.
Lemma F_224ec : fetch_word Plain.M.loaded_segments (0x224ec : word) = Some W_224ec.
Proof. vm_refl. Qed.
Lemma D_224ec : decode_any W_224ec = Some (Auipc 3 1048558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_224f0 : bv 32 := 0x31418193.
Lemma F_224f0 : fetch_word Plain.M.loaded_segments (0x224f0 : word) = Some W_224f0.
Proof. vm_refl. Qed.
Lemma D_224f0 : decode_any W_224f0 = Some (OpImm ALU_ADD 3 3 788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_224f4 : bv 32 := 0x00010513.
Lemma F_224f4 : fetch_word Plain.M.loaded_segments (0x224f4 : word) = Some W_224f4.
Proof. vm_refl. Qed.
Lemma D_224f4 : decode_any W_224f4 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_224f8 : bv 32 := 0xfffde597.
Lemma F_224f8 : fetch_word Plain.M.loaded_segments (0x224f8 : word) = Some W_224f8.
Proof. vm_refl. Qed.
Lemma D_224f8 : decode_any W_224f8 = Some (Auipc 11 1048542, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_224fc : bv 32 := 0xb0858593.
Lemma F_224fc : fetch_word Plain.M.loaded_segments (0x224fc : word) = Some W_224fc.
Proof. vm_refl. Qed.
Lemma D_224fc : decode_any W_224fc = Some (OpImm ALU_ADD 11 11 2824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22500 : bv 32 := 0xff017113.
Lemma F_22500 : fetch_word Plain.M.loaded_segments (0x22500 : word) = Some W_22500.
Proof. vm_refl. Qed.
Lemma D_22500 : decode_any W_22500 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22504 : bv 32 := 0x0040006f.
Lemma F_22504 : fetch_word Plain.M.loaded_segments (0x22504 : word) = Some W_22504.
Proof. vm_refl. Qed.
Lemma D_22504 : decode_any W_22504 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22508 : bv 32 := 0x00052583.
Lemma F_22508 : fetch_word Plain.M.loaded_segments (0x22508 : word) = Some W_22508.
Proof. vm_refl. Qed.
Lemma D_22508 : decode_any W_22508 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2250c : bv 32 := 0x00041617.
Lemma F_2250c : fetch_word Plain.M.loaded_segments (0x2250c : word) = Some W_2250c.
Proof. vm_refl. Qed.
Lemma D_2250c : decode_any W_2250c = Some (Auipc 12 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22510 : bv 32 := 0x00041697.
Lemma F_22510 : fetch_word Plain.M.loaded_segments (0x22510 : word) = Some W_22510.
Proof. vm_refl. Qed.
Lemma D_22510 : decode_any W_22510 = Some (Auipc 13 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22514 : bv 32 := 0x00041717.
Lemma F_22514 : fetch_word Plain.M.loaded_segments (0x22514 : word) = Some W_22514.
Proof. vm_refl. Qed.
Lemma D_22514 : decode_any W_22514 = Some (Auipc 14 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22518 : bv 32 := 0x76463783.
Lemma F_22518 : fetch_word Plain.M.loaded_segments (0x22518 : word) = Some W_22518.
Proof. vm_refl. Qed.
Lemma D_22518 : decode_any W_22518 = Some (Load SZ8 true 15 12 1892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2251c : bv 32 := 0x7686b683.
Lemma F_2251c : fetch_word Plain.M.loaded_segments (0x2251c : word) = Some W_2251c.
Proof. vm_refl. Qed.
Lemma D_2251c : decode_any W_2251c = Some (Load SZ8 true 13 13 1896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22520 : bv 32 := 0x76c73703.
Lemma F_22520 : fetch_word Plain.M.loaded_segments (0x22520 : word) = Some W_22520.
Proof. vm_refl. Qed.
Lemma D_22520 : decode_any W_22520 = Some (Load SZ8 true 14 14 1900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22524 : bv 32 := 0x00850613.
Lemma F_22524 : fetch_word Plain.M.loaded_segments (0x22524 : word) = Some W_22524.
Proof. vm_refl. Qed.
Lemma D_22524 : decode_any W_22524 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22528 : bv 32 := 0x00078513.
Lemma F_22528 : fetch_word Plain.M.loaded_segments (0x22528 : word) = Some W_22528.
Proof. vm_refl. Qed.
Lemma D_22528 : decode_any W_22528 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2252c : bv 32 := 0x00000793.
Lemma F_2252c : fetch_word Plain.M.loaded_segments (0x2252c : word) = Some W_2252c.
Proof. vm_refl. Qed.
Lemma D_2252c : decode_any W_2252c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22530 : bv 32 := 0x2d02e06f.
Lemma F_22530 : fetch_word Plain.M.loaded_segments (0x22530 : word) = Some W_22530.
Proof. vm_refl. Qed.
Lemma D_22530 : decode_any W_22530 = Some (Jal 0 189136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22534 : bv 32 := 0xff010113.
Lemma F_22534 : fetch_word Plain.M.loaded_segments (0x22534 : word) = Some W_22534.
Proof. vm_refl. Qed.
Lemma D_22534 : decode_any W_22534 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22538 : bv 32 := 0x00113423.
Lemma F_22538 : fetch_word Plain.M.loaded_segments (0x22538 : word) = Some W_22538.
Proof. vm_refl. Qed.
Lemma D_22538 : decode_any W_22538 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2253c : bv 32 := 0x00813023.
Lemma F_2253c : fetch_word Plain.M.loaded_segments (0x2253c : word) = Some W_2253c.
Proof. vm_refl. Qed.
Lemma D_2253c : decode_any W_2253c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22540 : bv 32 := 0x01010413.
Lemma F_22540 : fetch_word Plain.M.loaded_segments (0x22540 : word) = Some W_22540.
Proof. vm_refl. Qed.
Lemma D_22540 : decode_any W_22540 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22544 : bv 32 := 0x00043517.
Lemma F_22544 : fetch_word Plain.M.loaded_segments (0x22544 : word) = Some W_22544.
Proof. vm_refl. Qed.
Lemma D_22544 : decode_any W_22544 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22548 : bv 32 := 0xacc50513.
Lemma F_22548 : fetch_word Plain.M.loaded_segments (0x22548 : word) = Some W_22548.
Proof. vm_refl. Qed.
Lemma D_22548 : decode_any W_22548 = Some (OpImm ALU_ADD 10 10 2764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2254c : bv 32 := 0x00054503.
Lemma F_2254c : fetch_word Plain.M.loaded_segments (0x2254c : word) = Some W_2254c.
Proof. vm_refl. Qed.
Lemma D_2254c : decode_any W_2254c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22550 : bv 32 := 0x00157513.
Lemma F_22550 : fetch_word Plain.M.loaded_segments (0x22550 : word) = Some W_22550.
Proof. vm_refl. Qed.
Lemma D_22550 : decode_any W_22550 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22554 : bv 32 := 0x00050663.
Lemma F_22554 : fetch_word Plain.M.loaded_segments (0x22554 : word) = Some W_22554.
Proof. vm_refl. Qed.
Lemma D_22554 : decode_any W_22554 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22558 : bv 32 := 0x0040006f.
Lemma F_22558 : fetch_word Plain.M.loaded_segments (0x22558 : word) = Some W_22558.
Proof. vm_refl. Qed.
Lemma D_22558 : decode_any W_22558 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2255c : bv 32 := 0x03c0006f.
Lemma F_2255c : fetch_word Plain.M.loaded_segments (0x2255c : word) = Some W_2255c.
Proof. vm_refl. Qed.
Lemma D_2255c : decode_any W_2255c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22560 : bv 32 := 0x00043517.
Lemma F_22560 : fetch_word Plain.M.loaded_segments (0x22560 : word) = Some W_22560.
Proof. vm_refl. Qed.
Lemma D_22560 : decode_any W_22560 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22564 : bv 32 := 0xab050593.
Lemma F_22564 : fetch_word Plain.M.loaded_segments (0x22564 : word) = Some W_22564.
Proof. vm_refl. Qed.
Lemma D_22564 : decode_any W_22564 = Some (OpImm ALU_ADD 11 10 2736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22568 : bv 32 := 0x00100513.
Lemma F_22568 : fetch_word Plain.M.loaded_segments (0x22568 : word) = Some W_22568.
Proof. vm_refl. Qed.
Lemma D_22568 : decode_any W_22568 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2256c : bv 32 := 0x00a58023.
Lemma F_2256c : fetch_word Plain.M.loaded_segments (0x2256c : word) = Some W_2256c.
Proof. vm_refl. Qed.
Lemma D_2256c : decode_any W_2256c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22570 : bv 32 := 0x00041517.
Lemma F_22570 : fetch_word Plain.M.loaded_segments (0x22570 : word) = Some W_22570.
Proof. vm_refl. Qed.
Lemma D_22570 : decode_any W_22570 = Some (Auipc 10 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22574 : bv 32 := 0x71853503.
Lemma F_22574 : fetch_word Plain.M.loaded_segments (0x22574 : word) = Some W_22574.
Proof. vm_refl. Qed.
Lemma D_22574 : decode_any W_22574 = Some (Load SZ8 true 10 10 1816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22578 : bv 32 := 0x02050063.
Lemma F_22578 : fetch_word Plain.M.loaded_segments (0x22578 : word) = Some W_22578.
Proof. vm_refl. Qed.
Lemma D_22578 : decode_any W_22578 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2257c : bv 32 := 0x0040006f.
Lemma F_2257c : fetch_word Plain.M.loaded_segments (0x2257c : word) = Some W_2257c.
Proof. vm_refl. Qed.
Lemma D_2257c : decode_any W_2257c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22580 : bv 32 := 0xffff9517.
Lemma F_22580 : fetch_word Plain.M.loaded_segments (0x22580 : word) = Some W_22580.
Proof. vm_refl. Qed.
Lemma D_22580 : decode_any W_22580 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22584 : bv 32 := 0x2f850513.
Lemma F_22584 : fetch_word Plain.M.loaded_segments (0x22584 : word) = Some W_22584.
Proof. vm_refl. Qed.
Lemma D_22584 : decode_any W_22584 = Some (OpImm ALU_ADD 10 10 760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22588 : bv 32 := 0x00043597.
Lemma F_22588 : fetch_word Plain.M.loaded_segments (0x22588 : word) = Some W_22588.
Proof. vm_refl. Qed.
Lemma D_22588 : decode_any W_22588 = Some (Auipc 11 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2258c : bv 32 := 0xa9058593.
Lemma F_2258c : fetch_word Plain.M.loaded_segments (0x2258c : word) = Some W_2258c.
Proof. vm_refl. Qed.
Lemma D_2258c : decode_any W_2258c = Some (OpImm ALU_ADD 11 11 2704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22590 : bv 32 := 0x000000ef.
Lemma F_22590 : fetch_word Plain.M.loaded_segments (0x22590 : word) = Some W_22590.
Proof. vm_refl. Qed.
Lemma D_22590 : decode_any W_22590 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22594 : bv 32 := 0x0040006f.
Lemma F_22594 : fetch_word Plain.M.loaded_segments (0x22594 : word) = Some W_22594.
Proof. vm_refl. Qed.
Lemma D_22594 : decode_any W_22594 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22598 : bv 32 := 0x00813083.
Lemma F_22598 : fetch_word Plain.M.loaded_segments (0x22598 : word) = Some W_22598.
Proof. vm_refl. Qed.
Lemma D_22598 : decode_any W_22598 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2259c : bv 32 := 0x00013403.
Lemma F_2259c : fetch_word Plain.M.loaded_segments (0x2259c : word) = Some W_2259c.
Proof. vm_refl. Qed.
Lemma D_2259c : decode_any W_2259c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225a0 : bv 32 := 0x01010113.
Lemma F_225a0 : fetch_word Plain.M.loaded_segments (0x225a0 : word) = Some W_225a0.
Proof. vm_refl. Qed.
Lemma D_225a0 : decode_any W_225a0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225a4 : bv 32 := 0x00008067.
Lemma F_225a4 : fetch_word Plain.M.loaded_segments (0x225a4 : word) = Some W_225a4.
Proof. vm_refl. Qed.
Lemma D_225a4 : decode_any W_225a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225a8 : bv 32 := 0xff010113.
Lemma F_225a8 : fetch_word Plain.M.loaded_segments (0x225a8 : word) = Some W_225a8.
Proof. vm_refl. Qed.
Lemma D_225a8 : decode_any W_225a8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225ac : bv 32 := 0x00113423.
Lemma F_225ac : fetch_word Plain.M.loaded_segments (0x225ac : word) = Some W_225ac.
Proof. vm_refl. Qed.
Lemma D_225ac : decode_any W_225ac = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225b0 : bv 32 := 0x00813023.
Lemma F_225b0 : fetch_word Plain.M.loaded_segments (0x225b0 : word) = Some W_225b0.
Proof. vm_refl. Qed.
Lemma D_225b0 : decode_any W_225b0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225b4 : bv 32 := 0x01010413.
Lemma F_225b4 : fetch_word Plain.M.loaded_segments (0x225b4 : word) = Some W_225b4.
Proof. vm_refl. Qed.
Lemma D_225b4 : decode_any W_225b4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225b8 : bv 32 := 0x00043517.
Lemma F_225b8 : fetch_word Plain.M.loaded_segments (0x225b8 : word) = Some W_225b8.
Proof. vm_refl. Qed.
Lemma D_225b8 : decode_any W_225b8 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225bc : bv 32 := 0xaa050513.
Lemma F_225bc : fetch_word Plain.M.loaded_segments (0x225bc : word) = Some W_225bc.
Proof. vm_refl. Qed.
Lemma D_225bc : decode_any W_225bc = Some (OpImm ALU_ADD 10 10 2720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225c0 : bv 32 := 0x00054503.
Lemma F_225c0 : fetch_word Plain.M.loaded_segments (0x225c0 : word) = Some W_225c0.
Proof. vm_refl. Qed.
Lemma D_225c0 : decode_any W_225c0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225c4 : bv 32 := 0x00157513.
Lemma F_225c4 : fetch_word Plain.M.loaded_segments (0x225c4 : word) = Some W_225c4.
Proof. vm_refl. Qed.
Lemma D_225c4 : decode_any W_225c4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225c8 : bv 32 := 0x00050663.
Lemma F_225c8 : fetch_word Plain.M.loaded_segments (0x225c8 : word) = Some W_225c8.
Proof. vm_refl. Qed.
Lemma D_225c8 : decode_any W_225c8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225cc : bv 32 := 0x0040006f.
Lemma F_225cc : fetch_word Plain.M.loaded_segments (0x225cc : word) = Some W_225cc.
Proof. vm_refl. Qed.
Lemma D_225cc : decode_any W_225cc = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225d0 : bv 32 := 0x0580006f.
Lemma F_225d0 : fetch_word Plain.M.loaded_segments (0x225d0 : word) = Some W_225d0.
Proof. vm_refl. Qed.
Lemma D_225d0 : decode_any W_225d0 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225d4 : bv 32 := 0x00043517.
Lemma F_225d4 : fetch_word Plain.M.loaded_segments (0x225d4 : word) = Some W_225d4.
Proof. vm_refl. Qed.
Lemma D_225d4 : decode_any W_225d4 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225d8 : bv 32 := 0xa8450593.
Lemma F_225d8 : fetch_word Plain.M.loaded_segments (0x225d8 : word) = Some W_225d8.
Proof. vm_refl. Qed.
Lemma D_225d8 : decode_any W_225d8 = Some (OpImm ALU_ADD 11 10 2692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225dc : bv 32 := 0x00100513.
Lemma F_225dc : fetch_word Plain.M.loaded_segments (0x225dc : word) = Some W_225dc.
Proof. vm_refl. Qed.
Lemma D_225dc : decode_any W_225dc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225e0 : bv 32 := 0x00a58023.
Lemma F_225e0 : fetch_word Plain.M.loaded_segments (0x225e0 : word) = Some W_225e0.
Proof. vm_refl. Qed.
Lemma D_225e0 : decode_any W_225e0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225e4 : bv 32 := 0x00041517.
Lemma F_225e4 : fetch_word Plain.M.loaded_segments (0x225e4 : word) = Some W_225e4.
Proof. vm_refl. Qed.
Lemma D_225e4 : decode_any W_225e4 = Some (Auipc 10 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225e8 : bv 32 := 0x6ac53503.
Lemma F_225e8 : fetch_word Plain.M.loaded_segments (0x225e8 : word) = Some W_225e8.
Proof. vm_refl. Qed.
Lemma D_225e8 : decode_any W_225e8 = Some (Load SZ8 true 10 10 1708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225ec : bv 32 := 0x00050e63.
Lemma F_225ec : fetch_word Plain.M.loaded_segments (0x225ec : word) = Some W_225ec.
Proof. vm_refl. Qed.
Lemma D_225ec : decode_any W_225ec = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225f0 : bv 32 := 0x0040006f.
Lemma F_225f0 : fetch_word Plain.M.loaded_segments (0x225f0 : word) = Some W_225f0.
Proof. vm_refl. Qed.
Lemma D_225f0 : decode_any W_225f0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225f4 : bv 32 := 0x00042517.
Lemma F_225f4 : fetch_word Plain.M.loaded_segments (0x225f4 : word) = Some W_225f4.
Proof. vm_refl. Qed.
Lemma D_225f4 : decode_any W_225f4 = Some (Auipc 10 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225f8 : bv 32 := 0x7c450513.
Lemma F_225f8 : fetch_word Plain.M.loaded_segments (0x225f8 : word) = Some W_225f8.
Proof. vm_refl. Qed.
Lemma D_225f8 : decode_any W_225f8 = Some (OpImm ALU_ADD 10 10 1988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_225fc : bv 32 := 0x00053503.
Lemma F_225fc : fetch_word Plain.M.loaded_segments (0x225fc : word) = Some W_225fc.
Proof. vm_refl. Qed.
Lemma D_225fc : decode_any W_225fc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22600 : bv 32 := 0x70c2e0ef.
Lemma F_22600 : fetch_word Plain.M.loaded_segments (0x22600 : word) = Some W_22600.
Proof. vm_refl. Qed.
Lemma D_22600 : decode_any W_22600 = Some (Jal 1 190220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22604 : bv 32 := 0x0040006f.
Lemma F_22604 : fetch_word Plain.M.loaded_segments (0x22604 : word) = Some W_22604.
Proof. vm_refl. Qed.
Lemma D_22604 : decode_any W_22604 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22608 : bv 32 := 0x00041517.
Lemma F_22608 : fetch_word Plain.M.loaded_segments (0x22608 : word) = Some W_22608.
Proof. vm_refl. Qed.
Lemma D_22608 : decode_any W_22608 = Some (Auipc 10 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2260c : bv 32 := 0x69053503.
Lemma F_2260c : fetch_word Plain.M.loaded_segments (0x2260c : word) = Some W_2260c.
Proof. vm_refl. Qed.
Lemma D_2260c : decode_any W_2260c = Some (Load SZ8 true 10 10 1680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22610 : bv 32 := 0x00050c63.
Lemma F_22610 : fetch_word Plain.M.loaded_segments (0x22610 : word) = Some W_22610.
Proof. vm_refl. Qed.
Lemma D_22610 : decode_any W_22610 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22614 : bv 32 := 0x0040006f.
Lemma F_22614 : fetch_word Plain.M.loaded_segments (0x22614 : word) = Some W_22614.
Proof. vm_refl. Qed.
Lemma D_22614 : decode_any W_22614 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22618 : bv 32 := 0xffff9517.
Lemma F_22618 : fetch_word Plain.M.loaded_segments (0x22618 : word) = Some W_22618.
Proof. vm_refl. Qed.
Lemma D_22618 : decode_any W_22618 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2261c : bv 32 := 0x26050513.
Lemma F_2261c : fetch_word Plain.M.loaded_segments (0x2261c : word) = Some W_2261c.
Proof. vm_refl. Qed.
Lemma D_2261c : decode_any W_2261c = Some (OpImm ALU_ADD 10 10 608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22620 : bv 32 := 0x000000ef.
Lemma F_22620 : fetch_word Plain.M.loaded_segments (0x22620 : word) = Some W_22620.
Proof. vm_refl. Qed.
Lemma D_22620 : decode_any W_22620 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22624 : bv 32 := 0x0040006f.
Lemma F_22624 : fetch_word Plain.M.loaded_segments (0x22624 : word) = Some W_22624.
Proof. vm_refl. Qed.
Lemma D_22624 : decode_any W_22624 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22628 : bv 32 := 0x00813083.
Lemma F_22628 : fetch_word Plain.M.loaded_segments (0x22628 : word) = Some W_22628.
Proof. vm_refl. Qed.
Lemma D_22628 : decode_any W_22628 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2262c : bv 32 := 0x00013403.
Lemma F_2262c : fetch_word Plain.M.loaded_segments (0x2262c : word) = Some W_2262c.
Proof. vm_refl. Qed.
Lemma D_2262c : decode_any W_2262c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22630 : bv 32 := 0x01010113.
Lemma F_22630 : fetch_word Plain.M.loaded_segments (0x22630 : word) = Some W_22630.
Proof. vm_refl. Qed.
Lemma D_22630 : decode_any W_22630 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22634 : bv 32 := 0x00008067.
Lemma F_22634 : fetch_word Plain.M.loaded_segments (0x22634 : word) = Some W_22634.
Proof. vm_refl. Qed.
Lemma D_22634 : decode_any W_22634 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
