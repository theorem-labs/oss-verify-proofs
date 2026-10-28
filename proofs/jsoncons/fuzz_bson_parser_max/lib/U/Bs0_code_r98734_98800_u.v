(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_99510 : bv 32 := 0xfd010113.
Lemma F_99510 : fetch_word Ubsan.M.loaded_segments (0x9ab44 : word) = Some W_99510.
Proof. vm_refl. Qed.
Lemma D_99510 : decode_any W_99510 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99514 : bv 32 := 0x02113423.
Lemma F_99514 : fetch_word Ubsan.M.loaded_segments (0x9ab48 : word) = Some W_99514.
Proof. vm_refl. Qed.
Lemma D_99514 : decode_any W_99514 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99518 : bv 32 := 0x02813023.
Lemma F_99518 : fetch_word Ubsan.M.loaded_segments (0x9ab4c : word) = Some W_99518.
Proof. vm_refl. Qed.
Lemma D_99518 : decode_any W_99518 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9951c : bv 32 := 0x00913c23.
Lemma F_9951c : fetch_word Ubsan.M.loaded_segments (0x9ab50 : word) = Some W_9951c.
Proof. vm_refl. Qed.
Lemma D_9951c : decode_any W_9951c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99520 : bv 32 := 0x01213823.
Lemma F_99520 : fetch_word Ubsan.M.loaded_segments (0x9ab54 : word) = Some W_99520.
Proof. vm_refl. Qed.
Lemma D_99520 : decode_any W_99520 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99524 : bv 32 := 0x01313423.
Lemma F_99524 : fetch_word Ubsan.M.loaded_segments (0x9ab58 : word) = Some W_99524.
Proof. vm_refl. Qed.
Lemma D_99524 : decode_any W_99524 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99528 : bv 32 := 0x0004f517.
Lemma F_99528 : fetch_word Ubsan.M.loaded_segments (0x9ab5c : word) = Some W_99528.
Proof. vm_refl. Qed.
Lemma D_99528 : decode_any W_99528 = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9952c : bv 32 := 0x4ac50913.
Lemma F_9952c : fetch_word Ubsan.M.loaded_segments (0x9ab60 : word) = Some W_9952c.
Proof. vm_refl. Qed.
Lemma D_9952c : decode_any W_9952c = Some (OpImm ALU_ADD 18 10 1196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99530 : bv 32 := 0x00490413.
Lemma F_99530 : fetch_word Ubsan.M.loaded_segments (0x9ab64 : word) = Some W_99530.
Proof. vm_refl. Qed.
Lemma D_99530 : decode_any W_99530 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99534 : bv 32 := 0x00040513.
Lemma F_99534 : fetch_word Ubsan.M.loaded_segments (0x9ab68 : word) = Some W_99534.
Proof. vm_refl. Qed.
Lemma D_99534 : decode_any W_99534 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99538 : bv 32 := 0x5a4110ef.
Lemma F_99538 : fetch_word Ubsan.M.loaded_segments (0x9ab6c : word) = Some W_99538.
Proof. vm_refl. Qed.
Lemma D_99538 : decode_any W_99538 = Some (Jal 1 71076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9953c : bv 32 := 0x01093503.
Lemma F_9953c : fetch_word Ubsan.M.loaded_segments (0x9ab70 : word) = Some W_9953c.
Proof. vm_refl. Qed.
Lemma D_9953c : decode_any W_9953c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99540 : bv 32 := 0x06050863.
Lemma F_99540 : fetch_word Ubsan.M.loaded_segments (0x9ab74 : word) = Some W_99540.
Proof. vm_refl. Qed.
Lemma D_99540 : decode_any W_99540 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99544 : bv 32 := 0x00892583.
Lemma F_99544 : fetch_word Ubsan.M.loaded_segments (0x9ab78 : word) = Some W_99544.
Proof. vm_refl. Qed.
Lemma D_99544 : decode_any W_99544 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99548 : bv 32 := 0x0180006f.
Lemma F_99548 : fetch_word Ubsan.M.loaded_segments (0x9ab7c : word) = Some W_99548.
Proof. vm_refl. Qed.
Lemma D_99548 : decode_any W_99548 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9954c : bv 32 := 0x00053503.
Lemma F_9954c : fetch_word Ubsan.M.loaded_segments (0x9ab80 : word) = Some W_9954c.
Proof. vm_refl. Qed.
Lemma D_9954c : decode_any W_9954c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99550 : bv 32 := 0x02000593.
Lemma F_99550 : fetch_word Ubsan.M.loaded_segments (0x9ab84 : word) = Some W_99550.
Proof. vm_refl. Qed.
Lemma D_99550 : decode_any W_99550 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99554 : bv 32 := 0x00b92423.
Lemma F_99554 : fetch_word Ubsan.M.loaded_segments (0x9ab88 : word) = Some W_99554.
Proof. vm_refl. Qed.
Lemma D_99554 : decode_any W_99554 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99558 : bv 32 := 0x00a93823.
Lemma F_99558 : fetch_word Ubsan.M.loaded_segments (0x9ab8c : word) = Some W_99558.
Proof. vm_refl. Qed.
Lemma D_99558 : decode_any W_99558 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9955c : bv 32 := 0x04050a63.
Lemma F_9955c : fetch_word Ubsan.M.loaded_segments (0x9ab90 : word) = Some W_9955c.
Proof. vm_refl. Qed.
Lemma D_9955c : decode_any W_9955c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99560 : bv 32 := 0xfff5861b.
Lemma F_99560 : fetch_word Ubsan.M.loaded_segments (0x9ab94 : word) = Some W_99560.
Proof. vm_refl. Qed.
Lemma D_99560 : decode_any W_99560 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99564 : bv 32 := 0x00c92423.
Lemma F_99564 : fetch_word Ubsan.M.loaded_segments (0x9ab98 : word) = Some W_99564.
Proof. vm_refl. Qed.
Lemma D_99564 : decode_any W_99564 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99568 : bv 32 := 0xfeb052e3.
Lemma F_99568 : fetch_word Ubsan.M.loaded_segments (0x9ab9c : word) = Some W_99568.
Proof. vm_refl. Qed.
Lemma D_99568 : decode_any W_99568 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9956c : bv 32 := 0x01093503.
Lemma F_9956c : fetch_word Ubsan.M.loaded_segments (0x9aba0 : word) = Some W_9956c.
Proof. vm_refl. Qed.
Lemma D_9956c : decode_any W_9956c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99570 : bv 32 := 0x00361613.
Lemma F_99570 : fetch_word Ubsan.M.loaded_segments (0x9aba4 : word) = Some W_99570.
Proof. vm_refl. Qed.
Lemma D_99570 : decode_any W_99570 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99574 : bv 32 := 0x00c50533.
Lemma F_99574 : fetch_word Ubsan.M.loaded_segments (0x9aba8 : word) = Some W_99574.
Proof. vm_refl. Qed.
Lemma D_99574 : decode_any W_99574 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99578 : bv 32 := 0x00853983.
Lemma F_99578 : fetch_word Ubsan.M.loaded_segments (0x9abac : word) = Some W_99578.
Proof. vm_refl. Qed.
Lemma D_99578 : decode_any W_99578 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9957c : bv 32 := 0x10853483.
Lemma F_9957c : fetch_word Ubsan.M.loaded_segments (0x9abb0 : word) = Some W_9957c.
Proof. vm_refl. Qed.
Lemma D_9957c : decode_any W_9957c = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99580 : bv 32 := 0x00040513.
Lemma F_99580 : fetch_word Ubsan.M.loaded_segments (0x9abb4 : word) = Some W_99580.
Proof. vm_refl. Qed.
Lemma D_99580 : decode_any W_99580 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99584 : bv 32 := 0x7e0110ef.
Lemma F_99584 : fetch_word Ubsan.M.loaded_segments (0x9abb8 : word) = Some W_99584.
Proof. vm_refl. Qed.
Lemma D_99584 : decode_any W_99584 = Some (Jal 1 71648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99588 : bv 32 := 0x00048513.
Lemma F_99588 : fetch_word Ubsan.M.loaded_segments (0x9abbc : word) = Some W_99588.
Proof. vm_refl. Qed.
Lemma D_99588 : decode_any W_99588 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9958c : bv 32 := 0x000980e7.
Lemma F_9958c : fetch_word Ubsan.M.loaded_segments (0x9abc0 : word) = Some W_9958c.
Proof. vm_refl. Qed.
Lemma D_9958c : decode_any W_9958c = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99590 : bv 32 := 0x00040513.
Lemma F_99590 : fetch_word Ubsan.M.loaded_segments (0x9abc4 : word) = Some W_99590.
Proof. vm_refl. Qed.
Lemma D_99590 : decode_any W_99590 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99594 : bv 32 := 0x548110ef.
Lemma F_99594 : fetch_word Ubsan.M.loaded_segments (0x9abc8 : word) = Some W_99594.
Proof. vm_refl. Qed.
Lemma D_99594 : decode_any W_99594 = Some (Jal 1 70984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99598 : bv 32 := 0x00892503.
Lemma F_99598 : fetch_word Ubsan.M.loaded_segments (0x9abcc : word) = Some W_99598.
Proof. vm_refl. Qed.
Lemma D_99598 : decode_any W_99598 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9959c : bv 32 := 0xfff5061b.
Lemma F_9959c : fetch_word Ubsan.M.loaded_segments (0x9abd0 : word) = Some W_9959c.
Proof. vm_refl. Qed.
Lemma D_9959c : decode_any W_9959c = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995a0 : bv 32 := 0x00c92423.
Lemma F_995a0 : fetch_word Ubsan.M.loaded_segments (0x9abd4 : word) = Some W_995a0.
Proof. vm_refl. Qed.
Lemma D_995a0 : decode_any W_995a0 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995a4 : bv 32 := 0xfca044e3.
Lemma F_995a4 : fetch_word Ubsan.M.loaded_segments (0x9abd8 : word) = Some W_995a4.
Proof. vm_refl. Qed.
Lemma D_995a4 : decode_any W_995a4 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995a8 : bv 32 := 0x01093503.
Lemma F_995a8 : fetch_word Ubsan.M.loaded_segments (0x9abdc : word) = Some W_995a8.
Proof. vm_refl. Qed.
Lemma D_995a8 : decode_any W_995a8 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995ac : bv 32 := 0xfa1ff06f.
Lemma F_995ac : fetch_word Ubsan.M.loaded_segments (0x9abe0 : word) = Some W_995ac.
Proof. vm_refl. Qed.
Lemma D_995ac : decode_any W_995ac = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995b0 : bv 32 := 0x00100513.
Lemma F_995b0 : fetch_word Ubsan.M.loaded_segments (0x9abe4 : word) = Some W_995b0.
Proof. vm_refl. Qed.
Lemma D_995b0 : decode_any W_995b0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995b4 : bv 32 := 0x00a90023.
Lemma F_995b4 : fetch_word Ubsan.M.loaded_segments (0x9abe8 : word) = Some W_995b4.
Proof. vm_refl. Qed.
Lemma D_995b4 : decode_any W_995b4 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995b8 : bv 32 := 0x00040513.
Lemma F_995b8 : fetch_word Ubsan.M.loaded_segments (0x9abec : word) = Some W_995b8.
Proof. vm_refl. Qed.
Lemma D_995b8 : decode_any W_995b8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995bc : bv 32 := 0x02813083.
Lemma F_995bc : fetch_word Ubsan.M.loaded_segments (0x9abf0 : word) = Some W_995bc.
Proof. vm_refl. Qed.
Lemma D_995bc : decode_any W_995bc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995c0 : bv 32 := 0x02013403.
Lemma F_995c0 : fetch_word Ubsan.M.loaded_segments (0x9abf4 : word) = Some W_995c0.
Proof. vm_refl. Qed.
Lemma D_995c0 : decode_any W_995c0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995c4 : bv 32 := 0x01813483.
Lemma F_995c4 : fetch_word Ubsan.M.loaded_segments (0x9abf8 : word) = Some W_995c4.
Proof. vm_refl. Qed.
Lemma D_995c4 : decode_any W_995c4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995c8 : bv 32 := 0x01013903.
Lemma F_995c8 : fetch_word Ubsan.M.loaded_segments (0x9abfc : word) = Some W_995c8.
Proof. vm_refl. Qed.
Lemma D_995c8 : decode_any W_995c8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995cc : bv 32 := 0x00813983.
Lemma F_995cc : fetch_word Ubsan.M.loaded_segments (0x9ac00 : word) = Some W_995cc.
Proof. vm_refl. Qed.
Lemma D_995cc : decode_any W_995cc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995d0 : bv 32 := 0x03010113.
Lemma F_995d0 : fetch_word Ubsan.M.loaded_segments (0x9ac04 : word) = Some W_995d0.
Proof. vm_refl. Qed.
Lemma D_995d0 : decode_any W_995d0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995d4 : bv 32 := 0x7901106f.
Lemma F_995d4 : fetch_word Ubsan.M.loaded_segments (0x9ac08 : word) = Some W_995d4.
Proof. vm_refl. Qed.
Lemma D_995d4 : decode_any W_995d4 = Some (Jal 0 71568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_995d8 : bv 32 := 0x00008067.
Lemma F_995d8 : fetch_word Ubsan.M.loaded_segments (0x9ac0c : word) = Some W_995d8.
Proof. vm_refl. Qed.
Lemma D_995d8 : decode_any W_995d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
