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

Definition W_8c540 : bv 32 := 0x02060063.
Lemma F_8c540 : fetch_word AsanUbsan.M.loaded_segments (0x8c590 : word) = Some W_8c540.
Proof. vm_refl. Qed.
Lemma D_8c540 : decode_any W_8c540 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c544 : bv 32 := 0x00c50633.
Lemma F_8c544 : fetch_word AsanUbsan.M.loaded_segments (0x8c594 : word) = Some W_8c544.
Proof. vm_refl. Qed.
Lemma D_8c544 : decode_any W_8c544 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c548 : bv 32 := 0x00050693.
Lemma F_8c548 : fetch_word AsanUbsan.M.loaded_segments (0x8c598 : word) = Some W_8c548.
Proof. vm_refl. Qed.
Lemma D_8c548 : decode_any W_8c548 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c54c : bv 32 := 0x0005c703.
Lemma F_8c54c : fetch_word AsanUbsan.M.loaded_segments (0x8c59c : word) = Some W_8c54c.
Proof. vm_refl. Qed.
Lemma D_8c54c : decode_any W_8c54c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c550 : bv 32 := 0x00e68023.
Lemma F_8c550 : fetch_word AsanUbsan.M.loaded_segments (0x8c5a0 : word) = Some W_8c550.
Proof. vm_refl. Qed.
Lemma D_8c550 : decode_any W_8c550 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c554 : bv 32 := 0x00168693.
Lemma F_8c554 : fetch_word AsanUbsan.M.loaded_segments (0x8c5a4 : word) = Some W_8c554.
Proof. vm_refl. Qed.
Lemma D_8c554 : decode_any W_8c554 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c558 : bv 32 := 0x00158593.
Lemma F_8c558 : fetch_word AsanUbsan.M.loaded_segments (0x8c5a8 : word) = Some W_8c558.
Proof. vm_refl. Qed.
Lemma D_8c558 : decode_any W_8c558 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c55c : bv 32 := 0xfec698e3.
Lemma F_8c55c : fetch_word AsanUbsan.M.loaded_segments (0x8c5ac : word) = Some W_8c55c.
Proof. vm_refl. Qed.
Lemma D_8c55c : decode_any W_8c55c = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c560 : bv 32 := 0x00008067.
Lemma F_8c560 : fetch_word AsanUbsan.M.loaded_segments (0x8c5b0 : word) = Some W_8c560.
Proof. vm_refl. Qed.
Lemma D_8c560 : decode_any W_8c560 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c564 : bv 32 := 0x02b57463.
Lemma F_8c564 : fetch_word AsanUbsan.M.loaded_segments (0x8c5b4 : word) = Some W_8c564.
Proof. vm_refl. Qed.
Lemma D_8c564 : decode_any W_8c564 = Some (Branch BC_GEU 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c568 : bv 32 := 0x04c05863.
Lemma F_8c568 : fetch_word AsanUbsan.M.loaded_segments (0x8c5b8 : word) = Some W_8c568.
Proof. vm_refl. Qed.
Lemma D_8c568 : decode_any W_8c568 = Some (Branch BC_GE 0 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c56c : bv 32 := 0x00c50633.
Lemma F_8c56c : fetch_word AsanUbsan.M.loaded_segments (0x8c5bc : word) = Some W_8c56c.
Proof. vm_refl. Qed.
Lemma D_8c56c : decode_any W_8c56c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c570 : bv 32 := 0x00050693.
Lemma F_8c570 : fetch_word AsanUbsan.M.loaded_segments (0x8c5c0 : word) = Some W_8c570.
Proof. vm_refl. Qed.
Lemma D_8c570 : decode_any W_8c570 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c574 : bv 32 := 0x0005c703.
Lemma F_8c574 : fetch_word AsanUbsan.M.loaded_segments (0x8c5c4 : word) = Some W_8c574.
Proof. vm_refl. Qed.
Lemma D_8c574 : decode_any W_8c574 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c578 : bv 32 := 0x00e68023.
Lemma F_8c578 : fetch_word AsanUbsan.M.loaded_segments (0x8c5c8 : word) = Some W_8c578.
Proof. vm_refl. Qed.
Lemma D_8c578 : decode_any W_8c578 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c57c : bv 32 := 0x00168693.
Lemma F_8c57c : fetch_word AsanUbsan.M.loaded_segments (0x8c5cc : word) = Some W_8c57c.
Proof. vm_refl. Qed.
Lemma D_8c57c : decode_any W_8c57c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c580 : bv 32 := 0x00158593.
Lemma F_8c580 : fetch_word AsanUbsan.M.loaded_segments (0x8c5d0 : word) = Some W_8c580.
Proof. vm_refl. Qed.
Lemma D_8c580 : decode_any W_8c580 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c584 : bv 32 := 0xfec698e3.
Lemma F_8c584 : fetch_word AsanUbsan.M.loaded_segments (0x8c5d4 : word) = Some W_8c584.
Proof. vm_refl. Qed.
Lemma D_8c584 : decode_any W_8c584 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c588 : bv 32 := 0x0300006f.
Lemma F_8c588 : fetch_word AsanUbsan.M.loaded_segments (0x8c5d8 : word) = Some W_8c588.
Proof. vm_refl. Qed.
Lemma D_8c588 : decode_any W_8c588 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c58c : bv 32 := 0x02a5f663.
Lemma F_8c58c : fetch_word AsanUbsan.M.loaded_segments (0x8c5dc : word) = Some W_8c58c.
Proof. vm_refl. Qed.
Lemma D_8c58c : decode_any W_8c58c = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c590 : bv 32 := 0x02c05463.
Lemma F_8c590 : fetch_word AsanUbsan.M.loaded_segments (0x8c5e0 : word) = Some W_8c590.
Proof. vm_refl. Qed.
Lemma D_8c590 : decode_any W_8c590 = Some (Branch BC_GE 0 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c594 : bv 32 := 0xfff60693.
Lemma F_8c594 : fetch_word AsanUbsan.M.loaded_segments (0x8c5e4 : word) = Some W_8c594.
Proof. vm_refl. Qed.
Lemma D_8c594 : decode_any W_8c594 = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c598 : bv 32 := 0x00100613.
Lemma F_8c598 : fetch_word AsanUbsan.M.loaded_segments (0x8c5e8 : word) = Some W_8c598.
Proof. vm_refl. Qed.
Lemma D_8c598 : decode_any W_8c598 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c59c : bv 32 := 0x00d58733.
Lemma F_8c59c : fetch_word AsanUbsan.M.loaded_segments (0x8c5ec : word) = Some W_8c59c.
Proof. vm_refl. Qed.
Lemma D_8c59c : decode_any W_8c59c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5a0 : bv 32 := 0x00074703.
Lemma F_8c5a0 : fetch_word AsanUbsan.M.loaded_segments (0x8c5f0 : word) = Some W_8c5a0.
Proof. vm_refl. Qed.
Lemma D_8c5a0 : decode_any W_8c5a0 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5a4 : bv 32 := 0x00d507b3.
Lemma F_8c5a4 : fetch_word AsanUbsan.M.loaded_segments (0x8c5f4 : word) = Some W_8c5a4.
Proof. vm_refl. Qed.
Lemma D_8c5a4 : decode_any W_8c5a4 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5a8 : bv 32 := 0x00168813.
Lemma F_8c5a8 : fetch_word AsanUbsan.M.loaded_segments (0x8c5f8 : word) = Some W_8c5a8.
Proof. vm_refl. Qed.
Lemma D_8c5a8 : decode_any W_8c5a8 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5ac : bv 32 := 0xfff68693.
Lemma F_8c5ac : fetch_word AsanUbsan.M.loaded_segments (0x8c5fc : word) = Some W_8c5ac.
Proof. vm_refl. Qed.
Lemma D_8c5ac : decode_any W_8c5ac = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5b0 : bv 32 := 0x00e78023.
Lemma F_8c5b0 : fetch_word AsanUbsan.M.loaded_segments (0x8c600 : word) = Some W_8c5b0.
Proof. vm_refl. Qed.
Lemma D_8c5b0 : decode_any W_8c5b0 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5b4 : bv 32 := 0xff0664e3.
Lemma F_8c5b4 : fetch_word AsanUbsan.M.loaded_segments (0x8c604 : word) = Some W_8c5b4.
Proof. vm_refl. Qed.
Lemma D_8c5b4 : decode_any W_8c5b4 = Some (Branch BC_LTU 12 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5b8 : bv 32 := 0x00008067.
Lemma F_8c5b8 : fetch_word AsanUbsan.M.loaded_segments (0x8c608 : word) = Some W_8c5b8.
Proof. vm_refl. Qed.
Lemma D_8c5b8 : decode_any W_8c5b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5bc : bv 32 := 0x00a666b3.
Lemma F_8c5bc : fetch_word AsanUbsan.M.loaded_segments (0x8c60c : word) = Some W_8c5bc.
Proof. vm_refl. Qed.
Lemma D_8c5bc : decode_any W_8c5bc = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5c0 : bv 32 := 0x00f6f693.
Lemma F_8c5c0 : fetch_word AsanUbsan.M.loaded_segments (0x8c610 : word) = Some W_8c5c0.
Proof. vm_refl. Qed.
Lemma D_8c5c0 : decode_any W_8c5c0 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5c4 : bv 32 := 0x02068063.
Lemma F_8c5c4 : fetch_word AsanUbsan.M.loaded_segments (0x8c614 : word) = Some W_8c5c4.
Proof. vm_refl. Qed.
Lemma D_8c5c4 : decode_any W_8c5c4 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5c8 : bv 32 := 0x04060863.
Lemma F_8c5c8 : fetch_word AsanUbsan.M.loaded_segments (0x8c618 : word) = Some W_8c5c8.
Proof. vm_refl. Qed.
Lemma D_8c5c8 : decode_any W_8c5c8 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5cc : bv 32 := 0x00c50633.
Lemma F_8c5cc : fetch_word AsanUbsan.M.loaded_segments (0x8c61c : word) = Some W_8c5cc.
Proof. vm_refl. Qed.
Lemma D_8c5cc : decode_any W_8c5cc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5d0 : bv 32 := 0x00050693.
Lemma F_8c5d0 : fetch_word AsanUbsan.M.loaded_segments (0x8c620 : word) = Some W_8c5d0.
Proof. vm_refl. Qed.
Lemma D_8c5d0 : decode_any W_8c5d0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5d4 : bv 32 := 0x00b68023.
Lemma F_8c5d4 : fetch_word AsanUbsan.M.loaded_segments (0x8c624 : word) = Some W_8c5d4.
Proof. vm_refl. Qed.
Lemma D_8c5d4 : decode_any W_8c5d4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5d8 : bv 32 := 0x00168693.
Lemma F_8c5d8 : fetch_word AsanUbsan.M.loaded_segments (0x8c628 : word) = Some W_8c5d8.
Proof. vm_refl. Qed.
Lemma D_8c5d8 : decode_any W_8c5d8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5dc : bv 32 := 0xfec69ce3.
Lemma F_8c5dc : fetch_word AsanUbsan.M.loaded_segments (0x8c62c : word) = Some W_8c5dc.
Proof. vm_refl. Qed.
Lemma D_8c5dc : decode_any W_8c5dc = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5e0 : bv 32 := 0x0380006f.
Lemma F_8c5e0 : fetch_word AsanUbsan.M.loaded_segments (0x8c630 : word) = Some W_8c5e0.
Proof. vm_refl. Qed.
Lemma D_8c5e0 : decode_any W_8c5e0 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5e4 : bv 32 := 0x02060a63.
Lemma F_8c5e4 : fetch_word AsanUbsan.M.loaded_segments (0x8c634 : word) = Some W_8c5e4.
Proof. vm_refl. Qed.
Lemma D_8c5e4 : decode_any W_8c5e4 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5e8 : bv 32 := 0x00c50633.
Lemma F_8c5e8 : fetch_word AsanUbsan.M.loaded_segments (0x8c638 : word) = Some W_8c5e8.
Proof. vm_refl. Qed.
Lemma D_8c5e8 : decode_any W_8c5e8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5ec : bv 32 := 0x00859693.
Lemma F_8c5ec : fetch_word AsanUbsan.M.loaded_segments (0x8c63c : word) = Some W_8c5ec.
Proof. vm_refl. Qed.
Lemma D_8c5ec : decode_any W_8c5ec = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5f0 : bv 32 := 0x00b6e5b3.
Lemma F_8c5f0 : fetch_word AsanUbsan.M.loaded_segments (0x8c640 : word) = Some W_8c5f0.
Proof. vm_refl. Qed.
Lemma D_8c5f0 : decode_any W_8c5f0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5f4 : bv 32 := 0x01059693.
Lemma F_8c5f4 : fetch_word AsanUbsan.M.loaded_segments (0x8c644 : word) = Some W_8c5f4.
Proof. vm_refl. Qed.
Lemma D_8c5f4 : decode_any W_8c5f4 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5f8 : bv 32 := 0x00b6e5b3.
Lemma F_8c5f8 : fetch_word AsanUbsan.M.loaded_segments (0x8c648 : word) = Some W_8c5f8.
Proof. vm_refl. Qed.
Lemma D_8c5f8 : decode_any W_8c5f8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5fc : bv 32 := 0x02059693.
Lemma F_8c5fc : fetch_word AsanUbsan.M.loaded_segments (0x8c64c : word) = Some W_8c5fc.
Proof. vm_refl. Qed.
Lemma D_8c5fc : decode_any W_8c5fc = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c600 : bv 32 := 0x00b6e5b3.
Lemma F_8c600 : fetch_word AsanUbsan.M.loaded_segments (0x8c650 : word) = Some W_8c600.
Proof. vm_refl. Qed.
Lemma D_8c600 : decode_any W_8c600 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c604 : bv 32 := 0x00050693.
Lemma F_8c604 : fetch_word AsanUbsan.M.loaded_segments (0x8c654 : word) = Some W_8c604.
Proof. vm_refl. Qed.
Lemma D_8c604 : decode_any W_8c604 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c608 : bv 32 := 0x00b6b023.
Lemma F_8c608 : fetch_word AsanUbsan.M.loaded_segments (0x8c658 : word) = Some W_8c608.
Proof. vm_refl. Qed.
Lemma D_8c608 : decode_any W_8c608 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c60c : bv 32 := 0x00b6b423.
Lemma F_8c60c : fetch_word AsanUbsan.M.loaded_segments (0x8c65c : word) = Some W_8c60c.
Proof. vm_refl. Qed.
Lemma D_8c60c : decode_any W_8c60c = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c610 : bv 32 := 0x01068693.
Lemma F_8c610 : fetch_word AsanUbsan.M.loaded_segments (0x8c660 : word) = Some W_8c610.
Proof. vm_refl. Qed.
Lemma D_8c610 : decode_any W_8c610 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c614 : bv 32 := 0xfec6eae3.
Lemma F_8c614 : fetch_word AsanUbsan.M.loaded_segments (0x8c664 : word) = Some W_8c614.
Proof. vm_refl. Qed.
Lemma D_8c614 : decode_any W_8c614 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c618 : bv 32 := 0x00008067.
Lemma F_8c618 : fetch_word AsanUbsan.M.loaded_segments (0x8c668 : word) = Some W_8c618.
Proof. vm_refl. Qed.
Lemma D_8c618 : decode_any W_8c618 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
