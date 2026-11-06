(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_71564 : bv 32 := 0x02060063.
Lemma F_71564 : fetch_word AsanUbsan.M.loaded_segments (0x71564 : word) = Some W_71564.
Proof. vm_refl. Qed.
Lemma D_71564 : decode_any W_71564 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_71568 : bv 32 := 0x00c50633.
Lemma F_71568 : fetch_word AsanUbsan.M.loaded_segments (0x71568 : word) = Some W_71568.
Proof. vm_refl. Qed.
Lemma D_71568 : decode_any W_71568 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7156c : bv 32 := 0x00050693.
Lemma F_7156c : fetch_word AsanUbsan.M.loaded_segments (0x7156c : word) = Some W_7156c.
Proof. vm_refl. Qed.
Lemma D_7156c : decode_any W_7156c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71570 : bv 32 := 0x0005c703.
Lemma F_71570 : fetch_word AsanUbsan.M.loaded_segments (0x71570 : word) = Some W_71570.
Proof. vm_refl. Qed.
Lemma D_71570 : decode_any W_71570 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71574 : bv 32 := 0x00e68023.
Lemma F_71574 : fetch_word AsanUbsan.M.loaded_segments (0x71574 : word) = Some W_71574.
Proof. vm_refl. Qed.
Lemma D_71574 : decode_any W_71574 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71578 : bv 32 := 0x00168693.
Lemma F_71578 : fetch_word AsanUbsan.M.loaded_segments (0x71578 : word) = Some W_71578.
Proof. vm_refl. Qed.
Lemma D_71578 : decode_any W_71578 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7157c : bv 32 := 0x00158593.
Lemma F_7157c : fetch_word AsanUbsan.M.loaded_segments (0x7157c : word) = Some W_7157c.
Proof. vm_refl. Qed.
Lemma D_7157c : decode_any W_7157c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71580 : bv 32 := 0xfec698e3.
Lemma F_71580 : fetch_word AsanUbsan.M.loaded_segments (0x71580 : word) = Some W_71580.
Proof. vm_refl. Qed.
Lemma D_71580 : decode_any W_71580 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_71584 : bv 32 := 0x00008067.
Lemma F_71584 : fetch_word AsanUbsan.M.loaded_segments (0x71584 : word) = Some W_71584.
Proof. vm_refl. Qed.
Lemma D_71584 : decode_any W_71584 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71588 : bv 32 := 0x02b57463.
Lemma F_71588 : fetch_word AsanUbsan.M.loaded_segments (0x71588 : word) = Some W_71588.
Proof. vm_refl. Qed.
Lemma D_71588 : decode_any W_71588 = Some (Branch BC_GEU 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7158c : bv 32 := 0x04c05863.
Lemma F_7158c : fetch_word AsanUbsan.M.loaded_segments (0x7158c : word) = Some W_7158c.
Proof. vm_refl. Qed.
Lemma D_7158c : decode_any W_7158c = Some (Branch BC_GE 0 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_71590 : bv 32 := 0x00c50633.
Lemma F_71590 : fetch_word AsanUbsan.M.loaded_segments (0x71590 : word) = Some W_71590.
Proof. vm_refl. Qed.
Lemma D_71590 : decode_any W_71590 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71594 : bv 32 := 0x00050693.
Lemma F_71594 : fetch_word AsanUbsan.M.loaded_segments (0x71594 : word) = Some W_71594.
Proof. vm_refl. Qed.
Lemma D_71594 : decode_any W_71594 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71598 : bv 32 := 0x0005c703.
Lemma F_71598 : fetch_word AsanUbsan.M.loaded_segments (0x71598 : word) = Some W_71598.
Proof. vm_refl. Qed.
Lemma D_71598 : decode_any W_71598 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7159c : bv 32 := 0x00e68023.
Lemma F_7159c : fetch_word AsanUbsan.M.loaded_segments (0x7159c : word) = Some W_7159c.
Proof. vm_refl. Qed.
Lemma D_7159c : decode_any W_7159c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_715a0 : bv 32 := 0x00168693.
Lemma F_715a0 : fetch_word AsanUbsan.M.loaded_segments (0x715a0 : word) = Some W_715a0.
Proof. vm_refl. Qed.
Lemma D_715a0 : decode_any W_715a0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_715a4 : bv 32 := 0x00158593.
Lemma F_715a4 : fetch_word AsanUbsan.M.loaded_segments (0x715a4 : word) = Some W_715a4.
Proof. vm_refl. Qed.
Lemma D_715a4 : decode_any W_715a4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_715a8 : bv 32 := 0xfec698e3.
Lemma F_715a8 : fetch_word AsanUbsan.M.loaded_segments (0x715a8 : word) = Some W_715a8.
Proof. vm_refl. Qed.
Lemma D_715a8 : decode_any W_715a8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_715ac : bv 32 := 0x0300006f.
Lemma F_715ac : fetch_word AsanUbsan.M.loaded_segments (0x715ac : word) = Some W_715ac.
Proof. vm_refl. Qed.
Lemma D_715ac : decode_any W_715ac = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_715b0 : bv 32 := 0x02a5f663.
Lemma F_715b0 : fetch_word AsanUbsan.M.loaded_segments (0x715b0 : word) = Some W_715b0.
Proof. vm_refl. Qed.
Lemma D_715b0 : decode_any W_715b0 = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_715b4 : bv 32 := 0x02c05463.
Lemma F_715b4 : fetch_word AsanUbsan.M.loaded_segments (0x715b4 : word) = Some W_715b4.
Proof. vm_refl. Qed.
Lemma D_715b4 : decode_any W_715b4 = Some (Branch BC_GE 0 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_715b8 : bv 32 := 0xfff60693.
Lemma F_715b8 : fetch_word AsanUbsan.M.loaded_segments (0x715b8 : word) = Some W_715b8.
Proof. vm_refl. Qed.
Lemma D_715b8 : decode_any W_715b8 = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_715bc : bv 32 := 0x00100613.
Lemma F_715bc : fetch_word AsanUbsan.M.loaded_segments (0x715bc : word) = Some W_715bc.
Proof. vm_refl. Qed.
Lemma D_715bc : decode_any W_715bc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_715c0 : bv 32 := 0x00d58733.
Lemma F_715c0 : fetch_word AsanUbsan.M.loaded_segments (0x715c0 : word) = Some W_715c0.
Proof. vm_refl. Qed.
Lemma D_715c0 : decode_any W_715c0 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_715c4 : bv 32 := 0x00074703.
Lemma F_715c4 : fetch_word AsanUbsan.M.loaded_segments (0x715c4 : word) = Some W_715c4.
Proof. vm_refl. Qed.
Lemma D_715c4 : decode_any W_715c4 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_715c8 : bv 32 := 0x00d507b3.
Lemma F_715c8 : fetch_word AsanUbsan.M.loaded_segments (0x715c8 : word) = Some W_715c8.
Proof. vm_refl. Qed.
Lemma D_715c8 : decode_any W_715c8 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_715cc : bv 32 := 0x00168813.
Lemma F_715cc : fetch_word AsanUbsan.M.loaded_segments (0x715cc : word) = Some W_715cc.
Proof. vm_refl. Qed.
Lemma D_715cc : decode_any W_715cc = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_715d0 : bv 32 := 0xfff68693.
Lemma F_715d0 : fetch_word AsanUbsan.M.loaded_segments (0x715d0 : word) = Some W_715d0.
Proof. vm_refl. Qed.
Lemma D_715d0 : decode_any W_715d0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_715d4 : bv 32 := 0x00e78023.
Lemma F_715d4 : fetch_word AsanUbsan.M.loaded_segments (0x715d4 : word) = Some W_715d4.
Proof. vm_refl. Qed.
Lemma D_715d4 : decode_any W_715d4 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_715d8 : bv 32 := 0xff0664e3.
Lemma F_715d8 : fetch_word AsanUbsan.M.loaded_segments (0x715d8 : word) = Some W_715d8.
Proof. vm_refl. Qed.
Lemma D_715d8 : decode_any W_715d8 = Some (Branch BC_LTU 12 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_715dc : bv 32 := 0x00008067.
Lemma F_715dc : fetch_word AsanUbsan.M.loaded_segments (0x715dc : word) = Some W_715dc.
Proof. vm_refl. Qed.
Lemma D_715dc : decode_any W_715dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_715e0 : bv 32 := 0x00a666b3.
Lemma F_715e0 : fetch_word AsanUbsan.M.loaded_segments (0x715e0 : word) = Some W_715e0.
Proof. vm_refl. Qed.
Lemma D_715e0 : decode_any W_715e0 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_715e4 : bv 32 := 0x00f6f693.
Lemma F_715e4 : fetch_word AsanUbsan.M.loaded_segments (0x715e4 : word) = Some W_715e4.
Proof. vm_refl. Qed.
Lemma D_715e4 : decode_any W_715e4 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_715e8 : bv 32 := 0x02068063.
Lemma F_715e8 : fetch_word AsanUbsan.M.loaded_segments (0x715e8 : word) = Some W_715e8.
Proof. vm_refl. Qed.
Lemma D_715e8 : decode_any W_715e8 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_715ec : bv 32 := 0x04060863.
Lemma F_715ec : fetch_word AsanUbsan.M.loaded_segments (0x715ec : word) = Some W_715ec.
Proof. vm_refl. Qed.
Lemma D_715ec : decode_any W_715ec = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_715f0 : bv 32 := 0x00c50633.
Lemma F_715f0 : fetch_word AsanUbsan.M.loaded_segments (0x715f0 : word) = Some W_715f0.
Proof. vm_refl. Qed.
Lemma D_715f0 : decode_any W_715f0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_715f4 : bv 32 := 0x00050693.
Lemma F_715f4 : fetch_word AsanUbsan.M.loaded_segments (0x715f4 : word) = Some W_715f4.
Proof. vm_refl. Qed.
Lemma D_715f4 : decode_any W_715f4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_715f8 : bv 32 := 0x00b68023.
Lemma F_715f8 : fetch_word AsanUbsan.M.loaded_segments (0x715f8 : word) = Some W_715f8.
Proof. vm_refl. Qed.
Lemma D_715f8 : decode_any W_715f8 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_715fc : bv 32 := 0x00168693.
Lemma F_715fc : fetch_word AsanUbsan.M.loaded_segments (0x715fc : word) = Some W_715fc.
Proof. vm_refl. Qed.
Lemma D_715fc : decode_any W_715fc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71600 : bv 32 := 0xfec69ce3.
Lemma F_71600 : fetch_word AsanUbsan.M.loaded_segments (0x71600 : word) = Some W_71600.
Proof. vm_refl. Qed.
Lemma D_71600 : decode_any W_71600 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_71604 : bv 32 := 0x0380006f.
Lemma F_71604 : fetch_word AsanUbsan.M.loaded_segments (0x71604 : word) = Some W_71604.
Proof. vm_refl. Qed.
Lemma D_71604 : decode_any W_71604 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_71608 : bv 32 := 0x02060a63.
Lemma F_71608 : fetch_word AsanUbsan.M.loaded_segments (0x71608 : word) = Some W_71608.
Proof. vm_refl. Qed.
Lemma D_71608 : decode_any W_71608 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7160c : bv 32 := 0x00c50633.
Lemma F_7160c : fetch_word AsanUbsan.M.loaded_segments (0x7160c : word) = Some W_7160c.
Proof. vm_refl. Qed.
Lemma D_7160c : decode_any W_7160c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71610 : bv 32 := 0x00859693.
Lemma F_71610 : fetch_word AsanUbsan.M.loaded_segments (0x71610 : word) = Some W_71610.
Proof. vm_refl. Qed.
Lemma D_71610 : decode_any W_71610 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_71614 : bv 32 := 0x00b6e5b3.
Lemma F_71614 : fetch_word AsanUbsan.M.loaded_segments (0x71614 : word) = Some W_71614.
Proof. vm_refl. Qed.
Lemma D_71614 : decode_any W_71614 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_71618 : bv 32 := 0x01059693.
Lemma F_71618 : fetch_word AsanUbsan.M.loaded_segments (0x71618 : word) = Some W_71618.
Proof. vm_refl. Qed.
Lemma D_71618 : decode_any W_71618 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7161c : bv 32 := 0x00b6e5b3.
Lemma F_7161c : fetch_word AsanUbsan.M.loaded_segments (0x7161c : word) = Some W_7161c.
Proof. vm_refl. Qed.
Lemma D_7161c : decode_any W_7161c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_71620 : bv 32 := 0x02059693.
Lemma F_71620 : fetch_word AsanUbsan.M.loaded_segments (0x71620 : word) = Some W_71620.
Proof. vm_refl. Qed.
Lemma D_71620 : decode_any W_71620 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_71624 : bv 32 := 0x00b6e5b3.
Lemma F_71624 : fetch_word AsanUbsan.M.loaded_segments (0x71624 : word) = Some W_71624.
Proof. vm_refl. Qed.
Lemma D_71624 : decode_any W_71624 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_71628 : bv 32 := 0x00050693.
Lemma F_71628 : fetch_word AsanUbsan.M.loaded_segments (0x71628 : word) = Some W_71628.
Proof. vm_refl. Qed.
Lemma D_71628 : decode_any W_71628 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7162c : bv 32 := 0x00b6b023.
Lemma F_7162c : fetch_word AsanUbsan.M.loaded_segments (0x7162c : word) = Some W_7162c.
Proof. vm_refl. Qed.
Lemma D_7162c : decode_any W_7162c = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71630 : bv 32 := 0x00b6b423.
Lemma F_71630 : fetch_word AsanUbsan.M.loaded_segments (0x71630 : word) = Some W_71630.
Proof. vm_refl. Qed.
Lemma D_71630 : decode_any W_71630 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_71634 : bv 32 := 0x01068693.
Lemma F_71634 : fetch_word AsanUbsan.M.loaded_segments (0x71634 : word) = Some W_71634.
Proof. vm_refl. Qed.
Lemma D_71634 : decode_any W_71634 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_71638 : bv 32 := 0xfec6eae3.
Lemma F_71638 : fetch_word AsanUbsan.M.loaded_segments (0x71638 : word) = Some W_71638.
Proof. vm_refl. Qed.
Lemma D_71638 : decode_any W_71638 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7163c : bv 32 := 0x00008067.
Lemma F_7163c : fetch_word AsanUbsan.M.loaded_segments (0x7163c : word) = Some W_7163c.
Proof. vm_refl. Qed.
Lemma D_7163c : decode_any W_7163c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
