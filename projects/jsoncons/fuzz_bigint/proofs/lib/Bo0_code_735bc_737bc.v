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

Definition W_735bc : bv 32 := 0xfd010113.
Lemma F_735bc : fetch_word AsanUbsan.M.loaded_segments (0x735bc : word) = Some W_735bc.
Proof. vm_refl. Qed.
Lemma D_735bc : decode_any W_735bc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_735c0 : bv 32 := 0x02113423.
Lemma F_735c0 : fetch_word AsanUbsan.M.loaded_segments (0x735c0 : word) = Some W_735c0.
Proof. vm_refl. Qed.
Lemma D_735c0 : decode_any W_735c0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_735c4 : bv 32 := 0x02813023.
Lemma F_735c4 : fetch_word AsanUbsan.M.loaded_segments (0x735c4 : word) = Some W_735c4.
Proof. vm_refl. Qed.
Lemma D_735c4 : decode_any W_735c4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_735c8 : bv 32 := 0x00913c23.
Lemma F_735c8 : fetch_word AsanUbsan.M.loaded_segments (0x735c8 : word) = Some W_735c8.
Proof. vm_refl. Qed.
Lemma D_735c8 : decode_any W_735c8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_735cc : bv 32 := 0x01213823.
Lemma F_735cc : fetch_word AsanUbsan.M.loaded_segments (0x735cc : word) = Some W_735cc.
Proof. vm_refl. Qed.
Lemma D_735cc : decode_any W_735cc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_735d0 : bv 32 := 0x00060413.
Lemma F_735d0 : fetch_word AsanUbsan.M.loaded_segments (0x735d0 : word) = Some W_735d0.
Proof. vm_refl. Qed.
Lemma D_735d0 : decode_any W_735d0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_735d4 : bv 32 := 0x00058493.
Lemma F_735d4 : fetch_word AsanUbsan.M.loaded_segments (0x735d4 : word) = Some W_735d4.
Proof. vm_refl. Qed.
Lemma D_735d4 : decode_any W_735d4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_735d8 : bv 32 := 0x00050913.
Lemma F_735d8 : fetch_word AsanUbsan.M.loaded_segments (0x735d8 : word) = Some W_735d8.
Proof. vm_refl. Qed.
Lemma D_735d8 : decode_any W_735d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_735dc : bv 32 := 0x00d12623.
Lemma F_735dc : fetch_word AsanUbsan.M.loaded_segments (0x735dc : word) = Some W_735dc.
Proof. vm_refl. Qed.
Lemma D_735dc : decode_any W_735dc = Some (Store SZ4 2 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_735e0 : bv 32 := 0x00c10613.
Lemma F_735e0 : fetch_word AsanUbsan.M.loaded_segments (0x735e0 : word) = Some W_735e0.
Proof. vm_refl. Qed.
Lemma D_735e0 : decode_any W_735e0 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_735e4 : bv 32 := 0x00070513.
Lemma F_735e4 : fetch_word AsanUbsan.M.loaded_segments (0x735e4 : word) = Some W_735e4.
Proof. vm_refl. Qed.
Lemma D_735e4 : decode_any W_735e4 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_735e8 : bv 32 := 0x3a5000ef.
Lemma F_735e8 : fetch_word AsanUbsan.M.loaded_segments (0x735e8 : word) = Some W_735e8.
Proof. vm_refl. Qed.
Lemma D_735e8 : decode_any W_735e8 = Some (Jal 1 2980, 4%Z).
Proof. vm_refl. Qed.

Definition W_735ec : bv 32 := 0x00c12683.
Lemma F_735ec : fetch_word AsanUbsan.M.loaded_segments (0x735ec : word) = Some W_735ec.
Proof. vm_refl. Qed.
Lemma D_735ec : decode_any W_735ec = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_735f0 : bv 32 := 0x00050713.
Lemma F_735f0 : fetch_word AsanUbsan.M.loaded_segments (0x735f0 : word) = Some W_735f0.
Proof. vm_refl. Qed.
Lemma D_735f0 : decode_any W_735f0 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_735f4 : bv 32 := 0x00090513.
Lemma F_735f4 : fetch_word AsanUbsan.M.loaded_segments (0x735f4 : word) = Some W_735f4.
Proof. vm_refl. Qed.
Lemma D_735f4 : decode_any W_735f4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_735f8 : bv 32 := 0x00048593.
Lemma F_735f8 : fetch_word AsanUbsan.M.loaded_segments (0x735f8 : word) = Some W_735f8.
Proof. vm_refl. Qed.
Lemma D_735f8 : decode_any W_735f8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_735fc : bv 32 := 0x00040613.
Lemma F_735fc : fetch_word AsanUbsan.M.loaded_segments (0x735fc : word) = Some W_735fc.
Proof. vm_refl. Qed.
Lemma D_735fc : decode_any W_735fc = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73600 : bv 32 := 0x00000793.
Lemma F_73600 : fetch_word AsanUbsan.M.loaded_segments (0x73600 : word) = Some W_73600.
Proof. vm_refl. Qed.
Lemma D_73600 : decode_any W_73600 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73604 : bv 32 := 0xfdcfe0ef.
Lemma F_73604 : fetch_word AsanUbsan.M.loaded_segments (0x73604 : word) = Some W_73604.
Proof. vm_refl. Qed.
Lemma D_73604 : decode_any W_73604 = Some (Jal 1 2090972, 4%Z).
Proof. vm_refl. Qed.

Definition W_73608 : bv 32 := 0x00050413.
Lemma F_73608 : fetch_word AsanUbsan.M.loaded_segments (0x73608 : word) = Some W_73608.
Proof. vm_refl. Qed.
Lemma D_73608 : decode_any W_73608 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7360c : bv 32 := 0x00000593.
Lemma F_7360c : fetch_word AsanUbsan.M.loaded_segments (0x7360c : word) = Some W_7360c.
Proof. vm_refl. Qed.
Lemma D_7360c : decode_any W_7360c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73610 : bv 32 := 0xfb0fe0ef.
Lemma F_73610 : fetch_word AsanUbsan.M.loaded_segments (0x73610 : word) = Some W_73610.
Proof. vm_refl. Qed.
Lemma D_73610 : decode_any W_73610 = Some (Jal 1 2090928, 4%Z).
Proof. vm_refl. Qed.

Definition W_73614 : bv 32 := 0x00040513.
Lemma F_73614 : fetch_word AsanUbsan.M.loaded_segments (0x73614 : word) = Some W_73614.
Proof. vm_refl. Qed.
Lemma D_73614 : decode_any W_73614 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73618 : bv 32 := 0x02813083.
Lemma F_73618 : fetch_word AsanUbsan.M.loaded_segments (0x73618 : word) = Some W_73618.
Proof. vm_refl. Qed.
Lemma D_73618 : decode_any W_73618 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7361c : bv 32 := 0x02013403.
Lemma F_7361c : fetch_word AsanUbsan.M.loaded_segments (0x7361c : word) = Some W_7361c.
Proof. vm_refl. Qed.
Lemma D_7361c : decode_any W_7361c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_73620 : bv 32 := 0x01813483.
Lemma F_73620 : fetch_word AsanUbsan.M.loaded_segments (0x73620 : word) = Some W_73620.
Proof. vm_refl. Qed.
Lemma D_73620 : decode_any W_73620 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_73624 : bv 32 := 0x01013903.
Lemma F_73624 : fetch_word AsanUbsan.M.loaded_segments (0x73624 : word) = Some W_73624.
Proof. vm_refl. Qed.
Lemma D_73624 : decode_any W_73624 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73628 : bv 32 := 0x03010113.
Lemma F_73628 : fetch_word AsanUbsan.M.loaded_segments (0x73628 : word) = Some W_73628.
Proof. vm_refl. Qed.
Lemma D_73628 : decode_any W_73628 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7362c : bv 32 := 0x00008067.
Lemma F_7362c : fetch_word AsanUbsan.M.loaded_segments (0x7362c : word) = Some W_7362c.
Proof. vm_refl. Qed.
Lemma D_7362c : decode_any W_7362c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73630 : bv 32 := 0xfd010113.
Lemma F_73630 : fetch_word AsanUbsan.M.loaded_segments (0x73630 : word) = Some W_73630.
Proof. vm_refl. Qed.
Lemma D_73630 : decode_any W_73630 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_73634 : bv 32 := 0x02113423.
Lemma F_73634 : fetch_word AsanUbsan.M.loaded_segments (0x73634 : word) = Some W_73634.
Proof. vm_refl. Qed.
Lemma D_73634 : decode_any W_73634 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_73638 : bv 32 := 0x02813023.
Lemma F_73638 : fetch_word AsanUbsan.M.loaded_segments (0x73638 : word) = Some W_73638.
Proof. vm_refl. Qed.
Lemma D_73638 : decode_any W_73638 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7363c : bv 32 := 0x00913c23.
Lemma F_7363c : fetch_word AsanUbsan.M.loaded_segments (0x7363c : word) = Some W_7363c.
Proof. vm_refl. Qed.
Lemma D_7363c : decode_any W_7363c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_73640 : bv 32 := 0x01213823.
Lemma F_73640 : fetch_word AsanUbsan.M.loaded_segments (0x73640 : word) = Some W_73640.
Proof. vm_refl. Qed.
Lemma D_73640 : decode_any W_73640 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73644 : bv 32 := 0x02050e63.
Lemma F_73644 : fetch_word AsanUbsan.M.loaded_segments (0x73644 : word) = Some W_73644.
Proof. vm_refl. Qed.
Lemma D_73644 : decode_any W_73644 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_73648 : bv 32 := 0x00058413.
Lemma F_73648 : fetch_word AsanUbsan.M.loaded_segments (0x73648 : word) = Some W_73648.
Proof. vm_refl. Qed.
Lemma D_73648 : decode_any W_73648 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7364c : bv 32 := 0x02058a63.
Lemma F_7364c : fetch_word AsanUbsan.M.loaded_segments (0x7364c : word) = Some W_7364c.
Proof. vm_refl. Qed.
Lemma D_7364c : decode_any W_7364c = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_73650 : bv 32 := 0x00060493.
Lemma F_73650 : fetch_word AsanUbsan.M.loaded_segments (0x73650 : word) = Some W_73650.
Proof. vm_refl. Qed.
Lemma D_73650 : decode_any W_73650 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73654 : bv 32 := 0x00050913.
Lemma F_73654 : fetch_word AsanUbsan.M.loaded_segments (0x73654 : word) = Some W_73654.
Proof. vm_refl. Qed.
Lemma D_73654 : decode_any W_73654 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73658 : bv 32 := 0x00040593.
Lemma F_73658 : fetch_word AsanUbsan.M.loaded_segments (0x73658 : word) = Some W_73658.
Proof. vm_refl. Qed.
Lemma D_73658 : decode_any W_73658 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7365c : bv 32 := 0xf90fe0ef.
Lemma F_7365c : fetch_word AsanUbsan.M.loaded_segments (0x7365c : word) = Some W_7365c.
Proof. vm_refl. Qed.
Lemma D_7365c : decode_any W_7365c = Some (Jal 1 2090896, 4%Z).
Proof. vm_refl. Qed.

Definition W_73660 : bv 32 := 0xaaaab5b7.
Lemma F_73660 : fetch_word AsanUbsan.M.loaded_segments (0x73660 : word) = Some W_73660.
Proof. vm_refl. Qed.
Lemma D_73660 : decode_any W_73660 = Some (Lui 11 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_73664 : bv 32 := 0xaaa58593.
Lemma F_73664 : fetch_word AsanUbsan.M.loaded_segments (0x73664 : word) = Some W_73664.
Proof. vm_refl. Qed.
Lemma D_73664 : decode_any W_73664 = Some (OpImm ALU_ADD 11 11 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_73668 : bv 32 := 0x00b12623.
Lemma F_73668 : fetch_word AsanUbsan.M.loaded_segments (0x73668 : word) = Some W_73668.
Proof. vm_refl. Qed.
Lemma D_73668 : decode_any W_73668 = Some (Store SZ4 2 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7366c : bv 32 := 0x00c10593.
Lemma F_7366c : fetch_word AsanUbsan.M.loaded_segments (0x7366c : word) = Some W_7366c.
Proof. vm_refl. Qed.
Lemma D_7366c : decode_any W_7366c = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73670 : bv 32 := 0xf50fe0ef.
Lemma F_73670 : fetch_word AsanUbsan.M.loaded_segments (0x73670 : word) = Some W_73670.
Proof. vm_refl. Qed.
Lemma D_73670 : decode_any W_73670 = Some (Jal 1 2090832, 4%Z).
Proof. vm_refl. Qed.

Definition W_73674 : bv 32 := 0x02051263.
Lemma F_73674 : fetch_word AsanUbsan.M.loaded_segments (0x73674 : word) = Some W_73674.
Proof. vm_refl. Qed.
Lemma D_73674 : decode_any W_73674 = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_73678 : bv 32 := 0x00040513.
Lemma F_73678 : fetch_word AsanUbsan.M.loaded_segments (0x73678 : word) = Some W_73678.
Proof. vm_refl. Qed.
Lemma D_73678 : decode_any W_73678 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7367c : bv 32 := 0xe8cfa0ef.
Lemma F_7367c : fetch_word AsanUbsan.M.loaded_segments (0x7367c : word) = Some W_7367c.
Proof. vm_refl. Qed.
Lemma D_7367c : decode_any W_7367c = Some (Jal 1 2074252, 4%Z).
Proof. vm_refl. Qed.

Definition W_73680 : bv 32 := 0x02813083.
Lemma F_73680 : fetch_word AsanUbsan.M.loaded_segments (0x73680 : word) = Some W_73680.
Proof. vm_refl. Qed.
Lemma D_73680 : decode_any W_73680 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_73684 : bv 32 := 0x02013403.
Lemma F_73684 : fetch_word AsanUbsan.M.loaded_segments (0x73684 : word) = Some W_73684.
Proof. vm_refl. Qed.
Lemma D_73684 : decode_any W_73684 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_73688 : bv 32 := 0x01813483.
Lemma F_73688 : fetch_word AsanUbsan.M.loaded_segments (0x73688 : word) = Some W_73688.
Proof. vm_refl. Qed.
Lemma D_73688 : decode_any W_73688 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7368c : bv 32 := 0x01013903.
Lemma F_7368c : fetch_word AsanUbsan.M.loaded_segments (0x7368c : word) = Some W_7368c.
Proof. vm_refl. Qed.
Lemma D_7368c : decode_any W_7368c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73690 : bv 32 := 0x03010113.
Lemma F_73690 : fetch_word AsanUbsan.M.loaded_segments (0x73690 : word) = Some W_73690.
Proof. vm_refl. Qed.
Lemma D_73690 : decode_any W_73690 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_73694 : bv 32 := 0x00008067.
Lemma F_73694 : fetch_word AsanUbsan.M.loaded_segments (0x73694 : word) = Some W_73694.
Proof. vm_refl. Qed.
Lemma D_73694 : decode_any W_73694 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73698 : bv 32 := 0x00c12603.
Lemma F_73698 : fetch_word AsanUbsan.M.loaded_segments (0x73698 : word) = Some W_73698.
Proof. vm_refl. Qed.
Lemma D_73698 : decode_any W_73698 = Some (Load SZ4 true 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7369c : bv 32 := 0x00090513.
Lemma F_7369c : fetch_word AsanUbsan.M.loaded_segments (0x7369c : word) = Some W_7369c.
Proof. vm_refl. Qed.
Lemma D_7369c : decode_any W_7369c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736a0 : bv 32 := 0x00040593.
Lemma F_736a0 : fetch_word AsanUbsan.M.loaded_segments (0x736a0 : word) = Some W_736a0.
Proof. vm_refl. Qed.
Lemma D_736a0 : decode_any W_736a0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736a4 : bv 32 := 0x00048693.
Lemma F_736a4 : fetch_word AsanUbsan.M.loaded_segments (0x736a4 : word) = Some W_736a4.
Proof. vm_refl. Qed.
Lemma D_736a4 : decode_any W_736a4 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736a8 : bv 32 := 0x85cfa0ef.
Lemma F_736a8 : fetch_word AsanUbsan.M.loaded_segments (0x736a8 : word) = Some W_736a8.
Proof. vm_refl. Qed.
Lemma D_736a8 : decode_any W_736a8 = Some (Jal 1 2072668, 4%Z).
Proof. vm_refl. Qed.

Definition W_736ac : bv 32 := 0xfd010113.
Lemma F_736ac : fetch_word AsanUbsan.M.loaded_segments (0x736ac : word) = Some W_736ac.
Proof. vm_refl. Qed.
Lemma D_736ac : decode_any W_736ac = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_736b0 : bv 32 := 0x02113423.
Lemma F_736b0 : fetch_word AsanUbsan.M.loaded_segments (0x736b0 : word) = Some W_736b0.
Proof. vm_refl. Qed.
Lemma D_736b0 : decode_any W_736b0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_736b4 : bv 32 := 0x02813023.
Lemma F_736b4 : fetch_word AsanUbsan.M.loaded_segments (0x736b4 : word) = Some W_736b4.
Proof. vm_refl. Qed.
Lemma D_736b4 : decode_any W_736b4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_736b8 : bv 32 := 0x00913c23.
Lemma F_736b8 : fetch_word AsanUbsan.M.loaded_segments (0x736b8 : word) = Some W_736b8.
Proof. vm_refl. Qed.
Lemma D_736b8 : decode_any W_736b8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_736bc : bv 32 := 0x01213823.
Lemma F_736bc : fetch_word AsanUbsan.M.loaded_segments (0x736bc : word) = Some W_736bc.
Proof. vm_refl. Qed.
Lemma D_736bc : decode_any W_736bc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_736c0 : bv 32 := 0x00058413.
Lemma F_736c0 : fetch_word AsanUbsan.M.loaded_segments (0x736c0 : word) = Some W_736c0.
Proof. vm_refl. Qed.
Lemma D_736c0 : decode_any W_736c0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736c4 : bv 32 := 0x00063597.
Lemma F_736c4 : fetch_word AsanUbsan.M.loaded_segments (0x736c4 : word) = Some W_736c4.
Proof. vm_refl. Qed.
Lemma D_736c4 : decode_any W_736c4 = Some (Auipc 11 99, 4%Z).
Proof. vm_refl. Qed.

Definition W_736c8 : bv 32 := 0xde45b903.
Lemma F_736c8 : fetch_word AsanUbsan.M.loaded_segments (0x736c8 : word) = Some W_736c8.
Proof. vm_refl. Qed.
Lemma D_736c8 : decode_any W_736c8 = Some (Load SZ8 true 18 11 3556, 4%Z).
Proof. vm_refl. Qed.

Definition W_736cc : bv 32 := 0x00093583.
Lemma F_736cc : fetch_word AsanUbsan.M.loaded_segments (0x736cc : word) = Some W_736cc.
Proof. vm_refl. Qed.
Lemma D_736cc : decode_any W_736cc = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736d0 : bv 32 := 0x00050493.
Lemma F_736d0 : fetch_word AsanUbsan.M.loaded_segments (0x736d0 : word) = Some W_736d0.
Proof. vm_refl. Qed.
Lemma D_736d0 : decode_any W_736d0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736d4 : bv 32 := 0x00059863.
Lemma F_736d4 : fetch_word AsanUbsan.M.loaded_segments (0x736d4 : word) = Some W_736d4.
Proof. vm_refl. Qed.
Lemma D_736d4 : decode_any W_736d4 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_736d8 : bv 32 := 0xe34ff0ef.
Lemma F_736d8 : fetch_word AsanUbsan.M.loaded_segments (0x736d8 : word) = Some W_736d8.
Proof. vm_refl. Qed.
Lemma D_736d8 : decode_any W_736d8 = Some (Jal 1 2094644, 4%Z).
Proof. vm_refl. Qed.

Definition W_736dc : bv 32 := 0x00050593.
Lemma F_736dc : fetch_word AsanUbsan.M.loaded_segments (0x736dc : word) = Some W_736dc.
Proof. vm_refl. Qed.
Lemma D_736dc : decode_any W_736dc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736e0 : bv 32 := 0x00a93023.
Lemma F_736e0 : fetch_word AsanUbsan.M.loaded_segments (0x736e0 : word) = Some W_736e0.
Proof. vm_refl. Qed.
Lemma D_736e0 : decode_any W_736e0 = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_736e4 : bv 32 := 0xfff58513.
Lemma F_736e4 : fetch_word AsanUbsan.M.loaded_segments (0x736e4 : word) = Some W_736e4.
Proof. vm_refl. Qed.
Lemma D_736e4 : decode_any W_736e4 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_736e8 : bv 32 := 0x00a5f533.
Lemma F_736e8 : fetch_word AsanUbsan.M.loaded_segments (0x736e8 : word) = Some W_736e8.
Proof. vm_refl. Qed.
Lemma D_736e8 : decode_any W_736e8 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_736ec : bv 32 := 0x08051a63.
Lemma F_736ec : fetch_word AsanUbsan.M.loaded_segments (0x736ec : word) = Some W_736ec.
Proof. vm_refl. Qed.
Lemma D_736ec : decode_any W_736ec = Some (Branch BC_NE 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_736f0 : bv 32 := 0x00b484b3.
Lemma F_736f0 : fetch_word AsanUbsan.M.loaded_segments (0x736f0 : word) = Some W_736f0.
Proof. vm_refl. Qed.
Lemma D_736f0 : decode_any W_736f0 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_736f4 : bv 32 := 0x40b00533.
Lemma F_736f4 : fetch_word AsanUbsan.M.loaded_segments (0x736f4 : word) = Some W_736f4.
Proof. vm_refl. Qed.
Lemma D_736f4 : decode_any W_736f4 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_736f8 : bv 32 := 0xfff48493.
Lemma F_736f8 : fetch_word AsanUbsan.M.loaded_segments (0x736f8 : word) = Some W_736f8.
Proof. vm_refl. Qed.
Lemma D_736f8 : decode_any W_736f8 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_736fc : bv 32 := 0x00a4f4b3.
Lemma F_736fc : fetch_word AsanUbsan.M.loaded_segments (0x736fc : word) = Some W_736fc.
Proof. vm_refl. Qed.
Lemma D_736fc : decode_any W_736fc = Some (Op ALU_AND 9 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_73700 : bv 32 := 0x02200513.
Lemma F_73700 : fetch_word AsanUbsan.M.loaded_segments (0x73700 : word) = Some W_73700.
Proof. vm_refl. Qed.
Lemma D_73700 : decode_any W_73700 = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_73704 : bv 32 := 0x00a12623.
Lemma F_73704 : fetch_word AsanUbsan.M.loaded_segments (0x73704 : word) = Some W_73704.
Proof. vm_refl. Qed.
Lemma D_73704 : decode_any W_73704 = Some (Store SZ4 2 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73708 : bv 32 := 0x00c10613.
Lemma F_73708 : fetch_word AsanUbsan.M.loaded_segments (0x73708 : word) = Some W_73708.
Proof. vm_refl. Qed.
Lemma D_73708 : decode_any W_73708 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7370c : bv 32 := 0x00040513.
Lemma F_7370c : fetch_word AsanUbsan.M.loaded_segments (0x7370c : word) = Some W_7370c.
Proof. vm_refl. Qed.
Lemma D_7370c : decode_any W_7370c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73710 : bv 32 := 0x00048593.
Lemma F_73710 : fetch_word AsanUbsan.M.loaded_segments (0x73710 : word) = Some W_73710.
Proof. vm_refl. Qed.
Lemma D_73710 : decode_any W_73710 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73714 : bv 32 := 0x279000ef.
Lemma F_73714 : fetch_word AsanUbsan.M.loaded_segments (0x73714 : word) = Some W_73714.
Proof. vm_refl. Qed.
Lemma D_73714 : decode_any W_73714 = Some (Jal 1 2680, 4%Z).
Proof. vm_refl. Qed.

Definition W_73718 : bv 32 := 0x00c12683.
Lemma F_73718 : fetch_word AsanUbsan.M.loaded_segments (0x73718 : word) = Some W_73718.
Proof. vm_refl. Qed.
Lemma D_73718 : decode_any W_73718 = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7371c : bv 32 := 0x00050713.
Lemma F_7371c : fetch_word AsanUbsan.M.loaded_segments (0x7371c : word) = Some W_7371c.
Proof. vm_refl. Qed.
Lemma D_7371c : decode_any W_7371c = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73720 : bv 32 := 0x00300613.
Lemma F_73720 : fetch_word AsanUbsan.M.loaded_segments (0x73720 : word) = Some W_73720.
Proof. vm_refl. Qed.
Lemma D_73720 : decode_any W_73720 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_73724 : bv 32 := 0x00000513.
Lemma F_73724 : fetch_word AsanUbsan.M.loaded_segments (0x73724 : word) = Some W_73724.
Proof. vm_refl. Qed.
Lemma D_73724 : decode_any W_73724 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73728 : bv 32 := 0x00048593.
Lemma F_73728 : fetch_word AsanUbsan.M.loaded_segments (0x73728 : word) = Some W_73728.
Proof. vm_refl. Qed.
Lemma D_73728 : decode_any W_73728 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7372c : bv 32 := 0x00000793.
Lemma F_7372c : fetch_word AsanUbsan.M.loaded_segments (0x7372c : word) = Some W_7372c.
Proof. vm_refl. Qed.
Lemma D_7372c : decode_any W_7372c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73730 : bv 32 := 0xeb0fe0ef.
Lemma F_73730 : fetch_word AsanUbsan.M.loaded_segments (0x73730 : word) = Some W_73730.
Proof. vm_refl. Qed.
Lemma D_73730 : decode_any W_73730 = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

Definition W_73734 : bv 32 := 0x00050913.
Lemma F_73734 : fetch_word AsanUbsan.M.loaded_segments (0x73734 : word) = Some W_73734.
Proof. vm_refl. Qed.
Lemma D_73734 : decode_any W_73734 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73738 : bv 32 := 0x00000593.
Lemma F_73738 : fetch_word AsanUbsan.M.loaded_segments (0x73738 : word) = Some W_73738.
Proof. vm_refl. Qed.
Lemma D_73738 : decode_any W_73738 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7373c : bv 32 := 0xe84fe0ef.
Lemma F_7373c : fetch_word AsanUbsan.M.loaded_segments (0x7373c : word) = Some W_7373c.
Proof. vm_refl. Qed.
Lemma D_7373c : decode_any W_7373c = Some (Jal 1 2090628, 4%Z).
Proof. vm_refl. Qed.

Definition W_73740 : bv 32 := 0xaaaab537.
Lemma F_73740 : fetch_word AsanUbsan.M.loaded_segments (0x73740 : word) = Some W_73740.
Proof. vm_refl. Qed.
Lemma D_73740 : decode_any W_73740 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_73744 : bv 32 := 0xaaa50513.
Lemma F_73744 : fetch_word AsanUbsan.M.loaded_segments (0x73744 : word) = Some W_73744.
Proof. vm_refl. Qed.
Lemma D_73744 : decode_any W_73744 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_73748 : bv 32 := 0x00a12423.
Lemma F_73748 : fetch_word AsanUbsan.M.loaded_segments (0x73748 : word) = Some W_73748.
Proof. vm_refl. Qed.
Lemma D_73748 : decode_any W_73748 = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7374c : bv 32 := 0x00810593.
Lemma F_7374c : fetch_word AsanUbsan.M.loaded_segments (0x7374c : word) = Some W_7374c.
Proof. vm_refl. Qed.
Lemma D_7374c : decode_any W_7374c = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_73750 : bv 32 := 0x00090513.
Lemma F_73750 : fetch_word AsanUbsan.M.loaded_segments (0x73750 : word) = Some W_73750.
Proof. vm_refl. Qed.
Lemma D_73750 : decode_any W_73750 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73754 : bv 32 := 0xe6cfe0ef.
Lemma F_73754 : fetch_word AsanUbsan.M.loaded_segments (0x73754 : word) = Some W_73754.
Proof. vm_refl. Qed.
Lemma D_73754 : decode_any W_73754 = Some (Jal 1 2090604, 4%Z).
Proof. vm_refl. Qed.

Definition W_73758 : bv 32 := 0x02051c63.
Lemma F_73758 : fetch_word AsanUbsan.M.loaded_segments (0x73758 : word) = Some W_73758.
Proof. vm_refl. Qed.
Lemma D_73758 : decode_any W_73758 = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7375c : bv 32 := 0x00048513.
Lemma F_7375c : fetch_word AsanUbsan.M.loaded_segments (0x7375c : word) = Some W_7375c.
Proof. vm_refl. Qed.
Lemma D_7375c : decode_any W_7375c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73760 : bv 32 := 0xd64fa0ef.
Lemma F_73760 : fetch_word AsanUbsan.M.loaded_segments (0x73760 : word) = Some W_73760.
Proof. vm_refl. Qed.
Lemma D_73760 : decode_any W_73760 = Some (Jal 1 2073956, 4%Z).
Proof. vm_refl. Qed.

Definition W_73764 : bv 32 := 0x00090513.
Lemma F_73764 : fetch_word AsanUbsan.M.loaded_segments (0x73764 : word) = Some W_73764.
Proof. vm_refl. Qed.
Lemma D_73764 : decode_any W_73764 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73768 : bv 32 := 0x02813083.
Lemma F_73768 : fetch_word AsanUbsan.M.loaded_segments (0x73768 : word) = Some W_73768.
Proof. vm_refl. Qed.
Lemma D_73768 : decode_any W_73768 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7376c : bv 32 := 0x02013403.
Lemma F_7376c : fetch_word AsanUbsan.M.loaded_segments (0x7376c : word) = Some W_7376c.
Proof. vm_refl. Qed.
Lemma D_7376c : decode_any W_7376c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_73770 : bv 32 := 0x01813483.
Lemma F_73770 : fetch_word AsanUbsan.M.loaded_segments (0x73770 : word) = Some W_73770.
Proof. vm_refl. Qed.
Lemma D_73770 : decode_any W_73770 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_73774 : bv 32 := 0x01013903.
Lemma F_73774 : fetch_word AsanUbsan.M.loaded_segments (0x73774 : word) = Some W_73774.
Proof. vm_refl. Qed.
Lemma D_73774 : decode_any W_73774 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73778 : bv 32 := 0x03010113.
Lemma F_73778 : fetch_word AsanUbsan.M.loaded_segments (0x73778 : word) = Some W_73778.
Proof. vm_refl. Qed.
Lemma D_73778 : decode_any W_73778 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7377c : bv 32 := 0x00008067.
Lemma F_7377c : fetch_word AsanUbsan.M.loaded_segments (0x7377c : word) = Some W_7377c.
Proof. vm_refl. Qed.
Lemma D_7377c : decode_any W_7377c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73780 : bv 32 := 0xfff9f517.
Lemma F_73780 : fetch_word AsanUbsan.M.loaded_segments (0x73780 : word) = Some W_73780.
Proof. vm_refl. Qed.
Lemma D_73780 : decode_any W_73780 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_73784 : bv 32 := 0xff250513.
Lemma F_73784 : fetch_word AsanUbsan.M.loaded_segments (0x73784 : word) = Some W_73784.
Proof. vm_refl. Qed.
Lemma D_73784 : decode_any W_73784 = Some (OpImm ALU_ADD 10 10 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_73788 : bv 32 := 0xd0dfa0ef.
Lemma F_73788 : fetch_word AsanUbsan.M.loaded_segments (0x73788 : word) = Some W_73788.
Proof. vm_refl. Qed.
Lemma D_73788 : decode_any W_73788 = Some (Jal 1 2075916, 4%Z).
Proof. vm_refl. Qed.

Definition W_7378c : bv 32 := 0x291050ef.
Lemma F_7378c : fetch_word AsanUbsan.M.loaded_segments (0x7378c : word) = Some W_7378c.
Proof. vm_refl. Qed.
Lemma D_7378c : decode_any W_7378c = Some (Jal 1 23184, 4%Z).
Proof. vm_refl. Qed.

Definition W_73790 : bv 32 := 0x00812683.
Lemma F_73790 : fetch_word AsanUbsan.M.loaded_segments (0x73790 : word) = Some W_73790.
Proof. vm_refl. Qed.
Lemma D_73790 : decode_any W_73790 = Some (Load SZ4 true 13 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_73794 : bv 32 := 0x00c00513.
Lemma F_73794 : fetch_word AsanUbsan.M.loaded_segments (0x73794 : word) = Some W_73794.
Proof. vm_refl. Qed.
Lemma D_73794 : decode_any W_73794 = Some (OpImm ALU_ADD 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73798 : bv 32 := 0x00a69663.
Lemma F_73798 : fetch_word AsanUbsan.M.loaded_segments (0x73798 : word) = Some W_73798.
Proof. vm_refl. Qed.
Lemma D_73798 : decode_any W_73798 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7379c : bv 32 := 0x00000913.
Lemma F_7379c : fetch_word AsanUbsan.M.loaded_segments (0x7379c : word) = Some W_7379c.
Proof. vm_refl. Qed.
Lemma D_7379c : decode_any W_7379c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_737a0 : bv 32 := 0xfc5ff06f.
Lemma F_737a0 : fetch_word AsanUbsan.M.loaded_segments (0x737a0 : word) = Some W_737a0.
Proof. vm_refl. Qed.
Lemma D_737a0 : decode_any W_737a0 = Some (Jal 0 2097092, 4%Z).
Proof. vm_refl. Qed.

Definition W_737a4 : bv 32 := 0xfffa7517.
Lemma F_737a4 : fetch_word AsanUbsan.M.loaded_segments (0x737a4 : word) = Some W_737a4.
Proof. vm_refl. Qed.
Lemma D_737a4 : decode_any W_737a4 = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_737a8 : bv 32 := 0x43450613.
Lemma F_737a8 : fetch_word AsanUbsan.M.loaded_segments (0x737a8 : word) = Some W_737a8.
Proof. vm_refl. Qed.
Lemma D_737a8 : decode_any W_737a8 = Some (OpImm ALU_ADD 12 10 1076, 4%Z).
Proof. vm_refl. Qed.

Definition W_737ac : bv 32 := 0x00048513.
Lemma F_737ac : fetch_word AsanUbsan.M.loaded_segments (0x737ac : word) = Some W_737ac.
Proof. vm_refl. Qed.
Lemma D_737ac : decode_any W_737ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_737b0 : bv 32 := 0x00040593.
Lemma F_737b0 : fetch_word AsanUbsan.M.loaded_segments (0x737b0 : word) = Some W_737b0.
Proof. vm_refl. Qed.
Lemma D_737b0 : decode_any W_737b0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_737b4 : bv 32 := 0x00000713.
Lemma F_737b4 : fetch_word AsanUbsan.M.loaded_segments (0x737b4 : word) = Some W_737b4.
Proof. vm_refl. Qed.
Lemma D_737b4 : decode_any W_737b4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_737b8 : bv 32 := 0xe75f90ef.
Lemma F_737b8 : fetch_word AsanUbsan.M.loaded_segments (0x737b8 : word) = Some W_737b8.
Proof. vm_refl. Qed.
Lemma D_737b8 : decode_any W_737b8 = Some (Jal 1 2072180, 4%Z).
Proof. vm_refl. Qed.
