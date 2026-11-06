(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_933bc : bv 32 := 0x02060063.
Lemma D_933bc : decode_any W_933bc = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_933c0 : bv 32 := 0x00c50633.
Lemma D_933c0 : decode_any W_933c0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_933c4 : bv 32 := 0x00050693.
Lemma D_933c4 : decode_any W_933c4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_933c8 : bv 32 := 0x0005c703.
Lemma D_933c8 : decode_any W_933c8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_933cc : bv 32 := 0x00e68023.
Lemma D_933cc : decode_any W_933cc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_933d0 : bv 32 := 0x00168693.
Lemma D_933d0 : decode_any W_933d0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_933d4 : bv 32 := 0x00158593.
Lemma D_933d4 : decode_any W_933d4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_933d8 : bv 32 := 0xfec698e3.
Lemma D_933d8 : decode_any W_933d8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_933dc : bv 32 := 0x00008067.
Lemma D_933dc : decode_any W_933dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_93438 : bv 32 := 0x00a666b3.
Lemma D_93438 : decode_any W_93438 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9343c : bv 32 := 0x00f6f693.
Lemma D_9343c : decode_any W_9343c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93440 : bv 32 := 0x02068063.
Lemma D_93440 : decode_any W_93440 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93444 : bv 32 := 0x04060863.
Lemma D_93444 : decode_any W_93444 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93448 : bv 32 := 0x00c50633.
Lemma D_93448 : decode_any W_93448 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9344c : bv 32 := 0x00050693.
Lemma D_9344c : decode_any W_9344c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93450 : bv 32 := 0x00b68023.
Lemma D_93450 : decode_any W_93450 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93454 : bv 32 := 0x00168693.
Lemma D_93454 : decode_any W_93454 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93458 : bv 32 := 0xfec69ce3.
Lemma D_93458 : decode_any W_93458 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9345c : bv 32 := 0x0380006f.
Lemma D_9345c : decode_any W_9345c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93460 : bv 32 := 0x02060a63.
Lemma D_93460 : decode_any W_93460 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93464 : bv 32 := 0x00c50633.
Lemma D_93464 : decode_any W_93464 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93468 : bv 32 := 0x00859693.
Lemma D_93468 : decode_any W_93468 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9346c : bv 32 := 0x00b6e5b3.
Lemma D_9346c : decode_any W_9346c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93470 : bv 32 := 0x01059693.
Lemma D_93470 : decode_any W_93470 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93474 : bv 32 := 0x00b6e5b3.
Lemma D_93474 : decode_any W_93474 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93478 : bv 32 := 0x02059693.
Lemma D_93478 : decode_any W_93478 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9347c : bv 32 := 0x00b6e5b3.
Lemma D_9347c : decode_any W_9347c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93480 : bv 32 := 0x00050693.
Lemma D_93480 : decode_any W_93480 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93484 : bv 32 := 0x00b6b023.
Lemma D_93484 : decode_any W_93484 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93488 : bv 32 := 0x00b6b423.
Lemma D_93488 : decode_any W_93488 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9348c : bv 32 := 0x01068693.
Lemma D_9348c : decode_any W_9348c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93490 : bv 32 := 0xfec6eae3.
Lemma D_93490 : decode_any W_93490 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93494 : bv 32 := 0x00008067.
Lemma D_93494 : decode_any W_93494 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_93864 : bv 32 := 0x06060663.
Lemma D_93864 : decode_any W_93864 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93868 : bv 32 := 0x00000693.
Lemma D_93868 : decode_any W_93868 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9386c : bv 32 := 0x00d58733.
Lemma D_9386c : decode_any W_9386c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93870 : bv 32 := 0x00074703.
Lemma D_93870 : decode_any W_93870 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93874 : bv 32 := 0x00070c63.
Lemma D_93874 : decode_any W_93874 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93878 : bv 32 := 0x00d507b3.
Lemma D_93878 : decode_any W_93878 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9387c : bv 32 := 0x00168693.
Lemma D_9387c : decode_any W_9387c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93880 : bv 32 := 0x00e78023.
Lemma D_93880 : decode_any W_93880 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93884 : bv 32 := 0xfed614e3.
Lemma D_93884 : decode_any W_93884 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93888 : bv 32 := 0x00060693.
Lemma D_93888 : decode_any W_93888 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9388c : bv 32 := 0x00d505b3.
Lemma D_9388c : decode_any W_9388c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93890 : bv 32 := 0x40d6073b.
Lemma D_93890 : decode_any W_93890 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93894 : bv 32 := 0x00b76733.
Lemma D_93894 : decode_any W_93894 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93898 : bv 32 := 0x00f77713.
Lemma D_93898 : decode_any W_93898 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9389c : bv 32 := 0x00070e63.
Lemma D_9389c : decode_any W_9389c = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938a0 : bv 32 := 0x02d60863.
Lemma D_938a0 : decode_any W_938a0 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938a4 : bv 32 := 0x00c50633.
Lemma D_938a4 : decode_any W_938a4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938a8 : bv 32 := 0x00058023.
Lemma D_938a8 : decode_any W_938a8 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938ac : bv 32 := 0x00158593.
Lemma D_938ac : decode_any W_938ac = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938b0 : bv 32 := 0xfec59ce3.
Lemma D_938b0 : decode_any W_938b0 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938b4 : bv 32 := 0x01c0006f.
Lemma D_938b4 : decode_any W_938b4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938b8 : bv 32 := 0x00d60c63.
Lemma D_938b8 : decode_any W_938b8 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938bc : bv 32 := 0x00c50633.
Lemma D_938bc : decode_any W_938bc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938c0 : bv 32 := 0x0005b023.
Lemma D_938c0 : decode_any W_938c0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938c4 : bv 32 := 0x0005b423.
Lemma D_938c4 : decode_any W_938c4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938c8 : bv 32 := 0x01058593.
Lemma D_938c8 : decode_any W_938c8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938cc : bv 32 := 0xfec5eae3.
Lemma D_938cc : decode_any W_938cc = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_938d0 : bv 32 := 0x00008067.
Lemma D_938d0 : decode_any W_938d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_93968 : bv 32 := 0xff010113.
Lemma D_93968 : decode_any W_93968 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9396c : bv 32 := 0x00113423.
Lemma D_9396c : decode_any W_9396c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93970 : bv 32 := 0x00058693.
Lemma D_93970 : decode_any W_93970 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93974 : bv 32 := 0x00100713.
Lemma D_93974 : decode_any W_93974 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93978 : bv 32 := 0x02871713.
Lemma D_93978 : decode_any W_93978 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9397c : bv 32 := 0x00170593.
Lemma D_9397c : decode_any W_9397c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93980 : bv 32 := 0x08b6f263.
Lemma D_93980 : decode_any W_93980 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93984 : bv 32 := 0x00000593.
Lemma D_93984 : decode_any W_93984 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93988 : bv 32 := 0x00d50733.
Lemma D_93988 : decode_any W_93988 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9398c : bv 32 := 0x00750793.
Lemma D_9398c : decode_any W_9398c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93990 : bv 32 := 0xff87f793.
Lemma D_93990 : decode_any W_93990 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93994 : bv 32 := 0xff877613.
Lemma D_93994 : decode_any W_93994 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93998 : bv 32 := 0x02f57463.
Lemma D_93998 : decode_any W_93998 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9399c : bv 32 := 0x02068263.
Lemma D_9399c : decode_any W_9399c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939a0 : bv 32 := 0x00000593.
Lemma D_939a0 : decode_any W_939a0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939a4 : bv 32 := 0x00150693.
Lemma D_939a4 : decode_any W_939a4 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939a8 : bv 32 := 0x00068813.
Lemma D_939a8 : decode_any W_939a8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939ac : bv 32 := 0xfff6c683.
Lemma D_939ac : decode_any W_939ac = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939b0 : bv 32 := 0x00d5e5b3.
Lemma D_939b0 : decode_any W_939b0 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939b4 : bv 32 := 0x00f87663.
Lemma D_939b4 : decode_any W_939b4 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939b8 : bv 32 := 0x00180693.
Lemma D_939b8 : decode_any W_939b8 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939bc : bv 32 := 0xfee866e3.
Lemma D_939bc : decode_any W_939bc = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939c0 : bv 32 := 0x00c7fa63.
Lemma D_939c0 : decode_any W_939c0 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939c4 : bv 32 := 0x0007b683.
Lemma D_939c4 : decode_any W_939c4 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939c8 : bv 32 := 0x00878793.
Lemma D_939c8 : decode_any W_939c8 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939cc : bv 32 := 0x00b6e5b3.
Lemma D_939cc : decode_any W_939cc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939d0 : bv 32 := 0xfec7eae3.
Lemma D_939d0 : decode_any W_939d0 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939d4 : bv 32 := 0x02a66063.
Lemma D_939d4 : decode_any W_939d4 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939d8 : bv 32 := 0x00e67e63.
Lemma D_939d8 : decode_any W_939d8 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939dc : bv 32 := 0x40c70733.
Lemma D_939dc : decode_any W_939dc = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939e0 : bv 32 := 0x00064503.
Lemma D_939e0 : decode_any W_939e0 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939e4 : bv 32 := 0xfff70713.
Lemma D_939e4 : decode_any W_939e4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939e8 : bv 32 := 0x00a5e5b3.
Lemma D_939e8 : decode_any W_939e8 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939ec : bv 32 := 0x00160613.
Lemma D_939ec : decode_any W_939ec = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939f0 : bv 32 := 0xfe0718e3.
Lemma D_939f0 : decode_any W_939f0 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939f4 : bv 32 := 0x0015b513.
Lemma D_939f4 : decode_any W_939f4 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939f8 : bv 32 := 0x00813083.
Lemma D_939f8 : decode_any W_939f8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939fc : bv 32 := 0x01010113.
Lemma D_939fc : decode_any W_939fc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93a00 : bv 32 := 0x00008067.
Lemma D_93a00 : decode_any W_93a00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_80bd8 : bv 32 := 0x00200613.
Lemma D_80bd8 : decode_any W_80bd8 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bdc : bv 32 := 0x14c5ea63.
Lemma D_80bdc : decode_any W_80bdc = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80be0 : bv 32 := 0x00100613.
Lemma D_80be0 : decode_any W_80be0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80be4 : bv 32 := 0x00100693.
Lemma D_80be4 : decode_any W_80be4 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80be8 : bv 32 := 0x00c0006f.
Lemma D_80be8 : decode_any W_80be8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bec : bv 32 := 0x00160613.
Lemma D_80bec : decode_any W_80bec = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bf0 : bv 32 := 0x12b60c63.
Lemma D_80bf0 : decode_any W_80bf0 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bf4 : bv 32 := 0x00461713.
Lemma D_80bf4 : decode_any W_80bf4 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bf8 : bv 32 := 0x00e50733.
Lemma D_80bf8 : decode_any W_80bf8 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80bfc : bv 32 := 0x00072703.
Lemma D_80bfc : decode_any W_80bfc = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c00 : bv 32 := 0x00060893.
Lemma D_80c00 : decode_any W_80c00 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c04 : bv 32 := 0xfff88793.
Lemma D_80c04 : decode_any W_80c04 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c08 : bv 32 := 0x0017d813.
Lemma D_80c08 : decode_any W_80c08 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c0c : bv 32 := 0x00481293.
Lemma D_80c0c : decode_any W_80c0c = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c10 : bv 32 := 0x005502b3.
Lemma D_80c10 : decode_any W_80c10 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c14 : bv 32 := 0x0002a303.
Lemma D_80c14 : decode_any W_80c14 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c18 : bv 32 := 0xfce37ae3.
Lemma D_80c18 : decode_any W_80c18 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c1c : bv 32 := 0x0002b303.
Lemma D_80c1c : decode_any W_80c1c = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c20 : bv 32 := 0x00489893.
Lemma D_80c20 : decode_any W_80c20 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c24 : bv 32 := 0x011508b3.
Lemma D_80c24 : decode_any W_80c24 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c28 : bv 32 := 0x0048a383.
Lemma D_80c28 : decode_any W_80c28 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c2c : bv 32 := 0x0068b023.
Lemma D_80c2c : decode_any W_80c2c = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c30 : bv 32 := 0x0082b303.
Lemma D_80c30 : decode_any W_80c30 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c34 : bv 32 := 0x0088be03.
Lemma D_80c34 : decode_any W_80c34 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c38 : bv 32 := 0x0068b423.
Lemma D_80c38 : decode_any W_80c38 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c3c : bv 32 := 0x00e2a023.
Lemma D_80c3c : decode_any W_80c3c = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c40 : bv 32 := 0x0072a223.
Lemma D_80c40 : decode_any W_80c40 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c44 : bv 32 := 0x01c2b423.
Lemma D_80c44 : decode_any W_80c44 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c48 : bv 32 := 0x00080893.
Lemma D_80c48 : decode_any W_80c48 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c4c : bv 32 := 0xfaf6ece3.
Lemma D_80c4c : decode_any W_80c4c = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c50 : bv 32 := 0xf9dff06f.
Lemma D_80c50 : decode_any W_80c50 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c54 : bv 32 := 0x00000613.
Lemma D_80c54 : decode_any W_80c54 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c58 : bv 32 := 0x00459693.
Lemma D_80c58 : decode_any W_80c58 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c5c : bv 32 := 0x00d506b3.
Lemma D_80c5c : decode_any W_80c5c = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c60 : bv 32 := 0x0006b703.
Lemma D_80c60 : decode_any W_80c60 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c64 : bv 32 := 0x0086b783.
Lemma D_80c64 : decode_any W_80c64 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c68 : bv 32 := 0x00053803.
Lemma D_80c68 : decode_any W_80c68 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c6c : bv 32 := 0x00853883.
Lemma D_80c6c : decode_any W_80c6c = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c70 : bv 32 := 0x00e53023.
Lemma D_80c70 : decode_any W_80c70 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c74 : bv 32 := 0x00f53423.
Lemma D_80c74 : decode_any W_80c74 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c78 : bv 32 := 0x0106b023.
Lemma D_80c78 : decode_any W_80c78 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c7c : bv 32 := 0x0116b423.
Lemma D_80c7c : decode_any W_80c7c = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c80 : bv 32 := 0x00000693.
Lemma D_80c80 : decode_any W_80c80 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c84 : bv 32 := 0x00161793.
Lemma D_80c84 : decode_any W_80c84 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c88 : bv 32 := 0x00178813.
Lemma D_80c88 : decode_any W_80c88 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c8c : bv 32 := 0x00461713.
Lemma D_80c8c : decode_any W_80c8c = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c90 : bv 32 := 0x00b86a63.
Lemma D_80c90 : decode_any W_80c90 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c94 : bv 32 := 0x00278793.
Lemma D_80c94 : decode_any W_80c94 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c98 : bv 32 := 0x02b7ea63.
Lemma D_80c98 : decode_any W_80c98 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80c9c : bv 32 := 0x04c69c63.
Lemma D_80c9c : decode_any W_80c9c = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ca0 : bv 32 := 0x0880006f.
Lemma D_80ca0 : decode_any W_80ca0 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ca4 : bv 32 := 0x00e506b3.
Lemma D_80ca4 : decode_any W_80ca4 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ca8 : bv 32 := 0x00481893.
Lemma D_80ca8 : decode_any W_80ca8 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cac : bv 32 := 0x011508b3.
Lemma D_80cac : decode_any W_80cac = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cb0 : bv 32 := 0x0006a683.
Lemma D_80cb0 : decode_any W_80cb0 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cb4 : bv 32 := 0x0008a883.
Lemma D_80cb4 : decode_any W_80cb4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cb8 : bv 32 := 0x0116e463.
Lemma D_80cb8 : decode_any W_80cb8 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cbc : bv 32 := 0x00060813.
Lemma D_80cbc : decode_any W_80cbc = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cc0 : bv 32 := 0x00080693.
Lemma D_80cc0 : decode_any W_80cc0 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cc4 : bv 32 := 0x00278793.
Lemma D_80cc4 : decode_any W_80cc4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cc8 : bv 32 := 0xfcb7fae3.
Lemma D_80cc8 : decode_any W_80cc8 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ccc : bv 32 := 0x00469813.
Lemma D_80ccc : decode_any W_80ccc = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cd0 : bv 32 := 0x00479893.
Lemma D_80cd0 : decode_any W_80cd0 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cd4 : bv 32 := 0x01050833.
Lemma D_80cd4 : decode_any W_80cd4 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cd8 : bv 32 := 0x011508b3.
Lemma D_80cd8 : decode_any W_80cd8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cdc : bv 32 := 0x00082803.
Lemma D_80cdc : decode_any W_80cdc = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ce0 : bv 32 := 0x0008a883.
Lemma D_80ce0 : decode_any W_80ce0 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ce4 : bv 32 := 0x01186463.
Lemma D_80ce4 : decode_any W_80ce4 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80ce8 : bv 32 := 0x00068793.
Lemma D_80ce8 : decode_any W_80ce8 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cec : bv 32 := 0x00078693.
Lemma D_80cec : decode_any W_80cec = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cf0 : bv 32 := 0x02c78c63.
Lemma D_80cf0 : decode_any W_80cf0 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cf4 : bv 32 := 0x00469613.
Lemma D_80cf4 : decode_any W_80cf4 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cf8 : bv 32 := 0x00c50633.
Lemma D_80cf8 : decode_any W_80cf8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80cfc : bv 32 := 0x00063783.
Lemma D_80cfc : decode_any W_80cfc = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d00 : bv 32 := 0x00e50733.
Lemma D_80d00 : decode_any W_80d00 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d04 : bv 32 := 0x00073803.
Lemma D_80d04 : decode_any W_80d04 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d08 : bv 32 := 0x00873883.
Lemma D_80d08 : decode_any W_80d08 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d0c : bv 32 := 0x00f73023.
Lemma D_80d0c : decode_any W_80d0c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d10 : bv 32 := 0x00863783.
Lemma D_80d10 : decode_any W_80d10 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d14 : bv 32 := 0x00f73423.
Lemma D_80d14 : decode_any W_80d14 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d18 : bv 32 := 0x01063023.
Lemma D_80d18 : decode_any W_80d18 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d1c : bv 32 := 0x01163423.
Lemma D_80d1c : decode_any W_80d1c = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d20 : bv 32 := 0x00068613.
Lemma D_80d20 : decode_any W_80d20 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d24 : bv 32 := 0xf6b6e0e3.
Lemma D_80d24 : decode_any W_80d24 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d28 : bv 32 := 0xfff58593.
Lemma D_80d28 : decode_any W_80d28 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d2c : bv 32 := 0xf20594e3.
Lemma D_80d2c : decode_any W_80d2c = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80d30 : bv 32 := 0x00008067.
Lemma D_80d30 : decode_any W_80d30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

