(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_862f4 : bv 32 := 0x02060063.
Lemma D_862f4 : decode_any W_862f4 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_862f8 : bv 32 := 0x00c50633.
Lemma D_862f8 : decode_any W_862f8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_862fc : bv 32 := 0x00050693.
Lemma D_862fc : decode_any W_862fc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86300 : bv 32 := 0x0005c703.
Lemma D_86300 : decode_any W_86300 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86304 : bv 32 := 0x00e68023.
Lemma D_86304 : decode_any W_86304 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86308 : bv 32 := 0x00168693.
Lemma D_86308 : decode_any W_86308 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8630c : bv 32 := 0x00158593.
Lemma D_8630c : decode_any W_8630c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86310 : bv 32 := 0xfec698e3.
Lemma D_86310 : decode_any W_86310 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86314 : bv 32 := 0x00008067.
Lemma D_86314 : decode_any W_86314 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86370 : bv 32 := 0x00a666b3.
Lemma D_86370 : decode_any W_86370 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86374 : bv 32 := 0x00f6f693.
Lemma D_86374 : decode_any W_86374 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86378 : bv 32 := 0x02068063.
Lemma D_86378 : decode_any W_86378 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8637c : bv 32 := 0x04060863.
Lemma D_8637c : decode_any W_8637c = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86380 : bv 32 := 0x00c50633.
Lemma D_86380 : decode_any W_86380 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86384 : bv 32 := 0x00050693.
Lemma D_86384 : decode_any W_86384 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86388 : bv 32 := 0x00b68023.
Lemma D_86388 : decode_any W_86388 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8638c : bv 32 := 0x00168693.
Lemma D_8638c : decode_any W_8638c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86390 : bv 32 := 0xfec69ce3.
Lemma D_86390 : decode_any W_86390 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86394 : bv 32 := 0x0380006f.
Lemma D_86394 : decode_any W_86394 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86398 : bv 32 := 0x02060a63.
Lemma D_86398 : decode_any W_86398 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8639c : bv 32 := 0x00c50633.
Lemma D_8639c : decode_any W_8639c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863a0 : bv 32 := 0x00859693.
Lemma D_863a0 : decode_any W_863a0 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863a4 : bv 32 := 0x00b6e5b3.
Lemma D_863a4 : decode_any W_863a4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863a8 : bv 32 := 0x01059693.
Lemma D_863a8 : decode_any W_863a8 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863ac : bv 32 := 0x00b6e5b3.
Lemma D_863ac : decode_any W_863ac = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863b0 : bv 32 := 0x02059693.
Lemma D_863b0 : decode_any W_863b0 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863b4 : bv 32 := 0x00b6e5b3.
Lemma D_863b4 : decode_any W_863b4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863b8 : bv 32 := 0x00050693.
Lemma D_863b8 : decode_any W_863b8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863bc : bv 32 := 0x00b6b023.
Lemma D_863bc : decode_any W_863bc = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863c0 : bv 32 := 0x00b6b423.
Lemma D_863c0 : decode_any W_863c0 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863c4 : bv 32 := 0x01068693.
Lemma D_863c4 : decode_any W_863c4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863c8 : bv 32 := 0xfec6eae3.
Lemma D_863c8 : decode_any W_863c8 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_863cc : bv 32 := 0x00008067.
Lemma D_863cc : decode_any W_863cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868a0 : bv 32 := 0xff010113.
Lemma D_868a0 : decode_any W_868a0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868a4 : bv 32 := 0x00113423.
Lemma D_868a4 : decode_any W_868a4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868a8 : bv 32 := 0x00058693.
Lemma D_868a8 : decode_any W_868a8 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868ac : bv 32 := 0x00100713.
Lemma D_868ac : decode_any W_868ac = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868b0 : bv 32 := 0x02871713.
Lemma D_868b0 : decode_any W_868b0 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868b4 : bv 32 := 0x00170593.
Lemma D_868b4 : decode_any W_868b4 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868b8 : bv 32 := 0x08b6f263.
Lemma D_868b8 : decode_any W_868b8 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868bc : bv 32 := 0x00000593.
Lemma D_868bc : decode_any W_868bc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868c0 : bv 32 := 0x00d50733.
Lemma D_868c0 : decode_any W_868c0 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868c4 : bv 32 := 0x00750793.
Lemma D_868c4 : decode_any W_868c4 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868c8 : bv 32 := 0xff87f793.
Lemma D_868c8 : decode_any W_868c8 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868cc : bv 32 := 0xff877613.
Lemma D_868cc : decode_any W_868cc = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868d0 : bv 32 := 0x02f57463.
Lemma D_868d0 : decode_any W_868d0 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868d4 : bv 32 := 0x02068263.
Lemma D_868d4 : decode_any W_868d4 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868d8 : bv 32 := 0x00000593.
Lemma D_868d8 : decode_any W_868d8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868dc : bv 32 := 0x00150693.
Lemma D_868dc : decode_any W_868dc = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868e0 : bv 32 := 0x00068813.
Lemma D_868e0 : decode_any W_868e0 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868e4 : bv 32 := 0xfff6c683.
Lemma D_868e4 : decode_any W_868e4 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868e8 : bv 32 := 0x00d5e5b3.
Lemma D_868e8 : decode_any W_868e8 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868ec : bv 32 := 0x00f87663.
Lemma D_868ec : decode_any W_868ec = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868f0 : bv 32 := 0x00180693.
Lemma D_868f0 : decode_any W_868f0 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868f4 : bv 32 := 0xfee866e3.
Lemma D_868f4 : decode_any W_868f4 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868f8 : bv 32 := 0x00c7fa63.
Lemma D_868f8 : decode_any W_868f8 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_868fc : bv 32 := 0x0007b683.
Lemma D_868fc : decode_any W_868fc = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86900 : bv 32 := 0x00878793.
Lemma D_86900 : decode_any W_86900 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86904 : bv 32 := 0x00b6e5b3.
Lemma D_86904 : decode_any W_86904 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86908 : bv 32 := 0xfec7eae3.
Lemma D_86908 : decode_any W_86908 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8690c : bv 32 := 0x02a66063.
Lemma D_8690c : decode_any W_8690c = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86910 : bv 32 := 0x00e67e63.
Lemma D_86910 : decode_any W_86910 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86914 : bv 32 := 0x40c70733.
Lemma D_86914 : decode_any W_86914 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86918 : bv 32 := 0x00064503.
Lemma D_86918 : decode_any W_86918 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8691c : bv 32 := 0xfff70713.
Lemma D_8691c : decode_any W_8691c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86920 : bv 32 := 0x00a5e5b3.
Lemma D_86920 : decode_any W_86920 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86924 : bv 32 := 0x00160613.
Lemma D_86924 : decode_any W_86924 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86928 : bv 32 := 0xfe0718e3.
Lemma D_86928 : decode_any W_86928 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8692c : bv 32 := 0x0015b513.
Lemma D_8692c : decode_any W_8692c = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86930 : bv 32 := 0x00813083.
Lemma D_86930 : decode_any W_86930 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86934 : bv 32 := 0x01010113.
Lemma D_86934 : decode_any W_86934 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86938 : bv 32 := 0x00008067.
Lemma D_86938 : decode_any W_86938 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
