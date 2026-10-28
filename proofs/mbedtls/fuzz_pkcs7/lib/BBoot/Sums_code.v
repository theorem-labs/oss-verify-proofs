(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7a478 : bv 32 := 0x02060063.
Lemma D_7a478 : decode_any W_7a478 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a47c : bv 32 := 0x00c50633.
Lemma D_7a47c : decode_any W_7a47c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a480 : bv 32 := 0x00050693.
Lemma D_7a480 : decode_any W_7a480 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a484 : bv 32 := 0x0005c703.
Lemma D_7a484 : decode_any W_7a484 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a488 : bv 32 := 0x00e68023.
Lemma D_7a488 : decode_any W_7a488 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a48c : bv 32 := 0x00168693.
Lemma D_7a48c : decode_any W_7a48c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a490 : bv 32 := 0x00158593.
Lemma D_7a490 : decode_any W_7a490 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a494 : bv 32 := 0xfec698e3.
Lemma D_7a494 : decode_any W_7a494 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a498 : bv 32 := 0x00008067.
Lemma D_7a498 : decode_any W_7a498 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f4 : bv 32 := 0x00a666b3.
Lemma D_7a4f4 : decode_any W_7a4f4 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f8 : bv 32 := 0x00f6f693.
Lemma D_7a4f8 : decode_any W_7a4f8 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4fc : bv 32 := 0x02068063.
Lemma D_7a4fc : decode_any W_7a4fc = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a500 : bv 32 := 0x04060863.
Lemma D_7a500 : decode_any W_7a500 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a504 : bv 32 := 0x00c50633.
Lemma D_7a504 : decode_any W_7a504 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a508 : bv 32 := 0x00050693.
Lemma D_7a508 : decode_any W_7a508 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a50c : bv 32 := 0x00b68023.
Lemma D_7a50c : decode_any W_7a50c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a510 : bv 32 := 0x00168693.
Lemma D_7a510 : decode_any W_7a510 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a514 : bv 32 := 0xfec69ce3.
Lemma D_7a514 : decode_any W_7a514 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a518 : bv 32 := 0x0380006f.
Lemma D_7a518 : decode_any W_7a518 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a51c : bv 32 := 0x02060a63.
Lemma D_7a51c : decode_any W_7a51c = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a520 : bv 32 := 0x00c50633.
Lemma D_7a520 : decode_any W_7a520 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a524 : bv 32 := 0x00859693.
Lemma D_7a524 : decode_any W_7a524 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a528 : bv 32 := 0x00b6e5b3.
Lemma D_7a528 : decode_any W_7a528 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a52c : bv 32 := 0x01059693.
Lemma D_7a52c : decode_any W_7a52c = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a530 : bv 32 := 0x00b6e5b3.
Lemma D_7a530 : decode_any W_7a530 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a534 : bv 32 := 0x02059693.
Lemma D_7a534 : decode_any W_7a534 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a538 : bv 32 := 0x00b6e5b3.
Lemma D_7a538 : decode_any W_7a538 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a53c : bv 32 := 0x00050693.
Lemma D_7a53c : decode_any W_7a53c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a540 : bv 32 := 0x00b6b023.
Lemma D_7a540 : decode_any W_7a540 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a544 : bv 32 := 0x00b6b423.
Lemma D_7a544 : decode_any W_7a544 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a548 : bv 32 := 0x01068693.
Lemma D_7a548 : decode_any W_7a548 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a54c : bv 32 := 0xfec6eae3.
Lemma D_7a54c : decode_any W_7a54c = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a550 : bv 32 := 0x00008067.
Lemma D_7a550 : decode_any W_7a550 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa24 : bv 32 := 0xff010113.
Lemma D_7aa24 : decode_any W_7aa24 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa28 : bv 32 := 0x00113423.
Lemma D_7aa28 : decode_any W_7aa28 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa2c : bv 32 := 0x00058693.
Lemma D_7aa2c : decode_any W_7aa2c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa30 : bv 32 := 0x00100713.
Lemma D_7aa30 : decode_any W_7aa30 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa34 : bv 32 := 0x02871713.
Lemma D_7aa34 : decode_any W_7aa34 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa38 : bv 32 := 0x00170593.
Lemma D_7aa38 : decode_any W_7aa38 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa3c : bv 32 := 0x08b6f263.
Lemma D_7aa3c : decode_any W_7aa3c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa40 : bv 32 := 0x00000593.
Lemma D_7aa40 : decode_any W_7aa40 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa44 : bv 32 := 0x00d50733.
Lemma D_7aa44 : decode_any W_7aa44 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa48 : bv 32 := 0x00750793.
Lemma D_7aa48 : decode_any W_7aa48 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa4c : bv 32 := 0xff87f793.
Lemma D_7aa4c : decode_any W_7aa4c = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa50 : bv 32 := 0xff877613.
Lemma D_7aa50 : decode_any W_7aa50 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa54 : bv 32 := 0x02f57463.
Lemma D_7aa54 : decode_any W_7aa54 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa58 : bv 32 := 0x02068263.
Lemma D_7aa58 : decode_any W_7aa58 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa5c : bv 32 := 0x00000593.
Lemma D_7aa5c : decode_any W_7aa5c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa60 : bv 32 := 0x00150693.
Lemma D_7aa60 : decode_any W_7aa60 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa64 : bv 32 := 0x00068813.
Lemma D_7aa64 : decode_any W_7aa64 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa68 : bv 32 := 0xfff6c683.
Lemma D_7aa68 : decode_any W_7aa68 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa6c : bv 32 := 0x00d5e5b3.
Lemma D_7aa6c : decode_any W_7aa6c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa70 : bv 32 := 0x00f87663.
Lemma D_7aa70 : decode_any W_7aa70 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa74 : bv 32 := 0x00180693.
Lemma D_7aa74 : decode_any W_7aa74 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa78 : bv 32 := 0xfee866e3.
Lemma D_7aa78 : decode_any W_7aa78 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa7c : bv 32 := 0x00c7fa63.
Lemma D_7aa7c : decode_any W_7aa7c = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa80 : bv 32 := 0x0007b683.
Lemma D_7aa80 : decode_any W_7aa80 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa84 : bv 32 := 0x00878793.
Lemma D_7aa84 : decode_any W_7aa84 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa88 : bv 32 := 0x00b6e5b3.
Lemma D_7aa88 : decode_any W_7aa88 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa8c : bv 32 := 0xfec7eae3.
Lemma D_7aa8c : decode_any W_7aa8c = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa90 : bv 32 := 0x02a66063.
Lemma D_7aa90 : decode_any W_7aa90 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa94 : bv 32 := 0x00e67e63.
Lemma D_7aa94 : decode_any W_7aa94 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa98 : bv 32 := 0x40c70733.
Lemma D_7aa98 : decode_any W_7aa98 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa9c : bv 32 := 0x00064503.
Lemma D_7aa9c : decode_any W_7aa9c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaa0 : bv 32 := 0xfff70713.
Lemma D_7aaa0 : decode_any W_7aaa0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaa4 : bv 32 := 0x00a5e5b3.
Lemma D_7aaa4 : decode_any W_7aaa4 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaa8 : bv 32 := 0x00160613.
Lemma D_7aaa8 : decode_any W_7aaa8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaac : bv 32 := 0xfe0718e3.
Lemma D_7aaac : decode_any W_7aaac = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aab0 : bv 32 := 0x0015b513.
Lemma D_7aab0 : decode_any W_7aab0 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aab4 : bv 32 := 0x00813083.
Lemma D_7aab4 : decode_any W_7aab4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aab8 : bv 32 := 0x01010113.
Lemma D_7aab8 : decode_any W_7aab8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aabc : bv 32 := 0x00008067.
Lemma D_7aabc : decode_any W_7aabc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
