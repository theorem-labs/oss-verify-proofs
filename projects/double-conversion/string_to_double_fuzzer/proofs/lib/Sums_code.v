(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require BvKH.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_879cc : bv 32 := 0x02060063.
Lemma D_879cc : decode_any W_879cc = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879d0 : bv 32 := 0x00c50633.
Lemma D_879d0 : decode_any W_879d0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879d4 : bv 32 := 0x00050693.
Lemma D_879d4 : decode_any W_879d4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879d8 : bv 32 := 0x0005c703.
Lemma D_879d8 : decode_any W_879d8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879dc : bv 32 := 0x00e68023.
Lemma D_879dc : decode_any W_879dc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879e0 : bv 32 := 0x00168693.
Lemma D_879e0 : decode_any W_879e0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879e4 : bv 32 := 0x00158593.
Lemma D_879e4 : decode_any W_879e4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879e8 : bv 32 := 0xfec698e3.
Lemma D_879e8 : decode_any W_879e8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879ec : bv 32 := 0x00008067.
Lemma D_879ec : decode_any W_879ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a48 : bv 32 := 0x00a666b3.
Lemma D_87a48 : decode_any W_87a48 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a4c : bv 32 := 0x00f6f693.
Lemma D_87a4c : decode_any W_87a4c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a50 : bv 32 := 0x02068063.
Lemma D_87a50 : decode_any W_87a50 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a54 : bv 32 := 0x04060863.
Lemma D_87a54 : decode_any W_87a54 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a58 : bv 32 := 0x00c50633.
Lemma D_87a58 : decode_any W_87a58 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a5c : bv 32 := 0x00050693.
Lemma D_87a5c : decode_any W_87a5c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a60 : bv 32 := 0x00b68023.
Lemma D_87a60 : decode_any W_87a60 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a64 : bv 32 := 0x00168693.
Lemma D_87a64 : decode_any W_87a64 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a68 : bv 32 := 0xfec69ce3.
Lemma D_87a68 : decode_any W_87a68 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a6c : bv 32 := 0x0380006f.
Lemma D_87a6c : decode_any W_87a6c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a70 : bv 32 := 0x02060a63.
Lemma D_87a70 : decode_any W_87a70 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a74 : bv 32 := 0x00c50633.
Lemma D_87a74 : decode_any W_87a74 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a78 : bv 32 := 0x00859693.
Lemma D_87a78 : decode_any W_87a78 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a7c : bv 32 := 0x00b6e5b3.
Lemma D_87a7c : decode_any W_87a7c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a80 : bv 32 := 0x01059693.
Lemma D_87a80 : decode_any W_87a80 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a84 : bv 32 := 0x00b6e5b3.
Lemma D_87a84 : decode_any W_87a84 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a88 : bv 32 := 0x02059693.
Lemma D_87a88 : decode_any W_87a88 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a8c : bv 32 := 0x00b6e5b3.
Lemma D_87a8c : decode_any W_87a8c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a90 : bv 32 := 0x00050693.
Lemma D_87a90 : decode_any W_87a90 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a94 : bv 32 := 0x00b6b023.
Lemma D_87a94 : decode_any W_87a94 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a98 : bv 32 := 0x00b6b423.
Lemma D_87a98 : decode_any W_87a98 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a9c : bv 32 := 0x01068693.
Lemma D_87a9c : decode_any W_87a9c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87aa0 : bv 32 := 0xfec6eae3.
Lemma D_87aa0 : decode_any W_87aa0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87aa4 : bv 32 := 0x00008067.
Lemma D_87aa4 : decode_any W_87aa4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87f94 : bv 32 := 0xff010113.
Lemma D_87f94 : decode_any W_87f94 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87f98 : bv 32 := 0x00113423.
Lemma D_87f98 : decode_any W_87f98 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87f9c : bv 32 := 0x00058693.
Lemma D_87f9c : decode_any W_87f9c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fa0 : bv 32 := 0x00100713.
Lemma D_87fa0 : decode_any W_87fa0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fa4 : bv 32 := 0x02871713.
Lemma D_87fa4 : decode_any W_87fa4 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fa8 : bv 32 := 0x00170593.
Lemma D_87fa8 : decode_any W_87fa8 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fac : bv 32 := 0x08b6f263.
Lemma D_87fac : decode_any W_87fac = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fb0 : bv 32 := 0x00000593.
Lemma D_87fb0 : decode_any W_87fb0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fb4 : bv 32 := 0x00d50733.
Lemma D_87fb4 : decode_any W_87fb4 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fb8 : bv 32 := 0x00750793.
Lemma D_87fb8 : decode_any W_87fb8 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fbc : bv 32 := 0xff87f793.
Lemma D_87fbc : decode_any W_87fbc = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fc0 : bv 32 := 0xff877613.
Lemma D_87fc0 : decode_any W_87fc0 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fc4 : bv 32 := 0x02f57463.
Lemma D_87fc4 : decode_any W_87fc4 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fc8 : bv 32 := 0x02068263.
Lemma D_87fc8 : decode_any W_87fc8 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fcc : bv 32 := 0x00000593.
Lemma D_87fcc : decode_any W_87fcc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fd0 : bv 32 := 0x00150693.
Lemma D_87fd0 : decode_any W_87fd0 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fd4 : bv 32 := 0x00068813.
Lemma D_87fd4 : decode_any W_87fd4 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fd8 : bv 32 := 0xfff6c683.
Lemma D_87fd8 : decode_any W_87fd8 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fdc : bv 32 := 0x00d5e5b3.
Lemma D_87fdc : decode_any W_87fdc = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe0 : bv 32 := 0x00f87663.
Lemma D_87fe0 : decode_any W_87fe0 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe4 : bv 32 := 0x00180693.
Lemma D_87fe4 : decode_any W_87fe4 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe8 : bv 32 := 0xfee866e3.
Lemma D_87fe8 : decode_any W_87fe8 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fec : bv 32 := 0x00c7fa63.
Lemma D_87fec : decode_any W_87fec = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ff0 : bv 32 := 0x0007b683.
Lemma D_87ff0 : decode_any W_87ff0 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ff4 : bv 32 := 0x00878793.
Lemma D_87ff4 : decode_any W_87ff4 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ff8 : bv 32 := 0x00b6e5b3.
Lemma D_87ff8 : decode_any W_87ff8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ffc : bv 32 := 0xfec7eae3.
Lemma D_87ffc : decode_any W_87ffc = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88000 : bv 32 := 0x02a66063.
Lemma D_88000 : decode_any W_88000 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88004 : bv 32 := 0x00e67e63.
Lemma D_88004 : decode_any W_88004 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88008 : bv 32 := 0x40c70733.
Lemma D_88008 : decode_any W_88008 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8800c : bv 32 := 0x00064503.
Lemma D_8800c : decode_any W_8800c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88010 : bv 32 := 0xfff70713.
Lemma D_88010 : decode_any W_88010 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88014 : bv 32 := 0x00a5e5b3.
Lemma D_88014 : decode_any W_88014 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88018 : bv 32 := 0x00160613.
Lemma D_88018 : decode_any W_88018 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8801c : bv 32 := 0xfe0718e3.
Lemma D_8801c : decode_any W_8801c = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88020 : bv 32 := 0x0015b513.
Lemma D_88020 : decode_any W_88020 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88024 : bv 32 := 0x00813083.
Lemma D_88024 : decode_any W_88024 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88028 : bv 32 := 0x01010113.
Lemma D_88028 : decode_any W_88028 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8802c : bv 32 := 0x00008067.
Lemma D_8802c : decode_any W_8802c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
