(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_63344 : bv 32 := 0x02060063.
Lemma D_63344 : decode_any W_63344 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63348 : bv 32 := 0x00c50633.
Lemma D_63348 : decode_any W_63348 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6334c : bv 32 := 0x00050693.
Lemma D_6334c : decode_any W_6334c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63350 : bv 32 := 0x0005c703.
Lemma D_63350 : decode_any W_63350 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63354 : bv 32 := 0x00e68023.
Lemma D_63354 : decode_any W_63354 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63358 : bv 32 := 0x00168693.
Lemma D_63358 : decode_any W_63358 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6335c : bv 32 := 0x00158593.
Lemma D_6335c : decode_any W_6335c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63360 : bv 32 := 0xfec698e3.
Lemma D_63360 : decode_any W_63360 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63364 : bv 32 := 0x00008067.
Lemma D_63364 : decode_any W_63364 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633c0 : bv 32 := 0x00a666b3.
Lemma D_633c0 : decode_any W_633c0 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633c4 : bv 32 := 0x00f6f693.
Lemma D_633c4 : decode_any W_633c4 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633c8 : bv 32 := 0x02068063.
Lemma D_633c8 : decode_any W_633c8 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633cc : bv 32 := 0x04060863.
Lemma D_633cc : decode_any W_633cc = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633d0 : bv 32 := 0x00c50633.
Lemma D_633d0 : decode_any W_633d0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633d4 : bv 32 := 0x00050693.
Lemma D_633d4 : decode_any W_633d4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633d8 : bv 32 := 0x00b68023.
Lemma D_633d8 : decode_any W_633d8 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633dc : bv 32 := 0x00168693.
Lemma D_633dc : decode_any W_633dc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633e0 : bv 32 := 0xfec69ce3.
Lemma D_633e0 : decode_any W_633e0 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633e4 : bv 32 := 0x0380006f.
Lemma D_633e4 : decode_any W_633e4 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633e8 : bv 32 := 0x02060a63.
Lemma D_633e8 : decode_any W_633e8 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633ec : bv 32 := 0x00c50633.
Lemma D_633ec : decode_any W_633ec = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633f0 : bv 32 := 0x00859693.
Lemma D_633f0 : decode_any W_633f0 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633f4 : bv 32 := 0x00b6e5b3.
Lemma D_633f4 : decode_any W_633f4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633f8 : bv 32 := 0x01059693.
Lemma D_633f8 : decode_any W_633f8 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_633fc : bv 32 := 0x00b6e5b3.
Lemma D_633fc : decode_any W_633fc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63400 : bv 32 := 0x02059693.
Lemma D_63400 : decode_any W_63400 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63404 : bv 32 := 0x00b6e5b3.
Lemma D_63404 : decode_any W_63404 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63408 : bv 32 := 0x00050693.
Lemma D_63408 : decode_any W_63408 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6340c : bv 32 := 0x00b6b023.
Lemma D_6340c : decode_any W_6340c = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63410 : bv 32 := 0x00b6b423.
Lemma D_63410 : decode_any W_63410 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63414 : bv 32 := 0x01068693.
Lemma D_63414 : decode_any W_63414 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63418 : bv 32 := 0xfec6eae3.
Lemma D_63418 : decode_any W_63418 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6341c : bv 32 := 0x00008067.
Lemma D_6341c : decode_any W_6341c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638f0 : bv 32 := 0xff010113.
Lemma D_638f0 : decode_any W_638f0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638f4 : bv 32 := 0x00113423.
Lemma D_638f4 : decode_any W_638f4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638f8 : bv 32 := 0x00058693.
Lemma D_638f8 : decode_any W_638f8 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_638fc : bv 32 := 0x00100713.
Lemma D_638fc : decode_any W_638fc = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63900 : bv 32 := 0x02871713.
Lemma D_63900 : decode_any W_63900 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63904 : bv 32 := 0x00170593.
Lemma D_63904 : decode_any W_63904 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63908 : bv 32 := 0x08b6f263.
Lemma D_63908 : decode_any W_63908 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6390c : bv 32 := 0x00000593.
Lemma D_6390c : decode_any W_6390c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63910 : bv 32 := 0x00d50733.
Lemma D_63910 : decode_any W_63910 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63914 : bv 32 := 0x00750793.
Lemma D_63914 : decode_any W_63914 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63918 : bv 32 := 0xff87f793.
Lemma D_63918 : decode_any W_63918 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6391c : bv 32 := 0xff877613.
Lemma D_6391c : decode_any W_6391c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63920 : bv 32 := 0x02f57463.
Lemma D_63920 : decode_any W_63920 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63924 : bv 32 := 0x02068263.
Lemma D_63924 : decode_any W_63924 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63928 : bv 32 := 0x00000593.
Lemma D_63928 : decode_any W_63928 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6392c : bv 32 := 0x00150693.
Lemma D_6392c : decode_any W_6392c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63930 : bv 32 := 0x00068813.
Lemma D_63930 : decode_any W_63930 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63934 : bv 32 := 0xfff6c683.
Lemma D_63934 : decode_any W_63934 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63938 : bv 32 := 0x00d5e5b3.
Lemma D_63938 : decode_any W_63938 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6393c : bv 32 := 0x00f87663.
Lemma D_6393c : decode_any W_6393c = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63940 : bv 32 := 0x00180693.
Lemma D_63940 : decode_any W_63940 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63944 : bv 32 := 0xfee866e3.
Lemma D_63944 : decode_any W_63944 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63948 : bv 32 := 0x00c7fa63.
Lemma D_63948 : decode_any W_63948 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6394c : bv 32 := 0x0007b683.
Lemma D_6394c : decode_any W_6394c = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63950 : bv 32 := 0x00878793.
Lemma D_63950 : decode_any W_63950 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63954 : bv 32 := 0x00b6e5b3.
Lemma D_63954 : decode_any W_63954 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63958 : bv 32 := 0xfec7eae3.
Lemma D_63958 : decode_any W_63958 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6395c : bv 32 := 0x02a66063.
Lemma D_6395c : decode_any W_6395c = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63960 : bv 32 := 0x00e67e63.
Lemma D_63960 : decode_any W_63960 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63964 : bv 32 := 0x40c70733.
Lemma D_63964 : decode_any W_63964 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63968 : bv 32 := 0x00064503.
Lemma D_63968 : decode_any W_63968 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6396c : bv 32 := 0xfff70713.
Lemma D_6396c : decode_any W_6396c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63970 : bv 32 := 0x00a5e5b3.
Lemma D_63970 : decode_any W_63970 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63974 : bv 32 := 0x00160613.
Lemma D_63974 : decode_any W_63974 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63978 : bv 32 := 0xfe0718e3.
Lemma D_63978 : decode_any W_63978 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6397c : bv 32 := 0x0015b513.
Lemma D_6397c : decode_any W_6397c = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63980 : bv 32 := 0x00813083.
Lemma D_63980 : decode_any W_63980 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63984 : bv 32 := 0x01010113.
Lemma D_63984 : decode_any W_63984 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63988 : bv 32 := 0x00008067.
Lemma D_63988 : decode_any W_63988 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
