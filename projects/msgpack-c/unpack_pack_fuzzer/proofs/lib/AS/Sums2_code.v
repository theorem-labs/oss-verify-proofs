(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7045c : bv 32 := 0x06060663.
Lemma D_7045c : decode_any W_7045c = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_70460 : bv 32 := 0x00000693.
Lemma D_70460 : decode_any W_70460 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70464 : bv 32 := 0x00d58733.
Lemma D_70464 : decode_any W_70464 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70468 : bv 32 := 0x00074703.
Lemma D_70468 : decode_any W_70468 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7046c : bv 32 := 0x00070c63.
Lemma D_7046c : decode_any W_7046c = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_70470 : bv 32 := 0x00d507b3.
Lemma D_70470 : decode_any W_70470 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70474 : bv 32 := 0x00168693.
Lemma D_70474 : decode_any W_70474 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70478 : bv 32 := 0x00e78023.
Lemma D_70478 : decode_any W_70478 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7047c : bv 32 := 0xfed614e3.
Lemma D_7047c : decode_any W_7047c = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_70480 : bv 32 := 0x00060693.
Lemma D_70480 : decode_any W_70480 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70484 : bv 32 := 0x00d505b3.
Lemma D_70484 : decode_any W_70484 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70488 : bv 32 := 0x40d6073b.
Lemma D_70488 : decode_any W_70488 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7048c : bv 32 := 0x00b76733.
Lemma D_7048c : decode_any W_7048c = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70490 : bv 32 := 0x00f77713.
Lemma D_70490 : decode_any W_70490 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_70494 : bv 32 := 0x00070e63.
Lemma D_70494 : decode_any W_70494 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70498 : bv 32 := 0x02d60863.
Lemma D_70498 : decode_any W_70498 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7049c : bv 32 := 0x00c50633.
Lemma D_7049c : decode_any W_7049c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_704a0 : bv 32 := 0x00058023.
Lemma D_704a0 : decode_any W_704a0 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_704a4 : bv 32 := 0x00158593.
Lemma D_704a4 : decode_any W_704a4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_704a8 : bv 32 := 0xfec59ce3.
Lemma D_704a8 : decode_any W_704a8 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_704ac : bv 32 := 0x01c0006f.
Lemma D_704ac : decode_any W_704ac = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_704b0 : bv 32 := 0x00d60c63.
Lemma D_704b0 : decode_any W_704b0 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_704b4 : bv 32 := 0x00c50633.
Lemma D_704b4 : decode_any W_704b4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_704b8 : bv 32 := 0x0005b023.
Lemma D_704b8 : decode_any W_704b8 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_704bc : bv 32 := 0x0005b423.
Lemma D_704bc : decode_any W_704bc = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_704c0 : bv 32 := 0x01058593.
Lemma D_704c0 : decode_any W_704c0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_704c4 : bv 32 := 0xfec5eae3.
Lemma D_704c4 : decode_any W_704c4 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_704c8 : bv 32 := 0x00008067.
Lemma D_704c8 : decode_any W_704c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca6c : bv 32 := 0x00200613.
Lemma D_5ca6c : decode_any W_5ca6c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca70 : bv 32 := 0x14c5ea63.
Lemma D_5ca70 : decode_any W_5ca70 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca74 : bv 32 := 0x00100613.
Lemma D_5ca74 : decode_any W_5ca74 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca78 : bv 32 := 0x00100693.
Lemma D_5ca78 : decode_any W_5ca78 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca7c : bv 32 := 0x00c0006f.
Lemma D_5ca7c : decode_any W_5ca7c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca80 : bv 32 := 0x00160613.
Lemma D_5ca80 : decode_any W_5ca80 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca84 : bv 32 := 0x12b60c63.
Lemma D_5ca84 : decode_any W_5ca84 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca88 : bv 32 := 0x00461713.
Lemma D_5ca88 : decode_any W_5ca88 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca8c : bv 32 := 0x00e50733.
Lemma D_5ca8c : decode_any W_5ca8c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca90 : bv 32 := 0x00072703.
Lemma D_5ca90 : decode_any W_5ca90 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca94 : bv 32 := 0x00060893.
Lemma D_5ca94 : decode_any W_5ca94 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca98 : bv 32 := 0xfff88793.
Lemma D_5ca98 : decode_any W_5ca98 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ca9c : bv 32 := 0x0017d813.
Lemma D_5ca9c : decode_any W_5ca9c = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5caa0 : bv 32 := 0x00481293.
Lemma D_5caa0 : decode_any W_5caa0 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5caa4 : bv 32 := 0x005502b3.
Lemma D_5caa4 : decode_any W_5caa4 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5caa8 : bv 32 := 0x0002a303.
Lemma D_5caa8 : decode_any W_5caa8 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5caac : bv 32 := 0xfce37ae3.
Lemma D_5caac : decode_any W_5caac = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cab0 : bv 32 := 0x0002b303.
Lemma D_5cab0 : decode_any W_5cab0 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cab4 : bv 32 := 0x00489893.
Lemma D_5cab4 : decode_any W_5cab4 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cab8 : bv 32 := 0x011508b3.
Lemma D_5cab8 : decode_any W_5cab8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cabc : bv 32 := 0x0048a383.
Lemma D_5cabc : decode_any W_5cabc = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cac0 : bv 32 := 0x0068b023.
Lemma D_5cac0 : decode_any W_5cac0 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cac4 : bv 32 := 0x0082b303.
Lemma D_5cac4 : decode_any W_5cac4 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cac8 : bv 32 := 0x0088be03.
Lemma D_5cac8 : decode_any W_5cac8 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cacc : bv 32 := 0x0068b423.
Lemma D_5cacc : decode_any W_5cacc = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cad0 : bv 32 := 0x00e2a023.
Lemma D_5cad0 : decode_any W_5cad0 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cad4 : bv 32 := 0x0072a223.
Lemma D_5cad4 : decode_any W_5cad4 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cad8 : bv 32 := 0x01c2b423.
Lemma D_5cad8 : decode_any W_5cad8 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cadc : bv 32 := 0x00080893.
Lemma D_5cadc : decode_any W_5cadc = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cae0 : bv 32 := 0xfaf6ece3.
Lemma D_5cae0 : decode_any W_5cae0 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cae4 : bv 32 := 0xf9dff06f.
Lemma D_5cae4 : decode_any W_5cae4 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cae8 : bv 32 := 0x00000613.
Lemma D_5cae8 : decode_any W_5cae8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5caec : bv 32 := 0x00459693.
Lemma D_5caec : decode_any W_5caec = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5caf0 : bv 32 := 0x00d506b3.
Lemma D_5caf0 : decode_any W_5caf0 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5caf4 : bv 32 := 0x0006b703.
Lemma D_5caf4 : decode_any W_5caf4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5caf8 : bv 32 := 0x0086b783.
Lemma D_5caf8 : decode_any W_5caf8 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cafc : bv 32 := 0x00053803.
Lemma D_5cafc : decode_any W_5cafc = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb00 : bv 32 := 0x00853883.
Lemma D_5cb00 : decode_any W_5cb00 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb04 : bv 32 := 0x00e53023.
Lemma D_5cb04 : decode_any W_5cb04 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb08 : bv 32 := 0x00f53423.
Lemma D_5cb08 : decode_any W_5cb08 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb0c : bv 32 := 0x0106b023.
Lemma D_5cb0c : decode_any W_5cb0c = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb10 : bv 32 := 0x0116b423.
Lemma D_5cb10 : decode_any W_5cb10 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb14 : bv 32 := 0x00000693.
Lemma D_5cb14 : decode_any W_5cb14 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb18 : bv 32 := 0x00161793.
Lemma D_5cb18 : decode_any W_5cb18 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb1c : bv 32 := 0x00178813.
Lemma D_5cb1c : decode_any W_5cb1c = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb20 : bv 32 := 0x00461713.
Lemma D_5cb20 : decode_any W_5cb20 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb24 : bv 32 := 0x00b86a63.
Lemma D_5cb24 : decode_any W_5cb24 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb28 : bv 32 := 0x00278793.
Lemma D_5cb28 : decode_any W_5cb28 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb2c : bv 32 := 0x02b7ea63.
Lemma D_5cb2c : decode_any W_5cb2c = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb30 : bv 32 := 0x04c69c63.
Lemma D_5cb30 : decode_any W_5cb30 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb34 : bv 32 := 0x0880006f.
Lemma D_5cb34 : decode_any W_5cb34 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb38 : bv 32 := 0x00e506b3.
Lemma D_5cb38 : decode_any W_5cb38 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb3c : bv 32 := 0x00481893.
Lemma D_5cb3c : decode_any W_5cb3c = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb40 : bv 32 := 0x011508b3.
Lemma D_5cb40 : decode_any W_5cb40 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb44 : bv 32 := 0x0006a683.
Lemma D_5cb44 : decode_any W_5cb44 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb48 : bv 32 := 0x0008a883.
Lemma D_5cb48 : decode_any W_5cb48 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb4c : bv 32 := 0x0116e463.
Lemma D_5cb4c : decode_any W_5cb4c = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb50 : bv 32 := 0x00060813.
Lemma D_5cb50 : decode_any W_5cb50 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb54 : bv 32 := 0x00080693.
Lemma D_5cb54 : decode_any W_5cb54 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb58 : bv 32 := 0x00278793.
Lemma D_5cb58 : decode_any W_5cb58 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb5c : bv 32 := 0xfcb7fae3.
Lemma D_5cb5c : decode_any W_5cb5c = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb60 : bv 32 := 0x00469813.
Lemma D_5cb60 : decode_any W_5cb60 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb64 : bv 32 := 0x00479893.
Lemma D_5cb64 : decode_any W_5cb64 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb68 : bv 32 := 0x01050833.
Lemma D_5cb68 : decode_any W_5cb68 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb6c : bv 32 := 0x011508b3.
Lemma D_5cb6c : decode_any W_5cb6c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb70 : bv 32 := 0x00082803.
Lemma D_5cb70 : decode_any W_5cb70 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb74 : bv 32 := 0x0008a883.
Lemma D_5cb74 : decode_any W_5cb74 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb78 : bv 32 := 0x01186463.
Lemma D_5cb78 : decode_any W_5cb78 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb7c : bv 32 := 0x00068793.
Lemma D_5cb7c : decode_any W_5cb7c = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb80 : bv 32 := 0x00078693.
Lemma D_5cb80 : decode_any W_5cb80 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb84 : bv 32 := 0x02c78c63.
Lemma D_5cb84 : decode_any W_5cb84 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb88 : bv 32 := 0x00469613.
Lemma D_5cb88 : decode_any W_5cb88 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb8c : bv 32 := 0x00c50633.
Lemma D_5cb8c : decode_any W_5cb8c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb90 : bv 32 := 0x00063783.
Lemma D_5cb90 : decode_any W_5cb90 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb94 : bv 32 := 0x00e50733.
Lemma D_5cb94 : decode_any W_5cb94 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb98 : bv 32 := 0x00073803.
Lemma D_5cb98 : decode_any W_5cb98 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cb9c : bv 32 := 0x00873883.
Lemma D_5cb9c : decode_any W_5cb9c = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cba0 : bv 32 := 0x00f73023.
Lemma D_5cba0 : decode_any W_5cba0 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cba4 : bv 32 := 0x00863783.
Lemma D_5cba4 : decode_any W_5cba4 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cba8 : bv 32 := 0x00f73423.
Lemma D_5cba8 : decode_any W_5cba8 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cbac : bv 32 := 0x01063023.
Lemma D_5cbac : decode_any W_5cbac = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cbb0 : bv 32 := 0x01163423.
Lemma D_5cbb0 : decode_any W_5cbb0 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cbb4 : bv 32 := 0x00068613.
Lemma D_5cbb4 : decode_any W_5cbb4 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cbb8 : bv 32 := 0xf6b6e0e3.
Lemma D_5cbb8 : decode_any W_5cbb8 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cbbc : bv 32 := 0xfff58593.
Lemma D_5cbbc : decode_any W_5cbbc = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cbc0 : bv 32 := 0xf20594e3.
Lemma D_5cbc0 : decode_any W_5cbc0 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cbc4 : bv 32 := 0x00008067.
Lemma D_5cbc4 : decode_any W_5cbc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
