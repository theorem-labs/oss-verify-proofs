(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_69cd0 : bv 32 := 0x06060663.
Lemma D_69cd0 : decode_any W_69cd0 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cd4 : bv 32 := 0x00000693.
Lemma D_69cd4 : decode_any W_69cd4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cd8 : bv 32 := 0x00d58733.
Lemma D_69cd8 : decode_any W_69cd8 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cdc : bv 32 := 0x00074703.
Lemma D_69cdc : decode_any W_69cdc = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ce0 : bv 32 := 0x00070c63.
Lemma D_69ce0 : decode_any W_69ce0 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ce4 : bv 32 := 0x00d507b3.
Lemma D_69ce4 : decode_any W_69ce4 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ce8 : bv 32 := 0x00168693.
Lemma D_69ce8 : decode_any W_69ce8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cec : bv 32 := 0x00e78023.
Lemma D_69cec : decode_any W_69cec = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cf0 : bv 32 := 0xfed614e3.
Lemma D_69cf0 : decode_any W_69cf0 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cf4 : bv 32 := 0x00060693.
Lemma D_69cf4 : decode_any W_69cf4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cf8 : bv 32 := 0x00d505b3.
Lemma D_69cf8 : decode_any W_69cf8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cfc : bv 32 := 0x40d6073b.
Lemma D_69cfc : decode_any W_69cfc = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d00 : bv 32 := 0x00b76733.
Lemma D_69d00 : decode_any W_69d00 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d04 : bv 32 := 0x00f77713.
Lemma D_69d04 : decode_any W_69d04 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d08 : bv 32 := 0x00070e63.
Lemma D_69d08 : decode_any W_69d08 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d0c : bv 32 := 0x02d60863.
Lemma D_69d0c : decode_any W_69d0c = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d10 : bv 32 := 0x00c50633.
Lemma D_69d10 : decode_any W_69d10 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d14 : bv 32 := 0x00058023.
Lemma D_69d14 : decode_any W_69d14 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d18 : bv 32 := 0x00158593.
Lemma D_69d18 : decode_any W_69d18 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d1c : bv 32 := 0xfec59ce3.
Lemma D_69d1c : decode_any W_69d1c = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d20 : bv 32 := 0x01c0006f.
Lemma D_69d20 : decode_any W_69d20 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d24 : bv 32 := 0x00d60c63.
Lemma D_69d24 : decode_any W_69d24 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d28 : bv 32 := 0x00c50633.
Lemma D_69d28 : decode_any W_69d28 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d2c : bv 32 := 0x0005b023.
Lemma D_69d2c : decode_any W_69d2c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d30 : bv 32 := 0x0005b423.
Lemma D_69d30 : decode_any W_69d30 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d34 : bv 32 := 0x01058593.
Lemma D_69d34 : decode_any W_69d34 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d38 : bv 32 := 0xfec5eae3.
Lemma D_69d38 : decode_any W_69d38 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d3c : bv 32 := 0x00008067.
Lemma D_69d3c : decode_any W_69d3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56378 : bv 32 := 0x00200613.
Lemma D_56378 : decode_any W_56378 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5637c : bv 32 := 0x14c5ea63.
Lemma D_5637c : decode_any W_5637c = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_56380 : bv 32 := 0x00100613.
Lemma D_56380 : decode_any W_56380 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_56384 : bv 32 := 0x00100693.
Lemma D_56384 : decode_any W_56384 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_56388 : bv 32 := 0x00c0006f.
Lemma D_56388 : decode_any W_56388 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5638c : bv 32 := 0x00160613.
Lemma D_5638c : decode_any W_5638c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_56390 : bv 32 := 0x12b60c63.
Lemma D_56390 : decode_any W_56390 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_56394 : bv 32 := 0x00461713.
Lemma D_56394 : decode_any W_56394 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_56398 : bv 32 := 0x00e50733.
Lemma D_56398 : decode_any W_56398 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5639c : bv 32 := 0x00072703.
Lemma D_5639c : decode_any W_5639c = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_563a0 : bv 32 := 0x00060893.
Lemma D_563a0 : decode_any W_563a0 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_563a4 : bv 32 := 0xfff88793.
Lemma D_563a4 : decode_any W_563a4 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_563a8 : bv 32 := 0x0017d813.
Lemma D_563a8 : decode_any W_563a8 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_563ac : bv 32 := 0x00481293.
Lemma D_563ac : decode_any W_563ac = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_563b0 : bv 32 := 0x005502b3.
Lemma D_563b0 : decode_any W_563b0 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_563b4 : bv 32 := 0x0002a303.
Lemma D_563b4 : decode_any W_563b4 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_563b8 : bv 32 := 0xfce37ae3.
Lemma D_563b8 : decode_any W_563b8 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_563bc : bv 32 := 0x0002b303.
Lemma D_563bc : decode_any W_563bc = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_563c0 : bv 32 := 0x00489893.
Lemma D_563c0 : decode_any W_563c0 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_563c4 : bv 32 := 0x011508b3.
Lemma D_563c4 : decode_any W_563c4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_563c8 : bv 32 := 0x0048a383.
Lemma D_563c8 : decode_any W_563c8 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_563cc : bv 32 := 0x0068b023.
Lemma D_563cc : decode_any W_563cc = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_563d0 : bv 32 := 0x0082b303.
Lemma D_563d0 : decode_any W_563d0 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_563d4 : bv 32 := 0x0088be03.
Lemma D_563d4 : decode_any W_563d4 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_563d8 : bv 32 := 0x0068b423.
Lemma D_563d8 : decode_any W_563d8 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_563dc : bv 32 := 0x00e2a023.
Lemma D_563dc : decode_any W_563dc = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_563e0 : bv 32 := 0x0072a223.
Lemma D_563e0 : decode_any W_563e0 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_563e4 : bv 32 := 0x01c2b423.
Lemma D_563e4 : decode_any W_563e4 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_563e8 : bv 32 := 0x00080893.
Lemma D_563e8 : decode_any W_563e8 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_563ec : bv 32 := 0xfaf6ece3.
Lemma D_563ec : decode_any W_563ec = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_563f0 : bv 32 := 0xf9dff06f.
Lemma D_563f0 : decode_any W_563f0 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

Definition W_563f4 : bv 32 := 0x00000613.
Lemma D_563f4 : decode_any W_563f4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_563f8 : bv 32 := 0x00459693.
Lemma D_563f8 : decode_any W_563f8 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_563fc : bv 32 := 0x00d506b3.
Lemma D_563fc : decode_any W_563fc = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_56400 : bv 32 := 0x0006b703.
Lemma D_56400 : decode_any W_56400 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56404 : bv 32 := 0x0086b783.
Lemma D_56404 : decode_any W_56404 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_56408 : bv 32 := 0x00053803.
Lemma D_56408 : decode_any W_56408 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5640c : bv 32 := 0x00853883.
Lemma D_5640c : decode_any W_5640c = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_56410 : bv 32 := 0x00e53023.
Lemma D_56410 : decode_any W_56410 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56414 : bv 32 := 0x00f53423.
Lemma D_56414 : decode_any W_56414 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_56418 : bv 32 := 0x0106b023.
Lemma D_56418 : decode_any W_56418 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5641c : bv 32 := 0x0116b423.
Lemma D_5641c : decode_any W_5641c = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_56420 : bv 32 := 0x00000693.
Lemma D_56420 : decode_any W_56420 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56424 : bv 32 := 0x00161793.
Lemma D_56424 : decode_any W_56424 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_56428 : bv 32 := 0x00178813.
Lemma D_56428 : decode_any W_56428 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5642c : bv 32 := 0x00461713.
Lemma D_5642c : decode_any W_5642c = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_56430 : bv 32 := 0x00b86a63.
Lemma D_56430 : decode_any W_56430 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_56434 : bv 32 := 0x00278793.
Lemma D_56434 : decode_any W_56434 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_56438 : bv 32 := 0x02b7ea63.
Lemma D_56438 : decode_any W_56438 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5643c : bv 32 := 0x04c69c63.
Lemma D_5643c : decode_any W_5643c = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_56440 : bv 32 := 0x0880006f.
Lemma D_56440 : decode_any W_56440 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_56444 : bv 32 := 0x00e506b3.
Lemma D_56444 : decode_any W_56444 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_56448 : bv 32 := 0x00481893.
Lemma D_56448 : decode_any W_56448 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5644c : bv 32 := 0x011508b3.
Lemma D_5644c : decode_any W_5644c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_56450 : bv 32 := 0x0006a683.
Lemma D_56450 : decode_any W_56450 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56454 : bv 32 := 0x0008a883.
Lemma D_56454 : decode_any W_56454 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56458 : bv 32 := 0x0116e463.
Lemma D_56458 : decode_any W_56458 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5645c : bv 32 := 0x00060813.
Lemma D_5645c : decode_any W_5645c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56460 : bv 32 := 0x00080693.
Lemma D_56460 : decode_any W_56460 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56464 : bv 32 := 0x00278793.
Lemma D_56464 : decode_any W_56464 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_56468 : bv 32 := 0xfcb7fae3.
Lemma D_56468 : decode_any W_56468 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5646c : bv 32 := 0x00469813.
Lemma D_5646c : decode_any W_5646c = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_56470 : bv 32 := 0x00479893.
Lemma D_56470 : decode_any W_56470 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_56474 : bv 32 := 0x01050833.
Lemma D_56474 : decode_any W_56474 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_56478 : bv 32 := 0x011508b3.
Lemma D_56478 : decode_any W_56478 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5647c : bv 32 := 0x00082803.
Lemma D_5647c : decode_any W_5647c = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56480 : bv 32 := 0x0008a883.
Lemma D_56480 : decode_any W_56480 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56484 : bv 32 := 0x01186463.
Lemma D_56484 : decode_any W_56484 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_56488 : bv 32 := 0x00068793.
Lemma D_56488 : decode_any W_56488 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5648c : bv 32 := 0x00078693.
Lemma D_5648c : decode_any W_5648c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_56490 : bv 32 := 0x02c78c63.
Lemma D_56490 : decode_any W_56490 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_56494 : bv 32 := 0x00469613.
Lemma D_56494 : decode_any W_56494 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_56498 : bv 32 := 0x00c50633.
Lemma D_56498 : decode_any W_56498 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5649c : bv 32 := 0x00063783.
Lemma D_5649c : decode_any W_5649c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_564a0 : bv 32 := 0x00e50733.
Lemma D_564a0 : decode_any W_564a0 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_564a4 : bv 32 := 0x00073803.
Lemma D_564a4 : decode_any W_564a4 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_564a8 : bv 32 := 0x00873883.
Lemma D_564a8 : decode_any W_564a8 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_564ac : bv 32 := 0x00f73023.
Lemma D_564ac : decode_any W_564ac = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_564b0 : bv 32 := 0x00863783.
Lemma D_564b0 : decode_any W_564b0 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_564b4 : bv 32 := 0x00f73423.
Lemma D_564b4 : decode_any W_564b4 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_564b8 : bv 32 := 0x01063023.
Lemma D_564b8 : decode_any W_564b8 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_564bc : bv 32 := 0x01163423.
Lemma D_564bc : decode_any W_564bc = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_564c0 : bv 32 := 0x00068613.
Lemma D_564c0 : decode_any W_564c0 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_564c4 : bv 32 := 0xf6b6e0e3.
Lemma D_564c4 : decode_any W_564c4 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_564c8 : bv 32 := 0xfff58593.
Lemma D_564c8 : decode_any W_564c8 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_564cc : bv 32 := 0xf20594e3.
Lemma D_564cc : decode_any W_564cc = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_564d0 : bv 32 := 0x00008067.
Lemma D_564d0 : decode_any W_564d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
