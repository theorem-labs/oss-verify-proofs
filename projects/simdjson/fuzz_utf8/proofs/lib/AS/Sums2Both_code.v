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

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_93454 : bv 32 := 0x06060663.
Lemma D_93454 : decode_any W_93454 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93458 : bv 32 := 0x00000693.
Lemma D_93458 : decode_any W_93458 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9345c : bv 32 := 0x00d58733.
Lemma D_9345c : decode_any W_9345c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93460 : bv 32 := 0x00074703.
Lemma D_93460 : decode_any W_93460 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93464 : bv 32 := 0x00070c63.
Lemma D_93464 : decode_any W_93464 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93468 : bv 32 := 0x00d507b3.
Lemma D_93468 : decode_any W_93468 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9346c : bv 32 := 0x00168693.
Lemma D_9346c : decode_any W_9346c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93470 : bv 32 := 0x00e78023.
Lemma D_93470 : decode_any W_93470 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93474 : bv 32 := 0xfed614e3.
Lemma D_93474 : decode_any W_93474 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93478 : bv 32 := 0x00060693.
Lemma D_93478 : decode_any W_93478 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9347c : bv 32 := 0x00d505b3.
Lemma D_9347c : decode_any W_9347c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93480 : bv 32 := 0x40d6073b.
Lemma D_93480 : decode_any W_93480 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93484 : bv 32 := 0x00b76733.
Lemma D_93484 : decode_any W_93484 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93488 : bv 32 := 0x00f77713.
Lemma D_93488 : decode_any W_93488 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9348c : bv 32 := 0x00070e63.
Lemma D_9348c : decode_any W_9348c = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93490 : bv 32 := 0x02d60863.
Lemma D_93490 : decode_any W_93490 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93494 : bv 32 := 0x00c50633.
Lemma D_93494 : decode_any W_93494 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93498 : bv 32 := 0x00058023.
Lemma D_93498 : decode_any W_93498 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9349c : bv 32 := 0x00158593.
Lemma D_9349c : decode_any W_9349c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_934a0 : bv 32 := 0xfec59ce3.
Lemma D_934a0 : decode_any W_934a0 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_934a4 : bv 32 := 0x01c0006f.
Lemma D_934a4 : decode_any W_934a4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_934a8 : bv 32 := 0x00d60c63.
Lemma D_934a8 : decode_any W_934a8 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_934ac : bv 32 := 0x00c50633.
Lemma D_934ac : decode_any W_934ac = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_934b0 : bv 32 := 0x0005b023.
Lemma D_934b0 : decode_any W_934b0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_934b4 : bv 32 := 0x0005b423.
Lemma D_934b4 : decode_any W_934b4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_934b8 : bv 32 := 0x01058593.
Lemma D_934b8 : decode_any W_934b8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_934bc : bv 32 := 0xfec5eae3.
Lemma D_934bc : decode_any W_934bc = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_934c0 : bv 32 := 0x00008067.
Lemma D_934c0 : decode_any W_934c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_7f234 : bv 32 := 0x00200613.
Lemma D_7f234 : decode_any W_7f234 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f238 : bv 32 := 0x14c5ea63.
Lemma D_7f238 : decode_any W_7f238 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f23c : bv 32 := 0x00100613.
Lemma D_7f23c : decode_any W_7f23c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f240 : bv 32 := 0x00100693.
Lemma D_7f240 : decode_any W_7f240 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f244 : bv 32 := 0x00c0006f.
Lemma D_7f244 : decode_any W_7f244 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f248 : bv 32 := 0x00160613.
Lemma D_7f248 : decode_any W_7f248 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f24c : bv 32 := 0x12b60c63.
Lemma D_7f24c : decode_any W_7f24c = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f250 : bv 32 := 0x00461713.
Lemma D_7f250 : decode_any W_7f250 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f254 : bv 32 := 0x00e50733.
Lemma D_7f254 : decode_any W_7f254 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f258 : bv 32 := 0x00072703.
Lemma D_7f258 : decode_any W_7f258 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f25c : bv 32 := 0x00060893.
Lemma D_7f25c : decode_any W_7f25c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f260 : bv 32 := 0xfff88793.
Lemma D_7f260 : decode_any W_7f260 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f264 : bv 32 := 0x0017d813.
Lemma D_7f264 : decode_any W_7f264 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f268 : bv 32 := 0x00481293.
Lemma D_7f268 : decode_any W_7f268 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f26c : bv 32 := 0x005502b3.
Lemma D_7f26c : decode_any W_7f26c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f270 : bv 32 := 0x0002a303.
Lemma D_7f270 : decode_any W_7f270 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f274 : bv 32 := 0xfce37ae3.
Lemma D_7f274 : decode_any W_7f274 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f278 : bv 32 := 0x0002b303.
Lemma D_7f278 : decode_any W_7f278 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f27c : bv 32 := 0x00489893.
Lemma D_7f27c : decode_any W_7f27c = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f280 : bv 32 := 0x011508b3.
Lemma D_7f280 : decode_any W_7f280 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f284 : bv 32 := 0x0048a383.
Lemma D_7f284 : decode_any W_7f284 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f288 : bv 32 := 0x0068b023.
Lemma D_7f288 : decode_any W_7f288 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f28c : bv 32 := 0x0082b303.
Lemma D_7f28c : decode_any W_7f28c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f290 : bv 32 := 0x0088be03.
Lemma D_7f290 : decode_any W_7f290 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f294 : bv 32 := 0x0068b423.
Lemma D_7f294 : decode_any W_7f294 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f298 : bv 32 := 0x00e2a023.
Lemma D_7f298 : decode_any W_7f298 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f29c : bv 32 := 0x0072a223.
Lemma D_7f29c : decode_any W_7f29c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2a0 : bv 32 := 0x01c2b423.
Lemma D_7f2a0 : decode_any W_7f2a0 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2a4 : bv 32 := 0x00080893.
Lemma D_7f2a4 : decode_any W_7f2a4 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2a8 : bv 32 := 0xfaf6ece3.
Lemma D_7f2a8 : decode_any W_7f2a8 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2ac : bv 32 := 0xf9dff06f.
Lemma D_7f2ac : decode_any W_7f2ac = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2b0 : bv 32 := 0x00000613.
Lemma D_7f2b0 : decode_any W_7f2b0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2b4 : bv 32 := 0x00459693.
Lemma D_7f2b4 : decode_any W_7f2b4 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2b8 : bv 32 := 0x00d506b3.
Lemma D_7f2b8 : decode_any W_7f2b8 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2bc : bv 32 := 0x0006b703.
Lemma D_7f2bc : decode_any W_7f2bc = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2c0 : bv 32 := 0x0086b783.
Lemma D_7f2c0 : decode_any W_7f2c0 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2c4 : bv 32 := 0x00053803.
Lemma D_7f2c4 : decode_any W_7f2c4 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2c8 : bv 32 := 0x00853883.
Lemma D_7f2c8 : decode_any W_7f2c8 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2cc : bv 32 := 0x00e53023.
Lemma D_7f2cc : decode_any W_7f2cc = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2d0 : bv 32 := 0x00f53423.
Lemma D_7f2d0 : decode_any W_7f2d0 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2d4 : bv 32 := 0x0106b023.
Lemma D_7f2d4 : decode_any W_7f2d4 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2d8 : bv 32 := 0x0116b423.
Lemma D_7f2d8 : decode_any W_7f2d8 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2dc : bv 32 := 0x00000693.
Lemma D_7f2dc : decode_any W_7f2dc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2e0 : bv 32 := 0x00161793.
Lemma D_7f2e0 : decode_any W_7f2e0 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2e4 : bv 32 := 0x00178813.
Lemma D_7f2e4 : decode_any W_7f2e4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2e8 : bv 32 := 0x00461713.
Lemma D_7f2e8 : decode_any W_7f2e8 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2ec : bv 32 := 0x00b86a63.
Lemma D_7f2ec : decode_any W_7f2ec = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2f0 : bv 32 := 0x00278793.
Lemma D_7f2f0 : decode_any W_7f2f0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2f4 : bv 32 := 0x02b7ea63.
Lemma D_7f2f4 : decode_any W_7f2f4 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2f8 : bv 32 := 0x04c69c63.
Lemma D_7f2f8 : decode_any W_7f2f8 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f2fc : bv 32 := 0x0880006f.
Lemma D_7f2fc : decode_any W_7f2fc = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f300 : bv 32 := 0x00e506b3.
Lemma D_7f300 : decode_any W_7f300 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f304 : bv 32 := 0x00481893.
Lemma D_7f304 : decode_any W_7f304 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f308 : bv 32 := 0x011508b3.
Lemma D_7f308 : decode_any W_7f308 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f30c : bv 32 := 0x0006a683.
Lemma D_7f30c : decode_any W_7f30c = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f310 : bv 32 := 0x0008a883.
Lemma D_7f310 : decode_any W_7f310 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f314 : bv 32 := 0x0116e463.
Lemma D_7f314 : decode_any W_7f314 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f318 : bv 32 := 0x00060813.
Lemma D_7f318 : decode_any W_7f318 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f31c : bv 32 := 0x00080693.
Lemma D_7f31c : decode_any W_7f31c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f320 : bv 32 := 0x00278793.
Lemma D_7f320 : decode_any W_7f320 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f324 : bv 32 := 0xfcb7fae3.
Lemma D_7f324 : decode_any W_7f324 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f328 : bv 32 := 0x00469813.
Lemma D_7f328 : decode_any W_7f328 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f32c : bv 32 := 0x00479893.
Lemma D_7f32c : decode_any W_7f32c = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f330 : bv 32 := 0x01050833.
Lemma D_7f330 : decode_any W_7f330 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f334 : bv 32 := 0x011508b3.
Lemma D_7f334 : decode_any W_7f334 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f338 : bv 32 := 0x00082803.
Lemma D_7f338 : decode_any W_7f338 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f33c : bv 32 := 0x0008a883.
Lemma D_7f33c : decode_any W_7f33c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f340 : bv 32 := 0x01186463.
Lemma D_7f340 : decode_any W_7f340 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f344 : bv 32 := 0x00068793.
Lemma D_7f344 : decode_any W_7f344 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f348 : bv 32 := 0x00078693.
Lemma D_7f348 : decode_any W_7f348 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f34c : bv 32 := 0x02c78c63.
Lemma D_7f34c : decode_any W_7f34c = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f350 : bv 32 := 0x00469613.
Lemma D_7f350 : decode_any W_7f350 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f354 : bv 32 := 0x00c50633.
Lemma D_7f354 : decode_any W_7f354 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f358 : bv 32 := 0x00063783.
Lemma D_7f358 : decode_any W_7f358 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f35c : bv 32 := 0x00e50733.
Lemma D_7f35c : decode_any W_7f35c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f360 : bv 32 := 0x00073803.
Lemma D_7f360 : decode_any W_7f360 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f364 : bv 32 := 0x00873883.
Lemma D_7f364 : decode_any W_7f364 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f368 : bv 32 := 0x00f73023.
Lemma D_7f368 : decode_any W_7f368 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f36c : bv 32 := 0x00863783.
Lemma D_7f36c : decode_any W_7f36c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f370 : bv 32 := 0x00f73423.
Lemma D_7f370 : decode_any W_7f370 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f374 : bv 32 := 0x01063023.
Lemma D_7f374 : decode_any W_7f374 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f378 : bv 32 := 0x01163423.
Lemma D_7f378 : decode_any W_7f378 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f37c : bv 32 := 0x00068613.
Lemma D_7f37c : decode_any W_7f37c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f380 : bv 32 := 0xf6b6e0e3.
Lemma D_7f380 : decode_any W_7f380 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f384 : bv 32 := 0xfff58593.
Lemma D_7f384 : decode_any W_7f384 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f388 : bv 32 := 0xf20594e3.
Lemma D_7f388 : decode_any W_7f388 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f38c : bv 32 := 0x00008067.
Lemma D_7f38c : decode_any W_7f38c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
