(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_cc524 : bv 32 := 0x06060663.
Lemma D_cc524 : decode_any W_cc524 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc528 : bv 32 := 0x00000693.
Lemma D_cc528 : decode_any W_cc528 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc52c : bv 32 := 0x00d58733.
Lemma D_cc52c : decode_any W_cc52c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc530 : bv 32 := 0x00074703.
Lemma D_cc530 : decode_any W_cc530 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc534 : bv 32 := 0x00070c63.
Lemma D_cc534 : decode_any W_cc534 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc538 : bv 32 := 0x00d507b3.
Lemma D_cc538 : decode_any W_cc538 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc53c : bv 32 := 0x00168693.
Lemma D_cc53c : decode_any W_cc53c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc540 : bv 32 := 0x00e78023.
Lemma D_cc540 : decode_any W_cc540 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc544 : bv 32 := 0xfed614e3.
Lemma D_cc544 : decode_any W_cc544 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc548 : bv 32 := 0x00060693.

Definition W_cc54c : bv 32 := 0x00d505b3.
Lemma D_cc54c : decode_any W_cc54c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc550 : bv 32 := 0x40d6073b.
Lemma D_cc550 : decode_any W_cc550 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc554 : bv 32 := 0x00b76733.
Lemma D_cc554 : decode_any W_cc554 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc558 : bv 32 := 0x00f77713.
Lemma D_cc558 : decode_any W_cc558 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc55c : bv 32 := 0x00070e63.
Lemma D_cc55c : decode_any W_cc55c = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc560 : bv 32 := 0x02d60863.
Lemma D_cc560 : decode_any W_cc560 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc564 : bv 32 := 0x00c50633.
Lemma D_cc564 : decode_any W_cc564 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc568 : bv 32 := 0x00058023.
Lemma D_cc568 : decode_any W_cc568 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc56c : bv 32 := 0x00158593.
Lemma D_cc56c : decode_any W_cc56c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc570 : bv 32 := 0xfec59ce3.
Lemma D_cc570 : decode_any W_cc570 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc574 : bv 32 := 0x01c0006f.
Lemma D_cc574 : decode_any W_cc574 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc578 : bv 32 := 0x00d60c63.

Definition W_cc57c : bv 32 := 0x00c50633.

Definition W_cc580 : bv 32 := 0x0005b023.

Definition W_cc584 : bv 32 := 0x0005b423.

Definition W_cc588 : bv 32 := 0x01058593.

Definition W_cc58c : bv 32 := 0xfec5eae3.

Definition W_cc590 : bv 32 := 0x00008067.
Lemma D_cc590 : decode_any W_cc590 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b8304 : bv 32 := 0x00200613.

Definition W_b8308 : bv 32 := 0x14c5ea63.

Definition W_b830c : bv 32 := 0x00100613.

Definition W_b8310 : bv 32 := 0x00100693.

Definition W_b8314 : bv 32 := 0x00c0006f.

Definition W_b8318 : bv 32 := 0x00160613.

Definition W_b831c : bv 32 := 0x12b60c63.

Definition W_b8320 : bv 32 := 0x00461713.

Definition W_b8324 : bv 32 := 0x00e50733.

Definition W_b8328 : bv 32 := 0x00072703.

Definition W_b832c : bv 32 := 0x00060893.

Definition W_b8330 : bv 32 := 0xfff88793.

Definition W_b8334 : bv 32 := 0x0017d813.

Definition W_b8338 : bv 32 := 0x00481293.

Definition W_b833c : bv 32 := 0x005502b3.

Definition W_b8340 : bv 32 := 0x0002a303.

Definition W_b8344 : bv 32 := 0xfce37ae3.

Definition W_b8348 : bv 32 := 0x0002b303.

Definition W_b834c : bv 32 := 0x00489893.

Definition W_b8350 : bv 32 := 0x011508b3.

Definition W_b8354 : bv 32 := 0x0048a383.

Definition W_b8358 : bv 32 := 0x0068b023.

Definition W_b835c : bv 32 := 0x0082b303.

Definition W_b8360 : bv 32 := 0x0088be03.

Definition W_b8364 : bv 32 := 0x0068b423.

Definition W_b8368 : bv 32 := 0x00e2a023.

Definition W_b836c : bv 32 := 0x0072a223.

Definition W_b8370 : bv 32 := 0x01c2b423.

Definition W_b8374 : bv 32 := 0x00080893.

Definition W_b8378 : bv 32 := 0xfaf6ece3.

Definition W_b837c : bv 32 := 0xf9dff06f.

Definition W_b8380 : bv 32 := 0x00000613.

Definition W_b8384 : bv 32 := 0x00459693.

Definition W_b8388 : bv 32 := 0x00d506b3.

Definition W_b838c : bv 32 := 0x0006b703.

Definition W_b8390 : bv 32 := 0x0086b783.

Definition W_b8394 : bv 32 := 0x00053803.

Definition W_b8398 : bv 32 := 0x00853883.

Definition W_b839c : bv 32 := 0x00e53023.

Definition W_b83a0 : bv 32 := 0x00f53423.

Definition W_b83a4 : bv 32 := 0x0106b023.

Definition W_b83a8 : bv 32 := 0x0116b423.

Definition W_b83ac : bv 32 := 0x00000693.

Definition W_b83b0 : bv 32 := 0x00161793.

Definition W_b83b4 : bv 32 := 0x00178813.

Definition W_b83b8 : bv 32 := 0x00461713.

Definition W_b83bc : bv 32 := 0x00b86a63.

Definition W_b83c0 : bv 32 := 0x00278793.

Definition W_b83c4 : bv 32 := 0x02b7ea63.

Definition W_b83c8 : bv 32 := 0x04c69c63.

Definition W_b83cc : bv 32 := 0x0880006f.

Definition W_b83d0 : bv 32 := 0x00e506b3.

Definition W_b83d4 : bv 32 := 0x00481893.

Definition W_b83d8 : bv 32 := 0x011508b3.

Definition W_b83dc : bv 32 := 0x0006a683.

Definition W_b83e0 : bv 32 := 0x0008a883.

Definition W_b83e4 : bv 32 := 0x0116e463.

Definition W_b83e8 : bv 32 := 0x00060813.

Definition W_b83ec : bv 32 := 0x00080693.

Definition W_b83f0 : bv 32 := 0x00278793.

Definition W_b83f4 : bv 32 := 0xfcb7fae3.

Definition W_b83f8 : bv 32 := 0x00469813.

Definition W_b83fc : bv 32 := 0x00479893.

Definition W_b8400 : bv 32 := 0x01050833.

Definition W_b8404 : bv 32 := 0x011508b3.

Definition W_b8408 : bv 32 := 0x00082803.

Definition W_b840c : bv 32 := 0x0008a883.

Definition W_b8410 : bv 32 := 0x01186463.

Definition W_b8414 : bv 32 := 0x00068793.

Definition W_b8418 : bv 32 := 0x00078693.

Definition W_b841c : bv 32 := 0x02c78c63.

Definition W_b8420 : bv 32 := 0x00469613.

Definition W_b8424 : bv 32 := 0x00c50633.

Definition W_b8428 : bv 32 := 0x00063783.

Definition W_b842c : bv 32 := 0x00e50733.

Definition W_b8430 : bv 32 := 0x00073803.

Definition W_b8434 : bv 32 := 0x00873883.

Definition W_b8438 : bv 32 := 0x00f73023.

Definition W_b843c : bv 32 := 0x00863783.

Definition W_b8440 : bv 32 := 0x00f73423.

Definition W_b8444 : bv 32 := 0x01063023.

Definition W_b8448 : bv 32 := 0x01163423.

Definition W_b844c : bv 32 := 0x00068613.

Definition W_b8450 : bv 32 := 0xf6b6e0e3.

Definition W_b8454 : bv 32 := 0xfff58593.

Definition W_b8458 : bv 32 := 0xf20594e3.

Definition W_b845c : bv 32 := 0x00008067.

