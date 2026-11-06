(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_103d3c : bv 32 := 0x06060663.
Lemma D_103d3c : decode_any W_103d3c = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d40 : bv 32 := 0x00000693.
Lemma D_103d40 : decode_any W_103d40 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d44 : bv 32 := 0x00d58733.
Lemma D_103d44 : decode_any W_103d44 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d48 : bv 32 := 0x00074703.
Lemma D_103d48 : decode_any W_103d48 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d4c : bv 32 := 0x00070c63.
Lemma D_103d4c : decode_any W_103d4c = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d50 : bv 32 := 0x00d507b3.
Lemma D_103d50 : decode_any W_103d50 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d54 : bv 32 := 0x00168693.
Lemma D_103d54 : decode_any W_103d54 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d58 : bv 32 := 0x00e78023.
Lemma D_103d58 : decode_any W_103d58 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d5c : bv 32 := 0xfed614e3.
Lemma D_103d5c : decode_any W_103d5c = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d60 : bv 32 := 0x00060693.
Lemma D_103d60 : decode_any W_103d60 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d64 : bv 32 := 0x00d505b3.
Lemma D_103d64 : decode_any W_103d64 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d68 : bv 32 := 0x40d6073b.
Lemma D_103d68 : decode_any W_103d68 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d6c : bv 32 := 0x00b76733.
Lemma D_103d6c : decode_any W_103d6c = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d70 : bv 32 := 0x00f77713.
Lemma D_103d70 : decode_any W_103d70 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d74 : bv 32 := 0x00070e63.
Lemma D_103d74 : decode_any W_103d74 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d78 : bv 32 := 0x02d60863.
Lemma D_103d78 : decode_any W_103d78 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d7c : bv 32 := 0x00c50633.
Lemma D_103d7c : decode_any W_103d7c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d80 : bv 32 := 0x00058023.
Lemma D_103d80 : decode_any W_103d80 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d84 : bv 32 := 0x00158593.
Lemma D_103d84 : decode_any W_103d84 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d88 : bv 32 := 0xfec59ce3.
Lemma D_103d88 : decode_any W_103d88 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d8c : bv 32 := 0x01c0006f.
Lemma D_103d8c : decode_any W_103d8c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d90 : bv 32 := 0x00d60c63.
Lemma D_103d90 : decode_any W_103d90 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d94 : bv 32 := 0x00c50633.
Lemma D_103d94 : decode_any W_103d94 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d98 : bv 32 := 0x0005b023.
Lemma D_103d98 : decode_any W_103d98 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_103d9c : bv 32 := 0x0005b423.
Lemma D_103d9c : decode_any W_103d9c = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_103da0 : bv 32 := 0x01058593.
Lemma D_103da0 : decode_any W_103da0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_103da4 : bv 32 := 0xfec5eae3.
Lemma D_103da4 : decode_any W_103da4 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.
Definition W_103da8 : bv 32 := 0x00008067.
Lemma D_103da8 : decode_any W_103da8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa68 : bv 32 := 0x00200613.
Lemma D_eaa68 : decode_any W_eaa68 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa6c : bv 32 := 0x14c5ea63.
Lemma D_eaa6c : decode_any W_eaa6c = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa70 : bv 32 := 0x00100613.
Lemma D_eaa70 : decode_any W_eaa70 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa74 : bv 32 := 0x00100693.
Lemma D_eaa74 : decode_any W_eaa74 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa78 : bv 32 := 0x00c0006f.
Lemma D_eaa78 : decode_any W_eaa78 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa7c : bv 32 := 0x00160613.
Lemma D_eaa7c : decode_any W_eaa7c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa80 : bv 32 := 0x12b60c63.
Lemma D_eaa80 : decode_any W_eaa80 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa84 : bv 32 := 0x00461713.
Lemma D_eaa84 : decode_any W_eaa84 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa88 : bv 32 := 0x00e50733.
Lemma D_eaa88 : decode_any W_eaa88 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa8c : bv 32 := 0x00072703.
Lemma D_eaa8c : decode_any W_eaa8c = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa90 : bv 32 := 0x00060893.
Lemma D_eaa90 : decode_any W_eaa90 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa94 : bv 32 := 0xfff88793.
Lemma D_eaa94 : decode_any W_eaa94 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa98 : bv 32 := 0x0017d813.
Lemma D_eaa98 : decode_any W_eaa98 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaa9c : bv 32 := 0x00481293.
Lemma D_eaa9c : decode_any W_eaa9c = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaaa0 : bv 32 := 0x005502b3.
Lemma D_eaaa0 : decode_any W_eaaa0 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaaa4 : bv 32 := 0x0002a303.
Lemma D_eaaa4 : decode_any W_eaaa4 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaaa8 : bv 32 := 0xfce37ae3.
Lemma D_eaaa8 : decode_any W_eaaa8 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaaac : bv 32 := 0x0002b303.
Lemma D_eaaac : decode_any W_eaaac = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaab0 : bv 32 := 0x00489893.
Lemma D_eaab0 : decode_any W_eaab0 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaab4 : bv 32 := 0x011508b3.
Lemma D_eaab4 : decode_any W_eaab4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaab8 : bv 32 := 0x0048a383.
Lemma D_eaab8 : decode_any W_eaab8 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaabc : bv 32 := 0x0068b023.
Lemma D_eaabc : decode_any W_eaabc = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaac0 : bv 32 := 0x0082b303.
Lemma D_eaac0 : decode_any W_eaac0 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaac4 : bv 32 := 0x0088be03.
Lemma D_eaac4 : decode_any W_eaac4 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaac8 : bv 32 := 0x0068b423.
Lemma D_eaac8 : decode_any W_eaac8 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaacc : bv 32 := 0x00e2a023.
Lemma D_eaacc : decode_any W_eaacc = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaad0 : bv 32 := 0x0072a223.
Lemma D_eaad0 : decode_any W_eaad0 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaad4 : bv 32 := 0x01c2b423.
Lemma D_eaad4 : decode_any W_eaad4 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaad8 : bv 32 := 0x00080893.
Lemma D_eaad8 : decode_any W_eaad8 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaadc : bv 32 := 0xfaf6ece3.
Lemma D_eaadc : decode_any W_eaadc = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaae0 : bv 32 := 0xf9dff06f.
Lemma D_eaae0 : decode_any W_eaae0 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaae4 : bv 32 := 0x00000613.
Lemma D_eaae4 : decode_any W_eaae4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaae8 : bv 32 := 0x00459693.
Lemma D_eaae8 : decode_any W_eaae8 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaaec : bv 32 := 0x00d506b3.
Lemma D_eaaec : decode_any W_eaaec = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaaf0 : bv 32 := 0x0006b703.
Lemma D_eaaf0 : decode_any W_eaaf0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaaf4 : bv 32 := 0x0086b783.
Lemma D_eaaf4 : decode_any W_eaaf4 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaaf8 : bv 32 := 0x00053803.
Lemma D_eaaf8 : decode_any W_eaaf8 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaafc : bv 32 := 0x00853883.
Lemma D_eaafc : decode_any W_eaafc = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab00 : bv 32 := 0x00e53023.
Lemma D_eab00 : decode_any W_eab00 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab04 : bv 32 := 0x00f53423.
Lemma D_eab04 : decode_any W_eab04 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab08 : bv 32 := 0x0106b023.
Lemma D_eab08 : decode_any W_eab08 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab0c : bv 32 := 0x0116b423.
Lemma D_eab0c : decode_any W_eab0c = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab10 : bv 32 := 0x00000693.
Lemma D_eab10 : decode_any W_eab10 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab14 : bv 32 := 0x00161793.
Lemma D_eab14 : decode_any W_eab14 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab18 : bv 32 := 0x00178813.
Lemma D_eab18 : decode_any W_eab18 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab1c : bv 32 := 0x00461713.
Lemma D_eab1c : decode_any W_eab1c = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab20 : bv 32 := 0x00b86a63.
Lemma D_eab20 : decode_any W_eab20 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab24 : bv 32 := 0x00278793.
Lemma D_eab24 : decode_any W_eab24 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab28 : bv 32 := 0x02b7ea63.
Lemma D_eab28 : decode_any W_eab28 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab2c : bv 32 := 0x04c69c63.
Lemma D_eab2c : decode_any W_eab2c = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab30 : bv 32 := 0x0880006f.
Lemma D_eab30 : decode_any W_eab30 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab34 : bv 32 := 0x00e506b3.
Lemma D_eab34 : decode_any W_eab34 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab38 : bv 32 := 0x00481893.
Lemma D_eab38 : decode_any W_eab38 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab3c : bv 32 := 0x011508b3.
Lemma D_eab3c : decode_any W_eab3c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab40 : bv 32 := 0x0006a683.
Lemma D_eab40 : decode_any W_eab40 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab44 : bv 32 := 0x0008a883.
Lemma D_eab44 : decode_any W_eab44 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab48 : bv 32 := 0x0116e463.
Lemma D_eab48 : decode_any W_eab48 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab4c : bv 32 := 0x00060813.
Lemma D_eab4c : decode_any W_eab4c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab50 : bv 32 := 0x00080693.
Lemma D_eab50 : decode_any W_eab50 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab54 : bv 32 := 0x00278793.
Lemma D_eab54 : decode_any W_eab54 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab58 : bv 32 := 0xfcb7fae3.
Lemma D_eab58 : decode_any W_eab58 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab5c : bv 32 := 0x00469813.
Lemma D_eab5c : decode_any W_eab5c = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab60 : bv 32 := 0x00479893.
Lemma D_eab60 : decode_any W_eab60 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab64 : bv 32 := 0x01050833.
Lemma D_eab64 : decode_any W_eab64 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab68 : bv 32 := 0x011508b3.
Lemma D_eab68 : decode_any W_eab68 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab6c : bv 32 := 0x00082803.
Lemma D_eab6c : decode_any W_eab6c = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab70 : bv 32 := 0x0008a883.
Lemma D_eab70 : decode_any W_eab70 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab74 : bv 32 := 0x01186463.
Lemma D_eab74 : decode_any W_eab74 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab78 : bv 32 := 0x00068793.
Lemma D_eab78 : decode_any W_eab78 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab7c : bv 32 := 0x00078693.
Lemma D_eab7c : decode_any W_eab7c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab80 : bv 32 := 0x02c78c63.
Lemma D_eab80 : decode_any W_eab80 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab84 : bv 32 := 0x00469613.
Lemma D_eab84 : decode_any W_eab84 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab88 : bv 32 := 0x00c50633.
Lemma D_eab88 : decode_any W_eab88 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab8c : bv 32 := 0x00063783.
Lemma D_eab8c : decode_any W_eab8c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab90 : bv 32 := 0x00e50733.
Lemma D_eab90 : decode_any W_eab90 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab94 : bv 32 := 0x00073803.
Lemma D_eab94 : decode_any W_eab94 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab98 : bv 32 := 0x00873883.
Lemma D_eab98 : decode_any W_eab98 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eab9c : bv 32 := 0x00f73023.
Lemma D_eab9c : decode_any W_eab9c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaba0 : bv 32 := 0x00863783.
Lemma D_eaba0 : decode_any W_eaba0 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaba4 : bv 32 := 0x00f73423.
Lemma D_eaba4 : decode_any W_eaba4 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eaba8 : bv 32 := 0x01063023.
Lemma D_eaba8 : decode_any W_eaba8 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eabac : bv 32 := 0x01163423.
Lemma D_eabac : decode_any W_eabac = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_eabb0 : bv 32 := 0x00068613.
Lemma D_eabb0 : decode_any W_eabb0 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_eabb4 : bv 32 := 0xf6b6e0e3.
Lemma D_eabb4 : decode_any W_eabb4 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.
Definition W_eabb8 : bv 32 := 0xfff58593.
Lemma D_eabb8 : decode_any W_eabb8 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_eabbc : bv 32 := 0xf20594e3.
Lemma D_eabbc : decode_any W_eabbc = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.
Definition W_eabc0 : bv 32 := 0x00008067.
Lemma D_eabc0 : decode_any W_eabc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
