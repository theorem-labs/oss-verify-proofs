(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_854d0 : bv 32 := 0x06060663.
Lemma D_854d0 : decode_any W_854d0 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854d4 : bv 32 := 0x00000693.
Lemma D_854d4 : decode_any W_854d4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854d8 : bv 32 := 0x00d58733.
Lemma D_854d8 : decode_any W_854d8 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854dc : bv 32 := 0x00074703.
Lemma D_854dc : decode_any W_854dc = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854e0 : bv 32 := 0x00070c63.
Lemma D_854e0 : decode_any W_854e0 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854e4 : bv 32 := 0x00d507b3.
Lemma D_854e4 : decode_any W_854e4 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854e8 : bv 32 := 0x00168693.
Lemma D_854e8 : decode_any W_854e8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854ec : bv 32 := 0x00e78023.
Lemma D_854ec : decode_any W_854ec = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854f0 : bv 32 := 0xfed614e3.
Lemma D_854f0 : decode_any W_854f0 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854f4 : bv 32 := 0x00060693.
Lemma D_854f4 : decode_any W_854f4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854f8 : bv 32 := 0x00d505b3.
Lemma D_854f8 : decode_any W_854f8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_854fc : bv 32 := 0x40d6073b.
Lemma D_854fc : decode_any W_854fc = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85500 : bv 32 := 0x00b76733.
Lemma D_85500 : decode_any W_85500 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85504 : bv 32 := 0x00f77713.
Lemma D_85504 : decode_any W_85504 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85508 : bv 32 := 0x00070e63.
Lemma D_85508 : decode_any W_85508 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8550c : bv 32 := 0x02d60863.
Lemma D_8550c : decode_any W_8550c = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85510 : bv 32 := 0x00c50633.
Lemma D_85510 : decode_any W_85510 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85514 : bv 32 := 0x00058023.
Lemma D_85514 : decode_any W_85514 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85518 : bv 32 := 0x00158593.
Lemma D_85518 : decode_any W_85518 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8551c : bv 32 := 0xfec59ce3.
Lemma D_8551c : decode_any W_8551c = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85520 : bv 32 := 0x01c0006f.
Lemma D_85520 : decode_any W_85520 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85524 : bv 32 := 0x00d60c63.
Lemma D_85524 : decode_any W_85524 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85528 : bv 32 := 0x00c50633.
Lemma D_85528 : decode_any W_85528 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8552c : bv 32 := 0x0005b023.
Lemma D_8552c : decode_any W_8552c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85530 : bv 32 := 0x0005b423.
Lemma D_85530 : decode_any W_85530 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85534 : bv 32 := 0x01058593.
Lemma D_85534 : decode_any W_85534 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85538 : bv 32 := 0xfec5eae3.
Lemma D_85538 : decode_any W_85538 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8553c : bv 32 := 0x00008067.
Lemma D_8553c : decode_any W_8553c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71018 : bv 32 := 0x00200613.
Lemma D_71018 : decode_any W_71018 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7101c : bv 32 := 0x14c5ea63.
Lemma D_7101c : decode_any W_7101c = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71020 : bv 32 := 0x00100613.
Lemma D_71020 : decode_any W_71020 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71024 : bv 32 := 0x00100693.
Lemma D_71024 : decode_any W_71024 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71028 : bv 32 := 0x00c0006f.
Lemma D_71028 : decode_any W_71028 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7102c : bv 32 := 0x00160613.
Lemma D_7102c : decode_any W_7102c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71030 : bv 32 := 0x12b60c63.
Lemma D_71030 : decode_any W_71030 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71034 : bv 32 := 0x00461713.
Lemma D_71034 : decode_any W_71034 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71038 : bv 32 := 0x00e50733.
Lemma D_71038 : decode_any W_71038 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7103c : bv 32 := 0x00072703.
Lemma D_7103c : decode_any W_7103c = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71040 : bv 32 := 0x00060893.
Lemma D_71040 : decode_any W_71040 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71044 : bv 32 := 0xfff88793.
Lemma D_71044 : decode_any W_71044 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71048 : bv 32 := 0x0017d813.
Lemma D_71048 : decode_any W_71048 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7104c : bv 32 := 0x00481293.
Lemma D_7104c : decode_any W_7104c = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71050 : bv 32 := 0x005502b3.
Lemma D_71050 : decode_any W_71050 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71054 : bv 32 := 0x0002a303.
Lemma D_71054 : decode_any W_71054 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71058 : bv 32 := 0xfce37ae3.
Lemma D_71058 : decode_any W_71058 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7105c : bv 32 := 0x0002b303.
Lemma D_7105c : decode_any W_7105c = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71060 : bv 32 := 0x00489893.
Lemma D_71060 : decode_any W_71060 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71064 : bv 32 := 0x011508b3.
Lemma D_71064 : decode_any W_71064 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71068 : bv 32 := 0x0048a383.
Lemma D_71068 : decode_any W_71068 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7106c : bv 32 := 0x0068b023.
Lemma D_7106c : decode_any W_7106c = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71070 : bv 32 := 0x0082b303.
Lemma D_71070 : decode_any W_71070 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71074 : bv 32 := 0x0088be03.
Lemma D_71074 : decode_any W_71074 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71078 : bv 32 := 0x0068b423.
Lemma D_71078 : decode_any W_71078 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7107c : bv 32 := 0x00e2a023.
Lemma D_7107c : decode_any W_7107c = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71080 : bv 32 := 0x0072a223.
Lemma D_71080 : decode_any W_71080 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71084 : bv 32 := 0x01c2b423.
Lemma D_71084 : decode_any W_71084 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71088 : bv 32 := 0x00080893.
Lemma D_71088 : decode_any W_71088 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7108c : bv 32 := 0xfaf6ece3.
Lemma D_7108c : decode_any W_7108c = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71090 : bv 32 := 0xf9dff06f.
Lemma D_71090 : decode_any W_71090 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71094 : bv 32 := 0x00000613.
Lemma D_71094 : decode_any W_71094 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71098 : bv 32 := 0x00459693.
Lemma D_71098 : decode_any W_71098 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7109c : bv 32 := 0x00d506b3.
Lemma D_7109c : decode_any W_7109c = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710a0 : bv 32 := 0x0006b703.
Lemma D_710a0 : decode_any W_710a0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710a4 : bv 32 := 0x0086b783.
Lemma D_710a4 : decode_any W_710a4 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710a8 : bv 32 := 0x00053803.
Lemma D_710a8 : decode_any W_710a8 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710ac : bv 32 := 0x00853883.
Lemma D_710ac : decode_any W_710ac = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710b0 : bv 32 := 0x00e53023.
Lemma D_710b0 : decode_any W_710b0 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710b4 : bv 32 := 0x00f53423.
Lemma D_710b4 : decode_any W_710b4 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710b8 : bv 32 := 0x0106b023.
Lemma D_710b8 : decode_any W_710b8 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710bc : bv 32 := 0x0116b423.
Lemma D_710bc : decode_any W_710bc = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710c0 : bv 32 := 0x00000693.
Lemma D_710c0 : decode_any W_710c0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710c4 : bv 32 := 0x00161793.
Lemma D_710c4 : decode_any W_710c4 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710c8 : bv 32 := 0x00178813.
Lemma D_710c8 : decode_any W_710c8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710cc : bv 32 := 0x00461713.
Lemma D_710cc : decode_any W_710cc = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710d0 : bv 32 := 0x00b86a63.
Lemma D_710d0 : decode_any W_710d0 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710d4 : bv 32 := 0x00278793.
Lemma D_710d4 : decode_any W_710d4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710d8 : bv 32 := 0x02b7ea63.
Lemma D_710d8 : decode_any W_710d8 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710dc : bv 32 := 0x04c69c63.
Lemma D_710dc : decode_any W_710dc = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710e0 : bv 32 := 0x0880006f.
Lemma D_710e0 : decode_any W_710e0 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710e4 : bv 32 := 0x00e506b3.
Lemma D_710e4 : decode_any W_710e4 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710e8 : bv 32 := 0x00481893.
Lemma D_710e8 : decode_any W_710e8 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710ec : bv 32 := 0x011508b3.
Lemma D_710ec : decode_any W_710ec = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710f0 : bv 32 := 0x0006a683.
Lemma D_710f0 : decode_any W_710f0 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710f4 : bv 32 := 0x0008a883.
Lemma D_710f4 : decode_any W_710f4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710f8 : bv 32 := 0x0116e463.
Lemma D_710f8 : decode_any W_710f8 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_710fc : bv 32 := 0x00060813.
Lemma D_710fc : decode_any W_710fc = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71100 : bv 32 := 0x00080693.
Lemma D_71100 : decode_any W_71100 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71104 : bv 32 := 0x00278793.
Lemma D_71104 : decode_any W_71104 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71108 : bv 32 := 0xfcb7fae3.
Lemma D_71108 : decode_any W_71108 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7110c : bv 32 := 0x00469813.
Lemma D_7110c : decode_any W_7110c = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71110 : bv 32 := 0x00479893.
Lemma D_71110 : decode_any W_71110 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71114 : bv 32 := 0x01050833.
Lemma D_71114 : decode_any W_71114 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71118 : bv 32 := 0x011508b3.
Lemma D_71118 : decode_any W_71118 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7111c : bv 32 := 0x00082803.
Lemma D_7111c : decode_any W_7111c = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71120 : bv 32 := 0x0008a883.
Lemma D_71120 : decode_any W_71120 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71124 : bv 32 := 0x01186463.
Lemma D_71124 : decode_any W_71124 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71128 : bv 32 := 0x00068793.
Lemma D_71128 : decode_any W_71128 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7112c : bv 32 := 0x00078693.
Lemma D_7112c : decode_any W_7112c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71130 : bv 32 := 0x02c78c63.
Lemma D_71130 : decode_any W_71130 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71134 : bv 32 := 0x00469613.
Lemma D_71134 : decode_any W_71134 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71138 : bv 32 := 0x00c50633.
Lemma D_71138 : decode_any W_71138 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7113c : bv 32 := 0x00063783.
Lemma D_7113c : decode_any W_7113c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71140 : bv 32 := 0x00e50733.
Lemma D_71140 : decode_any W_71140 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71144 : bv 32 := 0x00073803.
Lemma D_71144 : decode_any W_71144 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71148 : bv 32 := 0x00873883.
Lemma D_71148 : decode_any W_71148 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7114c : bv 32 := 0x00f73023.
Lemma D_7114c : decode_any W_7114c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71150 : bv 32 := 0x00863783.
Lemma D_71150 : decode_any W_71150 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71154 : bv 32 := 0x00f73423.
Lemma D_71154 : decode_any W_71154 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71158 : bv 32 := 0x01063023.
Lemma D_71158 : decode_any W_71158 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7115c : bv 32 := 0x01163423.
Lemma D_7115c : decode_any W_7115c = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71160 : bv 32 := 0x00068613.
Lemma D_71160 : decode_any W_71160 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71164 : bv 32 := 0xf6b6e0e3.
Lemma D_71164 : decode_any W_71164 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71168 : bv 32 := 0xfff58593.
Lemma D_71168 : decode_any W_71168 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7116c : bv 32 := 0xf20594e3.
Lemma D_7116c : decode_any W_7116c = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_71170 : bv 32 := 0x00008067.
Lemma D_71170 : decode_any W_71170 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
