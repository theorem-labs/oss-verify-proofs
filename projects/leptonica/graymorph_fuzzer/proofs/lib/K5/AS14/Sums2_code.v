(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_73b84 : bv 32 := 0x06060663.
Lemma D_73b84 : decode_any W_73b84 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b88 : bv 32 := 0x00000693.
Lemma D_73b88 : decode_any W_73b88 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b8c : bv 32 := 0x00d58733.
Lemma D_73b8c : decode_any W_73b8c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b90 : bv 32 := 0x00074703.
Lemma D_73b90 : decode_any W_73b90 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b94 : bv 32 := 0x00070c63.
Lemma D_73b94 : decode_any W_73b94 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b98 : bv 32 := 0x00d507b3.
Lemma D_73b98 : decode_any W_73b98 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b9c : bv 32 := 0x00168693.
Lemma D_73b9c : decode_any W_73b9c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ba0 : bv 32 := 0x00e78023.
Lemma D_73ba0 : decode_any W_73ba0 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ba4 : bv 32 := 0xfed614e3.
Lemma D_73ba4 : decode_any W_73ba4 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ba8 : bv 32 := 0x00060693.
Lemma D_73ba8 : decode_any W_73ba8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bac : bv 32 := 0x00d505b3.
Lemma D_73bac : decode_any W_73bac = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bb0 : bv 32 := 0x40d6073b.
Lemma D_73bb0 : decode_any W_73bb0 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bb4 : bv 32 := 0x00b76733.
Lemma D_73bb4 : decode_any W_73bb4 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bb8 : bv 32 := 0x00f77713.
Lemma D_73bb8 : decode_any W_73bb8 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bbc : bv 32 := 0x00070e63.
Lemma D_73bbc : decode_any W_73bbc = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bc0 : bv 32 := 0x02d60863.
Lemma D_73bc0 : decode_any W_73bc0 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bc4 : bv 32 := 0x00c50633.
Lemma D_73bc4 : decode_any W_73bc4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bc8 : bv 32 := 0x00058023.
Lemma D_73bc8 : decode_any W_73bc8 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bcc : bv 32 := 0x00158593.
Lemma D_73bcc : decode_any W_73bcc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bd0 : bv 32 := 0xfec59ce3.
Lemma D_73bd0 : decode_any W_73bd0 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bd4 : bv 32 := 0x01c0006f.
Lemma D_73bd4 : decode_any W_73bd4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bd8 : bv 32 := 0x00d60c63.
Lemma D_73bd8 : decode_any W_73bd8 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bdc : bv 32 := 0x00c50633.
Lemma D_73bdc : decode_any W_73bdc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73be0 : bv 32 := 0x0005b023.
Lemma D_73be0 : decode_any W_73be0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73be4 : bv 32 := 0x0005b423.
Lemma D_73be4 : decode_any W_73be4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73be8 : bv 32 := 0x01058593.
Lemma D_73be8 : decode_any W_73be8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bec : bv 32 := 0xfec5eae3.
Lemma D_73bec : decode_any W_73bec = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bf0 : bv 32 := 0x00008067.
Lemma D_73bf0 : decode_any W_73bf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_60134 : bv 32 := 0x00200613.
Lemma D_60134 : decode_any W_60134 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60138 : bv 32 := 0x14c5ea63.
Lemma D_60138 : decode_any W_60138 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6013c : bv 32 := 0x00100613.
Lemma D_6013c : decode_any W_6013c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60140 : bv 32 := 0x00100693.
Lemma D_60140 : decode_any W_60140 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60144 : bv 32 := 0x00c0006f.
Lemma D_60144 : decode_any W_60144 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60148 : bv 32 := 0x00160613.
Lemma D_60148 : decode_any W_60148 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6014c : bv 32 := 0x12b60c63.
Lemma D_6014c : decode_any W_6014c = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60150 : bv 32 := 0x00461713.
Lemma D_60150 : decode_any W_60150 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60154 : bv 32 := 0x00e50733.
Lemma D_60154 : decode_any W_60154 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60158 : bv 32 := 0x00072703.
Lemma D_60158 : decode_any W_60158 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6015c : bv 32 := 0x00060893.
Lemma D_6015c : decode_any W_6015c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60160 : bv 32 := 0xfff88793.
Lemma D_60160 : decode_any W_60160 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60164 : bv 32 := 0x0017d813.
Lemma D_60164 : decode_any W_60164 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60168 : bv 32 := 0x00481293.
Lemma D_60168 : decode_any W_60168 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6016c : bv 32 := 0x005502b3.
Lemma D_6016c : decode_any W_6016c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60170 : bv 32 := 0x0002a303.
Lemma D_60170 : decode_any W_60170 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60174 : bv 32 := 0xfce37ae3.
Lemma D_60174 : decode_any W_60174 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60178 : bv 32 := 0x0002b303.
Lemma D_60178 : decode_any W_60178 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6017c : bv 32 := 0x00489893.
Lemma D_6017c : decode_any W_6017c = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60180 : bv 32 := 0x011508b3.
Lemma D_60180 : decode_any W_60180 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60184 : bv 32 := 0x0048a383.
Lemma D_60184 : decode_any W_60184 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60188 : bv 32 := 0x0068b023.
Lemma D_60188 : decode_any W_60188 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6018c : bv 32 := 0x0082b303.
Lemma D_6018c : decode_any W_6018c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60190 : bv 32 := 0x0088be03.
Lemma D_60190 : decode_any W_60190 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60194 : bv 32 := 0x0068b423.
Lemma D_60194 : decode_any W_60194 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60198 : bv 32 := 0x00e2a023.
Lemma D_60198 : decode_any W_60198 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6019c : bv 32 := 0x0072a223.
Lemma D_6019c : decode_any W_6019c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601a0 : bv 32 := 0x01c2b423.
Lemma D_601a0 : decode_any W_601a0 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601a4 : bv 32 := 0x00080893.
Lemma D_601a4 : decode_any W_601a4 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601a8 : bv 32 := 0xfaf6ece3.
Lemma D_601a8 : decode_any W_601a8 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601ac : bv 32 := 0xf9dff06f.
Lemma D_601ac : decode_any W_601ac = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601b0 : bv 32 := 0x00000613.
Lemma D_601b0 : decode_any W_601b0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601b4 : bv 32 := 0x00459693.
Lemma D_601b4 : decode_any W_601b4 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601b8 : bv 32 := 0x00d506b3.
Lemma D_601b8 : decode_any W_601b8 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601bc : bv 32 := 0x0006b703.
Lemma D_601bc : decode_any W_601bc = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601c0 : bv 32 := 0x0086b783.
Lemma D_601c0 : decode_any W_601c0 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601c4 : bv 32 := 0x00053803.
Lemma D_601c4 : decode_any W_601c4 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601c8 : bv 32 := 0x00853883.
Lemma D_601c8 : decode_any W_601c8 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601cc : bv 32 := 0x00e53023.
Lemma D_601cc : decode_any W_601cc = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601d0 : bv 32 := 0x00f53423.
Lemma D_601d0 : decode_any W_601d0 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601d4 : bv 32 := 0x0106b023.
Lemma D_601d4 : decode_any W_601d4 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601d8 : bv 32 := 0x0116b423.
Lemma D_601d8 : decode_any W_601d8 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601dc : bv 32 := 0x00000693.
Lemma D_601dc : decode_any W_601dc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601e0 : bv 32 := 0x00161793.
Lemma D_601e0 : decode_any W_601e0 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601e4 : bv 32 := 0x00178813.
Lemma D_601e4 : decode_any W_601e4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601e8 : bv 32 := 0x00461713.
Lemma D_601e8 : decode_any W_601e8 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601ec : bv 32 := 0x00b86a63.
Lemma D_601ec : decode_any W_601ec = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601f0 : bv 32 := 0x00278793.
Lemma D_601f0 : decode_any W_601f0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601f4 : bv 32 := 0x02b7ea63.
Lemma D_601f4 : decode_any W_601f4 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601f8 : bv 32 := 0x04c69c63.
Lemma D_601f8 : decode_any W_601f8 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_601fc : bv 32 := 0x0880006f.
Lemma D_601fc : decode_any W_601fc = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60200 : bv 32 := 0x00e506b3.
Lemma D_60200 : decode_any W_60200 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60204 : bv 32 := 0x00481893.
Lemma D_60204 : decode_any W_60204 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60208 : bv 32 := 0x011508b3.
Lemma D_60208 : decode_any W_60208 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6020c : bv 32 := 0x0006a683.
Lemma D_6020c : decode_any W_6020c = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60210 : bv 32 := 0x0008a883.
Lemma D_60210 : decode_any W_60210 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60214 : bv 32 := 0x0116e463.
Lemma D_60214 : decode_any W_60214 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60218 : bv 32 := 0x00060813.
Lemma D_60218 : decode_any W_60218 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6021c : bv 32 := 0x00080693.
Lemma D_6021c : decode_any W_6021c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60220 : bv 32 := 0x00278793.
Lemma D_60220 : decode_any W_60220 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60224 : bv 32 := 0xfcb7fae3.
Lemma D_60224 : decode_any W_60224 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60228 : bv 32 := 0x00469813.
Lemma D_60228 : decode_any W_60228 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6022c : bv 32 := 0x00479893.
Lemma D_6022c : decode_any W_6022c = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60230 : bv 32 := 0x01050833.
Lemma D_60230 : decode_any W_60230 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60234 : bv 32 := 0x011508b3.
Lemma D_60234 : decode_any W_60234 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60238 : bv 32 := 0x00082803.
Lemma D_60238 : decode_any W_60238 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6023c : bv 32 := 0x0008a883.
Lemma D_6023c : decode_any W_6023c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60240 : bv 32 := 0x01186463.
Lemma D_60240 : decode_any W_60240 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60244 : bv 32 := 0x00068793.
Lemma D_60244 : decode_any W_60244 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60248 : bv 32 := 0x00078693.
Lemma D_60248 : decode_any W_60248 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6024c : bv 32 := 0x02c78c63.
Lemma D_6024c : decode_any W_6024c = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60250 : bv 32 := 0x00469613.
Lemma D_60250 : decode_any W_60250 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60254 : bv 32 := 0x00c50633.
Lemma D_60254 : decode_any W_60254 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60258 : bv 32 := 0x00063783.
Lemma D_60258 : decode_any W_60258 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6025c : bv 32 := 0x00e50733.
Lemma D_6025c : decode_any W_6025c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60260 : bv 32 := 0x00073803.
Lemma D_60260 : decode_any W_60260 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60264 : bv 32 := 0x00873883.
Lemma D_60264 : decode_any W_60264 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60268 : bv 32 := 0x00f73023.
Lemma D_60268 : decode_any W_60268 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6026c : bv 32 := 0x00863783.
Lemma D_6026c : decode_any W_6026c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60270 : bv 32 := 0x00f73423.
Lemma D_60270 : decode_any W_60270 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60274 : bv 32 := 0x01063023.
Lemma D_60274 : decode_any W_60274 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60278 : bv 32 := 0x01163423.
Lemma D_60278 : decode_any W_60278 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6027c : bv 32 := 0x00068613.
Lemma D_6027c : decode_any W_6027c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60280 : bv 32 := 0xf6b6e0e3.
Lemma D_60280 : decode_any W_60280 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60284 : bv 32 := 0xfff58593.
Lemma D_60284 : decode_any W_60284 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60288 : bv 32 := 0xf20594e3.
Lemma D_60288 : decode_any W_60288 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6028c : bv 32 := 0x00008067.
Lemma D_6028c : decode_any W_6028c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
