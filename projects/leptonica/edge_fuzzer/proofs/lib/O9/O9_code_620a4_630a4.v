(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushS9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_620f8 : bv 32 := 0xff010113.
Lemma F_620f8 : fetch_word Plain.M.loaded_segments (0x62150 : word) = Some W_620f8.
Proof. vm_refl. Qed.
Lemma D_620f8 : decode_any W_620f8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_620fc : bv 32 := 0x00113423.
Lemma F_620fc : fetch_word Plain.M.loaded_segments (0x62154 : word) = Some W_620fc.
Proof. vm_refl. Qed.
Lemma D_620fc : decode_any W_620fc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62100 : bv 32 := 0x00813023.
Lemma F_62100 : fetch_word Plain.M.loaded_segments (0x62158 : word) = Some W_62100.
Proof. vm_refl. Qed.
Lemma D_62100 : decode_any W_62100 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62104 : bv 32 := 0x080000ef.
Lemma F_62104 : fetch_word Plain.M.loaded_segments (0x6215c : word) = Some W_62104.
Proof. vm_refl. Qed.
Lemma D_62104 : decode_any W_62104 = Some (Jal 1 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62108 : bv 32 := 0x02050863.
Lemma F_62108 : fetch_word Plain.M.loaded_segments (0x62160 : word) = Some W_62108.
Proof. vm_refl. Qed.
Lemma D_62108 : decode_any W_62108 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6210c : bv 32 := 0x00456603.
Lemma F_6210c : fetch_word Plain.M.loaded_segments (0x62164 : word) = Some W_6210c.
Proof. vm_refl. Qed.
Lemma D_6210c : decode_any W_6210c = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62110 : bv 32 := 0x01056683.
Lemma F_62110 : fetch_word Plain.M.loaded_segments (0x62168 : word) = Some W_62110.
Proof. vm_refl. Qed.
Lemma D_62110 : decode_any W_62110 = Some (Load SZ4 false 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62114 : bv 32 := 0x03853583.
Lemma F_62114 : fetch_word Plain.M.loaded_segments (0x6216c : word) = Some W_62114.
Proof. vm_refl. Qed.
Lemma D_62114 : decode_any W_62114 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62118 : bv 32 := 0x02c68633.
Lemma F_62118 : fetch_word Plain.M.loaded_segments (0x62170 : word) = Some W_62118.
Proof. vm_refl. Qed.
Lemma D_62118 : decode_any W_62118 = Some (Mul M_MUL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6211c : bv 32 := 0x00261613.
Lemma F_6211c : fetch_word Plain.M.loaded_segments (0x62174 : word) = Some W_6211c.
Proof. vm_refl. Qed.
Lemma D_6211c : decode_any W_6211c = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62120 : bv 32 := 0x00050413.
Lemma F_62120 : fetch_word Plain.M.loaded_segments (0x62178 : word) = Some W_62120.
Proof. vm_refl. Qed.
Lemma D_62120 : decode_any W_62120 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62124 : bv 32 := 0x00058513.
Lemma F_62124 : fetch_word Plain.M.loaded_segments (0x6217c : word) = Some W_62124.
Proof. vm_refl. Qed.
Lemma D_62124 : decode_any W_62124 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62128 : bv 32 := 0x00000593.
Lemma F_62128 : fetch_word Plain.M.loaded_segments (0x62180 : word) = Some W_62128.
Proof. vm_refl. Qed.
Lemma D_62128 : decode_any W_62128 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6212c : bv 32 := 0x2d0840ef.
Lemma F_6212c : fetch_word Plain.M.loaded_segments (0x62184 : word) = Some W_6212c.
Proof. vm_refl. Qed.
Lemma D_6212c : decode_any W_6212c = Some (Jal 1 541392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62130 : bv 32 := 0x00040513.
Lemma F_62130 : fetch_word Plain.M.loaded_segments (0x62188 : word) = Some W_62130.
Proof. vm_refl. Qed.
Lemma D_62130 : decode_any W_62130 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62134 : bv 32 := 0x0400006f.
Lemma F_62134 : fetch_word Plain.M.loaded_segments (0x6218c : word) = Some W_62134.
Proof. vm_refl. Qed.
Lemma D_62134 : decode_any W_62134 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62138 : bv 32 := 0x0008c517.
Lemma F_62138 : fetch_word Plain.M.loaded_segments (0x62190 : word) = Some W_62138.
Proof. vm_refl. Qed.
Lemma D_62138 : decode_any W_62138 = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6213c : bv 32 := 0x3e053503.
Lemma F_6213c : fetch_word Plain.M.loaded_segments (0x62194 : word) = Some W_6213c.
Proof. vm_refl. Qed.
Lemma D_6213c : decode_any W_6213c = Some (Load SZ8 true 10 10 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62140 : bv 32 := 0x00052503.
Lemma F_62140 : fetch_word Plain.M.loaded_segments (0x62198 : word) = Some W_62140.
Proof. vm_refl. Qed.
Lemma D_62140 : decode_any W_62140 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62144 : bv 32 := 0x00500593.
Lemma F_62144 : fetch_word Plain.M.loaded_segments (0x6219c : word) = Some W_62144.
Proof. vm_refl. Qed.
Lemma D_62144 : decode_any W_62144 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62148 : bv 32 := 0x02a5c463.
Lemma F_62148 : fetch_word Plain.M.loaded_segments (0x621a0 : word) = Some W_62148.
Proof. vm_refl. Qed.
Lemma D_62148 : decode_any W_62148 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6214c : bv 32 := 0xfffb0517.
Lemma F_6214c : fetch_word Plain.M.loaded_segments (0x621a4 : word) = Some W_6214c.
Proof. vm_refl. Qed.
Lemma D_6214c : decode_any W_6214c = Some (Auipc 10 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62150 : bv 32 := 0xfffb2597.
Lemma F_62150 : fetch_word Plain.M.loaded_segments (0x621a8 : word) = Some W_62150.
Proof. vm_refl. Qed.
Lemma D_62150 : decode_any W_62150 = Some (Auipc 11 1048498, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62154 : bv 32 := 0xebe50513.
Lemma F_62154 : fetch_word Plain.M.loaded_segments (0x621ac : word) = Some W_62154.
Proof. vm_refl. Qed.
Lemma D_62154 : decode_any W_62154 = Some (OpImm ALU_ADD 10 10 3774, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62158 : bv 32 := 0x38558593.
Lemma F_62158 : fetch_word Plain.M.loaded_segments (0x621b0 : word) = Some W_62158.
Proof. vm_refl. Qed.
Lemma D_62158 : decode_any W_62158 = Some (OpImm ALU_ADD 11 11 901, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6215c : bv 32 := 0x00000613.
Lemma F_6215c : fetch_word Plain.M.loaded_segments (0x621b4 : word) = Some W_6215c.
Proof. vm_refl. Qed.
Lemma D_6215c : decode_any W_6215c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62160 : bv 32 := 0x00813083.
Lemma F_62160 : fetch_word Plain.M.loaded_segments (0x621b8 : word) = Some W_62160.
Proof. vm_refl. Qed.
Lemma D_62160 : decode_any W_62160 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62164 : bv 32 := 0x00013403.
Lemma F_62164 : fetch_word Plain.M.loaded_segments (0x621bc : word) = Some W_62164.
Proof. vm_refl. Qed.
Lemma D_62164 : decode_any W_62164 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62168 : bv 32 := 0x01010113.
Lemma F_62168 : fetch_word Plain.M.loaded_segments (0x621c0 : word) = Some W_62168.
Proof. vm_refl. Qed.
Lemma D_62168 : decode_any W_62168 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6216c : bv 32 := 0xce1fa06f.
Lemma F_6216c : fetch_word Plain.M.loaded_segments (0x621c4 : word) = Some W_6216c.
Proof. vm_refl. Qed.
Lemma D_6216c : decode_any W_6216c = Some (Jal 0 2075872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62174 : bv 32 := 0x00813083.
Lemma F_62174 : fetch_word Plain.M.loaded_segments (0x621cc : word) = Some W_62174.
Proof. vm_refl. Qed.
Lemma D_62174 : decode_any W_62174 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62178 : bv 32 := 0x00013403.
Lemma F_62178 : fetch_word Plain.M.loaded_segments (0x621d0 : word) = Some W_62178.
Proof. vm_refl. Qed.
Lemma D_62178 : decode_any W_62178 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6217c : bv 32 := 0x01010113.
Lemma F_6217c : fetch_word Plain.M.loaded_segments (0x621d4 : word) = Some W_6217c.
Proof. vm_refl. Qed.
Lemma D_6217c : decode_any W_6217c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62180 : bv 32 := 0x00008067.
Lemma F_62180 : fetch_word Plain.M.loaded_segments (0x621d8 : word) = Some W_62180.
Proof. vm_refl. Qed.
Lemma D_62180 : decode_any W_62180 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62184 : bv 32 := 0xfd010113.
Lemma F_62184 : fetch_word Plain.M.loaded_segments (0x621dc : word) = Some W_62184.
Proof. vm_refl. Qed.
Lemma D_62184 : decode_any W_62184 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62188 : bv 32 := 0x02113423.
Lemma F_62188 : fetch_word Plain.M.loaded_segments (0x621e0 : word) = Some W_62188.
Proof. vm_refl. Qed.
Lemma D_62188 : decode_any W_62188 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6218c : bv 32 := 0x02813023.
Lemma F_6218c : fetch_word Plain.M.loaded_segments (0x621e4 : word) = Some W_6218c.
Proof. vm_refl. Qed.
Lemma D_6218c : decode_any W_6218c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62190 : bv 32 := 0x00913c23.
Lemma F_62190 : fetch_word Plain.M.loaded_segments (0x621e8 : word) = Some W_62190.
Proof. vm_refl. Qed.
Lemma D_62190 : decode_any W_62190 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62194 : bv 32 := 0x01213823.
Lemma F_62194 : fetch_word Plain.M.loaded_segments (0x621ec : word) = Some W_62194.
Proof. vm_refl. Qed.
Lemma D_62194 : decode_any W_62194 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62198 : bv 32 := 0x00058493.
Lemma F_62198 : fetch_word Plain.M.loaded_segments (0x621f0 : word) = Some W_62198.
Proof. vm_refl. Qed.
Lemma D_62198 : decode_any W_62198 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6219c : bv 32 := 0x124000ef.
Lemma F_6219c : fetch_word Plain.M.loaded_segments (0x621f4 : word) = Some W_6219c.
Proof. vm_refl. Qed.
Lemma D_6219c : decode_any W_6219c = Some (Jal 1 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621a0 : bv 32 := 0x02050e63.
Lemma F_621a0 : fetch_word Plain.M.loaded_segments (0x621f8 : word) = Some W_621a0.
Proof. vm_refl. Qed.
Lemma D_621a0 : decode_any W_621a0 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621a4 : bv 32 := 0x00050413.
Lemma F_621a4 : fetch_word Plain.M.loaded_segments (0x621fc : word) = Some W_621a4.
Proof. vm_refl. Qed.
Lemma D_621a4 : decode_any W_621a4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621a8 : bv 32 := 0x01052503.
Lemma F_621a8 : fetch_word Plain.M.loaded_segments (0x62200 : word) = Some W_621a8.
Proof. vm_refl. Qed.
Lemma D_621a8 : decode_any W_621a8 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621ac : bv 32 := 0x0008d597.
Lemma F_621ac : fetch_word Plain.M.loaded_segments (0x62204 : word) = Some W_621ac.
Proof. vm_refl. Qed.
Lemma D_621ac : decode_any W_621ac = Some (Auipc 11 141, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621b0 : bv 32 := 0x56458913.
Lemma F_621b0 : fetch_word Plain.M.loaded_segments (0x62208 : word) = Some W_621b0.
Proof. vm_refl. Qed.
Lemma D_621b0 : decode_any W_621b0 = Some (OpImm ALU_ADD 18 11 1380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621b4 : bv 32 := 0x00093583.
Lemma F_621b4 : fetch_word Plain.M.loaded_segments (0x6220c : word) = Some W_621b4.
Proof. vm_refl. Qed.
Lemma D_621b4 : decode_any W_621b4 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621b8 : bv 32 := 0x02a48533.
Lemma F_621b8 : fetch_word Plain.M.loaded_segments (0x62210 : word) = Some W_621b8.
Proof. vm_refl. Qed.
Lemma D_621b8 : decode_any W_621b8 = Some (Mul M_MUL 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621bc : bv 32 := 0x00251513.
Lemma F_621bc : fetch_word Plain.M.loaded_segments (0x62214 : word) = Some W_621bc.
Proof. vm_refl. Qed.
Lemma D_621bc : decode_any W_621bc = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621c0 : bv 32 := 0x000580e7.
Lemma F_621c0 : fetch_word Plain.M.loaded_segments (0x62218 : word) = Some W_621c0.
Proof. vm_refl. Qed.
Lemma D_621c0 : decode_any W_621c0 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621c4 : bv 32 := 0x04050c63.
Lemma F_621c4 : fetch_word Plain.M.loaded_segments (0x6221c : word) = Some W_621c4.
Proof. vm_refl. Qed.
Lemma D_621c4 : decode_any W_621c4 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621c8 : bv 32 := 0x02a43c23.
Lemma F_621c8 : fetch_word Plain.M.loaded_segments (0x62220 : word) = Some W_621c8.
Proof. vm_refl. Qed.
Lemma D_621c8 : decode_any W_621c8 = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621cc : bv 32 := 0x00040513.
Lemma F_621cc : fetch_word Plain.M.loaded_segments (0x62224 : word) = Some W_621cc.
Proof. vm_refl. Qed.
Lemma D_621cc : decode_any W_621cc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621d0 : bv 32 := 0x00000593.
Lemma F_621d0 : fetch_word Plain.M.loaded_segments (0x62228 : word) = Some W_621d0.
Proof. vm_refl. Qed.
Lemma D_621d0 : decode_any W_621d0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621d4 : bv 32 := 0x45d010ef.
Lemma F_621d4 : fetch_word Plain.M.loaded_segments (0x6222c : word) = Some W_621d4.
Proof. vm_refl. Qed.
Lemma D_621d4 : decode_any W_621d4 = Some (Jal 1 7260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621d8 : bv 32 := 0x0cc0006f.
Lemma F_621d8 : fetch_word Plain.M.loaded_segments (0x62230 : word) = Some W_621d8.
Proof. vm_refl. Qed.
Lemma D_621d8 : decode_any W_621d8 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621dc : bv 32 := 0x0008c517.
Lemma F_621dc : fetch_word Plain.M.loaded_segments (0x62234 : word) = Some W_621dc.
Proof. vm_refl. Qed.
Lemma D_621dc : decode_any W_621dc = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621e0 : bv 32 := 0x33c53503.
Lemma F_621e0 : fetch_word Plain.M.loaded_segments (0x62238 : word) = Some W_621e0.
Proof. vm_refl. Qed.
Lemma D_621e0 : decode_any W_621e0 = Some (Load SZ8 true 10 10 828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621e4 : bv 32 := 0x00052503.
Lemma F_621e4 : fetch_word Plain.M.loaded_segments (0x6223c : word) = Some W_621e4.
Proof. vm_refl. Qed.
Lemma D_621e4 : decode_any W_621e4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621e8 : bv 32 := 0x00500593.
Lemma F_621e8 : fetch_word Plain.M.loaded_segments (0x62240 : word) = Some W_621e8.
Proof. vm_refl. Qed.
Lemma D_621e8 : decode_any W_621e8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621ec : bv 32 := 0x0aa5ca63.
Lemma F_621ec : fetch_word Plain.M.loaded_segments (0x62244 : word) = Some W_621ec.
Proof. vm_refl. Qed.
Lemma D_621ec : decode_any W_621ec = Some (Branch BC_LT 11 10 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621f0 : bv 32 := 0xfffb0517.
Lemma F_621f0 : fetch_word Plain.M.loaded_segments (0x62248 : word) = Some W_621f0.
Proof. vm_refl. Qed.
Lemma D_621f0 : decode_any W_621f0 = Some (Auipc 10 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621f4 : bv 32 := 0xfffb1597.
Lemma F_621f4 : fetch_word Plain.M.loaded_segments (0x6224c : word) = Some W_621f4.
Proof. vm_refl. Qed.
Lemma D_621f4 : decode_any W_621f4 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621f8 : bv 32 := 0xe1a50513.
Lemma F_621f8 : fetch_word Plain.M.loaded_segments (0x62250 : word) = Some W_621f8.
Proof. vm_refl. Qed.
Lemma D_621f8 : decode_any W_621f8 = Some (OpImm ALU_ADD 10 10 3610, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_621fc : bv 32 := 0xfc158593.
Lemma F_621fc : fetch_word Plain.M.loaded_segments (0x62254 : word) = Some W_621fc.
Proof. vm_refl. Qed.
Lemma D_621fc : decode_any W_621fc = Some (OpImm ALU_ADD 11 11 4033, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62200 : bv 32 := 0x00000613.
Lemma F_62200 : fetch_word Plain.M.loaded_segments (0x62258 : word) = Some W_62200.
Proof. vm_refl. Qed.
Lemma D_62200 : decode_any W_62200 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62204 : bv 32 := 0x02813083.
Lemma F_62204 : fetch_word Plain.M.loaded_segments (0x6225c : word) = Some W_62204.
Proof. vm_refl. Qed.
Lemma D_62204 : decode_any W_62204 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62208 : bv 32 := 0x02013403.
Lemma F_62208 : fetch_word Plain.M.loaded_segments (0x62260 : word) = Some W_62208.
Proof. vm_refl. Qed.
Lemma D_62208 : decode_any W_62208 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6220c : bv 32 := 0x01813483.
Lemma F_6220c : fetch_word Plain.M.loaded_segments (0x62264 : word) = Some W_6220c.
Proof. vm_refl. Qed.
Lemma D_6220c : decode_any W_6220c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62210 : bv 32 := 0x01013903.
Lemma F_62210 : fetch_word Plain.M.loaded_segments (0x62268 : word) = Some W_62210.
Proof. vm_refl. Qed.
Lemma D_62210 : decode_any W_62210 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62214 : bv 32 := 0x03010113.
Lemma F_62214 : fetch_word Plain.M.loaded_segments (0x6226c : word) = Some W_62214.
Proof. vm_refl. Qed.
Lemma D_62214 : decode_any W_62214 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62218 : bv 32 := 0xc35fa06f.
Lemma F_62218 : fetch_word Plain.M.loaded_segments (0x62270 : word) = Some W_62218.
Proof. vm_refl. Qed.
Lemma D_62218 : decode_any W_62218 = Some (Jal 0 2075700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6221c : bv 32 := 0x01440513.
Lemma F_6221c : fetch_word Plain.M.loaded_segments (0x62274 : word) = Some W_6221c.
Proof. vm_refl. Qed.
Lemma D_6221c : decode_any W_6221c = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62220 : bv 32 := 0xfff00593.
Lemma F_62220 : fetch_word Plain.M.loaded_segments (0x62278 : word) = Some W_62220.
Proof. vm_refl. Qed.
Lemma D_62220 : decode_any W_62220 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62224 : bv 32 := 0x06b5252f.
Lemma F_62224 : fetch_word Plain.M.loaded_segments (0x6227c : word) = Some W_62224.
Proof. vm_refl. Qed.
Lemma D_62224 : decode_any W_62224 = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62228 : bv 32 := 0x00100593.
Lemma F_62228 : fetch_word Plain.M.loaded_segments (0x62280 : word) = Some W_62228.
Proof. vm_refl. Qed.
Lemma D_62228 : decode_any W_62228 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6222c : bv 32 := 0x04b51063.
Lemma F_6222c : fetch_word Plain.M.loaded_segments (0x62284 : word) = Some W_6222c.
Proof. vm_refl. Qed.
Lemma D_6222c : decode_any W_6222c = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62230 : bv 32 := 0x03843503.
Lemma F_62230 : fetch_word Plain.M.loaded_segments (0x62288 : word) = Some W_62230.
Proof. vm_refl. Qed.
Lemma D_62230 : decode_any W_62230 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62234 : bv 32 := 0x00050663.
Lemma F_62234 : fetch_word Plain.M.loaded_segments (0x6228c : word) = Some W_62234.
Proof. vm_refl. Qed.
Lemma D_62234 : decode_any W_62234 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62240 : bv 32 := 0x02843503.
Lemma F_62240 : fetch_word Plain.M.loaded_segments (0x62298 : word) = Some W_62240.
Proof. vm_refl. Qed.
Lemma D_62240 : decode_any W_62240 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62244 : bv 32 := 0x00050463.
Lemma F_62244 : fetch_word Plain.M.loaded_segments (0x6229c : word) = Some W_62244.
Proof. vm_refl. Qed.
Lemma D_62244 : decode_any W_62244 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6224c : bv 32 := 0x03043503.
Lemma F_6224c : fetch_word Plain.M.loaded_segments (0x622a4 : word) = Some W_6224c.
Proof. vm_refl. Qed.
Lemma D_6224c : decode_any W_6224c = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62250 : bv 32 := 0x00a13423.
Lemma F_62250 : fetch_word Plain.M.loaded_segments (0x622a8 : word) = Some W_62250.
Proof. vm_refl. Qed.
Lemma D_62250 : decode_any W_62250 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62254 : bv 32 := 0x00050863.
Lemma F_62254 : fetch_word Plain.M.loaded_segments (0x622ac : word) = Some W_62254.
Proof. vm_refl. Qed.
Lemma D_62254 : decode_any W_62254 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62264 : bv 32 := 0x00040513.
Lemma F_62264 : fetch_word Plain.M.loaded_segments (0x622bc : word) = Some W_62264.
Proof. vm_refl. Qed.
Lemma D_62264 : decode_any W_62264 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62268 : bv 32 := 0x744750ef.
Lemma F_62268 : fetch_word Plain.M.loaded_segments (0x622c0 : word) = Some W_62268.
Proof. vm_refl. Qed.
Lemma D_62268 : decode_any W_62268 = Some (Jal 1 481092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6226c : bv 32 := 0x0008c517.
Lemma F_6226c : fetch_word Plain.M.loaded_segments (0x622c4 : word) = Some W_6226c.
Proof. vm_refl. Qed.
Lemma D_6226c : decode_any W_6226c = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62270 : bv 32 := 0x2ac53503.
Lemma F_62270 : fetch_word Plain.M.loaded_segments (0x622c8 : word) = Some W_62270.
Proof. vm_refl. Qed.
Lemma D_62270 : decode_any W_62270 = Some (Load SZ8 true 10 10 684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62274 : bv 32 := 0x00052503.
Lemma F_62274 : fetch_word Plain.M.loaded_segments (0x622cc : word) = Some W_62274.
Proof. vm_refl. Qed.
Lemma D_62274 : decode_any W_62274 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62278 : bv 32 := 0x00500593.
Lemma F_62278 : fetch_word Plain.M.loaded_segments (0x622d0 : word) = Some W_62278.
Proof. vm_refl. Qed.
Lemma D_62278 : decode_any W_62278 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6227c : bv 32 := 0x02a5c263.
Lemma F_6227c : fetch_word Plain.M.loaded_segments (0x622d4 : word) = Some W_6227c.
Proof. vm_refl. Qed.
Lemma D_6227c : decode_any W_6227c = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62280 : bv 32 := 0xfffb7517.
Lemma F_62280 : fetch_word Plain.M.loaded_segments (0x622d8 : word) = Some W_62280.
Proof. vm_refl. Qed.
Lemma D_62280 : decode_any W_62280 = Some (Auipc 10 1048503, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62284 : bv 32 := 0xfffb1597.
Lemma F_62284 : fetch_word Plain.M.loaded_segments (0x622dc : word) = Some W_62284.
Proof. vm_refl. Qed.
Lemma D_62284 : decode_any W_62284 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62288 : bv 32 := 0x66f50513.
Lemma F_62288 : fetch_word Plain.M.loaded_segments (0x622e0 : word) = Some W_62288.
Proof. vm_refl. Qed.
Lemma D_62288 : decode_any W_62288 = Some (OpImm ALU_ADD 10 10 1647, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6228c : bv 32 := 0xf3158593.
Lemma F_6228c : fetch_word Plain.M.loaded_segments (0x622e4 : word) = Some W_6228c.
Proof. vm_refl. Qed.
Lemma D_6228c : decode_any W_6228c = Some (OpImm ALU_ADD 11 11 3889, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62290 : bv 32 := 0x00000613.
Lemma F_62290 : fetch_word Plain.M.loaded_segments (0x622e8 : word) = Some W_62290.
Proof. vm_refl. Qed.
Lemma D_62290 : decode_any W_62290 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62294 : bv 32 := 0xbb9fa0ef.
Lemma F_62294 : fetch_word Plain.M.loaded_segments (0x622ec : word) = Some W_62294.
Proof. vm_refl. Qed.
Lemma D_62294 : decode_any W_62294 = Some (Jal 1 2075576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62298 : bv 32 := 0x00050413.
Lemma F_62298 : fetch_word Plain.M.loaded_segments (0x622f0 : word) = Some W_62298.
Proof. vm_refl. Qed.
Lemma D_62298 : decode_any W_62298 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6229c : bv 32 := 0x0080006f.
Lemma F_6229c : fetch_word Plain.M.loaded_segments (0x622f4 : word) = Some W_6229c.
Proof. vm_refl. Qed.
Lemma D_6229c : decode_any W_6229c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_622a4 : bv 32 := 0x00040513.
Lemma F_622a4 : fetch_word Plain.M.loaded_segments (0x622fc : word) = Some W_622a4.
Proof. vm_refl. Qed.
Lemma D_622a4 : decode_any W_622a4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_622a8 : bv 32 := 0x02813083.
Lemma F_622a8 : fetch_word Plain.M.loaded_segments (0x62300 : word) = Some W_622a8.
Proof. vm_refl. Qed.
Lemma D_622a8 : decode_any W_622a8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_622ac : bv 32 := 0x02013403.
Lemma F_622ac : fetch_word Plain.M.loaded_segments (0x62304 : word) = Some W_622ac.
Proof. vm_refl. Qed.
Lemma D_622ac : decode_any W_622ac = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_622b0 : bv 32 := 0x01813483.
Lemma F_622b0 : fetch_word Plain.M.loaded_segments (0x62308 : word) = Some W_622b0.
Proof. vm_refl. Qed.
Lemma D_622b0 : decode_any W_622b0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_622b4 : bv 32 := 0x01013903.
Lemma F_622b4 : fetch_word Plain.M.loaded_segments (0x6230c : word) = Some W_622b4.
Proof. vm_refl. Qed.
Lemma D_622b4 : decode_any W_622b4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_622b8 : bv 32 := 0x03010113.
Lemma F_622b8 : fetch_word Plain.M.loaded_segments (0x62310 : word) = Some W_622b8.
Proof. vm_refl. Qed.
Lemma D_622b8 : decode_any W_622b8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_622bc : bv 32 := 0x00008067.
Lemma F_622bc : fetch_word Plain.M.loaded_segments (0x62314 : word) = Some W_622bc.
Proof. vm_refl. Qed.
Lemma D_622bc : decode_any W_622bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62780 : bv 32 := 0xfe010113.
Lemma F_62780 : fetch_word Plain.M.loaded_segments (0x627d8 : word) = Some W_62780.
Proof. vm_refl. Qed.
Lemma D_62780 : decode_any W_62780 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62784 : bv 32 := 0x00113c23.
Lemma F_62784 : fetch_word Plain.M.loaded_segments (0x627dc : word) = Some W_62784.
Proof. vm_refl. Qed.
Lemma D_62784 : decode_any W_62784 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62788 : bv 32 := 0x00813823.
Lemma F_62788 : fetch_word Plain.M.loaded_segments (0x627e0 : word) = Some W_62788.
Proof. vm_refl. Qed.
Lemma D_62788 : decode_any W_62788 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6278c : bv 32 := 0x00913423.
Lemma F_6278c : fetch_word Plain.M.loaded_segments (0x627e4 : word) = Some W_6278c.
Proof. vm_refl. Qed.
Lemma D_6278c : decode_any W_6278c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62790 : bv 32 := 0x02050a63.
Lemma F_62790 : fetch_word Plain.M.loaded_segments (0x627e8 : word) = Some W_62790.
Proof. vm_refl. Qed.
Lemma D_62790 : decode_any W_62790 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62794 : bv 32 := 0x00050493.
Lemma F_62794 : fetch_word Plain.M.loaded_segments (0x627ec : word) = Some W_62794.
Proof. vm_refl. Qed.
Lemma D_62794 : decode_any W_62794 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62798 : bv 32 := 0x00052503.
Lemma F_62798 : fetch_word Plain.M.loaded_segments (0x627f0 : word) = Some W_62798.
Proof. vm_refl. Qed.
Lemma D_62798 : decode_any W_62798 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6279c : bv 32 := 0x0044a583.
Lemma F_6279c : fetch_word Plain.M.loaded_segments (0x627f4 : word) = Some W_6279c.
Proof. vm_refl. Qed.
Lemma D_6279c : decode_any W_6279c = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627a0 : bv 32 := 0x0084a603.
Lemma F_627a0 : fetch_word Plain.M.loaded_segments (0x627f8 : word) = Some W_627a0.
Proof. vm_refl. Qed.
Lemma D_627a0 : decode_any W_627a0 = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627a4 : bv 32 := 0x9e1ff0ef.
Lemma F_627a4 : fetch_word Plain.M.loaded_segments (0x627fc : word) = Some W_627a4.
Proof. vm_refl. Qed.
Lemma D_627a4 : decode_any W_627a4 = Some (Jal 1 2095584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627a8 : bv 32 := 0x04050263.
Lemma F_627a8 : fetch_word Plain.M.loaded_segments (0x62800 : word) = Some W_627a8.
Proof. vm_refl. Qed.
Lemma D_627a8 : decode_any W_627a8 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627ac : bv 32 := 0x00050413.
Lemma F_627ac : fetch_word Plain.M.loaded_segments (0x62804 : word) = Some W_627ac.
Proof. vm_refl. Qed.
Lemma D_627ac : decode_any W_627ac = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627b0 : bv 32 := 0x08a48063.
Lemma F_627b0 : fetch_word Plain.M.loaded_segments (0x62808 : word) = Some W_627b0.
Proof. vm_refl. Qed.
Lemma D_627b0 : decode_any W_627b0 = Some (Branch BC_EQ 9 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627b4 : bv 32 := 0x00c4a503.
Lemma F_627b4 : fetch_word Plain.M.loaded_segments (0x6280c : word) = Some W_627b4.
Proof. vm_refl. Qed.
Lemma D_627b4 : decode_any W_627b4 = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627b8 : bv 32 := 0x08a05463.
Lemma F_627b8 : fetch_word Plain.M.loaded_segments (0x62810 : word) = Some W_627b8.
Proof. vm_refl. Qed.
Lemma D_627b8 : decode_any W_627b8 = Some (Branch BC_GE 0 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627bc : bv 32 := 0x00a42623.
Lemma F_627bc : fetch_word Plain.M.loaded_segments (0x62814 : word) = Some W_627bc.
Proof. vm_refl. Qed.
Lemma D_627bc : decode_any W_627bc = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627c0 : bv 32 := 0x0ac0006f.
Lemma F_627c0 : fetch_word Plain.M.loaded_segments (0x62818 : word) = Some W_627c0.
Proof. vm_refl. Qed.
Lemma D_627c0 : decode_any W_627c0 = Some (Jal 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627ec : bv 32 := 0x0008c517.
Lemma F_627ec : fetch_word Plain.M.loaded_segments (0x62844 : word) = Some W_627ec.
Proof. vm_refl. Qed.
Lemma D_627ec : decode_any W_627ec = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627f0 : bv 32 := 0xd2c53503.
Lemma F_627f0 : fetch_word Plain.M.loaded_segments (0x62848 : word) = Some W_627f0.
Proof. vm_refl. Qed.
Lemma D_627f0 : decode_any W_627f0 = Some (Load SZ8 true 10 10 3372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627f4 : bv 32 := 0x00052503.
Lemma F_627f4 : fetch_word Plain.M.loaded_segments (0x6284c : word) = Some W_627f4.
Proof. vm_refl. Qed.
Lemma D_627f4 : decode_any W_627f4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627f8 : bv 32 := 0x00500593.
Lemma F_627f8 : fetch_word Plain.M.loaded_segments (0x62850 : word) = Some W_627f8.
Proof. vm_refl. Qed.
Lemma D_627f8 : decode_any W_627f8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_627fc : bv 32 := 0x02a5c663.
Lemma F_627fc : fetch_word Plain.M.loaded_segments (0x62854 : word) = Some W_627fc.
Proof. vm_refl. Qed.
Lemma D_627fc : decode_any W_627fc = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62800 : bv 32 := 0xfffb0517.
Lemma F_62800 : fetch_word Plain.M.loaded_segments (0x62858 : word) = Some W_62800.
Proof. vm_refl. Qed.
Lemma D_62800 : decode_any W_62800 = Some (Auipc 10 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62804 : bv 32 := 0xfffb7597.
Lemma F_62804 : fetch_word Plain.M.loaded_segments (0x6285c : word) = Some W_62804.
Proof. vm_refl. Qed.
Lemma D_62804 : decode_any W_62804 = Some (Auipc 11 1048503, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62808 : bv 32 := 0x80a50513.
Lemma F_62808 : fetch_word Plain.M.loaded_segments (0x62860 : word) = Some W_62808.
Proof. vm_refl. Qed.
Lemma D_62808 : decode_any W_62808 = Some (OpImm ALU_ADD 10 10 2058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6280c : bv 32 := 0x10858593.
Lemma F_6280c : fetch_word Plain.M.loaded_segments (0x62864 : word) = Some W_6280c.
Proof. vm_refl. Qed.
Lemma D_6280c : decode_any W_6280c = Some (OpImm ALU_ADD 11 11 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62810 : bv 32 := 0x00000613.
Lemma F_62810 : fetch_word Plain.M.loaded_segments (0x62868 : word) = Some W_62810.
Proof. vm_refl. Qed.
Lemma D_62810 : decode_any W_62810 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62814 : bv 32 := 0x01813083.
Lemma F_62814 : fetch_word Plain.M.loaded_segments (0x6286c : word) = Some W_62814.
Proof. vm_refl. Qed.
Lemma D_62814 : decode_any W_62814 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62818 : bv 32 := 0x01013403.
Lemma F_62818 : fetch_word Plain.M.loaded_segments (0x62870 : word) = Some W_62818.
Proof. vm_refl. Qed.
Lemma D_62818 : decode_any W_62818 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6281c : bv 32 := 0x00813483.
Lemma F_6281c : fetch_word Plain.M.loaded_segments (0x62874 : word) = Some W_6281c.
Proof. vm_refl. Qed.
Lemma D_6281c : decode_any W_6281c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62820 : bv 32 := 0x02010113.
Lemma F_62820 : fetch_word Plain.M.loaded_segments (0x62878 : word) = Some W_62820.
Proof. vm_refl. Qed.
Lemma D_62820 : decode_any W_62820 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62824 : bv 32 := 0xe28fa06f.
Lemma F_62824 : fetch_word Plain.M.loaded_segments (0x6287c : word) = Some W_62824.
Proof. vm_refl. Qed.
Lemma D_62824 : decode_any W_62824 = Some (Jal 0 2074152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6286c : bv 32 := 0x0184b503.
Lemma F_6286c : fetch_word Plain.M.loaded_segments (0x628c4 : word) = Some W_6286c.
Proof. vm_refl. Qed.
Lemma D_6286c : decode_any W_6286c = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62870 : bv 32 := 0x00a43c23.
Lemma F_62870 : fetch_word Plain.M.loaded_segments (0x628c8 : word) = Some W_62870.
Proof. vm_refl. Qed.
Lemma D_62870 : decode_any W_62870 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62874 : bv 32 := 0x00040513.
Lemma F_62874 : fetch_word Plain.M.loaded_segments (0x628cc : word) = Some W_62874.
Proof. vm_refl. Qed.
Lemma D_62874 : decode_any W_62874 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62878 : bv 32 := 0x00048593.
Lemma F_62878 : fetch_word Plain.M.loaded_segments (0x628d0 : word) = Some W_62878.
Proof. vm_refl. Qed.
Lemma D_62878 : decode_any W_62878 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6287c : bv 32 := 0x144000ef.
Lemma F_6287c : fetch_word Plain.M.loaded_segments (0x628d4 : word) = Some W_6287c.
Proof. vm_refl. Qed.
Lemma D_6287c : decode_any W_6287c = Some (Jal 1 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62880 : bv 32 := 0x0284b583.
Lemma F_62880 : fetch_word Plain.M.loaded_segments (0x628d8 : word) = Some W_62880.
Proof. vm_refl. Qed.
Lemma D_62880 : decode_any W_62880 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62884 : bv 32 := 0x02840513.
Lemma F_62884 : fetch_word Plain.M.loaded_segments (0x628dc : word) = Some W_62884.
Proof. vm_refl. Qed.
Lemma D_62884 : decode_any W_62884 = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62888 : bv 32 := 0xafdfa0ef.
Lemma F_62888 : fetch_word Plain.M.loaded_segments (0x628e0 : word) = Some W_62888.
Proof. vm_refl. Qed.
Lemma D_62888 : decode_any W_62888 = Some (Jal 1 2075388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6288c : bv 32 := 0x0204a503.
Lemma F_6288c : fetch_word Plain.M.loaded_segments (0x628e4 : word) = Some W_6288c.
Proof. vm_refl. Qed.
Lemma D_6288c : decode_any W_6288c = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62890 : bv 32 := 0x02a42023.
Lemma F_62890 : fetch_word Plain.M.loaded_segments (0x628e8 : word) = Some W_62890.
Proof. vm_refl. Qed.
Lemma D_62890 : decode_any W_62890 = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62894 : bv 32 := 0x00040513.
Lemma F_62894 : fetch_word Plain.M.loaded_segments (0x628ec : word) = Some W_62894.
Proof. vm_refl. Qed.
Lemma D_62894 : decode_any W_62894 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62898 : bv 32 := 0x00000593.
Lemma F_62898 : fetch_word Plain.M.loaded_segments (0x628f0 : word) = Some W_62898.
Proof. vm_refl. Qed.
Lemma D_62898 : decode_any W_62898 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6289c : bv 32 := 0x594010ef.
Lemma F_6289c : fetch_word Plain.M.loaded_segments (0x628f4 : word) = Some W_6289c.
Proof. vm_refl. Qed.
Lemma D_6289c : decode_any W_6289c = Some (Jal 1 5524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628a0 : bv 32 := 0x00040513.
Lemma F_628a0 : fetch_word Plain.M.loaded_segments (0x628f8 : word) = Some W_628a0.
Proof. vm_refl. Qed.
Lemma D_628a0 : decode_any W_628a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628a4 : bv 32 := 0x01813083.
Lemma F_628a4 : fetch_word Plain.M.loaded_segments (0x628fc : word) = Some W_628a4.
Proof. vm_refl. Qed.
Lemma D_628a4 : decode_any W_628a4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628a8 : bv 32 := 0x01013403.
Lemma F_628a8 : fetch_word Plain.M.loaded_segments (0x62900 : word) = Some W_628a8.
Proof. vm_refl. Qed.
Lemma D_628a8 : decode_any W_628a8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628ac : bv 32 := 0x00813483.
Lemma F_628ac : fetch_word Plain.M.loaded_segments (0x62904 : word) = Some W_628ac.
Proof. vm_refl. Qed.
Lemma D_628ac : decode_any W_628ac = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628b0 : bv 32 := 0x02010113.
Lemma F_628b0 : fetch_word Plain.M.loaded_segments (0x62908 : word) = Some W_628b0.
Proof. vm_refl. Qed.
Lemma D_628b0 : decode_any W_628b0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628b4 : bv 32 := 0x00008067.
Lemma F_628b4 : fetch_word Plain.M.loaded_segments (0x6290c : word) = Some W_628b4.
Proof. vm_refl. Qed.
Lemma D_628b4 : decode_any W_628b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628b8 : bv 32 := 0x00058463.
Lemma F_628b8 : fetch_word Plain.M.loaded_segments (0x62910 : word) = Some W_628b8.
Proof. vm_refl. Qed.
Lemma D_628b8 : decode_any W_628b8 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628bc : bv 32 := 0x0005a023.
Lemma F_628bc : fetch_word Plain.M.loaded_segments (0x62914 : word) = Some W_628bc.
Proof. vm_refl. Qed.
Lemma D_628bc : decode_any W_628bc = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628c0 : bv 32 := 0x00060463.
Lemma F_628c0 : fetch_word Plain.M.loaded_segments (0x62918 : word) = Some W_628c0.
Proof. vm_refl. Qed.
Lemma D_628c0 : decode_any W_628c0 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628c4 : bv 32 := 0x00062023.
Lemma F_628c4 : fetch_word Plain.M.loaded_segments (0x6291c : word) = Some W_628c4.
Proof. vm_refl. Qed.
Lemma D_628c4 : decode_any W_628c4 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628c8 : bv 32 := 0x00068463.
Lemma F_628c8 : fetch_word Plain.M.loaded_segments (0x62920 : word) = Some W_628c8.
Proof. vm_refl. Qed.
Lemma D_628c8 : decode_any W_628c8 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628cc : bv 32 := 0x0006a023.
Lemma F_628cc : fetch_word Plain.M.loaded_segments (0x62924 : word) = Some W_628cc.
Proof. vm_refl. Qed.
Lemma D_628cc : decode_any W_628cc = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628d0 : bv 32 := 0x02050a63.
Lemma F_628d0 : fetch_word Plain.M.loaded_segments (0x62928 : word) = Some W_628d0.
Proof. vm_refl. Qed.
Lemma D_628d0 : decode_any W_628d0 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628d4 : bv 32 := 0x00058663.
Lemma F_628d4 : fetch_word Plain.M.loaded_segments (0x6292c : word) = Some W_628d4.
Proof. vm_refl. Qed.
Lemma D_628d4 : decode_any W_628d4 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628d8 : bv 32 := 0x00052703.
Lemma F_628d8 : fetch_word Plain.M.loaded_segments (0x62930 : word) = Some W_628d8.
Proof. vm_refl. Qed.
Lemma D_628d8 : decode_any W_628d8 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628dc : bv 32 := 0x00e5a023.
Lemma F_628dc : fetch_word Plain.M.loaded_segments (0x62934 : word) = Some W_628dc.
Proof. vm_refl. Qed.
Lemma D_628dc : decode_any W_628dc = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628e0 : bv 32 := 0x00060663.
Lemma F_628e0 : fetch_word Plain.M.loaded_segments (0x62938 : word) = Some W_628e0.
Proof. vm_refl. Qed.
Lemma D_628e0 : decode_any W_628e0 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628e4 : bv 32 := 0x00452583.
Lemma F_628e4 : fetch_word Plain.M.loaded_segments (0x6293c : word) = Some W_628e4.
Proof. vm_refl. Qed.
Lemma D_628e4 : decode_any W_628e4 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628e8 : bv 32 := 0x00b62023.
Lemma F_628e8 : fetch_word Plain.M.loaded_segments (0x62940 : word) = Some W_628e8.
Proof. vm_refl. Qed.
Lemma D_628e8 : decode_any W_628e8 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628ec : bv 32 := 0x00000593.
Lemma F_628ec : fetch_word Plain.M.loaded_segments (0x62944 : word) = Some W_628ec.
Proof. vm_refl. Qed.
Lemma D_628ec : decode_any W_628ec = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628f0 : bv 32 := 0x00068663.
Lemma F_628f0 : fetch_word Plain.M.loaded_segments (0x62948 : word) = Some W_628f0.
Proof. vm_refl. Qed.
Lemma D_628f0 : decode_any W_628f0 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628f4 : bv 32 := 0x00852503.
Lemma F_628f4 : fetch_word Plain.M.loaded_segments (0x6294c : word) = Some W_628f4.
Proof. vm_refl. Qed.
Lemma D_628f4 : decode_any W_628f4 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628f8 : bv 32 := 0x00a6a023.
Lemma F_628f8 : fetch_word Plain.M.loaded_segments (0x62950 : word) = Some W_628f8.
Proof. vm_refl. Qed.
Lemma D_628f8 : decode_any W_628f8 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_628fc : bv 32 := 0x00058513.
Lemma F_628fc : fetch_word Plain.M.loaded_segments (0x62954 : word) = Some W_628fc.
Proof. vm_refl. Qed.
Lemma D_628fc : decode_any W_628fc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62900 : bv 32 := 0x00008067.
Lemma F_62900 : fetch_word Plain.M.loaded_segments (0x62958 : word) = Some W_62900.
Proof. vm_refl. Qed.
Lemma D_62900 : decode_any W_62900 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629c0 : bv 32 := 0xfd010113.
Lemma F_629c0 : fetch_word Plain.M.loaded_segments (0x62a18 : word) = Some W_629c0.
Proof. vm_refl. Qed.
Lemma D_629c0 : decode_any W_629c0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629c4 : bv 32 := 0x02113423.
Lemma F_629c4 : fetch_word Plain.M.loaded_segments (0x62a1c : word) = Some W_629c4.
Proof. vm_refl. Qed.
Lemma D_629c4 : decode_any W_629c4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629c8 : bv 32 := 0x02813023.
Lemma F_629c8 : fetch_word Plain.M.loaded_segments (0x62a20 : word) = Some W_629c8.
Proof. vm_refl. Qed.
Lemma D_629c8 : decode_any W_629c8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629cc : bv 32 := 0x00913c23.
Lemma F_629cc : fetch_word Plain.M.loaded_segments (0x62a24 : word) = Some W_629cc.
Proof. vm_refl. Qed.
Lemma D_629cc : decode_any W_629cc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629d0 : bv 32 := 0x0e058063.
Lemma F_629d0 : fetch_word Plain.M.loaded_segments (0x62a28 : word) = Some W_629d0.
Proof. vm_refl. Qed.
Lemma D_629d0 : decode_any W_629d0 = Some (Branch BC_EQ 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629d4 : bv 32 := 0x10050263.
Lemma F_629d4 : fetch_word Plain.M.loaded_segments (0x62a2c : word) = Some W_629d4.
Proof. vm_refl. Qed.
Lemma D_629d4 : decode_any W_629d4 = Some (Branch BC_EQ 10 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629d8 : bv 32 := 0x0ca58863.
Lemma F_629d8 : fetch_word Plain.M.loaded_segments (0x62a30 : word) = Some W_629d8.
Proof. vm_refl. Qed.
Lemma D_629d8 : decode_any W_629d8 = Some (Branch BC_EQ 11 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629dc : bv 32 := 0x0085a603.
Lemma F_629dc : fetch_word Plain.M.loaded_segments (0x62a34 : word) = Some W_629dc.
Proof. vm_refl. Qed.
Lemma D_629dc : decode_any W_629dc = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629e0 : bv 32 := 0x00852683.
Lemma F_629e0 : fetch_word Plain.M.loaded_segments (0x62a38 : word) = Some W_629e0.
Proof. vm_refl. Qed.
Lemma D_629e0 : decode_any W_629e0 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629e4 : bv 32 := 0x10d61e63.
Lemma F_629e4 : fetch_word Plain.M.loaded_segments (0x62a3c : word) = Some W_629e4.
Proof. vm_refl. Qed.
Lemma D_629e4 : decode_any W_629e4 = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629e8 : bv 32 := 0x03053603.
Lemma F_629e8 : fetch_word Plain.M.loaded_segments (0x62a40 : word) = Some W_629e8.
Proof. vm_refl. Qed.
Lemma D_629e8 : decode_any W_629e8 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629ec : bv 32 := 0x00c13823.
Lemma F_629ec : fetch_word Plain.M.loaded_segments (0x62a44 : word) = Some W_629ec.
Proof. vm_refl. Qed.
Lemma D_629ec : decode_any W_629ec = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_629f0 : bv 32 := 0x02060063.
Lemma F_629f0 : fetch_word Plain.M.loaded_segments (0x62a48 : word) = Some W_629f0.
Proof. vm_refl. Qed.
Lemma D_629f0 : decode_any W_629f0 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a10 : bv 32 := 0x0305b403.
Lemma F_62a10 : fetch_word Plain.M.loaded_segments (0x62a68 : word) = Some W_62a10.
Proof. vm_refl. Qed.
Lemma D_62a10 : decode_any W_62a10 = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a14 : bv 32 := 0x08040a63.
Lemma F_62a14 : fetch_word Plain.M.loaded_segments (0x62a6c : word) = Some W_62a14.
Proof. vm_refl. Qed.
Lemma D_62a14 : decode_any W_62a14 = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a18 : bv 32 := 0x00050493.
Lemma F_62a18 : fetch_word Plain.M.loaded_segments (0x62a70 : word) = Some W_62a18.
Proof. vm_refl. Qed.
Lemma D_62a18 : decode_any W_62a18 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a1c : bv 32 := 0x00c10613.
Lemma F_62a1c : fetch_word Plain.M.loaded_segments (0x62a74 : word) = Some W_62a1c.
Proof. vm_refl. Qed.
Lemma D_62a1c : decode_any W_62a1c = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a20 : bv 32 := 0x00040513.
Lemma F_62a20 : fetch_word Plain.M.loaded_segments (0x62a78 : word) = Some W_62a20.
Proof. vm_refl. Qed.
Lemma D_62a20 : decode_any W_62a20 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a24 : bv 32 := 0x00000593.
Lemma F_62a24 : fetch_word Plain.M.loaded_segments (0x62a7c : word) = Some W_62a24.
Proof. vm_refl. Qed.
Lemma D_62a24 : decode_any W_62a24 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a28 : bv 32 := 0x4f0020ef.
Lemma F_62a28 : fetch_word Plain.M.loaded_segments (0x62a80 : word) = Some W_62a28.
Proof. vm_refl. Qed.
Lemma D_62a28 : decode_any W_62a28 = Some (Jal 1 9456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a2c : bv 32 := 0x00c12503.
Lemma F_62a2c : fetch_word Plain.M.loaded_segments (0x62a84 : word) = Some W_62a2c.
Proof. vm_refl. Qed.
Lemma D_62a2c : decode_any W_62a2c = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a30 : bv 32 := 0x10050663.
Lemma F_62a30 : fetch_word Plain.M.loaded_segments (0x62a88 : word) = Some W_62a30.
Proof. vm_refl. Qed.
Lemma D_62a30 : decode_any W_62a30 = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a34 : bv 32 := 0x00040513.
Lemma F_62a34 : fetch_word Plain.M.loaded_segments (0x62a8c : word) = Some W_62a34.
Proof. vm_refl. Qed.
Lemma D_62a34 : decode_any W_62a34 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a38 : bv 32 := 0x3e4020ef.
Lemma F_62a38 : fetch_word Plain.M.loaded_segments (0x62a90 : word) = Some W_62a38.
Proof. vm_refl. Qed.
Lemma D_62a38 : decode_any W_62a38 = Some (Jal 1 9188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a3c : bv 32 := 0x12050463.
Lemma F_62a3c : fetch_word Plain.M.loaded_segments (0x62a94 : word) = Some W_62a3c.
Proof. vm_refl. Qed.
Lemma D_62a3c : decode_any W_62a3c = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a40 : bv 32 := 0x00048593.
Lemma F_62a40 : fetch_word Plain.M.loaded_segments (0x62a98 : word) = Some W_62a40.
Proof. vm_refl. Qed.
Lemma D_62a40 : decode_any W_62a40 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a44 : bv 32 := 0x0304b603.
Lemma F_62a44 : fetch_word Plain.M.loaded_segments (0x62a9c : word) = Some W_62a44.
Proof. vm_refl. Qed.
Lemma D_62a44 : decode_any W_62a44 = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a48 : bv 32 := 0x00c13823.
Lemma F_62a48 : fetch_word Plain.M.loaded_segments (0x62aa0 : word) = Some W_62a48.
Proof. vm_refl. Qed.
Lemma D_62a48 : decode_any W_62a48 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a4c : bv 32 := 0x00060c63.
Lemma F_62a4c : fetch_word Plain.M.loaded_segments (0x62aa4 : word) = Some W_62a4c.
Proof. vm_refl. Qed.
Lemma D_62a4c : decode_any W_62a4c = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a64 : bv 32 := 0x02a5b823.
Lemma F_62a64 : fetch_word Plain.M.loaded_segments (0x62abc : word) = Some W_62a64.
Proof. vm_refl. Qed.
Lemma D_62a64 : decode_any W_62a64 = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a68 : bv 32 := 0x01010613.
Lemma F_62a68 : fetch_word Plain.M.loaded_segments (0x62ac0 : word) = Some W_62a68.
Proof. vm_refl. Qed.
Lemma D_62a68 : decode_any W_62a68 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a6c : bv 32 := 0x00000593.
Lemma F_62a6c : fetch_word Plain.M.loaded_segments (0x62ac4 : word) = Some W_62a6c.
Proof. vm_refl. Qed.
Lemma D_62a6c : decode_any W_62a6c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a70 : bv 32 := 0x4a8020ef.
Lemma F_62a70 : fetch_word Plain.M.loaded_segments (0x62ac8 : word) = Some W_62a70.
Proof. vm_refl. Qed.
Lemma D_62a70 : decode_any W_62a70 = Some (Jal 1 9384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a74 : bv 32 := 0x01012503.
Lemma F_62a74 : fetch_word Plain.M.loaded_segments (0x62acc : word) = Some W_62a74.
Proof. vm_refl. Qed.
Lemma D_62a74 : decode_any W_62a74 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62a78 : bv 32 := 0x02051863.
Lemma F_62a78 : fetch_word Plain.M.loaded_segments (0x62ad0 : word) = Some W_62a78.
Proof. vm_refl. Qed.
Lemma D_62a78 : decode_any W_62a78 = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62aa8 : bv 32 := 0x00000513.
Lemma F_62aa8 : fetch_word Plain.M.loaded_segments (0x62b00 : word) = Some W_62aa8.
Proof. vm_refl. Qed.
Lemma D_62aa8 : decode_any W_62aa8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62aac : bv 32 := 0x0ec0006f.
Lemma F_62aac : fetch_word Plain.M.loaded_segments (0x62b04 : word) = Some W_62aac.
Proof. vm_refl. Qed.
Lemma D_62aac : decode_any W_62aac = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b64 : bv 32 := 0x0008c517.
Lemma F_62b64 : fetch_word Plain.M.loaded_segments (0x62bbc : word) = Some W_62b64.
Proof. vm_refl. Qed.
Lemma D_62b64 : decode_any W_62b64 = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b68 : bv 32 := 0x9b453503.
Lemma F_62b68 : fetch_word Plain.M.loaded_segments (0x62bc0 : word) = Some W_62b68.
Proof. vm_refl. Qed.
Lemma D_62b68 : decode_any W_62b68 = Some (Load SZ8 true 10 10 2484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b6c : bv 32 := 0x00052503.
Lemma F_62b6c : fetch_word Plain.M.loaded_segments (0x62bc4 : word) = Some W_62b6c.
Proof. vm_refl. Qed.
Lemma D_62b6c : decode_any W_62b6c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b70 : bv 32 := 0x00500593.
Lemma F_62b70 : fetch_word Plain.M.loaded_segments (0x62bc8 : word) = Some W_62b70.
Proof. vm_refl. Qed.
Lemma D_62b70 : decode_any W_62b70 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b74 : bv 32 := 0x02a5c063.
Lemma F_62b74 : fetch_word Plain.M.loaded_segments (0x62bcc : word) = Some W_62b74.
Proof. vm_refl. Qed.
Lemma D_62b74 : decode_any W_62b74 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b78 : bv 32 := 0xfffaf517.
Lemma F_62b78 : fetch_word Plain.M.loaded_segments (0x62bd0 : word) = Some W_62b78.
Proof. vm_refl. Qed.
Lemma D_62b78 : decode_any W_62b78 = Some (Auipc 10 1048495, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b7c : bv 32 := 0xfffb0597.
Lemma F_62b7c : fetch_word Plain.M.loaded_segments (0x62bd4 : word) = Some W_62b7c.
Proof. vm_refl. Qed.
Lemma D_62b7c : decode_any W_62b7c = Some (Auipc 11 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b80 : bv 32 := 0x4a050513.
Lemma F_62b80 : fetch_word Plain.M.loaded_segments (0x62bd8 : word) = Some W_62b80.
Proof. vm_refl. Qed.
Lemma D_62b80 : decode_any W_62b80 = Some (OpImm ALU_ADD 10 10 1184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b84 : bv 32 := 0xadd58593.
Lemma F_62b84 : fetch_word Plain.M.loaded_segments (0x62bdc : word) = Some W_62b84.
Proof. vm_refl. Qed.
Lemma D_62b84 : decode_any W_62b84 = Some (OpImm ALU_ADD 11 11 2781, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b88 : bv 32 := 0x00100613.
Lemma F_62b88 : fetch_word Plain.M.loaded_segments (0x62be0 : word) = Some W_62b88.
Proof. vm_refl. Qed.
Lemma D_62b88 : decode_any W_62b88 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b8c : bv 32 := 0x9f0fa0ef.
Lemma F_62b8c : fetch_word Plain.M.loaded_segments (0x62be4 : word) = Some W_62b8c.
Proof. vm_refl. Qed.
Lemma D_62b8c : decode_any W_62b8c = Some (Jal 1 2073072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b90 : bv 32 := 0x0080006f.
Lemma F_62b90 : fetch_word Plain.M.loaded_segments (0x62be8 : word) = Some W_62b90.
Proof. vm_refl. Qed.
Lemma D_62b90 : decode_any W_62b90 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b98 : bv 32 := 0x02813083.
Lemma F_62b98 : fetch_word Plain.M.loaded_segments (0x62bf0 : word) = Some W_62b98.
Proof. vm_refl. Qed.
Lemma D_62b98 : decode_any W_62b98 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62b9c : bv 32 := 0x02013403.
Lemma F_62b9c : fetch_word Plain.M.loaded_segments (0x62bf4 : word) = Some W_62b9c.
Proof. vm_refl. Qed.
Lemma D_62b9c : decode_any W_62b9c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ba0 : bv 32 := 0x01813483.
Lemma F_62ba0 : fetch_word Plain.M.loaded_segments (0x62bf8 : word) = Some W_62ba0.
Proof. vm_refl. Qed.
Lemma D_62ba0 : decode_any W_62ba0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ba4 : bv 32 := 0x03010113.
Lemma F_62ba4 : fetch_word Plain.M.loaded_segments (0x62bfc : word) = Some W_62ba4.
Proof. vm_refl. Qed.
Lemma D_62ba4 : decode_any W_62ba4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ba8 : bv 32 := 0x00008067.
Lemma F_62ba8 : fetch_word Plain.M.loaded_segments (0x62c00 : word) = Some W_62ba8.
Proof. vm_refl. Qed.
Lemma D_62ba8 : decode_any W_62ba8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62dd8 : bv 32 := 0xfd010113.
Lemma F_62dd8 : fetch_word Plain.M.loaded_segments (0x62e30 : word) = Some W_62dd8.
Proof. vm_refl. Qed.
Lemma D_62dd8 : decode_any W_62dd8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ddc : bv 32 := 0x02113423.
Lemma F_62ddc : fetch_word Plain.M.loaded_segments (0x62e34 : word) = Some W_62ddc.
Proof. vm_refl. Qed.
Lemma D_62ddc : decode_any W_62ddc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62de0 : bv 32 := 0x02813023.
Lemma F_62de0 : fetch_word Plain.M.loaded_segments (0x62e38 : word) = Some W_62de0.
Proof. vm_refl. Qed.
Lemma D_62de0 : decode_any W_62de0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62de4 : bv 32 := 0x00913c23.
Lemma F_62de4 : fetch_word Plain.M.loaded_segments (0x62e3c : word) = Some W_62de4.
Proof. vm_refl. Qed.
Lemma D_62de4 : decode_any W_62de4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62de8 : bv 32 := 0x01213823.
Lemma F_62de8 : fetch_word Plain.M.loaded_segments (0x62e40 : word) = Some W_62de8.
Proof. vm_refl. Qed.
Lemma D_62de8 : decode_any W_62de8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62dec : bv 32 := 0x01313423.
Lemma F_62dec : fetch_word Plain.M.loaded_segments (0x62e44 : word) = Some W_62dec.
Proof. vm_refl. Qed.
Lemma D_62dec : decode_any W_62dec = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62df0 : bv 32 := 0x00050413.
Lemma F_62df0 : fetch_word Plain.M.loaded_segments (0x62e48 : word) = Some W_62df0.
Proof. vm_refl. Qed.
Lemma D_62df0 : decode_any W_62df0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62df4 : bv 32 := 0x06058063.
Lemma F_62df4 : fetch_word Plain.M.loaded_segments (0x62e4c : word) = Some W_62df4.
Proof. vm_refl. Qed.
Lemma D_62df4 : decode_any W_62df4 = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62df8 : bv 32 := 0x00058493.
Lemma F_62df8 : fetch_word Plain.M.loaded_segments (0x62e50 : word) = Some W_62df8.
Proof. vm_refl. Qed.
Lemma D_62df8 : decode_any W_62df8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62dfc : bv 32 := 0x18858e63.
Lemma F_62dfc : fetch_word Plain.M.loaded_segments (0x62e54 : word) = Some W_62dfc.
Proof. vm_refl. Qed.
Lemma D_62dfc : decode_any W_62dfc = Some (Branch BC_EQ 11 8 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e00 : bv 32 := 0x0044a503.
Lemma F_62e00 : fetch_word Plain.M.loaded_segments (0x62e58 : word) = Some W_62e00.
Proof. vm_refl. Qed.
Lemma D_62e00 : decode_any W_62e00 = Some (Load SZ4 true 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e04 : bv 32 := 0x0104a583.
Lemma F_62e04 : fetch_word Plain.M.loaded_segments (0x62e5c : word) = Some W_62e04.
Proof. vm_refl. Qed.
Lemma D_62e04 : decode_any W_62e04 = Some (Load SZ4 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e08 : bv 32 := 0x02a58533.
Lemma F_62e08 : fetch_word Plain.M.loaded_segments (0x62e60 : word) = Some W_62e08.
Proof. vm_refl. Qed.
Lemma D_62e08 : decode_any W_62e08 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e0c : bv 32 := 0x0025191b.
Lemma F_62e0c : fetch_word Plain.M.loaded_segments (0x62e64 : word) = Some W_62e0c.
Proof. vm_refl. Qed.
Lemma D_62e0c : decode_any W_62e0c = Some (ShiftImm32 ALU_SLL 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e10 : bv 32 := 0x08040463.
Lemma F_62e10 : fetch_word Plain.M.loaded_segments (0x62e68 : word) = Some W_62e10.
Proof. vm_refl. Qed.
Lemma D_62e10 : decode_any W_62e10 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e4c : bv 32 := 0x00000613.
Lemma F_62e4c : fetch_word Plain.M.loaded_segments (0x62ea4 : word) = Some W_62e4c.
Proof. vm_refl. Qed.
Lemma D_62e4c : decode_any W_62e4c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e50 : bv 32 := 0x02c0006f.
Lemma F_62e50 : fetch_word Plain.M.loaded_segments (0x62ea8 : word) = Some W_62e50.
Proof. vm_refl. Qed.
Lemma D_62e50 : decode_any W_62e50 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e7c : bv 32 := 0x02813083.
Lemma F_62e7c : fetch_word Plain.M.loaded_segments (0x62ed4 : word) = Some W_62e7c.
Proof. vm_refl. Qed.
Lemma D_62e7c : decode_any W_62e7c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e80 : bv 32 := 0x02013403.
Lemma F_62e80 : fetch_word Plain.M.loaded_segments (0x62ed8 : word) = Some W_62e80.
Proof. vm_refl. Qed.
Lemma D_62e80 : decode_any W_62e80 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e84 : bv 32 := 0x01813483.
Lemma F_62e84 : fetch_word Plain.M.loaded_segments (0x62edc : word) = Some W_62e84.
Proof. vm_refl. Qed.
Lemma D_62e84 : decode_any W_62e84 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e88 : bv 32 := 0x01013903.
Lemma F_62e88 : fetch_word Plain.M.loaded_segments (0x62ee0 : word) = Some W_62e88.
Proof. vm_refl. Qed.
Lemma D_62e88 : decode_any W_62e88 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e8c : bv 32 := 0x00813983.
Lemma F_62e8c : fetch_word Plain.M.loaded_segments (0x62ee4 : word) = Some W_62e8c.
Proof. vm_refl. Qed.
Lemma D_62e8c : decode_any W_62e8c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e90 : bv 32 := 0x03010113.
Lemma F_62e90 : fetch_word Plain.M.loaded_segments (0x62ee8 : word) = Some W_62e90.
Proof. vm_refl. Qed.
Lemma D_62e90 : decode_any W_62e90 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e94 : bv 32 := 0xfb9f906f.
Lemma F_62e94 : fetch_word Plain.M.loaded_segments (0x62eec : word) = Some W_62e94.
Proof. vm_refl. Qed.
Lemma D_62e94 : decode_any W_62e94 = Some (Jal 0 2072504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e98 : bv 32 := 0x00048513.
Lemma F_62e98 : fetch_word Plain.M.loaded_segments (0x62ef0 : word) = Some W_62e98.
Proof. vm_refl. Qed.
Lemma D_62e98 : decode_any W_62e98 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62e9c : bv 32 := 0x8e5ff0ef.
Lemma F_62e9c : fetch_word Plain.M.loaded_segments (0x62ef4 : word) = Some W_62e9c.
Proof. vm_refl. Qed.
Lemma D_62e9c : decode_any W_62e9c = Some (Jal 1 2095332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ea0 : bv 32 := 0x04050263.
Lemma F_62ea0 : fetch_word Plain.M.loaded_segments (0x62ef8 : word) = Some W_62ea0.
Proof. vm_refl. Qed.
Lemma D_62ea0 : decode_any W_62ea0 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ea4 : bv 32 := 0x00050413.
Lemma F_62ea4 : fetch_word Plain.M.loaded_segments (0x62efc : word) = Some W_62ea4.
Proof. vm_refl. Qed.
Lemma D_62ea4 : decode_any W_62ea4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ea8 : bv 32 := 0x00456583.
Lemma F_62ea8 : fetch_word Plain.M.loaded_segments (0x62f00 : word) = Some W_62ea8.
Proof. vm_refl. Qed.
Lemma D_62ea8 : decode_any W_62ea8 = Some (Load SZ4 false 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62eac : bv 32 := 0x01056603.
Lemma F_62eac : fetch_word Plain.M.loaded_segments (0x62f04 : word) = Some W_62eac.
Proof. vm_refl. Qed.
Lemma D_62eac : decode_any W_62eac = Some (Load SZ4 false 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62eb0 : bv 32 := 0x03853503.
Lemma F_62eb0 : fetch_word Plain.M.loaded_segments (0x62f08 : word) = Some W_62eb0.
Proof. vm_refl. Qed.
Lemma D_62eb0 : decode_any W_62eb0 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62eb4 : bv 32 := 0x02b60633.
Lemma F_62eb4 : fetch_word Plain.M.loaded_segments (0x62f0c : word) = Some W_62eb4.
Proof. vm_refl. Qed.
Lemma D_62eb4 : decode_any W_62eb4 = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62eb8 : bv 32 := 0x00261613.
Lemma F_62eb8 : fetch_word Plain.M.loaded_segments (0x62f10 : word) = Some W_62eb8.
Proof. vm_refl. Qed.
Lemma D_62eb8 : decode_any W_62eb8 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ebc : bv 32 := 0x00000593.
Lemma F_62ebc : fetch_word Plain.M.loaded_segments (0x62f14 : word) = Some W_62ebc.
Proof. vm_refl. Qed.
Lemma D_62ebc : decode_any W_62ebc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ec0 : bv 32 := 0x53c830ef.
Lemma F_62ec0 : fetch_word Plain.M.loaded_segments (0x62f18 : word) = Some W_62ec0.
Proof. vm_refl. Qed.
Lemma D_62ec0 : decode_any W_62ec0 = Some (Jal 1 537916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ec4 : bv 32 := 0x0c40006f.
Lemma F_62ec4 : fetch_word Plain.M.loaded_segments (0x62f1c : word) = Some W_62ec4.
Proof. vm_refl. Qed.
Lemma D_62ec4 : decode_any W_62ec4 = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ee4 : bv 32 := 0x0008b517.
Lemma F_62ee4 : fetch_word Plain.M.loaded_segments (0x62f3c : word) = Some W_62ee4.
Proof. vm_refl. Qed.
Lemma D_62ee4 : decode_any W_62ee4 = Some (Auipc 10 139, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ee8 : bv 32 := 0x63453983.
Lemma F_62ee8 : fetch_word Plain.M.loaded_segments (0x62f40 : word) = Some W_62ee8.
Proof. vm_refl. Qed.
Lemma D_62ee8 : decode_any W_62ee8 = Some (Load SZ8 true 19 10 1588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62eec : bv 32 := 0x0009a503.
Lemma F_62eec : fetch_word Plain.M.loaded_segments (0x62f44 : word) = Some W_62eec.
Proof. vm_refl. Qed.
Lemma D_62eec : decode_any W_62eec = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ef0 : bv 32 := 0x00600593.
Lemma F_62ef0 : fetch_word Plain.M.loaded_segments (0x62f48 : word) = Some W_62ef0.
Proof. vm_refl. Qed.
Lemma D_62ef0 : decode_any W_62ef0 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ef4 : bv 32 := 0x04b55263.
Lemma F_62ef4 : fetch_word Plain.M.loaded_segments (0x62f4c : word) = Some W_62ef4.
Proof. vm_refl. Qed.
Lemma D_62ef4 : decode_any W_62ef4 = Some (Branch BC_GE 10 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62ef8 : bv 32 := 0xfffaf517.
Lemma F_62ef8 : fetch_word Plain.M.loaded_segments (0x62f50 : word) = Some W_62ef8.
Proof. vm_refl. Qed.
Lemma D_62ef8 : decode_any W_62ef8 = Some (Auipc 10 1048495, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62efc : bv 32 := 0xfffb5597.
Lemma F_62efc : fetch_word Plain.M.loaded_segments (0x62f54 : word) = Some W_62efc.
Proof. vm_refl. Qed.
Lemma D_62efc : decode_any W_62efc = Some (Auipc 11 1048501, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f00 : bv 32 := 0x11250513.
Lemma F_62f00 : fetch_word Plain.M.loaded_segments (0x62f58 : word) = Some W_62f00.
Proof. vm_refl. Qed.
Lemma D_62f00 : decode_any W_62f00 = Some (OpImm ALU_ADD 10 10 274, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f04 : bv 32 := 0xad958593.
Lemma F_62f04 : fetch_word Plain.M.loaded_segments (0x62f5c : word) = Some W_62f04.
Proof. vm_refl. Qed.
Lemma D_62f04 : decode_any W_62f04 = Some (OpImm ALU_ADD 11 11 2777, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f08 : bv 32 := 0x00000613.
Lemma F_62f08 : fetch_word Plain.M.loaded_segments (0x62f60 : word) = Some W_62f08.
Proof. vm_refl. Qed.
Lemma D_62f08 : decode_any W_62f08 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f0c : bv 32 := 0xf41f90ef.
Lemma F_62f0c : fetch_word Plain.M.loaded_segments (0x62f64 : word) = Some W_62f0c.
Proof. vm_refl. Qed.
Lemma D_62f0c : decode_any W_62f0c = Some (Jal 1 2072384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f10 : bv 32 := 0x00050413.
Lemma F_62f10 : fetch_word Plain.M.loaded_segments (0x62f68 : word) = Some W_62f10.
Proof. vm_refl. Qed.
Lemma D_62f10 : decode_any W_62f10 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f14 : bv 32 := 0x06051a63.
Lemma F_62f14 : fetch_word Plain.M.loaded_segments (0x62f6c : word) = Some W_62f14.
Proof. vm_refl. Qed.
Lemma D_62f14 : decode_any W_62f14 = Some (Branch BC_NE 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f18 : bv 32 := 0x0009a503.
Lemma F_62f18 : fetch_word Plain.M.loaded_segments (0x62f70 : word) = Some W_62f18.
Proof. vm_refl. Qed.
Lemma D_62f18 : decode_any W_62f18 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f1c : bv 32 := 0x00500593.
Lemma F_62f1c : fetch_word Plain.M.loaded_segments (0x62f74 : word) = Some W_62f1c.
Proof. vm_refl. Qed.
Lemma D_62f1c : decode_any W_62f1c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f20 : bv 32 := 0x00a5cc63.
Lemma F_62f20 : fetch_word Plain.M.loaded_segments (0x62f78 : word) = Some W_62f20.
Proof. vm_refl. Qed.
Lemma D_62f20 : decode_any W_62f20 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f24 : bv 32 := 0xfffaf517.
Lemma F_62f24 : fetch_word Plain.M.loaded_segments (0x62f7c : word) = Some W_62f24.
Proof. vm_refl. Qed.
Lemma D_62f24 : decode_any W_62f24 = Some (Auipc 10 1048495, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f28 : bv 32 := 0xfffb4597.
Lemma F_62f28 : fetch_word Plain.M.loaded_segments (0x62f80 : word) = Some W_62f28.
Proof. vm_refl. Qed.
Lemma D_62f28 : decode_any W_62f28 = Some (Auipc 11 1048500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f2c : bv 32 := 0x0e650513.
Lemma F_62f2c : fetch_word Plain.M.loaded_segments (0x62f84 : word) = Some W_62f2c.
Proof. vm_refl. Qed.
Lemma D_62f2c : decode_any W_62f2c = Some (OpImm ALU_ADD 10 10 230, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f30 : bv 32 := 0x52758593.
Lemma F_62f30 : fetch_word Plain.M.loaded_segments (0x62f88 : word) = Some W_62f30.
Proof. vm_refl. Qed.
Lemma D_62f30 : decode_any W_62f30 = Some (OpImm ALU_ADD 11 11 1319, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f34 : bv 32 := 0xf19ff06f.
Lemma F_62f34 : fetch_word Plain.M.loaded_segments (0x62f8c : word) = Some W_62f34.
Proof. vm_refl. Qed.
Lemma D_62f34 : decode_any W_62f34 = Some (Jal 0 2096920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f88 : bv 32 := 0x03843503.
Lemma F_62f88 : fetch_word Plain.M.loaded_segments (0x62fe0 : word) = Some W_62f88.
Proof. vm_refl. Qed.
Lemma D_62f88 : decode_any W_62f88 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f8c : bv 32 := 0x0384b583.
Lemma F_62f8c : fetch_word Plain.M.loaded_segments (0x62fe4 : word) = Some W_62f8c.
Proof. vm_refl. Qed.
Lemma D_62f8c : decode_any W_62f8c = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f90 : bv 32 := 0x00090613.
Lemma F_62f90 : fetch_word Plain.M.loaded_segments (0x62fe8 : word) = Some W_62f90.
Proof. vm_refl. Qed.
Lemma D_62f90 : decode_any W_62f90 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f94 : bv 32 := 0x6e9820ef.
Lemma F_62f94 : fetch_word Plain.M.loaded_segments (0x62fec : word) = Some W_62f94.
Proof. vm_refl. Qed.
Lemma D_62f94 : decode_any W_62f94 = Some (Jal 1 536296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f98 : bv 32 := 0x00040513.
Lemma F_62f98 : fetch_word Plain.M.loaded_segments (0x62ff0 : word) = Some W_62f98.
Proof. vm_refl. Qed.
Lemma D_62f98 : decode_any W_62f98 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62f9c : bv 32 := 0x02813083.
Lemma F_62f9c : fetch_word Plain.M.loaded_segments (0x62ff4 : word) = Some W_62f9c.
Proof. vm_refl. Qed.
Lemma D_62f9c : decode_any W_62f9c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62fa0 : bv 32 := 0x02013403.
Lemma F_62fa0 : fetch_word Plain.M.loaded_segments (0x62ff8 : word) = Some W_62fa0.
Proof. vm_refl. Qed.
Lemma D_62fa0 : decode_any W_62fa0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62fa4 : bv 32 := 0x01813483.
Lemma F_62fa4 : fetch_word Plain.M.loaded_segments (0x62ffc : word) = Some W_62fa4.
Proof. vm_refl. Qed.
Lemma D_62fa4 : decode_any W_62fa4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62fa8 : bv 32 := 0x01013903.
Lemma F_62fa8 : fetch_word Plain.M.loaded_segments (0x63000 : word) = Some W_62fa8.
Proof. vm_refl. Qed.
Lemma D_62fa8 : decode_any W_62fa8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62fac : bv 32 := 0x00813983.
Lemma F_62fac : fetch_word Plain.M.loaded_segments (0x63004 : word) = Some W_62fac.
Proof. vm_refl. Qed.
Lemma D_62fac : decode_any W_62fac = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62fb0 : bv 32 := 0x03010113.
Lemma F_62fb0 : fetch_word Plain.M.loaded_segments (0x63008 : word) = Some W_62fb0.
Proof. vm_refl. Qed.
Lemma D_62fb0 : decode_any W_62fb0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_62fb4 : bv 32 := 0x00008067.
Lemma F_62fb4 : fetch_word Plain.M.loaded_segments (0x6300c : word) = Some W_62fb4.
Proof. vm_refl. Qed.
Lemma D_62fb4 : decode_any W_62fb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

