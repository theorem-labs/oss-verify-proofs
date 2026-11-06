(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6d428 : bv 32 := 0xfd010113.
Lemma F_6d428 : fetch_word Plain.M.loaded_segments (0x6d480 : word) = Some W_6d428.
Proof. vm_refl. Qed.
Lemma D_6d428 : decode_any W_6d428 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d42c : bv 32 := 0x02113423.
Lemma F_6d42c : fetch_word Plain.M.loaded_segments (0x6d484 : word) = Some W_6d42c.
Proof. vm_refl. Qed.
Lemma D_6d42c : decode_any W_6d42c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d430 : bv 32 := 0x02813023.
Lemma F_6d430 : fetch_word Plain.M.loaded_segments (0x6d488 : word) = Some W_6d430.
Proof. vm_refl. Qed.
Lemma D_6d430 : decode_any W_6d430 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d434 : bv 32 := 0x00913c23.
Lemma F_6d434 : fetch_word Plain.M.loaded_segments (0x6d48c : word) = Some W_6d434.
Proof. vm_refl. Qed.
Lemma D_6d434 : decode_any W_6d434 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d438 : bv 32 := 0x01213823.
Lemma F_6d438 : fetch_word Plain.M.loaded_segments (0x6d490 : word) = Some W_6d438.
Proof. vm_refl. Qed.
Lemma D_6d438 : decode_any W_6d438 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d43c : bv 32 := 0x01313423.
Lemma F_6d43c : fetch_word Plain.M.loaded_segments (0x6d494 : word) = Some W_6d43c.
Proof. vm_refl. Qed.
Lemma D_6d43c : decode_any W_6d43c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d440 : bv 32 := 0x00050413.
Lemma F_6d440 : fetch_word Plain.M.loaded_segments (0x6d498 : word) = Some W_6d440.
Proof. vm_refl. Qed.
Lemma D_6d440 : decode_any W_6d440 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d444 : bv 32 := 0x06058063.
Lemma F_6d444 : fetch_word Plain.M.loaded_segments (0x6d49c : word) = Some W_6d444.
Proof. vm_refl. Qed.
Lemma D_6d444 : decode_any W_6d444 = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d448 : bv 32 := 0x00058493.
Lemma F_6d448 : fetch_word Plain.M.loaded_segments (0x6d4a0 : word) = Some W_6d448.
Proof. vm_refl. Qed.
Lemma D_6d448 : decode_any W_6d448 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d44c : bv 32 := 0x18858e63.
Lemma F_6d44c : fetch_word Plain.M.loaded_segments (0x6d4a4 : word) = Some W_6d44c.
Proof. vm_refl. Qed.
Lemma D_6d44c : decode_any W_6d44c = Some (Branch BC_EQ 11 8 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e8 : bv 32 := 0x00040513.
Lemma F_6d5e8 : fetch_word Plain.M.loaded_segments (0x6d640 : word) = Some W_6d5e8.
Proof. vm_refl. Qed.
Lemma D_6d5e8 : decode_any W_6d5e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5ec : bv 32 := 0x02813083.
Lemma F_6d5ec : fetch_word Plain.M.loaded_segments (0x6d644 : word) = Some W_6d5ec.
Proof. vm_refl. Qed.
Lemma D_6d5ec : decode_any W_6d5ec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f0 : bv 32 := 0x02013403.
Lemma F_6d5f0 : fetch_word Plain.M.loaded_segments (0x6d648 : word) = Some W_6d5f0.
Proof. vm_refl. Qed.
Lemma D_6d5f0 : decode_any W_6d5f0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f4 : bv 32 := 0x01813483.
Lemma F_6d5f4 : fetch_word Plain.M.loaded_segments (0x6d64c : word) = Some W_6d5f4.
Proof. vm_refl. Qed.
Lemma D_6d5f4 : decode_any W_6d5f4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f8 : bv 32 := 0x01013903.
Lemma F_6d5f8 : fetch_word Plain.M.loaded_segments (0x6d650 : word) = Some W_6d5f8.
Proof. vm_refl. Qed.
Lemma D_6d5f8 : decode_any W_6d5f8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5fc : bv 32 := 0x00813983.
Lemma F_6d5fc : fetch_word Plain.M.loaded_segments (0x6d654 : word) = Some W_6d5fc.
Proof. vm_refl. Qed.
Lemma D_6d5fc : decode_any W_6d5fc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d600 : bv 32 := 0x03010113.
Lemma F_6d600 : fetch_word Plain.M.loaded_segments (0x6d658 : word) = Some W_6d600.
Proof. vm_refl. Qed.
Lemma D_6d600 : decode_any W_6d600 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d604 : bv 32 := 0x00008067.
Lemma F_6d604 : fetch_word Plain.M.loaded_segments (0x6d65c : word) = Some W_6d604.
Proof. vm_refl. Qed.
Lemma D_6d604 : decode_any W_6d604 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_6d608 : bv 32 := 0x00050663.
Lemma F_6d608 : fetch_word Plain.M.loaded_segments (0x6d660 : word) = Some W_6d608.
Proof. vm_refl. Qed.
Lemma D_6d608 : decode_any W_6d608 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d60c : bv 32 := 0x00452503.
Lemma F_6d60c : fetch_word Plain.M.loaded_segments (0x6d664 : word) = Some W_6d60c.
Proof. vm_refl. Qed.
Lemma D_6d60c : decode_any W_6d60c = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d610 : bv 32 := 0x00008067.
Lemma F_6d610 : fetch_word Plain.M.loaded_segments (0x6d668 : word) = Some W_6d610.
Proof. vm_refl. Qed.
Lemma D_6d610 : decode_any W_6d610 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d928 : bv 32 := 0x00050663.
Lemma F_6d928 : fetch_word Plain.M.loaded_segments (0x6d980 : word) = Some W_6d928.
Proof. vm_refl. Qed.
Lemma D_6d928 : decode_any W_6d928 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d92c : bv 32 := 0x00852503.
Lemma F_6d92c : fetch_word Plain.M.loaded_segments (0x6d984 : word) = Some W_6d92c.
Proof. vm_refl. Qed.
Lemma D_6d92c : decode_any W_6d92c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d930 : bv 32 := 0x00008067.
Lemma F_6d930 : fetch_word Plain.M.loaded_segments (0x6d988 : word) = Some W_6d930.
Proof. vm_refl. Qed.
Lemma D_6d930 : decode_any W_6d930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dd50 : bv 32 := 0x00050663.
Lemma F_6dd50 : fetch_word Plain.M.loaded_segments (0x6dda8 : word) = Some W_6dd50.
Proof. vm_refl. Qed.
Lemma D_6dd50 : decode_any W_6dd50 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dd54 : bv 32 := 0x00052503.
Lemma F_6dd54 : fetch_word Plain.M.loaded_segments (0x6ddac : word) = Some W_6dd54.
Proof. vm_refl. Qed.
Lemma D_6dd54 : decode_any W_6dd54 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dd58 : bv 32 := 0x00008067.
Lemma F_6dd58 : fetch_word Plain.M.loaded_segments (0x6ddb0 : word) = Some W_6dd58.
Proof. vm_refl. Qed.
Lemma D_6dd58 : decode_any W_6dd58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dbc : bv 32 := 0xfd010113.
Lemma F_78dbc : fetch_word Plain.M.loaded_segments (0x78e14 : word) = Some W_78dbc.
Proof. vm_refl. Qed.
Lemma D_78dbc : decode_any W_78dbc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dc0 : bv 32 := 0x02113423.
Lemma F_78dc0 : fetch_word Plain.M.loaded_segments (0x78e18 : word) = Some W_78dc0.
Proof. vm_refl. Qed.
Lemma D_78dc0 : decode_any W_78dc0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dc4 : bv 32 := 0x02813023.
Lemma F_78dc4 : fetch_word Plain.M.loaded_segments (0x78e1c : word) = Some W_78dc4.
Proof. vm_refl. Qed.
Lemma D_78dc4 : decode_any W_78dc4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dc8 : bv 32 := 0x00913c23.
Lemma F_78dc8 : fetch_word Plain.M.loaded_segments (0x78e20 : word) = Some W_78dc8.
Proof. vm_refl. Qed.
Lemma D_78dc8 : decode_any W_78dc8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dcc : bv 32 := 0x01213823.
Lemma F_78dcc : fetch_word Plain.M.loaded_segments (0x78e24 : word) = Some W_78dcc.
Proof. vm_refl. Qed.
Lemma D_78dcc : decode_any W_78dcc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dd0 : bv 32 := 0x01313423.
Lemma F_78dd0 : fetch_word Plain.M.loaded_segments (0x78e28 : word) = Some W_78dd0.
Proof. vm_refl. Qed.
Lemma D_78dd0 : decode_any W_78dd0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dd4 : bv 32 := 0x00050413.
Lemma F_78dd4 : fetch_word Plain.M.loaded_segments (0x78e2c : word) = Some W_78dd4.
Proof. vm_refl. Qed.
Lemma D_78dd4 : decode_any W_78dd4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dd8 : bv 32 := 0x06058e63.
Lemma F_78dd8 : fetch_word Plain.M.loaded_segments (0x78e30 : word) = Some W_78dd8.
Proof. vm_refl. Qed.
Lemma D_78dd8 : decode_any W_78dd8 = Some (Branch BC_EQ 11 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ddc : bv 32 := 0x00060493.
Lemma F_78ddc : fetch_word Plain.M.loaded_segments (0x78e34 : word) = Some W_78ddc.
Proof. vm_refl. Qed.
Lemma D_78ddc : decode_any W_78ddc = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78de0 : bv 32 := 0x08060e63.
Lemma F_78de0 : fetch_word Plain.M.loaded_segments (0x78e38 : word) = Some W_78de0.
Proof. vm_refl. Qed.
Lemma D_78de0 : decode_any W_78de0 = Some (Branch BC_EQ 12 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78de4 : bv 32 := 0x0c940063.
Lemma F_78de4 : fetch_word Plain.M.loaded_segments (0x78e3c : word) = Some W_78de4.
Proof. vm_refl. Qed.
Lemma D_78de4 : decode_any W_78de4 = Some (Branch BC_EQ 8 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78de8 : bv 32 := 0x00058913.
Lemma F_78de8 : fetch_word Plain.M.loaded_segments (0x78e40 : word) = Some W_78de8.
Proof. vm_refl. Qed.
Lemma D_78de8 : decode_any W_78de8 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dec : bv 32 := 0x00058513.
Lemma F_78dec : fetch_word Plain.M.loaded_segments (0x78e44 : word) = Some W_78dec.
Proof. vm_refl. Qed.
Lemma D_78dec : decode_any W_78dec = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78df0 : bv 32 := 0xb39f40ef.
Lemma F_78df0 : fetch_word Plain.M.loaded_segments (0x78e48 : word) = Some W_78df0.
Proof. vm_refl. Qed.
Lemma D_78df0 : decode_any W_78df0 = Some (Jal 1 2050872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78df4 : bv 32 := 0x00050993.
Lemma F_78df4 : fetch_word Plain.M.loaded_segments (0x78e4c : word) = Some W_78df4.
Proof. vm_refl. Qed.
Lemma D_78df4 : decode_any W_78df4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78df8 : bv 32 := 0x00048513.
Lemma F_78df8 : fetch_word Plain.M.loaded_segments (0x78e50 : word) = Some W_78df8.
Proof. vm_refl. Qed.
Lemma D_78df8 : decode_any W_78df8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dfc : bv 32 := 0xb2df40ef.
Lemma F_78dfc : fetch_word Plain.M.loaded_segments (0x78e54 : word) = Some W_78dfc.
Proof. vm_refl. Qed.
Lemma D_78dfc : decode_any W_78dfc = Some (Jal 1 2050860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e00 : bv 32 := 0x0ca99663.
Lemma F_78e00 : fetch_word Plain.M.loaded_segments (0x78e58 : word) = Some W_78e00.
Proof. vm_refl. Qed.
Lemma D_78e00 : decode_any W_78e00 = Some (Branch BC_NE 19 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e04 : bv 32 := 0x00040513.
Lemma F_78e04 : fetch_word Plain.M.loaded_segments (0x78e5c : word) = Some W_78e04.
Proof. vm_refl. Qed.
Lemma D_78e04 : decode_any W_78e04 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e08 : bv 32 := 0x00090593.
Lemma F_78e08 : fetch_word Plain.M.loaded_segments (0x78e60 : word) = Some W_78e08.
Proof. vm_refl. Qed.
Lemma D_78e08 : decode_any W_78e08 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e0c : bv 32 := 0xe1cf40ef.
Lemma F_78e0c : fetch_word Plain.M.loaded_segments (0x78e64 : word) = Some W_78e0c.
Proof. vm_refl. Qed.
Lemma D_78e0c : decode_any W_78e0c = Some (Jal 1 2049564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e10 : bv 32 := 0x10050063.
Lemma F_78e10 : fetch_word Plain.M.loaded_segments (0x78e68 : word) = Some W_78e10.
Proof. vm_refl. Qed.
Lemma D_78e10 : decode_any W_78e10 = Some (Branch BC_EQ 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e14 : bv 32 := 0x00050413.
Lemma F_78e14 : fetch_word Plain.M.loaded_segments (0x78e6c : word) = Some W_78e14.
Proof. vm_refl. Qed.
Lemma D_78e14 : decode_any W_78e14 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e18 : bv 32 := 0xf39f40ef.
Lemma F_78e18 : fetch_word Plain.M.loaded_segments (0x78e70 : word) = Some W_78e18.
Proof. vm_refl. Qed.
Lemma D_78e18 : decode_any W_78e18 = Some (Jal 1 2051896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e1c : bv 32 := 0x00050913.
Lemma F_78e1c : fetch_word Plain.M.loaded_segments (0x78e74 : word) = Some W_78e1c.
Proof. vm_refl. Qed.
Lemma D_78e1c : decode_any W_78e1c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e20 : bv 32 := 0x00040513.
Lemma F_78e20 : fetch_word Plain.M.loaded_segments (0x78e78 : word) = Some W_78e20.
Proof. vm_refl. Qed.
Lemma D_78e20 : decode_any W_78e20 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e24 : bv 32 := 0xfe4f40ef.
Lemma F_78e24 : fetch_word Plain.M.loaded_segments (0x78e7c : word) = Some W_78e24.
Proof. vm_refl. Qed.
Lemma D_78e24 : decode_any W_78e24 = Some (Jal 1 2050020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e28 : bv 32 := 0x00050713.
Lemma F_78e28 : fetch_word Plain.M.loaded_segments (0x78e80 : word) = Some W_78e28.
Proof. vm_refl. Qed.
Lemma D_78e28 : decode_any W_78e28 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e2c : bv 32 := 0x00e00793.
Lemma F_78e2c : fetch_word Plain.M.loaded_segments (0x78e84 : word) = Some W_78e2c.
Proof. vm_refl. Qed.
Lemma D_78e2c : decode_any W_78e2c = Some (OpImm ALU_ADD 15 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e30 : bv 32 := 0x00013023.
Lemma F_78e30 : fetch_word Plain.M.loaded_segments (0x78e88 : word) = Some W_78e30.
Proof. vm_refl. Qed.
Lemma D_78e30 : decode_any W_78e30 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e34 : bv 32 := 0x00040513.
Lemma F_78e34 : fetch_word Plain.M.loaded_segments (0x78e8c : word) = Some W_78e34.
Proof. vm_refl. Qed.
Lemma D_78e34 : decode_any W_78e34 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e38 : bv 32 := 0x00000593.
Lemma F_78e38 : fetch_word Plain.M.loaded_segments (0x78e90 : word) = Some W_78e38.
Proof. vm_refl. Qed.
Lemma D_78e38 : decode_any W_78e38 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e3c : bv 32 := 0x00000613.
Lemma F_78e3c : fetch_word Plain.M.loaded_segments (0x78e94 : word) = Some W_78e3c.
Proof. vm_refl. Qed.
Lemma D_78e3c : decode_any W_78e3c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e40 : bv 32 := 0x00090693.
Lemma F_78e40 : fetch_word Plain.M.loaded_segments (0x78e98 : word) = Some W_78e40.
Proof. vm_refl. Qed.
Lemma D_78e40 : decode_any W_78e40 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e44 : bv 32 := 0x00048813.
Lemma F_78e44 : fetch_word Plain.M.loaded_segments (0x78e9c : word) = Some W_78e44.
Proof. vm_refl. Qed.
Lemma D_78e44 : decode_any W_78e44 = Some (OpImm ALU_ADD 16 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e48 : bv 32 := 0x00000893.
Lemma F_78e48 : fetch_word Plain.M.loaded_segments (0x78ea0 : word) = Some W_78e48.
Proof. vm_refl. Qed.
Lemma D_78e48 : decode_any W_78e48 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e4c : bv 32 := 0x109000ef.
Lemma F_78e4c : fetch_word Plain.M.loaded_segments (0x78ea4 : word) = Some W_78e4c.
Proof. vm_refl. Qed.
Lemma D_78e4c : decode_any W_78e4c = Some (Jal 1 2312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e50 : bv 32 := 0x0f00006f.
Lemma F_78e50 : fetch_word Plain.M.loaded_segments (0x78ea8 : word) = Some W_78e50.
Proof. vm_refl. Qed.
Lemma D_78e50 : decode_any W_78e50 = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f40 : bv 32 := 0x00040513.
Lemma F_78f40 : fetch_word Plain.M.loaded_segments (0x78f98 : word) = Some W_78f40.
Proof. vm_refl. Qed.
Lemma D_78f40 : decode_any W_78f40 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f44 : bv 32 := 0x02813083.
Lemma F_78f44 : fetch_word Plain.M.loaded_segments (0x78f9c : word) = Some W_78f44.
Proof. vm_refl. Qed.
Lemma D_78f44 : decode_any W_78f44 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f48 : bv 32 := 0x02013403.
Lemma F_78f48 : fetch_word Plain.M.loaded_segments (0x78fa0 : word) = Some W_78f48.
Proof. vm_refl. Qed.
Lemma D_78f48 : decode_any W_78f48 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f4c : bv 32 := 0x01813483.
Lemma F_78f4c : fetch_word Plain.M.loaded_segments (0x78fa4 : word) = Some W_78f4c.
Proof. vm_refl. Qed.
Lemma D_78f4c : decode_any W_78f4c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f50 : bv 32 := 0x01013903.
Lemma F_78f50 : fetch_word Plain.M.loaded_segments (0x78fa8 : word) = Some W_78f50.
Proof. vm_refl. Qed.
Lemma D_78f50 : decode_any W_78f50 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f54 : bv 32 := 0x00813983.
Lemma F_78f54 : fetch_word Plain.M.loaded_segments (0x78fac : word) = Some W_78f54.
Proof. vm_refl. Qed.
Lemma D_78f54 : decode_any W_78f54 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f58 : bv 32 := 0x03010113.
Lemma F_78f58 : fetch_word Plain.M.loaded_segments (0x78fb0 : word) = Some W_78f58.
Proof. vm_refl. Qed.
Lemma D_78f58 : decode_any W_78f58 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f5c : bv 32 := 0x00008067.
Lemma F_78f5c : fetch_word Plain.M.loaded_segments (0x78fb4 : word) = Some W_78f5c.
Proof. vm_refl. Qed.
Lemma D_78f5c : decode_any W_78f5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
