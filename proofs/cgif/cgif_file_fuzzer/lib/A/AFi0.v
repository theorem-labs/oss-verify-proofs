(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0f YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0m AF0x AFl0 AFhy AFhz.
Import ListNotations. Open Scope Z_scope.
Definition hMS1 : nat := 133.
Definition hCL2 : nat := 139.
Definition hMS2 : nat := 144.
Definition R_scr2 : YP09.region := YP09.mkRegion (Some 2%nat) (- ASTACK) (- 2272) (- ASTACK) (- 2272) [].
Definition rs_D : smem := match ss_mem SS_PD with r0 :: r1 :: rest => r0 :: trim_lo r1 (-2272) :: rest | l => l end.
Definition SS_2 : sstate := Eval vm_compute in addreg R_scr2 (ss_after_call SS_PD rs_D hD1 0x318cc).
Definition SS_M0 : sstate := Eval vm_compute in runto 0x318f4 SS_2.
Definition SS_M : sstate := Eval vm_compute in pin SS_M0 10%bv (SOff aSK 0).
Definition SS_N0 : sstate := Eval vm_compute in runto 0x319c4 SS_M.
Definition SS_N : sstate := Eval vm_compute in pin SS_N0 22%bv (SOff aN8D 0).
Definition SS_O0 : sstate := Eval vm_compute in runto 0x53a88 SS_N.
Definition SS_O : sstate := Eval vm_compute in pin (pin SS_O0 8%bv (SOff aCNT8 0)) 10%bv (SOff aSU 0).
Definition SS_MS1 : sstate := Eval vm_compute in runto 0x97698 SS_O.
Definition CLOB_MS : list (bv 5) := [11; 12; 13; 14; 15; 16]%bv.
Definition SS_Q : sstate := Eval vm_compute in ss_after_stretch SS_MS1 (ss_mem SS_MS1) hMS1 CLOB_MS 0x319d8.
Definition SS_Qe : sstate := Eval vm_compute in arm BC_EQ true (SOff 10 0) (SOff aN8D 0) SS_Q.
Definition SS_Qo : sstate := Eval vm_compute in arm BC_EQ false (SOff 10 0) (SOff aN8D 0) SS_Q.
Definition R_pb : YP09.region := YP09.mkRegion (Some aPB) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 250))].
Definition SS_P0 : sstate := Eval vm_compute in runto 0x31a68 SS_Qo.
Definition SS_Po : sstate := Eval vm_compute in addreg R_pb (pin SS_P0 10%bv (SOff aPB 0)).
Definition CLOB_CL2 : list (bv 5) := [12; 13; 14; 15; 16]%bv.
Definition st_R (ss : sstate) : sstate := runto 0x31ac4 ss.
Definition st_S (lo : bool) (ss : sstate) : sstate := noconds (pin (forget (runto 0x31bb0 (arm BC_LTU (negb lo) (SLit 512) (SOff aND 0) ss)) hCL2 CLOB_CL2) 11%bv (SOff aCL 0)).
Definition st_T (ss : sstate) : sstate := pin (runto 0x31bb8 ss) 10%bv (SOff aSSLOT 0).
Definition st_V (ss : sstate) : sstate := runto 0x31be0 ss.
Definition st_W (small : bool) (ss : sstate) : sstate := noconds (pin (runto 0x31be8 (arm BC_LTU small (SOff 10 0) (SLit 4096) ss)) 12%bv (SOff aFIL 0)).
Definition st_X (ss : sstate) : sstate := let m := runto 0x97698 ss in ss_after_stretch m (ss_mem m) hMS2 CLOB_MS 0x31c00.
Definition st_Y (ss : sstate) : sstate := arm BC_EQ false (SOff aU (-16)) (SOff aK 0) (runto 0x31c28 ss).
Definition st_Z (ss : sstate) : sstate := arm BC_LTU false (SOff aU (-16)) (SOff aK 16) (runto 0x31c30 ss).
Definition st_RET (ss : sstate) : sstate := runto 0x52c5c ss.
Definition SS_Re : sstate := Eval vm_compute in st_R SS_Qe.
Definition SS_Se : sstate := Eval vm_compute in st_S true SS_Re.
Definition SS_Te : sstate := Eval vm_compute in st_T SS_Se.
Definition SS_Ve : sstate := Eval vm_compute in st_V SS_Te.
Definition SS_We : sstate := Eval vm_compute in st_W true SS_Ve.
Definition SS_Xe : sstate := Eval vm_compute in st_X SS_We.
Definition SS_Ye : sstate := Eval vm_compute in st_Y SS_Xe.
Definition SS_Ze : sstate := Eval vm_compute in st_Z SS_Ye.
Definition SS_RETe : sstate := Eval vm_compute in st_RET SS_Ze.
Definition SS_Ro : sstate := Eval vm_compute in st_R SS_Po.
Definition SS_So : sstate := Eval vm_compute in st_S true SS_Ro.
Definition SS_To : sstate := Eval vm_compute in st_T SS_So.
Definition SS_Vo : sstate := Eval vm_compute in st_V SS_To.
Definition SS_Wo : sstate := Eval vm_compute in st_W true SS_Vo.
Definition SS_Xo : sstate := Eval vm_compute in st_X SS_Wo.
Definition SS_Yo : sstate := Eval vm_compute in st_Y SS_Xo.
Definition SS_Zo : sstate := Eval vm_compute in st_Z SS_Yo.
Definition SS_RETo : sstate := Eval vm_compute in st_RET SS_Zo.
Lemma SS_Se_hi : st_S false SS_Re = SS_Se. Proof. vm_compute. reflexivity. Qed.
Lemma SS_So_hi : st_S false SS_Ro = SS_So. Proof. vm_compute. reflexivity. Qed.
Lemma SS_We_big : st_W false SS_Ve = SS_We. Proof. vm_compute. reflexivity. Qed.
Lemma SS_Wo_big : st_W false SS_Vo = SS_Wo. Proof. vm_compute. reflexivity. Qed.
Definition CL2_lo : sv := Eval vm_compute in sr_get (ss_regs (runto 0x31bb0 (arm BC_LTU false (SLit 512) (SOff aND 0) SS_Re))) 11%bv.
Definition CL2_hi : sv := Eval vm_compute in sr_get (ss_regs (runto 0x31bb0 (arm BC_LTU true (SLit 512) (SOff aND 0) SS_Re))) 11%bv.
Lemma seg2_stops :
ss_pc SS_M0 = 0x318f4 /\ ss_pc SS_N0 = 0x319c4 /\ ss_pc SS_O0 = 0x53a88 /\ ss_pc SS_MS1 = 0x97698 /\ ss_pc SS_P0 = 0x31a68 /\
ss_pc SS_Re = 0x31ac4 /\ ss_pc SS_Ro = 0x31ac4 /\ ss_pc SS_Ve = 0x31be0 /\ ss_pc SS_Vo = 0x31be0 /\
ss_pc SS_RETe = 0x52c5c /\ ss_pc SS_RETo = 0x52c5c /\
sr_get (ss_regs SS_M0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aK 0) (SLit 3)) /\
sr_get (ss_regs SS_N0) 22%bv = SAlu ALU_AND (SOff 10 0) (SLit 281474976710648) /\
sr_get (ss_regs SS_O0) 8%bv = SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff aN8D (-8)) (SOff aU 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aU 0) (SLit 3)) /\
sr_get (ss_regs SS_O0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aU 0) (SLit 3)) /\
sr_get (ss_regs SS_MS1) 10%bv = SOff aSU 0 /\ sr_get (ss_regs SS_MS1) 11%bv = SLit 0 /\ sr_get (ss_regs SS_MS1) 12%bv = SOff aCNT8 0 /\ sr_get (ss_regs SS_MS1) 1%bv = SLit 0x319d8 /\
sr_get (ss_regs SS_P0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SAlu ALU_ADD (SOff aN8D 0) (SOff aU 0)) (SLit 3)) /\
CL2_lo = SAlu ALU_SRL (SOff aND 31) (SLit 5) /\ svpure CL2_hi = true /\ sv_only aND CL2_hi = true /\
sr_get (ss_regs (runto 0x31bb8 SS_Se)) 10%bv = SAlu ALU_ADD (SOff aT 2912) (SAlu ALU_SLL (SOff aCL 0) (SLit 3)) /\
(let m := runto 0x97698 SS_We in (sr_get (ss_regs m) 10%bv, sr_get (ss_regs m) 11%bv, sr_get (ss_regs m) 12%bv, sr_get (ss_regs m) 1%bv)) = (SOff aU 0, SLit 190, SOff aFIL 0, SLit 0x31c00) /\
sr_get (ss_regs SS_RETe) 10%bv = SOff aU 0 /\ sr_get (ss_regs SS_RETo) 10%bv = SOff aU 0 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 SS_Ze) = RS_stopped (SR_jalr (SOff 1 0)) /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 SS_Zo) = RS_stopped (SR_jalr (SOff 1 0)).
Proof. vm_compute. repeat split; reflexivity. Qed.
