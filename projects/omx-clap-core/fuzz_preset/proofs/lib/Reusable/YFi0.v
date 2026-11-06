(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFi0.v, with its module paths changed; relocated to fuzz_preset asan-ubsan (pin f8f98a95bc52), map sha256 69a6a2e91fb7, checker port_addr_check.py 39e67a7eb166. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgCellsB.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0d YB1v YB1q YF0m YF0x YFl0 YFhy YFhz.
Import ListNotations. Open Scope Z_scope.
Definition hMS1 : nat := 133.
Definition hCL2 : nat := 139.
Definition hMS2 : nat := 144.
Definition R_scr2 : YP09.region := YP09.mkRegion (Some 2%nat) (- ASTACK) (- 2272) (- ASTACK) (- 2272) [].
Definition rs_D : smem := match ss_mem SS_PD with r0 :: r1 :: rest => r0 :: trim_lo r1 (-2272) :: rest | l => l end.
Definition SS_2 : sstate := Eval vm_compute in addreg R_scr2 (ss_after_call SS_PD rs_D hD1 B_ALLOCTYPE_PC_OFF_3AC).
Definition SS_M0 : sstate := Eval vm_compute in runto B_ALLOCTYPE_PC_OFF_3D4 SS_2.
Definition SS_M : sstate := Eval vm_compute in pin SS_M0 10%bv (SOff aSK 0).
Definition SS_N0 : sstate := Eval vm_compute in runto B_ALLOCTYPE_PC_OFF_4A4 SS_M.
Definition SS_N : sstate := Eval vm_compute in pin SS_N0 22%bv (SOff aN8D 0).
Definition SS_O0 : sstate := Eval vm_compute in runto B_POISONSHADOW_PC_OFF_2B8 SS_N.
Definition SS_O : sstate := Eval vm_compute in pin (pin SS_O0 8%bv (SOff aCNT8 0)) 10%bv (SOff aSU 0).
Definition SS_MS1 : sstate := Eval vm_compute in runto B_MEMSET_PC SS_O.
Definition CLOB_MS : list (bv 5) := [11; 12; 13; 14; 15; 16]%bv.
Definition SS_Q : sstate := Eval vm_compute in ss_after_stretch SS_MS1 (ss_mem SS_MS1) hMS1 CLOB_MS B_ALLOCTYPE_PC_OFF_4B8.
Definition SS_Qe : sstate := Eval vm_compute in arm BC_EQ true (SOff 10 0) (SOff aN8D 0) SS_Q.
Definition SS_Qo : sstate := Eval vm_compute in arm BC_EQ false (SOff 10 0) (SOff aN8D 0) SS_Q.
Definition R_pb : YP09.region := YP09.mkRegion (Some aPB) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 250))].
Definition SS_P0 : sstate := Eval vm_compute in runto B_ALLOCTYPE_PC_OFF_548 SS_Qo.
Definition SS_Po : sstate := Eval vm_compute in addreg R_pb (pin SS_P0 10%bv (SOff aPB 0)).
Definition CLOB_CL2 : list (bv 5) := [12; 13; 14; 15; 16]%bv.
Definition st_R (ss : sstate) : sstate := runto B_ALLOCTYPE_PC_OFF_5A4 ss.
Definition st_S (lo : bool) (ss : sstate) : sstate := noconds (pin (forget (runto B_ALLOCTYPE_PC_OFF_690 (arm BC_LTU (negb lo) (SLit 512) (SOff aND 0) ss)) hCL2 CLOB_CL2) 11%bv (SOff aCL 0)).
Definition st_T (ss : sstate) : sstate := pin (runto B_ALLOCTYPE_PC_OFF_698 ss) 10%bv (SOff aSSLOT 0).
Definition st_V (ss : sstate) : sstate := runto B_ALLOCTYPE_PC_OFF_6C0 ss.
Definition st_W (small : bool) (ss : sstate) : sstate := noconds (pin (runto B_ALLOCTYPE_PC_OFF_6C8 (arm BC_LTU small (SOff 10 0) (SLit 4096) ss)) 12%bv (SOff aFIL 0)).
Definition st_X (ss : sstate) : sstate := let m := runto B_MEMSET_PC ss in ss_after_stretch m (ss_mem m) hMS2 CLOB_MS B_ALLOCTYPE_PC_OFF_6E0.
Definition st_Y (ss : sstate) : sstate := arm BC_EQ false (SOff aU (-16)) (SOff aK 0) (runto B_ALLOCTYPE_PC_OFF_708 ss).
Definition st_Z (ss : sstate) : sstate := arm BC_LTU false (SOff aU (-16)) (SOff aK 16) (runto B_ALLOCTYPE_PC_OFF_710 ss).
Definition st_RET (ss : sstate) : sstate := runto B_INTERCEPTOR_MALLOC_PC_OFF_158 ss.
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
Definition CL2_lo : sv := Eval vm_compute in sr_get (ss_regs (runto B_ALLOCTYPE_PC_OFF_690 (arm BC_LTU false (SLit 512) (SOff aND 0) SS_Re))) 11%bv.
Definition CL2_hi : sv := Eval vm_compute in sr_get (ss_regs (runto B_ALLOCTYPE_PC_OFF_690 (arm BC_LTU true (SLit 512) (SOff aND 0) SS_Re))) 11%bv.
Lemma seg2_stops :
ss_pc SS_M0 = B_ALLOCTYPE_PC_OFF_3D4 /\ ss_pc SS_N0 = B_ALLOCTYPE_PC_OFF_4A4 /\ ss_pc SS_O0 = B_POISONSHADOW_PC_OFF_2B8 /\ ss_pc SS_MS1 = B_MEMSET_PC /\ ss_pc SS_P0 = B_ALLOCTYPE_PC_OFF_548 /\
ss_pc SS_Re = B_ALLOCTYPE_PC_OFF_5A4 /\ ss_pc SS_Ro = B_ALLOCTYPE_PC_OFF_5A4 /\ ss_pc SS_Ve = B_ALLOCTYPE_PC_OFF_6C0 /\ ss_pc SS_Vo = B_ALLOCTYPE_PC_OFF_6C0 /\
ss_pc SS_RETe = B_INTERCEPTOR_MALLOC_PC_OFF_158 /\ ss_pc SS_RETo = B_INTERCEPTOR_MALLOC_PC_OFF_158 /\
sr_get (ss_regs SS_M0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aK 0) (SLit 3)) /\
sr_get (ss_regs SS_N0) 22%bv = SAlu ALU_AND (SOff 10 0) (SLit 281474976710648) /\
sr_get (ss_regs SS_O0) 8%bv = SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff aN8D (-8)) (SOff aU 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aU 0) (SLit 3)) /\
sr_get (ss_regs SS_O0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aU 0) (SLit 3)) /\
sr_get (ss_regs SS_MS1) 10%bv = SOff aSU 0 /\ sr_get (ss_regs SS_MS1) 11%bv = SLit 0 /\ sr_get (ss_regs SS_MS1) 12%bv = SOff aCNT8 0 /\ sr_get (ss_regs SS_MS1) 1%bv = SLit B_ALLOCTYPE_PC_OFF_4B8 /\
sr_get (ss_regs SS_P0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SAlu ALU_ADD (SOff aN8D 0) (SOff aU 0)) (SLit 3)) /\
CL2_lo = SAlu ALU_SRL (SOff aND 31) (SLit 5) /\ svpure CL2_hi = true /\ sv_only aND CL2_hi = true /\
sr_get (ss_regs (runto B_ALLOCTYPE_PC_OFF_698 SS_Se)) 10%bv = SAlu ALU_ADD (SOff aT 2912) (SAlu ALU_SLL (SOff aCL 0) (SLit 3)) /\
(let m := runto B_MEMSET_PC SS_We in (sr_get (ss_regs m) 10%bv, sr_get (ss_regs m) 11%bv, sr_get (ss_regs m) 12%bv, sr_get (ss_regs m) 1%bv)) = (SOff aU 0, SLit 190, SOff aFIL 0, SLit B_ALLOCTYPE_PC_OFF_6E0) /\
sr_get (ss_regs SS_RETe) 10%bv = SOff aU 0 /\ sr_get (ss_regs SS_RETo) 10%bv = SOff aU 0 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 SS_Ze) = RS_stopped (SR_jalr (SOff 1 0)) /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 SS_Zo) = RS_stopped (SR_jalr (SOff 1 0)).
Proof. vm_compute. repeat split; reflexivity. Qed.
