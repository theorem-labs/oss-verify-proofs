(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFig.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan+UBSan build (fuzz_state.asan-ubsan). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YF0m YF0x YFl0 YFhy YFhz YFi0 YFi4 YFi9 YFid YFie YFif.
Import ListNotations. Open Scope Z_scope.
Definition sM5 : nat := 182.
Definition kJQ : nat := 203.
Definition sMF : nat := 224.
Definition sL6 : nat := 218.
Definition CLOB_L6 : list (bv 5) := [12; 13; 14; 15; 16; 17]%bv.
Definition CLOBJ : list (bv 5) := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition USH_LEN : sv :=
SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff aMAP 6136) (SOff aN8DS 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aMAP 6144) (SLit 3)).
Definition U_M5 : sstate := Eval vm_compute in runto 0x99340 (arm BC_LTU true USH_LEN (SLit 18446744073709551615) T_R).
Definition U_Q : sstate := Eval vm_compute in ss_after_stretch U_M5 (ss_mem U_M5) sM5 CLOB_MS 0x3241c.
Definition joinQ0 (ss : sstate) : sstate :=
noconds (forget (mkSS (ss_pc ss) (ss_regs ss) (trimscratch (-2272) (ss_mem ss)) (ss_resv ss) (ss_facts ss)) kJQ CLOBJ).
Definition U_QJ : sstate := Eval vm_compute in joinQ0 U_Q.
Definition Ue_MF : sstate := Eval vm_compute in runto 0x99340 (arm BC_EQ true (SOff 10 0) (SOff aN8DS 0) U_QJ).
Definition R_pbS : YP09.region := YP09.mkRegion (Some aPBS) 0 1 0 1 [].
Definition Uo_L6 : sstate := Eval vm_compute in runto 0x32448 (arm BC_EQ false (SOff 10 0) (SOff aN8DS 0) U_QJ).
Definition Uo_L6lo : sstate := Eval vm_compute in runto 0x324ac (armR BC_GEU true 12 22 Uo_L6).
Definition Uo_L6h : sstate := Eval vm_compute in runto 0x32484 (armR BC_GEU false 12 22 Uo_L6).
Definition Uo_L6h2 : sstate := Eval vm_compute in runto 0x32488 (armR BC_LTU false 17 22 Uo_L6h).
Definition Uo_L6hi : sstate := Eval vm_compute in runto 0x324ac (armR BC_GEU false 16 22 Uo_L6h2).
Definition Uo_P0 : sstate := Eval vm_compute in noconds (forget Uo_L6lo sL6 CLOB_L6).
Lemma Uo_P0_h : noconds (forget Uo_L6hi sL6 CLOB_L6) = Uo_P0. Proof. vm_compute. reflexivity. Qed.
Definition Uo_P : sstate := Eval vm_compute in addreg R_pbS (pin Uo_P0 10%bv (SOff aPBS 0)).
Definition Uo_MF : sstate := Eval vm_compute in runto 0x99340 Uo_P.
Definition st_end (ss : sstate) : sstate :=
let a := ss_after_stretch ss (ss_mem ss) sMF CLOB_MS 0x32644 in
runto 0x53414 (arm BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112) (runto 0x32674 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x3266c a)))).
Definition Ue_RET : sstate := Eval vm_compute in st_end Ue_MF.
Definition Uo_RET : sstate := Eval vm_compute in st_end Uo_MF.
Lemma segS4_stops :
ss_pc U_M5 = 0x99340 /\
map (sr_get (ss_regs U_M5)) [1; 10; 11; 12]%bv =
[SLit 0x3241c; SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aMAP 6144) (SLit 3)); SLit 0; SAlu ALU_ADD USH_LEN (SLit 0)] /\
ss_pc U_Q = 0x3241c /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 U_Q) = RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff aN8DS 0)) /\
ss_pc U_QJ = 0x3241c /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 U_QJ) = RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff aN8DS 0)) /\
ss_pc Ue_MF = 0x99340 /\ map (sr_get (ss_regs Ue_MF)) [1; 10; 11; 12]%bv = [SLit 0x32644; SOff aMAP 6144; SLit 190; SLit 4096] /\
ss_pc Uo_P0 = 0x324ac /\ sr_get (ss_regs Uo_P0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SAlu ALU_ADD (SOff aMAP 6144) (SOff aN8DS 0)) (SLit 3)) /\
ss_pc Uo_MF = 0x99340 /\ map (sr_get (ss_regs Uo_MF)) [1; 10; 11; 12]%bv = [SLit 0x32644; SOff aMAP 6144; SLit 190; SLit 4096] /\
ss_pc Ue_RET = 0x53414 /\ ss_pc Uo_RET = 0x53414 /\
map (sr_get (ss_regs Ue_RET)) [2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 2 0; SOff 8 0; SOff 9 0; SOff aMAP 6144; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
map (sr_get (ss_regs Uo_RET)) [2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 2 0; SOff 8 0; SOff 9 0; SOff aMAP 6144; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 Ue_RET) = RS_stopped (SR_jalr (SOff 1 0)).
Proof. vm_compute. repeat split; reflexivity. Qed.
