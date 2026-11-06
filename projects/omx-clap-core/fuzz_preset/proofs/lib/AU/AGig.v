(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGig.v (cold/c-asan-realloc-primary c7c1c792ad5, file sha256 edc7a6a6d58f) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53); module paths changed; its 30 image addresses moved by code-verified function pairs (27 port_addr_check 39e67a7eb166 MAPS predictions, each code one re-derived by funcpair.py; 7 code pcs the tool read as sizes, by funcpair.py), and 3 pcs named in comments; no other numeral changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0d YB1v YB1q YF0m YF0x YFl0 YFhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGhy AGhz AGi0 AGi4 AGi9 AGid AGie AGif.
Import ListNotations. Open Scope Z_scope.
Definition sM5 : nat := 182.
Definition kJQ : nat := 203.
Definition sMF : nat := 224.
Definition sL6 : nat := 218.
Definition CLOB_L6 : list (bv 5) := [12; 13; 14; 15; 16; 17]%bv.
Definition CLOBJ : list (bv 5) := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition USH_LEN : sv :=
SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff aMAP 6136) (SOff aN8DS 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aMAP 6144) (SLit 3)).
Definition U_M5 : sstate := Eval vm_compute in runto 0x9bf08 (arm BC_LTU true USH_LEN (SLit 18446744073709551615) T_R).
Definition U_Q : sstate := Eval vm_compute in ss_after_stretch U_M5 (ss_mem U_M5) sM5 CLOB_MS 0x32b5c.
Definition joinQ0 (ss : sstate) : sstate :=
noconds (forget (mkSS (ss_pc ss) (ss_regs ss) (trimscratch (-128) (ss_mem ss)) (ss_resv ss) (ss_facts ss)) kJQ CLOBJ).
Definition U_QJ : sstate := Eval vm_compute in joinQ0 U_Q.
(* can_fill (atom 15) is tested at 0x32d4c: cf <> 0 falls through to the fill (stF); cf = 0 jumps to 0x32d84 (stV0). *)
Definition stF (ss : sstate) : sstate := runto 0x9bf08 (arm BC_EQ false (SOff 15 0) (SLit 0) (runto 0x32d4c ss)).
Definition stV0 (ss : sstate) : sstate := arm BC_EQ true (SOff 15 0) (SLit 0) (runto 0x32d4c ss).
Definition Ue_MF : sstate := Eval vm_compute in stF (arm BC_EQ true (SOff 10 0) (SOff aN8DS 0) U_QJ).
Definition R_pbS : YP09.region := YP09.mkRegion (Some aPBS) 0 1 0 1 [].
Definition Uo_L6 : sstate := Eval vm_compute in runto 0x32b88 (arm BC_EQ false (SOff 10 0) (SOff aN8DS 0) U_QJ).
Definition Uo_L6lo : sstate := Eval vm_compute in runto 0x32bec (armR BC_GEU true 12 22 Uo_L6).
Definition Uo_L6h : sstate := Eval vm_compute in runto 0x32bc4 (armR BC_GEU false 12 22 Uo_L6).
Definition Uo_L6h2 : sstate := Eval vm_compute in runto 0x32bc8 (armR BC_LTU false 17 22 Uo_L6h).
Definition Uo_L6hi : sstate := Eval vm_compute in runto 0x32bec (armR BC_GEU false 16 22 Uo_L6h2).
Definition Uo_P0 : sstate := Eval vm_compute in noconds (forget Uo_L6lo sL6 CLOB_L6).
Lemma Uo_P0_h : noconds (forget Uo_L6hi sL6 CLOB_L6) = Uo_P0. Proof. vm_compute. reflexivity. Qed.
Definition Uo_P : sstate := Eval vm_compute in addreg R_pbS (pin Uo_P0 10%bv (SOff aPBS 0)).
Definition Uo_MF : sstate := Eval vm_compute in stF Uo_P.
Definition st_end (ss : sstate) : sstate :=
let a := ss_after_stretch ss (ss_mem ss) sMF CLOB_MS 0x32d84 in
runto 0x32e14 (arm BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112) (runto 0x32db4 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x32dac a)))).
(* The cf = 0 end: no fill, the same tail from 0x32d84. *)
Definition st_end0 (ss : sstate) : sstate :=
runto 0x32e14 (arm BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112) (runto 0x32db4 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x32dac (stV0 ss))))).
Definition Ue_RET : sstate := Eval vm_compute in st_end Ue_MF.
Definition Uo_RET : sstate := Eval vm_compute in st_end Uo_MF.
Definition Ue_RET0 : sstate := Eval vm_compute in st_end0 (arm BC_EQ true (SOff 10 0) (SOff aN8DS 0) U_QJ).
Definition Uo_RET0 : sstate := Eval vm_compute in st_end0 Uo_P.
Lemma segS4_stops :
ss_pc U_M5 = 0x9bf08 /\
map (sr_get (ss_regs U_M5)) [1; 10; 11; 12]%bv =
[SLit 0x32b5c; SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SOff aMAP 6144) (SLit 3)); SLit 0; SAlu ALU_ADD USH_LEN (SLit 0)] /\
ss_pc U_Q = 0x32b5c /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 U_Q) = RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff aN8DS 0)) /\
ss_pc U_QJ = 0x32b5c /\ snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 U_QJ) = RS_stopped (SR_branch BC_EQ (SOff 10 0) (SOff aN8DS 0)) /\
ss_pc Ue_MF = 0x9bf08 /\ map (sr_get (ss_regs Ue_MF)) [1; 10; 11; 12]%bv = [SLit 0x32d84; SOff aMAP 6144; SLit 190; SLit 4096] /\
ss_pc Uo_P0 = 0x32bec /\ sr_get (ss_regs Uo_P0) 10%bv = SAlu ALU_ADD (SOff aSHB 0) (SAlu ALU_SRL (SAlu ALU_ADD (SOff aMAP 6144) (SOff aN8DS 0)) (SLit 3)) /\
ss_pc Uo_MF = 0x9bf08 /\ map (sr_get (ss_regs Uo_MF)) [1; 10; 11; 12]%bv = [SLit 0x32d84; SOff aMAP 6144; SLit 190; SLit 4096] /\
ss_pc Ue_RET = 0x32e14 /\ ss_pc Uo_RET = 0x32e14 /\
map (sr_get (ss_regs Ue_RET)) [2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 2 0; SOff 8 0; SOff 9 0; SOff aMAP 6144; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
map (sr_get (ss_regs Uo_RET)) [2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 2 0; SOff 8 0; SOff 9 0; SOff aMAP 6144; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 Ue_RET) = RS_stopped (SR_jalr (SOff 1 0)) /\
ss_pc Ue_RET0 = 0x32e14 /\ ss_pc Uo_RET0 = 0x32e14 /\
map (sr_get (ss_regs Ue_RET0)) [2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 2 0; SOff 8 0; SOff 9 0; SOff aMAP 6144; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
map (sr_get (ss_regs Uo_RET0)) [2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 2 0; SOff 8 0; SOff 9 0; SOff aMAP 6144; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0] /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 Ue_RET0) = RS_stopped (SR_jalr (SOff 1 0)).
Proof. vm_compute. repeat split; reflexivity. Qed.
