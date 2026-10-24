(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02 YN2j YN0j YN1k YN0b YN1g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition PS_B : Z := src0_A_alloc_slot + 0xc8.
Definition PS_C : Z := src0_A_alloc_slot + 0xf4.
Definition PS_D : Z := src0_A_alloc_slot + 0x128.
Definition PS_G0' : Z := src0_A_alloc_slot + 0x1e0.
Definition R_actW0 : region := mkRegion (Some 33%nat) 88 96 88 96 [].
Definition R_actW (v : sv) : region := mkRegion (Some 33%nat) 88 96 88 96 [mkChunk 88 (CVal 8 v)].
Definition FM (k : nat) : nat * afact := (k, mkAF 4096 (2 ^ 63) 3).
Definition FNZ (k : nat) : nat * afact := (k, mkAF 1 (2 ^ 32 - 1) 0).
Definition MEM0 : smem := R_actW0 :: tl (ss_mem ss_hd).
Definition closeF (ss0 : sstate) (stop : Z) : sstate := set_facts (fst (sym_run_toN src0segs src0tbl FUEL stop ss0)) (ss_facts ss0).
Definition ss_beta : sstate := Eval vm_compute in
mkSS PS_B (sr_set (sr_set (ss_regs ss_hd) 10%bv (SOff 40 0)) 11%bv (SOff 43 0)) MEM0 None (ss_facts ss_hd).
Definition JG : list reg := [10; 11; 12; 13]%bv.
Definition ss_gamma : sstate := Eval vm_compute in
mkSS PS_C (sr_set (ss_regs (junk_regs JG 48 ss_hd)) 14%bv (SLit 2)) MEM0 None (ss_facts ss_hd).
Definition JD : list reg := [10; 11; 12; 13; 14; 15; 16; 17; 5; 6]%bv.
Definition ss_delta : sstate := Eval vm_compute in
mkSS PS_D (ss_regs (junk_regs JD 80 ss_hd)) MEM0 None (ss_facts ss_hd).
Lemma ss_beta_pc : ss_pc ss_beta = PS_B. Proof. reflexivity. Qed.
Lemma ss_gamma_pc : ss_pc ss_gamma = PS_C. Proof. reflexivity. Qed.
Lemma ss_delta_pc : ss_pc ss_delta = PS_D. Proof. reflexivity. Qed.
Lemma ss_beta_atoms : ss_atoms_lt 44 ss_beta = true. Proof. vm_compute. reflexivity. Qed.
Lemma ss_gamma_atoms : ss_atoms_lt 52 ss_gamma = true. Proof. vm_compute. reflexivity. Qed.
Lemma ss_delta_atoms : ss_atoms_lt 90 ss_delta = true. Proof. vm_compute. reflexivity. Qed.
Lemma stations_shape :
ss_mem ss_beta = MEM0 /\ ss_mem ss_gamma = MEM0 /\ ss_mem ss_delta = MEM0 /\
ss_facts ss_beta = ss_facts ss_hd /\ ss_facts ss_gamma = ss_facts ss_hd /\ ss_facts ss_delta = ss_facts ss_hd /\
ss_resv ss_beta = None /\ ss_resv ss_gamma = None /\ ss_resv ss_delta = None /\
sr_get (ss_regs ss_beta) 10 = SOff 40 0 /\ sr_get (ss_regs ss_gamma) 10 = SOff 48 0 /\ sr_get (ss_regs ss_gamma) 13 = SOff 51 0 /\
sr_get (ss_regs ss_delta) 10 = SOff 80 0 /\
(forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> sr_get (ss_regs ss_beta) r = sr_get (ss_regs ss_hd) r) /\
(forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> sr_get (ss_regs ss_gamma) r = sr_get (ss_regs ss_hd) r) /\
(forall r, In r [1; 2; 3; 4; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> sr_get (ss_regs ss_delta) r = sr_get (ss_regs ss_hd) r).
Proof.
repeat (split; [vm_compute; reflexivity|]).
split; [|split]; intros r Hr; cbn [In] in Hr; decompose [or] Hr; try contradiction; subst r; reflexivity.
Qed.
Definition aNX0 := 40%nat. Definition aPR0 := 41%nat. Definition aFR0 := 42%nat.
Definition R_m0r : region := mkRegion (Some 34%nat) 0 40 0 0 [mkChunk 8 (CVal 8 (SOff aNX0 0)); mkChunk 24 (CVal 4 (SLit 0)); mkChunk 28 (CVal 4 (SOff aFR0 0))].
Definition C_fr0 : acond := mkAC BC_NE (SExt true 32 (SOff aFR0 0)) (SLit 0).
Definition ss_AR1 : sstate := mkSS (ss_pc ss_hd) (ss_regs ss_hd) ([R_m0r; R_actW (SOff 34 0)] ++ tl (ss_mem ss_hd)) None
(mkFacts ([FM 34; FM aNX0; FNZ aFR0] ++ f_atoms (ss_facts ss_hd)) [C_hd1; C_fr0] []).
Definition R_m0d1 : region := mkRegion (Some 34%nat) 0 40 0 16 [mkChunk 0 (CVal 8 (SOff 34 0)); mkChunk 8 (CVal 8 (SOff 34 0)); mkChunk 24 (CVal 4 (SLit 0)); mkChunk 28 (CVal 4 (SLit 0))].
Definition ss_AD1 : sstate := mkSS (ss_pc ss_hd) (ss_regs ss_hd) ([R_m0d1; R_actW (SOff 34 0)] ++ tl (ss_mem ss_hd)) None
(mkFacts ([FM 34] ++ f_atoms (ss_facts ss_hd)) [C_hd1] []).
Definition R_m0d (pr : sv) : region := mkRegion (Some 34%nat) 0 40 0 16 [mkChunk 0 (CVal 8 pr); mkChunk 8 (CVal 8 (SOff aNX0 0)); mkChunk 24 (CVal 4 (SLit 0)); mkChunk 28 (CVal 4 (SLit 0))].
Definition R_m1d2 : region := mkRegion (Some aNX0) 0 40 0 16 [].
Definition C_nx0 : acond := mkAC BC_NE (SOff aNX0 0) (SOff 34 0).
Definition ss_AD2 : sstate := mkSS (ss_pc ss_hd) (ss_regs ss_hd) ([R_m0d (SOff aNX0 0); R_m1d2; R_actW (SOff 34 0)] ++ tl (ss_mem ss_hd)) None
(mkFacts ([FM 34; FM aNX0] ++ f_atoms (ss_facts ss_hd)) [C_hd1; C_nx0] []).
Definition R_prd3 : region := mkRegion (Some aPR0) 0 40 8 16 [].
Definition R_nxd3 : region := mkRegion (Some aNX0) 0 40 0 8 [].
Definition ss_AD3 : sstate := mkSS (ss_pc ss_hd) (ss_regs ss_hd) ([R_m0d (SOff aPR0 0); R_prd3; R_nxd3; R_actW (SOff 34 0)] ++ tl (ss_mem ss_hd)) None
(mkFacts ([FM 34; FM aNX0; FM aPR0] ++ f_atoms (ss_facts ss_hd)) [C_hd1; C_nx0] []).
Definition SSA_R1 : sstate := Eval vm_compute in closeF ss_AR1 PS_B.
Definition SSA_D1 : sstate := Eval vm_compute in closeF ss_AD1 PS_G0'.
Definition SSA_D2 : sstate := Eval vm_compute in closeF ss_AD2 PS_B.
Definition SSA_D3 : sstate := Eval vm_compute in closeF ss_AD3 PS_B.
Lemma AR1_run_ok : run_to_ok PS_B ss_AR1 (fst (sym_run_toN src0segs src0tbl FUEL PS_B ss_AR1)). Proof. split; vm_compute; reflexivity. Qed.
Lemma AD1_run_ok : run_to_ok PS_G0' ss_AD1 (fst (sym_run_toN src0segs src0tbl FUEL PS_G0' ss_AD1)). Proof. split; vm_compute; reflexivity. Qed.
Lemma AD2_run_ok : run_to_ok PS_B ss_AD2 (fst (sym_run_toN src0segs src0tbl FUEL PS_B ss_AD2)). Proof. split; vm_compute; reflexivity. Qed.
Lemma AD3_run_ok : run_to_ok PS_B ss_AD3 (fst (sym_run_toN src0segs src0tbl FUEL PS_B ss_AD3)). Proof. split; vm_compute; reflexivity. Qed.
Lemma SSA_R1_eq : closeF ss_AR1 PS_B = SSA_R1. Proof. vm_compute. reflexivity. Qed.
Lemma SSA_D1_eq : closeF ss_AD1 PS_G0' = SSA_D1. Proof. vm_compute. reflexivity. Qed.
Lemma SSA_D2_eq : closeF ss_AD2 PS_B = SSA_D2. Proof. vm_compute. reflexivity. Qed.
Lemma SSA_D3_eq : closeF ss_AD3 PS_B = SSA_D3. Proof. vm_compute. reflexivity. Qed.
Lemma merge_AR1 : ss_atoms_lt 43 SSA_R1 = true /\ mergeb ss_beta (junk_regs [11%bv] 43 SSA_R1) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma merge_AD2 : ss_atoms_lt 43 SSA_D2 = true /\ mergeb ss_beta (junk_regs [11%bv] 43 SSA_D2) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma merge_AD3 : ss_atoms_lt 43 SSA_D3 = true /\ mergeb ss_beta (junk_regs [11%bv] 43 SSA_D3) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma SSA_R1_shape : ss_mem SSA_R1 = [R_m0r; R_actW (SOff aNX0 0)] ++ tl (ss_mem ss_hd) /\ sr_get (ss_regs SSA_R1) 10 = SOff aNX0 0.
Proof. vm_compute. split; reflexivity. Qed.
Definition R_m0z (wlo whi : Z) : region := mkRegion (Some 34%nat) 0 40 wlo whi [mkChunk 8 (CVal 8 (SLit 0)); mkChunk 0 (CVal 8 (SLit 0)); mkChunk 24 (CVal 4 (SLit 0)); mkChunk 28 (CVal 4 (SLit 0))].
Lemma SSA_D1_shape : ss_mem SSA_D1 = [R_m0z 0 16; R_actW (SLit 0)] ++ tl (ss_mem ss_hd) /\ ss_pc SSA_D1 = PS_G0' /\ ss_resv SSA_D1 = None /\
sr_get (ss_regs SSA_D1) 10 = SLit 0 /\ sr_get (ss_regs SSA_D1) 11 = SLit 0 /\ sr_get (ss_regs SSA_D1) 12 = SOff 34 0 /\
(forall r, In r [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> sr_get (ss_regs SSA_D1) r = sr_get (ss_regs ss_hd) r).
Proof. repeat (split; [vm_compute; reflexivity|]). intros r Hr; cbn [In] in Hr; decompose [or] Hr; try contradiction; subst r; reflexivity. Qed.
Lemma SSA_D2_shape : ss_mem SSA_D2 = [R_m0z 0 16; mkRegion (Some aNX0) 0 40 0 16 [mkChunk 0 (CVal 8 (SOff aNX0 0)); mkChunk 8 (CVal 8 (SOff aNX0 0))]; R_actW (SOff aNX0 0)] ++ tl (ss_mem ss_hd) /\
sr_get (ss_regs SSA_D2) 10 = SOff aNX0 0.
Proof. vm_compute. split; reflexivity. Qed.
Lemma SSA_D3_shape : ss_mem SSA_D3 = [R_m0z 0 16; mkRegion (Some aPR0) 0 40 8 16 [mkChunk 8 (CVal 8 (SOff aNX0 0))]; mkRegion (Some aNX0) 0 40 0 8 [mkChunk 0 (CVal 8 (SOff aPR0 0))]; R_actW (SOff aNX0 0)] ++ tl (ss_mem ss_hd) /\
sr_get (ss_regs SSA_D3) 10 = SOff aNX0 0.
Proof. vm_compute. split; reflexivity. Qed.
Definition aFR1 := 44%nat. Definition aBITS1 := 45%nat. Definition aNX1 := 46%nat. Definition aFR2 := 47%nat.
Definition FRX1 : sv := SExt true 32 (SOff aFR1 0).
Definition ONES1 : sv := SAluw ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff aBITS1 0)) (SLit (-1)).
Definition C_frb : acond := mkAC BC_NE (SAlu ALU_AND (SOff aBITS1 0) (SLit 32)) (SLit 0).
Definition C_noskip : acond := mkAC BC_NE FRX1 ONES1.
Definition C_skip : acond := mkAC BC_EQ FRX1 ONES1.
Definition R_m1B (nx : sv) : region := mkRegion (Some 40%nat) 0 40 0 0 [mkChunk 8 (CVal 8 nx); mkChunk 28 (CVal 4 (SOff aFR1 0)); mkChunk 32 (CVal 8 (SOff aBITS1 0))].
Definition R_m2B : region := mkRegion (Some aNX1) 0 40 0 0 [mkChunk 28 (CVal 4 (SOff aFR2 0))].
Definition b_atoms : list (nat * afact) := [FM 40; FNZ aFR1; (aBITS1, mkAF 0 (2 ^ 64 - 1) 0); FM aNX1; FNZ aFR2].
Definition ss_B (rs : smem) (c : acond) : sstate :=
mkSS PS_B (ss_regs ss_beta) (rs ++ R_actW (SOff 40 0) :: tl (ss_mem ss_hd)) None (mkFacts (b_atoms ++ f_atoms (ss_facts ss_hd)) [C_frb; c] []).
Definition ss_Bn : sstate := ss_B [R_m1B (SOff aNX1 0)] C_noskip.
Definition ss_Bs : sstate := ss_B [R_m1B (SOff aNX1 0); R_m2B] C_skip.
Definition ss_Bss : sstate := ss_B [R_m1B (SOff 40 0)] C_skip.
Definition SSB_n : sstate := Eval vm_compute in closeF ss_Bn PS_C.
Definition SSB_s : sstate := Eval vm_compute in closeF ss_Bs PS_C.
Definition SSB_ss : sstate := Eval vm_compute in closeF ss_Bss PS_C.
Lemma Bn_run_ok : run_to_ok PS_C ss_Bn (fst (sym_run_toN src0segs src0tbl FUEL PS_C ss_Bn)). Proof. split; vm_compute; reflexivity. Qed.
Lemma Bs_run_ok : run_to_ok PS_C ss_Bs (fst (sym_run_toN src0segs src0tbl FUEL PS_C ss_Bs)). Proof. split; vm_compute; reflexivity. Qed.
Lemma Bss_run_ok : run_to_ok PS_C ss_Bss (fst (sym_run_toN src0segs src0tbl FUEL PS_C ss_Bss)). Proof. split; vm_compute; reflexivity. Qed.
Lemma SSB_n_eq : closeF ss_Bn PS_C = SSB_n. Proof. vm_compute. reflexivity. Qed.
Lemma SSB_s_eq : closeF ss_Bs PS_C = SSB_s. Proof. vm_compute. reflexivity. Qed.
Lemma SSB_ss_eq : closeF ss_Bss PS_C = SSB_ss. Proof. vm_compute. reflexivity. Qed.
Lemma merge_Bn : ss_atoms_lt 48 SSB_n = true /\ mergeb ss_gamma (junk_regs JG 48 SSB_n) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma merge_Bs : ss_atoms_lt 48 SSB_s = true /\ mergeb ss_gamma (junk_regs JG 48 SSB_s) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma merge_Bss : ss_atoms_lt 48 SSB_ss = true /\ mergeb ss_gamma (junk_regs JG 48 SSB_ss) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma SSB_n_shape : ss_mem SSB_n = ss_mem ss_Bn /\ sr_get (ss_regs SSB_n) 10 = SOff 40 0 /\ sr_get (ss_regs SSB_n) 13 = FRX1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma SSB_s_shape : ss_mem SSB_s = [R_m1B (SOff aNX1 0); R_m2B; R_actW (SOff aNX1 0)] ++ tl (ss_mem ss_hd) /\ sr_get (ss_regs SSB_s) 10 = SOff aNX1 0 /\ sr_get (ss_regs SSB_s) 13 = SExt true 32 (SOff aFR2 0).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma SSB_ss_shape : ss_mem SSB_ss = ss_mem ss_Bss /\ sr_get (ss_regs SSB_ss) 10 = SOff 40 0 /\ sr_get (ss_regs SSB_ss) 13 = FRX1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition aG2 := 52%nat. Definition aAI2 := 53%nat. Definition aNX2 := 54%nat.
Definition ACT2 : sv := SAluw ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff aAI2 0)) (SLit (-1)).
Definition MA2 : sv := SAlu ALU_AND ACT2 (SOff 51 0).
Definition C_c0 : acond := mkAC BC_NE MA2 (SLit 0).
Definition C_c12 : acond := mkAC BC_EQ MA2 (SLit 0).
Definition C_nx2 : acond := mkAC BC_NE (SOff aNX2 0) (SOff 48 0).
Definition R_m2C (nx : sv) : region := mkRegion (Some 48%nat) 0 40 0 0 [mkChunk 8 (CVal 8 nx); mkChunk 16 (CVal 8 (SOff aG2 0)); mkChunk 24 (CVal 4 (SLit 0))].
Definition R_g2 : region := mkRegion (Some aG2) 0 16 0 0 [mkChunk 8 (CVal 1 (SOff aAI2 0))].
Definition R_nxC : region := mkRegion (Some aNX2) 0 40 0 0 [mkChunk 24 (CVal 4 (SLit 0))].
Definition c_atoms : list (nat * afact) := [FM 48; (51%nat, mkAF 0 (2 ^ 64 - 1) 0); (aG2, mkAF 4096 (2 ^ 63) 4); (aAI2, mkAF 0 255 0); FM aNX2].
Definition ss_C (rs : smem) (cs : list acond) : sstate :=
mkSS PS_C (ss_regs ss_gamma) (rs ++ R_actW (SOff 48 0) :: tl (ss_mem ss_hd)) None (mkFacts (c_atoms ++ f_atoms (ss_facts ss_hd)) cs []).
Definition ss_C0 : sstate := ss_C [R_m2C (SOff aNX2 0); R_g2] [C_c0].
Definition ss_C1 : sstate := ss_C [R_m2C (SOff aNX2 0); R_g2; R_nxC] [C_c12; C_nx2].
Definition SSC_0 : sstate := Eval vm_compute in closeF ss_C0 PS_D.
Definition SSC_1 : sstate := Eval vm_compute in closeF ss_C1 PS_D.
Lemma C0_run_ok : run_to_ok PS_D ss_C0 (fst (sym_run_toN src0segs src0tbl FUEL PS_D ss_C0)). Proof. split; vm_compute; reflexivity. Qed.
Lemma C1_run_ok : run_to_ok PS_D ss_C1 (fst (sym_run_toN src0segs src0tbl FUEL PS_D ss_C1)). Proof. split; vm_compute; reflexivity. Qed.
Lemma SSC_0_eq : closeF ss_C0 PS_D = SSC_0. Proof. vm_compute. reflexivity. Qed.
Lemma SSC_1_eq : closeF ss_C1 PS_D = SSC_1. Proof. vm_compute. reflexivity. Qed.
Lemma merge_C0 : ss_atoms_lt 80 SSC_0 = true /\ mergeb ss_delta (junk_regs JD 80 SSC_0) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma merge_C1 : ss_atoms_lt 80 SSC_1 = true /\ mergeb ss_delta (junk_regs JD 80 SSC_1) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma SSC_0_shape : ss_mem SSC_0 = ss_mem ss_C0 /\ sr_get (ss_regs SSC_0) 10 = SOff 48 0.
Proof. vm_compute. split; reflexivity. Qed.
Lemma SSC_1_shape : ss_mem SSC_1 = [R_m2C (SOff aNX2 0); R_g2; R_nxC; R_actW (SOff aNX2 0)] ++ tl (ss_mem ss_hd) /\ sr_get (ss_regs SSC_1) 10 = SOff aNX2 0.
Proof. vm_compute. split; reflexivity. Qed.
Definition aG3 := 90%nat. Definition aAI3 := 91%nat. Definition aFR3 := 92%nat. Definition aBITS3 := 93%nat.
Definition aBAD := 94%nat. Definition aBV := 95%nat. Definition aTQ3 := 96%nat. Definition aJ3 := 97%nat.
Definition R_m3 : region := mkRegion (Some 80%nat) 0 40 24 32
[mkChunk 16 (CVal 8 (SOff aG3 0)); mkChunk 24 (CVal 4 (SLit 0)); mkChunk 28 (CVal 4 (SOff aFR3 0)); mkChunk 32 (CVal 4 (SOff aBITS3 0))].
Definition R_g3 : region := mkRegion (Some aG3) 0 16 0 0 [mkChunk 8 (CVal 1 (SOff aAI3 0))].
Definition R_bnc (v : sv) : region := mkRegion (Some aBAD) 0 1 0 1 [mkChunk 0 (CVal 1 v)].
Definition R_tq3 : region := mkRegion (Some aTQ3) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff aJ3 0))].
Definition FRX3 : sv := SExt true 32 (SOff aFR3 0).
Definition SH3 : sv := SAluw ALU_SLL (SLit 2) (SOff aAI3 0).
Definition NEWAV : sv := SAlu ALU_AND FRX3 (SAluw ALU_ADD SH3 (SLit (-1))).
Definition NEWFR : sv := SAlu ALU_AND FRX3 (SAluw ALU_SUB (SLit 0) SH3).
Definition LOWBIT3 : sv := SAlu ALU_AND NEWAV (SAluw ALU_SUB (SLit 0) NEWAV).
Definition AVAIL3' : sv := SAluw ALU_SUB NEWAV LOWBIT3.
Definition TQADDR3 : sv := SAlu ALU_ADD (SLit DEB) (SAluw ALU_SRL (SMd M_MUL LOWBIT3 (SLit DBJ)) (SLit 27)).
Definition SCM7 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff aBITS3 0)) (SLit 52)) (SLit 58)) (SLit (-7)).
Definition BADX : sv := SAlu ALU_ADD (SLit YN0j.LOCK) SCM7.
Definition C_cas : acond := mkAC BC_EQ (SAlu ALU_ADD FRX3 (SLit 0)) FRX3.
Definition C_nav : acond := mkAC BC_NE NEWAV (SLit 0).
Definition C_lb3 : acond := mkAC BC_NE LOWBIT3 (SLit 0).
Definition C_e0 : acond := mkAC BC_LTU (SLit 31) SCM7.
Definition C_e12 : acond := mkAC BC_GEU (SLit 31) SCM7.
Definition AL_tq3 : sv * sv := (TQADDR3, SOff aTQ3 0).
Definition AL_bad : sv * sv := (BADX, SOff aBAD (-888)).
Definition d_atoms : list (nat * afact) :=
[FM 80; (aG3, mkAF 4096 (2 ^ 63) 4); (aAI3, mkAF 0 255 0); (aFR3, mkAF 0 (2 ^ 32 - 1) 0); (aBITS3, mkAF 0 (2 ^ 32 - 1) 0);
(aBAD, mkAF 0x10000 0x51000 0); (aBV, mkAF 1 255 0); (aTQ3, mkAF DEB (DEB + 31) 0); (aJ3, mkAF 0 31 0)].
Definition ss_Dg (rs : smem) (c : acond) (al : list (sv * sv)) : sstate :=
mkSS PS_D (ss_regs ss_delta) ([R_m3; R_g3; R_tq3] ++ rs ++ R_actW (SOff 80 0) :: tl (ss_mem ss_hd)) None
(mkFacts (d_atoms ++ f_atoms (ss_facts ss_hd)) [C_cas; C_nav; C_lb3; c] (AL_tq3 :: al)).
Definition ss_DE0 : sstate := ss_Dg [] C_e0 [].
Definition ss_DE1 : sstate := ss_Dg [R_bnc (SLit 0)] C_e12 [AL_bad].
Definition ss_DE2 : sstate := ss_Dg [R_bnc (SOff aBV 0)] C_e12 [AL_bad].
Definition SSD_0 : sstate := Eval vm_compute in closeF ss_DE0 PS_JR.
Definition SSD_1 : sstate := Eval vm_compute in closeF ss_DE1 PS_JR.
Definition SSD_2 : sstate := Eval vm_compute in closeF ss_DE2 PS_JR.
Lemma DE0_run_ok : run_to_ok PS_JR ss_DE0 (fst (sym_run_toN src0segs src0tbl FUEL PS_JR ss_DE0)). Proof. split; vm_compute; reflexivity. Qed.
Lemma DE1_run_ok : run_to_ok PS_JR ss_DE1 (fst (sym_run_toN src0segs src0tbl FUEL PS_JR ss_DE1)). Proof. split; vm_compute; reflexivity. Qed.
Lemma DE2_run_ok : run_to_ok PS_JR ss_DE2 (fst (sym_run_toN src0segs src0tbl FUEL PS_JR ss_DE2)). Proof. split; vm_compute; reflexivity. Qed.
Lemma SSD_0_eq : closeF ss_DE0 PS_JR = SSD_0. Proof. vm_compute. reflexivity. Qed.
Lemma SSD_1_eq : closeF ss_DE1 PS_JR = SSD_1. Proof. vm_compute. reflexivity. Qed.
Lemma SSD_2_eq : closeF ss_DE2 PS_JR = SSD_2. Proof. vm_compute. reflexivity. Qed.
Definition R_m3' : region := mkRegion (Some 80%nat) 0 40 24 32
[mkChunk 24 (CVal 4 AVAIL3'); mkChunk 28 (CVal 4 NEWFR); mkChunk 16 (CVal 8 (SOff aG3 0)); mkChunk 32 (CVal 4 (SOff aBITS3 0))].
Lemma SSD_shape :
(ss_mem SSD_0 = [R_m3'; R_g3; R_tq3] ++ R_actW (SOff 80 0) :: tl (ss_mem ss_hd) /\ ss_mem SSD_1 = [R_m3'; R_g3; R_tq3; R_bnc (SLit 0)] ++ R_actW (SOff 80 0) :: tl (ss_mem ss_hd) /\
ss_mem SSD_2 = [R_m3'; R_g3; R_tq3; R_bnc (SOff aBV (-1))] ++ R_actW (SOff 80 0) :: tl (ss_mem ss_hd)) /\
(forall ssx, In ssx [SSD_0; SSD_1; SSD_2] ->
ss_pc ssx = PS_JR /\ ss_resv ssx = None /\ sr_get (ss_regs ssx) 1 = SOff 1 0 /\ sr_get (ss_regs ssx) 10 = SOff aJ3 0).
Proof.
split; [vm_compute; repeat split; reflexivity|].
intros ssx Hin. cbn [In] in Hin. decompose [or] Hin; try contradiction; subst ssx; (repeat split; vm_compute; reflexivity).
Qed.
Fixpoint sv_free (k : nat) (v : sv) : bool :=
match v with
| SLit _ => true
| SOff n _ => negb (Nat.eqb n k)
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => sv_free k a && sv_free k b
| SExt _ _ a => sv_free k a
| SData _ _ _ => true
| SF1 _ a => sv_free k a
| SF2 _ a b => sv_free k a && sv_free k b
| SF3 _ a b c => sv_free k a && sv_free k b && sv_free k c
end.
Lemma sv_denot_ewset_free k w E v : sv_free k v = true -> sv_denot (ewset E k w) v = sv_denot E v.
Proof.
induction v; cbn; intros H; try reflexivity;
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end;
rewrite ?IHv, ?IHv1, ?IHv2, ?IHv3 by assumption; try reflexivity.
apply negb_true_iff in H. rewrite H. reflexivity.
Qed.
Definition chunk_free (k : nat) (c : chunk) : bool := match c_val c with CVal _ v => sv_free k v | _ => true end.
Definition region_free (k : nat) (r : YP09.region) : bool :=
match r_base r with Some b => negb (Nat.eqb b k) | None => true end && forallb (chunk_free k) (r_chunks r).
Lemma base_val_ewset_other k w E b : b <> Some k -> base_val (ewset E k w) b = base_val E b.
Proof. intros H. destruct b as [n|]; cbn; [|reflexivity]. destruct (Nat.eqb_spec n k) as [->|]; [exfalso; exact (H eq_refl) | reflexivity]. Qed.
Lemma region_ok_ewset_free k w E m r : region_free k r = true -> region_ok src0segs E m r -> region_ok src0segs (ewset E k w) m r.
Proof.
intros Hf (H1 & H2 & H3 & H4). unfold region_free in Hf. apply andb_prop in Hf as [Hb Hc].
assert (EB : base_val (ewset E k w) (r_base r) = base_val E (r_base r)).
{ apply base_val_ewset_other. destruct (r_base r) as [b|]; [|discriminate]. apply negb_true_iff in Hb. apply Nat.eqb_neq in Hb. congruence. }
unfold region_ok. rewrite EB. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
apply Forall_forall. intros c Hin i Hi. pose proof (proj1 (Forall_forall _ _) H4 c Hin i Hi) as (b & Hb1 & Hb2). exists b. split; [|exact Hb2].
pose proof (proj1 (forallb_forall _ _) Hc c Hin) as Fc. unfold chunk_free in Fc. destruct (c_val c) as [wd v| | |]; cbn [cbyte] in Hb1 |- *; try exact Hb1.
rewrite (sv_denot_ewset_free k w E v Fc). exact Hb1.
Qed.
Definition ADDR36 : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 1)) (SLit SCT).
Definition ss_AD1g : sstate := mkSS (ss_pc ss_hd) (ss_regs ss_hd) ([R_m0d1; R_sct; R_actW (SOff 34 0)] ++ tl (ss_mem ss_hd)) None
(mkFacts ([FM 34; (36%nat, F_sct); (35%nat, F_sz)] ++ f_atoms (ss_facts ss_hd)) [C_hd1] [(ADDR36, SOff 36 0)]).
Definition SSA_D1g : sstate := Eval vm_compute in closeF ss_AD1g src0_A_alloc_meta.
Lemma AD1g_run_ok : run_to_ok src0_A_alloc_meta ss_AD1g (fst (sym_run_toN src0segs src0tbl FUEL src0_A_alloc_meta ss_AD1g)). Proof. split; vm_compute; reflexivity. Qed.
Lemma SSA_D1g_eq : closeF ss_AD1g src0_A_alloc_meta = SSA_D1g. Proof. vm_compute. reflexivity. Qed.
Lemma SSA_D1g_shape : ss_mem SSA_D1g = [R_m0z 0 16; R_sct; R_actW (SLit 0)] ++ tl (ss_mem ss_hd) /\ ss_pc SSA_D1g = src0_A_alloc_meta /\ ss_resv SSA_D1g = None /\
sr_get (ss_regs SSA_D1g) 11 = SLit 0 /\ sr_get (ss_regs SSA_D1g) 12 = SOff 34 0 /\ sr_get (ss_regs SSA_D1g) 19 = SOff 36 (- SCT).
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition g0_regs : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Lemma g0_regs_check : forallb (fun k => let r : reg := Z_to_bv 5 (Z.of_nat k) in sv_eqb (sr_get (ss_regs ss_G0) r) (sr_get (ss_regs SSA_D1g) r) && sv_free 34 (sr_get (ss_regs ss_G0) r)) g0_regs = true /\
sr_get (ss_regs ss_G0) 11 = SOff 37 0 /\ sr_get (ss_regs ss_G0) 12 = SOff 38 0 /\ sr_get (ss_regs ss_G0) 19 = SAlu ALU_SLL (SOff 10 0) (SLit 1) /\ sr_get (ss_regs ss_G0) 0 = SLit 0 /\
ss_pc ss_G0 = src0_A_alloc_meta /\ ss_resv ss_G0 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma g0_mem_shape : ss_mem ss_G0 = [R_sct; R_act] ++ tl (ss_mem ss_hd) /\ regions_wf (ss_mem ss_G0) = true /\ forallb (region_free 34) (R_sct :: tl (ss_mem ss_hd)) = true /\
ss_facts ss_G0 = mkFacts [(36%nat, F_sct); (35%nat, F_sz); (33%nat, F_s7); (34%nat, F_hd); (2%nat, F_spS); (10%nat, mkAF 0 47 0); (11%nat, mkAF 0 131051 0)] [C_hd0] [].
Proof. vm_compute. repeat split; reflexivity. Qed.
End d.
